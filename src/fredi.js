import {
  BufferJSON,
  WA_DEFAULT_EPHEMERAL,
  generateWAMessageFromContent,
  proto,
  generateWAMessageContent,
  generateWAMessage,
  prepareWAMessageMedia,
  areJidsSameUser,
  getContentType,
  downloadContentFromMessage
} from '@whiskeysockets/baileys';
import fs from 'fs';
import { fileURLToPath } from 'url';
import { dirname } from 'path';
import path from 'path';
import util from 'util';
import speed from 'performance-now';

import {
  smsg,
  formatp,
  tanggal,
  formatDate,
  getTime,
  sleep,
  clockString,
  fetchJson,
  getBuffer,
  jsonformat,
  generateProfilePicture,
  parseMention,
  getRandom,
  fetchBuffer,
  sendJson
} from '../lib/botFunctions.js';
import { exec, spawn, execSync } from 'child_process';
import { TelegraPh, UploadFileUgu } from '../lib/toUrl.js';
import { commands, aliases, totalCommands } from '../handlers/commandHandler.js';
import status_saver from '../features/status_saver.js';
import gcPresence from '../features/gcPresence.js';
import antitag from '../features/antitag.js';
import antilink from '../features/antilink.js';
import { getGroupSettings, updateSetting } from '../database/config.js';
import { getFakeQuoted } from '../lib/fakeQuoted.js';
import {
  getCachedSettings,
  getCachedSudo,
  getCachedBanned,
  getCachedSettingsSync,
  getCachedSudoSync,
  getCachedBannedSync
} from '../lib/settingsCache.js';
import { botname, mycode } from '../config/settings.js';
import { cleanupOldMessages } from '../lib/Store.js';
import * as MessageStore from '../lib/MessageStore.js';
import antistatusmention from '../features/antistatusmention.js';
import autoai from '../features/autoai.js';
import antiviewonce from '../features/antiviewonce.js';
import frediai from '../features/frediai.js';
import afk from '../features/afk.js';
import Ownermiddleware from '../utils/botUtil/Ownermiddleware.js';
import { lidMappingCache } from '../handlers/smsg.js';
import { resolveTargetJid, resolveSenderJid } from '../lib/lidResolver.js';

const __filename = fileURLToPath(import.meta.url);
const __dirname = dirname(__filename);

const DEV_NUMBER = '255752593977';
const OWNER_NUMBER_ENV = (process.env.OWNER_NUMBER || '').replace(/\D/g, '').slice(-10) || null;
const MODS_ENV = (process.env.MODS || '')
  .split(',')
  .map(n => n.replace(/\D/g, '').slice(-10))
  .filter(Boolean);

process.setMaxListeners(50);
cleanupOldMessages();

let _frediPict = Buffer.alloc(0);
try {
  _frediPict = fs.readFileSync(path.resolve(__dirname, '../fredi.jpg'));
} catch (err) {
  _frediPict = Buffer.alloc(0);
}

setInterval(() => cleanupOldMessages(), 60 * 60 * 1000);

let _cachedBotNumber = '';
let _cachedBotJid = '';

if (!global._frediGroupMetaCache) global._frediGroupMetaCache = new Map();
const _groupMetaCache = global._frediGroupMetaCache;
const _groupMetaInFlight = new Map();
const GROUP_META_TTL = 300000; // 5 minutes

async function fastGroupMetadata(client, jid) {
  const now = Date.now();
  const cached = _groupMetaCache.get(jid);
  if (cached && now - cached.time < GROUP_META_TTL) return cached.data;
  if (_groupMetaInFlight.has(jid)) return _groupMetaInFlight.get(jid);

  const promise = (async () => {
    try {
      const data = await Promise.race([
        client.groupMetadata(jid),
        new Promise((_, reject) => setTimeout(() => reject(new Error('meta_timeout')), 3000))
      ]);
      _groupMetaCache.set(jid, { data, time: Date.now() });
      if (_groupMetaCache.size > 200) {
        const oldestKey = _groupMetaCache.keys().next().value;
        _groupMetaCache.delete(oldestKey);
      }
      return data;
    } catch (err) {
      return cached?.data || {};
    } finally {
      _groupMetaInFlight.delete(jid);
    }
  })();

  _groupMetaInFlight.set(jid, promise);
  return promise;
}

async function downloadMedia(client, msgContent, mediaType) {
  try {
    const stream = await downloadContentFromMessage(msgContent, mediaType);
    let buffer = Buffer.from([]);
    for await (const chunk of stream) {
      buffer = Buffer.concat([buffer, chunk]);
    }
    return buffer;
  } catch (err) {
    return await client.downloadMediaMessage(msgContent);
  }
}

function shouldStoreMessage(m) {
  const chatJid = m.chat || m.key?.remoteJid;
  if (!chatJid) return false;
  return !chatJid.includes('@broadcast') && !chatJid.includes('@newsletter');
}

function resolveLidToPhoneNumber(jid) {
  if (!jid || !jid.endsWith('@lid')) return jid;
  try {
    const lidNum = jid.split('@')[0].split(':')[0];
    const mapped =
      lidMappingCache.get(lidNum) ||
      (globalThis.lidPhoneCache && globalThis.lidPhoneCache.get(lidNum));
    if (mapped) return mapped + '@s.whatsapp.net';

    try {
      const sessionDir = path.join(__dirname, '../Session');
      const reverseFile = path.join(sessionDir, `lid-mapping-${lidNum}_reverse.json`);
      if (fs.existsSync(reverseFile)) {
        const raw = fs.readFileSync(reverseFile, 'utf-8');
        const parsed = JSON.parse(raw);
        if (parsed) {
          const phone = String(parsed).split('@')[0].split(':')[0].replace(/\D/g, '');
          if (phone && phone.length >= 7 && phone !== lidNum) {
            if (globalThis.lidPhoneCache) globalThis.lidPhoneCache.set(lidNum, phone);
            return phone + '@s.whatsapp.net';
          }
        }
      }
    } catch {}
    return jid;
  } catch (err) {
    return jid;
  }
}

function getCleanNumber(jid) {
  if (!jid) return 'Unknown';
  let num = jid.split('@')[0].split(':')[0].replace(/[^\d]/g, '');
  if (num.length > 10) num = num.slice(-10);
  return num;
}

function normalizeNumber(jid) {
  if (!jid) return '';
  let num = jid.split('@')[0].split(':')[0].replace(/[^\d]/g, '');
  if (num.length > 10) num = num.slice(-10);
  return num;
}

function isDevNumber(jid) {
  if (!jid) return false;
  const norm = normalizeNumber(jid);
  return norm === DEV_NUMBER;
}

function extractInnerMessage(message) {
  if (!message) return message;
  if (message.ephemeralMessage?.message) return extractInnerMessage(message.ephemeralMessage.message);
  if (message.viewOnceMessage?.message) return extractInnerMessage(message.viewOnceMessage.message);
  if (message.viewOnceMessageV2?.message) return extractInnerMessage(message.viewOnceMessageV2.message);
  if (message.viewOnceMessageV2Extension?.message) return extractInnerMessage(message.viewOnceMessageV2Extension.message);
  if (message.documentWithCaptionMessage?.message) return message.documentWithCaptionMessage.message;
  return message;
}

function getMessageType(message) {
  if (!message) return '❓ Unknown';
  const vo = message.viewOnceMessage || message.viewOnceMessageV2 || message.viewOnceMessageV2Extension;
  if (vo) {
    const inner = vo.message || vo;
    if (inner.imageMessage) return '👁️ View Once Image';
    if (inner.videoMessage) return '👁️ View Once Video';
    if (inner.audioMessage) return '👁️ View Once Audio';
    return '👁️ View Once';
  }
  if (message.imageMessage?.viewOnce) return '👁️ View Once Image';
  if (message.videoMessage?.viewOnce) return '👁️ View Once Video';
  if (message.conversation) return '📝 Text';
  if (message.imageMessage) return '🖼️ Image';
  if (message.videoMessage) return '🎥 Video';
  if (message.audioMessage) return '🔊 Audio';
  if (message.stickerMessage) return '😀 Sticker';
  if (message.documentMessage || message.documentWithCaptionMessage) return '📄 Document';
  if (message.contactMessage) return '👤 Contact';
  if (message.contactsArrayMessage) return '👤 Contacts';
  if (message.locationMessage) return '📍 Location';
  if (message.liveLocationMessage) return '📍 Live Location';
  if (message.pollCreationMessage || message.pollCreationMessageV3) return '📊 Poll';
  if (message.extendedTextMessage?.text) return '📝 Extended Text';
  if (message.buttonsResponseMessage) return '🔘 Button Response';
  if (message.listResponseMessage) return '📋 List Response';
  if (message.templateButtonReplyMessage) return '🎨 Template Button';
  if (message.editedMessage) return '✏️ Edited';
  return '❓ Unknown';
}

function isViewOnceMessage(message) {
  if (!message) return false;
  if (message.viewOnceMessage || message.viewOnceMessageV2 || message.viewOnceMessageV2Extension) return true;
  const inner = extractInnerMessage(message);
  if (inner?.imageMessage?.viewOnce === true) return true;
  if (inner?.videoMessage?.viewOnce === true) return true;
  return false;
}

function getViewOnceMedia(message) {
  const vo = message.viewOnceMessage || message.viewOnceMessageV2 || message.viewOnceMessageV2Extension;
  if (vo) {
    const inner = vo.message || vo;
    return {
      image: inner.imageMessage || null,
      video: inner.videoMessage || null
    };
  }
  const inner = extractInnerMessage(message);
  return {
    image: inner?.imageMessage?.viewOnce ? inner.imageMessage : null,
    video: inner?.videoMessage?.viewOnce ? inner.videoMessage : null
  };
}

export default async (client, m, chatUpdate, store) => {
  if (!_cachedBotJid && client.user?.id) {
    _cachedBotJid = client.decodeJid(client.user.id);
    if (_cachedBotJid && _cachedBotJid.includes(':')) {
      _cachedBotJid = _cachedBotJid.split(':')[0];
    }
  }

  if (m.key?.fromMe === true) {
    m.sender = client.user?.id || client.decodeJid(client.user?.id);
  } else {
    m.sender =
      m.key?.participantAlt ||
      m.key?.participant ||
      m.key?.remoteJidAlt ||
      m.key?.remoteJid;
  }

  if (m.sender && m.sender.endsWith('@lid')) {
    m.sender = resolveLidToPhoneNumber(m.sender);
  }
  if (m.chat && m.chat.endsWith('@lid')) {
    m.chat = resolveLidToPhoneNumber(m.chat);
  }

  // Store messages for antidelete / antiedit
  if (shouldStoreMessage(m)) {
    const chatJid = m.chat || m.key?.remoteJid;
    if (chatJid && m.key?.id) {
      const msgKeys = Object.keys(m.message || {});
      const isProtocol =
        msgKeys.length === 0 ||
        (msgKeys.length === 1 && (msgKeys[0] === 'protocolMessage' || msgKeys[0] === 'senderKeyDistributionMessage')) ||
        (msgKeys.length === 2 && msgKeys.includes('senderKeyDistributionMessage') && msgKeys.includes('messageContextInfo'));

      if (!isProtocol) {
        const msgId = m.key.id;
        const senderJid = m.sender || m.key.participant || m.key.remoteJid || '';
        const storedObj = {
          key: m.key,
          message: m.message || {},
          pushName: m.pushName || ''
        };
        await MessageStore.saveMessage(msgId, chatJid, senderJid, storedObj).catch(() => {});
      }
    }
  }

  if (store && shouldStoreMessage(m)) {
    const chatJid = m.chat || m.key?.remoteJid;
    if (chatJid) {
      if (!store.chats) store.chats = Object.create(null);
      if (!store.messageMap) store.messageMap = Object.create(null);
      if (!store.chats[chatJid]) store.chats[chatJid] = [];

      const msgId = m.key.id;
      store.chats[chatJid].push({
        ...m,
        message: m.message || {},
        timestamp: Date.now(),
        originalRemoteJid: chatJid,
        normalizedRemoteJid: chatJid
      });
      store.messageMap[msgId] = {
        normalizedJid: chatJid,
        originalJid: chatJid,
        timestamp: Date.now()
      };

      if (store.chats[chatJid].length > 500) {
        const removed = store.chats[chatJid].shift();
        if (removed?.key?.id) delete store.messageMap[removed.key.id];
      }
    }
  }

  try {
    const rawSudo = getCachedSudoSync();
    const rawBanned = getCachedBannedSync();
    const rawSettings = getCachedSettingsSync();
    getCachedSettings().catch(() => {});

    const sudoList = Array.isArray(rawSudo) ? rawSudo : [];
    const bannedList = Array.isArray(rawBanned) ? rawBanned : [];

    let settings = rawSettings;
    if (!settings) {
      try {
        settings = await getCachedSettings();
      } catch {}
      if (!settings) return;
    }

    const {
      prefix,
      mode,
      gcpresence,
      antitag: antitagSetting,
      antidelete,
      antilink: antilinkSetting,
      chatbotpm,
      packname,
      multiprefix,
      stealth
    } = settings;

    // Extract inner message so ephemeral/viewOnce wrappers don't hide text from owner/users
    const innerMsg = extractInnerMessage(m.message) || m.message || {};

    var body =
      innerMsg?.conversation ||
      innerMsg?.extendedTextMessage?.text ||
      innerMsg?.imageMessage?.caption ||
      innerMsg?.videoMessage?.caption ||
      innerMsg?.documentMessage?.caption ||
      innerMsg?.buttonsResponseMessage?.selectedButtonId ||
      innerMsg?.listResponseMessage?.singleSelectReply?.selectedRowId ||
      innerMsg?.templateButtonReplyMessage?.selectedId ||
      innerMsg?.interactiveResponseMessage?.nativeFlowResponseMessage?.paramsJson ||
      m.text ||
      m.body ||
      '';

    body = typeof body === 'string' ? body : '';

    if (innerMsg?.interactiveResponseMessage?.nativeFlowResponseMessage?.paramsJson) {
      try {
        const rawParams = innerMsg.interactiveResponseMessage.nativeFlowResponseMessage.paramsJson;
        const parsedParams = typeof rawParams === 'string' ? JSON.parse(rawParams) : rawParams;
        body = parsedParams?.id || body;
      } catch {}
    }

    if (innerMsg?.templateButtonReplyMessage?.selectedId) {
      body = innerMsg.templateButtonReplyMessage.selectedId;
    }

    // Prevent bot from replying to its own non-command messages in a loop
    const validPrefixes = ['.', '!', '#', '/', '$', '?', '+', '-', '*', '~', '@', '%', '&', '^', '=', '|', '>', '$'];
    if (m.key?.fromMe) {
      const trimmedBody = body.trim();
      const isQuickViewOnceTrigger = ['w', 'uhm', 'xd', 'p', 'wow'].includes(trimmedBody.toLowerCase()) && m.quoted;
      const hasValidPrefix =
        (prefix && trimmedBody.startsWith(prefix)) ||
        validPrefixes.some(p => trimmedBody.startsWith(p));
      if (!trimmedBody || (!hasValidPrefix && !isQuickViewOnceTrigger)) return;
    }

    const mentionedJid = innerMsg?.extendedTextMessage?.contextInfo?.mentionedJid || [];
    var quotedMsg = innerMsg?.extendedTextMessage?.contextInfo?.quotedMessage || null;
    var budy = typeof m.text === 'string' ? m.text : body;

    const startTime = speed();
    const fredispeed = speed() - startTime;
    const pict = _frediPict;

    const prefixList = ['.', '!', '#', '/', '$', '?', '+', '-', '*', '~', '@', '%', '&', '^', '=', '|'];
    let command = null;
    let usedPrefix = prefix || '.';

    if (body) {
      if (multiprefix === 'true' || multiprefix === true) {
        const matchedPrefix = prefixList.find(p => body.startsWith(p));
        if (matchedPrefix) {
          const rawCmd = body.slice(matchedPrefix.length).trim().split(/\s+/)[0].toLowerCase();
          command = rawCmd.replace(/^[^\w+]+/, '') || rawCmd;
          usedPrefix = matchedPrefix;
        } else if (!prefix) {
          command = body.trim().split(/\s+/)[0].toLowerCase();
        }
      } else {
        if (prefix && body.startsWith(prefix)) {
          const rawCmd = body.slice(prefix.length).trim().split(/\s+/)[0].toLowerCase();
          command = rawCmd.replace(/^[^\w+]+/, '') || rawCmd;
          usedPrefix = prefix;
        } else if (body.startsWith('/') && prefix !== '/') {
          const rawCmd = body.slice(1).trim().split(/\s+/)[0].toLowerCase();
          command = rawCmd.replace(/^[^\w+]+/, '') || rawCmd;
          usedPrefix = '/';
        } else if (!prefix) {
          command = body.trim().split(/\s+/)[0].toLowerCase();
        }
      }
    }

    const resolvedCmdName = aliases[command] || command;
    const cmd = commands[resolvedCmdName];
    const args = body.slice(usedPrefix.length).trim().split(/ +/).slice(1);
    const pushname = m.pushName || 'No Name';

    if (!_cachedBotNumber && client?.user?.id) {
      _cachedBotNumber = client.decodeJid(client.user.id);
      if (_cachedBotNumber && _cachedBotNumber.includes(':')) {
        _cachedBotNumber = _cachedBotNumber.split(':')[0];
      }
    }

    let botNumber = _cachedBotNumber || client.decodeJid(client.user?.id);
    if (botNumber && botNumber.includes(':')) {
      botNumber = botNumber.split(':')[0];
    }

    const senderNorm = normalizeNumber(m.sender);
    const botNorm = normalizeNumber(botNumber);

    // FIXED: Ensure m.key.fromMe is always recognized as itsMe/Owner even if WhatsApp sends @lid
    const itsMe = Boolean(m.key?.fromMe) || (Boolean(senderNorm && botNorm) && senderNorm === botNorm);
    const isDev = isDevNumber(m.sender);
    const isSudo =
      sudoList.some(num => normalizeNumber(String(num)) === senderNorm) ||
      MODS_ENV.some(num => num === senderNorm);
    const isEnvOwner = Boolean(OWNER_NUMBER_ENV && senderNorm === OWNER_NUMBER_ENV);
    const Owner = itsMe || isDev || isSudo || isEnvOwner;
console.log('[DEBUG-CMD]', { fromMe: m.key?.fromMe, sender: m.sender, botNumber, Owner, mode, prefix: usedPrefix, body, command, cmdFound: Boolean(cmd) });

    let text = args.join(' ');
    m.isGroup = m.chat?.endsWith('@g.us');
    m.metadata = {};

    let isAdmin = false;
    let isBotAdmin = false;

    if (m.isGroup) {
      try {
        const cached = _groupMetaCache.get(m.chat);
        if (cached && Date.now() - cached.time < GROUP_META_TTL) {
          m.metadata = cached.data;
        } else {
          m.metadata = await fastGroupMetadata(client, m.chat);
          _groupMetaCache.set(m.chat, { data: m.metadata, time: Date.now() });
        }
      } catch {
        m.metadata = {};
      }

      const participants = m.metadata?.participants || [];
      const cleanDigits = j => (!j ? '' : j.split('@')[0].split(':')[0].replace(/\D/g, ''));
      const resolveParticipantDigits = j => {
        if (!j) return '';
        if (j.endsWith('@lid')) {
          const lidDigits = cleanDigits(j);
          const cachedPhone = globalThis.lidPhoneCache && globalThis.lidPhoneCache.get(lidDigits);
          if (cachedPhone) return String(cachedPhone).replace(/\D/g, '');
          if (m.metadata) {
            const ownerLid = cleanDigits(m.metadata.owner || '');
            if (ownerLid && ownerLid === lidDigits && m.metadata.ownerPn) {
              return m.metadata.ownerPn.split('@')[0].replace(/\D/g, '');
            }
            const subjOwnerLid = cleanDigits(m.metadata.subjectOwner || '');
            if (subjOwnerLid && subjOwnerLid === lidDigits && m.metadata.subjectOwnerPn) {
              return m.metadata.subjectOwnerPn.split('@')[0].replace(/\D/g, '');
            }
          }
          return lidDigits;
        }
        return j.split('@')[0].split(':')[0].replace(/\D/g, '');
      };

      const numbersMatch = (a, b) => {
        if (!a || !b) return false;
        if (a === b) return true;
        const shorter = a.length < b.length ? a : b;
        const longer = a.length < b.length ? b : a;
        return longer.endsWith(shorter) && shorter.length >= 9;
      };

      const senderDigits = resolveParticipantDigits(m.sender);
      const botDigits = resolveParticipantDigits(botNumber);
      const senderLidDigits = m.sender?.endsWith('@lid') ? cleanDigits(m.sender) : '';

      for (const p of participants) {
        const pId = p.id || p.jid || '';
        const pLid = p.lid || '';
        const pPhone = p.phoneNumber || p.phone_number || p.pn || '';
        const pPhoneClean = pPhone ? String(pPhone).replace(/\D/g, '') : '';
        const pResolved = pPhoneClean || resolveParticipantDigits(pId) || resolveParticipantDigits(pLid);
        const pLidClean = pId.endsWith('@lid') ? cleanDigits(pId) : pLid ? cleanDigits(pLid) : '';

        const pIsAdmin = p.admin === 'admin' || p.admin === 'superadmin';
        const matchSender = numbersMatch(pResolved, senderDigits);
        const matchSenderLid = senderLidDigits && pLidClean && senderLidDigits === pLidClean;

        if (pIsAdmin && (matchSender || matchSenderLid)) isAdmin = true;
        if (pIsAdmin && numbersMatch(pResolved, botDigits)) isBotAdmin = true;
      }

      if (Owner) isAdmin = true;
    }

    m.isAdmin = isAdmin;
    m.isBotAdmin = isBotAdmin;

    let quotedTarget = m.quoted || m;
    let qmsg = m;
    if (quotedTarget && typeof quotedTarget === 'object') {
      if (quotedTarget.mtype === 'viewOnceMessage') {
        qmsg = quotedTarget[Object.keys(quotedTarget)[0]];
      } else if (quotedTarget.mtype === 'viewOnceMessageV2') {
        qmsg = quotedTarget.viewOnceMessage?.[Object.keys(quotedTarget.viewOnceMessage || {})[0]] || quotedTarget;
      } else if (quotedTarget.mtype === 'viewOnceMessageV2Extension') {
        qmsg = quotedTarget[Object.keys(quotedTarget)[0]];
      } else if (m.quoted) {
        qmsg = m.quoted;
      }
    }

    const mime = qmsg?.msg ? qmsg.msg.mimetype : qmsg?.mimetype || '';
    const mediaTarget = qmsg?.msg ? qmsg.msg : qmsg;
    const fakeQuoted = getFakeQuoted(m);

    m.reply = async (replyText, targetChat = m.chat, opts = {}) => {
      try {
        return await client.sendMessage(targetChat, { text: String(replyText ?? '') }, { quoted: fakeQuoted, ...opts });
      } catch {
        return await client.sendMessage(targetChat, { text: String(replyText ?? '') }, opts);
      }
    };

    // Eval / Shell (> or $) for Owner
    const rawTrimmed = body.trim();
    if ((rawTrimmed.startsWith('>') || rawTrimmed.startsWith('$')) && Owner && !cmd) {
      const evalCode = rawTrimmed.slice(1).trim();
      if (!evalCode) return await m.reply('W eval?🟢!');
      await client.sendMessage(m.chat, { react: { text: '⌛', key: m.key } });
      try {
        let evaled = await eval(evalCode);
        if (typeof evaled !== 'string') evaled = util.inspect(evaled);
        await client.sendMessage(m.chat, { react: { text: '✅', key: m.key } });
        if (evaled && evaled !== 'undefined' && evaled !== 'null') await m.reply(evaled);
      } catch (err) {
        await client.sendMessage(m.chat, { react: { text: '❌', key: m.key } });
        await m.reply('Error:\n' + String(err));
      }
      return;
    }

    // Banned check
    if (cmd && !isDev && !Owner) {
      const cleanSender = (m.sender || '').replace(/@s\.whatsapp\.net$/, '').split(':')[0];
      if (bannedList.includes(cleanSender)) {
        await client.sendMessage(
          m.chat,
          {
            text: `╭━━━ᕙ FEE-XMD ᕗ━━━\n├━━━≫ Bᴀɴɴᴇᴅ ≪━━━\nツ You're banned from using\nツ my commands. Get unbanned by owner.\n╰━━━━━━━━━━━━━ᕗ`
          },
          { quoted: fakeQuoted }
        );
        return;
      }
    }

    // Mode check (private / group / inbox)
    if (cmd && !itsMe && !isDev && !Owner) {
      if (mode === 'private') return;
      if (mode === 'group' && !m.isGroup) return;
      if (mode === 'inbox' && m.isGroup) return;
    }

    // Stealth check
    const isStealth = stealth === 'true' || stealth === true;
    if (isStealth) {
      if (command === 'stealth' && cmd) {
        const context = {
          client, m, args, text, Owner, chatUpdate, store, isBotAdmin, isAdmin,
          IsGroup: m.isGroup, participants: m.metadata?.participants || [],
          pushname, body, budy, totalCommands, mime, qmsg: mediaTarget,
          msgFredi: quotedMsg, botNumber, itsMe, packname: settings.packname,
          generateProfilePicture, groupMetadata: m.metadata || {}, fredispeed,
          mycode, fetchJson, exec, getRandom, UploadFileUgu, TelegraPh,
          prefix: usedPrefix, cmd, botname, mode, gcpresence, antitag: antitagSetting,
          antidelete, fetchBuffer, sendJson, settings, getGroupAdmins: () => [],
          pict, Tag: mentionedJid, stealth, multiprefix, isDev, isSudo, isEnvOwner,
          fakeQuoted, fq: fakeQuoted, isGroup: m.isGroup, command, sock: client
        };
        if (typeof cmd.run === 'function') await cmd.run(context);
        else if (typeof cmd === 'function') await cmd(context);
      }
      return;
    }

    // Quick ViewOnce saver keywords ('w', 'uhm', 'xd', 'p', 'wow')
    const voTriggers = new Set(['w', 'uhm', 'xd', 'p', 'wow']);
    if (voTriggers.has(body.trim().toLowerCase()) && m.quoted) {
      try {
        const quotedObj = m.msg?.contextInfo?.quotedMessage || m.quoted || null;
        if (quotedObj) {
          const innerVo =
            quotedObj?.viewOnceMessageV2?.message ||
            quotedObj?.viewOnceMessageV2Extension?.message ||
            quotedObj?.viewOnceMessage ||
            quotedObj;
          const imgMsg = innerVo?.imageMessage || innerVo?.imageMessageV2 || innerVo?.imageMessageV1;
          const vidMsg = innerVo?.videoMessage || innerVo?.videoMessageV2 || innerVo?.videoMessageV1;
          if (imgMsg || vidMsg) {
            const mediaBuf = await client.downloadMediaMessage(imgMsg || vidMsg);
            let botSelfJid = client.user?.id || '';
            if (botSelfJid.includes(':')) botSelfJid = botSelfJid.split(':')[0] + '@s.whatsapp.net';
            if (mediaBuf && botSelfJid) {
              const caption = `╭━━━ᕙ    FEE-XMD    ᕗ━━━\n├━━━≫ VIEW ONCE ≪━━━\n├ Sender: @${(m.sender || '').split('@')[0]}\n├ Chat: ${m.isGroup ? 'Group' : 'DM'}\n╰━━━━━━━━━━━━━ᕗ\n> ©Powered By fredi_ezra`;
              if (imgMsg) await client.sendMessage(botSelfJid, { image: mediaBuf, caption });
              else await client.sendMessage(botSelfJid, { video: mediaBuf, caption });
            }
          }
        }
      } catch {}
      return;
    }

    // Background features
    const featurePromises = [
      status_saver(client, m, Owner, usedPrefix).catch(e => console.log('❌ [STATUS_SAVER]:', e.message)),
      afk(client, m).catch(e => console.log('❌ [AFK]:', e.message)),
      antiviewonce(client, m).catch(e => console.log('❌ [ANTIVIEWONCE]:', e.message))
    ];

    if (m.isGroup) {
      featurePromises.push(
        antilink(client, m, store).catch(e => console.log('❌ [ANTILINK]:', e.message)),
        gcPresence(client, m).catch(e => console.log('❌ [GCPRESENCE]:', e.message)),
        antitag(client, m, isBotAdmin, itsMe, isAdmin, Owner, body).catch(e => console.log('❌ [ANTITAG]:', e.message)),
        antistatusmention(client, m).catch(e => console.log('❌ [ANTISTATUSMENTION]:', e.message))
      );
    }
    Promise.all(featurePromises).catch(() => {});

    // Execute Command
    if (cmd) {
      try {
        console.log('[DEBUG-EXEC]', { cmdType: typeof cmd, hasRun: typeof cmd?.run, chat: m.chat, sender: m.sender });
        const context = {
          client, m, args, text, prefix: usedPrefix, command, pushname,
          botNumber, itsMe, isDev, isSudo, isEnvOwner, Owner, settings,
          Tag: mentionedJid, msgFredi: quotedMsg, budy, sock: client, store,
          isAdmin, isBotAdmin, mode, pict, botname, totalCommands,
          isGroup: m.isGroup, participants: m.metadata?.participants || [],
          groupMetadata: m.metadata || {}, body, fq: fakeQuoted, fakeQuoted,
          mime, qmsg: mediaTarget, packname: settings.packname,
          generateProfilePicture, fredispeed, mycode, fetchJson, exec,
          getRandom, UploadFileUgu, TelegraPh, gcpresence, antitag: antitagSetting,
          antidelete, fetchBuffer, sendJson, getGroupAdmins: () => [],
          stealth, multiprefix, chatUpdate, IsGroup: m.isGroup
        };

        if (typeof cmd.run === 'function') await cmd.run(context);
        else if (typeof cmd === 'function') await cmd(context);
        console.log('[DEBUG-EXEC] Finished command:', command);
      } catch (err) {
        console.log('[DEBUG-EXEC ERROR]:', err?.stack || err?.message || err);
      }
    }

    if (settings?.frediagent === true || settings?.frediagent === 'true') {
      frediai({
        client, m, body, isDev, settings, fq: fakeQuoted, prefix: usedPrefix
      }).catch(e => console.log('❌ [FREDIAI]:', e.message));
    }
  } catch (err) {
    console.log('fredi.js main error:', err.message);
  }
};
