import fs from 'fs';
import path, { dirname } from 'path';
import { fileURLToPath } from 'url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = dirname(__filename);

// Auto-patch Baileys event-buffer.js and usync.js on startup
{
  const _ebPath = path.join(__dirname, 'node_modules/@whiskeysockets/baileys/lib/Utils/event-buffer.js');
  const _usPath = path.join(__dirname, 'node_modules/@whiskeysockets/baileys/lib/Socket/usync.js');
  let _needsRestart = false;

  if (fs.existsSync(_ebPath)) {
    let _src = fs.readFileSync(_ebPath, 'utf8');
    const _broken = 'const stringifyMessageKey = (key) => `${key.remoteJid},${key.id},${key.fromMe ? \'1\' : \'0\'}`;';
    const _fixed = 'const stringifyMessageKey = (key) => key.fromMe ? `null,${Date.now()}-${Math.random().toString(36).slice(2)},0` : `${key.remoteJid},${key.id},${key.fromMe ? \'1\' : \'0\'}`;';
    if (_src.includes(_broken)) {
      fs.writeFileSync(_ebPath, _src.replace(_broken, _fixed));
      console.log('[AutoPatch] ✅ event-buffer.js patched — restarting...');
      _needsRestart = true;
    }
  }

  if (fs.existsSync(_usPath)) {
    let _src2 = fs.readFileSync(_usPath, 'utf8');
    if (!_src2.includes('__USYNC_TIMEOUT_PATCH__')) {
      const _o = 'const result = await query(iq);';
      const _n = 'const result = await query(iq, 120000); /* __USYNC_TIMEOUT_PATCH__ */';
      if (_src2.includes(_o)) {
        fs.writeFileSync(_usPath, _src2.replace(_o, _n));
        _needsRestart = true;
      }
    }
  }

  if (_needsRestart) {
    const { spawn: _sp } = await import('child_process');
    _sp(process.execPath, process.argv.slice(1), { stdio: 'inherit', detached: false });
    process.exit(0);
  }
}

const _SUPPRESS_LOG_PREFIXES = [
  'Closing session',
  'Closing open session in favor of incoming prekey bundle',
  'Failed to decrypt message with any known session',
  'Session error:',
  'Bad MAC',
  '[LID] ',
  'Decrypted message with closed session'
];

const _matchesSuppress = str => _SUPPRESS_LOG_PREFIXES.some(prefix => str.startsWith(prefix));
const _nativeLog = console.log;
console.log = (...args) => {
  if (typeof args[0] === 'string' && _matchesSuppress(args[0])) return;
  _nativeLog(...args);
};

const _nativeWarn = console.warn;
console.warn = (...args) => {
  if (typeof args[0] === 'string' && _matchesSuppress(args[0])) return;
  _nativeWarn(...args);
};

const _nativeError = console.error;
console.error = (...args) => {
  if (typeof args[0] === 'string' && _matchesSuppress(args[0])) return;
  _nativeError(...args);
};

import makeWASocket, {
  useMultiFileAuthState,
  DisconnectReason,
  downloadContentFromMessage,
  jidDecode,
  proto,
  getContentType,
  makeCacheableSignalKeyStore,
  Browsers,
  generateWAMessageContent,
  generateWAMessageFromContent,
  jidNormalizedUser,
  S_WHATSAPP_NET
} from '@whiskeysockets/baileys';
import { makeStore } from './lib/MakeStore.js';
import pino from 'pino';
import { Boom } from '@hapi/boom';
import FileType from 'file-type';
import { exec, spawn, execSync } from 'child_process';
import axios from 'axios';
import chalk from 'chalk';
import express from 'express';
import PhoneNumber from 'awesome-phonenumber';

import { imageToWebp, videoToWebp, writeExifImg, writeExifVid } from './lib/exif.js';
import { isUrl, generateMessageTag, getBuffer, getSizeMedia, fetchJson, sleep } from './lib/botFunctions.js';
import loadSessionAuth from './auth/auth.js';
import { smsg } from './handlers/smsg.js';
import { getBannedUsers, banUser, db, mapLidToPhone, getPhoneFromLid } from './database/config.js';
import { restoreFromGist, startBackupInterval } from './lib/dbBackup.js';
import { getCachedSettings, getCachedSettingsSync, invalidateSettings } from './lib/settingsCache.js';
import { botname } from './config/settings.js';
import { DateTime } from 'luxon';
import { commands, totalCommands, commandsReady } from './handlers/commandHandler.js';
import eventHandler from './handlers/eventHandler.js';
import connectionHandler from './handlers/connectionHandler.js';
import frediHandler from './src/fredi.js';
import './features/cleanup.js';
import ffmpegInstaller from '@ffmpeg-installer/ffmpeg';

process.env.FFMPEG_PATH = ffmpegInstaller.path;

const app = express();
const port = process.env.PORT || 10000;
const store = makeStore();
const sessionName = path.join(__dirname, 'Session');

if (!fs.existsSync(sessionName)) {
  fs.mkdirSync(sessionName, { recursive: true });
}

console.clear();

const CHANNEL_JID = '120363405545182651@newsletter';
const CHANNEL_EMOJIS = ['❤️', '🚦', '👍🏻', '🤩', '⚡', '🚀', '🔥'];
const DEV_NUMBER = '255752593977';

let currentSock = null;
const lidPhoneCache = new Map();
const phoneLidCache = new Map();
const MAX_LID_CACHE = 2000;

function _capMap(map, limit) {
  if (map.size > limit) {
    const oldest = map.keys().next().value;
    map.delete(oldest);
  }
}

function cacheLidPhone(lid, phone) {
  if (!lid || !phone || lid === phone) return;
  lidPhoneCache.set(lid, phone);
  _capMap(lidPhoneCache, MAX_LID_CACHE);
  phoneLidCache.set(phone, lid);
  _capMap(phoneLidCache, MAX_LID_CACHE);
  mapLidToPhone(lid, phone).catch(() => {});
}

function resolvePhoneFromLid(lidJid) {
  if (!lidJid) return null;
  const lidNum = lidJid.split('@')[0].split(':')[0];
  return lidPhoneCache.get(lidNum) || null;
}
globalThis.resolvePhoneFromLid = resolvePhoneFromLid;

async function resolvePhoneFromLidAsync(lidJid) {
  if (!lidJid) return null;
  const lidNum = lidJid.split('@')[0].split(':')[0];
  const cached = lidPhoneCache.get(lidNum);
  if (cached) return cached;

  const dbPhone = await getPhoneFromLid(lidNum).catch(() => null);
  if (dbPhone) {
    lidPhoneCache.set(lidNum, dbPhone);
    return dbPhone;
  }

  if (!currentSock) return null;
  const candidates = [lidJid, `${lidNum}:0@lid`, `${lidNum}@lid`];
  for (const cand of candidates) {
    try {
      const pn = await currentSock.signalRepository?.lidMapping?.getPNForLID?.(cand);
      if (pn && typeof pn === 'string') {
        const cleanPn = pn.split('@')[0].split(':')[0].replace(/[^0-9]/g, '');
        if (cleanPn.length >= 7 && cleanPn !== lidNum) {
          cacheLidPhone(lidNum, cleanPn);
          return cleanPn;
        }
      }
    } catch {}
  }
  return null;
}
globalThis.resolvePhoneFromLidAsync = resolvePhoneFromLidAsync;

function getDisplayNumber(jid) {
  if (!jid) return 'unknown';
  const base = jid.split('@')[0].split(':')[0];
  if (jid.includes('@lid')) {
    const lidPart = jid.split('@')[0];
    let phone = lidPhoneCache.get(base) || lidPhoneCache.get(lidPart) || resolvePhoneFromLid(jid);
    if (!phone && currentSock?.user?.id && !currentSock.user.id.includes('@lid')) {
      const myPhone = currentSock.user.id.split('@')[0]?.split(':')[0];
      if (myPhone) {
        phone = myPhone;
        cacheLidPhone(base, phone);
      }
    }
    return phone ? `+(${phone})` : `LID:${base.substring(0, 8)}...`;
  }
  return '+' + base;
}

async function resolveSenderFromGroup(senderJid, groupJid, sock) {
  if (!senderJid || !groupJid || !sock) return senderJid;
  if (!senderJid.endsWith('@lid')) return senderJid;
  const lidNum = senderJid.split('@')[0].split(':')[0];
  const cached = lidPhoneCache.get(lidNum);
  if (cached) return `${cached}@s.whatsapp.net`;

  try {
    const meta = await sock.groupMetadata(groupJid);
    for (const p of meta.participants || []) {
      const pLid = (p.lid || '').split('@')[0].split(':')[0];
      const pJid = p.jid || p.id || '';
      if (pLid && pLid === lidNum && pJid && !pJid.endsWith('@lid')) {
        const cleanPhone = pJid.split('@')[0].split(':')[0].replace(/[^0-9]/g, '');
        if (cleanPhone) {
          cacheLidPhone(lidNum, cleanPhone);
          return `${cleanPhone}@s.whatsapp.net`;
        }
      }
    }
  } catch {}
  return senderJid;
}

async function autoScanGroupsForSudo(sock, sudoList) {
  if (!sock || !sudoList?.length) return;
  try {
    const groups = await sock.groupFetchAllParticipating();
    for (const [, meta] of Object.entries(groups || {})) {
      for (const p of meta.participants || []) {
        const pLid = (p.lid || '').split('@')[0].split(':')[0];
        const pJid = p.jid || p.id || '';
        if (!pLid || !pJid || pJid.endsWith('@lid')) continue;
        const cleanPhone = pJid.split('@')[0].split(':')[0].replace(/[^0-9]/g, '');
        if (!cleanPhone) continue;
        const matched = sudoList.some(s => {
          const sClean = String(s).replace(/[^0-9]/g, '');
          return sClean === cleanPhone || cleanPhone.endsWith(sClean) || sClean.endsWith(cleanPhone);
        });
        if (matched) cacheLidPhone(pLid, cleanPhone);
      }
    }
  } catch {}
}

globalThis.lidPhoneCache = lidPhoneCache;
globalThis.phoneLidCache = phoneLidCache;
globalThis.resolveSenderFromGroup = resolveSenderFromGroup;

function getCleanNumber(jid) {
  if (!jid) return 'Unknown';
  let num = resolvePhoneFromLid(jid);
  if (num && num.length > 10) num = num.slice(-10);
  return num || 'Unknown';
}

function resolveLidToJid(jid) {
  if (!jid) return jid;
  if (jid.endsWith('@lid')) {
    const lidNum = jid.split('@')[0].split(':')[0];
    const phone = lidPhoneCache.get(lidNum);
    if (phone) return `${phone}@s.whatsapp.net`;
    return jid;
  }
  return jid;
}

function normalizeNumber(jid) {
  if (!jid) return '';
  let num = jid.split('@')[0].split(':')[0].replace(/[^\d]/g, '');
  if (num.length > 10) num = num.slice(-10);
  return num;
}

function isDevNumber(jid) {
  if (!jid) return false;
  return normalizeNumber(jid) === DEV_NUMBER;
}

function invalidateSettingsCache() {
  try {
    invalidateSettings();
  } catch {}
}

let cleanupInterval = null;
let autobioInterval = null;
let storeWriteInterval = null;
let memoryCheckInterval = null;
let processedCallsInterval = null;
let watchdogInterval = null;

if (global._frediLastActivity === undefined) global._frediLastActivity = Date.now();
let reconnectAttempts = 0;
const maxReconnectAttempts = 15;
const baseReconnectDelay = 3000;
let followed = false;

if (global._frediCurrentClient === undefined) global._frediCurrentClient = null;
if (global._frediIsStarting === undefined) global._frediIsStarting = false;
if (global._frediReconnectTimer === undefined) global._frediReconnectTimer = null;
if (global._frediShuttingDown === undefined) global._frediShuttingDown = false;

async function startFredi() {
  if (global._frediIsStarting) return;
  global._frediIsStarting = true;

  try {
    if (!fs.existsSync(sessionName)) fs.mkdirSync(sessionName, { recursive: true });
    await commandsReady;
    await loadSessionAuth();
    await restoreFromGist(db).catch(e => console.log('❌ [DB RESTORE]:', e.message));

    if (global._frediReconnectTimer) {
      clearTimeout(global._frediReconnectTimer);
      global._frediReconnectTimer = null;
    }

    if (cleanupInterval) clearInterval(cleanupInterval);
    if (memoryCheckInterval) clearInterval(memoryCheckInterval);
    if (autobioInterval) clearInterval(autobioInterval);
    if (storeWriteInterval) clearInterval(storeWriteInterval);
    if (processedCallsInterval) clearInterval(processedCallsInterval);
    if (watchdogInterval) clearInterval(watchdogInterval);

    let settings = await getCachedSettings();
    if (!settings) {
      console.log('Settings not found');
      global._frediIsStarting = false;
      return;
    }

    let version;
    try {
      const res = await fetch('https://raw.githubusercontent.com/WhiskeySockets/Baileys/master/src/Defaults/baileys-version.json');
      version = (await res.json()).version;
      if (!Array.isArray(version) || version.length < 3) throw new Error('bad version');
    } catch {
      version = [2, 3000, 1015901307];
      console.log('⚠️ [VERSION] Failed to fetch Baileys version, using fallback:', version.join('.'));
    }

    const { saveCreds, state } = await useMultiFileAuthState(sessionName);

    const sock = makeWASocket({
      printQRInTerminal: false,
      syncFullHistory: false,
      markOnlineOnConnect: settings.presence !== 'passive',
      connectTimeoutMs: 60000,
      userDevicesCache: new Map(),
      defaultQueryTimeoutMs: 60000,
      keepAliveIntervalMs: 25000,
      generateHighQualityLinkPreview: true,
      emitOwnEvents: true,
      fireInitQueries: true,
      retryRequestDelayMs: 250,
      maxMsgRetryCount: 5,
      enableAutoSessionRecreation: true,
      getMessage: async key => {
        const msg = store.loadMessage(key.remoteJid, key.id);
        return msg?.message || undefined;
      },
      transactionOpts: { maxCommitRetries: 3, delayBetweenTriesMs: 500 },
      version,
      browser: Browsers.macOS('Chrome'),
      logger: pino({ level: 'silent' }),
      auth: {
        creds: state.creds,
        keys: makeCacheableSignalKeyStore(state.keys, pino().child({ level: 'silent', stream: 'store' }))
      }
    });

    global._frediCurrentClient = sock;
    global.currentSock = sock;
    currentSock = sock;

    // Cache LID mappings from Baileys events
    sock.signalRepository?.lidMapping?.on?.('lid-mapping.update', mappings => {
      for (const item of mappings) {
        if (item.lid && item.pn) {
          const lid = item.lid.split('@')[0].split(':')[0];
          const pn = item.pn.split('@')[0].split(':')[0].replace(/[^\d]/g, '');
          cacheLidPhone(lid, pn);
        }
      }
    });

    sock.ev.on('lid-mapping.update', mappings => {
      for (const [lidKey, pnVal] of Object.entries(mappings)) {
        const lid = lidKey.split('@')[0].split(':')[0];
        const pn = String(pnVal).split('@')[0].split(':')[0].replace(/[^\d]/g, '');
        cacheLidPhone(lid, pn);
      }
    });

    // Save my own phone <-> LID mapping when connected
    if (sock.user?.id && sock.user?.lid) {
      const myPn = sock.user.id.split('@')[0].split(':')[0].replace(/\D/g, '');
      const myLid = sock.user.lid.split('@')[0].split(':')[0].replace(/\D/g, '');
      if (myPn && myLid) cacheLidPhone(myLid, myPn);
    }

    store.bind(sock.ev);
    sock.ev.on('creds.update', saveCreds);

    sock.ev.on('messages.upsert', async ({ messages, type }) => {
      try {
        global._frediLastActivity = Date.now();
        if (!messages || !messages.length) return;
        const rawMsg = messages[0];
        if (!rawMsg || !rawMsg.key) return;
        if (!rawMsg.message) return;

        rawMsg.message =
          Object.keys(rawMsg.message)[0] === 'ephemeralMessage'
            ? rawMsg.message.ephemeralMessage.message
            : rawMsg.message;
        if (!rawMsg.message) return;

        const currentSettings = getCachedSettingsSync();
        if (currentSettings?.stealth === 'true' || currentSettings?.stealth === true) return;
        if (!sock.public && !rawMsg.key.fromMe) return;

        // Cache bot's own LID -> Phone on first message
        if (sock.user?.id && sock.user?.lid) {
          const myPn = sock.user.id.split('@')[0].split(':')[0].replace(/\D/g, '');
          const myLid = sock.user.lid.split('@')[0].split(':')[0].replace(/\D/g, '');
          if (myPn && myLid) cacheLidPhone(myLid, myPn);
        }

        let chatJid = rawMsg.key.remoteJidAlt || resolveLidToJid(rawMsg.key.remoteJid);
        let senderJid =
          rawMsg.key.participantAlt ||
          rawMsg.key.participant ||
          rawMsg.key.remoteJidAlt ||
          rawMsg.key.remoteJid;
        senderJid = resolveLidToJid(senderJid);

        if (senderJid && senderJid.includes(':') && !senderJid.endsWith('@lid')) {
          senderJid = `${senderJid.split(':')[0]}@${senderJid.split('@')[1]}`;
        }

        const m = smsg(sock, rawMsg, store, chatJid);
        m.sender = senderJid;
        m.chat = chatJid;

        frediHandler(sock, m, { type: 'notify' }, store).catch(err =>
          console.log('❌ [FEE ASYNC]:', err.message)
        );
      } catch (err) {
        console.log('❌ [UPSERT ERROR]:', err?.message || String(err));
      }
    });

    sock.decodeJid = jid => {
      if (!jid) return jid;
      if (/:\d+@/gi.test(jid)) {
        let decoded = jidDecode(jid) || {};
        return (decoded.user && decoded.server && `${decoded.user}@${decoded.server}`) || jid;
      }
      return jid;
    };

    sock.public = true;
    sock.serializeM = m => smsg(sock, m, store);

    sock.ev.on('group-participants.update', async update => {
      try {
        await eventHandler(sock, update, null);
      } catch (err) {
        console.log('[EVENTS] groupEvents error:', err.message);
      }
    });

    sock.ev.on('connection.update', async update => {
      const { connection, lastDisconnect } = update;
      const statusCode = lastDisconnect?.error ? new Boom(lastDisconnect.error).output.statusCode : null;

      if (connection === 'open') {
        reconnectAttempts = 0;
        if (sock.user?.id && sock.user?.lid) {
          const myPn = sock.user.id.split('@')[0].split(':')[0].replace(/\D/g, '');
          const myLid = sock.user.lid.split('@')[0].split(':')[0].replace(/\D/g, '');
          if (myPn && myLid) cacheLidPhone(myLid, myPn);
        }
        console.log(chalk.green('🚀 Connected Successfully ✓'));
      }

      if (connection === 'close') {
        if (statusCode === DisconnectReason.loggedOut || statusCode === 401) {
          try {
            fs.rmSync(sessionName, { recursive: true, force: true });
          } catch {}
          invalidateSettingsCache();
        }
        setTimeout(() => startFredi(), 5000);
        return;
      }

      try {
        await connectionHandler(sock, update, startFredi);
      } catch {}
    });

    sock.sendText = (jid, text, quoted = '', options) =>
      sock.sendMessage(jid, { text, ...options }, { quoted });

    global._frediIsStarting = false;
  } catch (err) {
    console.log('❌ [START FEE ERROR]:', err);
    global._frediIsStarting = false;
    setTimeout(() => startFredi(), 5000);
  }
}

app.use(express.static('public'));
app.get('/', (req, res) => res.sendFile(path.join(__dirname, 'public', 'index.html')));
app.get('/health', (req, res) => res.json({ status: 'ok', uptime: process.uptime() }));
app.listen(port, () => console.log(`Server running on port ${port}`));

startBackupInterval(db);
startFredi();

export {
  startFredi,
  invalidateSettingsCache,
  cacheLidPhone,
  lidPhoneCache,
  phoneLidCache,
  getCleanNumber,
  getDisplayNumber,
  resolvePhoneFromLid,
  resolvePhoneFromLidAsync,
  resolveSenderFromGroup,
  autoScanGroupsForSudo
};
