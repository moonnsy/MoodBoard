import { getContext } from '../../../extensions.js';
import { eventSource, event_types } from '../../../../script.js';

const EXT = 'MoodBoard', LOG = `[${EXT}]`;
const BOARD_SIZE = 4000;              // logical board coordinate space
// Ceiling for "how much of the chat travels with the board". 50 was a guess from
// when the whole request was one string; the turns are sent as turns now, so the
// only real limit is the model's own context.
const CTX_MAX = 300;
const DRAW_RES = 2000;                // backing-store size of the drawing canvas (halves GPU memory)
const DRAW_SCALE = DRAW_RES / BOARD_SIZE;
let boards = { global: { cards: [] } };
let scope = 'chat';
let tool = 'select';
let drawColor = '#e74c3c', drawSize = 3, cardColors = ['#fdf6e3','#ffe4e1','#e0f0ff','#e8ffe0','#fff3cd','#f0e0ff'];
let panX = 0, panY = 0, zoom = 1, isPanning = false, panOff = { x:0, y:0 };
let dragCard = null, drawCtx = null, isDrawing = false;
// Assigned in bindEvents; togglePanel calls it after dismissing the keyboard.
let syncViewport = null;
// Last values written to --mb-vh / --mb-vtop, so a re-measure that changes
// nothing costs nothing.
let lastVh = -1, lastVtop = -1;
let vpPokeTimer = null, vpPokeLeft = 0;
// Is the on-screen keyboard plausibly up? Only a text-entry element can raise it.
function isTypingTarget(el) {
    return !!el && (el.isContentEditable === true ||
        /^(input|textarea|select)$/i.test(el.tagName || ''));
}
// Re-measures the viewport a handful of times over the next second. The keyboard
// animates in and out, and on Android the resize event for the *end* of that
// animation is routinely missing — one measurement is not enough.
function pokeViewport(times = 8) {
    if (typeof syncViewport !== 'function') return;
    vpPokeLeft = Math.max(vpPokeLeft, times);
    syncViewport();
    if (vpPokeTimer) return;
    vpPokeTimer = setInterval(() => {
        syncViewport();
        if (--vpPokeLeft <= 0) { clearInterval(vpPokeTimer); vpPokeTimer = null; }
    }, 140);
}
// Last resort against a layout frozen at keyboard height. Every event-driven
// recovery depends on some event actually arriving, and on Android there is
// always one browser that delivers none of them — leaving the window stuck until
// the page is reloaded. This just checks, twice a second, that the size on screen
// still matches reality. syncViewport writes nothing when it already does, so the
// cost of being wrong here is two number comparisons.
//
// Once a second rather than twice: this is a safety net for an event that failed
// to arrive, not a mechanism anything depends on, and it ticks for as long as the
// board is open.
let vpWatchTimer = null;
function startViewportWatch() {
    if (vpWatchTimer) return;
    vpWatchTimer = setInterval(() => {
        if (!document.getElementById('mb-modal') || !$('#mb-modal').is(':visible')) {
            clearInterval(vpWatchTimer); vpWatchTimer = null; return;
        }
        syncViewport?.();
    }, 1000);
}
let settingsOpen = false, aiPanelOpen = false, zoomTimer = null;
// Pinch zoom state
let pinchDist = 0, pinchZoomStart = 1, pinchPanStart = { x:0, y:0 }, pinchMid = { x:0, y:0 };
let activeTouches = 0, isPinching = false;
// Live-stroke state: strokes are previewed on a viewport-sized overlay and only
// committed to the big board canvas on pointerup, so a pinch can cancel them cleanly.
let liveCanvas = null, liveCtx = null, strokePts = [];
// Second ink canvas, stacked above the cards, for drawing on top of photos.
let topCanvas = null, topCtx = null;
let brushKind = 'pen', drawAbove = false;
// ===== GRID =====
// A view preference rather than board content: the same board looks the same
// everywhere, but whether *you* want lines under it is your business, so it
// lives in localStorage next to the brush settings.
let gridShow = false, gridSnap = false, gridSize = 40;
// ===== CONNECTORS =====
// While the link tool is pulling a thread out of a card. `to` is in board coords.
let linkDraft = null;
// Card box sizes read from the DOM. Positions always come from the card data, so
// this only has to be rebuilt when a card is added, removed, resized or re-laid
// out — not on every pan frame.
let linkGeom = new Map(), linkGeomDirty = true;
let activeLink = null;          // the connector whose menu is open
// ===== LONG PRESS =====
// A tap and a long press start identically; which one it was only becomes clear
// 450ms in. When the press wins, the browser still delivers a `click` on
// release — and that click would both re-trigger the button's own action and
// count as "a click outside", closing the panel the press just opened. So the
// moment a hold acts is remembered, and every tap handler and every
// close-on-outside-click handler ignores what arrives immediately after.
let holdActedAt = 0;
function markHold() { holdActedAt = Date.now(); }
function holdJustFired() { return Date.now() - holdActedAt < 800; }

function scopeKey() {
    const c = getContext();
    if (scope === 'global') return 'global';
    if (scope === 'char') return 'char_' + (c.name2 || 'unknown');
    return 'chat_' + (c.chatId || c.chat_id || 'default');
}

// ===== BOARD TABS =====
// Each scope (chat / character / global) can hold several boards. The tab list
// lives under `_tabs`, keyed by scope; the first tab keeps the bare scope key so
// boards made before tabs existed stay exactly where they were.
const MAIN_TAB = 'main';
function tabsMeta() {
    if (!boards._tabs || typeof boards._tabs !== 'object') boards._tabs = {};
    const sk = scopeKey();
    let m = boards._tabs[sk];
    if (!m || !Array.isArray(m.list) || !m.list.length) {
        m = boards._tabs[sk] = { list: [{ id: MAIN_TAB, name: 'Доска 1' }], active: MAIN_TAB };
    }
    if (!m.list.some(t => t.id === m.active)) m.active = m.list[0].id;
    return m;
}
function tabBoardKey(tabId) {
    const sk = scopeKey();
    return tabId === MAIN_TAB ? sk : `${sk}::${tabId}`;
}
function boardKey() { return tabBoardKey(tabsMeta().active); }
function getBoard() { const k = boardKey(); if (!boards[k]) boards[k] = { cards: [], drawings: '' }; return boards[k]; }
function genId() { return Math.random().toString(36).substr(2, 9); }

// ===== STORAGE =====
// Boards live on the server, in the user's own files directory, so the same
// boards appear on every device and clearing browser data cannot lose them.
//
// They are NOT kept in Tavern's extensionSettings: saving those re-uploads the
// whole settings.json — ~10MB here, nearly all of it other extensions — and over
// a phone connection that request simply fails, which is how work used to get
// lost. Uploading one file of our own avoids that entirely.
//
// IndexedDB stays on as a local cache: it is written instantly on every edit, so
// nothing is riding on the network round-trip, and it is what we fall back to if
// the server cannot be reached.
const SERVER_FILE = 'moodboard_data.json';
const SERVER_PATH = '/user/files/' + SERVER_FILE;
let serverRev = 0;              // revision we last read or wrote
let serverOk = true;            // false once an upload has failed
let serverStamp = '';           // ETag/Last-Modified of the copy we already have
let uploadTimer = null, uploading = false, uploadAgain = false;

function stHeaders() {
    const c = typeof getContext === 'function' ? getContext() : null;
    const h = (typeof c?.getRequestHeaders === 'function') ? c.getRequestHeaders() : {};
    h['Content-Type'] = 'application/json';
    return h;
}

function setSyncState(state) {
    $('#mb-sync').attr('data-state', state);
    $('#mb-sync-text').text(
        state === 'saving' ? 'Сохраняю на сервер…' :
        state === 'error'  ? 'Сервер не отвечает — правки ждут в локальной копии' :
                              'Доски сохраняются на сервере');
}

// Identifies the version of the file on disk without downloading it.
function fileStamp(res) {
    return res.headers.get('etag') || res.headers.get('last-modified') || '';
}
async function serverRead() {
    // Cache-buster: this file changes constantly and must never come from cache.
    const res = await fetch(SERVER_PATH + '?t=' + Date.now(), { cache: 'no-store' });
    if (res.status === 404) return null;
    if (!res.ok) throw new Error('HTTP ' + res.status);
    serverStamp = fileStamp(res);
    const text = await res.text();
    if (!text.trim()) return null;
    return JSON.parse(text);
}
// Records the stamp of the file we just wrote, so opening the board afterwards
// does not download and re-parse our own upload.
async function refreshStamp() {
    try {
        const res = await fetch(SERVER_PATH + '?t=' + Date.now(), { method: 'HEAD', cache: 'no-store' });
        if (res.ok) serverStamp = fileStamp(res);
    } catch (e) {}
}

// ===== IMAGE STORE =====
// Pictures used to live inside the boards file as `data:` URLs, and that one
// decision was the most expensive thing in the extension. Every save had to
// re-clone, re-stringify and re-upload every photo on every board, because they
// were all one JSON document — pinning a picture during a chat cost a full
// megabyte-scale round of work, and so did nudging a card afterwards.
//
// A `data:` URL is also a JavaScript string, which means the browser must keep
// its decoded bitmap alive for as long as the string is reachable. It can never
// be evicted under memory pressure. That is what leaves a phone hot with the
// board just sitting open.
//
// So each picture is now its own file beside the boards file, and the card holds
// a path. The boards JSON stays in the kilobytes no matter how many photos are
// pinned, and every <img> is an ordinary cacheable, evictable resource.
//
// Nothing here is load-bearing: if an upload fails, the data URL is kept as-is
// and everything downstream still works, because every consumer only ever hands
// the value to an <img src> or to `new Image()`. Both forms are equally valid
// there. That is the whole compatibility story — there is no second code path.
const IMG_PREFIX = 'mb_img_';
// source string -> Promise<path>, for uploads that are in flight *right now*, so
// two callers handing over the same picture at the same time get one file rather
// than two. Entries are dropped the moment the upload settles, and that matters:
// the key is the data URL itself, so a surviving entry would pin a megabyte of
// string in memory long after the board had stopped referring to it.
const imgUploads = new Map();

// Whether this server can hold our pictures at all. Not every SillyTavern is the
// same age, and an older /api/files/upload may not take what we send. Until one
// tiny probe file has made the round trip, nothing large is attempted — the
// alternative is discovering the problem one megabyte at a time, which is how a
// phone ends up hot with nothing to show for it.
let imgStore = 'unknown';           // 'unknown' | 'ok' | 'off'
let imgStoreProbe = null;
let imgFailStreak = 0;

function isDataUrl(s) { return typeof s === 'string' && s.startsWith('data:'); }
// Everything the extension stores that is not a data URL is already a path we
// wrote ourselves, so this is only ever asked about strings that hold pixels.
function isStoredImg(s) { return typeof s === 'string' && s.includes('/' + IMG_PREFIX); }

const IMG_EXT = { 'image/webp': 'webp', 'image/png': 'png', 'image/jpeg': 'jpg', 'image/gif': 'gif' };
// Deliberately not a regular expression. These strings run to millions of
// characters, and a pattern ending in `(.+)$` makes the engine walk and then
// copy the whole payload — per picture, on the main thread. indexOf and slice
// do neither: V8 hands back a view onto the original string.
function splitDataUrl(src) {
    if (!isDataUrl(src)) return null;
    const comma = src.indexOf(',');
    if (comma < 0) return null;
    const head = src.slice(5, comma);                 // past "data:"
    if (!head.endsWith(';base64')) return null;       // only base64 payloads
    const ext = IMG_EXT[head.slice(0, -7).toLowerCase()];
    if (!ext) return null;                            // not something we can name
    return { ext, b64: src.slice(comma + 1) };
}

// Names are random rather than a hash of the content. Hashing meant a
// per-character pass over a multi-megabyte string for every single picture, and
// on a phone that is seconds of blocked main thread each — the exact cost this
// whole change exists to remove. Two copies of one picture costing two files is
// a much better trade than that.
function imgFileName(ext) { return IMG_PREFIX + genId() + Date.now().toString(36) + '.' + ext; }

async function putImageFile(name, b64) {
    // Built by concatenation, not JSON.stringify: base64 contains nothing JSON
    // has to escape, so stringify would only mean one more full scan and one
    // more full copy of the payload.
    const body = '{"name":"' + name + '","data":"' + b64 + '"}';
    const res = await fetch('/api/files/upload', { method: 'POST', headers: stHeaders(), body });
    if (!res.ok) throw new Error('HTTP ' + res.status + ' ' + (await res.text()).slice(0, 120));
    const out = await res.json().catch(() => null);
    const p = out?.path || ('user/files/' + name);
    return p.startsWith('/') ? p : '/' + p;
}

// One 43-byte file, written and read back. Cheap enough to be free, and it is
// the difference between "this works here" and grinding a phone through a whole
// board's worth of uploads that were never going to land.
function probeImageStore() {
    if (imgStore !== 'unknown') return Promise.resolve(imgStore === 'ok');
    if (imgStoreProbe) return imgStoreProbe;
    imgStoreProbe = (async () => {
        try {
            const path = await putImageFile(IMG_PREFIX + 'probe.gif', BLANK_PX.slice(BLANK_PX.indexOf(',') + 1));
            const back = await fetch(path, { cache: 'no-store' });
            if (!back.ok) throw new Error('read back HTTP ' + back.status);
            imgStore = 'ok';
        } catch (e) {
            imgStore = 'off';
            console.warn(LOG, 'this server will not hold image files; pictures stay inside the boards file', e);
        }
        return imgStore === 'ok';
    })();
    return imgStoreProbe;
}

// Moves one data URL out to a file and answers with its path. Anything it cannot
// handle comes back unchanged, which is always safe — see the note above.
async function storeImage(src) {
    if (!isDataUrl(src)) return src;
    if (!await probeImageStore()) return src;
    const hit = imgUploads.get(src);
    if (hit) { try { return await hit; } catch (e) { return src; } }
    const parts = splitDataUrl(src);
    if (!parts) return src;
    const job = putImageFile(imgFileName(parts.ext), parts.b64);
    imgUploads.set(src, job);
    try {
        const path = await job;
        imgFailStreak = 0;
        return path;
    } catch (e) {
        console.warn(LOG, 'image upload failed, keeping it inline', e);
        // A server that refuses three in a row is not going to take the fourth,
        // and retrying is what turns a bad connection into a hot phone.
        if (++imgFailStreak >= 3) {
            imgStore = 'off';
            console.warn(LOG, 'giving up on the image store for this session');
        }
        return src;
    } finally {
        imgUploads.delete(src);
    }
}

// Several at once, in order, for the places that make a pair or a whole collage.
function storeImages(list) { return Promise.all((list || []).map(s => storeImage(s))); }

// The reverse trip, for the few callers that genuinely need bytes rather than a
// src — re-encoding an existing picture, mainly.
async function imgAsDataUrl(src) {
    if (!src || isDataUrl(src)) return src;
    try {
        const res = await fetch(src, { cache: 'force-cache' });
        if (!res.ok) throw new Error('HTTP ' + res.status);
        const blob = await res.blob();
        return await new Promise((resolve, reject) => {
            const fr = new FileReader();
            fr.onload = () => resolve(fr.result);
            fr.onerror = reject;
            fr.readAsDataURL(blob);
        });
    } catch (e) {
        console.warn(LOG, 'could not read back', src, e);
        return src;
    }
}

// Puts every stored picture back inline, in place, across a whole set of boards.
// Only the backup export wants this: a file that leaves this machine cannot
// refer to files that live on it. Operates on the copies IndexedDB just handed
// back, never on the live boards.
async function inlineStoredImages(map) {
    const seen = new Map();     // one read per distinct picture, however many cards use it
    for (const board of Object.values(map || {})) {
        if (!board || typeof board !== 'object') continue;
        for (const [obj, key] of imageSlots(board)) {
            const v = obj?.[key];
            if (!isStoredImg(v)) continue;
            if (!seen.has(v)) seen.set(v, await imgAsDataUrl(v));
            obj[key] = seen.get(v);
        }
    }
}

// The file holds every image on every board, so this is the single most expensive
// thing the extension does: stringify, UTF-8 encode, base64, upload. On the main
// thread that is a visible freeze on a phone — a second or more with a busy
// board. A worker does the same work off-thread, and the only cost left here is
// handing it the data. If a worker cannot be created (a strict CSP, say), the old
// main-thread path is still there.
const UPLOAD_WORKER_SRC = `
self.onmessage = async (e) => {
    const { id, url, headers, name, payload } = e.data;
    try {
        const json = JSON.stringify(payload);
        // btoa only handles latin1, and boards are full of Cyrillic and base64 images.
        const bytes = new TextEncoder().encode(json);
        let bin = '';
        const CH = 0x8000;
        for (let i = 0; i < bytes.length; i += CH) {
            bin += String.fromCharCode.apply(null, bytes.subarray(i, i + CH));
        }
        const res = await fetch(url, {
            method: 'POST', headers,
            body: JSON.stringify({ name, data: btoa(bin) }),
        });
        if (!res.ok) {
            const text = (await res.text()).slice(0, 120);
            self.postMessage({ id, ok: false, http: true, err: 'HTTP ' + res.status + ' ' + text });
            return;
        }
        self.postMessage({ id, ok: true, size: json.length });
    } catch (err) {
        self.postMessage({ id, ok: false, http: false, err: String(err && err.message || err) });
    }
};`;

let uploadWorker = null, workerUnusable = false, workerJobId = 0;
const workerJobs = new Map();
function getUploadWorker() {
    if (workerUnusable) return null;
    if (uploadWorker) return uploadWorker;
    try {
        const url = URL.createObjectURL(new Blob([UPLOAD_WORKER_SRC], { type: 'text/javascript' }));
        uploadWorker = new Worker(url);
        URL.revokeObjectURL(url);
        uploadWorker.onmessage = (e) => {
            const job = workerJobs.get(e.data?.id);
            if (!job) return;
            workerJobs.delete(e.data.id);
            clearTimeout(job.timer);
            if (e.data.ok) job.resolve(e.data.size);
            else job.reject(Object.assign(new Error(e.data.err || 'upload failed'), { mbHttp: !!e.data.http }));
        };
        uploadWorker.onerror = () => killUploadWorker('worker error');
        return uploadWorker;
    } catch (e) {
        console.warn(LOG, 'upload worker unavailable, saving on the main thread', e);
        workerUnusable = true;
        return null;
    }
}
// Anything that means the worker itself is broken: retire it and let the caller
// fall back, rather than reporting a save failure the server never saw.
function killUploadWorker(why) {
    console.warn(LOG, 'upload worker retired:', why);
    try { uploadWorker?.terminate(); } catch (e) {}
    uploadWorker = null;
    workerUnusable = true;
    for (const [, job] of workerJobs) {
        clearTimeout(job.timer);
        job.reject(Object.assign(new Error(why), { mbWorkerDead: true }));
    }
    workerJobs.clear();
}
function workerWrite(w, payload) {
    return new Promise((resolve, reject) => {
        const id = ++workerJobId;
        const timer = setTimeout(() => {
            if (workerJobs.has(id)) killUploadWorker('no answer in 60s');
        }, 60000);
        workerJobs.set(id, { resolve, reject, timer });
        try {
            w.postMessage({
                id, url: location.origin + '/api/files/upload',
                headers: stHeaders(), name: SERVER_FILE, payload,
            });
        } catch (e) {
            // Structured clone refused the payload — nothing a retry can fix.
            workerJobs.delete(id); clearTimeout(timer);
            killUploadWorker('payload not cloneable');
            reject(Object.assign(e, { mbWorkerDead: true }));
        }
    });
}

async function serverWrite(payload) {
    const w = getUploadWorker();
    if (w) {
        try { return await workerWrite(w, payload); }
        catch (e) {
            if (e.mbHttp) throw e;             // the server answered, and said no
            if (!e.mbWorkerDead) throw e;      // a real network failure
            // otherwise: worker is gone, do it here
        }
    }
    return serverWriteMain(payload);
}

async function serverWriteMain(payload) {
    const json = JSON.stringify(payload);
    // btoa only handles latin1, and boards are full of Cyrillic and base64 images.
    const bytes = new TextEncoder().encode(json);
    let bin = '';
    const CH = 0x8000;
    for (let i = 0; i < bytes.length; i += CH) {
        bin += String.fromCharCode.apply(null, bytes.subarray(i, i + CH));
    }
    const res = await fetch('/api/files/upload', {
        method: 'POST', headers: stHeaders(),
        body: JSON.stringify({ name: SERVER_FILE, data: btoa(bin) }),
    });
    if (!res.ok) throw new Error('HTTP ' + res.status + ' ' + (await res.text()).slice(0, 120));
    return json.length;
}

// Coalesced upload of the whole set. One board edit is small, but the file holds
// the images too, so this waits for a pause rather than firing per gesture.
function queueUpload(immediate) {
    clearTimeout(uploadTimer);
    if (immediate) { runUpload(); return; }
    uploadTimer = setTimeout(runUpload, 1500);
}
// True while a finger is on the board. Serializing a big board mid-gesture is
// exactly the hitch this is here to avoid, so the save waits for the hand to lift.
function gestureActive() {
    return isPanning || isDrawing || isPinching || !!dragCard;
}
async function runUpload() {
    uploadTimer = null;
    if (gestureActive()) { uploadTimer = setTimeout(runUpload, 500); return; }
    // Pictures are being moved out right now, which means the file is still
    // carrying most of them. Sending it repeatedly through that window is
    // megabytes of upload competing with the image uploads for the same
    // connection — and it is all superseded by the one save at the end.
    if (migrating) { uploadTimer = setTimeout(runUpload, 1500); return; }
    if (uploading) { uploadAgain = true; return; }   // never overlap two writes
    uploading = true;
    setSyncState('saving');
    try {
        serverRev++;
        await serverWrite({ _mb: 'moodboard', rev: serverRev, at: Date.now(), boards });
        serverOk = true;
        setSyncState('ok');
        refreshStamp();
    } catch (e) {
        console.error(LOG, 'server save failed', e);
        serverOk = false;
        setSyncState('error');
        if (!saveWarned && typeof toastr !== 'undefined') {
            saveWarned = true;
            toastr.error('Не удалось сохранить доски на сервер. Локальная копия цела — проверьте связь.', '', { timeOut: 8000 });
        }
    } finally {
        uploading = false;
        if (uploadAgain) { uploadAgain = false; queueUpload(); }
    }
}

// Picks up edits made on another device.
async function pullIfNewer(announce) {
    try {
        // Ask what version is on disk before pulling it: the file carries every
        // image on every board, and downloading plus re-parsing megabytes just to
        // find out nothing changed is a stall you can feel when opening the board.
        if (serverStamp) {
            try {
                const head = await fetch(SERVER_PATH + '?t=' + Date.now(), { method: 'HEAD', cache: 'no-store' });
                if (head.ok && fileStamp(head) === serverStamp) return false;
            } catch (e) { /* no HEAD, no problem — fall through to the full read */ }
        }
        const data = await serverRead();
        if (!data || typeof data.rev !== 'number' || data.rev <= serverRev) return false;
        serverRev = data.rev;
        boards = data.boards || {};
        // Handed over live: IndexedDB structured-clones what it is given, so the
        // JSON round trip that used to be here was a second full copy of every
        // board — on the main thread, in the middle of opening the board.
        for (const [k, v] of Object.entries(boards)) idbPut(k, v).catch(() => idbPut(k, structuredCloneSafe(v)).catch(() => {}));
        if ($('#mb-modal').is(':visible')) renderBoard();
        if (announce && typeof toastr !== 'undefined') toastr.info('Доски обновлены с другого устройства');
        return true;
    } catch (e) { return false; }
}

const DB_NAME = 'MoodBoardDB', DB_VERSION = 1, STORE = 'boards';
let dbPromise = null;

function openDb() {
    if (dbPromise) return dbPromise;
    dbPromise = new Promise((resolve, reject) => {
        const req = indexedDB.open(DB_NAME, DB_VERSION);
        req.onupgradeneeded = () => {
            const db = req.result;
            if (!db.objectStoreNames.contains(STORE)) db.createObjectStore(STORE);
        };
        req.onsuccess = () => resolve(req.result);
        req.onerror = () => reject(req.error);
    }).catch(e => { dbPromise = null; throw e; });
    return dbPromise;
}
function idbTx(mode, fn) {
    return openDb().then(db => new Promise((resolve, reject) => {
        const tx = db.transaction(STORE, mode);
        const store = tx.objectStore(STORE);
        let out;
        try { out = fn(store); } catch (e) { reject(e); return; }
        tx.oncomplete = () => resolve(out && 'result' in out ? out.result : out);
        tx.onerror = () => reject(tx.error);
        tx.onabort = () => reject(tx.error);
    }));
}
const idbPut = (key, val) => idbTx('readwrite', s => s.put(val, key));
const idbDelete = key => idbTx('readwrite', s => s.delete(key));
const idbGetAll = () => idbTx('readonly', s => {
    const keys = s.getAllKeys(), vals = s.getAll();
    return { get result() { return keys.result.map((k, i) => [k, vals.result[i]]); } };
});

let saveTimer = null, saveWarned = false;
const dirtyBoards = new Set();

async function flushSave() {
    saveTimer = null;
    // Never in the middle of a gesture: on a board full of images this is heavy
    // enough to be felt under the finger.
    if (gestureActive()) { saveTimer = setTimeout(flushSave, 400); return; }
    // 'global' carries stickers, pinned colours and the API profile, so it is
    // always a candidate alongside whichever board is on screen.
    dirtyBoards.add(boardKey()); dirtyBoards.add('global'); dirtyBoards.add('_tabs');
    const keys = [...dirtyBoards];
    dirtyBoards.clear();
    // Local cache first — instant, and it means a failed upload never costs work.
    for (const k of keys) {
        if (!boards[k]) continue;
        try {
            // Hand IndexedDB the live object: it structured-clones internally, and
            // the JSON round trip below used to do that same work twice over —
            // once to a string and once back — for every image on the board.
            await idbPut(k, boards[k]);
        } catch (e) {
            try { await idbPut(k, structuredCloneSafe(boards[k])); }
            catch (e2) { console.warn(LOG, 'local cache write failed', e2); }
        }
    }
    queueUpload();
}
// IndexedDB rejects anything it can't structured-clone (DOM nodes, functions).
// Boards are plain data, but a stray reference would silently kill every save,
// so normalise through JSON first.
function structuredCloneSafe(v) {
    try { return JSON.parse(JSON.stringify(v)); } catch (e) { return v; }
}
function save(immediate) {
    dirtyBoards.add(boardKey());
    // Anything worth saving can have changed a card's size — a note's text, its
    // font, its frame. Connectors measure cards from the DOM, so this is the one
    // place that reliably knows those measurements may be stale.
    linkGeomDirty = true;
    clearTimeout(saveTimer);
    if (immediate) { flushSave(); return; }
    saveTimer = setTimeout(flushSave, 600);
}

// The board canvas is huge; toDataURL() on it blocks for hundreds of ms on phones.
// Only do it once the user has stopped drawing.
let drawSaveTimer = null;
function serializeDrawing() {
    clearTimeout(drawSaveTimer); drawSaveTimer = null;
    const cv = document.getElementById('mb-draw-canvas');
    if (!cv) return;
    try { getBoard().drawings = cv.toDataURL('image/webp', 0.85); } catch(e) { console.warn(LOG, e); }
}
function saveDrawing() {
    clearTimeout(drawSaveTimer);
    drawSaveTimer = setTimeout(() => { serializeDrawing(); save(); }, 700);
}
// Adds boards that exist only in this device's cache into `target`. Never
// replaces a board the server already has, and never deletes anything — the
// worst case is a board reappearing, which beats one disappearing.
async function mergeLocalCacheInto(target) {
    const added = [];
    try {
        const rows = await idbGetAll();
        for (const [k, v] of rows) {
            if (!v || typeof v !== 'object') continue;
            if (k === '_tabs') {   // bookkeeping, not a board: fill in missing scopes only
                if (!target._tabs) target._tabs = {};
                for (const [sk, meta] of Object.entries(v)) {
                    if (!target._tabs[sk]) target._tabs[sk] = meta;
                }
                continue;
            }
            const hasContent = (v.cards || []).length || (v.strokes || []).length ||
                               (v.aiHistory || []).length || (v.stickers || []).length ||
                               (v.frames || []).length || (v.fonts || []).length || v.drawings;
            if (!hasContent) continue;
            const cur = target[k];
            const curEmpty = !cur || (!(cur.cards || []).length && !(cur.strokes || []).length &&
                                      !(cur.aiHistory || []).length && !(cur.stickers || []).length &&
                                      !(cur.frames || []).length && !(cur.fonts || []).length && !cur.drawings);
            if (curEmpty) { target[k] = v; added.push(k); }
        }
    } catch (e) { console.warn(LOG, 'cache merge skipped', e); }
    return added;
}

// Order of preference: the server copy (shared by every device), then the local
// cache, then whatever the older builds left behind.
async function load() {
    // 1. The server is the source of truth.
    try {
        const data = await serverRead();
        if (data && data.boards && Object.keys(data.boards).length) {
            boards = data.boards;
            serverRev = typeof data.rev === 'number' ? data.rev : 1;
            serverOk = true;
            // A device that has boards the server has never seen must not lose
            // them just because some other device wrote first. Fold them in and
            // push the result back; this only ever adds.
            const added = await mergeLocalCacheInto(boards);
            for (const [k, v] of Object.entries(boards)) idbPut(k, structuredCloneSafe(v)).catch(() => {});
            if (added.length) {
                console.log(LOG, 'merged local-only boards to server:', added);
                queueUpload(true);
                if (typeof toastr !== 'undefined') toastr.info(`Добавлено на сервер досок: ${added.length}`);
            }
            console.log(LOG, 'loaded', Object.keys(boards).length, 'boards from server (rev', serverRev + ')');
            return;
        }
    } catch (e) {
        console.warn(LOG, 'server unreachable, falling back to local cache', e);
        serverOk = false;
        if (typeof toastr !== 'undefined') {
            toastr.warning('Сервер недоступен — открыта локальная копия досок. Правки уйдут на сервер, когда связь вернётся.', '', { timeOut: 7000 });
        }
    }

    // 2. Local cache from a previous session on this device.
    let local = null;
    try {
        const rows = await idbGetAll();
        if (rows.length) { local = {}; for (const [k, v] of rows) local[k] = v; }
    } catch (e) {
        console.error(LOG, 'IndexedDB unavailable', e);
    }

    // 3. Anything the older builds stored.
    const c = getContext();
    let legacy = c?.extensionSettings?.moodboard_v1;
    if (!legacy) {
        try { const s = localStorage.getItem('moodboard_v1'); if (s) legacy = JSON.parse(s); } catch (e) {}
    }

    const source = local || legacy;
    if (!source || typeof source !== 'object') return;
    boards = source;

    // Push whatever we found up to the server so every device sees it from now on.
    if (serverOk) {
        try {
            serverRev = 1;
            await serverWrite({ _mb: 'moodboard', rev: serverRev, at: Date.now(), boards });
            for (const [k, v] of Object.entries(boards)) idbPut(k, structuredCloneSafe(v)).catch(() => {});
            if (c?.extensionSettings?.moodboard_v1) {
                delete c.extensionSettings.moodboard_v1;
                c.saveSettingsDebounced?.();
            }
            localStorage.removeItem('moodboard_v1');
            console.log(LOG, 'migrated', Object.keys(boards).length, 'boards to the server');
            if (typeof toastr !== 'undefined') {
                toastr.success('Доски перенесены на сервер — теперь они общие для телефона и компьютера.', '', { timeOut: 7000 });
            }
        } catch (e) {
            console.error(LOG, 'migration upload failed', e);
        }
    }
}

// --- AI Analysis Logic ---
function refreshProfilesUI() {
    const $opts = $('#mb-api-dropdown .mb-select-options');
    if (!$opts.length) return;
    $opts.empty();
    $opts.append(`<div data-val="tavern"><span class="mb-opt-title">Default Tavern AI</span><span class="mb-opt-desc">Текущее подключение Таверны</span></div>`);

    const stCtx = typeof getContext === 'function' ? getContext() : {};
    const profiles = stCtx.extensionSettings?.connectionManager?.profiles ?? [];
    profiles.forEach(p => {
        const sub = [p.api, p.model].filter(Boolean).join(' · ') || 'Профиль подключения';
        $opts.append(`<div data-val="${escHtml(p.name)}"><span class="mb-opt-title">🔗 ${escHtml(p.name)}</span><span class="mb-opt-desc">${escHtml(sub)}</span></div>`);
    });
    syncApiDropdown();
}

// Mirror the stored choice into the closed dropdown's label and tick the row.
function syncApiDropdown() {
    const cur = boards.global?.apiProfile || 'tavern';
    const $sel = $('#mb-api-dropdown');
    const $row = $sel.find(`.mb-select-options div[data-val="${cur.replace(/"/g, '\\"')}"]`);
    $sel.find('.mb-select-options div').removeClass('active');
    if ($row.length) {
        $row.addClass('active');
        $sel.find('.mb-select-value').text($row.find('.mb-opt-title').text());
    } else {
        // Profile disappeared from Tavern — say so instead of showing a stale name.
        $sel.find('.mb-select-value').text(cur === 'tavern' ? 'Default Tavern AI' : `⚠ ${cur} (не найден)`);
    }
}

function syncStyleDropdown() {
    const cur = boards.global?.responseStyle || 'balanced';
    const s = RESPONSE_STYLES.find(x => x[0] === cur) || RESPONSE_STYLES[0];
    const $sel = $('#mb-style-dropdown');
    $sel.find('.mb-select-value').html(`<i class="fa-solid fa-${s[2]} mb-opt-icon"></i>${escHtml(s[1])}`);
    $sel.find('.mb-select-options div').removeClass('active')
        .filter(`[data-val="${s[0]}"]`).addClass('active');
    $('#mb-style-hint').text(s[4]);
    $('#mb-custom-prompt-wrap').toggle(s[0] === 'custom');
}

async function ensureHtml2Canvas() {
    if (typeof window.html2canvas !== 'undefined') return window.html2canvas;
    return new Promise((res, rej) => {
        const script = document.createElement('script');
        script.src = 'https://cdnjs.cloudflare.com/ajax/libs/html2canvas/1.4.1/html2canvas.min.js';
        script.onload = () => res(window.html2canvas);
        script.onerror = rej;
        document.head.appendChild(script);
    });
}

// Console only, on purpose: this is diagnostic detail, not something worth
// interrupting anyone with.
function warnProfileRoute(why) {
    console.warn(LOG, 'preset-aware route unavailable, request sent directly:', why);
}

// Decided BEFORE anything is sent, and never after. Retrying a failed request on
// the other route would mean two requests — and two hits on the quota — every time
// the model says no, which is exactly what a rate-limited key cannot afford.
function serviceRouteReady(profile) {
    const stCtx = typeof getContext === 'function' ? getContext() : {};
    if (profile) {
        const svc = stCtx.ConnectionManagerRequestService;
        if (!svc || typeof svc.sendRequest !== 'function' || !profile.id) return false;
        if (stCtx.extensionSettings?.disabledExtensions?.includes('connection-manager')) return false;
        try { svc.validateProfile(profile); } catch (e) { warnProfileRoute(e?.message || e); return false; }
        return true;
    }
    const svc = stCtx.ChatCompletionService;
    return !!(svc && typeof svc.processRequest === 'function'
        && stCtx.chatCompletionSettings?.chat_completion_source);
}

// "Default Tavern AI" has no connection profile, so it goes through the same
// preset-aware service directly, using whatever Tavern is currently connected to
// and whichever completion preset is selected right now.
//
// This is also where a long-standing bug lived: the source was read from
// `chatCompletionSettings.api` and the model from `.model`, and neither field
// exists — the real names are `chat_completion_source` and a per-source model
// field. Every request on this option therefore went out as OpenAI with an empty
// model, which is exactly the "OpenAI API key is missing" that came back.
async function fetchViaCurrentConnection(messages, maxTokens) {
    const stCtx = typeof getContext === 'function' ? getContext() : {};
    const svc = stCtx.ChatCompletionService;
    const cc = stCtx.chatCompletionSettings || {};
    const source = cc.chat_completion_source;
    if (!svc || typeof svc.processRequest !== 'function' || !source) return null;

    const payload = {
        stream: false,
        messages,
        max_tokens: maxTokens,
        model: (typeof stCtx.getChatCompletionModel === 'function' ? stCtx.getChatCompletionModel() : '') || '',
        chat_completion_source: source,
    };
    // Connection details Tavern keeps per source; the preset does not always carry
    // them, and without them the request cannot reach the endpoint at all.
    if (source === 'custom') payload.custom_url = cc.custom_url;
    if (source === 'vertexai') {
        payload.vertexai_region = cc.vertexai_region;
        if (cc.vertexai_auth_mode) payload.vertexai_auth_mode = cc.vertexai_auth_mode;
        if (cc.vertexai_express_project_id) payload.vertexai_express_project_id = cc.vertexai_express_project_id;
    }

    let presetName;
    try { presetName = stCtx.getPresetManager?.('openai')?.getSelectedPresetName?.(); } catch (e) {}

    const res = await svc.processRequest(payload, { presetName }, true);
    if (typeof res === 'string') return res;
    return typeof res?.content === 'string' ? res.content : '';
}

// Sends the request through Tavern's own Connection Manager, so it carries the
// generation settings of the preset attached to the chosen profile — temperature,
// top_p/top_k, the penalties, the custom-endpoint body and header extras, the
// proxy and the profile's own API key — instead of this extension's bare
// defaults. A board request used to arrive at the endpoint stripped of all of
// that, which is a good part of why the very same model refuses a board while it
// never refuses a chat post.
//
// What is deliberately NOT taken from the preset: max_tokens (kept at the value
// this extension has always sent) and the message list. Preset *prompts* are not
// part of this path at all — `includePreset` only brings generation parameters.
//
// Returns the reply text, or null if this route is unavailable, in which case the
// caller falls back to the direct request below.
async function fetchViaProfile(profile, messages, maxTokens) {
    const stCtx = typeof getContext === 'function' ? getContext() : {};
    const svc = stCtx.ConnectionManagerRequestService;
    if (!svc || typeof svc.sendRequest !== 'function' || !profile?.id) return null;

    // Anything the profile itself cannot supply has to be handed over explicitly.
    // Vertex is the case that matters: whether the preset fills in the auth mode
    // depends on which source *the preset* was saved with, and these boards are
    // used with presets saved as `custom`.
    const overrides = {};
    if ((profile.api || '') === 'vertexai') {
        const cc = stCtx.chatCompletionSettings || {};
        if (cc.vertexai_auth_mode) overrides.vertexai_auth_mode = cc.vertexai_auth_mode;
        if (cc.vertexai_express_project_id) overrides.vertexai_express_project_id = cc.vertexai_express_project_id;
    }

    const res = await svc.sendRequest(
        profile.id,
        messages,
        maxTokens,
        { stream: false, extractData: true, includePreset: true },
        overrides,
    );
    // An empty answer is passed straight through: the callers already decide what
    // to do with one, and a filtered reply must not look like a broken route.
    if (typeof res === 'string') return res;
    return typeof res?.content === 'string' ? res.content : '';
}

// `prompt` is either a plain string (one user turn, as thread replies send) or a
// ready list of messages (what a board capture builds).
//
// `wantTokens` raises the reply budget for callers that need a long answer. A
// board reaction is a paragraph and fits in whatever the chat is set to; a tree
// is a JSON document, and half a JSON document is worth nothing at all — which
// is exactly what came back when the chat's own max_length was modest.
async function fetchFromLLM(prompt, imageBase64, wantTokens) {
    const profileName = boards.global?.apiProfile || 'tavern';
    const stCtx = typeof getContext === 'function' ? getContext() : {};
    let cc_source = 'openai';
    let p = null;

    const ccSettings = stCtx.chatCompletionSettings || {};
    if (profileName !== 'tavern') {
        const profiles = stCtx.extensionSettings?.connectionManager?.profiles ?? [];
        p = profiles.find(x => x.name === profileName);
        if (!p) throw new Error(`Profile '${profileName}' not found!`);
        cc_source = p.api || 'openai';
    } else {
        // `.api` never existed on these settings — see fetchViaCurrentConnection.
        cc_source = ccSettings.chat_completion_source || 'openai';
    }

    // Copied, never mutated in place: the caller's list is stored with the reply so
    // a swipe can re-send it, and the picture must not end up baked into it (it is
    // already kept once, as the snapshot).
    const messages = Array.isArray(prompt)
        ? prompt.map(m => ({ ...m }))
        : [{ role: 'user', content: prompt }];
    if (imageBase64) {
        const last = messages[messages.length - 1];
        last.content = [
            { type: "text", text: typeof last.content === 'string' ? last.content : '' },
            { type: "image_url", image_url: { url: imageBase64 } }
        ];
    }

    const maxTokens = Math.max(wantTokens || 0, parseInt(stCtx.chatCompletionSettings?.max_length) || 3000);

    // One route, one request: the route is chosen before anything is sent, and an
    // error from the model is its own answer — it never triggers a second attempt.
    if (serviceRouteReady(p)) {
        const viaService = p
            ? await fetchViaProfile(p, messages, maxTokens)
            : await fetchViaCurrentConnection(messages, maxTokens);
        if (viaService !== null) return viaService;
    }
    warnProfileRoute('используется прямой запрос');

    let generate_data = {
        'messages': messages,
        'model': p ? p.model
            : ((typeof stCtx.getChatCompletionModel === 'function' ? stCtx.getChatCompletionModel() : '') || ''),
        'temperature': 0.7,
        'stream': false,
        'chat_completion_source': cc_source,
        'max_tokens': maxTokens
    };

    if (cc_source === 'custom') generate_data['custom_url'] = p ? p['api-url'] : ccSettings.custom_url;
    else if (cc_source === 'vertexai') {
        generate_data['vertexai_region'] = p ? p['api-url'] : ccSettings.vertexai_region;
        if (ccSettings.vertexai_auth_mode) generate_data['vertexai_auth_mode'] = ccSettings.vertexai_auth_mode;
        if (ccSettings.vertexai_express_project_id) generate_data['vertexai_express_project_id'] = ccSettings.vertexai_express_project_id;
    }

    const headers = (typeof stCtx.getRequestHeaders === 'function') ? stCtx.getRequestHeaders() : {};
    headers['Content-Type'] = 'application/json';

    const res = await fetch('/api/backends/chat-completions/generate', { 
        method: 'POST', body: JSON.stringify(generate_data), headers: headers
    });
    const d = await res.json();
    if (d.error) throw new Error(d.error.message || JSON.stringify(d.error));
    return typeof d.content === 'string' ? d.content : (d.content?.[0]?.text || d.choices?.[0]?.message?.content || '');
}

// Bounding box of everything on the board, in board coordinates. Capturing the
// full 4000x4000 canvas is what makes analysis crawl on mobile.
function contentBounds() {
    const cards = document.querySelectorAll('#mb-canvas-inner .mb-card');
    let x0 = Infinity, y0 = Infinity, x1 = -Infinity, y1 = -Infinity;
    cards.forEach(el => {
        const x = el.offsetLeft, y = el.offsetTop;
        x0 = Math.min(x0, x); y0 = Math.min(y0, y);
        x1 = Math.max(x1, x + el.offsetWidth); y1 = Math.max(y1, y + el.offsetHeight);
    });
    // Drawings count as content too, or a board that is only doodles crops to
    // nothing. Eraser strokes are skipped: they only take ink away, so counting
    // them padded the crop with blank space wherever something had been rubbed out.
    for (const s of boardStrokes()) {
        if (!s.p || s.p.length < 2 || s.t === 'eraser') continue;
        const b = s.b || strokeBounds(s.p);
        const pad = (s.w || 3);
        x0 = Math.min(x0, b[0] - pad); y0 = Math.min(y0, b[1] - pad);
        x1 = Math.max(x1, b[2] + pad); y1 = Math.max(y1, b[3] + pad);
    }
    // A timeline is content: an axis running past the last card must not be
    // cropped out of the picture it belongs to.
    const tl = getBoard().timeline;
    if (tl?.on) {
        x0 = Math.min(x0, tl.x0 - 30); x1 = Math.max(x1, tl.x1 + 30);
        y0 = Math.min(y0, tl.y - 70); y1 = Math.max(y1, tl.y + 50);
    }
    if (!isFinite(x0)) {
        // No cards — fall back to whatever the user is currently looking at.
        const area = document.getElementById('mb-canvas-area');
        const w = (area?.clientWidth || 800) / zoom, h = (area?.clientHeight || 600) / zoom;
        x0 = -panX / zoom; y0 = -panY / zoom; x1 = x0 + w; y1 = y0 + h;
    }
    const pad = 40;
    x0 = Math.max(0, x0 - pad); y0 = Math.max(0, y0 - pad);
    x1 = Math.min(BOARD_SIZE, x1 + pad); y1 = Math.min(BOARD_SIZE, y1 + pad);
    return { x: x0, y: y0, w: Math.max(1, x1 - x0), h: Math.max(1, y1 - y0) };
}

// Give the browser two frames to actually paint the overlay before we start
// blocking the main thread with html2canvas.
function nextPaint() {
    return new Promise(res => requestAnimationFrame(() => requestAnimationFrame(() => setTimeout(res, 0))));
}

// How the character should shape its reaction. Each entry appends its own
// instruction to the prompt, so switching styles genuinely changes what comes
// back rather than just trimming it afterwards.
// [key, label shown in the picker, instruction sent to the model, what the user
// should expect back]
const RESPONSE_STYLES = [
    ['balanced', 'Сбалансированно', 'scale-balanced',
     'Mix a little action with speech, roughly one short paragraph.',
     'Немного действий и немного реплик, примерно один абзац. Обычный режим.'],
    ['brief', 'Коротко', 'bolt',
     'Answer in ONE or TWO sentences. Pure reaction, no narration, no asterisked actions.',
     'Одна-две фразы. Только реакция, без описаний и действий в звёздочках.'],
    ['detailed', 'Подробно', 'book-open',
     'Write two or three full paragraphs. Pick out specific images and notes on the board and say what each one stirs up.',
     'Два-три абзаца. Разбирает конкретные картинки и заметки и говорит, что каждая в нём поднимает.'],
    ['epic', 'Развёрнуто', 'water',
     'Write at length and let yourself go — four or more paragraphs, following every thread the board suggests.',
     'Четыре абзаца и больше, во всю ширь — тянет каждую ниточку, которую подкидывает доска.'],
    ['thoughts', 'Мысли про себя', 'comment-dots',
     'Write ONLY unspoken inner monologue. No dialogue, no actions — just what runs through your head as you look at it.',
     'Только внутренний монолог. Ни реплик, ни действий — что у него в голове, пока он смотрит.'],
    ['spoken', 'Только речь', 'quote-right',
     'Write ONLY spoken dialogue addressed to the user. No narration, no actions, no asterisks.',
     'Только прямая речь, обращённая к тебе. Никаких описаний и действий.'],
    ['poetic', 'Поэтично', 'feather',
     'Answer in vivid, image-led prose. Lean on metaphor and sensory detail rather than plain description.',
     'Образный язык, метафоры, ощущения вместо сухого описания.'],
    ['teasing', 'С подколом', 'face-smile-wink',
     'Be playful and a little smug. Tease the user about what the board reveals, keeping it affectionate.',
     'Игриво и самодовольно — подначивает тебя тем, что выдаёт твоя доска. По-доброму.'],
    ['notes', 'Впечатления', 'list-ul',
     'Answer as a short list of 3-6 impression lines, each starting with "—". Fragments, not full sentences.',
     'Список из 3–6 коротких строк через тире. Обрывки впечатлений, а не связный текст.'],
    ['scene', 'Заявка на сцену', 'clapperboard',
     'Do not merely comment: propose ONE concrete scene the board is asking for, in a single evocative paragraph, and end by asking whether to play it out.',
     'Не просто комментирует, а предлагает одну конкретную сцену по мотивам доски и спрашивает, отыграть ли её.'],
    ['npc', 'Реакция НПС', 'users',
     'Answer NOT as the main character but as the side characters and bystanders of this world — friends, family, colleagues, strangers. Name whoever is speaking. Give two or three of them a short reaction each.',
     'Отвечает не главный герой, а второстепенные персонажи мира — друзья, родня, коллеги, случайные люди. По короткой реплике от двух-трёх, каждый подписан.'],
    ['everyone', 'Реакция всех', 'people-group',
     'Give a round of reactions: first the main character, then several side characters and bystanders. Label each speaker on its own line. Keep every reaction to a couple of sentences so the whole chorus fits.',
     'Сначала главный герой, потом несколько второстепенных. Каждый подписан, у каждого пара фраз — получается общий хор откликов.'],
    ['custom', 'Свой промпт', 'pen-to-square', '', 'Ваша собственная инструкция — задаётся ниже.'],
];
function responseStylePrompt() {
    const key = boards.global?.responseStyle || 'balanced';
    if (key === 'custom') {
        const own = (boards.global?.customPrompt || '').trim();
        return own || RESPONSE_STYLES[0][3];   // empty custom box: fall back to balanced
    }
    const found = RESPONSE_STYLES.find(s => s[0] === key) || RESPONSE_STYLES[0];
    return found[3];
}

// The two "+" buttons that live outside the board — the quote popup and the pin
// in the corner of chat images. Stored with the rest of the global settings, so
// switching them off follows you to your other devices. Absent means on, which is
// how every board behaved before these existed.
function uiPref(key) {
    const v = boards.global?.[key];
    return v === undefined ? true : !!v;
}
// Which corner of a picture the "+" sits in. Bottom-right by default: Tavern's
// own controls run along the top edge, and on a phone ours landed underneath the
// delete button — a tap either missed or hit the wrong thing entirely.
const PIN_CORNERS = ['tl', 'tr', 'bl', 'br'];
function pinPos() {
    const v = boards.global?.imgBtnPos;
    return PIN_CORNERS.includes(v) ? v : 'br';
}
// One attribute on the document; the CSS does the rest, so moving the button is
// instant and needs no re-injection.
function applyPinPos() {
    document.documentElement.setAttribute('data-mb-pin-pos', pinPos());
    $('#mb-pin-pos .mb-corner-opt').removeClass('active')
        .filter(`[data-pos="${pinPos()}"]`).addClass('active');
}
function setUiPref(key, on) {
    if (!boards.global) boards.global = { cards: [] };
    boards.global[key] = !!on;
    save();
}

// Pulls the settings panel back in line with what is actually stored.
function syncSettingsUI() {
    syncStyleDropdown();
    const ctx = boards.global?.apiContextSize;
    if (typeof ctx === 'number') setCtxSize(ctx, null);
    $('#mb-custom-prompt').val(boards.global?.customPrompt || '');
    $('#mb-tg-quote').prop('checked', uiPref('showQuoteBtn'));
    $('#mb-tg-image').prop('checked', uiPref('showImageBtn'));
    $('#mb-tg-charcard').prop('checked', sendPref('sendCharCard'));
    $('#mb-tg-persona').prop('checked', sendPref('sendPersona'));
    $('#mb-tg-lore').prop('checked', sendPref('sendLore'));
    $('#mb-tg-note').prop('checked', sendPref('sendAuthorNote'));
    applyPinPos();
}

// One writer for the context size, so the slider, the number box and storage can
// never drift apart. `from` is the control that was just touched — it keeps its
// own value while the user is still typing in it.
function setCtxSize(v, from) {
    const n = Math.max(0, Math.min(CTX_MAX, parseInt(v, 10) || 0));
    if (from !== 'slider') $('#mb-ctx-slider').val(n);
    if (from !== 'num') $('#mb-ctx-num').val(n);
    return n;
}

// The prompt for a board reaction. Kept apart from analyzeBoard so a swipe can
// rebuild an equivalent one for replies captured before prompts were stored.
function buildBoardPrompt({ user, charName, charDesc, charPersona, notes, chatMsgs, partial }) {
    let prompt = `[System Note: You are ${charName}. You are roleplaying with ${user}. ${user} has assembled a Mood Board (a visual collage) to reflect the current atmosphere, mood, or planning of your scene.]\n\n`;
    if (sendPref('sendCharCard') && (charDesc || charPersona)) {
        prompt += `[Your Persona/Description:\n${(charDesc || '').substring(0, 1000)}\n${(charPersona || '').substring(0, 500)}]\n\n`;
    }

    prompt += `[### Text Notes on the Board:\n${notes ? notes : 'No text notes on board.'}]\n\n`;
    prompt += `[### Recent Chat Context:\n${chatMsgs ? chatMsgs : 'No recent chat context.'}]\n\n`;

    // ZERO DEPTH INSTRUCTIONS
    if (partial) {
        prompt += `[NOTE: ${user} has singled out ${partial} item(s) from the board — the image shows only those. React to what is in front of you, not to the board as a whole.]\n\n`;
    }
    prompt += `[SYSTEM COMMAND: Look at the Mood Board image and read the notes. Provide an IN-CHARACTER reaction, thoughts, or commentary about the board itself. Speak directly to ${user} or muse to yourself. React to the vibe and imagery! IMPORTANT: DO NOT WRITE A ROLEPLAY CONTINUATION! ONLY COMMENT ON THE BOARD!`;
    prompt += ` ${responseStylePrompt()}]`;
    const note = (boards.global?.aiNote || '').trim();
    if (note) prompt += `\n\n[${user} adds a direct instruction for this reply — follow it: ${note}]`;
    return prompt;
}

// ===== GROUP CHATS: WHO ANSWERS =====
// In a solo chat the answer obviously comes from the character. In a group there
// is no single "the character" — Tavern's `name2` is whatever spoke last, which is
// why a board reaction used to arrive signed "Character". So the group's members
// are offered as a choice: one of them, several, or all.
function groupInfo() {
    const stCtx = typeof getContext === 'function' ? getContext() : {};
    if (!stCtx.groupId) return { isGroup: false, group: null, members: [] };
    const group = (stCtx.groups || []).find(g => String(g.id) === String(stCtx.groupId)) || null;
    const disabled = new Set(group?.disabled_members || []);
    const members = (group?.members || [])
        .filter(a => !disabled.has(a))
        .map(a => (stCtx.characters || []).find(c => c.avatar === a))
        .filter(Boolean);
    return { isGroup: true, group, members };
}
// Kept per group, so a choice made in one group does not follow you into another.
function speakerStore() {
    if (!boards.global) boards.global = { cards: [] };
    if (!boards.global.groupSpeakers) boards.global.groupSpeakers = {};
    return boards.global.groupSpeakers;
}
function pickedSpeakers() {
    const info = groupInfo();
    if (!info.isGroup) return [];
    const stCtx = getContext();
    const chosen = speakerStore()[String(stCtx.groupId)];
    if (!Array.isArray(chosen) || !chosen.length) return info.members;   // nothing chosen: everyone
    const keep = info.members.filter(c => chosen.includes(c.avatar));
    return keep.length ? keep : info.members;
}
function toggleSpeaker(avatar) {
    const stCtx = getContext();
    const key = String(stCtx.groupId);
    const store = speakerStore();
    const info = groupInfo();
    // An empty list means "everyone", so the first tap starts from the full set.
    const cur = Array.isArray(store[key]) && store[key].length
        ? [...store[key]] : info.members.map(c => c.avatar);
    const i = cur.indexOf(avatar);
    if (i >= 0) cur.splice(i, 1); else cur.push(avatar);
    // Deselecting the last one reads as "everyone" again rather than "nobody".
    store[key] = cur.length ? cur : [];
    save();
}

// ===== BOARD REQUEST AS A CONVERSATION =====
// A chat post reaches the model as a conversation: a system instruction, then the
// history as separate user/assistant turns. A board request used to arrive as ONE
// user turn with the entire history pasted inside it — same tokens, but the shape
// of somebody dumping a pile of prose rather than a story in progress, and that is
// the last real difference left between a post and a board request.
//
// Every instruction string below is byte-for-byte what it was before; only where
// each one sits has changed.
// ===== WHAT TRAVELS WITH THE BOARD =====
// Three switches, because how much of the setting a board reaction needs is a
// matter of taste and of token budget. The character card is what has always
// been sent; the other two are new ground.
//
// Lorebook entries are picked the way Tavern picks them for an ordinary reply:
// by keyword, scanned against the board's own notes and the recent chat. So a
// note naming an NPC who lives in a lorebook pulls that NPC in, which is the
// entire point of the setting.
const LORE_MAX = 8000;

function sendPref(key) {
    const v = boards.global?.[key];
    return v === undefined ? true : !!v;   // absent means yes, as it always was
}

// The Author's Note is a standing instruction about the scene — "they have been
// together five years and have a daughter" — which is exactly the sort of thing
// a reaction to the board should already know. Tavern keeps up to three of them:
// one on the chat, one bound to the character, and a default for new chats.
const NOTE_MAX = 2000;
function authorNoteText(stCtx) {
    if (!sendPref('sendAuthorNote')) return '';
    const meta = stCtx.chatMetadata || {};
    const cfg = stCtx.extensionSettings?.note || {};
    const parts = [];
    const chat = (meta.note_prompt || '').trim();
    if (chat) parts.push(chat);
    const chara = (cfg.chara || []).find(c => c && c.name === stCtx.name2);
    const charaNote = (chara?.prompt || '').trim();
    if (charaNote && charaNote !== chat) parts.push(charaNote);
    // The default only matters when nothing more specific has been written; a
    // chat that has its own note has already replaced it.
    if (!parts.length) {
        const def = (cfg.default || '').trim();
        if (def) parts.push(def);
    }
    const s = parts.join('\n').trim();
    return s.length > NOTE_MAX ? s.slice(0, NOTE_MAX) + '…' : s;
}

function personaText(stCtx) {
    if (!sendPref('sendPersona')) return '';
    const pu = stCtx.powerUserSettings || {};
    const d = (pu.persona_description || '').trim();
    return d ? d.slice(0, 1200) : '';
}

async function loreText(stCtx, scanText) {
    if (!sendPref('sendLore')) return '';
    if (typeof stCtx.getWorldInfoPrompt !== 'function') return '';
    try {
        // Dry run: a board request must not burn through the sticky/cooldown
        // state that belongs to the conversation itself.
        const wi = await stCtx.getWorldInfoPrompt(scanText, stCtx.maxContext || 8192, true);
        const parts = [wi.worldInfoBefore, wi.worldInfoAfter];
        for (const d of (wi.worldInfoDepth || [])) {
            if (Array.isArray(d?.entries)) parts.push(d.entries.join('\n'));
        }
        const s = parts.filter(Boolean).join('\n').trim();
        return s.length > LORE_MAX ? s.slice(0, LORE_MAX) + '\n…' : s;
    } catch (e) {
        console.warn(LOG, 'world info lookup failed', e);
        return '';
    }
}

// The text lorebook activation is matched against: what is written on the board
// plus the last few things said.
function loreScanText(stCtx, notes, ctxSize) {
    const msgs = (stCtx.chat || []).slice(-Math.max(4, Math.min(ctxSize || 10, 20)))
        .map(m => m?.mes || '').filter(Boolean);
    return [notes || '', ...msgs].filter(Boolean);
}

function boardSystemText({ user, charName, charDesc, charPersona, notes, speakers, persona, lore, authorNote }) {
    let s;
    if (speakers && speakers.length > 1) {
        // A group: every chosen member gets its own card, and the model is told
        // plainly that it is voicing all of them.
        const names = speakers.map(c => c.name).join(', ');
        s = `[System Note: You are playing ALL of these characters: ${names}. You are roleplaying with ${user}. ${user} has assembled a Mood Board (a visual collage) to reflect the current atmosphere, mood, or planning of your scene.]\n\n`;
        if (sendPref('sendCharCard')) {
            for (const c of speakers) {
                const desc = (c.description || '').substring(0, 600);
                const pers = (c.personality || '').substring(0, 300);
                if (desc || pers) s += `[Character — ${c.name}:\n${desc}\n${pers}]\n\n`;
            }
        }
    } else {
        s = `[System Note: You are ${charName}. You are roleplaying with ${user}. ${user} has assembled a Mood Board (a visual collage) to reflect the current atmosphere, mood, or planning of your scene.]\n\n`;
        // Cards are long — six thousand characters is ordinary — and the old
        // thousand-character slice usually stopped inside the appearance
        // section. Now that sending the card is a deliberate choice, send enough
        // of it to be worth choosing.
        if (sendPref('sendCharCard') && (charDesc || charPersona)) {
            s += `[Your Persona/Description:\n${(charDesc || '').substring(0, 4000)}\n${(charPersona || '').substring(0, 1500)}]\n\n`;
        }
    }
    if (persona) s += `[Who ${user} is, in their own words:\n${persona}]\n\n`;
    if (lore) s += `[World and lore that applies to this scene — treat it as established fact:\n${lore}]\n\n`;
    // Last of the background blocks, closest to the board itself: an author's
    // note is about how things stand right now, and that is what the reaction is
    // being written against.
    if (authorNote) s += `[Standing note about this story — it is true and current:\n${authorNote}]\n\n`;
    s += `[### Text Notes on the Board:\n${notes ? notes : 'No text notes on board.'}]`;
    return s;
}

// The task and the response style go in the final turn, immediately before the
// answer — the position with the most pull over format, and the same one Tavern's
// own presets use for their formatting rules.
function boardAskText({ user, partial, speakers }) {
    let s = '';
    if (partial) {
        s += `[NOTE: ${user} has singled out ${partial} item(s) from the board — the image shows only those. React to what is in front of you, not to the board as a whole.]\n\n`;
    }
    s += `[SYSTEM COMMAND: Look at the Mood Board image and read the notes. Provide an IN-CHARACTER reaction, thoughts, or commentary about the board itself. Speak directly to ${user} or muse to yourself. React to the vibe and imagery! IMPORTANT: DO NOT WRITE A ROLEPLAY CONTINUATION! ONLY COMMENT ON THE BOARD!`;
    // Said right before the style, so the chosen format still governs the shape of
    // each individual reaction. Two of the styles are *about* rounding up extra
    // voices — pinning the cast down would only argue with them, so there the
    // style decides who speaks and this only supplies the cards.
    const chorusStyle = ['npc', 'everyone'].includes(boards.global?.responseStyle);
    if (speakers && speakers.length > 1 && !chorusStyle) {
        s += ` Answer as EVERY ONE of these characters in turn: ${speakers.map(c => c.name).join(', ')}. Label each reaction with that character's name on its own line, and give no reactions from anyone else.`;
    } else if (speakers && speakers.length === 1 && !chorusStyle) {
        s += ` Answer as ${speakers[0].name} and no one else.`;
    } else if (speakers && speakers.length) {
        s += ` The characters present are: ${speakers.map(c => c.name).join(', ')}.`;
    }
    s += ` ${responseStylePrompt()}]`;
    const note = (boards.global?.aiNote || '').trim();
    if (note) s += `\n\n[${user} adds a direct instruction for this reply — follow it: ${note}]`;
    return s;
}

// The recent chat, as the turns it actually is.
function chatTurns(stCtx, ctxSize) {
    if (!ctxSize) return [];
    const isGroup = !!stCtx.groupId;
    return (stCtx.chat || []).slice(-ctxSize)
        .filter(m => m && !m.is_system && (m.mes || '').trim())
        .map(m => ({
            role: m.is_user ? 'user' : 'assistant',
            // In a group several characters share the assistant role, so the name
            // has to stay in the text or the reactions get pinned on the wrong one.
            content: (isGroup && !m.is_user) ? `${m.name}: ${m.mes}` : m.mes,
        }));
}

function buildBoardMessages(o) {
    return [
        { role: 'system', content: boardSystemText(o) },
        ...chatTurns(o.stCtx, o.ctxSize),
        { role: 'user', content: boardAskText(o) },
    ];
}

// Who the reply is signed with, and whose cards go into it.
function resolveSpeakers(stCtx) {
    const isGroup = !!stCtx.groupId;
    let charName = stCtx.name2 || 'Character';
    let charDesc = '', charPersona = '', speakers = null;

    if (isGroup) {
        speakers = pickedSpeakers();
        if (speakers.length === 1) {
            charName = speakers[0].name;
            charDesc = speakers[0].description || '';
            charPersona = speakers[0].personality || '';
        } else if (speakers.length > 1) {
            charName = speakers.map(c => c.name).join(' · ');
        }
    } else if (stCtx.characters) {
        // `characterId` is an index into the list — "3", as a string — not an
        // avatar filename. Matching it against `avatar` therefore never found
        // anybody, and the character's own description has been quietly missing
        // from every board request. Index first, then the older meanings of the
        // field, so this keeps working whichever way Tavern reports it.
        const char = stCtx.characters[stCtx.characterId]
            || stCtx.characters.find(c => c.avatar === stCtx.characterId)
            || stCtx.characters.find(c => c.name === stCtx.name2);
        if (char) {
            charName = char.name;
            charDesc = char.description || '';
            charPersona = char.personality || '';
        }
    }
    return { charName, charDesc, charPersona, speakers };
}

async function analyzeBoard() {
    const btn = $('#mb-btn-analyze');
    const oldHtml = btn.html();
    btn.addClass('mb-busy').prop('disabled', true);

    if (!$('#mb-ai-overlay').length) {
        // Sizing note: <html> carries a transform in SillyTavern, which makes it the
        // containing block for position:fixed. Percentage heights then resolve
        // against <html> (effectively 0) and the overlay collapses into a strip at
        // the top of the screen. Viewport units are immune to that.
        // No backdrop-filter here either: it would hold a full-screen blur for the
        // entire request, exactly when the phone can least afford it.
        $('body').append(`<div id="mb-ai-overlay" style="position:fixed;top:0;left:0;width:100vw;height:100vh;height:100dvh;background:rgba(0,0,0,0.88);z-index:9999999;display:flex;flex-direction:column;align-items:center;justify-content:center;color:#fff;">
            <i class="fa-solid fa-spinner fa-spin fa-3x" style="color:var(--mb-accent);margin-bottom:20px;"></i>
            <h2 style="font-family:var(--mb-font-handwritten);font-size:2em;font-weight:normal;">Analyzing Board...</h2>
        </div>`);
    } else {
        $('#mb-ai-overlay').css('display', 'flex');
    }

    let clone = null;
    pauseCull();
    try {
        const h2c = await ensureHtml2Canvas();
        await nextPaint();

        uncullCards(); // hidden cards must be visible or they won't be captured
        await awaitCardImages();
        await useFullResImages(true);

        // With a selection active, capture only those cards: crop to their box
        // and drop the rest from the copy. Drawings inside that box come along,
        // which is what makes marks *on* a photo part of the picture.
        const onlySelected = selectMode && picked.size > 0;
        const box = onlySelected ? (pickedBounds() || contentBounds()) : contentBounds();

        const inner = document.getElementById('mb-canvas-inner');
        clone = inner.cloneNode(true);
        clone.id = 'mb-canvas-clone';
        clone.style.transform = 'none';
        clone.style.position = 'absolute';
        clone.style.top = '-99999px';
        clone.style.left = '-99999px';
        wakeCloneCards(clone);
        document.body.appendChild(clone);
        if (onlySelected) {
            clone.querySelectorAll('.mb-card').forEach(el => {
                if (!picked.has(el.dataset.id)) el.remove();
            });
        }

        await paintInkOntoClone(clone);

        // Crop to the content and cap the long edge so the rasterized image stays
        // small. html2canvas takes x/y relative to the captured element's own
        // coordinate space, so these are plain board coordinates.
        const scale = Math.min(1, 1400 / Math.max(box.w, box.h));
        const canvas = await h2c(clone, {
            useCORS: true, allowTaint: true, backgroundColor: null,
            x: box.x, y: box.y, width: box.w, height: box.h,
            scale, logging: false, removeContainer: true,
        });
        document.body.removeChild(clone); clone = null;

        const base64 = canvas.toDataURL('image/jpeg', 0.8);
        // A small copy of exactly what was sent, stored with the reply so it is
        // always clear which part of the board the character was looking at.
        const shot = await compressImageSrc(base64, 640, 0.85, true);
        canvas.width = canvas.height = 0; // release the bitmap immediately
        await nextPaint();

        const b = getBoard();
        const noteSource = onlySelected
            ? b.cards.filter(c => picked.has(c.id))
            : b.cards;
        const notes = noteSource.filter(c => c.type === 'text' || c.type === 'quote')
            .map(c => plainNote(c.content)).filter(Boolean)
            // A tree card is a note too — a list of who is who and how they are
            // tied together is exactly the kind of thing worth sending.
            .concat(noteSource.filter(c => c.type === 'tree').map(treeAsText).filter(Boolean))
            .join('\n---\n');
        
        // Storage is the source of truth; the slider may not have been synced yet.
        const stored = boards.global?.apiContextSize;
        const ctxSize = Number.isFinite(stored) ? stored : (parseInt($('#mb-ctx-slider').val()) || 10);
        const stCtx = typeof getContext === 'function' ? getContext() : {};
        const user = stCtx.name1 || 'User';
        const { charName, charDesc, charPersona, speakers } = resolveSpeakers(stCtx);
        
        const persona = personaText(stCtx);
        const lore = await loreText(stCtx, loreScanText(stCtx, notes, ctxSize));
        const authorNote = authorNoteText(stCtx);

        const prompt = buildBoardMessages({
            stCtx, ctxSize, user, charName, charDesc, charPersona, notes, speakers, persona, lore, authorNote,
            partial: onlySelected ? picked.size : 0,
        });

        const res = await fetchFromLLM(prompt, base64);

        if (!b.aiHistory) b.aiHistory = [];
        // The prompt travels with the reply: that is what a swipe re-sends, so a
        // second take is about the same board even after the board has moved on.
        const msgObj = { id: genId(), name: charName, text: res, time: Date.now(), shot,
                         partial: onlySelected ? picked.size : 0, prompt };
        b.aiHistory.push(msgObj);
        save(true);   // an AI reply is expensive to regenerate — never leave it on a timer

        appendAiMessage(msgObj);
        $('#mb-settings, #mb-stickers, #mb-custom-color-panel').removeClass('open');
        settingsOpen = false;
        $('#mb-ai-panel').addClass('open'); aiPanelOpen = true;

    } catch(err) {
        console.error(err);
        if (typeof toastr !== 'undefined') toastr.error('Error analyzing board: ' + err.message);
    } finally {
        if (clone?.parentNode) clone.parentNode.removeChild(clone);
        await useFullResImages(false);
        $('#mb-ai-overlay').css('display', 'none');
        btn.removeClass('mb-busy').html(oldHtml).prop('disabled', false);
        resumeCull();
    }
}

function appendAiMessage(msgObj) {
    const hist = $('#mb-ai-history');
    hist.find('.empty-msg').remove();
    const folderTag = msgObj.folder
        ? `<span class="mb-folder-tag"><i class="fa-solid fa-folder"></i>${escHtml(msgObj.folder)}</span>` : '';

    const bubble = $(`<div class="mb-ai-msg" id="ai-msg-${msgObj.id}">
        <div class="mb-ai-msg-head">
            <span class="mb-ai-msg-name">${escHtml(msgObj.name)}</span>
            <div class="mb-ai-acts">
                <i class="fa-solid fa-reply act-reply" title="Ответить"></i>
                <i class="fa-solid fa-folder-open act-folder" title="Папка"></i>
                <i class="fa-solid fa-comment-medical act-tochat" title="Вшить в последнее сообщение чата"></i>
                <i class="fa-solid fa-trash act-del" title="Удалить"></i>
            </div>
        </div>
        ${folderTag}
        ${msgObj.shot ? `<div class="mb-ai-shot" title="Что было отправлено">
            <img src="${msgObj.shot}" alt="">
            ${msgObj.partial ? `<span class="mb-ai-shot-tag">выбрано: ${msgObj.partial}</span>` : ''}
        </div>` : ''}
        <div class="mb-ai-msg-body mb-rich">${formatRich(msgObj.text, msgObj.name)}</div>
        ${swipeBarHtml(msgObj)}
        <div class="mb-thread"></div>
        <div class="mb-reply-box"></div>
    </div>`);

    renderThread(bubble.find('.mb-thread'), msgObj);
    bindSwipes(bubble, msgObj);

    bubble.find('.act-del').on('click', async function() {
        if (!await mbConfirm('Удалить отклик?', 'Вместе с ним пропадёт вся переписка под ним.',
                             { okLabel: 'Удалить', danger: true })) return;
        const b = getBoard();
        if (b.aiHistory) {
            b.aiHistory = b.aiHistory.filter(m => m.id !== msgObj.id);
            save(true);
        }
        $(`#ai-msg-${msgObj.id}`).fadeOut(200, function() {
            $(this).remove();
            if (!hist.children().length) renderAiHistory();
            renderFolderBar();
        });
    });
    bubble.find('.act-folder').on('click', () => pickFolder(msgObj));
    bubble.find('.act-tochat').on('click', () => insertThreadIntoChat(msgObj));
    bubble.find('.act-reply').on('click', () => openReplyBox(bubble, msgObj));

    // Newest first, so a fresh reaction is right there without scrolling.
    hist.prepend(bubble);
}

function renderThread($wrap, msgObj) {
    $wrap.empty();
    (msgObj.thread || []).forEach(t => {
        $wrap.append(`<div class="mb-thread-msg ${t.role === 'user' ? 'is-user' : 'is-char'}">
            <span class="mb-thread-who">${t.role === 'user' ? 'Я' : escHtml(msgObj.name)}</span>
            <div class="mb-thread-text mb-rich">${formatRich(t.text, t.role === 'user' ? '' : msgObj.name)}</div>
        </div>`);
    });
}

// ===== SWIPES =====
// A reply can hold several takes on the same board. The right arrow past the last
// one asks the character again with the very same prompt and the very same
// snapshot; every earlier take stays where it was, with its own conversation
// under it, so nothing is ever traded away for a reroll.
const regenBusy = new Set();

function swipeCount(m) { return Array.isArray(m.swipes) && m.swipes.length ? m.swipes.length : 1; }
function swipeIndex(m) {
    const n = swipeCount(m);
    const i = typeof m.swipe === 'number' ? m.swipe : 0;
    return i >= 0 && i < n ? i : 0;
}
// Materialises the array on first use only: replies that are never swiped stay
// exactly as they were saved, which keeps old boards from growing for nothing.
function ensureSwipes(m) {
    if (!Array.isArray(m.swipes) || !m.swipes.length) {
        m.swipes = [{ text: m.text, thread: Array.isArray(m.thread) ? m.thread : [] }];
        m.swipe = 0;
    }
    m.swipe = swipeIndex(m);
    return m.swipes;
}
// `text` and `thread` stay the live mirror of the active take, so everything that
// already reads them — the chat insert, the reply thread, the folder tools —
// keeps working untouched.
function syncActiveSwipe(m) {
    const s = m.swipes[m.swipe];
    if (!s) return;
    if (!Array.isArray(s.thread)) s.thread = [];
    m.text = s.text;
    m.thread = s.thread;
}

function swipeBarHtml(m) {
    const n = swipeCount(m), i = swipeIndex(m);
    return `<div class="mb-swipe-bar">
        <i class="fa-solid fa-chevron-left mb-swipe-prev ${i === 0 ? 'disabled' : ''}" title="Предыдущий вариант"></i>
        <span class="mb-swipe-count">${i + 1}/${n}</span>
        <i class="fa-solid fa-chevron-right mb-swipe-next" title="${i + 1 < n ? 'Следующий вариант' : 'Сгенерировать новый вариант'}"></i>
    </div>`;
}

// Repaints just the parts a swipe changes.
function paintSwipe(m, $bubble) {
    const $body = $bubble.find('.mb-ai-msg-body');
    $body.html(formatRich(m.text, m.name)).removeClass('mb-swipe-fade');
    void $body[0]?.offsetWidth;   // the class has to leave the element before the fade can retrigger
    $body.addClass('mb-swipe-fade');
    renderThread($bubble.find('.mb-thread'), m);
    $bubble.find('.mb-reply-box').empty();
    $bubble.find('.mb-swipe-bar').replaceWith(swipeBarHtml(m));
}

async function stepSwipe(m, $bubble, dir) {
    if (regenBusy.has(m.id)) return;
    ensureSwipes(m);
    const i = m.swipe + dir;
    if (i < 0) return;
    if (i >= m.swipes.length) { await regenSwipe(m, $bubble); return; }
    m.swipe = i;
    syncActiveSwipe(m);
    save(true);
    paintSwipe(m, $bubble);
}

async function regenSwipe(m, $bubble) {
    if (regenBusy.has(m.id)) return;
    regenBusy.add(m.id);
    const $bar = $bubble.find('.mb-swipe-bar').addClass('busy');
    $bar.find('.mb-swipe-count').html('<i class="fa-solid fa-spinner fa-spin"></i>');
    try {
        // The stored snapshot is the picture the character saw the first time —
        // reusing it is what makes a swipe a reroll of the same board rather than
        // a fresh look at whatever the board became since.
        const res = await fetchFromLLM(m.prompt || rebuildBoardPrompt(m), m.shot || null);
        if (!res || !res.trim()) throw new Error('пустой ответ');
        ensureSwipes(m);
        m.swipes.push({ text: res, thread: [] });
        m.swipe = m.swipes.length - 1;
        syncActiveSwipe(m);
        save(true);
        paintSwipe(m, $bubble);
    } catch (e) {
        console.error(LOG, e);
        if (typeof toastr !== 'undefined') toastr.error('Не удалось сгенерировать: ' + e.message);
        $bar.removeClass('busy');
        paintSwipe(m, $bubble);
    } finally {
        regenBusy.delete(m.id);
    }
}

// Replies saved before prompts were stored still deserve a swipe. Rebuild an
// equivalent prompt from the character and the board as they are now.
function rebuildBoardPrompt(m) {
    const stCtx = typeof getContext === 'function' ? getContext() : {};
    const b = getBoard();
    const notes = (b.cards || []).filter(c => c.type === 'text' || c.type === 'quote')
        .map(c => c.content).filter(Boolean).join('\n---\n');
    const stored = boards.global?.apiContextSize;
    const ctxSize = Number.isFinite(stored) ? stored : 10;
    const chatMsgs = (stCtx.chat || []).slice(-ctxSize).map(x => `${x.name}: ${x.mes}`).join('\n\n');
    let charDesc = '', charPersona = '';
    const char = (stCtx.characters || []).find(c => c.avatar === stCtx.characterId);
    if (char && char.name === m.name) { charDesc = char.description || ''; charPersona = char.personality || ''; }
    return buildBoardPrompt({
        user: stCtx.name1 || 'User', charName: m.name, charDesc, charPersona,
        notes, chatMsgs, partial: m.partial || 0,
    });
}

function bindSwipes($bubble, m) {
    $bubble.on('click', '.mb-swipe-prev', () => stepSwipe(m, $bubble, -1));
    $bubble.on('click', '.mb-swipe-next', () => stepSwipe(m, $bubble, 1));
    // Dragging the reply sideways works too, the way it does on a chat message.
    // Vertical movement wins, so this never fights scrolling the panel.
    let sx = 0, sy = 0, st = 0;
    $bubble.on('touchstart', '.mb-ai-msg-body', e => {
        const t = e.originalEvent?.touches?.[0];
        if (!t || e.originalEvent.touches.length > 1) { st = 0; return; }
        sx = t.clientX; sy = t.clientY; st = Date.now();
    });
    $bubble.on('touchend', '.mb-ai-msg-body', e => {
        if (!st) return;
        const t = e.originalEvent?.changedTouches?.[0];
        const dt = Date.now() - st;
        st = 0;
        if (!t || dt > 700) return;
        const dx = t.clientX - sx, dy = t.clientY - sy;
        if (Math.abs(dx) < 55 || Math.abs(dx) < Math.abs(dy) * 2) return;
        stepSwipe(m, $bubble, dx < 0 ? 1 : -1);   // drag left = next, like a carousel
    });
}

function openReplyBox($bubble, msgObj) {
    const $box = $bubble.find('.mb-reply-box');
    if ($box.children().length) { $box.empty(); return; }   // toggle closed
    const $ta = $('<textarea class="mb-reply-input" rows="2" placeholder="Ответить…"></textarea>');
    const $send = $('<button class="mb-settings-btn mb-reply-send">Отправить</button>');
    $box.append($ta).append($send);
    $ta.trigger('focus');
    const go = async () => {
        const text = ($ta.val() || '').trim();
        if (!text) return;
        $send.prop('disabled', true).html('<i class="fa-solid fa-spinner fa-spin"></i>');
        try {
            await sendThreadReply(msgObj, text);
            $box.empty();
            renderThread($bubble.find('.mb-thread'), msgObj);
        } catch (e) {
            console.error(LOG, e);
            if (typeof toastr !== 'undefined') toastr.error('Не удалось отправить: ' + e.message);
            $send.prop('disabled', false).text('Отправить');
        }
    };
    $send.on('click', go);
    // Enter sends, Shift+Enter makes a new line.
    $ta.on('keydown', e => {
        if (e.key === 'Enter' && !e.shiftKey) { e.preventDefault(); go(); }
        if (e.key === 'Escape') { e.stopPropagation(); $box.empty(); }
    });
}

// Continues the conversation about the board. The board image is not re-sent —
// the character already described it, and its own words carry that context
// forward far more cheaply than another screenshot would.
async function sendThreadReply(msgObj, userText) {
    const stCtx = typeof getContext === 'function' ? getContext() : {};
    const user = stCtx.name1 || 'User';
    const b = getBoard();
    if (!Array.isArray(msgObj.thread)) msgObj.thread = [];
    // Each take keeps its own conversation, so re-point the swipe at whatever
    // array we are about to append to.
    const sw = Array.isArray(msgObj.swipes) ? msgObj.swipes[swipeIndex(msgObj)] : null;
    if (sw) sw.thread = msgObj.thread;
    msgObj.thread.push({ id: genId(), role: 'user', text: userText, time: Date.now() });
    save(true);

    const notes = (b.cards || []).filter(c => c.type === 'text' || c.type === 'quote')
        .map(c => c.content).filter(Boolean).join('\n---\n');

    let prompt = `[System Note: You are ${msgObj.name}. You and ${user} are talking about a Mood Board ${user} assembled — a visual collage of the scene's mood.]\n\n`;
    if (notes) prompt += `[### Text notes pinned on the board:\n${notes}]\n\n`;
    prompt += `[### The conversation so far about this board:\n`;
    prompt += `${msgObj.name}: ${msgObj.text}\n`;
    for (const t of msgObj.thread) {
        prompt += `${t.role === 'user' ? user : msgObj.name}: ${t.text}\n`;
    }
    prompt += `]\n\n`;
    prompt += `[SYSTEM COMMAND: ${user} has just replied to you directly about the board — the last line above is ${user} speaking TO YOU. Answer them in character, as a conversation. Address what they actually said; do not restate your earlier comment and do not narrate a roleplay scene. ${responseStylePrompt()}]`;
    // The standing note applies here too — it is an instruction for every reply,
    // not only for the first capture.
    const note = (boards.global?.aiNote || '').trim();
    if (note) prompt += `\n\n[${user} adds a direct instruction — follow it: ${note}]`;

    const res = await fetchFromLLM(prompt);
    msgObj.thread.push({ id: genId(), role: 'char', text: res, time: Date.now() });
    save(true);
    return res;
}

// ===== FOLDERS =====
function boardFolders() {
    const b = getBoard();
    if (!Array.isArray(b.aiFolders)) b.aiFolders = [];
    return b.aiFolders;
}

function pickFolder(msgObj) {
    const folders = boardFolders();
    const $m = $('<div class="mb-shape-picker mb-folder-menu open"></div>');
    const add = (label, fn, cls) => $(`<div class="mb-folder-opt ${cls || ''}">${label}</div>`)
        .on('click', e => { e.stopPropagation(); $m.remove(); fn(); }).appendTo($m);

    add('<i class="fa-solid fa-ban"></i> Без папки', () => { delete msgObj.folder; save(true); renderAiHistory(); });
    folders.forEach(f => add(`<i class="fa-solid fa-folder"></i> ${escHtml(f)}`, () => {
        msgObj.folder = f; save(true); renderAiHistory();
    }, msgObj.folder === f ? 'active' : ''));
    add('<i class="fa-solid fa-plus"></i> Новая папка…', async () => {
        const name = await mbPrompt('Новая папка', '', 'Например: Сцены');
        if (!name) return;
        if (!folders.includes(name)) folders.push(name);
        msgObj.folder = name;
        save(true); renderAiHistory();
    });

    $('body').append($m);
    const r = $(`#ai-msg-${msgObj.id} .act-folder`)[0].getBoundingClientRect();
    const w = $m.outerWidth();
    $m.css({ left: Math.max(8, Math.min(r.left, window.innerWidth - w - 8)), top: r.bottom + 6 });
    setTimeout(() => $(document).one('click', () => $m.remove()), 0);
}

function renderFolderBar() {
    const $bar = $('#mb-folder-bar');
    if (!$bar.length) return;
    const b = getBoard();
    const used = [...new Set((b.aiHistory || []).map(m => m.folder).filter(Boolean))];
    if (!used.length) { $bar.empty().hide(); return; }
    $bar.show().empty();
    const cur = b.aiFolderFilter || '';
    const chip = (label, val) => $(`<div class="mb-folder-chip ${cur === val ? 'active' : ''}">${label}</div>`)
        .on('click', () => { b.aiFolderFilter = val; save(); renderAiHistory(); }).appendTo($bar);
    chip('Все', '');
    used.forEach(f => chip(`<i class="fa-solid fa-folder"></i> ${escHtml(f)}`, f));
}

// ===== INSERT INTO CHAT =====
// Everything is flattened onto a single line: the wrapper tag the user relies on
// for collapsing breaks apart the moment a newline lands inside it.
function threadToOneLine(msgObj) {
    const stCtx = typeof getContext === 'function' ? getContext() : {};
    const user = stCtx.name1 || 'User';
    // Square brackets would close the wrapper's own [...] early.
    const flat = s => (s || '').replace(/\s+/g, ' ').replace(/[\[\]]/g, '').trim();
    const parts = [`${msgObj.name}: ${flat(msgObj.text)}`];
    (msgObj.thread || []).forEach(t =>
        parts.push(`${t.role === 'user' ? user : msgObj.name}: ${flat(t.text)}`));
    return `Обсуждение мудборда — ${parts.join(' — ')}`;
}

async function insertThreadIntoChat(msgObj) {
    const stCtx = typeof getContext === 'function' ? getContext() : {};
    const chat = stCtx.chat;
    if (!chat || !chat.length) {
        if (typeof toastr !== 'undefined') toastr.warning('В чате пока нет сообщений.');
        return;
    }
    // A span carrying its own inline display:none — the same shape other
    // extensions use to slip context into a message. The text reaches the model
    // but never shows in the chat, and staying on one line keeps it intact.
    const line = `<span class="mb-hidden-context" style="display:none;" title="MoodBoard Context">` +
                 `[${threadToOneLine(msgObj)}]</span>`;
    const idx = chat.length - 1;
    const mes = chat[idx];
    mes.mes = (mes.mes || '') + (mes.mes ? '\n' : '') + line;
    // A message being swiped keeps its text in two places; miss the swipe copy
    // and the insert vanishes the moment the user swipes back.
    if (Array.isArray(mes.swipes) && typeof mes.swipe_id === 'number' && mes.swipes[mes.swipe_id] !== undefined) {
        mes.swipes[mes.swipe_id] = mes.mes;
    }
    try {
        stCtx.updateMessageBlock?.(idx, mes);
        await stCtx.saveChat?.();
        if (typeof toastr !== 'undefined') toastr.success('Вшито в последнее сообщение чата');
    } catch (e) {
        console.error(LOG, e);
        if (typeof toastr !== 'undefined') toastr.error('Не удалось вшить в чат: ' + e.message);
    }
}

async function testConnection() {
    const btn = $('#mb-btn-test-api');
    const oldText = btn.html();
    btn.html('<i class="fa-solid fa-spinner fa-spin"></i>').prop('disabled', true);
    try {
        await fetchFromLLM("Test connection. Please reply with exactly one word: 'OK'.");
        toastr.success("API Connection successful!");
    } catch (e) {
        toastr.error("API Connection failed: " + e.message);
    } finally {
        btn.html(oldText).prop('disabled', false);
    }
}

// ===== CUSTOM THEME =====
// Each entry is [css variable, label, default]. Only the tones that actually
// change the look are exposed; the chip/hover washes are derived from them so a
// custom theme can never end up with invisible controls.
const THEME_FIELDS = [
    ['--mb-accent',      'Акцент',            '#d4a574'],
    ['--mb-board-bg',    'Фон доски',         '#6b4f3a'],
    ['--mb-bg-primary',  'Панели',            '#3e3026'],
    ['--mb-bg-secondary','Шапка',             '#4e3c2e'],
    ['--mb-text',        'Текст интерфейса',  '#f3e7d8'],
    ['--mb-border',      'Границы',           '#7d6449'],
    ['--mb-card-bg',     'Фон карточек',      '#fdf6e3'],
    ['--mb-card-text',   'Текст карточек',    '#3c2a1a'],
    ['--mb-pin-color',   'Кнопки-булавки',    '#e74c3c'],
];

function customTheme() {
    if (!boards.global) boards.global = { cards: [] };
    if (!boards.global.customTheme) boards.global.customTheme = { vars: {}, bg: null };
    const t = boards.global.customTheme;
    if (!t.vars) t.vars = {};
    return t;
}
function savedThemes() {
    if (!boards.global) boards.global = { cards: [] };
    if (!Array.isArray(boards.global.savedThemes)) boards.global.savedThemes = [];
    return boards.global.savedThemes;
}

// Rough perceived brightness, used to pick readable derived tones.
function isLight(hex) {
    const m = /^#?([0-9a-f]{6})$/i.exec(hex || '');
    if (!m) return false;
    const n = parseInt(m[1], 16);
    return (((n >> 16 & 255) * 299 + (n >> 8 & 255) * 587 + (n & 255) * 114) / 1000) > 140;
}

function applyCustomTheme() {
    const t = customTheme();
    let el = document.getElementById('mb-custom-theme-css');
    if (!el) {
        el = document.createElement('style');
        el.id = 'mb-custom-theme-css';
        document.head.appendChild(el);
    }
    const v = k => t.vars[k] || (THEME_FIELDS.find(f => f[0] === k) || [])[2] || '';
    const panelLight = isLight(v('--mb-bg-primary'));
    const lines = THEME_FIELDS.map(([k]) => `    ${k}: ${v(k)};`);
    // Derived tones so nothing has to be hand-tuned to stay legible.
    lines.push(`    --mb-text-muted: ${panelLight ? 'rgba(0,0,0,0.55)' : 'rgba(255,255,255,0.62)'};`);
    lines.push(`    --mb-on-accent: ${isLight(v('--mb-accent')) ? '#1a1a1a' : '#ffffff'};`);
    lines.push(`    --mb-accent-hover: ${v('--mb-accent')};`);
    lines.push(`    --mb-bg-input: ${panelLight ? 'rgba(255,255,255,0.85)' : 'rgba(0,0,0,0.35)'};`);
    lines.push(`    --mb-chip: ${panelLight ? 'rgba(0,0,0,0.05)' : 'rgba(255,255,255,0.07)'};`);
    lines.push(`    --mb-chip-strong: ${panelLight ? 'rgba(0,0,0,0.11)' : 'rgba(255,255,255,0.14)'};`);
    lines.push(`    --mb-card-shadow: 0 3px 14px rgba(0,0,0,0.32);`);
    lines.push(`    --mb-font-handwritten: 'Caveat', cursive;`);
    // The backdrop lives on the viewport-sized canvas area, never on the 4000px
    // inner surface — so it costs one fixed-size paint no matter how far you zoom.
    lines.push(`    --mb-board-texture: ${t.bg ? `url(${t.bg.src})` : 'none'};`);

    let css = `[data-mb-theme="custom"] {\n${lines.join('\n')}\n}`;
    if (t.bg) {
        const size = t.bg.mode === 'tile' ? 'auto' : 'cover';
        const repeat = t.bg.mode === 'tile' ? 'repeat' : 'no-repeat';
        css += `\n[data-mb-theme="custom"] .mb-canvas-area {
    background-size: ${size};
    background-repeat: ${repeat};
    background-position: center;
    background-attachment: local;
}`;
    }
    el.textContent = css;
}

function applyTheme(t) {
    document.documentElement.setAttribute('data-mb-theme', t || 'cork');
    if (t === 'custom') applyCustomTheme();
    $('#mb-edit-theme').toggle(t === 'custom');
}

let camSaveTimer = null;
// Where the camera sits is deliberately NOT part of the board. A board save
// re-serializes every image pinned to it — on a phone with a busy board that is
// hundreds of milliseconds of frozen UI — and panning must never cost that.
// localStorage is instant, and a per-device camera is arguably the nicer
// behaviour anyway.
function camKey() { return 'mb_cam_' + boardKey(); }
function saveCamera() {
    clearTimeout(camSaveTimer);
    camSaveTimer = setTimeout(() => {
        try { localStorage.setItem(camKey(), JSON.stringify({ panX, panY, zoom })); } catch (e) {}
    }, 500);
}
// Falls back to `board.camera`, which is where older builds stored it.
function loadCamera() {
    try {
        const raw = localStorage.getItem(camKey());
        if (raw) {
            const c = JSON.parse(raw);
            if (Number.isFinite(c?.panX) && Number.isFinite(c?.panY) && Number.isFinite(c?.zoom)) return c;
        }
    } catch (e) {}
    const b = getBoard();
    return b.camera && Number.isFinite(b.camera.zoom) ? b.camera : null;
}
function applyCamera() {
    const c = loadCamera();
    if (!c) { centerViewport(); return; }
    panX = c.panX; panY = c.panY; zoom = c.zoom;
    updateTransform();
}

function centerViewport() {
    const area = document.getElementById('mb-canvas-area');
    if (!area) return;
    const w = area.clientWidth, h = area.clientHeight;
    // Center on the middle of the board
    panX = w / 2 - (BOARD_SIZE / 2) * zoom;
    panY = h / 2 - (BOARD_SIZE / 2) * zoom;
    // The transform transition is off by default (it fights per-frame gestures);
    // turn it on just for this one deliberate jump.
    const inner = document.getElementById('mb-canvas-inner');
    inner.classList.add('mb-smooth');
    updateTransform();
    setTimeout(() => inner.classList.remove('mb-smooth'), 260);
    saveCamera();
}

function viewportCenter() {
    const area = document.getElementById('mb-canvas-area');
    if (!area || area.clientWidth === 0) return { x: 2000, y: 2000 };
    const w = area.clientWidth, h = area.clientHeight;
    return {
        x: (w / 2 - panX) / zoom,
        y: (h / 2 - panY) / zoom
    };
}

function attachWand() {
    if ($('#mb-wand-container').length) return;
    const tryAttach = () => {
        const $menu = $('#extensionsMenu');
        if (!$menu.length) { setTimeout(tryAttach, 500); return; }
        $menu.append(`<div id="mb-wand-container" class="extension_container interactable" tabindex="0">
            <div id="mb-wand-item" class="list-group-item flex-container flexGap5 interactable" tabindex="0" style="align-items:center">
                <i class="fa-fw mb-wand-icon"></i><span>MoodBoard</span>
            </div></div>`);
        $('#mb-wand-item').on('click', () => openBoard());
    };
    tryAttach();
}

function openBoard() {
    // Someone may have edited on another device since this tab last looked.
    pullIfNewer(true);
    $('#mb-modal').css('display','block');
    // Camera first, then the cards. The other way round, the very first cull ran
    // against last session's viewport, so on a big board every picture on it was
    // decoded before anything decided which ones were even on screen.
    const cam = loadCamera();
    if (cam) { panX = cam.panX; panY = cam.panY; zoom = cam.zoom; }
    pokeViewport();
    startViewportWatch();
    renderBoard();
    setTimeout(() => {
        if (!cam) centerViewport();
        resizeLive();
        renderInk();
        cullCards();
    }, 50);
}
function closeBoard() {
    cancelStroke();
    cancelDrag();
    cancelLink();
    $('#mb-modal').css('display','none');
    if (drawSaveTimer) serializeDrawing();
    save(true);
    injectChatImageButtons();
}

// A switch, not a checkbox: the same row markup everywhere so one block of CSS
// covers every setting that is simply on or off.
function switchRow(id, title, desc) {
    // No `for`: the input is inside the label, and having both is what makes some
    // browsers count one tap as two and flip the setting straight back.
    return `<label class="mb-switch-row">
        <span class="mb-switch-text"><b>${escHtml(title)}</b>${desc ? `<em>${escHtml(desc)}</em>` : ''}</span>
        <input type="checkbox" id="${id}" class="mb-switch-input">
        <span class="mb-switch"><span class="mb-switch-knob"></span></span>
    </label>`;
}

function buildUI() {
    $(`<div id="mb-modal"><div class="mb-shell">
        <div class="mb-header">
            <div class="mb-header-left">
                <span class="mb-title">✦ MoodBoard</span>
                <button class="mb-scope-btn active" data-scope="chat"><i class="fa-solid fa-message fa-xs"></i> Chat</button>
                <button class="mb-scope-btn" data-scope="char"><i class="fa-solid fa-user fa-xs"></i> Char</button>
                <button class="mb-scope-btn" data-scope="global"><i class="fa-solid fa-globe fa-xs"></i> Global</button>
            </div>
            <div class="mb-header-right">
                <button class="mb-icon-btn accent" id="mb-btn-analyze" title="Send board to AI"><i class="fa-solid fa-wand-magic-sparkles"></i></button>
                <button class="mb-icon-btn" id="mb-btn-ai-panel" title="AI Insights"><i class="fa-solid fa-book-open"></i></button>
                <button class="mb-icon-btn" id="mb-btn-center" title="Center view"><i class="fa-solid fa-crosshairs"></i></button>
                <button class="mb-icon-btn" id="mb-btn-settings" title="Settings"><i class="fa-solid fa-gear"></i></button>
                <i class="fa-solid fa-xmark mb-close" id="mb-btn-close"></i>
            </div>
        </div>
        <div class="mb-tabs" id="mb-tabs"></div>
        <button class="mb-toolbar-toggle" id="mb-toolbar-toggle" title="Hide / show tools"><i class="fa-solid fa-chevron-up"></i></button>
        <div class="mb-toolbar" id="mb-toolbar">
            <button class="mb-tool-btn active" data-tool="select" title="Select/Move"><i class="fa-solid fa-arrow-pointer"></i></button>
            <button class="mb-tool-btn" data-tool="text" title="Add Text"><i class="fa-solid fa-font"></i></button>
            <button class="mb-tool-btn" data-tool="image" title="Add Image"><i class="fa-solid fa-image"></i></button>
            <button class="mb-tool-btn has-menu" data-tool="collage" id="mb-btn-collage" title="Коллаж — удерживайте для выбора раскладки"><i class="fa-solid fa-grip-vertical"></i></button>
            <button class="mb-tool-btn has-menu" id="mb-btn-tree" title="Дерево связей — удерживайте для выбора вида"><i class="fa-solid fa-sitemap"></i></button>
            <div class="mb-tool-sep"></div>
            <button class="mb-tool-btn" data-tool="link" id="mb-btn-link" title="Связать карточки ниткой"><i class="fa-solid fa-circle-nodes"></i></button>
            <button class="mb-tool-btn has-menu" id="mb-btn-grid" title="Сетка и привязка — удерживайте для настроек"><i class="fa-solid fa-border-all"></i></button>
            <button class="mb-tool-btn has-menu" id="mb-btn-timeline" title="Лента времени — удерживайте для настроек"><i class="fa-solid fa-timeline"></i></button>
            <div class="mb-tool-sep"></div>
            <button class="mb-tool-btn has-menu" data-tool="draw" id="mb-btn-draw" title="Карандаш — удерживайте для настроек"><i class="fa-solid fa-pencil"></i></button>
            <button class="mb-tool-btn" data-tool="arrow" title="Arrow"><i class="fa-solid fa-arrow-right"></i></button>
            <button class="mb-tool-btn has-menu" data-tool="shape" id="mb-btn-shape" title="Shape — long-press for more"><i class="fa-solid fa-square"></i></button>
            <button class="mb-tool-btn" data-tool="eraser" title="Eraser"><i class="fa-solid fa-eraser"></i></button>
            <button class="mb-tool-btn" id="mb-btn-undo" title="Отменить последнее — штрих, удалённую карточку или очистку доски"><i class="fa-solid fa-rotate-left"></i></button>
            <div class="mb-tool-sep"></div>
            <div class="mb-color-row" id="mb-color-row"></div>
            <div class="mb-color-picker mb-custom-color-btn" title="Custom color"><i class="fa-solid fa-palette"></i></div>
            <div class="mb-tool-sep"></div>
            <button class="mb-tool-btn" id="mb-btn-stickers" title="Stickers"><i class="fa-solid fa-face-smile"></i></button>
            <div class="mb-tool-sep"></div>
            <div class="mb-custom-select" id="mb-stroke-dropdown">
                <div class="mb-select-value" style="font-family:'Font Awesome 6 Free';font-weight:900">&#xf304; Size</div>
                <div class="mb-select-options">
                    <div data-val="2">Thin</div><div data-val="3">Normal</div>
                    <div data-val="6">Thick</div><div data-val="10">Bold</div>
                </div>
            </div>
        </div>
        <div class="mb-select-bar" id="mb-select-bar">
            <span class="mb-select-info">Выбрано: <b class="mb-select-count">0</b></span>
            <div class="mb-select-acts">
                <button class="mb-select-btn ghost" id="mb-select-style" title="Стиль ответа"><i class="fa-solid fa-scale-balanced"></i> <span id="mb-style-chip">Сбалансированно</span></button>
                <button class="mb-select-btn" id="mb-select-send"><i class="fa-solid fa-wand-magic-sparkles"></i> Отправить</button>
                <button class="mb-select-btn ghost" id="mb-select-cancel">Отмена</button>
            </div>
        </div>
        <div class="mb-canvas-area" id="mb-canvas-area">
            <div class="mb-canvas-inner" id="mb-canvas-inner">
                <div class="mb-grid-layer" id="mb-grid-layer"></div>
                <canvas class="mb-draw-canvas" id="mb-draw-canvas" width="${DRAW_RES}" height="${DRAW_RES}"></canvas>
            </div>
            <canvas class="mb-live-canvas" id="mb-draw-live"></canvas>
            <canvas class="mb-live-canvas mb-live-top" id="mb-draw-live-top"></canvas>
            <div class="mb-zoom-indicator" id="mb-zoom-ind">100%</div>
            <div class="mb-settings-panel" id="mb-settings">
                <div class="mb-panel-head">
                    <strong>Настройки</strong>
                    <i class="fa-solid fa-xmark mb-panel-close" data-close="#mb-settings" title="Закрыть"></i>
                </div>
                <div class="mb-panel-body">
                <span class="mb-settings-label">Тема</span>
                <div class="mb-custom-select mb-select-wide" id="mb-theme-dropdown">
                    <div class="mb-select-value">🪵 Cork Board</div>
                    <div class="mb-select-options">
                        <div data-val="cork">🪵 Cork Board</div>
                        <div data-val="auto">✨ Tavern Auto</div>
                        <div data-val="linen">🧵 Linen</div>
                        <div data-val="ink">🖋 Ink &amp; Paper</div>
                        <div data-val="plum">🍇 Plum Velvet</div>
                        <div data-val="forest">🌿 Deep Forest</div>
                        <div data-val="custom">🎨 Своя тема</div>
                    </div>
                </div>
                <button class="mb-settings-btn secondary" id="mb-edit-theme" style="display:none;margin-top:8px"><i class="fa-solid fa-sliders"></i> Настроить тему</button>
                <span class="mb-settings-label">Экспорт / импорт</span>
                <button class="mb-settings-btn" id="mb-export-png"><i class="fa-solid fa-image"></i> Сохранить доску в PNG</button>
                <button class="mb-settings-btn secondary" id="mb-export">Экспорт доски (JSON)</button>
                <button class="mb-settings-btn secondary" id="mb-export-all"><i class="fa-solid fa-shield-halved"></i> Резервная копия всех досок</button>
                <button class="mb-settings-btn secondary" id="mb-import">Импорт доски (JSON)</button>
                <div class="mb-sync-line"><span class="mb-sync" id="mb-sync" data-state="ok"></span><span id="mb-sync-text">Доски сохраняются на сервере</span></div>
                <div class="mb-select-hint">Доски лежат на сервере, поэтому одинаковы на телефоне и компьютере, а очистка данных браузера их не тронет. Резервная копия — на случай, если захочется откатиться или перенести всё в другую установку.</div>
                <span class="mb-settings-label" style="margin-top:20px">Интеграция с ИИ</span>
                <span class="mb-settings-label" style="margin-top:0">Профиль подключения</span>
                <div class="mb-custom-select mb-select-wide" id="mb-api-dropdown">
                    <div class="mb-select-value">Default Tavern AI</div>
                    <div class="mb-select-options"></div>
                </div>
                <span class="mb-settings-label">Стиль ответа</span>
                <div class="mb-custom-select mb-select-wide" id="mb-style-dropdown">
                    <div class="mb-select-value">⚖️ Сбалансированно</div>
                    <div class="mb-select-options mb-rich-options"></div>
                </div>
                <div id="mb-style-hint" class="mb-select-hint"></div>
                <div id="mb-custom-prompt-wrap" style="display:none">
                    <textarea id="mb-custom-prompt" class="mb-settings-input" rows="4" placeholder="Например: Ответь одним абзацем от лица твоей сестры, которая случайно увидела эту доску."></textarea>
                    <div class="mb-select-hint">Пишите как указание персонажу, по-русски или по-английски: кто говорит, какой длины ответ, что делать и чего не делать. Эта строка подставляется в конец промпта, всё остальное — картинка доски, заметки и контекст чата — передаётся как обычно.</div>
                </div>
                <div class="mb-ctx-head">
                    <span>Контекст (сообщений)</span>
                    <input type="number" id="mb-ctx-num" class="mb-ctx-num" min="0" max="${CTX_MAX}" step="1" value="10">
                </div>
                <input type="range" id="mb-ctx-slider" min="0" max="${CTX_MAX}" value="10" style="width:100%;margin-bottom:4px">
                <div class="mb-select-hint">Сколько последних сообщений чата уходит вместе с доской. Можно вписать точное число в окошко — до ${CTX_MAX}. Чем больше, тем дороже запрос и тем выше шанс упереться в лимит контекста модели.</div>
                <span class="mb-settings-label" style="margin-top:18px">Что отправлять вместе с доской</span>
                ${switchRow('mb-tg-charcard', 'Карту персонажа', 'Описание и характер того, кто отвечает')}
                ${switchRow('mb-tg-persona', 'Карту персоны', 'Описание вас — то, что стоит в «Persona»')}
                ${switchRow('mb-tg-lore', 'Лорбуки', 'Записи мира, сработавшие по ключевым словам')}
                ${switchRow('mb-tg-note', 'Авторские заметки', 'Заметка этого чата, персонажа или общая')}
                <div class="mb-select-hint">Авторская заметка — то, что вписано в «Author’s Note»: как обстоят дела сейчас. Берётся заметка этого чата, к ней добавляется привязанная к персонажу, а если обеих нет — общая. Не длиннее ${NOTE_MAX} символов.</div>
                <div class="mb-select-hint">Лорбуки подбираются так же, как в обычном ответе персонажа: по ключевым словам из заметок на доске и из последних сообщений. Значит, НПС, который живёт в лорбуке, приедет вместе с доской, если он на ней упомянут — а записи, помеченные как постоянные (синие), приезжают всегда. Отправляется не больше ${LORE_MAX} символов, чтобы запрос не раздулся.</div>
                <button class="mb-settings-btn secondary" id="mb-btn-test-api"><i class="fa-solid fa-plug"></i> Проверить подключение</button>
                <span class="mb-settings-label" style="margin-top:20px">Кнопки «+» в чате</span>
                ${switchRow('mb-tg-quote', 'Цитаты', 'Кнопка «+» рядом с выделенным текстом')}
                ${switchRow('mb-tg-image', 'Картинки', 'Кнопка «+» в углу картинок в чате')}
                <div class="mb-select-hint">Выключенная кнопка просто не появляется — всё уже прикреплённое на досках остаётся на месте.</div>
                <span class="mb-settings-label">Где держать кнопку на картинке</span>
                <div class="mb-corner-row" id="mb-pin-pos">
                    <div class="mb-corner-opt" data-pos="tl"><span class="mb-corner-box"><i></i></span>Сверху слева</div>
                    <div class="mb-corner-opt" data-pos="tr"><span class="mb-corner-box"><i></i></span>Сверху справа</div>
                    <div class="mb-corner-opt" data-pos="bl"><span class="mb-corner-box"><i></i></span>Снизу слева</div>
                    <div class="mb-corner-opt" data-pos="br"><span class="mb-corner-box"><i></i></span>Снизу справа</div>
                </div>
                <div class="mb-select-hint">Свои кнопки — увеличить, перерисовать, удалить — SillyTavern держит вдоль верхнего края картинки, и на узком экране наша кнопка попадала прямо под корзину. Поэтому по умолчанию она внизу справа; если у вашей темы занят другой угол, выберите свободный.</div>

                <span class="mb-settings-label" style="margin-top:20px">Свои рамки</span>
                <button class="mb-settings-btn secondary" id="mb-add-frame"><i class="fa-solid fa-plus"></i> Загрузить рамку (PNG)</button>
                <input type="file" id="mb-frame-file" accept="image/png,image/webp" multiple style="display:none">
                <div class="mb-select-hint">PNG с прозрачной серединой — получится рамка; сплошная плашка или мазок — получится подложка под текст. Пустые поля по краям обрезаются сами, а ширина полосы подстраивается под размер карточки: середина тянется, края остаются целыми.</div>
                <button class="mb-settings-btn secondary" id="mb-reprocess-frames"><i class="fa-solid fa-arrows-rotate"></i> Пересобрать мои рамки</button>
                <div class="mb-select-hint">Для тех, что загружены раньше: обрежет поля, пережмёт и пересчитает, как их растягивать.</div>
                <div class="mb-custom-list" id="mb-frame-list"></div>

                <span class="mb-settings-label" style="margin-top:20px">Свои шрифты</span>
                <input type="text" id="mb-font-url" class="mb-settings-input" placeholder="Ссылка на шрифт">
                <button class="mb-settings-btn secondary" id="mb-add-font"><i class="fa-solid fa-plus"></i> Добавить по ссылке</button>
                <button class="mb-settings-btn secondary" id="mb-add-font-file"><i class="fa-solid fa-upload"></i> Загрузить файл шрифта</button>
                <input type="file" id="mb-font-file" accept=".woff2,.woff,.ttf,.otf,font/*" style="display:none">
                <div class="mb-select-hint">
                    Подходит одно из трёх:<br>
                    1. Google Fonts — «Get font» → «Get embed code», ссылка вида <code>https://fonts.googleapis.com/css2?family=Bad+Script</code><br>
                    2. Прямая ссылка на файл шрифта: <code>.woff2</code>, <code>.woff</code>, <code>.ttf</code>, <code>.otf</code> — с любого сайта<br>
                    3. Файл шрифта с телефона или компьютера<br>
                    Для русского текста нужен шрифт с кириллицей — если её нет, я предупрежу сразу после добавления.
                </div>
                <div class="mb-custom-list" id="mb-font-list"></div>

                <span class="mb-settings-label" style="margin-top:20px">Опасная зона</span>
                <button class="mb-settings-btn danger" id="mb-clear-board">Очистить эту доску</button>
                </div>
            </div>

            <div class="mb-settings-panel" id="mb-ai-panel">
                <div class="mb-panel-head">
                    <strong>✦ Insights</strong>
                    <i class="fa-solid fa-xmark mb-panel-close" data-close="#mb-ai-panel" title="Закрыть"></i>
                </div>
                <div class="mb-folder-bar" id="mb-folder-bar"></div>
                <div id="mb-ai-history"></div>
            </div>
            <div class="mb-settings-panel mb-panel-left" id="mb-custom-color-panel">
                <div class="mb-panel-head">
                    <strong>Свой цвет</strong>
                    <i class="fa-solid fa-xmark mb-panel-close" data-close="#mb-custom-color-panel" title="Закрыть"></i>
                </div>
                <div class="mb-panel-body">
                <input type="range" id="mb-hue-slider" min="0" max="360" value="0" style="width:100%;margin-bottom:10px">
                <input type="range" id="mb-lightness-slider" min="0" max="100" value="50" style="width:100%;margin-bottom:15px">
                <div id="mb-color-preview" style="width:100%;height:30px;border-radius:4px;background:#f00;margin-bottom:10px"></div>
                <input type="text" id="mb-hex-input" value="#ff0000" class="mb-settings-input" style="text-align:center;margin-bottom:10px">
                <button class="mb-settings-btn" id="mb-apply-color">Взять этот цвет</button>
                <button class="mb-settings-btn secondary" id="mb-pin-color"><i class="fa-solid fa-thumbtack"></i> Закрепить в палитре</button>
                <span class="mb-settings-label" style="margin-top:18px">Мои цвета</span>
                <div class="mb-saved-colors" id="mb-saved-colors"></div>
                <div class="mb-select-hint">Долгое нажатие по цвету удаляет его.</div>
                </div>
            </div>
            <div class="mb-settings-panel" id="mb-theme-panel">
                <div class="mb-panel-head">
                    <strong>Своя тема</strong>
                    <i class="fa-solid fa-xmark mb-panel-close" data-close="#mb-theme-panel" title="Закрыть"></i>
                </div>
                <div class="mb-panel-body" id="mb-theme-body"></div>
            </div>
            <div class="mb-settings-panel mb-panel-left" id="mb-frame-panel">
                <div class="mb-panel-head">
                    <strong>✎ Редактирование</strong>
                    <i class="fa-solid fa-xmark mb-panel-close" data-close="#mb-frame-panel" title="Закрыть"></i>
                </div>
                <div class="mb-panel-body" id="mb-frame-body"></div>
            </div>
            <div class="mb-settings-panel mb-panel-left" id="mb-stickers">
                <div class="mb-panel-head">
                    <strong>Стикеры</strong>
                    <i class="fa-solid fa-xmark mb-panel-close" data-close="#mb-stickers" title="Закрыть"></i>
                </div>
                <div class="mb-panel-body">
                <div class="mb-sticker-grid" id="mb-sticker-grid"></div>
                <button class="mb-settings-btn secondary" id="mb-upload-sticker" style="margin-top:10px">Загрузить свой стикер</button>
                <input type="file" id="mb-sticker-file-input" accept="image/*" multiple style="display:none">
                <button class="mb-settings-btn secondary" id="mb-trim-stickers"><i class="fa-solid fa-crop-simple"></i> Обрезать пустые поля</button>
                <div class="mb-select-hint">У новых стикеров прозрачные поля срезаются сами. Кнопка выше — для тех, что уже лежат в галерее. Крестик на стикере убирает его отсюда.</div>
                </div>
            </div>
            <div class="mb-settings-panel mb-panel-left" id="mb-tree-panel">
                <div class="mb-panel-head">
                    <strong>Дерево связей</strong>
                    <i class="fa-solid fa-xmark mb-panel-close" data-close="#mb-tree-panel" title="Закрыть"></i>
                </div>
                <div class="mb-panel-body" id="mb-tree-body"></div>
            </div>
            <div class="mb-settings-panel mb-panel-left" id="mb-timeline-panel">
                <div class="mb-panel-head">
                    <strong>Лента времени</strong>
                    <i class="fa-solid fa-xmark mb-panel-close" data-close="#mb-timeline-panel" title="Закрыть"></i>
                </div>
                <div class="mb-panel-body" id="mb-timeline-body"></div>
            </div>
            <div class="mb-shape-picker" id="mb-shape-picker"></div>
            <div class="mb-brush-panel" id="mb-grid-picker"></div>
            <div class="mb-brush-panel" id="mb-tree-picker"></div>
            <div class="mb-brush-panel" id="mb-link-menu"></div>
            <div class="mb-brush-panel" id="mb-avatar-picker"></div>
            <div class="mb-brush-panel" id="mb-brush-panel"></div>
            <div class="mb-brush-panel" id="mb-collage-picker"></div>
            <div class="mb-brush-panel" id="mb-style-picker"></div>
        </div>
    </div></div>`).appendTo('body');

    $(`<div id="mb-quote-popup">+</div>`).appendTo('body');
    $('<input type="file" id="mb-file-input" accept="image/*" style="display:none">').appendTo('body');
    $('<input type="file" id="mb-collage-input" accept="image/*" multiple style="display:none">').appendTo('body');
    $('<input type="file" id="mb-theme-bg-input" accept="image/*" style="display:none">').appendTo('body');
    bindEvents();
}

// ===== DIALOGS =====
// The browser's own prompt()/confirm() boxes look nothing like the rest of the
// board and, on Android, steal focus in a way that leaves the keyboard state
// muddled. These are plain elements inside the modal instead.
function mbDialog({ title, text, value, placeholder, okLabel = 'OK', cancelLabel = 'Отмена', danger = false, input = false }) {
    return new Promise(resolve => {
        $('#mb-dialog').remove();
        const $d = $(`<div id="mb-dialog" class="mb-dialog-back">
            <div class="mb-dialog">
                <div class="mb-dialog-title">${escHtml(title || '')}</div>
                ${text ? `<div class="mb-dialog-text">${escHtml(text)}</div>` : ''}
                ${input ? `<input type="text" class="mb-dialog-input" placeholder="${escHtml(placeholder || '')}">` : ''}
                <div class="mb-dialog-btns">
                    <button class="mb-dialog-btn cancel">${escHtml(cancelLabel)}</button>
                    <button class="mb-dialog-btn ok ${danger ? 'danger' : ''}">${escHtml(okLabel)}</button>
                </div>
            </div>
        </div>`).appendTo('body');

        const $inp = $d.find('.mb-dialog-input');
        if (input) { $inp.val(value || ''); setTimeout(() => $inp.trigger('focus').trigger('select'), 30); }

        const done = (result) => {
            $d.remove();
            // Give the keyboard a beat to retract before anything re-measures.
            if (typeof syncViewport === 'function') setTimeout(syncViewport, 320);
            resolve(result);
        };
        $d.find('.ok').on('click', () => done(input ? ($inp.val() || '').trim() : true));
        $d.find('.cancel').on('click', () => done(input ? null : false));
        $d.on('click', e => { if (e.target === $d[0]) done(input ? null : false); });
        $d.on('keydown', e => {
            e.stopPropagation();
            if (e.key === 'Enter' && input) { e.preventDefault(); done(($inp.val() || '').trim()); }
            if (e.key === 'Escape') { e.preventDefault(); done(input ? null : false); }
        });
    });
}
// ===== COLOUR PICKER =====
function hexToHsl(hex) {
    const m = /^#?([0-9a-f]{6})$/i.exec((hex || '').trim());
    if (!m) return { h: 0, s: 70, l: 50 };
    const n = parseInt(m[1], 16);
    const r = (n >> 16 & 255) / 255, g = (n >> 8 & 255) / 255, b = (n & 255) / 255;
    const max = Math.max(r, g, b), min = Math.min(r, g, b);
    const l = (max + min) / 2;
    let h = 0, s = 0;
    if (max !== min) {
        const d = max - min;
        s = l > 0.5 ? d / (2 - max - min) : d / (max + min);
        if (max === r) h = ((g - b) / d + (g < b ? 6 : 0));
        else if (max === g) h = (b - r) / d + 2;
        else h = (r - g) / d + 4;
        h *= 60;
    }
    return { h: Math.round(h), s: Math.round(s * 100), l: Math.round(l * 100) };
}
function hslToHex(h, s, l) {
    s /= 100; l /= 100;
    const a = s * Math.min(l, 1 - l);
    const f = n => {
        const k = (n + h / 30) % 12;
        const v = l - a * Math.max(Math.min(k - 3, 9 - k, 1), -1);
        return Math.round(255 * v).toString(16).padStart(2, '0');
    };
    return `#${f(0)}${f(8)}${f(4)}`;
}

// Replaces the browser's own colour dialog, which on Android is an eight-swatch
// grid with a cramped "custom" link — unusable for picking a theme.
function mbColorPicker(title, initial) {
    return new Promise(resolve => {
        $('#mb-dialog').remove();
        let { h, s, l } = hexToHsl(initial || '#d4a574');

        const $d = $(`<div id="mb-dialog" class="mb-dialog-back">
            <div class="mb-dialog mb-color-dialog">
                <div class="mb-dialog-title">${escHtml(title || 'Цвет')}</div>
                <div class="mb-cp-preview"></div>
                <input type="text" class="mb-dialog-input mb-cp-hex" spellcheck="false">
                <div class="mb-cp-row"><span>Тон</span><input type="range" class="mb-cp-h" min="0" max="360"></div>
                <div class="mb-cp-row"><span>Насыщ.</span><input type="range" class="mb-cp-s" min="0" max="100"></div>
                <div class="mb-cp-row"><span>Яркость</span><input type="range" class="mb-cp-l" min="0" max="100"></div>
                <div class="mb-cp-saved"></div>
                <div class="mb-dialog-btns">
                    <button class="mb-dialog-btn cancel">Отмена</button>
                    <button class="mb-dialog-btn ok">Выбрать</button>
                </div>
            </div>
        </div>`).appendTo('body');

        const $prev = $d.find('.mb-cp-preview'), $hex = $d.find('.mb-cp-hex');
        const $h = $d.find('.mb-cp-h'), $s = $d.find('.mb-cp-s'), $l = $d.find('.mb-cp-l');

        const paint = () => {
            const hex = hslToHex(h, s, l);
            $prev.css('background', hex);
            $hex.val(hex);
            // Each slider previews the axis it controls, so the effect is visible
            // before you drag it.
            $s.css('background', `linear-gradient(to right, ${hslToHex(h,0,l)}, ${hslToHex(h,100,l)})`);
            $l.css('background', `linear-gradient(to right, #000, ${hslToHex(h,s,50)}, #fff)`);
            $h.val(h); $s.val(s); $l.val(l);
        };
        paint();

        $h.on('input', function() { h = +this.value; paint(); });
        $s.on('input', function() { s = +this.value; paint(); });
        $l.on('input', function() { l = +this.value; paint(); });
        $hex.on('input change', function() {
            const v = this.value.trim();
            if (/^#?[0-9a-f]{6}$/i.test(v)) {
                ({ h, s, l } = hexToHsl(v));
                const keep = this.selectionStart;
                paint();
                this.value = v.startsWith('#') ? v : '#' + v;
                this.setSelectionRange(keep, keep);
            }
        });

        // Recently used and pinned colours, both one tap away.
        const $sv = $d.find('.mb-cp-saved');
        const strip = (label, list) => {
            if (!list.length) return;
            $sv.append(`<span class="mb-cp-saved-label">${label}</span>`);
            list.forEach(c => $(`<span class="mb-saved-dot" style="background:${c}"></span>`)
                .on('click', () => { ({ h, s, l } = hexToHsl(c)); paint(); }).appendTo($sv));
        };
        strip('Недавние', (boards.global?.recentColors || []).slice(0, 9));
        strip('Мои цвета', (boards.global?.savedColors || []));

        const done = v => {
            if (v) { rememberColor(v); save(); }
            $d.remove();
            if (typeof syncViewport === 'function') setTimeout(syncViewport, 300);
            resolve(v);
        };
        $d.find('.ok').on('click', () => done(hslToHex(h, s, l)));
        $d.find('.cancel').on('click', () => done(null));
        $d.on('click', e => { if (e.target === $d[0]) done(null); });
        $d.on('keydown', e => {
            e.stopPropagation();
            if (e.key === 'Escape') { e.preventDefault(); done(null); }
            if (e.key === 'Enter') { e.preventDefault(); done(hslToHex(h, s, l)); }
        });
    });
}

const mbConfirm = (title, text, opts = {}) => mbDialog({ title, text, okLabel: opts.okLabel || 'Да', danger: opts.danger });
const mbPrompt = (title, value, placeholder) => mbDialog({ title, value, placeholder, input: true, okLabel: 'Сохранить' });

// Exactly one side panel is open at a time. Returns whether the target ended up open.
const ALL_PANELS = '#mb-settings, #mb-ai-panel, #mb-stickers, #mb-custom-color-panel, #mb-frame-panel, #mb-theme-panel, #mb-tree-panel, #mb-timeline-panel';
function togglePanel(sel, force) {
    const $t = $(sel);
    const willOpen = force !== undefined ? force : !$t.hasClass('open');
    // Dismiss any open note editor first. Leaving it focused keeps the phone
    // keyboard up while a panel slides in, and the layout ends up sized for a
    // viewport that is no longer there.
    commitOpenEditor();
    if (document.activeElement && document.activeElement !== document.body) {
        try { document.activeElement.blur(); } catch (e) {}
    }
    $(ALL_PANELS).removeClass('open');
    $t.toggleClass('open', willOpen);
    if (sel !== '#mb-settings') settingsOpen = false;
    if (sel !== '#mb-ai-panel') aiPanelOpen = false;
    // The keyboard takes a moment to retract; keep re-measuring until it has.
    pokeViewport();
    return willOpen;
}

// Pins an open dropdown to the viewport in fixed coordinates. Anchoring it to
// the trigger with CSS put it off-screen whenever the trigger sat near an edge —
// on a phone the toolbar's size menu opened past the left margin, and reparenting
// it to escape that pushed it below the fold entirely.
function placeSelectMenu(selectEl, keepSide) {
    const menu = selectEl.querySelector('.mb-select-options');
    if (!menu) return;
    const pad = 8;
    // Measure at natural size first.
    menu.style.cssText = 'position:fixed;visibility:hidden;display:block;max-height:none;left:0;top:0;right:auto';
    const mw = menu.offsetWidth, mh = menu.offsetHeight;
    const a = selectEl.getBoundingClientRect();
    const vw = window.innerWidth, vh = window.innerHeight;

    let left = Math.min(a.right - mw, vw - mw - pad);   // right-aligned by default
    left = Math.max(pad, left);

    // Which side to open on is decided once, when the menu opens, and then kept.
    // Re-deciding it on every scroll made the menu leap from above the trigger to
    // below it the instant enough room appeared.
    const roomBelow = vh - (a.bottom + 6) - pad;
    const side = keepSide || (roomBelow < Math.min(mh, 180) && a.top > roomBelow ? 'up' : 'down');
    selectEl._mbMenuSide = side;

    let top, maxH;
    if (side === 'up') {
        maxH = a.top - 6 - pad;
        top = Math.max(pad, a.top - 6 - Math.min(mh, Math.max(120, maxH)));
    } else {
        top = a.bottom + 6;
        maxH = vh - top - pad;
    }
    menu.style.cssText =
        `position:fixed;display:block;left:${left}px;top:${top}px;right:auto;` +
        `max-width:${vw - pad * 2}px;max-height:${Math.max(120, maxH)}px;overflow-y:auto;z-index:1000001`;
}

// Being pinned in viewport coordinates, an open menu would otherwise hang in
// place while the panel behind it scrolls away. Re-anchor it to its trigger on
// every scroll, and give up once the trigger itself is no longer visible.
let menuScrollHook = null;
function trackSelectMenu(selectEl) {
    untrackSelectMenu();
    const onScroll = (e) => {
        if (e.target?.classList?.contains('mb-select-options')) return; // scrolling inside the menu
        const r = selectEl.getBoundingClientRect();
        if (r.bottom < 0 || r.top > window.innerHeight) {
            $(selectEl).removeClass('open');
            const m = selectEl.querySelector('.mb-select-options');
            if (m) m.style.cssText = '';
            untrackSelectMenu();
            return;
        }
        placeSelectMenu(selectEl, selectEl._mbMenuSide);
    };
    document.addEventListener('scroll', onScroll, { capture: true, passive: true });
    menuScrollHook = onScroll;
}
function untrackSelectMenu() {
    if (!menuScrollHook) return;
    document.removeEventListener('scroll', menuScrollHook, { capture: true });
    menuScrollHook = null;
}

function selectTool(t) {
    cancelStroke();
    cancelLink();
    tool = t;
    // The grid / timeline / tree buttons are switches, not tools; they light up on
    // their own state and must not be cleared here.
    $('.mb-tool-btn[data-tool]').removeClass('active');
    $(`.mb-tool-btn[data-tool="${t}"]`).addClass('active');
    const isDraw = ['draw','arrow','shape','eraser'].includes(t);
    $('#mb-draw-canvas').toggleClass('active', isDraw);
    $('#mb-canvas-area').toggleClass('drawing', isDraw);
    $('#mb-canvas-area').toggleClass('linking', t === 'link');
    if (t === 'text') addCard('', 'text');
    if (t === 'image') $('#mb-file-input').trigger('click');
    if (t === 'collage') $('#mb-collage-input').trigger('click');
}

// ===== PALETTE =====
const BASE_COLORS = ['#e74c3c','#3498db','#2ecc71','#f39c12','#9b59b6','#1a1a1a','#ffffff'];
function savedColors() {
    if (!boards.global) boards.global = { cards: [] };
    if (!Array.isArray(boards.global.savedColors)) boards.global.savedColors = [];
    return boards.global.savedColors;
}
function renderColorRow() {
    const $row = $('#mb-color-row').empty();
    const all = [...BASE_COLORS, ...savedColors()];
    all.forEach(c => {
        const border = c.toLowerCase() === '#ffffff' ? ';border:1px solid #bbb' : '';
        $row.append(`<div class="mb-color-dot ${c === drawColor ? 'active' : ''}" data-color="${c}" style="background:${c}${border}"></div>`);
    });
}
function renderSavedColors() {
    const $g = $('#mb-saved-colors').empty();
    const saved = savedColors();
    if (!saved.length) { $g.append('<div class="mb-empty-hint">No pinned colors yet.</div>'); return; }
    saved.forEach(c => {
        const $d = $(`<div class="mb-saved-dot" data-color="${c}" style="background:${c}"></div>`);
        let hold = null;
        $d.on('pointerdown', () => {
            hold = setTimeout(() => {
                const i = savedColors().indexOf(c);
                if (i >= 0) savedColors().splice(i, 1);
                save(); renderColorRow(); renderSavedColors();
            }, 500);
        }).on('pointerup pointerleave pointercancel', () => clearTimeout(hold));
        $d.on('click', () => {
            drawColor = c;
            $('.mb-color-dot').removeClass('active');
            $(`.mb-color-dot[data-color="${c}"]`).addClass('active');
            $('#mb-hex-input').val(c);
            $('#mb-color-preview').css('background', c);
        });
        $g.append($d);
    });
}

// html2canvas can't render CSS masks, clip-path, outline, or gradients on
// pseudo-elements, so several frames came out as plain rectangles in the PNG.
// Rewrite those effects on the *clone* into real elements and borders, which it
// does render. The live board is untouched.
// html2canvas ignores object-fit and stretches the image to the element box,
// which is why circular photos came out squashed. Pre-crop them to the same
// region `cover` would have shown, so the rasterizer only has to scale 1:1.
function precropCoverImages(clone) {
    const jobs = [];
    // Only .shape-circle actually crops: film sets object-fit but leaves height
    // auto, so the box already matches the image and nothing is cut.
    clone.querySelectorAll('.mb-card.shape-circle img').forEach(img => {
        const box = img.getBoundingClientRect();
        const w = Math.round(box.width) || img.naturalWidth;
        const h = Math.round(box.height) || img.naturalHeight;
        const nw = img.naturalWidth, nh = img.naturalHeight;
        if (!w || !h || !nw || !nh) return;
        const targetRatio = w / h, srcRatio = nw / nh;
        // the source rectangle `cover` would pick
        let sw = nw, sh = nh, sx = 0, sy = 0;
        if (srcRatio > targetRatio) { sw = nh * targetRatio; sx = (nw - sw) / 2; }
        else { sh = nw / targetRatio; sy = (nh - sh) / 2; }
        const c = document.createElement('canvas');
        // render at 2x the layout box so the export still has detail to work with
        c.width = Math.max(1, Math.round(w * 2));
        c.height = Math.max(1, Math.round(h * 2));
        c.getContext('2d').drawImage(img, sx, sy, sw, sh, 0, 0, c.width, c.height);
        jobs.push(new Promise(res => {
            img.onload = img.onerror = () => res();
            img.src = c.toDataURL('image/webp', 0.92);
            img.style.objectFit = 'fill';
        }));
    });
    return Promise.all(jobs);
}

// Belt and braces around the culler: whatever state the live board was in, every
// card in the copy we are about to rasterize is awake and carries its picture.
function wakeCloneCards(clone) {
    clone.querySelectorAll('.mb-card').forEach(el => {
        el.style.visibility = '';
        delete el.dataset.mbUnloaded;
    });
    clone.querySelectorAll('img[data-mb-src]').forEach(img => {
        img.setAttribute('src', img.dataset.mbSrc);
        delete img.dataset.mbSrc;
        img.style.width = ''; img.style.height = '';
    });
}

function prepareCloneForExport(clone, boardBg) {
    wakeCloneCards(clone);
    const notch = (parent, css) => {
        const d = document.createElement('div');
        d.style.cssText = 'position:absolute;' + css;
        parent.appendChild(d);
        return d;
    };
    clone.querySelectorAll('.mb-card').forEach(card => {
        const cs = getComputedStyle(card);
        const cardBg = cs.backgroundColor;
        // The card element itself has no colour of its own; the ink colour these
        // frames are drawn in lives on the theme variable.
        const textCol = cs.getPropertyValue('--mb-card-text').trim() || '#333';

        if (card.classList.contains('shape-gold')) {
            // background-clip:border-box gradient -> a plain thick border
            card.style.backgroundImage = 'none';
            card.style.backgroundColor = 'var(--mb-card-bg)';
            card.style.border = '5px solid #c9a227';
        }
        if (card.classList.contains('shape-double')) {
            // outline + outline-offset is dropped, and so is a box-shadow ring;
            // only a real bordered element survives the rasterizer.
            card.style.outline = 'none';
            notch(card, `left:-5px;right:-5px;top:-5px;bottom:-5px;border:1px solid ${textCol};`);
        }
        if (card.classList.contains('shape-ticket')) {
            const inner = card.querySelector('.mb-card-content');
            if (inner) { inner.style.webkitMask = 'none'; inner.style.mask = 'none'; }
            card.style.background = cardBg !== 'rgba(0, 0, 0, 0)' ? cardBg : 'var(--mb-card-bg)';
            // punch the side notches with two board-coloured circles
            const c = `width:22px;height:22px;border-radius:50%;background:${boardBg};top:50%;margin-top:-11px;`;
            notch(card, c + 'left:-11px;');
            notch(card, c + 'right:-11px;');
        }
        if (card.classList.contains('shape-torn')) {
            const inner = card.querySelector('.mb-card-content');
            if (inner) { inner.style.clipPath = 'none'; inner.style.background = 'var(--mb-card-bg)'; }
            card.style.filter = 'none';
            // Stacked gradients don't composite reliably in html2canvas, so build
            // the teeth from individual rotated squares instead.
            const strip = notch(card, 'left:0;right:0;bottom:-6px;height:14px;overflow:hidden;');
            const w = card.offsetWidth || 210;
            for (let i = 0; i * 10 < w + 10; i++) {
                notch(strip, `left:${i * 10 - 5}px;top:1px;width:10px;height:10px;` +
                    `background:${boardBg};transform:rotate(45deg);`);
            }
        }
        if (card.classList.contains('shape-tape') || card.classList.contains('shape-washi')) {
            // ::before/::after can't be captured — recreate them as real divs
            const strip = 'height:20px;width:54px;background:linear-gradient(135deg,rgba(255,255,255,0.75),rgba(205,185,228,0.75));box-shadow:0 1px 3px rgba(0,0,0,0.2);';
            if (card.classList.contains('shape-washi')) {
                notch(card, strip + 'top:-9px;left:-12px;transform:rotate(-28deg);');
                notch(card, strip + 'top:-9px;right:-12px;transform:rotate(28deg);');
            } else {
                notch(card, 'top:-10px;left:50%;margin-left:-40px;width:80px;height:24px;' +
                    'background:rgba(255,255,255,0.55);box-shadow:0 1px 3px rgba(0,0,0,0.18);transform:rotate(-2deg);');
            }
        }
    });
}

// Paints the ink straight onto the export bitmap at its real pixel scale, so
// strokes stay vector-sharp instead of being resampled from a half-size canvas.
// `s` maps board units to output pixels; `box` is the crop in board coordinates.
async function paintInkOntoOutput(octx, box, s, layer = 'below') {
    // The ink gets its own transparent canvas first. Painted straight onto the
    // output, an eraser stroke's destination-out would chew through the board
    // background instead of the ink — which is exactly why erased areas turned up
    // as solid black blobs in the exported PNG.
    const w = Math.max(1, Math.round(box.w * s)), h = Math.max(1, Math.round(box.h * s));
    const ink = document.createElement('canvas');
    ink.width = w; ink.height = h;
    const ictx = ink.getContext('2d');

    // The legacy raster layer only ever existed underneath the cards.
    const legacy = layer === 'below' ? getBoard().drawings : null;
    if (legacy) {
        const im = new Image();
        im.src = legacy;
        try {
            await im.decode();
            ictx.drawImage(im, -box.x * s, -box.y * s, BOARD_SIZE * s, BOARD_SIZE * s);
        } catch (e) {}
    }
    const project = p => ({ x: (p.x - box.x) * s, y: (p.y - box.y) * s });
    const wantAbove = layer === 'above';
    let painted = 0;
    for (const stroke of boardStrokes()) {
        if (!stroke.p || stroke.p.length < 2) continue;
        if (!!stroke.a !== wantAbove) continue;
        paintStroke(ictx, stroke, project, s);
        painted++;
    }
    if (painted || legacy) octx.drawImage(ink, 0, 0);
    ink.width = ink.height = 0;
}

// The ink layer is a screen-space overlay, so a clone of the board doesn't carry
// it. Repaint legacy raster + vector strokes into the clone's canvas, in board
// coordinates, before rasterizing.
async function paintInkOntoClone(clone) {
    const cloneCanvas = clone.querySelector('#mb-draw-canvas');
    if (!cloneCanvas) return;
    cloneCanvas.width = DRAW_RES; cloneCanvas.height = DRAW_RES;
    const c2 = cloneCanvas.getContext('2d');
    c2.setTransform(DRAW_SCALE, 0, 0, DRAW_SCALE, 0, 0);
    c2.clearRect(0, 0, BOARD_SIZE, BOARD_SIZE);
    const legacy = getBoard().drawings;
    if (legacy) {
        const im = new Image();
        im.src = legacy;
        try { await im.decode(); c2.drawImage(im, 0, 0, BOARD_SIZE, BOARD_SIZE); } catch (e) {}
    }
    // The character should see the connections too — a thread with "лжёт ему" on
    // it is as much a note as anything written on a card.
    renderTimeline(c2, p => p, 1);
    renderLinks(c2, p => p, 1);
    for (const s of boardStrokes()) {
        if (s.p && s.p.length >= 2) paintStroke(c2, s, p => p, 1);
    }
    clone.querySelector('#mb-grid-layer')?.remove();
}

// ===== PNG EXPORT =====
// Same capture path as the AI snapshot, but at full resolution and cropped to the
// content, so empty board space never ends up in the file.
// The scale at which the biggest stored photo would land on the page at its own
// resolution. Above this there is nothing left to gain; below it, zooming into
// the PNG shows the enlargement.
function nativeScaleFor(onlySelected) {
    const cards = getBoard().cards || [];
    let best = 1;
    for (const el of document.querySelectorAll('#mb-canvas-inner .mb-card')) {
        if (onlySelected && !picked.has(el.dataset.id)) continue;
        const card = cards.find(c => c.id === el.dataset.id);
        const img = el.querySelector('img');
        if (!card || !img) continue;
        const w = el.offsetWidth;
        if (!w) continue;
        // The original is what export swaps in, so measure against that.
        const natural = card.thumb ? (card.origW || 0) : img.naturalWidth;
        const src = natural || img.naturalWidth;
        if (src) best = Math.max(best, src / w);
    }
    return Math.min(12, Math.max(1, best));
}

const EXPORT_QUALITY = {
    screen: { edge: 3000, budget: 24e6 },
    high:   { edge: 6000, budget: 60e6 },
    max:    { edge: Infinity, budget: 120e6 },
};

function exportScale(box, quality, onlySelected) {
    const q = EXPORT_QUALITY[quality] || EXPORT_QUALITY.screen;
    const maxEdge = Math.max(box.w, box.h);
    const native = nativeScaleFor(onlySelected);
    // Never exceed what the images can actually supply…
    let scale = Math.min(native, q.edge === Infinity ? native : Math.max(1, q.edge / maxEdge));
    scale = Math.max(1, scale);
    // …and stay inside the pixel budget and the browser's canvas side limit.
    if (box.w * box.h * scale * scale > q.budget) scale = Math.sqrt(q.budget / (box.w * box.h));
    const SIDE = 16000;
    scale = Math.min(scale, SIDE / maxEdge);
    return Math.max(1, scale);
}

// Asks how sharp, showing what each choice actually produces. A big board simply
// cannot hold every photo at full resolution in one image — the honest thing is
// to show the numbers and let the choice be made.
async function askExportQuality(box, onlySelected) {
    const rows = Object.keys(EXPORT_QUALITY).map(q => {
        const s = exportScale(box, q, onlySelected);
        const w = Math.round(box.w * s), h = Math.round(box.h * s);
        const mp = (w * h / 1e6).toFixed(0);
        return { q, w, h, mp, s };
    });
    const label = { screen: 'Обычное', high: 'Высокое', max: 'Максимум' };
    const note  = {
        screen: 'Быстро и легко, для просмотра на экране.',
        high:   'Заметно чётче при увеличении. Файл крупный.',
        max:    'Столько, сколько отдают сами картинки. На телефоне может не хватить памяти.',
    };
    return new Promise(resolve => {
        $('#mb-dialog').remove();
        const $d = $(`<div id="mb-dialog" class="mb-dialog-back"><div class="mb-dialog">
            <div class="mb-dialog-title">Качество PNG</div>
            ${onlySelected ? `<div class="mb-dialog-text">Выбрано карточек: ${picked.size} — в файл попадут только они.</div>` : ''}
            <div class="mb-export-list"></div>
            <div class="mb-dialog-btns"><button class="mb-dialog-btn cancel">Отмена</button></div>
        </div></div>`).appendTo('body');
        const $list = $d.find('.mb-export-list');
        rows.forEach(r => {
            const same = r.s >= nativeScaleFor(onlySelected) - 0.01;
            $(`<div class="mb-export-opt">
                <b>${label[r.q]}</b>
                <span>${r.w}×${r.h} · ~${r.mp} Мп${same ? ' · предел исходников' : ''}</span>
                <em>${note[r.q]}</em>
            </div>`).on('click', function() {
                // Take the dialog down at once, then hand control back to the
                // browser for a moment before the render seizes the main thread.
                // Without that pause the removal is never painted and, on a phone,
                // the tap looks as though it did nothing while everything freezes.
                // A timer rather than requestAnimationFrame: frames stop arriving
                // when the page isn't painting, and this must not stall.
                $(this).addClass('chosen');
                $d.remove();
                setTimeout(() => resolve(r.q), 40);
            }).appendTo($list);
        });
        const bail = () => { $d.remove(); resolve(null); };
        $d.find('.cancel').on('click', bail);
        $d.on('click', e => { if (e.target === $d[0]) bail(); });
        $d.on('keydown', e => { e.stopPropagation(); if (e.key === 'Escape') bail(); });
    });
}

// Full-screen progress. A phone gives no other sign that anything is happening
// while html2canvas holds the main thread for tens of seconds.
function showBusy(text) {
    let $o = $('#mb-busy');
    if (!$o.length) {
        $o = $(`<div id="mb-busy" class="mb-busy-overlay">
            <i class="fa-solid fa-spinner fa-spin"></i>
            <div class="mb-busy-text"></div>
        </div>`).appendTo('body');
    }
    $o.find('.mb-busy-text').text(text || '');
    $o.css('display', 'flex');
    // A plain timer, for the same reason as above: this must yield even when the
    // page is not currently producing animation frames.
    return new Promise(res => setTimeout(res, 40));
}
function hideBusy() { $('#mb-busy').css('display', 'none'); }
// Updates the line without the yield showBusy does — for progress inside a loop
// that is already yielding on its own.
function showBusyText(text) { $('#mb-busy .mb-busy-text').text(text || ''); }

async function exportPng(quality) {
    const $btn = $('#mb-export-png');
    const old = $btn.html();
    $btn.prop('disabled', true).html('<i class="fa-solid fa-spinner fa-spin"></i> Rendering...');
    let clone = null;
    pauseCull();
    try {
        const h2c = await ensureHtml2Canvas();
        // html2canvas measures whatever is loaded at capture time; an unfetched
        // Cyrillic subset would bake the fallback font into the PNG.
        await preloadCardFonts();
        await nextPaint();
        uncullCards();
        await awaitCardImages();   // culled cards had their pixels dropped; get them back first
        await useFullResImages(true);

        // A selection narrows the export the same way it narrows what the AI
        // sees — and it is the only way to get a few photos out at full quality
        // when the whole board is too big to fit in one image.
        const onlySelected = selectMode && picked.size > 0;
        const box = onlySelected ? (pickedBounds() || contentBounds()) : contentBounds();

        if (!quality) {
            quality = await askExportQuality(box, onlySelected);
            if (!quality) { $btn.prop('disabled', false).html(old); await useFullResImages(false); return; }
        }
        await showBusy('Собираю PNG…');

        const inner = document.getElementById('mb-canvas-inner');
        const inner2 = inner.cloneNode(true);
        inner2.style.cssText = `transform:none;position:absolute;left:${-box.x}px;top:${-box.y}px`;
        if (onlySelected) {
            inner2.querySelectorAll('.mb-card').forEach(el => {
                if (!picked.has(el.dataset.id)) el.remove();
            });
        }
        // Rasterize a box-sized wrapper rather than handing html2canvas the whole
        // 4000px surface with a crop. Given the surface, it renders all of it into
        // one internal bitmap; past a few times magnification that exceeds the
        // browser's canvas limit, and the result comes back upscaled from
        // something smaller — more pixels, *less* detail. Cropping first keeps the
        // bitmap small enough that the requested scale is honoured.
        clone = document.createElement('div');
        clone.style.cssText = `position:absolute;top:-99999px;left:-99999px;overflow:hidden;` +
                              `width:${Math.ceil(box.w)}px;height:${Math.ceil(box.h)}px`;
        clone.appendChild(inner2);
        document.body.appendChild(clone);

        // Deliberately NOT painting the ink into the clone: that canvas is
        // DRAW_RES over a BOARD_SIZE box (half scale), so html2canvas would
        // upscale it and the strokes would come out pixellated. They get drawn
        // straight onto the finished bitmap at full export scale instead.
        clone.querySelector('#mb-draw-canvas')?.remove();
        // Graph paper is a drawing aid, not part of the picture.
        clone.querySelector('#mb-grid-layer')?.remove();

        // Unlike the AI snapshot, a saved PNG gets the board colour behind it —
        // a transparent cut-out of scattered cards is not what you want to share.
        const boardBg = getComputedStyle(document.getElementById('mb-canvas-area')).backgroundColor;
        prepareCloneForExport(clone, boardBg);
        await precropCoverImages(clone);
        // Aim for a long edge around 3000px and allow genuine upscaling for small
        // boards — capping at 2x meant a compact board exported at barely 1000px
        // and looked soft. The pixel budget keeps a huge board from exhausting
        // memory on a phone.
        let scale = exportScale(box, quality, onlySelected);
        // Cards are rasterized over a transparent background so they can be laid
        // on top of the ink; drawings belong *under* the cards, as on the board.
        // A phone can simply run out of memory at these sizes, so step down and
        // retry rather than failing outright.
        let cardsCanvas = null;
        for (let attempt = 0; attempt < 4 && !cardsCanvas; attempt++) {
            try {
                // No x/y/width/height: the wrapper is already the crop.
                cardsCanvas = await h2c(clone, {
                    useCORS: true, allowTaint: true, backgroundColor: null,
                    scale, logging: false, removeContainer: true,
                });
                if (!cardsCanvas.width || !cardsCanvas.height) throw new Error('empty canvas');
            } catch (err) {
                cardsCanvas = null;
                if (attempt === 3 || scale <= 1) throw err;
                scale = Math.max(1, scale / 1.6);
                console.warn(LOG, 'export retry at scale', scale.toFixed(2));
            }
        }
        document.body.removeChild(clone); clone = null;

        const canvas = document.createElement('canvas');
        canvas.width = cardsCanvas.width;
        canvas.height = cardsCanvas.height;
        const octx = canvas.getContext('2d');
        octx.fillStyle = boardBg || '#ffffff';
        octx.fillRect(0, 0, canvas.width, canvas.height);
        const s = canvas.width / box.w;
        // Threads and the timeline sit under the cards on the board, and under
        // them in the file too.
        const project = p => ({ x: (p.x - box.x) * s, y: (p.y - box.y) * s });
        renderTimeline(octx, project, s);
        renderLinks(octx, project, s);
        await paintInkOntoOutput(octx, box, s, 'below');
        octx.drawImage(cardsCanvas, 0, 0);
        // Strokes drawn on top of the cards go on last, as they do on the board.
        await paintInkOntoOutput(octx, box, s, 'above');
        cardsCanvas.width = cardsCanvas.height = 0;

        const blob = await new Promise(r => canvas.toBlob(r, 'image/png'));
        canvas.width = canvas.height = 0;
        const a = document.createElement('a');
        a.href = URL.createObjectURL(blob);
        a.download = `moodboard_${boardKey().replace(/[^\w-]+/g, '_')}.png`;
        a.click();
        setTimeout(() => URL.revokeObjectURL(a.href), 10000);
        if (typeof toastr !== 'undefined') toastr.success('PNG saved');
    } catch (err) {
        console.error(LOG, err);
        if (typeof toastr !== 'undefined') toastr.error('PNG export failed: ' + err.message);
    } finally {
        if (clone?.parentNode) clone.parentNode.removeChild(clone);
        await useFullResImages(false);
        hideBusy();
        $btn.prop('disabled', false).html(old);
        resumeCull();
    }
}

// Board cards render a lightweight preview; swap in the stored originals only for
// the moment we rasterize, then swap back.
async function useFullResImages(on) {
    const cards = getBoard().cards || [];
    const byId = new Map(cards.map(c => [c.id, c]));
    const imgs = [...document.querySelectorAll('#mb-canvas-inner .mb-card img')];
    const waits = [];
    for (const img of imgs) {
        const id = img.closest('.mb-card')?.dataset.id;
        const card = byId.get(id);
        if (!card) continue;
        // Collage tiles keep their own pair of copies, one per cell.
        const cellEl = img.closest('.mb-collage-cell');
        const source = cellEl ? (card.cells || [])[parseInt(cellEl.dataset.i, 10)] : card;
        if (!source || !source.thumb) continue;         // nothing to swap
        const want = on ? source.content : source.thumb;
        if (!want || img.getAttribute('src') === want) continue;
        img.setAttribute('src', want);
        waits.push(img.decode().catch(() => {}));
    }
    await Promise.all(waits);
}

function bindEvents() {
    $('#mb-btn-close').on('click', closeBoard);
    $('#mb-btn-center').on('click', () => centerViewport());
    $('.mb-scope-btn').on('click', function() {
        // Flush any pending drawing against the board we're leaving, not the new one.
        if (drawSaveTimer) { serializeDrawing(); save(); }
        cancelStroke();
        scope = $(this).data('scope');
        $('.mb-scope-btn').removeClass('active'); $(this).addClass('active');
        setSelectMode(false);
        renderTabs();   // each scope keeps its own set of boards
        renderBoard();
    });
    // Only real tools carry data-tool. The AI button used to live in this bar and
    // matched this selector, so pressing it set `tool` to undefined — which left
    // the board with no active tool and no way to pan until you re-picked one.
    $('.mb-tool-btn[data-tool]').on('click', function() {
        // The release after a long press arrives here as a click. Acting on it
        // is what made holding the collage button open its layout menu and then
        // immediately throw up the file picker anyway.
        if (holdJustFired()) return;
        selectTool($(this).data('tool'));
    });
    $('#mb-btn-undo').on('click', undoLast);
    $('#mb-toolbar-toggle').on('click', function() {
        const collapsed = $('#mb-toolbar').toggleClass('collapsed').hasClass('collapsed');
        $(this).toggleClass('collapsed', collapsed)
               .find('i').attr('class', collapsed ? 'fa-solid fa-chevron-down' : 'fa-solid fa-chevron-up');
        localStorage.setItem('mb_toolbar_collapsed', collapsed ? '1' : '0');
        resizeLive(); renderInk(); scheduleCull();
    });

    // ---- collage: tap uses the current layout, long-press picks another
    $('#mb-collage-input').on('change', async function(e) {
        const files = [...(e.target.files || [])];
        $(this).val('');
        if (files.length) await createCollage(files);
    });
    let collageHold = null;
    const openCollagePicker = () => {
        markHold();
        const $p = $('#mb-collage-picker').empty();
        $p.append('<div class="mb-brush-title">Раскладка коллажа</div>');
        const $g = $('<div class="mb-collage-grid"></div>').appendTo($p);
        COLLAGE_LAYOUTS.forEach(L => {
            $(`<div class="mb-brush-opt ${L.id === collageLayout ? 'active' : ''}">
                 <i class="fa-solid fa-${L.icon}"></i><span>${L.label}</span>
                 <em>${L.cells} фото</em></div>`)
                .on('click', e => {
                    e.stopPropagation();
                    collageLayout = L.id;
                    localStorage.setItem('mb_collage_layout', L.id);
                    $('#mb-btn-collage i').attr('class', `fa-solid fa-${L.icon}`);
                    $p.removeClass('open');
                    $('#mb-collage-input').trigger('click');
                }).appendTo($g);
        });
        const r = document.getElementById('mb-btn-collage').getBoundingClientRect();
        $p.addClass('open');
        const w = $p.outerWidth(), h = $p.outerHeight();
        $p.css({ left: Math.max(8, Math.min(r.left, window.innerWidth - w - 8)),
                 top: Math.min(r.bottom + 6, Math.max(8, window.innerHeight - h - 8)) });
    };
    $('#mb-btn-collage').on('pointerdown', () => { collageHold = setTimeout(openCollagePicker, 450); })
                        .on('pointerup pointerleave pointercancel', () => clearTimeout(collageHold))
                        .on('contextmenu', e => { e.preventDefault(); openCollagePicker(); });
    $(document).on('click', e => {
        if (holdJustFired()) return;   // the release of a long press, not a new tap
        if (!$(e.target).closest('#mb-collage-picker, #mb-btn-collage').length) $('#mb-collage-picker').removeClass('open');
    });

    // ---- grid: tap switches it on and off, long-press separates lines from snapping
    let gridHold = null;
    $('#mb-btn-grid').on('pointerdown', () => { gridHold = setTimeout(openGridPicker, 450); })
                     .on('pointerup pointerleave pointercancel', () => clearTimeout(gridHold))
                     .on('contextmenu', e => { e.preventDefault(); openGridPicker(); })
                     .on('click', function() {
                         // The click that ends a long press must do nothing at
                         // all — otherwise letting go of the button closes the
                         // panel the press just opened.
                         if (holdJustFired()) return;
                         // A later tap on the button puts the panel away instead
                         // of flipping the grid behind it.
                         if ($('#mb-grid-picker').hasClass('open')) { $('#mb-grid-picker').removeClass('open'); return; }
                         toggleGrid();
                     });
    $(document).on('click', e => {
        if (holdJustFired()) return;   // the release of a long press, not a new tap
        if (!$(e.target).closest('#mb-grid-picker, #mb-btn-grid').length) $('#mb-grid-picker').removeClass('open');
    });

    // ---- timeline: tap switches the axis on, long-press opens its settings
    let tlHold = null, tlWasHold = false;
    $('#mb-btn-timeline')
        .on('pointerdown', () => { tlWasHold = false; tlHold = setTimeout(() => { tlWasHold = true; openTimelinePanel(); }, 450); })
        .on('pointerup pointerleave pointercancel', () => clearTimeout(tlHold))
        .on('contextmenu', e => { e.preventDefault(); tlWasHold = true; openTimelinePanel(); })
        .on('click', function() {
            if (holdJustFired()) return;
            if (tlWasHold) { tlWasHold = false; return; }
            const tl = boardTimeline();
            tl.on = !tl.on;
            $(this).toggleClass('active', tl.on);
            // Switching it on for the first time puts the axis where you are
            // looking, not in the middle of a board you may be nowhere near.
            if (tl.on && !tl.placed) {
                const c = viewportCenter();
                const area = document.getElementById('mb-canvas-area');
                const halfW = ((area?.clientWidth || 900) / zoom) * 0.45;
                tl.y = Math.round(c.y);
                tl.x0 = Math.round(c.x - halfW); tl.x1 = Math.round(c.x + halfW);
                tl.placed = true;
            }
            save(); renderInk();
            toastr?.info(tl.on ? 'Лента времени включена — удерживайте кнопку для настроек' : 'Лента времени выключена', '', { timeOut: 1400 });
        });

    // ---- trees: tap offers what to build, long-press goes straight to the AI presets
    let treeHold = null, treeWasHold = false;
    $('#mb-btn-tree')
        .on('pointerdown', () => { treeWasHold = false; treeHold = setTimeout(() => { treeWasHold = true; openTreePicker(); }, 450); })
        .on('pointerup pointerleave pointercancel', () => clearTimeout(treeHold))
        .on('contextmenu', e => { e.preventDefault(); treeWasHold = true; openTreePicker(); })
        .on('click', function() {
            if (holdJustFired()) return;
            if (treeWasHold) { treeWasHold = false; return; }
            openTreePicker();
        });
    $(document).on('click', e => {
        if (holdJustFired()) return;   // the release of a long press, not a new tap
        if (!$(e.target).closest('#mb-tree-picker, #mb-btn-tree').length) $('#mb-tree-picker').removeClass('open');
        if (!$(e.target).closest('#mb-avatar-picker, .mb-tree-face').length) $('#mb-avatar-picker').removeClass('open');
    });
    // A thread's menu closes on any tap outside it. Taps on the board are handled
    // in onPointerDown instead — a `click` here would fire on the very gesture
    // that opened the menu and shut it again immediately.
    $(document).on('click', e => {
        if (holdJustFired()) return;   // the release of a long press, not a new tap
        if (!$(e.target).closest('#mb-link-menu, #mb-canvas-area').length) closeLinkMenu();
    });

    // ---- pencil: tap draws, long-press opens brush / size / layer options
    let penHold = null;
    const openBrushPanel = () => {
        markHold();
        const $p = $('#mb-brush-panel').empty();
        $p.append('<div class="mb-brush-title">Кисть</div>');
        const $grid = $('<div class="mb-brush-grid"></div>').appendTo($p);
        BRUSHES.forEach(([k, label, icon]) => {
            $(`<div class="mb-brush-opt ${k === brushKind ? 'active' : ''}">
                 <i class="fa-solid fa-${icon}"></i><span>${label}</span></div>`)
                .on('click', e => {
                    e.stopPropagation();
                    brushKind = k;
                    localStorage.setItem('mb_brush', k);
                    $grid.find('.mb-brush-opt').removeClass('active');
                    $(e.currentTarget).addClass('active');
                    selectTool('draw');
                }).appendTo($grid);
        });

        $p.append('<div class="mb-brush-title">Толщина</div>');
        const $row = $('<div class="mb-brush-size"></div>').appendTo($p);
        const $slider = $(`<input type="range" min="1" max="40" value="${drawSize}">`).appendTo($row);
        const $val = $(`<b>${drawSize}</b>`).appendTo($row);
        const $prev = $('<span class="mb-brush-dot"></span>').appendTo($row);
        const paintDot = () => $prev.css({
            width: Math.min(34, drawSize) + 'px', height: Math.min(34, drawSize) + 'px',
            background: drawColor,
        });
        paintDot();
        $slider.on('input', function() {
            drawSize = parseInt(this.value, 10);
            $val.text(drawSize); paintDot();
            localStorage.setItem('mb_draw_size', drawSize);
        });

        $p.append('<div class="mb-brush-title">Куда рисовать</div>');
        const $layer = $('<div class="mb-brush-layer"></div>').appendTo($p);
        [[false, 'Под карточками', 'layer-group'], [true, 'Поверх карточек', 'pen-fancy']].forEach(([v, label, icon]) => {
            $(`<div class="mb-brush-opt wide ${drawAbove === v ? 'active' : ''}">
                 <i class="fa-solid fa-${icon}"></i><span>${label}</span></div>`)
                .on('click', e => {
                    e.stopPropagation();
                    drawAbove = v;
                    localStorage.setItem('mb_draw_above', v ? '1' : '0');
                    $layer.find('.mb-brush-opt').removeClass('active');
                    $(e.currentTarget).addClass('active');
                }).appendTo($layer);
        });

        const r = document.getElementById('mb-btn-draw').getBoundingClientRect();
        $p.addClass('open');
        const w = $p.outerWidth(), h = $p.outerHeight();
        $p.css({
            left: Math.max(8, Math.min(r.left, window.innerWidth - w - 8)),
            top: Math.min(r.bottom + 6, Math.max(8, window.innerHeight - h - 8)),
        });
    };
    $('#mb-btn-draw').on('pointerdown', () => { penHold = setTimeout(openBrushPanel, 450); })
                     .on('pointerup pointerleave pointercancel', () => clearTimeout(penHold))
                     .on('contextmenu', e => { e.preventDefault(); openBrushPanel(); });
    $(document).on('click', e => {
        if (holdJustFired()) return;   // the release of a long press, not a new tap
        if (!$(e.target).closest('#mb-brush-panel, #mb-btn-draw').length) $('#mb-brush-panel').removeClass('open');
    });

    // ---- shape picker: tap uses the current shape, long-press offers the rest
    let shapeHold = null;
    const openShapePicker = () => {
        markHold();
        const $p = $('#mb-shape-picker').empty();
        const icons = { rect:'square', circle:'circle', ellipse:'egg', triangle:'play',
                        line:'minus', diamond:'diamond', star:'star' };
        SHAPE_KINDS.forEach(k => {
            $(`<div class="mb-shape-opt ${k === shapeKind ? 'active' : ''}" title="${k}"><i class="fa-solid fa-${icons[k]}"></i></div>`)
                .on('click', e => {
                    e.stopPropagation();
                    shapeKind = k;
                    $('#mb-btn-shape i').attr('class', `fa-solid fa-${icons[k]}`);
                    $p.removeClass('open');
                    selectTool('shape');
                    localStorage.setItem('mb_shape_kind', k);
                }).appendTo($p);
        });
        const r = document.getElementById('mb-btn-shape').getBoundingClientRect();
        $p.css({ left: Math.max(8, r.left), top: r.bottom + 6 }).addClass('open');
    };
    $('#mb-btn-shape').on('pointerdown', () => { shapeHold = setTimeout(openShapePicker, 450); })
                      .on('pointerup pointerleave pointercancel', () => { clearTimeout(shapeHold); })
                      .on('contextmenu', e => { e.preventDefault(); openShapePicker(); });
    $(document).on('click', e => {
        if (holdJustFired()) return;   // the release of a long press, not a new tap
        if (!$(e.target).closest('#mb-shape-picker, #mb-btn-shape').length) $('#mb-shape-picker').removeClass('open');
    });

    $('#mb-color-row').on('click', '.mb-color-dot', function() {
        drawColor = $(this).data('color');
        $('.mb-color-dot, .mb-custom-color-btn').removeClass('active');
        $(this).addClass('active');
    });
    $('.mb-custom-color-btn').on('click', function() {
        togglePanel('#mb-custom-color-panel');
        renderSavedColors();
    });
    // Panels sit on top of the board; their pointer events must not reach the pan handler.
    $('.mb-settings-panel, #mb-shape-picker, .mb-brush-panel').on('pointerdown pointermove pointerup', function(e) {
        e.stopPropagation();
    });
    $(document).on('click', '.mb-panel-close', function() {
        $($(this).data('close')).removeClass('open');
        if ($(this).data('close') === '#mb-ai-panel') aiPanelOpen = false;
    });
    function updateCustomColor() {
        const h = $('#mb-hue-slider').val();
        const l = $('#mb-lightness-slider').val();
        $('#mb-lightness-slider').css('background', `linear-gradient(to right, #000, hsl(${h}, 100%, 50%), #fff)`);
        const a = 1 * Math.min(l/100, 1 - l/100);
        const f = n => { const k = (n + h/30)%12; return Math.round(255 * (l/100 - a * Math.max(Math.min(k-3,9-k,1),-1))).toString(16).padStart(2,'0'); };
        const hex = `#${f(0)}${f(8)}${f(4)}`;
        $('#mb-color-preview').css('background', hex);
        $('#mb-hex-input').val(hex);
    }
    $('#mb-hue-slider, #mb-lightness-slider').on('input', updateCustomColor);
    $('#mb-hex-input').on('change', function() { $('#mb-color-preview').css('background', $(this).val()); });
    $('#mb-apply-color').on('click', function() {
        drawColor = $('#mb-hex-input').val();
        $('.mb-color-dot').removeClass('active');
        $('.mb-custom-color-btn').addClass('active').css({background: drawColor, borderColor: '#fff'});
        $('#mb-custom-color-panel').removeClass('open');
    });
    $('#mb-pin-color').on('click', function() {
        const hex = ($('#mb-hex-input').val() || '').trim();
        if (!/^#[0-9a-f]{6}$/i.test(hex)) { if (typeof toastr !== 'undefined') toastr.warning('Enter a colour like #a1b2c3'); return; }
        const saved = savedColors();
        if (saved.includes(hex)) { if (typeof toastr !== 'undefined') toastr.info('Already pinned'); return; }
        saved.push(hex);
        save();
        renderColorRow(); renderSavedColors();
        if (typeof toastr !== 'undefined') toastr.success('Pinned to palette');
    });
    $('#mb-btn-stickers').on('click', () => {
        togglePanel('#mb-stickers');
        if ($('#mb-stickers').hasClass('open')) renderStickers();
    });
    $('#mb-upload-sticker').on('click', () => $('#mb-sticker-file-input').trigger('click'));
    $('#mb-sticker-file-input').on('change', async function(e) {
        const files = e.target.files; if (!files || !files.length) return;
        if (!boards.global.stickers) boards.global.stickers = [];
        let trimmedCount = 0;
        for (let i = 0; i < files.length; i++) {
            const reader = new FileReader();
            const raw = await new Promise(res => {
                reader.onload = ev => res(ev.target.result);
                reader.readAsDataURL(files[i]);
            });
            // Cut the empty space away first, then shrink: trimming afterwards
            // would have thrown away resolution on padding nobody wanted.
            const cut = await trimTransparent(raw);
            if (cut.trimmed) trimmedCount++;
            boards.global.stickers.push(await shrinkSticker(cut.src));
        }
        save(); renderStickers();
        if (trimmedCount) toastr?.success(`Пустые поля обрезаны: ${trimmedCount} из ${files.length}`);
        $(this).val('');
    });
    // Stickers already in the gallery — including everything added before this
    // existed — can be cleaned up in one go.
    $('#mb-trim-stickers').on('click', async () => {
        const list = boards.global.stickers || [];
        if (!list.length) { toastr?.info('Галерея пуста'); return; }
        await showBusy('Обрезаю пустые поля…');
        let n = 0;
        try {
            for (let i = 0; i < list.length; i++) {
                const cut = await trimTransparent(list[i]);
                if (!cut.trimmed) continue;
                list[i] = await shrinkSticker(cut.src);
                n++;
            }
            save(true); renderStickers();
        } finally { hideBusy(); }
        toastr?.[n ? 'success' : 'info'](n ? `Обрезано стикеров: ${n}` : 'Обрезать было нечего');
    });
    // Custom Selects Logic
    $(document).on('click', '.mb-custom-select', function(e) {
        e.stopPropagation();
        $('.mb-custom-select').not(this).removeClass('open').each(function() {
            const m = this.querySelector('.mb-select-options');
            if (m) m.style.cssText = '';
        });
        const opening = !$(this).hasClass('open');
        $(this).toggleClass('open', opening);
        if (opening) { placeSelectMenu(this); trackSelectMenu(this); }
        else untrackSelectMenu();
    });
    $(document).on('click', '.mb-select-options div', function(e) {
        e.stopPropagation();
        const $sel = $(this).closest('.mb-custom-select');
        const val = $(this).data('val');
        $sel.removeClass('open');
        this.parentNode.style.cssText = '';   // undo the fixed placement
        const id = $sel.attr('id');
        if (id === 'mb-theme-dropdown') {
            $sel.find('.mb-select-value').text($(this).text());
            localStorage.setItem('mb_theme', val); applyTheme(val);
        } else if (id === 'mb-stroke-dropdown') {
            drawSize = parseInt(val);
        } else if (id === 'mb-style-dropdown') {
            boards.global.responseStyle = val;
            syncStyleDropdown();
            save();
        } else if (id === 'mb-api-dropdown') {
            boards.global.apiProfile = val;
            syncApiDropdown();
            save();
        }
    });
    const closeAllSelects = () => {
        untrackSelectMenu();
        $('.mb-custom-select').removeClass('open').each(function() {
            const m = this.querySelector('.mb-select-options');
            if (m) m.style.cssText = '';   // drop the fixed placement again
        });
    };
    $(document).on('click', closeAllSelects);
    // A menu pinned in viewport coordinates would otherwise hang in mid-air.
    window.addEventListener('resize', closeAllSelects);
    window.visualViewport?.addEventListener('resize', closeAllSelects);

    // AI Analysis Logic
    if (boards.global?.apiContextSize) setCtxSize(boards.global.apiContextSize, null);

    $('#mb-tg-quote').on('change', function() {
        setUiPref('showQuoteBtn', this.checked);
        if (!this.checked) $('#mb-quote-popup').hide();
    });
    [['mb-tg-charcard', 'sendCharCard'], ['mb-tg-persona', 'sendPersona'], ['mb-tg-lore', 'sendLore'], ['mb-tg-note', 'sendAuthorNote']]
        .forEach(([id, key]) => {
            $('#' + id).on('change', function() { setUiPref(key, this.checked); });
        });
    $('#mb-pin-pos').on('click', '.mb-corner-opt', function() {
        if (!boards.global) boards.global = { cards: [] };
        boards.global.imgBtnPos = $(this).data('pos');
        save();
        applyPinPos();
    });
    $('#mb-tg-image').on('change', function() {
        setUiPref('showImageBtn', this.checked);
        if (this.checked) {
            // The "already handled" flag has to go with the buttons, or nothing
            // would be put back.
            $('#chat img').removeData('mb-injected');
            injectChatImageButtons();
        } else $('.mb-chat-img-pin').remove();
    });

    // Response style: each row shows the name plus what it will actually do.
    const $styleOpts = $('#mb-style-dropdown .mb-select-options').empty();
    RESPONSE_STYLES.forEach(([val, label, icon, , ru]) => {
        $styleOpts.append(`<div data-val="${val}">` +
            `<span class="mb-opt-title"><i class="fa-solid fa-${icon} mb-opt-icon"></i>${escHtml(label)}</span>` +
            `<span class="mb-opt-desc">${escHtml(ru)}</span></div>`);
    });
    syncStyleDropdown();
    $('#mb-custom-prompt').on('input', function() { boards.global.customPrompt = this.value; save(); });
    $('#mb-ctx-slider').on('input', function() {
        boards.global.apiContextSize = setCtxSize(this.value, 'slider');
        save();
    });
    // Committed on change/blur, not on every keystroke: clamping mid-typing turns
    // "1" into "1" and then fights you over the "0" that follows.
    $('#mb-ctx-num').on('change blur', function() {
        boards.global.apiContextSize = setCtxSize(this.value, null);
        save();
    }).on('input', function() {
        const n = parseInt(this.value, 10);
        if (Number.isFinite(n) && n >= 0 && n <= CTX_MAX) {
            boards.global.apiContextSize = setCtxSize(n, 'num');
            save();
        }
    }).on('keydown', e => e.stopPropagation());
    // Style is a per-send decision far more often than a setting, so it is
    // reachable from where you actually send: hold the ✦, or use the chip in the
    // selection bar. Both write the same stored value the settings panel shows.
    const openQuickStyle = (anchor) => {
        markHold();
        const $p = $('#mb-style-picker').empty();

        // Group chats first: who answers is the more consequential choice, and in a
        // solo chat this section simply is not there.
        const gi = groupInfo();
        if (gi.isGroup && gi.members.length) {
            $p.append('<div class="mb-brush-title">Кто отвечает</div>');
            const $sp = $('<div class="mb-speaker-list"></div>').appendTo($p);
            const drawSpeakers = () => {
                $sp.empty();
                const chosen = new Set(pickedSpeakers().map(c => c.avatar));
                gi.members.forEach(c => {
                    $(`<div class="mb-speaker-opt ${chosen.has(c.avatar) ? 'active' : ''}">
                         <i class="fa-solid fa-${chosen.has(c.avatar) ? 'check' : 'user'}"></i>
                         <span>${escHtml(c.name)}</span></div>`)
                        .on('click', e => {
                            e.stopPropagation();
                            toggleSpeaker(c.avatar);
                            drawSpeakers();
                            updateStyleChip();
                        }).appendTo($sp);
                });
                const all = chosen.size === gi.members.length;
                $(`<div class="mb-select-hint" style="margin:2px 0 0">${all
                    ? 'Отвечают все участники группы.'
                    : `Отвечают только выбранные: ${[...gi.members].filter(c => chosen.has(c.avatar)).map(c => escHtml(c.name)).join(', ')}`}</div>`)
                    .appendTo($sp);
            };
            drawSpeakers();
        }

        $p.append('<div class="mb-brush-title">Стиль ответа</div>');
        const cur = boards.global?.responseStyle || 'balanced';
        const $list = $('<div class="mb-style-list"></div>').appendTo($p);
        RESPONSE_STYLES.forEach(([val, label, icon, , ru]) => {
            $(`<div class="mb-style-opt ${val === cur ? 'active' : ''}">
                 <i class="fa-solid fa-${icon}"></i>
                 <span><b>${escHtml(label)}</b><em>${escHtml(ru)}</em></span></div>`)
                .on('click', e => {
                    e.stopPropagation();
                    boards.global.responseStyle = val;
                    syncStyleDropdown();
                    save();
                    $p.removeClass('open');
                    updateStyleChip();
                    if (val === 'custom' && !(boards.global.customPrompt || '').trim()) {
                        toastr?.info('Свой промпт пока пуст — задайте его в настройках');
                    }
                }).appendTo($list);
        });
        // A note that rides along with whatever style is chosen — "обрати
        // внимание на…", "не упоминай Х", anything one-off. It is appended to the
        // prompt as a direct instruction and stays until cleared.
        $p.append('<div class="mb-brush-title">Заметка для ИИ</div>');
        const $note = $(`<textarea class="mb-ai-note" rows="2" placeholder="Например: обрати внимание на кухню"></textarea>`)
            .val(boards.global?.aiNote || '');
        $p.append($note);
        const $clear = $('<button class="mb-note-clear">Очистить заметку</button>')
            .on('click', e => { e.stopPropagation(); $note.val(''); boards.global.aiNote = ''; save(); updateStyleChip(); });
        $p.append($clear);
        $note.on('input', function() { boards.global.aiNote = this.value; save(); updateStyleChip(); });
        $note.on('click keydown', e => e.stopPropagation());

        const r = anchor.getBoundingClientRect();
        $p.addClass('open');
        const vh = visibleHeight();
        $p.css('max-height', (vh - 16) + 'px');
        const w = $p.outerWidth(), h = Math.min($p.outerHeight(), vh - 16);
        $p.css({ left: Math.max(8, Math.min(r.left - w / 2 + r.width / 2, window.innerWidth - w - 8)),
                 top: Math.max(8, Math.min(r.bottom + 8, vh - h - 8)) });
    };
    let analyzeHold = null, analyzeWasHold = false;
    $('#mb-btn-analyze')
        .on('pointerdown', function() {
            const el = this; analyzeWasHold = false;
            analyzeHold = setTimeout(() => { analyzeWasHold = true; openQuickStyle(el); }, 450);
        })
        .on('pointerup pointerleave pointercancel', () => clearTimeout(analyzeHold))
        .on('contextmenu', function(e) { e.preventDefault(); analyzeWasHold = true; openQuickStyle(this); })
        .on('click', function() {
            if (holdJustFired() || analyzeWasHold) { analyzeWasHold = false; return; }   // the hold already acted
            analyzeBoard();
        });
    $('#mb-select-style').on('click', function() { openQuickStyle(this); });
    $(document).on('click', e => {
        if (holdJustFired()) return;   // the release of a long press, not a new tap
        if (!$(e.target).closest('#mb-style-picker, #mb-btn-analyze, #mb-select-style').length) {
            $('#mb-style-picker').removeClass('open');
        }
    });
    $('#mb-select-cancel').on('click', () => setSelectMode(false));
    $('#mb-select-send').on('click', async () => {
        if (!picked.size) return;
        await analyzeBoard();
        setSelectMode(false);
    });
    $('#mb-btn-test-api').on('click', testConnection);
    $('#mb-btn-ai-panel').on('click', () => {
        aiPanelOpen = togglePanel('#mb-ai-panel');
    });

    $('#mb-btn-settings').on('click', () => {
        settingsOpen = togglePanel('#mb-settings');
        if (settingsOpen) refreshProfilesUI();
    });
    $('#mb-clear-board').on('click', async () => {
        if (!await mbConfirm('Очистить доску?',
                'Все карточки, рисунки и отклики этой доски будут удалены. Отменить нельзя.',
                { okLabel: 'Очистить', danger: true })) return;
        clearTimeout(drawSaveTimer); drawSaveTimer = null;
        cancelStroke();
        const b = getBoard();
        // Confirmed or not, "clear the board" is worth one step of undo.
        pushUndo({ type: 'clear', cards: b.cards || [], links: b.links || [],
                   strokes: b.strokes || [], drawings: b.drawings || '' });
        b.cards = []; b.drawings = ''; b.strokes = []; b.links = [];
        save(true); renderBoard(); renderInk();
    });
    $('#mb-export').on('click', async () => {
        await showBusy('Готовлю файл…');
        try {
            // Same reason as the full backup below: the pictures have to travel
            // with the board, not as paths into this installation.
            const one = { [boardKey()]: structuredCloneSafe(getBoard()) };
            await inlineStoredImages(one);
            const blob = new Blob([JSON.stringify(one[boardKey()], null, 2)], { type: 'application/json' });
            const a = document.createElement('a'); a.href = URL.createObjectURL(blob);
            a.download = `moodboard_${boardKey()}.json`; a.click();
            setTimeout(() => URL.revokeObjectURL(a.href), 10000);
        } catch (e) {
            console.error(LOG, e);
            toastr?.error('Не удалось выгрузить доску: ' + e.message);
        } finally { hideBusy(); }
    });
    // Wrapped, not passed directly: jQuery hands the handler the event object,
    // which would arrive as the `quality` argument and skip the picker.
    $('#mb-export-png').on('click', () => exportPng());
    // Everything in one file: boards, stickers, frames, fonts, saved themes.
    // Board data lives only in this browser now, so this is the one way to carry
    // it to another device or back after clearing site data.
    $('#mb-export-all').on('click', async () => {
        await showBusy('Собираю копию…');
        try {
            const rows = await idbGetAll();
            const dump = { _mb: 'moodboard-backup', v: 1, at: new Date().toISOString(), boards: {} };
            for (const [k, v] of rows) dump.boards[k] = v;
            // A backup has to survive the trip to another machine, where none of
            // our image files exist — so the pictures go back inline on the way
            // out. Restored, they arrive as data URLs and the idle migration
            // walks them out to files again on their own.
            await inlineStoredImages(dump.boards);
            const blob = new Blob([JSON.stringify(dump)], { type: 'application/json' });
            const a = document.createElement('a');
            a.href = URL.createObjectURL(blob);
            a.download = `moodboard_backup_${new Date().toISOString().slice(0, 10)}.json`;
            a.click();
            setTimeout(() => URL.revokeObjectURL(a.href), 10000);
            toastr?.success(`Сохранено досок: ${rows.length}`);
        } catch (e) {
            console.error(LOG, e);
            toastr?.error('Не удалось сделать копию: ' + e.message);
        } finally { hideBusy(); }
    });
    $('#mb-edit-theme').on('click', openThemePanel);
    $('#mb-theme-bg-input').on('change', async function(e) {
        const f = e.target.files?.[0];
        $(this).val('');
        if (f) await setThemeBackground(f);
    });
    $('#mb-add-frame').on('click', () => $('#mb-frame-file').trigger('click'));
    $('#mb-reprocess-frames').on('click', reprocessFrames);
    $('#mb-frame-file').on('change', async function(e) {
        const files = [...(e.target.files || [])];
        $(this).val('');
        if (files.length) { await addCustomFrames(files); injectCustomFrameCss(); }
    });
    $('#mb-add-font').on('click', () => addCustomFont($('#mb-font-url').val()));
    $('#mb-font-url').on('keydown', e => {
        if (e.key === 'Enter') { e.preventDefault(); addCustomFont($('#mb-font-url').val()); }
    });
    $('#mb-add-font-file').on('click', () => $('#mb-font-file').trigger('click'));
    $('#mb-font-file').on('change', async function(e) {
        const file = e.target.files?.[0];
        $(this).val('');
        if (file) await addCustomFontFile(file);
    });
    $('#mb-import').on('click', () => {
        const inp = document.createElement('input'); inp.type = 'file'; inp.accept = '.json';
        inp.onchange = e => {
            const r = new FileReader();
            r.onload = async ev => {
                let data;
                try { data = JSON.parse(ev.target.result); }
                catch (err) { toastr?.error('Файл не читается'); return; }

                // A full backup restores every board; a single-board export lands
                // on the board you are looking at, as before.
                if (data && data._mb === 'moodboard-backup' && data.boards) {
                    const keys = Object.keys(data.boards);
                    if (!await mbConfirm('Восстановить из копии?',
                            `В файле досок: ${keys.length}. Совпадающие по имени будут заменены.`,
                            { okLabel: 'Восстановить' })) return;
                    for (const k of keys) {
                        boards[k] = data.boards[k];
                        try { await idbPut(k, structuredCloneSafe(boards[k])); } catch (err) { console.error(LOG, err); }
                    }
                    renderBoard();
                    injectCustomFrameCss(); loadCustomFonts(); renderColorRow();
                    toastr?.success(`Восстановлено досок: ${keys.length}`);
                    return;
                }
                boards[boardKey()] = data;
                save(true); renderBoard();
                toastr?.success('Доска загружена');
            };
            r.readAsText(e.target.files[0]);
        }; inp.click();
    });

    // Canvas interactions
    const areaEl = document.getElementById('mb-canvas-area');
    // Long-press on the board is ours. Without this Android raises its image
    // menu ("save image", "search image"…) on the very same gesture that starts
    // a selection, and both happen at once.
    areaEl.addEventListener('contextmenu', e => {
        if (e.target.closest?.('.mb-settings-panel, [contenteditable="true"]')) return;
        e.preventDefault();
    });
    areaEl.addEventListener('pointerdown', onPointerDown);
    areaEl.addEventListener('pointermove', onPointerMove);
    areaEl.addEventListener('pointerup', onPointerUp);
    areaEl.addEventListener('pointercancel', onPointerUp);
    areaEl.addEventListener('wheel', onWheel, { passive: false });

    // Touch pinch-zoom
    areaEl.addEventListener('touchstart', onTouchStart, { passive: false });
    areaEl.addEventListener('touchmove', onTouchMove, { passive: false });
    areaEl.addEventListener('touchend', onTouchEnd, { passive: false });
    areaEl.addEventListener('touchcancel', onTouchEnd, { passive: false });

    // The board canvas is backed at DRAW_RES but addressed in board coordinates.
    drawCtx = document.getElementById('mb-draw-canvas').getContext('2d');
    drawCtx.setTransform(DRAW_SCALE, 0, 0, DRAW_SCALE, 0, 0);
    liveCanvas = document.getElementById('mb-draw-live');
    liveCtx = liveCanvas.getContext('2d');
    topCanvas = document.getElementById('mb-draw-live-top');
    topCtx = topCanvas.getContext('2d');
    window.addEventListener('resize', () => { renderInk(); scheduleCull(); });

    // Editing a note focuses a contenteditable, which opens the phone keyboard.
    // The browser then scrolls an ancestor to reveal the caret — and because the
    // modal is position:fixed, that scroll offset sticks around after the
    // keyboard closes, leaving the whole UI shifted upward with no way back
    // short of reloading. Force everything back to origin whenever the visible
    // viewport settles.
    // Pin the modal to the area the user can actually see. Without this the
    // shell keeps its full dvh height while the keyboard covers the bottom, so
    // the header scrolls out of reach and the close button becomes untappable.
    syncViewport = () => {
        const vv = window.visualViewport;
        // The visual viewport only shrinks for the on-screen keyboard, and the
        // keyboard can only be up while something editable holds focus. Android
        // does not reliably report the resize when it retracts — and when that
        // event went missing the modal stayed frozen at keyboard height until the
        // page was reloaded. So the measurement is only trusted while something is
        // actually being typed into; otherwise the layout viewport wins and any
        // stuck state heals itself on the next event.
        const typing = isTypingTarget(document.activeElement);
        const h = (vv && typing) ? vv.height : window.innerHeight;
        // Android keeps `position: fixed` anchored to the *layout* viewport, so
        // when the keyboard pushes the visual viewport down the modal's top edge
        // ends up above the screen and the header becomes unreachable. Offsetting
        // by visualViewport.offsetTop re-aligns the two.
        const top = (vv && typing) ? vv.offsetTop : 0;
        const de = document.documentElement;
        // Only write when something actually moved: this runs on every pointerdown
        // as a self-heal, and a no-op style write would dirty layout mid-gesture.
        if (h !== lastVh) { de.style.setProperty('--mb-vh', h + 'px'); lastVh = h; }
        if (top !== lastVtop) { de.style.setProperty('--mb-vtop', top + 'px'); lastVtop = top; }
    };
    syncViewport();
    window.addEventListener('resize', syncViewport);
    window.addEventListener('orientationchange', () => setTimeout(syncViewport, 150));

    const resetModalScroll = () => {
        if (!$('#mb-modal').is(':visible')) return;
        const modal = document.getElementById('mb-modal');
        const shell = document.querySelector('.mb-shell');
        if (shell && shell.scrollTop) shell.scrollTop = 0;
        if (shell && shell.scrollLeft) shell.scrollLeft = 0;
        // Any ancestor the browser scrolled to reveal the caret keeps the whole UI
        // offset after the keyboard is gone, and it is not always the document:
        // Tavern's own wrappers can take the scroll too. Zero every one of them.
        for (let el = modal; el; el = el.parentElement) {
            if (el.scrollTop) el.scrollTop = 0;
            if (el.scrollLeft) el.scrollLeft = 0;
        }
        const de = document.scrollingElement || document.documentElement;
        if (de && (de.scrollTop || de.scrollLeft)) de.scrollTo(0, 0);
    };
    document.addEventListener('focusout', e => {
        if ($(e.target).closest('#mb-modal').length) {
            setTimeout(resetModalScroll, 60);
            // The keyboard slides away over a few hundred ms and its final resize
            // event is the one Android likes to skip. Re-measure on a short timer
            // instead of trusting a single callback.
            pokeViewport();
        }
    });
    document.addEventListener('focusin', e => {
        if ($(e.target).closest('#mb-modal').length) pokeViewport();
    });
    // Last-resort heal: any touch inside the board re-measures. Cheap, because
    // syncViewport writes nothing when the numbers have not changed.
    document.getElementById('mb-modal')
        .addEventListener('pointerdown', () => syncViewport(), true);
    document.addEventListener('scroll', resetModalScroll, { passive: true, capture: true });
    if (window.visualViewport) {
        window.visualViewport.addEventListener('resize', () => {
            syncViewport();
            resetModalScroll();
            renderInk(); scheduleCull();
        });
        window.visualViewport.addEventListener('scroll', () => {
            syncViewport();
            resetModalScroll();
        });
    }

    $('#mb-file-input').on('change', function(e) {
        const file = e.target.files[0]; if (!file) return;
        const reader = new FileReader();
        reader.onload = async ev => {
            if (typeof toastr !== 'undefined') toastr.info('Optimizing image...', '', {timeOut: 1000});
            const img = await makeCardImage(ev.target.result);
            addCard(img.content, 'image', undefined, undefined, img.thumb, img.origW);
        };
        reader.readAsDataURL(file);
        $(this).val('');
    });

    // Text selection popup
    document.addEventListener('mouseup', onTextSelect);
    document.addEventListener('touchend', onTextSelect);
    $('#mb-quote-popup').on('click', onQuoteClick);

    // Mobile chat image click to show +
    $(document).on('click', '#chat img, .mb-img-wrapper', function(e) {
        if (window.innerWidth <= 768) {
            // Only act if it's a valid image with a pin
            const $wrap = $(this).closest('.mes_img_container, .mes_media_wrapper, .mb-img-wrapper, .sd_message_gen_image_container');
            const $btn = $wrap.find('.mb-chat-img-pin');
            if ($btn.length && $btn.css('opacity') < 1) {
                e.preventDefault(); e.stopPropagation();
                $('.mb-chat-img-pin').css('opacity', '0');
                $btn.css('opacity', '1');
                setTimeout(() => $btn.css('opacity', '0'), 4000);
            }
        }
    });

    // Universal Desktop Hover via JS (fixes missing hover on SD extension images)
    $(document).on('mouseenter', '#chat img, .mb-img-wrapper, .mb-chat-img-pin', function() {
        if (window.innerWidth > 768) {
            const $wrap = $(this).closest('.mes_img_container, .mes_media_wrapper, .mb-img-wrapper');
            $wrap.find('.mb-chat-img-pin').css('opacity', '1');
        }
    });
    $(document).on('mouseleave', '#chat img, .mb-img-wrapper, .mb-chat-img-pin', function() {
        if (window.innerWidth > 768) {
            const $wrap = $(this).closest('.mes_img_container, .mes_media_wrapper, .mb-img-wrapper');
            $wrap.find('.mb-chat-img-pin').css('opacity', '0');
        }
    });

    injectChatImageButtons();
    // A polling scan of the whole chat used to run here every 2s; on a phone that
    // shows up as a periodic hitch right in the middle of a drag. React to actual
    // DOM changes instead, debounced, and never while the board is open.
    let injectTimer = null;
    const scheduleInject = () => {
        if (injectTimer) return;
        injectTimer = setTimeout(() => {
            injectTimer = null;
            if ($('#mb-modal').is(':visible')) return;
            injectChatImageButtons();
        }, 400);
    };
    // A streaming reply appends text to the chat continuously, and every one of
    // those mutations used to arm the scan — so the whole chat was walked twice a
    // second for the entire length of a generation, when none of it could
    // possibly have added a picture. Only records that actually brought an <img>
    // are worth reacting to. Text nodes, which is nearly all of them during
    // streaming, are rejected on a nodeType check.
    //
    // Still subtree-wide: an image generator drops its result into a message that
    // already exists, so watching only #chat's own children would miss it.
    const chatObserver = new MutationObserver(records => {
        for (const r of records) {
            for (const n of r.addedNodes) {
                if (n.nodeType !== 1) continue;
                if (n.tagName === 'IMG' || n.querySelector?.('img')) { scheduleInject(); return; }
            }
        }
    });
    const chatEl = document.getElementById('chat');
    if (chatEl) chatObserver.observe(chatEl, { childList: true, subtree: true });
    if (typeof eventSource !== 'undefined') {
        eventSource.on(event_types.CHAT_CHANGED, scheduleInject);
    }
}

// A real icon rather than a "+" character: a text plus is centred on its font's
// baseline, not on the circle, so it always sat a hair high and off to one side.
const PIN_HTML = `<div class="mb-chat-img-pin" title="Прикрепить на MoodBoard"><i class="fa-solid fa-plus"></i></div>`;

function injectChatImageButtons() {
    if (!uiPref('showImageBtn')) { $('.mb-chat-img-pin').remove(); return; }
    $('#chat img').each(function() {
        const $img = $(this);
        // Exclude UI icons, avatars, emojis
        if ($img.closest('.avatar, .mesAvatarWrapper, .swipes-counter, .mes_buttons, .mes_edit_buttons, .mes_img_controls').length) return;
        if ($img.hasClass('emoji') || ($img.attr('src') && $img.attr('src').includes('sys/'))) return;
        // Thumbnails inside a collapsed block render at a couple of dozen pixels.
        // A button pinned to the corner of one of those has nowhere to sit and
        // ends up floating outside it. Deliberately not marked as handled: the
        // block may be expanded later, and then it deserves a button after all.
        // Asked first, and deliberately: getBoundingClientRect() forces layout,
        // and this scan re-runs every time the chat changes. Measuring images
        // that were already handled meant a forced layout per picture in the
        // whole chat, several times a second, all through a streaming reply.
        if ($img.data('mb-injected')) return;
        const box = this.getBoundingClientRect();
        if ((box.width && box.width < 64) || (box.height && box.height < 64)) return;
        $img.data('mb-injected', true);

        const $parent = $img.parent();
        // Re-enabled after being switched off: the wrapper is still there, only
        // the button was taken away.
        if ($parent.hasClass('mb-img-wrapper')) {
            if (!$parent.find('.mb-chat-img-pin').length) {
                $img.after(PIN_HTML);
            }
            return;
        }
        // If it's inside a standard ST media container, just append
        if ($parent.hasClass('mes_img_container') || $parent.hasClass('mes_media_wrapper') || $parent.hasClass('sd_message_gen_image_container')) {
            if ($parent.css('position') === 'static') $parent.css('position', 'relative');
            if (!$parent.find('.mb-chat-img-pin').length) {
                $parent.append(PIN_HTML);
            }
        } else {
            // It's a raw inline image (like from SD extensions) -> Wrap it!
            const $wrap = $('<div class="mb-img-wrapper" style="position:relative; display:inline-block; max-width:100%; margin:0; padding:0;"></div>');
            $img.wrap($wrap);
            $img.after(PIN_HTML);
        }
    });
}

// ===== CHAT IMAGE "+" BUTTONS =====
// Two copies per image: a high-quality original that PNG export and the AI
// snapshot use, and a small preview that the board actually renders. Decoding a
// dozen full-size photos is what makes a phone crawl; decoding a dozen ~520px
// previews is nothing, and no quality is lost where it matters.
// 2400 at q0.92 was the old pair, and it was chosen against no particular need:
// it is far more than a board on a phone can ever show, it made every stored
// picture two to three times heavier than it had to be, and — decoded — a single
// one of them is over 20 MB of live bitmap. 1600 still exceeds what any export
// of a whole board resolves to, and costs a third of the memory.
const IMG_FULL_DIM = 1600, IMG_FULL_Q = 0.86;
const IMG_THUMB_DIM = 520, IMG_THUMB_Q = 0.82;
// Stickers used to be capped at 400px, from when a sticker could only ever be
// small. They can be dragged out to fill a corner of the board now, so they are
// kept at a size that survives it.
const STICKER_DIM = 900;
async function shrinkSticker(src) { return storeImage(await compressImageSrc(src, STICKER_DIM, 0.92)); }
// Width of a stored data URL, used to judge how much detail an export can pull.
function imgWidth(src) {
    return new Promise(res => {
        const i = new Image();
        i.onload = () => res(i.naturalWidth);
        i.onerror = () => res(0);
        i.src = src;
    });
}

async function makeCardImage(src) {
    const full = await compressImageSrc(src, IMG_FULL_DIM, IMG_FULL_Q);
    const small = await compressImageSrc(full, IMG_THUMB_DIM, IMG_THUMB_Q, true);
    // Measured while the bytes are still in hand: asking a stored path how wide
    // it is would mean fetching the whole file back to read one number.
    const origW = await imgWidth(full);
    const [content, thumb] = await storeImages([full, small === full ? null : small]);
    return { content, thumb: thumb || null, origW };
}

async function compressImageSrc(src, maxDim = 1000, quality = 0.8, force = false) {
    if (!src) return src;
    // `force` exists so the thumbnail pass can re-encode an already-webp original.
    if (!force && src.startsWith('data:image/webp')) return src;
    return new Promise((resolve) => {
        const img = new Image();
        img.crossOrigin = 'Anonymous';
        img.onload = () => {
            let w = img.width, h = img.height;
            if (w > maxDim || h > maxDim) {
                const ratio = Math.min(maxDim / w, maxDim / h);
                w *= ratio; h *= ratio;
            } else if (force) {
                resolve(src); return;   // already small enough, no separate thumb needed
            }
            const canvas = document.createElement('canvas');
            canvas.width = w; canvas.height = h;
            const ctx = canvas.getContext('2d');
            ctx.drawImage(img, 0, 0, w, h);
            resolve(canvas.toDataURL('image/webp', quality));
        };
        img.onerror = () => resolve(src);
        img.src = src;
    });
}

$(document).on('click', '.mb-chat-img-pin', async function(e) {
    e.stopPropagation(); e.preventDefault();
    const $img = $(this).parent().find('img').first();
    const src = $img.attr('src');
    if (src) {
        if (typeof toastr !== 'undefined') toastr.info('Optimizing image...', '', {timeOut: 1000});
        const img = await makeCardImage(src);
        addCard(img.content, 'image', undefined, undefined, img.thumb, img.origW);
        if (typeof toastr !== 'undefined') toastr.success('Pinned to MoodBoard!');
    }
});

// ===== PINCH ZOOM (mobile) =====
function getTouchDist(t1, t2) { return Math.hypot(t2.clientX - t1.clientX, t2.clientY - t1.clientY); }
function getTouchMid(t1, t2) { return { x: (t1.clientX + t2.clientX) / 2, y: (t1.clientY + t2.clientY) / 2 }; }

function onTouchStart(e) {
    activeTouches = e.touches.length;
    if (e.touches.length >= 2) {
        e.preventDefault();
        // A second finger means "navigate", not "draw" — throw away whatever the
        // first finger started so it doesn't get committed as a stray line.
        cancelStroke();
        cancelDrag();
        cancelLink();
        tlDrag = null;
        isPinching = true;
        $('#mb-canvas-area').addClass('is-panning');
        isPanning = false;
        pinchDist = getTouchDist(e.touches[0], e.touches[1]) || 1;
        pinchZoomStart = zoom;
        pinchPanStart = { x: panX, y: panY };
        const rect = document.getElementById('mb-canvas-area').getBoundingClientRect();
        const mid = getTouchMid(e.touches[0], e.touches[1]);
        pinchMid = { x: mid.x - rect.left, y: mid.y - rect.top };
    }
}
function onTouchMove(e) {
    if (e.touches.length >= 2) {
        e.preventDefault();
        const newDist = getTouchDist(e.touches[0], e.touches[1]);
        const newZoom = Math.max(0.05, Math.min(5, pinchZoomStart * (newDist / pinchDist)));
        const rect = document.getElementById('mb-canvas-area').getBoundingClientRect();
        const m = getTouchMid(e.touches[0], e.touches[1]);
        const curMid = { x: m.x - rect.left, y: m.y - rect.top };
        // Keep the board point that was under the starting midpoint pinned to the
        // current midpoint — this is what makes two-finger panning work, not just zoom.
        const cx = (pinchMid.x - pinchPanStart.x) / pinchZoomStart;
        const cy = (pinchMid.y - pinchPanStart.y) / pinchZoomStart;
        panX = curMid.x - cx * newZoom;
        panY = curMid.y - cy * newZoom;
        zoom = newZoom;
        if (!panRAF) {
            panRAF = requestAnimationFrame(() => {
                updateTransform(); showZoom(); panRAF = null;
            });
        }
    }
}
function onTouchEnd(e) {
    activeTouches = e.touches.length;
    if (e.touches.length === 0) {
        // Stay "pinching" until every finger is up, so the leftover finger from a
        // pinch can't start a stroke on its way off the screen.
        isPinching = false;
        $('#mb-canvas-area').removeClass('is-panning');
        saveCamera();
    }
}

// ===== TEXT SELECTION =====
function onTextSelect(e) {
    const popup = document.getElementById('mb-quote-popup');
    if (!popup) return;
    if (!uiPref('showQuoteBtn')) { popup.style.display = 'none'; return; }
    if ($(e.target).closest('#mb-modal').length) return;
    const sel = window.getSelection();
    const text = sel?.toString().trim();
    if (text && text.length > 1 && text.length < 2000) {
        const range = sel.getRangeAt(0);
        const rect = range.getBoundingClientRect();
        popup.style.display = 'flex';
        popup.style.left = Math.min(rect.right + 6, window.innerWidth - 40) + 'px';
        popup.style.top = Math.max(rect.top - 4, 4) + 'px';
        popup.dataset.text = text;
    } else {
        setTimeout(() => { popup.style.display = 'none'; }, 200);
    }
}

function onQuoteClick() {
    const popup = document.getElementById('mb-quote-popup');
    const text = popup.dataset.text;
    if (text) {
        addCard(text, 'quote');
        popup.style.display = 'none';
        window.getSelection()?.removeAllRanges();
        if (typeof toastr !== 'undefined') toastr.success('Pinned to MoodBoard!');
    }
}

// ===== MULTI-SELECT =====
// Long-press any card to start picking; from then on a tap toggles. Only the
// picked cards are sent to the character, so a reaction can be about one photo
// rather than the whole board.
let selectMode = false, cardHoldTimer = null;
const picked = new Set();

function setSelectMode(on) {
    selectMode = on;
    if (!on) picked.clear();
    $('#mb-canvas-area').toggleClass('mb-selecting', on);
    refreshSelectionUI();
}
function togglePicked(id) {
    if (picked.has(id)) picked.delete(id); else picked.add(id);
    if (!picked.size) { setSelectMode(false); return; }
    refreshSelectionUI();
}
// Keeps the chip in the selection bar showing the style that will actually be used.
function updateStyleChip() {
    const cur = boards.global?.responseStyle || 'balanced';
    const s = RESPONSE_STYLES.find(x => x[0] === cur) || RESPONSE_STYLES[0];
    const hasNote = !!(boards.global?.aiNote || '').trim();
    $('#mb-style-chip').text(s[1] + (hasNote ? ' + заметка' : ''));
    $('#mb-select-style i').attr('class', `fa-solid fa-${s[2]}`);
    // A live note changes every reply, so make it visible on the send button too.
    $('#mb-btn-analyze').toggleClass('has-note', hasNote)
        .attr('title', hasNote ? 'Отправить доску ИИ (есть заметка)' : 'Отправить доску ИИ');
}

function refreshSelectionUI() {
    updateStyleChip();
    $('#mb-canvas-inner .mb-card').each(function() {
        $(this).toggleClass('mb-picked', selectMode && picked.has(this.dataset.id));
    });
    const $bar = $('#mb-select-bar');
    $bar.toggleClass('open', selectMode);
    $bar.find('.mb-select-count').text(picked.size);
}
// Bounding box of the picked cards, in board coordinates.
function pickedBounds() {
    let x0 = Infinity, y0 = Infinity, x1 = -Infinity, y1 = -Infinity;
    $('#mb-canvas-inner .mb-card').each(function() {
        if (!picked.has(this.dataset.id)) return;
        x0 = Math.min(x0, this.offsetLeft); y0 = Math.min(y0, this.offsetTop);
        x1 = Math.max(x1, this.offsetLeft + this.offsetWidth);
        y1 = Math.max(y1, this.offsetTop + this.offsetHeight);
    });
    if (!isFinite(x0)) return null;
    const pad = 30;
    return { x: Math.max(0, x0 - pad), y: Math.max(0, y0 - pad),
             w: (x1 - x0) + pad * 2, h: (y1 - y0) + pad * 2 };
}

// ===== LAYERS =====
// Every card keeps its own stacking order, so the first thing pinned stays at the
// bottom and each new one lands on top. Relying on DOM order alone did not
// survive a drag, which used to reset the card to a fixed z-index.
function maxCardZ() {
    const cards = getBoard().cards || [];
    return cards.reduce((m, c) => Math.max(m, c.z || 0), 0);
}
// Older boards predate this field; hand out an order matching how they render today.
function ensureCardZ(board) {
    const cards = board.cards || [];
    if (cards.every(c => typeof c.z === 'number')) return;
    cards.forEach((c, i) => { if (typeof c.z !== 'number') c.z = i + 1; });
}
function restack(card, where) {
    const cards = getBoard().cards || [];
    ensureCardZ(getBoard());
    const sorted = [...cards].sort((a, b) => (a.z || 0) - (b.z || 0));
    const i = sorted.indexOf(card);
    if (i < 0) return;
    sorted.splice(i, 1);
    if (where === 'front') sorted.push(card);
    else if (where === 'back') sorted.unshift(card);
    else if (where === 'up') sorted.splice(Math.min(sorted.length, i + 1), 0, card);
    else sorted.splice(Math.max(0, i - 1), 0, card);
    sorted.forEach((c, n) => { c.z = n + 1; });
    // Repaint the affected cards without rebuilding the whole board.
    sorted.forEach(c => {
        const el = document.querySelector(`.mb-card[data-id="${c.id}"]`);
        if (el) el.style.zIndex = c.z;
    });
    save();
}

function addCard(content, type, x, y, thumb, origW) {
    const board = getBoard();
    const vc = viewportCenter();
    const spread = 60;
    const card = {
        id: genId(), type, content, z: maxCardZ() + 1,
        x: x ?? (vc.x - 100 + (Math.random() - 0.5) * spread),
        y: y ?? (vc.y - 60 + (Math.random() - 0.5) * spread),
        w: type === 'image' ? 220 : 200,
        color: cardColors[Math.floor(Math.random() * cardColors.length)],
        created: Date.now()
    };
    if (thumb) card.thumb = thumb;
    // What the stored original measures. PNG export uses it to work out how far
    // it can usefully scale, and reading it here saves fetching the file back.
    if (origW) card.origW = origW;
    board.cards.push(card);
    save();
    if ($('#mb-modal').is(':visible')) renderCard(card, true);
    if (tool === 'text' || tool === 'image') {
        tool = 'select';
        $('.mb-tool-btn[data-tool]').removeClass('active').filter('[data-tool="select"]').addClass('active');
        $('#mb-draw-canvas').removeClass('active');
        $('#mb-canvas-area').removeClass('drawing');
    }
}

function renderBoard() {
    renderTabs();
    const board = getBoard();
    ensureCardZ(board);
    pruneLinks();
    linkGeomDirty = true;
    applyGridLayer();
    $('#mb-btn-timeline').toggleClass('active', !!board.timeline?.on);
    $('#mb-canvas-inner .mb-card').remove();
    // Build off-document so a large board costs one insertion, not one per card.
    const frag = document.createDocumentFragment();
    board.cards.forEach(c => renderCard(c, false, frag));
    document.getElementById('mb-canvas-inner').appendChild(frag);
    // Boards drawn before the vector ink layer kept a raster bitmap; keep painting
    // it underneath so nothing anyone already drew disappears.
    if (drawCtx) {
        drawCtx.clearRect(0, 0, BOARD_SIZE, BOARD_SIZE);
        if (board.drawings) {
            const img = new Image();
            img.onload = () => { drawCtx.drawImage(img, 0, 0, BOARD_SIZE, BOARD_SIZE); };
            img.src = board.drawings;
        }
    }

    renderAiHistory();
    updateTransform();
    groomBoard();
}

// Housekeeping for boards that predate the current storage: moving inlined
// pictures out to files, and making the previews that keep the board light.
//
// Neither is allowed to just happen. Both decode, re-encode and upload one photo
// at a time, and on an old board that is minutes of work — measured here at
// around half a minute of a *desktop* being unable to paint, for twelve pictures.
// On a phone, on someone's own connection, that is a hot device and a browser
// that may well give up. So past a handful of items this asks first, and does
// nothing until told.
const GROOM_QUIET_MAX = 4;
let groomRunning = false;
const idleTick = () => new Promise(res =>
    (window.requestIdleCallback || (cb => setTimeout(cb, 120)))(res, { timeout: 800 }));

// How much there is to do, in items, without touching any of it.
function pendingGroomWork() {
    const board = getBoard();
    const thumbs = (board.cards || []).filter(c =>
        (c.type === 'image' || c.type === 'sticker') && c.content && !c.thumb && !c.noThumb).length;
    const inline = countInlineImages();
    return { inline, thumbs, total: inline + thumbs };
}

async function groomBoard() {
    if (groomRunning) return;
    groomRunning = true;
    const started = getBoard();
    try {
        const work = pendingGroomWork();
        if (work.total > GROOM_QUIET_MAX) offerGrooming(work);
        else if (work.total) {
            await migrateInlineImages();
            await backfillThumbs();
        }
    } catch (e) {
        console.warn(LOG, 'board grooming stopped early', e);
    } finally {
        groomRunning = false;
    }
    // Both passes bail out the moment the board underneath them changes, and the
    // render that caused the switch has already been and gone — so without this
    // the board just switched to would never get its turn.
    if (getBoard() !== started && $('#mb-modal').is(':visible')) groomBoard();
}

// Everything on a board that holds pixels. Each entry is an object and the key
// on it that carries the picture, so one loop can rewrite all of them.
function* imageSlots(board) {
    for (const c of board.cards || []) {
        yield [c, 'content']; yield [c, 'thumb'];
        for (const cell of c.cells || []) { if (cell) { yield [cell, 'content']; yield [cell, 'thumb']; } }
    }
    yield [board, 'drawings'];                       // the legacy raster layer
    for (const f of board.frames || []) yield [f, 'src'];
    const list = board.stickers || [];
    for (let i = 0; i < list.length; i++) yield [list, String(i)];
    // Board backdrops: the one in use, and every one parked in a saved theme.
    if (board.customTheme?.bg) yield [board.customTheme.bg, 'src'];
    for (const th of board.savedThemes || []) { if (th?.bg) yield [th.bg, 'src']; }
}

// True while pictures are being moved out. The boards file is at its heaviest
// during exactly this window — most photos still inlined — so re-uploading it
// between images would mean sending several megabytes over and over alongside
// the image uploads themselves. runUpload waits this out; the local cache is
// still written as we go, so nothing is at risk.
let migrating = false;
// Attempted once per session. Without this a run that cannot finish — a server
// that refuses the files, a connection that keeps dropping — is retried in full
// on every single render, which is worse than never trying at all.
let migrateTried = false;

function countInlineImages() {
    let n = 0;
    for (const board of [getBoard(), boards.global || {}]) {
        for (const [obj, key] of imageSlots(board)) if (isDataUrl(obj?.[key])) n++;
    }
    return n;
}

// Boards written before the image store existed carry their photos inline.
// Interrupted at any point this is still correct: whatever moved is a path,
// whatever did not is still a data URL, and both render.
async function migrateInlineImages(force) {
    if (migrating) return;
    if (migrateTried && !force) return;
    const board = getBoard();
    const slots = [...imageSlots(board), ...imageSlots(boards.global || {})]
        .filter(([obj, key]) => isDataUrl(obj?.[key]));
    if (!slots.length) return;
    if (!await probeImageStore()) return;            // nothing would land anyway

    migrateTried = true;
    migrating = true;
    const total = slots.length;
    let moved = 0;
    console.info(LOG, `moving ${total} inlined image(s) out of the boards file`);
    try {
        for (const [obj, key] of slots) {
            if (!$('#mb-modal').is(':visible')) break;   // board closed — stop working
            if (imgStore !== 'ok') break;                // the store gave up on us
            await idleTick();
            if (getBoard() !== board) break;             // user switched scope
            const src = obj[key];
            if (!isDataUrl(src)) continue;               // something else got to it first
            const path = await storeImage(src);
            if (path === src) continue;                  // upload failed; it stays inline
            obj[key] = path;
            moved++;
            if (force) showBusyText(`Переношу картинки… ${moved} из ${total}`);
            // Cheap enough to just re-point every <img> that was showing it.
            for (const img of document.querySelectorAll('#mb-canvas-inner img')) {
                if (img.getAttribute('src') === src) img.setAttribute('src', path);
                if (img.dataset.mbSrc === src) img.dataset.mbSrc = path;
            }
            // A checkpoint every so often, to the local cache only — see the note
            // on `migrating` above. Not every picture: the cache write clones the
            // whole board, which during this window still holds most of them.
            // Losing a checkpoint costs nothing but a few orphaned files and a
            // second pass; the pictures themselves are already safely uploaded.
            if (moved % 10 === 0) {
                for (const k of new Set([boardKey(), 'global'])) {
                    try { await idbPut(k, boards[k]); } catch (e) {}
                }
            }
        }
    } finally {
        migrating = false;
    }
    // One upload, at the end, of a file that is now a fraction of what it was.
    if (moved) { save(true); console.info(LOG, `moved ${moved} image(s) out`); }
    return moved;
}

// Asked rather than assumed. The gain is real but it is not urgent, and it is
// paid for one photo at a time over whatever connection the user happens to be
// on — so starting it is theirs to decide, and doing it from a desktop once is
// enough for every device afterwards.
let groomOffered = false;
function offerGrooming(work) {
    if (groomOffered || typeof toastr === 'undefined') return;
    groomOffered = true;
    const what = work.inline && work.thumbs
        ? `${work.inline} картинок внутри файла досок и ${work.thumbs} без превью`
        : work.inline ? `${work.inline} картинок лежат внутри файла досок`
                      : `${work.thumbs} картинок без превью`;
    toastr.info(
        `${what}. Из-за этого доска тяжёлая и телефон греется. Нажмите, чтобы привести в порядок — ` +
        `это разовая операция, лучше запустить с компьютера. Займёт около минуты.`,
        'MoodBoard', { timeOut: 0, extendedTimeOut: 0, closeButton: true, tapToDismiss: false,
            onclick: () => runGroomingNow() });
}

let groomingNow = false;
async function runGroomingNow() {
    if (groomingNow) return;
    groomingNow = true;
    await showBusy('Привожу доску в порядок…');
    try {
        const moved = await migrateInlineImages(true) || 0;
        const made = await backfillThumbs(true) || 0;
        toastr?.success(moved || made
            ? `Готово: перенесено ${moved}, превью сделано ${made}`
            : 'Всё уже в порядке');
    } catch (e) {
        console.error(LOG, 'grooming failed', e);
        toastr?.error('Не получилось: ' + (e.message || e));
    } finally { groomingNow = false; hideBusy(); }
}

// Boards made before previews existed store only full-size images, so they'd stay
// just as heavy as before. Generate the missing previews and swap them in as they
// land.
async function backfillThumbs(force) {
    const board = getBoard();
    const pending = (board.cards || []).filter(c =>
        (c.type === 'image' || c.type === 'sticker') && c.content && !c.thumb && !c.noThumb);
    if (!pending.length) return 0;
    // Each item here decodes a full-size photo and encodes a new one. Held to the
    // same rule as the migration: a few can happen quietly, a boardful is asked
    // about first — see the note on GROOM_QUIET_MAX.
    if (!force && pending.length > GROOM_QUIET_MAX) return 0;
    const total = pending.length;
    let made = 0;
    // The save at the end rewrites the whole file, so hold the upload off until
    // then rather than letting one land per preview.
    migrating = true;
    try {
    for (const card of pending) {
        if (!$('#mb-modal').is(':visible')) break;   // board closed — stop working
        await idleTick();
        if (getBoard() !== board) break;             // user switched scope
        const shrunk = await compressImageSrc(card.content, IMG_THUMB_DIM, IMG_THUMB_Q, true);
        // Already small enough to be its own preview: compressImageSrc hands the
        // source straight back.
        if (!shrunk || shrunk === card.content) { card.noThumb = true; continue; }
        card.thumb = await storeImage(shrunk);
        made++;
        if (force) showBusyText(`Делаю превью… ${made} из ${total}`);
        const img = document.querySelector(`.mb-card[data-id="${card.id}"] .mb-card-content-wrap > img`);
        if (img) {
            const want = bestSrcFor(card);
            if (img.dataset.mbSrc) img.dataset.mbSrc = want;
            else img.setAttribute('src', want);
        }
    }
    } finally { migrating = false; }
    // `noThumb` is a decision worth keeping even when no preview came of it: it
    // is what stops the same picture being re-examined on every render.
    save(true);
    return made;
}

function renderTabs() {
    const $t = $('#mb-tabs');
    if (!$t.length) return;
    const meta = tabsMeta();
    $t.empty();
    meta.list.forEach(tab => {
        const active = tab.id === meta.active;
        const $tab = $(`<div class="mb-tab ${active ? 'active' : ''}" data-id="${tab.id}">
            <span class="mb-tab-name">${escHtml(tab.name)}</span>
            ${active ? '<i class="fa-solid fa-pen mb-tab-edit" title="Переименовать"></i>' : ''}
            ${active && meta.list.length > 1 ? '<i class="fa-solid fa-xmark mb-tab-del" title="Удалить доску"></i>' : ''}
        </div>`);
        $tab.on('click', function(e) {
            if ($(e.target).closest('.mb-tab-edit, .mb-tab-del').length) return;
            if (tab.id === meta.active) return;
            switchTab(tab.id);
        });
        $tab.find('.mb-tab-edit').on('click', async e => {
            e.stopPropagation();
            const name = await mbPrompt('Название доски', tab.name, 'Например: Пляж');
            if (!name) return;
            tab.name = name.slice(0, 40);
            save(true); renderTabs();
        });
        $tab.find('.mb-tab-del').on('click', async e => {
            e.stopPropagation();
            if (!await mbConfirm('Удалить доску?',
                    `«${tab.name}» и всё, что на ней, будет удалено. Отменить нельзя.`,
                    { okLabel: 'Удалить', danger: true })) return;
            const key = tabBoardKey(tab.id);
            delete boards[key];
            idbDelete(key).catch(() => {});
            meta.list = meta.list.filter(x => x.id !== tab.id);
            meta.active = meta.list[0].id;
            save(true); renderTabs(); renderBoard();
        });
        $t.append($tab);
    });
    $(`<div class="mb-tab mb-tab-add" title="Новая доска"><i class="fa-solid fa-plus"></i></div>`)
        .on('click', async () => {
            const name = await mbPrompt('Новая доска', '', `Доска ${meta.list.length + 1}`);
            if (name === null) return;
            const id = genId();
            meta.list.push({ id, name: (name || `Доска ${meta.list.length + 1}`).slice(0, 40) });
            switchTab(id);
        }).appendTo($t);
}

function switchTab(id) {
    // Commit whatever is pending against the board we're leaving.
    if (drawSaveTimer) { serializeDrawing(); }
    save(true);
    cancelStroke();
    setSelectMode(false);
    tabsMeta().active = id;
    save(true);
    renderTabs();
    renderBoard();
    applyCamera();
}

function renderAiHistory() {
    const board = getBoard();
    renderFolderBar();
    const filter = board.aiFolderFilter || '';
    const all = board.aiHistory || [];
    const shown = filter ? all.filter(m => m.folder === filter) : all;
    $('#mb-ai-history').html(shown.length ? '' : (all.length
        ? `<div class="empty-msg">В этой папке пусто.</div>`
        : `<div class="empty-msg">Откликов пока нет.<br>Отправьте доску персонажу кнопкой ✦.</div>`));
    // appendAiMessage prepends, so walking oldest→newest leaves newest on top.
    shown.forEach(m => appendAiMessage(m));
}

// ===== THEME EDITOR =====
function openThemePanel() {
    const t = customTheme();
    const $b = $('#mb-theme-body').empty();

    $b.append('<span class="mb-settings-label" style="margin-top:4px">Цвета</span>');
    const $list = $('<div class="mb-theme-list"></div>').appendTo($b);
    THEME_FIELDS.forEach(([key, label, def]) => {
        const cur = t.vars[key] || def;
        const $row = $(`<div class="mb-theme-row">
            <span class="mb-theme-swatch" style="background:${cur}"></span>
            <span class="mb-theme-name">${label}</span>
            <code>${cur}</code>
        </div>`);
        $row.on('click', async () => {
            const picked = await mbColorPicker(label, t.vars[key] || def);
            if (!picked) return;
            t.vars[key] = picked;
            $row.find('.mb-theme-swatch').css('background', picked);
            $row.find('code').text(picked);
            applyCustomTheme();
            save();
        });
        $list.append($row);
    });

    $b.append('<span class="mb-settings-label">Фон доски</span>');
    $b.append(`<div class="mb-select-hint">Лучше всего — бесшовная текстура 256–512&nbsp;px, она замостится без швов и почти ничего не весит. Обычная картинка тоже подойдёт: включите «Растянуть». Я уменьшу её до 1600&nbsp;px и пережму, а рисовать её буду по размеру экрана, а не доски — на скорость при зуме это не влияет.</div>`);
    const $bgRow = $('<div class="mb-theme-bg"></div>').appendTo($b);
    if (t.bg) {
        $bgRow.append(`<span class="mb-theme-bg-prev" style="background-image:url(${t.bg.src})"></span>`);
        const $mode = $(`<div class="mb-size-row mb-align-row" style="flex:1"></div>`).appendTo($bgRow);
        [['tile', 'Мозаикой'], ['cover', 'Растянуть']].forEach(([m, lbl]) => {
            $(`<div class="mb-size-opt ${(t.bg.mode || 'tile') === m ? 'active' : ''}">${lbl}</div>`)
                .on('click', () => { t.bg.mode = m; applyCustomTheme(); save(true); openThemePanel(); })
                .appendTo($mode);
        });
    }
    $('<button class="mb-settings-btn secondary"><i class="fa-solid fa-image"></i> Загрузить фон</button>')
        .on('click', () => $('#mb-theme-bg-input').trigger('click')).appendTo($b);
    if (t.bg) {
        $('<button class="mb-settings-btn secondary"><i class="fa-solid fa-xmark"></i> Убрать фон</button>')
            .on('click', () => { t.bg = null; applyCustomTheme(); save(true); openThemePanel(); }).appendTo($b);
    }

    $b.append('<span class="mb-settings-label" style="margin-top:18px">Сохранённые темы</span>');
    const $saved = $('<div class="mb-custom-list"></div>').appendTo($b);
    const list = savedThemes();
    if (!list.length) $saved.append('<div class="mb-empty-hint">Пока ничего не сохранено.</div>');
    list.forEach(th => {
        const $row = $(`<div class="mb-custom-row">
            <span class="mb-custom-prev" style="background:${th.vars['--mb-board-bg'] || '#666'};border:2px solid ${th.vars['--mb-accent'] || '#999'}"></span>
            <span class="mb-custom-name">${escHtml(th.name)}</span>
            <i class="fa-solid fa-arrow-rotate-left mb-theme-load" title="Применить"></i>
            <i class="fa-solid fa-trash mb-custom-del" title="Удалить"></i>
        </div>`);
        $row.find('.mb-theme-load').on('click', () => {
            boards.global.customTheme = JSON.parse(JSON.stringify({ vars: th.vars, bg: th.bg || null }));
            applyCustomTheme(); save(true); openThemePanel();
            toastr?.success(`Тема «${th.name}» применена`);
        });
        $row.find('.mb-custom-del').on('click', async () => {
            if (!await mbConfirm('Удалить тему?', th.name, { okLabel: 'Удалить', danger: true })) return;
            boards.global.savedThemes = savedThemes().filter(x => x.id !== th.id);
            save(true); openThemePanel();
        });
        $saved.append($row);
    });
    $('<button class="mb-settings-btn"><i class="fa-solid fa-floppy-disk"></i> Сохранить как…</button>')
        .on('click', async () => {
            const name = await mbPrompt('Название темы', '', 'Например: Ночной сад');
            if (!name) return;
            savedThemes().push({ id: genId(), name,
                vars: JSON.parse(JSON.stringify(t.vars)),
                bg: t.bg ? JSON.parse(JSON.stringify(t.bg)) : null });
            save(true); openThemePanel();
            toastr?.success('Тема сохранена');
        }).appendTo($b);
    $('<button class="mb-settings-btn secondary"><i class="fa-solid fa-rotate"></i> Сбросить цвета</button>')
        .on('click', () => { t.vars = {}; applyCustomTheme(); save(true); openThemePanel(); }).appendTo($b);

    togglePanel('#mb-theme-panel', true);
}

// The backdrop is capped and re-encoded so a 12MP holiday photo cannot quietly
// become part of every repaint.
async function setThemeBackground(file) {
    const raw = await new Promise((res, rej) => {
        const r = new FileReader();
        r.onload = e => res(e.target.result);
        r.onerror = rej;
        r.readAsDataURL(file);
    });
    const src = await storeImage(await compressImageSrc(raw, 1600, 0.85, true));
    const t = customTheme();
    t.bg = { src, mode: t.bg?.mode || 'tile' };
    applyCustomTheme();
    save(true);
    openThemePanel();
    toastr?.success('Фон установлен');
}

// ===== COLLAGES =====
// Each layout is a CSS grid plus an aspect ratio. `booth` layouts get the white
// photo-booth surround with a caption strip at the bottom.
const COLLAGE_LAYOUTS = [
    { id: 'booth4', label: 'Фотобудка ×4', icon: 'grip-vertical', cells: 4, booth: true,
      cols: '1fr', rows: 'repeat(4, 1fr)', ratio: 0.31, w: 190 },
    { id: 'booth3', label: 'Фотобудка ×3', icon: 'grip-vertical', cells: 3, booth: true,
      cols: '1fr', rows: 'repeat(3, 1fr)', ratio: 0.40, w: 190 },
    { id: 'booth2x4', label: 'Двойная лента', icon: 'table-cells', cells: 8, booth: true,
      cols: 'repeat(2, 1fr)', rows: 'repeat(4, 1fr)', ratio: 0.62, w: 250 },
    { id: 'boothWide', label: 'Будка поперёк', icon: 'grip-horizontal', cells: 4, booth: true,
      cols: 'repeat(4, 1fr)', rows: '1fr', ratio: 3.1, w: 340 },
    { id: 'grid2x2', label: 'Сетка 2×2', icon: 'table-cells-large', cells: 4,
      cols: 'repeat(2, 1fr)', rows: 'repeat(2, 1fr)', ratio: 1, w: 260 },
    { id: 'grid3x3', label: 'Сетка 3×3', icon: 'table-cells', cells: 9,
      cols: 'repeat(3, 1fr)', rows: 'repeat(3, 1fr)', ratio: 1, w: 280 },
    { id: 'duo', label: 'Пара', icon: 'grip-lines-vertical', cells: 2,
      cols: 'repeat(2, 1fr)', rows: '1fr', ratio: 1.6, w: 280 },
    { id: 'hero', label: 'Одна + две', icon: 'table-columns', cells: 3,
      cols: '2fr 1fr', rows: 'repeat(2, 1fr)', ratio: 1.25, w: 280,
      areas: ['grid-area:1/1/3/2', '', ''] },
    { id: 'film', label: 'Плёнка', icon: 'film', cells: 4, strip: true,
      cols: 'repeat(4, 1fr)', rows: '1fr', ratio: 3.2, w: 340 },
];
let collageLayout = 'booth4';

function layoutById(id) { return COLLAGE_LAYOUTS.find(l => l.id === id) || COLLAGE_LAYOUTS[0]; }

async function createCollage(files) {
    const layout = layoutById(collageLayout);
    const list = [...files].slice(0, layout.cells);
    if (!list.length) return;
    toastr?.info('Готовлю коллаж…', '', { timeOut: 1200 });

    const cells = [];
    for (const f of list) {
        try {
            const raw = await new Promise((res, rej) => {
                const r = new FileReader();
                r.onload = e => res(e.target.result);
                r.onerror = rej;
                r.readAsDataURL(f);
            });
            // Same two-copy treatment as ordinary photos: a light preview for the
            // board, the original kept for PNG export.
            const img = await makeCardImage(raw);
            cells.push({ content: img.content, thumb: img.thumb || null });
        } catch (e) {
            console.error(LOG, 'collage cell failed', e);
        }
    }
    while (cells.length < layout.cells) cells.push(null);

    const board = getBoard();
    const vc = viewportCenter();
    const card = {
        id: genId(), type: 'collage', layout: layout.id, cells,
        x: vc.x - layout.w / 2, y: vc.y - (layout.w / layout.ratio) / 2,
        w: layout.w, z: maxCardZ() + 1, created: Date.now(),
    };
    board.cards.push(card);
    save(true);
    if ($('#mb-modal').is(':visible')) renderCard(card, true);
    selectTool('select');
}

function collageHtml(card) {
    const L = layoutById(card.layout);
    const cells = (card.cells || []).slice(0, L.cells);
    while (cells.length < L.cells) cells.push(null);
    const inner = cells.map((c, i) => {
        const area = L.areas?.[i] ? L.areas[i] : '';
        const src = c ? (c.thumb || c.content) : '';
        const body = c
            ? `<img src="${src}" draggable="false" decoding="async">`
            : `<span class="mb-cell-empty"><i class="fa-solid fa-plus"></i></span>`;
        return `<div class="mb-collage-cell" data-i="${i}" style="${area}">${body}</div>`;
    }).join('');
    return `<div class="mb-collage ${L.booth ? 'is-booth' : ''} ${L.strip ? 'is-strip' : ''}"
                 style="grid-template-columns:${L.cols};grid-template-rows:${L.rows};aspect-ratio:${L.ratio}">
                ${inner}
            </div>${L.booth ? `<div class="mb-booth-caption">${escHtml(card.caption || '')}</div>` : ''}`;
}

// Swaps one tile's picture without disturbing the rest of the collage.
function replaceCollageCell(card, index, $card) {
    const inp = document.createElement('input');
    inp.type = 'file'; inp.accept = 'image/*';
    inp.onchange = async e => {
        const f = e.target.files?.[0];
        if (!f) return;
        const raw = await new Promise(res => {
            const r = new FileReader();
            r.onload = ev => res(ev.target.result);
            r.readAsDataURL(f);
        });
        const img = await makeCardImage(raw);
        if (!Array.isArray(card.cells)) card.cells = [];
        card.cells[index] = { content: img.content, thumb: img.thumb || null };
        save(true);
        const $cell = $card.find(`.mb-collage-cell[data-i="${index}"]`);
        $cell.html(`<img src="${img.thumb || img.content}" draggable="false" decoding="async">`);
    };
    inp.click();
}

// ===== USER-SUPPLIED FRAMES =====
// Applied through border-image, so one PNG stretches to any card size while its
// corners stay undistorted. `slice` is the share of the image treated as corner
// artwork; 33% suits most decorative frames.
function customFrames() {
    if (!boards.global) boards.global = { cards: [] };
    if (!Array.isArray(boards.global.frames)) boards.global.frames = [];
    return boards.global.frames;
}

async function addCustomFrames(files) {
    const frames = customFrames();
    let saved = 0;
    for (const file of files) {
        try {
            const raw = await new Promise((res, rej) => {
                const r = new FileReader();
                r.onload = e => res(e.target.result);
                r.onerror = rej;
                r.readAsDataURL(file);
            });
            // Exported artwork almost always carries a wide transparent margin.
            // Left in, that margin is part of the frame: the plaque ends up
            // floating in the middle of the card and the text sits off it. Cut
            // it away before anything is measured.
            const cut = await trimTransparent(raw, 6);
            const fitted = await analyzeFrameImage(cut.src);
            saved += Math.max(0, raw.length - (fitted.bytes || 0));
            frames.push({
                id: genId(),
                name: (file.name || 'Рамка').replace(/\.[^.]+$/, '').slice(0, 24),
                ...fitted,
                scale: 1,
            });
        } catch (e) {
            console.error(LOG, 'frame upload failed', e);
            if (typeof toastr !== 'undefined') toastr.error('Не удалось загрузить рамку: ' + (e.message || e));
        }
    }
    save(true);
    injectCustomFrameCss();
    renderFrameList();
    const kb = Math.round(saved / 1024);
    toastr?.success(`Рамка добавлена — ищите её в «Оформление»${kb > 20 ? `. Сжато на ${kb} КБ` : ''}`);
}

// Frames measured by an older version are re-measured once, quietly, at start-up.
// Only the numbers change — the picture itself is left exactly as stored.
async function refreshStaleFrames() {
    const frames = customFrames().filter(f => f.src && f.mode && (f.v || 0) < FRAME_ANALYSIS_V);
    if (!frames.length) return;
    let fixed = 0;
    for (const f of frames) {
        try {
            const measured = await analyzeFrameImage(f.src, 512, true);
            // Keep the name, the id and the user's own scale; replace what was measured.
            Object.assign(f, measured);
            fixed++;
        } catch (e) { console.warn(LOG, 're-measuring frame failed', f.name, e); }
    }
    if (!fixed) return;
    console.log(LOG, `re-measured ${fixed} frame(s) with the current analysis`);
    save();
    injectCustomFrameCss();
    renderFrameList();
    if ($('#mb-modal').is(':visible')) renderBoard();
}

// Runs the current processing over frames that were added before it existed.
async function reprocessFrames() {
    const frames = customFrames();
    if (!frames.length) { toastr?.info('Своих рамок пока нет'); return; }
    await showBusy('Пересобираю рамки…');
    let before = 0, after = 0;
    try {
        for (const f of frames) {
            if (!f.src) continue;
            // Measured in encoded bytes, not in the length of whatever `src`
            // happens to hold — a stored frame's src is a path a few dozen
            // characters long, which would report an absurd saving.
            before += f.bytes || f.src.length;
            try {
                const cut = await trimTransparent(f.src, 6);
                const fitted = await analyzeFrameImage(cut.src);
                Object.assign(f, fitted);
            } catch (e) { console.warn(LOG, 'frame reprocess failed', f.name, e); }
            after += f.bytes || f.src.length;
        }
        save(true);
        injectCustomFrameCss();
        renderFrameList();
        renderBoard();
    } finally { hideBusy(); }
    const kb = Math.round((before - after) / 1024);
    toastr?.success(kb > 0 ? `Готово, стало легче на ${kb} КБ` : 'Готово');
}

// Works out how to fit an arbitrary PNG by reading its alpha channel, instead of
// assuming every frame has the same proportions. Two shapes get handled:
//
//  · a frame — artwork around a see-through middle. Measured per side, then used
//    as a border-image with matching slices, so corners keep their shape and only
//    the straight edges stretch.
//  · a backdrop — a solid painted shape such as a brush stroke, with nothing to
//    see through. There is no border to slice, so it becomes a stretched
//    background with padding that keeps the text on the paint.
//
// The earlier version squashed everything into a square and always sliced at 33%,
// which is what distorted the artwork and left rectangular seams.
// Bumped whenever the measuring changes, so frames measured by an older version
// can be found and put right without the user having to know about it.
const FRAME_ANALYSIS_V = 2;

// `keepSrc` re-measures a picture that is already stored, without encoding it
// again — a second round trip through the encoder would cost quality for nothing.
async function analyzeFrameImage(src, max = 512, keepSrc = false) {
    const img = new Image();
    img.src = src;
    await img.decode();

    // Normalise size, aspect ratio intact.
    const ratio = Math.min(1, max / Math.max(img.width, img.height));
    const w = Math.max(8, Math.round(img.width * ratio));
    const h = Math.max(8, Math.round(img.height * ratio));
    const c = document.createElement('canvas');
    c.width = w; c.height = h;
    const ctx = c.getContext('2d');
    ctx.drawImage(img, 0, 0, w, h);
    const data = ctx.getImageData(0, 0, w, h).data;
    const alphaAt = (x, y) => data[((y * w + x) << 2) + 3];
    const CLEAR = 40;   // treat this and below as see-through

    // Probe several lines rather than one, so a gap in the artwork or a dark
    // flourish crossing the middle doesn't throw the measurement off.
    const probe = (fracs, scan) => {
        const vals = fracs.map(scan).filter(v => v !== null);
        if (!vals.length) return null;
        vals.sort((a, b) => a - b);
        return vals[Math.floor(vals.length / 2)];   // median
    };
    const rows = [0.35, 0.5, 0.65], cols = [0.35, 0.5, 0.65];

    // The see-through window along one line, as [where it starts, where it ends].
    //
    // It is found as the LONGEST run of transparency on that line, not the first.
    // An ornate frame — a bow at the bottom, filigree, a crest — has little gaps
    // inside its own artwork, and taking the first gap as the window cut the
    // ornament off: the frame was sliced through the middle of its decoration and
    // the photo was left sitting on top of the rest of it.
    const holeSpan = (len, sample) => {
        let best = null, bestLen = 0;
        let run = -1;
        for (let i = 0; i <= len; i++) {
            const clear = i < len && sample(i) <= CLEAR;
            if (clear) { if (run < 0) run = i; continue; }
            if (run >= 0) {
                const n = i - run;
                // A run that touches an edge is the outer margin, not the window.
                if (run > 0 && i < len && n > bestLen) { bestLen = n; best = [run, i]; }
                run = -1;
            }
        }
        return best;
    };

    // One span per probe line, then each edge is the median across the lines.
    const rowSpans = rows.map(f => holeSpan(w, i => alphaAt(i, Math.round(h * f))));
    const colSpans = cols.map(f => holeSpan(h, i => alphaAt(Math.round(w * f), i)));
    const left = probe(rowSpans, s => (s ? s[0] : null));
    const right = probe(rowSpans, s => (s ? w - s[1] : null));
    const top = probe(colSpans, s => (s ? s[0] : null));
    const bottom = probe(colSpans, s => (s ? h - s[1] : null));

    // WebP keeps the alpha channel and is a fraction of the size of the PNG these
    // usually arrive as; PNG stays as the fallback where it wins or is all the
    // browser can produce.
    let best = src;
    if (!keepSrc) {
        const png = c.toDataURL('image/png');
        best = png;
        try {
            const webp = c.toDataURL('image/webp', 0.92);
            if (webp.startsWith('data:image/webp') && webp.length < png.length) best = webp;
        } catch (e) { /* no webp encoder: PNG it is */ }
    }
    // `bytes` is what the encoded artwork weighs, recorded before it is moved out
    // to a file — once `src` is a path, its length says nothing about the picture.
    // With keepSrc there was no encoding, so whatever was measured before stands.
    const out = { src: await storeImage(best), sw: w, sh: h, v: FRAME_ANALYSIS_V };
    if (!keepSrc) out.bytes = best.length;

    // Nothing transparent along any middle line, or the hole would be so large
    // there is barely any artwork left: not a frame.
    const noHole = left === null || right === null || top === null || bottom === null;
    const holeW = noHole ? 0 : w - left - right;
    const holeH = noHole ? 0 : h - top - bottom;
    if (noHole || holeW < w * 0.12 || holeH < h * 0.12) {
        out.mode = 'backdrop';
        // Keep text off the ragged edges of a painted shape.
        out.pad = { t: Math.round(h * 0.14), r: Math.round(w * 0.10),
                    b: Math.round(h * 0.14), l: Math.round(w * 0.10) };
        // Where to cut it for stretching. The ends of a plaque carry the shape —
        // the curl of a banner, the taper of a brush stroke — so a generous third
        // of each side is kept intact and only the middle is allowed to stretch.
        out.slice3 = { t: 32, r: 32, b: 32, l: 32 };
        return out;
    }

    out.mode = 'frame';
    // A couple of pixels of overlap hides seams where edge meets corner.
    // The ceiling is per axis and generous: a frame whose bottom is one big
    // ornament — a bow, a plaque, a crest — genuinely is half artwork, and
    // clamping it lower is what chopped the ornament in half.
    const grow = 1;
    out.inset = {
        t: Math.min(Math.max(1, top + grow), Math.floor(h * 0.48)),
        r: Math.min(Math.max(1, right + grow), Math.floor(w * 0.48)),
        b: Math.min(Math.max(1, bottom + grow), Math.floor(h * 0.48)),
        l: Math.min(Math.max(1, left + grow), Math.floor(w * 0.48)),
    };
    return out;
}

function renderFrameList() {
    const $l = $('#mb-frame-list');
    if (!$l.length) return;
    $l.empty();
    const frames = customFrames();
    if (!frames.length) { $l.append('<div class="mb-empty-hint">Своих рамок пока нет.</div>'); return; }
    frames.forEach(f => {
        const modeLabel = f.mode === 'backdrop' ? 'фон' : 'рамка';
        const $row = $(`<div class="mb-custom-row">
            <span class="mb-custom-prev mb-frame-prev-${f.id}"></span>
            <span class="mb-custom-col">
                <span class="mb-custom-name">${escHtml(f.name)}</span>
                <span class="mb-custom-sub">
                    <a class="mb-mode-toggle">${modeLabel}</a> · ${f.sw || '?'}×${f.sh || '?'}
                </span>
            </span>
            <span class="mb-custom-tune"><i class="fa-solid fa-minus" data-d="-0.15" title="Тоньше"></i>
              <b>${Math.round((f.scale || 1) * 100)}%</b>
              <i class="fa-solid fa-plus" data-d="0.15" title="Толще"></i></span>
            <i class="fa-solid fa-trash mb-custom-del" title="Удалить"></i>
        </div>`);
        $row.find('.mb-custom-tune i').on('click', function() {
            f.scale = Math.max(0.3, Math.min(3, (f.scale || 1) + parseFloat($(this).data('d'))));
            save(true); injectCustomFrameCss(); renderFrameList();
        });
        // Auto-detection is a guess; let it be overridden rather than stranding a
        // frame that was read the wrong way.
        $row.find('.mb-mode-toggle').on('click', () => {
            f.mode = f.mode === 'backdrop' ? 'frame' : 'backdrop';
            if (f.mode === 'frame' && !f.inset) {
                f.inset = { t: Math.round((f.sh || 100) * 0.2), r: Math.round((f.sw || 100) * 0.2),
                            b: Math.round((f.sh || 100) * 0.2), l: Math.round((f.sw || 100) * 0.2) };
            }
            if (f.mode === 'backdrop' && !f.pad) {
                f.pad = { t: Math.round((f.sh || 100) * 0.14), r: Math.round((f.sw || 100) * 0.10),
                          b: Math.round((f.sh || 100) * 0.14), l: Math.round((f.sw || 100) * 0.10) };
            }
            save(true); injectCustomFrameCss(); renderFrameList();
        });
        $row.find('.mb-custom-del').on('click', async () => {
            if (!await mbConfirm('Удалить рамку?', f.name, { okLabel: 'Удалить', danger: true })) return;
            boards.global.frames = customFrames().filter(x => x.id !== f.id);
            save(true); injectCustomFrameCss(); renderFrameList();
        });
        $l.append($row);
        // Preview built in JS so it reuses the very same CSS the cards get.
        applyFramePreview($row.find('.mb-custom-prev')[0], f);
    });
}

// Paints a swatch with the frame's real styling, scaled down to thumbnail size.
function applyFramePreview(el, f) {
    if (!el) return;
    const k = Math.max(0.3, Math.min(3, f.scale || 1));
    if (!f.mode) {
        el.style.cssText = `border-style:solid;border-width:12px;` +
            `border-image:url(${f.src}) ${f.slice || 33}% fill stretch`;
        return;
    }
    if (f.mode === 'backdrop') {
        el.style.cssText = `background:url(${f.src}) 50% 50% / 100% 100% no-repeat`;
        return;
    }
    const i = f.inset;
    const pc = (v, t) => +(v / t * 100).toFixed(3);
    // Thumbnails are tiny, so cap the band width or the artwork fills the swatch.
    const cap = v => Math.max(4, Math.min(14, Math.round(v * k * 0.35)));
    el.style.cssText = `border-style:solid;` +
        `border-width:${cap(i.t)}px ${cap(i.r)}px ${cap(i.b)}px ${cap(i.l)}px;` +
        `border-image:url(${f.src}) ${pc(i.t, f.sh)}% ${pc(i.r, f.sw)}% ${pc(i.b, f.sh)}% ${pc(i.l, f.sw)}% stretch`;
}

function customFrameFor(card) {
    const shape = card?.shape || '';
    if (!shape.startsWith('custom-')) return null;
    return customFrames().find(f => f.id === shape.slice(7)) || null;
}

// The stylesheet can only state one thickness for a frame, but a frame has to
// look right on a 160px note and on a 900px one. This sizes the band per card,
// in proportion to how big the card is next to the artwork it was cut from —
// which is what stops a small card from being all border and no room, the state
// that made text jump around while it was being resized.
function applyCustomFrameSizing($card, card, liveW) {
    const el = $card && $card[0];
    if (!el) return;
    const f = customFrameFor(card);
    if (!f || !f.mode) {
        el.style.removeProperty('border-width');
        el.style.removeProperty('padding');
        return;
    }
    const band = f.mode === 'backdrop' ? f.pad : f.inset;
    if (!band) return;
    const w = liveW || card.w || el.offsetWidth || f.sw;
    const k = Math.max(0.3, Math.min(3, f.scale || 1));
    const s = Math.max(0.3, Math.min(2.5, w / f.sw)) * k;
    // Sideways the bands are capped, because the card's width is fixed and two
    // fat bands would leave nothing between them. Vertically there is nothing to
    // protect: the card simply grows taller, so a frame with a tall ornament at
    // the bottom keeps it at full size instead of being squashed to fit a cap.
    const capX = Math.max(6, w * 0.3);
    const capY = 4000;
    const px = (v, cap) => Math.round(Math.max(2, Math.min(cap, v * s)));
    const box = `${px(band.t, capY)}px ${px(band.r, capX)}px ${px(band.b, capY)}px ${px(band.l, capX)}px`;
    // A frame keeps text inside its hole with a border; a plaque keeps it on the
    // paint with padding. Either way the inset now tracks the card's size, which
    // is what stops the text from wandering as a card is dragged bigger.
    if (f.mode === 'backdrop') {
        el.style.removeProperty('border-width');
        el.style.setProperty('padding', box, 'important');
    } else {
        el.style.removeProperty('padding');
        el.style.setProperty('border-width', box, 'important');
    }
}

// One stylesheet holding a rule per custom frame, rewritten whenever they change.
function injectCustomFrameCss() {
    let el = document.getElementById('mb-custom-frame-css');
    if (!el) {
        el = document.createElement('style');
        el.id = 'mb-custom-frame-css';
        document.head.appendChild(el);
    }
    el.textContent = customFrames().map(f => frameCss(f)).join('\n');
}

function frameCss(f) {
    const sel = `.mb-card.shape-custom-${f.id}`;
    const hide = `${sel} .mb-card-color-strip, ${sel} .mb-card-pin { display: none; }`;
    const k = Math.max(0.3, Math.min(3, f.scale || 1));

    // Legacy entries from the first version of this feature carried only a flat
    // slice; render them the old way rather than dropping them on the floor.
    if (!f.mode) {
        return `${sel} {
    border-style: solid !important;
    border-width: ${Math.round((f.width || 26) * k)}px !important;
    border-image: url(${f.src}) ${f.slice || 33}% fill stretch !important;
    border-radius: 0 !important; background: transparent !important; box-shadow: none !important;
}\n${hide}`;
    }

    if (f.mode === 'backdrop') {
        // A painted plaque is stretched whole rather than nine-sliced. Slicing
        // keeps the ends undistorted, but the corners and the stretched middle
        // then scale by different amounts, and on soft artwork like this the
        // mismatch shows up as seams across the picture. A shape with no hole in
        // it has nothing to hide them behind, so it stretches as one piece.
        //
        // What was actually broken here was the padding: fixed pixels, so a
        // small card was nearly all margin and a big one had text sprawling off
        // the paint. It is proportional now — see applyCustomFrameSizing.
        const p = f.pad || { t: 18, r: 14, b: 18, l: 14 };
        return `${sel} {
    border: none !important; border-radius: 0 !important; box-shadow: none !important;
    background: url(${f.src}) 50% 50% / 100% 100% no-repeat !important;
    padding: ${Math.round(p.t * k)}px ${Math.round(p.r * k)}px ${Math.round(p.b * k)}px ${Math.round(p.l * k)}px;
}\n${hide}`;
    }

    const i = f.inset;
    // Slices are percentages of the source; the band drawn on screen is tied to
    // the border width by `border-image-width: 1`, so shrinking a card shrinks
    // the frame with it instead of leaving a fat border and a sliver of text.
    // The width itself carries no !important: renderCard sizes it per card.
    const pc = (v, total) => +(v / total * 100).toFixed(3);
    return `${sel} {
    border-style: solid !important;
    border-width: ${Math.round(i.t * k)}px ${Math.round(i.r * k)}px ${Math.round(i.b * k)}px ${Math.round(i.l * k)}px;
    border-image-source: url(${f.src}) !important;
    border-image-slice: ${pc(i.t, f.sh)}% ${pc(i.r, f.sw)}% ${pc(i.b, f.sh)}% ${pc(i.l, f.sw)}% !important;
    border-image-width: 1 !important;
    border-image-repeat: stretch !important;
    border-radius: 0 !important;
    box-shadow: none !important;
    /* No card colour behind a frame. A card paints its cream over the whole
       border box, including underneath the artwork — so every part of the frame
       that is transparent showed cream: a pale outline around the picture, and a
       pale rectangle behind the rounded corners of the frame itself. The frame
       is the whole of the card's appearance; nothing may sit behind it. */
    background: transparent !important;
}
/* A picture needs nothing behind it — the frame holds the photo and that is all.
   Text does: a note whose window opens straight onto the board is unreadable, so
   the paper is painted inside the window only, never around the artwork. */
${sel} .mb-card-content-wrap { background: transparent; }
${sel} .mb-card-content { background: var(--mb-card-bg); }
${sel} .mb-card-content:empty { background: transparent; }
${hide}`;
}

// ===== USER-SUPPLIED FONTS =====
function customFonts() {
    if (!boards.global) boards.global = { cards: [] };
    if (!Array.isArray(boards.global.fonts)) boards.global.fonts = [];
    return boards.global.fonts;
}

// Three ways in, because good fonts live in more places than Google:
//
//   1. a Google Fonts CSS link   → https://fonts.googleapis.com/css2?family=Bad+Script
//   2. a direct font file link   → …/whatever.woff2 | .woff | .ttf | .otf
//   3. a font file from the disk (handled by addCustomFontFile)
//
// A CSS stylesheet is only fetched from Google, because a stylesheet can pull in
// anything it likes. Other hosts must point straight at the font file, which is
// wrapped in an @font-face here — that can only ever be a font.
const FONT_FILE_RE = /\.(woff2|woff|ttf|otf)(\?|#|$)/i;

function parseFontInput(input) {
    const raw = (input || '').trim();
    if (!raw) return null;
    let url;
    try { url = new URL(raw); } catch (e) { return null; }
    if (!/^https?:$/.test(url.protocol)) return null;

    if (url.hostname === 'fonts.googleapis.com') {
        const fams = url.searchParams.getAll('family');
        if (!fams.length) return null;
        const family = fams[0].split(':')[0].replace(/\+/g, ' ').trim();
        if (!family) return null;
        return { kind: 'css', family, href: url.toString() };
    }
    if (FONT_FILE_RE.test(url.pathname)) {
        // "…/BadScript-Regular.woff2" -> "BadScript Regular"
        const base = decodeURIComponent(url.pathname.split('/').pop() || '')
            .replace(FONT_FILE_RE, '').replace(/[._-]+/g, ' ').trim();
        return { kind: 'file', family: base || 'Свой шрифт', href: url.toString(), needsName: true };
    }
    return null;
}

// CDN filenames are often hashes, and a font called "6NUT8F6PJgbFWQn47" is no use
// in a picker. Offer the derived name and let it be corrected.
async function askFontName(suggested) {
    const looksHashed = /^[A-Za-z0-9\s]{16,}$/.test(suggested) && !/\s(regular|italic|bold|light|medium)\b/i.test(suggested);
    const preset = looksHashed ? '' : suggested;
    const name = await mbPrompt('Название шрифта', preset, 'Как показывать его в списке');
    return (name || suggested).slice(0, 40);
}

async function addCustomFont(input) {
    const parsed = parseFontInput(input);
    if (!parsed) {
        toastr?.error('Нужна либо ссылка с fonts.googleapis.com, либо прямая ссылка на файл .woff2 / .woff / .ttf / .otf');
        return;
    }
    if (parsed.needsName) parsed.family = await askFontName(parsed.family);
    delete parsed.needsName;
    await registerFont(parsed);
    $('#mb-font-url').val('');
}

// A font picked from disk is embedded as data, so it keeps working offline and
// cannot break when someone else's site goes away.
async function addCustomFontFile(file) {
    if (!file) return;
    if (file.size > 6 * 1024 * 1024) {
        toastr?.error('Файл шрифта больше 6 МБ — возьмите вариант .woff2');
        return;
    }
    const href = await new Promise((res, rej) => {
        const r = new FileReader();
        r.onload = e => res(e.target.result);
        r.onerror = rej;
        r.readAsDataURL(file);
    });
    const derived = (file.name || 'Свой шрифт').replace(FONT_FILE_RE, '')
        .replace(/\.[^.]+$/, '').replace(/[._-]+/g, ' ').trim() || 'Свой шрифт';
    await registerFont({ kind: 'file', family: await askFontName(derived), href });
}

async function registerFont(entry) {
    const fonts = customFonts();
    if (fonts.some(f => f.family === entry.family)) {
        toastr?.info('Шрифт с таким названием уже добавлен');
        return;
    }
    fonts.push(entry);
    save(true);
    loadCustomFonts();
    renderFontList();
    // Say plainly whether it arrived, and whether Russian will actually render.
    try {
        await document.fonts.load(`400 16px "${entry.family}"`, 'Ilove');
        await document.fonts.load(`400 16px "${entry.family}"`, 'Ялюблю');
        const ok = document.fonts.check(`400 16px "${entry.family}"`, 'Ilove');
        const cyr = document.fonts.check(`400 16px "${entry.family}"`, 'Ялюблю');
        if (!ok) toastr?.warning(`«${entry.family}» не загрузился — проверьте ссылку или файл`);
        else if (!cyr) toastr?.warning(`«${entry.family}» добавлен, но кириллицы в нём нет — русский текст останется обычным`);
        else toastr?.success(`Шрифт «${entry.family}» добавлен`);
    } catch (e) { /* the entry stands either way */ }
}

function loadCustomFonts() {
    const fonts = customFonts();
    // Google stylesheets go in as <link>; everything else as an @font-face rule.
    document.querySelectorAll('link[data-mb-font]').forEach(l => {
        if (!fonts.some(f => f.kind === 'css' && f.href === l.href)) l.remove();
    });
    fonts.filter(f => f.kind === 'css' || !f.kind).forEach(f => {
        if ([...document.querySelectorAll('link[data-mb-font]')].some(l => l.href === f.href)) return;
        const link = document.createElement('link');
        link.rel = 'stylesheet';
        link.href = f.href;
        link.setAttribute('data-mb-font', f.family);
        document.head.appendChild(link);
    });

    let el = document.getElementById('mb-custom-font-css');
    if (!el) {
        el = document.createElement('style');
        el.id = 'mb-custom-font-css';
        document.head.appendChild(el);
    }
    const fmt = href => {
        const m = /\.(woff2|woff|ttf|otf)/i.exec(href) || [];
        return { woff2: 'woff2', woff: 'woff', ttf: 'truetype', otf: 'opentype' }[(m[1] || '').toLowerCase()] || 'woff2';
    };
    el.textContent = fonts.filter(f => f.kind === 'file').map(f =>
        `@font-face{font-family:"${f.family}";src:url("${f.href}") format("${fmt(f.href)}");font-display:swap;}`
    ).join('\n');
}

function renderFontList() {
    const $l = $('#mb-font-list');
    if (!$l.length) return;
    $l.empty();
    const fonts = customFonts();
    if (!fonts.length) { $l.append('<div class="mb-empty-hint">Своих шрифтов пока нет.</div>'); return; }
    fonts.forEach(f => {
        const $row = $(`<div class="mb-custom-row">
            <span class="mb-custom-name" style="font-family:'${f.family}',sans-serif">${escHtml(f.family)} — Аа Aa</span>
            <i class="fa-solid fa-trash mb-custom-del" title="Удалить"></i>
        </div>`);
        $row.find('.mb-custom-del').on('click', async () => {
            if (!await mbConfirm('Удалить шрифт?', f.family, { okLabel: 'Удалить', danger: true })) return;
            boards.global.fonts = customFonts().filter(x => x.family !== f.family);
            save(true); loadCustomFonts(); renderFontList();
        });
        $l.append($row);
    });
}

// ===== CARD STYLING =====
const CARD_FRAMES = {
    image: [
        ['none','Без рамки','ban'],
        ['default','Простая','square'], ['rounded','Скруглённая','clone'], ['polaroid','Полароид','image'],
        ['circle','Круг','circle'], ['tape','На скотче','note-sticky'], ['film','Плёнка','film'],
        ['stamp','Марка','stamp'], ['gold','Золочёная','crown'], ['double','Двойная','table-cells-large'],
        ['shadowbox','Тень','box'], ['washi','Васи-скотч','ribbon'],
    ],
    text: [
        ['none','Без рамки','ban'],
        ['default','Простая','square'], ['rounded','Скруглённая','clone'], ['torn','Рваная','file-invoice'],
        ['tape','На скотче','note-sticky'], ['stamp','Марка','stamp'], ['gold','Золочёная','crown'],
        ['double','Двойная','table-cells-large'], ['notebook','Тетрадь','book'],
        ['ticket','Билет','ticket'], ['postit','Стикер','note-sticky'],
        ['shadowbox','Тень','box'], ['washi','Васи-скотч','ribbon'],
    ],
};
const ALL_FRAME_CLASSES = [...new Set([...CARD_FRAMES.image, ...CARD_FRAMES.text].map(f => 'shape-' + f[0]))].join(' ');
// Every stack ends in fallbacks that exist on Android as well as desktop, and
// all of them cover Cyrillic — Impact and Arial Black do not, so they sit behind
// narrower faces that do.
const CARD_FONTS = [
    ['', 'Обычный'],
    ['var(--mb-font-handwritten)', 'Рукописный'],
    ["'Courier New', 'Droid Sans Mono', monospace", 'Печатная машинка'],
    ["Georgia, 'Noto Serif', 'Times New Roman', serif", 'С засечками'],
    ["'Trebuchet MS', Roboto, 'Segoe UI', sans-serif", 'Без засечек'],
    ["'Comic Sans MS', 'Segoe Print', cursive", 'Комиксный'],
    ["Impact, 'Roboto Condensed', 'Arial Narrow', sans-serif", 'Плакатный'],
];

// Google Fonts splits Caveat/Inter into per-script files selected by
// unicode-range, and the browser only fetches a subset once it has to paint a
// glyph from it. On a phone that request often loses the race (or never
// happens), so Latin text got the real font and Cyrillic silently fell back.
// Asking for both scripts up front forces every subset to download.
async function preloadCardFonts() {
    if (!document.fonts?.load) return;
    const samples = ['Ялюблюэтот', 'Ilovethis'];
    const specs = ['400 16px Caveat', '600 16px Caveat', '400 16px Inter', '600 16px Inter'];
    try {
        await Promise.all(specs.flatMap(s => samples.map(t => document.fonts.load(s, t))));
    } catch (e) { console.warn(LOG, 'font preload failed', e); }
}
const CARD_SIZES = [['0.8em','XS'],['1em','S'],['1.2em','M'],['1.5em','L'],['2em','XL'],['2.6em','XXL']];
// [tooltip, icon, what goes before the selection, what goes after, what to insert
// when nothing is selected]
const MARKUP_BTNS = [
    ['Спойлер — свёрнутый блок', 'eye-slash', '[spoiler=Заголовок]\n', '\n[/spoiler]', 'спрятанный текст'],
    ['Замазать в строке', 'eye-low-vision', '||', '||', 'секрет'],
    ['Жирный', 'bold', '**', '**', 'текст'],
    ['Курсив', 'italic', '*', '*', 'текст'],
    ['Подчёркнутый', 'underline', '__', '__', 'текст'],
    ['Зачёркнутый', 'strikethrough', '~~', '~~', 'текст'],
    ['Моноширинный', 'code', '`', '`', 'код'],
    ['Заголовок', 'heading', '# ', '', 'Заголовок'],
    ['Цитата', 'quote-left', '> ', '', 'цитата'],
];

// ===== CARD SIZE =====
// The corner handle can only ever drag as far as the screen is wide, which on a
// phone is a few hundred pixels — so a card could never be made genuinely large
// by dragging. Everything that sets a width goes through here, and the panel
// offers a slider that is not bounded by the size of your hand.
const CARD_W_MIN = 60, CARD_W_MAX = 3000;
function clampCardW(w) { return Math.round(Math.max(CARD_W_MIN, Math.min(CARD_W_MAX, w || 0))); }

// Which copy of a picture this card should be showing.
//
// A preview is ~520px wide; blown up past that it turns to mush, so a card being
// painted bigger than that gets the original instead. The question is what
// "bigger" means. This used to compare `card.w` — the card's width in *board*
// coordinates — against 520, which is not a size on the screen at all: at a
// typical phone zoom of 0.4 a card 600 board-px wide occupies about 240 real
// pixels, and it was still handed the full-size original. That is the difference
// between a 0.5 MB decoded bitmap and a 10 MB one, per card, for no visible gain.
//
// What matters is how many device pixels the picture actually covers.
function bestSrcFor(card) {
    if (!card || !card.content) return '';
    if (!card.thumb) return card.content;              // there is only one copy
    const cap = window.innerWidth <= 768 ? 2 : 3;
    const dpr = Math.min(window.devicePixelRatio || 1, cap);
    const onScreen = (card.w || 220) * zoom * dpr;
    // The margin is slack, not precision: it keeps a card parked exactly on the
    // boundary from swapping its source back and forth on every nudge of the zoom.
    return onScreen > IMG_THUMB_DIM * 1.15 ? card.content : card.thumb;
}

// Re-checks that choice for every card on the board. Only zoom can change the
// answer, so this is driven from the zoom settle rather than from every frame.
function refreshImgTiers() {
    const byId = new Map((getBoard().cards || []).map(c => [c.id, c]));
    for (const img of document.querySelectorAll('#mb-canvas-inner .mb-card > .mb-card-content-wrap > img')) {
        const card = byId.get(img.closest('.mb-card')?.dataset.id);
        if (!card || !card.content) continue;
        const want = bestSrcFor(card);
        if (!want) continue;
        // Asleep behind the blank pixel: correct what it will wake up as, and
        // leave the sleeping <img> alone.
        if (img.dataset.mbSrc) { img.dataset.mbSrc = want; continue; }
        if (img.getAttribute('src') !== want) img.setAttribute('src', want);
    }
}

function setCardWidth(card, $card, w) {
    card.w = clampCardW(w);
    $card.addClass('has-size').css('width', card.w + 'px');
    applyCustomFrameSizing($card, card);
    const img = $card.find('img')[0];
    if (img && (card.type === 'image' || card.type === 'sticker') && card.content) {
        const want = bestSrcFor(card);
        if (img.dataset.mbSrc) img.dataset.mbSrc = want;   // asleep right now; wake up with the right one
        else if (img.getAttribute('src') !== want) img.setAttribute('src', want);
    }
    linkGeomDirty = true;
    save();
    renderInk();
    scheduleCull();
}

// The size row every panel shares: a slider that reaches far past the screen,
// the exact number, and the two steps people actually want.
function appendSizeControl($body, card, $card) {
    const el = () => ($card && $card.length ? $card : $(`.mb-card[data-id="${card.id}"]`));
    $body.append('<span class="mb-settings-label">Размер</span>');
    const $row = $('<div class="mb-size-ctl"></div>').appendTo($body);
    const cur = () => clampCardW(card.w || el().width() || 200);
    const $sl = $(`<input type="range" min="${CARD_W_MIN}" max="${CARD_W_MAX}" step="10" value="${cur()}">`).appendTo($row);
    const $num = $(`<input type="number" class="mb-ctx-num" min="${CARD_W_MIN}" max="${CARD_W_MAX}" step="10" value="${cur()}">`).appendTo($row);
    const apply = (w, from) => {
        const v = clampCardW(w);
        if (from !== 'slider') $sl.val(v);
        if (from !== 'num') $num.val(v);
        setCardWidth(card, el(), v);
        if (card.type === 'tree') repaintTree(card, el());
    };
    $sl.on('input', function() { apply(this.value, 'slider'); });
    $num.on('input change', function() { apply(this.value, null); })
        .on('keydown', e => e.stopPropagation());
    const $steps = $('<div class="mb-size-steps"></div>').appendTo($body);
    [['÷2', () => cur() / 2], ['−100', () => cur() - 100], ['+100', () => cur() + 100],
     ['×2', () => cur() * 2], ['Во всю ширь', () => CARD_W_MAX]].forEach(([label, calc]) => {
        $(`<button class="mb-size-step">${label}</button>`)
            .on('click', () => apply(calc(), null)).appendTo($steps);
    });
    $body.append('<div class="mb-select-hint">Уголок карточки тоже тянется, но на телефоне дальше края экрана не утащишь — здесь предел в 3000 px.</div>');
}

function applyCardTypography($card, card, isImg) {
    if (isImg) return;
    const $c = $card.find('.mb-card-content');
    $c.css('font-size', card.fontSize || '');
    $c.css('font-family', card.fontFamily || '');
    $c.css('text-align', card.align || '');
    $c.css('color', card.textColor || '');
}

// Colours reached for lately, newest first. Kept apart from the pinned palette:
// one is deliberate, this one just remembers.
function recentColors() {
    if (!boards.global) boards.global = { cards: [] };
    if (!Array.isArray(boards.global.recentColors)) boards.global.recentColors = [];
    return boards.global.recentColors;
}
function rememberColor(hex) {
    if (!/^#[0-9a-f]{6}$/i.test(hex || '')) return;
    const r = recentColors();
    const i = r.indexOf(hex);
    if (i >= 0) r.splice(i, 1);
    r.unshift(hex);
    if (r.length > 12) r.length = 12;
}

function layerPositionText(card) {
    const cards = getBoard().cards || [];
    const sorted = [...cards].sort((a, b) => (a.z || 0) - (b.z || 0));
    const i = sorted.indexOf(card);
    if (i < 0) return '';
    return `${i + 1}-й снизу из ${sorted.length}`;
}

// Set while a note's panel is open; every control that changes how the card
// looks calls it so the preview follows along. Cleared when a panel for
// something other than a note is built.
let notePreviewRepaint = null;
function refreshNotePreview() { if (typeof notePreviewRepaint === 'function') notePreviewRepaint(); }

// The note's text, its markup buttons, and a live copy of how the card will
// look. The preview is the answer to the awkward part of moving typing off the
// board: on a phone the panel covers the card, so the card is brought into the
// panel instead — same renderer, same fonts, same spoilers, all of it tappable.
function appendNoteEditor($body, card, $card) {
    const isQuote = card.type === 'quote';
    $body.append('<span class="mb-settings-label" style="margin-top:4px">Текст заметки</span>');
    const $bar = $('<div class="mb-markup-bar"></div>').appendTo($body);
    const $ta = $('<textarea class="mb-settings-input mb-note-editor" rows="6" spellcheck="false"></textarea>')
        .val(card.content || '');
    const $prevWrap = $('<div class="mb-note-preview"></div>');

    // The preview is a real card, not a lookalike: same classes, so the frame,
    // the colour strip and every shape rule apply to it exactly as they do on
    // the board. Anything less and "как это будет выглядеть" would be a promise
    // the panel could not keep.
    const paintPreview = () => {
        $prevWrap.empty();
        const shapeCls = card.shape ? `shape-${card.shape}` : 'shape-default';
        const $mini = $(`<div class="mb-card mb-preview-card has-size ${shapeCls}">
            <div class="mb-card-color-strip" style="background:${card.color || '#fdf6e3'}"></div>
            <div class="mb-card-content ${isQuote ? 'quote' : ''}">${renderNote(card.content)}</div>
        </div>`);
        $prevWrap.append($mini);
        applyCardTypography($mini, card, false);
        // Custom frames size their band against the card's width; the preview is
        // narrower than the real thing, so it is measured on its own terms.
        applyCustomFrameSizing($mini, card, Math.max(120, $prevWrap.width() || 260));
        bindNoteMarkup($mini);
    };
    // Every other control in the panel — font, size, frame, colour — calls this
    // after it changes something, so the preview keeps up with all of them and
    // not just with the text.
    notePreviewRepaint = paintPreview;
    const repaint = () => {
        const el = $card && $card.find('.mb-card-content')[0];
        if (el) {
            el.innerHTML = renderNote(card.content);
            bindNoteMarkup($card);
        }
        paintPreview();
        linkGeomDirty = true;
        renderInk();
    };
    const wrapSel = (before, after, sample) => {
        const el = $ta[0];
        const a = el.selectionStart ?? el.value.length, b = el.selectionEnd ?? el.value.length;
        const sel = el.value.slice(a, b) || sample;
        el.value = el.value.slice(0, a) + before + sel + after + el.value.slice(b);
        card.content = el.value;
        repaint(); save();
        el.focus();
        el.selectionStart = a + before.length;
        el.selectionEnd = a + before.length + sel.length;
    };
    MARKUP_BTNS.forEach(([label, icon, before, after, sample]) => {
        $(`<div class="mb-markup-btn" title="${label}"><i class="fa-solid fa-${icon}"></i></div>`)
            .on('click', e => { e.stopPropagation(); wrapSel(before, after, sample); })
            .appendTo($bar);
    });
    $ta.appendTo($body)
       .on('input', function() { card.content = this.value; repaint(); save(); })
       .on('keydown click pointerdown', e => e.stopPropagation());

    $body.append('<span class="mb-settings-label">Как это будет выглядеть</span>');
    $body.append($prevWrap);
    $body.append('<div class="mb-select-hint">Так же, как на доске: рамка, шрифт, размер и цвет — всё здесь настоящее. Спойлеры тоже открываются.</div>');
    paintPreview();

    // Text size sits right under the preview rather than далеко внизу among the
    // frames: matching a note to what is already on the board is a nudge-and-look
    // job, and the two halves of it should be in the same glance.
    $body.append('<span class="mb-settings-label">Размер текста</span>');
    const $fs = $('<div class="mb-fontsize-row"></div>').appendTo($body);
    const emOf = () => {
        const v = parseFloat(card.fontSize);
        return Number.isFinite(v) ? v : 1;
    };
    const setEm = v => {
        const em = Math.max(0.6, Math.min(4, Math.round(v * 20) / 20));
        card.fontSize = em + 'em';
        $card?.find('.mb-card-content').css('font-size', card.fontSize);
        $val.text(Math.round(em * 100) + '%');
        $body.find('.mb-size-opt[data-em]').removeClass('active')
             .filter(`[data-em="${card.fontSize}"]`).addClass('active');
        linkGeomDirty = true;
        paintPreview(); save(); renderInk();
    };
    $('<button class="mb-size-step big">−</button>').on('click', () => setEm(emOf() - 0.1)).appendTo($fs);
    const $val = $(`<b class="mb-fontsize-val">${Math.round(emOf() * 100)}%</b>`).appendTo($fs);
    $('<button class="mb-size-step big">+</button>').on('click', () => setEm(emOf() + 0.1)).appendTo($fs);
    const $presets = $('<div class="mb-size-row"></div>').appendTo($body);
    CARD_SIZES.forEach(([val, label]) => {
        $(`<div class="mb-size-opt ${(card.fontSize || '1em') === val ? 'active' : ''}" data-em="${val}">${label}</div>`)
            .on('click', () => setEm(parseFloat(val))).appendTo($presets);
    });

    $body.append(`<div class="mb-select-hint">
        <b>[spoiler=Заголовок]…[/spoiler]</b> — свёрнутый блок, раскрывается по нажатию.<br>
        <b>||текст||</b> — замазанный кусок прямо в строке.<br>
        <b>**жирный**</b>, <b>*курсив*</b>, <b>__подчёркнутый__</b>, <b>~~зачёркнутый~~</b>, <b>\`моно\`</b>,
        <b># заголовок</b>, <b>&gt; цитата</b>.
    </div>`);
}

function openStylePanel(card, $card) {
    // A stale closure from the last note would repaint a preview that is gone.
    notePreviewRepaint = null;
    const isImg = card.type === 'image';
    const frames = isImg ? CARD_FRAMES.image : CARD_FRAMES.text;
    const $body = $('#mb-frame-body').empty();
    const custom = customFrames();
    const allFrameCls = ALL_FRAME_CLASSES + ' ' + custom.map(f => 'shape-custom-' + f.id).join(' ');

    const pickFrame = ($grid, val) => {
        card.shape = val;
        $card.removeClass(allFrameCls).addClass('shape-' + val);
        applyCustomFrameSizing($card, card);
        $body.find('.mb-frame-opt').removeClass('active');
        $grid.addClass('active');
        refreshNotePreview();
        save();
    };

    // The text comes first: on a note it is the reason the panel was opened.
    if (card.type === 'text' || card.type === 'quote') appendNoteEditor($body, card, $card);
    if (card.type === 'collage') {
        $body.append('<span class="mb-settings-label" style="margin-top:4px">Подпись</span>');
        $('<input type="text" class="mb-settings-input" placeholder="например «то самое утро»">')
            .val(card.caption || '')
            .on('input', function() {
                card.caption = this.value;
                $card.find('.mb-booth-caption').text(this.value);
                save();
            })
            .on('keydown', e => e.stopPropagation())
            .appendTo($body);
    }

    $body.append('<span class="mb-settings-label" style="margin-top:4px">Слой</span>');
    const $lay = $('<div class="mb-size-row mb-layer-row"></div>').appendTo($body);
    [['back', 'В самый низ', 'angles-down'], ['down', 'Ниже', 'angle-down'],
     ['up', 'Выше', 'angle-up'], ['front', 'В самый верх', 'angles-up']].forEach(([w, title, icon]) => {
        $(`<div class="mb-size-opt" title="${title}"><i class="fa-solid fa-${icon}"></i></div>`)
            .on('click', () => {
                restack(card, w);
                $lay.next('.mb-layer-pos').text(layerPositionText(card));
            }).appendTo($lay);
    });
    $body.append(`<div class="mb-layer-pos mb-select-hint">${layerPositionText(card)}</div>`);

    appendSizeControl($body, card, $card);
    // A sticker is a picture and nothing else: no frame, no font, no colour.
    // Layer and size are the whole panel for it.
    if (card.type === 'sticker') { togglePanel('#mb-frame-panel', true); return; }

    if (isImg) {
        // Pictures pinned before the quality limit was raised are stored small,
        // and no export can invent detail that was never saved. Re-uploading the
        // same file replaces the pixels while keeping position, frame and layer.
        const im = new Image();
        im.src = card.content;
        const shown = () => im.naturalWidth ? `${im.naturalWidth}×${im.naturalHeight}`
                          : (card.origW ? `${card.origW} px по ширине` : '…');
        const tail = ` — это и есть потолок чёткости в PNG. Картинки, добавленные раньше, сохранялись до 1000 px, сейчас — до ${IMG_FULL_DIM} px.`;
        const $q = $(`<div class="mb-select-hint" style="margin-top:4px">Сохранено: <b>${shown()}</b>${tail}</div>`);
        im.onload = () => $q.html(`Сохранено: <b>${shown()}</b>${tail}`);
        $body.append('<span class="mb-settings-label" style="margin-top:4px">Качество</span>').append($q);
        $('<button class="mb-settings-btn secondary" style="margin-top:6px"><i class="fa-solid fa-arrows-rotate"></i> Заменить картинку</button>')
            .on('click', () => {
                const inp = document.createElement('input');
                inp.type = 'file'; inp.accept = 'image/*';
                inp.onchange = async e => {
                    const f = e.target.files?.[0];
                    if (!f) return;
                    const raw = await new Promise(res => {
                        const r = new FileReader();
                        r.onload = ev => res(ev.target.result);
                        r.readAsDataURL(f);
                    });
                    const img = await makeCardImage(raw);
                    card.content = img.content;
                    if (img.thumb) card.thumb = img.thumb; else delete card.thumb;
                    card.origW = img.origW;
                    delete card.noThumb;
                    $card.find('img').attr('src', bestSrcFor(card));
                    save(true);
                    openStylePanel(card, $card);   // refresh the reported size
                    toastr?.success('Картинка заменена');
                };
                inp.click();
            }).appendTo($body);
    }

    $body.append('<span class="mb-settings-label">Рамка</span>');
    const $fg = $('<div class="mb-frame-grid"></div>').appendTo($body);
    frames.forEach(([val, label, icon]) => {
        $(`<div class="mb-frame-opt ${(card.shape || 'default') === val ? 'active' : ''}"><i class="fa-solid fa-${icon}"></i><span>${label}</span></div>`)
            .on('click', function() { pickFrame($(this), val); }).appendTo($fg);
    });

    if (custom.length) {
        $body.append('<span class="mb-settings-label">Мои рамки</span>');
        const $cg = $('<div class="mb-frame-grid"></div>').appendTo($body);
        custom.forEach(f => {
            const val = 'custom-' + f.id;
            const $opt = $(`<div class="mb-frame-opt ${card.shape === val ? 'active' : ''}">
                 <span class="mb-frame-thumb"></span>
                 <span>${escHtml(f.name)}</span></div>`)
                .on('click', function() { pickFrame($(this), val); }).appendTo($cg);
            applyFramePreview($opt.find('.mb-frame-thumb')[0], f);
        });
    }


    if (!isImg) {
        $body.append('<span class="mb-settings-label">Шрифт</span>');
        const $fo = $('<div class="mb-font-list"></div>').appendTo($body);
        const fontList = [...CARD_FONTS,
            ...customFonts().map(f => [`'${f.family}', sans-serif`, f.family])];
        fontList.forEach(([val, label]) => {
            $(`<div class="mb-font-opt ${(card.fontFamily || '') === val ? 'active' : ''}" style="font-family:${val || 'inherit'}">${label}</div>`)
                .on('click', function() {
                    card.fontFamily = val;
                    $card.find('.mb-card-content').css('font-family', val || '');
                    refreshNotePreview();
                    $fo.find('.mb-font-opt').removeClass('active');
                    $(this).addClass('active');
                    save();
                }).appendTo($fo);
        });

        // Notes already have their text size next to the preview, where it can
        // be judged against the board; only the other card types need it here.
        if (card.type !== 'text' && card.type !== 'quote') {
            $body.append('<span class="mb-settings-label">Размер</span>');
            const $sz = $('<div class="mb-size-row"></div>').appendTo($body);
            CARD_SIZES.forEach(([val, label]) => {
                $(`<div class="mb-size-opt ${(card.fontSize || '1em') === val ? 'active' : ''}">${label}</div>`)
                    .on('click', function() {
                        card.fontSize = val;
                        $card.find('.mb-card-content').css('font-size', val);
                        $sz.find('.mb-size-opt').removeClass('active');
                        $(this).addClass('active');
                        save();
                    }).appendTo($sz);
            });
        }

        $body.append('<span class="mb-settings-label">Цвет текста</span>');
        const $tc = $('<div class="mb-textcolor"></div>').appendTo($body);
        const setTextColor = (val) => {
            if (val) { card.textColor = val; rememberColor(val); }
            else delete card.textColor;
            $card.find('.mb-card-content').css('color', val || '');
            refreshNotePreview();
            save(true);
            openStylePanel(card, $card);   // refresh the swatch row
        };
        // "Default" hands the colour back to the frame, which is what most cards want.
        $(`<span class="mb-tc-swatch mb-tc-auto ${card.textColor ? '' : 'active'}" title="По умолчанию"><i class="fa-solid fa-ban"></i></span>`)
            .on('click', () => setTextColor(null)).appendTo($tc);
        const quick = [...new Set([...recentColors(), ...(boards.global?.savedColors || [])])].slice(0, 9);
        quick.forEach(c => {
            $(`<span class="mb-tc-swatch ${card.textColor === c ? 'active' : ''}" style="background:${c}" title="${c}"></span>`)
                .on('click', () => setTextColor(c)).appendTo($tc);
        });
        $(`<span class="mb-tc-swatch mb-tc-more" title="Выбрать цвет"><i class="fa-solid fa-plus"></i></span>`)
            .on('click', async () => {
                const pickedColor = await mbColorPicker('Цвет текста', card.textColor || '#3c2a1a');
                if (pickedColor) setTextColor(pickedColor);
            }).appendTo($tc);

        $body.append('<span class="mb-settings-label">Выравнивание</span>');
        const $al = $('<div class="mb-size-row mb-align-row"></div>').appendTo($body);
        [['left','align-left'],['center','align-center'],['right','align-right']].forEach(([val, icon]) => {
            $(`<div class="mb-size-opt ${(card.align || 'left') === val ? 'active' : ''}"><i class="fa-solid fa-${icon}"></i></div>`)
                .on('click', function() {
                    card.align = val;
                    $card.find('.mb-card-content').css('text-align', val);
                    refreshNotePreview();
                    $al.find('.mb-size-opt').removeClass('active');
                    $(this).addClass('active');
                    save();
                }).appendTo($al);
        });
    }
    togglePanel('#mb-frame-panel', true);
}

function renderCard(card, animate, target) {
    const isSticker = card.type === 'sticker';
    const isCollage = card.type === 'collage';
    const isTree = card.type === 'tree';
    const isImg = card.type === 'image' || isSticker;
    const isQuote = card.type === 'quote';
    const shapeCls = card.shape ? `shape-${card.shape}` : 'shape-default';

    let contentHtml = '';
    if (isTree) {
        // The tree draws its own background and frame, so the card around it is
        // nothing but a position and a size.
        contentHtml = `<div class="mb-tree-wrap">${treeSvg(card)}</div>`;
    } else if (isCollage) {
        contentHtml = collageHtml(card);
    } else if (isImg) {
        // Whichever copy this card's on-screen size actually calls for — usually
        // the preview. The original is pulled in for PNG export / AI regardless.
        const src = bestSrcFor(card);
        contentHtml = `<div class="mb-card-content-wrap"><img src="${src}" draggable="false" decoding="async" style="max-width:100%;display:block;${isSticker ? '' : 'border-radius:4px;'}"></div>`;
    } else {
        // Not editable until tapped. While a note is permanently contenteditable
        // the browser owns pointer events over the text, so pressing there never
        // starts a drag and the note only moves when grabbed by its thin border.
        // The markup is a view: the stored text stays exactly what was typed, and
        // the editor puts that raw text back on screen the moment you tap in.
        contentHtml = `<div class="mb-card-content ${isQuote ? 'quote' : ''}" contenteditable="false">${renderNote(card.content)}</div>`;
    }

    // A pencil, on every kind of card — notes, pictures, trees, stickers. It used
    // to be a wand, which is the same icon as "send the board to the character"
    // in the header: two completely different actions wearing the same face.
    // Everything a card can be changed about lives behind this one button.
    const styleBtn = `<div class="mb-card-act-btn style" title="Редактировать"><i class="fa-solid fa-pencil"></i></div>`;
    const writeBtn = '';
    const editBtn = isSticker ? '' : `<div class="mb-card-act-btn edit" title="Change color"><i class="fa-solid fa-palette"></i></div>`;
    const lockBtn = `<div class="mb-card-act-btn lock" title="Pin / Unpin"><i class="fa-solid fa-thumbtack" style="${card.locked ? 'color:var(--mb-accent)' : ''}"></i></div>`;
    const pinHtml = isSticker ? '' : `<div class="mb-card-pin"></div>`;
    const stripHtml = isSticker ? '' : `<div class="mb-card-color-strip" style="background:${card.color || '#fdf6e3'}"></div>`;

    const $card = $(`<div class="mb-card ${animate ? 'mb-card-enter' : ''} ${isSticker ? 'is-sticker' : ''} ${isCollage ? 'is-collage' : ''} ${isTree ? 'is-tree' : ''} ${card.w ? 'has-size' : ''} ${shapeCls}" data-id="${card.id}"
        style="left:${card.x}px;top:${card.y}px;z-index:${card.z || 1};${card.w ? 'width:'+card.w+'px' : ''}">
        ${stripHtml}
        ${pinHtml}
        <div class="mb-card-actions">
            ${lockBtn}
            ${styleBtn}
            ${editBtn}
            <div class="mb-card-act-btn del" title="Delete"><i class="fa-solid fa-trash"></i></div>
        </div>
        ${contentHtml}
        <div class="mb-card-resize"></div>
    </div>`);

    applyCardTypography($card, card, isImg || isCollage || isTree);
    applyCustomFrameSizing($card, card);
    if (card.locked) $card.addClass('is-locked');
    // A collage caption is text like any other, so it is typed in the panel too.
    // A second tap on a tile still swaps that picture — that is not typing.
    if (isCollage) $card.find('.mb-booth-caption').attr('contenteditable', 'false');
    // Drop the entrance animation the moment it finishes; while the class is on
    // the element the animation owns `transform` and drags cannot paint.
    if (animate) {
        $card.one('animationend', function () { $(this).removeClass('mb-card-enter'); });
        setTimeout(() => $card.removeClass('mb-card-enter'), 600); // in case the event never fires
    }

    // These fire on pointerup, not click: the pointerdown above captures the
    // pointer to this button, so the release is delivered here no matter how the
    // layout moves in between (see the keyboard note there). A `click` would be
    // hit-tested afresh at the release point and could land on nothing.
    $card.find('.del').on('pointerup', function(e) {
        e.stopPropagation();
        if (card.locked) return;
        const cards = getBoard().cards || [];
        const index = cards.indexOf(card);
        // Its threads go with it, and come back with it.
        const links = boardLinks().filter(l => l.a === card.id || l.b === card.id);
        pushUndo({ type: 'card', card, index: index < 0 ? cards.length : index, links });
        getBoard().cards = cards.filter(c => c.id !== card.id);
        pruneLinks();
        $card.remove(); save(); renderInk();
        toastr?.info('Удалено. Стрелка ↺ в панели вернёт', '', { timeOut: 2500 });
    });
    $card.find('.lock').on('pointerup', function(e) {
        e.stopPropagation();
        card.locked = !card.locked;
        $(this).find('i').css('color', card.locked ? 'var(--mb-accent)' : '');
        $card.toggleClass('is-locked', card.locked);
        save();
    });
    $card.find('.edit').on('pointerup', function(e) {
        e.stopPropagation();
        if (card.locked) return;
        card.color = cardColors[(cardColors.indexOf(card.color) + 1) % cardColors.length];
        $card.find('.mb-card-color-strip').css('background', card.color); save();
    });
    $card.find('.style').on('pointerup', function(e) {
        e.stopPropagation();
        if (card.locked) return;
        // A tree is edited as a tree; everything else through the card panel,
        // which now also holds the note's text.
        if (isTree) openTreePanel(card, $card);
        else openStylePanel(card, $card);
    });
    // A note on the board is only ever read, never typed into. Typing happens
    // in the pencil panel, in a plain textarea.
    //
    // This is not only about the icon. A contenteditable living on a draggable,
    // transformed element is a fragile place to type: the phone keyboard resizes
    // the world under the caret, a stray touch moves the card mid-word, and on
    // some setups the keyboard never comes up for it at all. A textarea has none
    // of those problems, and the panel keeps a live preview alongside it so the
    // formatting is still visible while typing.
    bindNoteMarkup($card);

    // Card drag
    $card.on('pointerdown', function(e) {
        // Pinned cards still take part here: being pinned means "don't move me",
        // not "don't talk to me". Selecting one to send it to the character used
        // to require unpinning it first. The move itself is blocked further down.
        if (tool !== 'select') return;
        // a pinch is navigation, not a drag
        if (isPinching || activeTouches > 1 || e.originalEvent?.isPrimary === false) return;
        // A spoiler is a control, not scenery: pressing one must not arm a drag
        // at all. It used to, and on a phone a finger always travels a few
        // pixels — so the tap was read as a drag and the spoiler never opened.
        const spoiler = $(e.target).closest('.mb-spoiler-head, .mb-inline-spoiler')[0];
        if (spoiler) {
            spoiler.setPointerCapture?.(e.pointerId);
            commitOpenEditor();
            e.stopPropagation();
            return;
        }
        // Only an *active* editor blocks dragging — that's when the user wants to
        // select text rather than move the card.
        if ($(e.target).closest('.mb-card-act-btn, .mb-card-resize, [contenteditable="true"]').length) {
            const actBtn = $(e.target).closest('.mb-card-act-btn')[0];
            if (actBtn) {
                // Reaching for one of the card's own buttons while a note is open.
                // Close the editor right here, on pointerdown, so the keyboard is
                // already on its way out — and capture the pointer, so the release
                // still lands on this button even though dismissing the keyboard
                // grows the modal and moves everything under the finger. Without
                // the capture the tap could miss, which is what left the panels
                // half-opened and the tabs stuck where they were.
                actBtn.setPointerCapture?.(e.pointerId);
                commitOpenEditor();
                pokeViewport();
            }
            return;
        }
        commitOpenEditor();
        e.stopPropagation();
        let cx = e.clientX ?? (e.originalEvent?.touches?.[0]?.clientX) ?? 0;
        let cy = e.clientY ?? (e.originalEvent?.touches?.[0]?.clientY) ?? 0;
        // Track the movement as a delta from where the finger went down rather
        // than against a board rect captured at that moment: opening or closing
        // the phone keyboard shifts the viewport mid-drag, and a cached rect
        // would throw the card off by that shift.
        dragCard = { el: $card, card, origX: card.x, origY: card.y, dx: 0, dy: 0, startX: cx, startY: cy };
        // Holding still on a card starts (or joins) a selection. Cancelled the
        // moment the finger travels, so it never fights with dragging.
        clearTimeout(cardHoldTimer);
        cardHoldTimer = setTimeout(() => {
            cardHoldTimer = null;
            if (!dragCard || Math.abs(dragCard.dx) > 4 || Math.abs(dragCard.dy) > 4) return;
            if (!selectMode) setSelectMode(true);
            picked.add(card.id);
            refreshSelectionUI();
            cancelDrag();
            // Android starts its own word selection on the very same hold. It is
            // suppressed by CSS on the card itself, but a stray range can still be
            // left over from whatever was touched before — drop it, or the phone
            // paints selection handles over the board.
            try { window.getSelection()?.removeAllRanges(); } catch (err) {}
            if (navigator.vibrate) navigator.vibrate(15);
        }, 500);
        // A leftover entrance animation would override the drag transform.
        $card.removeClass('mb-card-enter');
        $card.addClass('dragging is-dragging').css('z-index', 100000);
        // Capture on the card itself, not on e.target: e.target is often a child
        // (the <img>, the content div) that can be re-rendered mid-drag, which
        // silently drops the pointer stream and makes the move stutter/stop.
        this.setPointerCapture?.(e.pointerId);
    });

    // Resize
    let resizing = false, rs = {};
    $card.find('.mb-card-resize').on('pointerdown', function(e) {
        if (card.locked) return;
        e.stopPropagation(); resizing = true;
        let cx = e.clientX ?? (e.originalEvent?.touches?.[0]?.clientX) ?? 0;
        rs = { x: cx, w: $card.width() };
        $card.addClass('has-size');
        e.target.setPointerCapture?.(e.pointerId);
        $(e.target).on('pointermove', ev => {
            if (resizing) {
                let curX = ev.clientX ?? (ev.originalEvent?.touches?.[0]?.clientX) ?? rs.x;
                const live = clampCardW(rs.w + (curX - rs.x) / zoom);
                $card.css('width', live);
                // Keep the frame in step with the drag, or the band stays at its
                // old thickness until you let go and the text reflows twice.
                applyCustomFrameSizing($card, card, live);
            }
        });
        $(e.target).on('pointerup pointercancel', function() {
            resizing = false;
            setCardWidth(card, $card, $card.width());
            $(this).off('pointermove pointerup pointercancel');
        });
    });

    if (target) target.appendChild($card[0]);
    else { $('#mb-canvas-inner').append($card); scheduleCull(); }
}

function escHtml(s) { return (s||'').replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;'); }

// Runs a reply through Tavern's own formatter, so *actions*, **emphasis**,
// ~~strikethrough~~, `code`, "speech" and blockquotes come out looking exactly
// as they do in the chat — asterisks and all other markers included.
function formatRich(text, name) {
    const ctx = typeof getContext === 'function' ? getContext() : null;
    if (typeof ctx?.messageFormatting === 'function') {
        try { return ctx.messageFormatting(text || '', name || '', false, false, null); }
        catch (e) { console.warn(LOG, 'messageFormatting failed', e); }
    }
    // Tavern not reachable: a small subset by hand, still escaped first.
    let s = escHtml(text || '');
    s = s.replace(/\*\*\*([^*]+)\*\*\*/g, '<strong><em>$1</em></strong>')
         .replace(/\*\*([^*]+)\*\*/g, '<strong>$1</strong>')
         .replace(/\*([^*]+)\*/g, '<em>$1</em>')
         .replace(/~~([^~]+)~~/g, '<del>$1</del>')
         .replace(/`([^`]+)`/g, '<code>$1</code>')
         .replace(/^&gt;\s?(.*)$/gm, '<blockquote>$1</blockquote>');
    return s.replace(/\n/g, '<br>');
}

// ===== CONNECTORS (the crazy wall) =====
// A link stores two card ids and nothing about geometry: where the thread runs is
// worked out from where the cards are right now, so it follows them around
// forever — including while one is still under the finger.
//
//   { id, a, b, c: colour, w: width, s: style, h: arrowheads, t: label }
//
// They are painted on the ink layer, under the cards, so a thread never covers a
// face. Both ends are clipped to the card's border, so the line looks like it is
// pinned to the edge rather than sprouting from behind the middle.
const LINK_STYLES = [
    ['curve', 'Дуга', 'bezier-curve'],
    ['straight', 'Прямая', 'minus'],
    ['dashed', 'Пунктир', 'ellipsis'],
    ['thread', 'Нитка', 'link'],
];
const LINK_HEADS = [[0, 'Без стрелок', 'minus'], [1, 'В одну сторону', 'arrow-right'], [2, 'В обе стороны', 'arrows-left-right']];
const LINK_HIT = 14;       // screen px around the line that count as a tap on it

function boardLinks() {
    const b = getBoard();
    if (!Array.isArray(b.links)) b.links = [];
    return b.links;
}
// A link whose card is gone would draw to nowhere; deleting a card takes its
// threads with it.
function pruneLinks() {
    const b = getBoard();
    if (!Array.isArray(b.links) || !b.links.length) return;
    const ids = new Set((b.cards || []).map(c => c.id));
    const kept = b.links.filter(l => ids.has(l.a) && ids.has(l.b));
    if (kept.length !== b.links.length) b.links = kept;
}

function themeColor(name, fallback) {
    const el = document.getElementById('mb-canvas-area');
    if (!el) return fallback;
    return getComputedStyle(el).getPropertyValue(name).trim() || fallback;
}

// Card sizes come from the DOM (a note's height depends on its text), positions
// from the card data. Only the sizes need measuring, and only when something
// structural changed — a pan must never force a layout.
function rebuildLinkGeom() {
    linkGeom.clear();
    document.querySelectorAll('#mb-canvas-inner .mb-card').forEach(el => {
        linkGeom.set(el.dataset.id, { w: el.offsetWidth, h: el.offsetHeight });
    });
    linkGeomDirty = false;
}
function cardBox(card) {
    if (linkGeomDirty) rebuildLinkGeom();
    const g = linkGeom.get(card.id) || {};
    const w = g.w || card.w || 200, h = g.h || 120;
    let x = card.x, y = card.y;
    if (dragCard && dragCard.card === card && !card.locked) { x += dragCard.dx; y += dragCard.dy; }
    return { x, y, w, h, cx: x + w / 2, cy: y + h / 2 };
}

// Where a ray from the box centre toward (tx,ty) leaves the box.
function rectEdge(box, tx, ty) {
    const dx = tx - box.cx, dy = ty - box.cy;
    if (!dx && !dy) return { x: box.cx, y: box.cy };
    const hw = box.w / 2 + 3, hh = box.h / 2 + 3;
    const t = Math.min(dx ? hw / Math.abs(dx) : Infinity, dy ? hh / Math.abs(dy) : Infinity);
    return { x: box.cx + dx * t, y: box.cy + dy * t };
}
// from / ctrl / to, in board coordinates. A "thread" sags downward like real
// string; the other curved style bows sideways, the way a connector does in Miro.
function linkCurve(ba, bb, style) {
    const from = rectEdge(ba, bb.cx, bb.cy);
    const to = rectEdge(bb, ba.cx, ba.cy);
    const dx = to.x - from.x, dy = to.y - from.y;
    const len = Math.hypot(dx, dy) || 1;
    const mx = (from.x + to.x) / 2, my = (from.y + to.y) / 2;
    if (style === 'thread') return { from, to, ctrl: { x: mx, y: my + Math.min(160, len * 0.16) } };
    if (style === 'straight' || style === 'dashed') return { from, to, ctrl: { x: mx, y: my } };
    const k = Math.min(120, len * 0.14);
    return { from, to, ctrl: { x: mx - (dy / len) * k, y: my + (dx / len) * k } };
}
function quadAt(g, t) {
    const u = 1 - t;
    return {
        x: u * u * g.from.x + 2 * u * t * g.ctrl.x + t * t * g.to.x,
        y: u * u * g.from.y + 2 * u * t * g.ctrl.y + t * t * g.to.y,
    };
}

// `project` maps board coordinates to whatever surface is being painted (screen
// while the board is open, output pixels during an export); `scale` is how many
// of those units one board unit is worth, so line widths and text stay in step.
function paintLink(ctx, l, g, project, scale) {
    const p0 = project(g.from), pc = project(g.ctrl), p1 = project(g.to);
    const w = Math.max(1, (l.w || 3) * scale);
    const col = l.c || themeColor('--mb-pin-color', '#c0392b');
    ctx.save();
    ctx.strokeStyle = col; ctx.fillStyle = col;
    ctx.lineWidth = w; ctx.lineCap = 'round';
    if (l.s === 'dashed') ctx.setLineDash([w * 3, w * 2.4]);
    ctx.beginPath();
    ctx.moveTo(p0.x, p0.y);
    ctx.quadraticCurveTo(pc.x, pc.y, p1.x, p1.y);
    ctx.stroke();
    ctx.setLineDash([]);

    // A pin head at each end sells the "string between two pins" look and hides
    // the seam where the line meets the card.
    const heads = l.h === undefined ? 1 : l.h;
    [p0, p1].forEach(p => {
        ctx.beginPath(); ctx.arc(p.x, p.y, Math.max(2, w * 0.9), 0, Math.PI * 2); ctx.fill();
    });
    const head = (tip, from) => {
        const a = Math.atan2(tip.y - from.y, tip.x - from.x);
        const hl = 8 * scale + w * 2.2;
        ctx.beginPath();
        ctx.moveTo(tip.x, tip.y);
        ctx.lineTo(tip.x - hl * Math.cos(a - 0.42), tip.y - hl * Math.sin(a - 0.42));
        ctx.lineTo(tip.x - hl * Math.cos(a + 0.42), tip.y - hl * Math.sin(a + 0.42));
        ctx.closePath(); ctx.fill();
    };
    if (heads >= 1) head(p1, pc);
    if (heads >= 2) head(p0, pc);

    if (l.t) {
        const mid = project(quadAt(g, 0.5));
        const fs = Math.max(9, 13 * scale);
        ctx.font = `600 ${fs}px 'Inter', 'Segoe UI', sans-serif`;
        ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
        const tw = ctx.measureText(l.t).width;
        const padX = fs * 0.5, hh = fs * 0.85;
        ctx.fillStyle = themeColor('--mb-card-bg', '#fdf6e3');
        roundRect(ctx, mid.x - tw / 2 - padX, mid.y - hh, tw + padX * 2, hh * 2, fs * 0.45);
        ctx.fill();
        ctx.strokeStyle = col; ctx.lineWidth = Math.max(1, scale);
        ctx.stroke();
        ctx.fillStyle = themeColor('--mb-card-text', '#3c2a1a');
        ctx.fillText(l.t, mid.x, mid.y);
    }
    ctx.restore();
}
function roundRect(ctx, x, y, w, h, r) {
    const rr = Math.min(r, w / 2, h / 2);
    ctx.beginPath();
    ctx.moveTo(x + rr, y);
    ctx.arcTo(x + w, y, x + w, y + h, rr);
    ctx.arcTo(x + w, y + h, x, y + h, rr);
    ctx.arcTo(x, y + h, x, y, rr);
    ctx.arcTo(x, y, x + w, y, rr);
    ctx.closePath();
}

function renderLinks(ctx, project, scale) {
    const links = boardLinks();
    if (!links.length && !linkDraft) return;
    const cards = new Map((getBoard().cards || []).map(c => [c.id, c]));
    for (const l of links) {
        const A = cards.get(l.a), B = cards.get(l.b);
        if (!A || !B) continue;
        paintLink(ctx, l, linkCurve(cardBox(A), cardBox(B), l.s), project, scale);
    }
    // The thread being pulled out right now, before it has anywhere to land.
    if (linkDraft) {
        const A = cards.get(linkDraft.a);
        if (A) {
            const ba = cardBox(A);
            const from = rectEdge(ba, linkDraft.to.x, linkDraft.to.y);
            const p0 = project(from), p1 = project(linkDraft.to);
            ctx.save();
            ctx.strokeStyle = themeColor('--mb-accent', '#d4a574');
            ctx.lineWidth = Math.max(1, 2.5 * scale);
            ctx.setLineDash([8 * scale, 6 * scale]);
            ctx.beginPath(); ctx.moveTo(p0.x, p0.y); ctx.lineTo(p1.x, p1.y); ctx.stroke();
            ctx.setLineDash([]);
            ctx.fillStyle = ctx.strokeStyle;
            ctx.beginPath(); ctx.arc(p1.x, p1.y, 4 * scale, 0, Math.PI * 2); ctx.fill();
            ctx.restore();
        }
    }
}

// Which thread, if any, is under this screen point.
function linkAt(clientX, clientY) {
    const area = document.getElementById('mb-canvas-area');
    if (!area) return null;
    const r = area.getBoundingClientRect();
    const px = clientX - r.left, py = clientY - r.top;
    const cards = new Map((getBoard().cards || []).map(c => [c.id, c]));
    const links = boardLinks();
    for (let i = links.length - 1; i >= 0; i--) {
        const l = links[i];
        const A = cards.get(l.a), B = cards.get(l.b);
        if (!A || !B) continue;
        const g = linkCurve(cardBox(A), cardBox(B), l.s);
        for (let k = 0; k <= 24; k++) {
            const s = toScreen(quadAt(g, k / 24));
            if (Math.hypot(s.x - px, s.y - py) <= LINK_HIT) return l;
        }
    }
    return null;
}

// ---- link tool gestures
function beginLink(e, cardEl) {
    innerRect = document.getElementById('mb-canvas-inner').getBoundingClientRect();
    linkDraft = { a: cardEl.dataset.id, to: canvasPos(e) };
    document.getElementById('mb-canvas-area').setPointerCapture?.(e.pointerId);
    $(`.mb-card[data-id="${linkDraft.a}"]`).addClass('mb-link-source');
}
function finishLink(e) {
    const draft = linkDraft;
    linkDraft = null;
    innerRect = null;
    $('.mb-card').removeClass('mb-link-source');
    if (!draft) return;
    // elementFromPoint, not e.target: the pointer is captured by the board, so
    // e.target is the board no matter what the finger is actually over.
    const el = document.elementFromPoint(e.clientX, e.clientY)?.closest?.('.mb-card');
    const b = el?.dataset.id;
    renderInk();
    if (!b || b === draft.a) return;
    const links = boardLinks();
    // Tying the same pair twice just edits the thread that is already there.
    const twin = links.find(l => (l.a === draft.a && l.b === b) || (l.a === b && l.b === draft.a));
    if (twin) { toastr?.info('Эти карточки уже связаны'); openLinkMenu(twin, e.clientX, e.clientY); return; }
    const link = {
        id: genId(), a: draft.a, b,
        c: lastLinkColor || themeColor('--mb-pin-color', '#c0392b'),
        w: 3, s: lastLinkStyle, h: 1, t: '',
    };
    links.push(link);
    save();
    renderInk();
    if (navigator.vibrate) navigator.vibrate(12);
    openLinkMenu(link, e.clientX, e.clientY);
}
// Abandons a half-drawn thread — a second finger, a tool change, closing the board.
function cancelLink() {
    if (!linkDraft) return;
    linkDraft = null;
    innerRect = null;
    $('.mb-card').removeClass('mb-link-source');
    renderInk();
}
// New threads inherit the last look chosen, so tying a dozen of them does not
// mean re-picking the colour a dozen times.
let lastLinkColor = null, lastLinkStyle = 'curve';

function placePanelAt($p, x, y) {
    $p.addClass('open');
    const vh = visibleHeight();
    $p.css('max-height', (vh - 16) + 'px');
    const w = $p.outerWidth(), h = Math.min($p.outerHeight(), vh - 16);
    $p.css({
        left: Math.max(8, Math.min(x - w / 2, window.innerWidth - w - 8)),
        top: Math.max(8, Math.min(y + 12, vh - h - 8)),
    });
}

function closeLinkMenu() {
    $('#mb-link-menu').removeClass('open');
    activeLink = null;
}
function openLinkMenu(link, x, y) {
    markHold();
    activeLink = link;
    const $p = $('#mb-link-menu').empty();
    $p.append('<div class="mb-brush-title">Подпись</div>');
    const $t = $(`<input type="text" class="mb-settings-input mb-link-label" placeholder="например «сестра» или «врёт ему»">`)
        .val(link.t || '');
    $t.on('input', function() { link.t = this.value; renderInk(); save(); })
      .on('click pointerdown keydown', e => e.stopPropagation());
    $p.append($t);

    $p.append('<div class="mb-brush-title">Вид нити</div>');
    const $sg = $('<div class="mb-brush-grid"></div>').appendTo($p);
    LINK_STYLES.forEach(([val, label, icon]) => {
        $(`<div class="mb-brush-opt ${(link.s || 'curve') === val ? 'active' : ''}">
             <i class="fa-solid fa-${icon}"></i><span>${label}</span></div>`)
            .on('click', e => {
                e.stopPropagation();
                link.s = val; lastLinkStyle = val;
                $sg.find('.mb-brush-opt').removeClass('active');
                $(e.currentTarget).addClass('active');
                renderInk(); save();
            }).appendTo($sg);
    });

    $p.append('<div class="mb-brush-title">Стрелки</div>');
    const $hg = $('<div class="mb-brush-grid mb-grid-3"></div>').appendTo($p);
    LINK_HEADS.forEach(([val, label, icon]) => {
        $(`<div class="mb-brush-opt ${(link.h === undefined ? 1 : link.h) === val ? 'active' : ''}" title="${label}">
             <i class="fa-solid fa-${icon}"></i></div>`)
            .on('click', e => {
                e.stopPropagation();
                link.h = val;
                $hg.find('.mb-brush-opt').removeClass('active');
                $(e.currentTarget).addClass('active');
                renderInk(); save();
            }).appendTo($hg);
    });

    $p.append('<div class="mb-brush-title">Цвет и толщина</div>');
    const $cr = $('<div class="mb-link-colors"></div>').appendTo($p);
    const palette = [themeColor('--mb-pin-color', '#c0392b'), ...BASE_COLORS, ...savedColors()];
    [...new Set(palette)].forEach(c => {
        $(`<span class="mb-color-dot ${(link.c || '').toLowerCase() === c.toLowerCase() ? 'active' : ''}" style="background:${c}"></span>`)
            .on('click', e => {
                e.stopPropagation();
                link.c = c; lastLinkColor = c;
                $cr.find('.mb-color-dot').removeClass('active');
                $(e.currentTarget).addClass('active');
                renderInk(); save();
            }).appendTo($cr);
    });
    const $wr = $('<div class="mb-brush-size"></div>').appendTo($p);
    const $ws = $(`<input type="range" min="1" max="12" value="${link.w || 3}">`).appendTo($wr);
    const $wv = $(`<b>${link.w || 3}</b>`).appendTo($wr);
    $ws.on('input', function() { link.w = parseInt(this.value, 10); $wv.text(link.w); renderInk(); save(); })
       .on('click pointerdown', e => e.stopPropagation());

    $('<button class="mb-settings-btn danger" style="margin-top:10px"><i class="fa-solid fa-scissors"></i> Перерезать нить</button>')
        .on('click', e => {
            e.stopPropagation();
            const links = boardLinks();
            const i = links.indexOf(link);
            if (i >= 0) links.splice(i, 1);
            activeLink = null;
            $p.removeClass('open');
            renderInk(); save();
        }).appendTo($p);

    placePanelAt($p, x, y);
}

// ===== TIMELINE =====
// A horizontal axis drawn on the board background with cards that stick to it.
// It belongs to the board, not to the device: a chronology is content.
const TL_PULL = 130;       // board px around the axis where a card is caught
const TL_GAP = 18;         // how far off the line a caught card sits
const TL_TICK_PULL = 70;   // how close to a tick the card's centre has to be

function boardTimeline() {
    const b = getBoard();
    if (!b.timeline || typeof b.timeline !== 'object') {
        b.timeline = { on: false, y: BOARD_SIZE / 2, x0: 700, x1: 3300, div: 8, labels: [], title: 'Хронология' };
    }
    const t = b.timeline;
    if (!Array.isArray(t.labels)) t.labels = [];
    if (!(t.div > 0)) t.div = 8;
    return t;
}
function tickX(tl, i) { return tl.x0 + (tl.x1 - tl.x0) * (i / tl.div); }
function nearestTick(tl, x) {
    let best = null, bestD = TL_TICK_PULL;
    for (let i = 0; i <= tl.div; i++) {
        const d = Math.abs(tickX(tl, i) - x);
        if (d < bestD) { bestD = d; best = tickX(tl, i); }
    }
    return best;
}

function renderTimeline(ctx, project, scale) {
    const b = getBoard();
    const tl = b.timeline;
    if (!tl || !tl.on) return;
    const col = themeColor('--mb-accent', '#d4a574');
    const a = project({ x: tl.x0, y: tl.y }), z = project({ x: tl.x1, y: tl.y });
    ctx.save();
    ctx.strokeStyle = col; ctx.fillStyle = col;
    ctx.lineWidth = Math.max(1, 2.5 * scale);
    ctx.lineCap = 'round';
    ctx.beginPath(); ctx.moveTo(a.x, a.y); ctx.lineTo(z.x, z.y); ctx.stroke();
    // arrow at the far end — time runs left to right
    const hl = 14 * scale;
    ctx.beginPath();
    ctx.moveTo(z.x + hl * 0.7, z.y);
    ctx.lineTo(z.x - hl * 0.4, z.y - hl * 0.45);
    ctx.lineTo(z.x - hl * 0.4, z.y + hl * 0.45);
    ctx.closePath(); ctx.fill();

    const fs = Math.max(9, 17 * scale);
    ctx.font = `600 ${fs}px 'Caveat', cursive`;
    ctx.textAlign = 'center'; ctx.textBaseline = 'top';
    for (let i = 0; i <= tl.div; i++) {
        const p = project({ x: tickX(tl, i), y: tl.y });
        const t = 9 * scale;
        ctx.beginPath(); ctx.moveTo(p.x, p.y - t); ctx.lineTo(p.x, p.y + t); ctx.stroke();
        const label = (tl.labels[i] || '').trim();
        if (label) ctx.fillText(label, p.x, p.y + t + 4 * scale);
    }
    if (tl.title) {
        ctx.textAlign = 'left'; ctx.textBaseline = 'bottom';
        ctx.font = `600 ${Math.max(11, 22 * scale)}px 'Caveat', cursive`;
        ctx.fillText(tl.title, a.x, a.y - 16 * scale);
    }
    ctx.restore();
}

// Is this screen point on the axis? The axis is not an element, so it needs its
// own hit test to be draggable like everything else on the board.
let tlDrag = null;
function timelineHit(clientX, clientY) {
    const tl = getBoard().timeline;
    if (!tl || !tl.on) return false;
    const area = document.getElementById('mb-canvas-area');
    if (!area) return false;
    const r = area.getBoundingClientRect();
    const px = clientX - r.left, py = clientY - r.top;
    const a = toScreen({ x: tl.x0, y: tl.y }), z = toScreen({ x: tl.x1, y: tl.y });
    if (px < Math.min(a.x, z.x) - 24 || px > Math.max(a.x, z.x) + 24) return false;
    return Math.abs(py - a.y) <= 16;
}

// Where a dragged card actually wants to be. The timeline wins over the grid: if
// a card is being offered to the axis, lining it up with graph paper instead is
// not what anyone meant.
function applyMagnets(d) {
    const box = cardBox(d.card);
    let x = box.x, y = box.y;
    let lockX = false, lockY = false;
    const tl = getBoard().timeline;
    if (tl && tl.on) {
        const cy = y + box.h / 2;
        if (Math.abs(cy - tl.y) < TL_PULL) {
            y = cy < tl.y ? tl.y - box.h - TL_GAP : tl.y + TL_GAP;
            lockY = true;
            const t = nearestTick(tl, x + box.w / 2);
            if (t !== null) { x = t - box.w / 2; lockX = true; }
        }
    }
    if (gridSnap) {
        if (!lockX) x = snapValue(x);
        if (!lockY) y = snapValue(y);
    }
    d.dx = x - d.origX;
    d.dy = y - d.origY;
}

function openTimelinePanel() {
    markHold();
    const tl = boardTimeline();
    const $b = $('#mb-timeline-body').empty();
    const redraw = () => { renderInk(); save(); };

    const $sw = $(`<label class="mb-switch-row"><span class="mb-switch-text"><b>Показывать ось</b><em>Карточки будут к ней примагничиваться</em></span>
        <input type="checkbox" class="mb-switch-input" ${tl.on ? 'checked' : ''}>
        <span class="mb-switch"><span class="mb-switch-knob"></span></span></label>`);
    $sw.find('input').on('change', function() {
        tl.on = this.checked;
        $('#mb-btn-timeline').toggleClass('active', tl.on);
        redraw();
    });
    $b.append($sw);

    $b.append('<span class="mb-settings-label">Заголовок</span>');
    $(`<input type="text" class="mb-settings-input">`).val(tl.title || '')
        .on('input', function() { tl.title = this.value; redraw(); })
        .appendTo($b);

    $b.append('<span class="mb-settings-label">Делений</span>');
    const $dr = $('<div class="mb-brush-size"></div>').appendTo($b);
    const $ds = $(`<input type="range" min="2" max="24" value="${tl.div}">`).appendTo($dr);
    const $dv = $(`<b>${tl.div}</b>`).appendTo($dr);
    $ds.on('input', function() { tl.div = parseInt(this.value, 10); $dv.text(tl.div); redraw(); });

    $b.append('<span class="mb-settings-label">Подписи делений</span>');
    $(`<textarea class="mb-settings-input" rows="6" placeholder="Каждая подпись с новой строки:&#10;Пролог&#10;Первая встреча&#10;Ссора"></textarea>`)
        .val((tl.labels || []).join('\n'))
        .on('input', function() { tl.labels = this.value.split('\n'); redraw(); })
        .appendTo($b);
    $b.append('<div class="mb-select-hint">Первая строка — самое левое деление. Пустые строки оставляют деление без подписи.</div>');

    $b.append('<span class="mb-settings-label">Положение оси</span>');
    $('<button class="mb-settings-btn secondary"><i class="fa-solid fa-crosshairs"></i> Поставить по центру экрана</button>')
        .on('click', () => {
            const c = viewportCenter();
            tl.y = Math.round(c.y);
            const area = document.getElementById('mb-canvas-area');
            const halfW = ((area?.clientWidth || 900) / zoom) * 0.45;
            tl.x0 = Math.round(c.x - halfW); tl.x1 = Math.round(c.x + halfW);
            tl.on = true;
            $('#mb-btn-timeline').addClass('active');
            openTimelinePanel();
            redraw();
        }).appendTo($b);
    $('<button class="mb-settings-btn secondary"><i class="fa-solid fa-left-right"></i> Растянуть на всю ширину доски</button>')
        .on('click', () => { tl.x0 = 300; tl.x1 = BOARD_SIZE - 300; redraw(); }).appendTo($b);
    $b.append('<div class="mb-select-hint">Ось можно двигать и прямо на доске: возьмите её за линию инструментом «стрелка».</div>');

    $('<button class="mb-settings-btn secondary" style="margin-top:14px"><i class="fa-solid fa-wand-magic-sparkles"></i> Разложить карточки по оси</button>')
        .on('click', () => spreadCardsOnTimeline()).appendTo($b);
    $b.append('<div class="mb-select-hint">Расставит карточки этой доски по делениям в том порядке, в каком они добавлялись.</div>');

    togglePanel('#mb-timeline-panel', true);
}

// Lays the board's cards out along the axis in the order they were created —
// a starting point you then drag into the right order.
function spreadCardsOnTimeline() {
    const tl = boardTimeline();
    tl.on = true;
    const cards = [...(getBoard().cards || [])]
        .filter(c => !c.locked)
        .sort((a, b) => (a.created || 0) - (b.created || 0));
    if (!cards.length) { toastr?.info('На доске пока нечего раскладывать'); return; }
    if (linkGeomDirty) rebuildLinkGeom();
    cards.forEach((c, i) => {
        const g = linkGeom.get(c.id) || {};
        const w = g.w || c.w || 200, h = g.h || 120;
        const x = tickX(tl, Math.min(tl.div, i % (tl.div + 1)));
        const above = Math.floor(i / (tl.div + 1)) % 2 === 0;
        c.x = Math.round(x - w / 2);
        c.y = Math.round(above ? tl.y - h - TL_GAP : tl.y + TL_GAP);
        const el = document.querySelector(`.mb-card[data-id="${c.id}"]`);
        if (el) { el.style.left = c.x + 'px'; el.style.top = c.y + 'px'; }
    });
    $('#mb-btn-timeline').addClass('active');
    save(true); renderInk(); scheduleCull();
    toastr?.success('Карточки расставлены по ленте');
}

// ===== GRID =====
// The lines live in a div inside the scaled board, so they pan and zoom with
// everything else for free and cost nothing to redraw. Snapping is deliberately
// a separate switch from the lines: plenty of people want tidy positions without
// graph paper under their photos.
const GRID_SIZES = [20, 40, 60, 100];

function applyGridLayer() {
    const el = document.getElementById('mb-grid-layer');
    if (!el) return;
    el.classList.toggle('on', !!gridShow);
    el.style.backgroundSize = `${gridSize}px ${gridSize}px, ${gridSize}px ${gridSize}px, ${gridSize * 5}px ${gridSize * 5}px, ${gridSize * 5}px ${gridSize * 5}px`;
    $('#mb-btn-grid').toggleClass('active', gridShow || gridSnap);
}
function saveGridPrefs() {
    localStorage.setItem('mb_grid_show', gridShow ? '1' : '0');
    localStorage.setItem('mb_grid_snap', gridSnap ? '1' : '0');
    localStorage.setItem('mb_grid_size', String(gridSize));
}
// The toolbar button is the blunt version: everything on, or everything off.
// The long-press panel is where the two halves are separated.
function toggleGrid() {
    const on = !(gridShow || gridSnap);
    gridShow = on; gridSnap = on;
    saveGridPrefs(); applyGridLayer();
    toastr?.info(on ? 'Сетка и привязка включены' : 'Сетка выключена', '', { timeOut: 1200 });
}
function snapValue(v) { return Math.round(v / gridSize) * gridSize; }

function openGridPicker() {
    markHold();
    const $p = $('#mb-grid-picker').empty();
    $p.append('<div class="mb-brush-title">Сетка</div>');
    const $rows = $('<div></div>').appendTo($p);
    const row = (label, get, set) => {
        const $r = $(`<div class="mb-mini-switch"><span>${label}</span>
            <span class="mb-switch ${get() ? 'on' : ''}"><span class="mb-switch-knob"></span></span></div>`);
        $r.on('click', e => {
            e.stopPropagation();
            set(!get());
            $r.find('.mb-switch').toggleClass('on', get());
            saveGridPrefs(); applyGridLayer();
        });
        $rows.append($r);
    };
    row('Показывать линии', () => gridShow, v => { gridShow = v; });
    row('Привязывать карточки', () => gridSnap, v => { gridSnap = v; });

    $p.append('<div class="mb-brush-title">Шаг</div>');
    const $g = $('<div class="mb-brush-grid"></div>').appendTo($p);
    GRID_SIZES.forEach(s => {
        $(`<div class="mb-brush-opt ${s === gridSize ? 'active' : ''}"><b>${s}</b><span>px</span></div>`)
            .on('click', e => {
                e.stopPropagation();
                gridSize = s;
                $g.find('.mb-brush-opt').removeClass('active');
                $(e.currentTarget).addClass('active');
                saveGridPrefs(); applyGridLayer();
            }).appendTo($g);
    });
    $p.append('<div class="mb-select-hint" style="margin:8px 0 0">Привязка срабатывает в момент, когда вы отпускаете карточку, и никогда не двигает уже разложенное само по себе.</div>');
    anchorPanel($p, document.getElementById('mb-btn-grid'));
}

// How much of the screen there actually is. On a phone `innerHeight` counts the
// space behind the browser's own bars, so a panel sized against it hangs off
// both ends — which is exactly what the reply-style menu did.
function visibleHeight() {
    const vv = window.visualViewport?.height;
    return Math.min(window.innerHeight || Infinity, vv || Infinity) || 600;
}

// Places one of the small pop-over panels under the button that opened it,
// keeping it inside the window. Every long-press menu wants exactly this.
function anchorPanel($p, btn) {
    if (!btn) return;
    const r = btn.getBoundingClientRect();
    $p.addClass('open');
    const vh = visibleHeight();
    // Measure only after the cap is in place, or a tall panel reports a height
    // it will never be allowed to have.
    $p.css('max-height', (vh - 16) + 'px');
    const w = $p.outerWidth(), h = Math.min($p.outerHeight(), vh - 16);
    $p.css({
        left: Math.max(8, Math.min(r.left, window.innerWidth - w - 8)),
        top: Math.max(8, Math.min(r.bottom + 6, vh - h - 8)),
    });
}

// ===== RELATIONSHIP TREES =====
// A tree is one card holding a small graph — people and how they are tied
// together — drawn as SVG. Drawing it rather than asking the user to arrange
// boxes by hand is the whole point: the layout is derived from the links, so
// adding a person never means re-tidying the picture.
//
//   card.tree = { title, layout, skin, nodes: [{id,name,role,group,note,color}],
//                 edges: [{a,b,kind,label}], center }
// Roomier than looks strictly necessary: the gaps are where the connecting lines
// and their labels have to live, and a tight layout is what forced labels on top
// of names in the first place.
const NODE_W = 156, NODE_H = 58, GAP_X = 40, GAP_Y = 112;

// ===== FACES ON THE TREE =====
// Three ways to show a person, and every measurement downstream comes from here
// rather than from the constants above, because a portrait is a different shape
// from a name in a box.
const TREE_PHOTO_MODES = [
    ['off', 'Без фото', 'font'],
    ['chip', 'Аватарка сбоку', 'id-badge'],
    ['portrait', 'Портреты', 'image'],
];
const TREE_PHOTO_SHAPES = [
    ['circle', 'Круг'],
    ['rounded', 'Скруглённый'],
    ['square', 'Квадрат'],
];
const AVATAR_DIM = 128;      // what gets stored per face

function treePhoto(t) {
    const p = t.photo || {};
    return {
        mode: TREE_PHOTO_MODES.some(m => m[0] === p.mode) ? p.mode : 'off',
        shape: TREE_PHOTO_SHAPES.some(s => s[0] === p.shape) ? p.shape : 'circle',
        size: Math.max(0.7, Math.min(1.8, p.size || 1)),
    };
}
// The size of one person on the picture. Portraits are tall and narrow — a face
// with a name under it — so the whole layout has to be told, not assumed.
function nodeSize(t) {
    const p = treePhoto(t);
    if (p.mode === 'portrait') {
        const av = Math.round(84 * p.size);
        return { w: Math.round(Math.max(104, av + 26)), h: av + 44, av, mode: p.mode, shape: p.shape };
    }
    if (p.mode === 'chip') {
        const av = Math.round(40 * p.size);
        return { w: Math.round(NODE_W + av * 0.55), h: Math.max(NODE_H, av + 16), av, mode: p.mode, shape: p.shape };
    }
    return { w: NODE_W, h: NODE_H, av: 0, mode: 'off', shape: p.shape };
}
// Rounding for the chosen shape, given the box it goes in.
function avatarRadius(shape, size) {
    if (shape === 'circle') return size / 2;
    if (shape === 'square') return 0;
    return Math.round(size * 0.24);
}

const TREE_LAYOUTS = [
    ['hierarchy', 'Родословная', 'sitemap'],
    ['radial', 'Солнце', 'sun'],
    ['web', 'Паутина', 'circle-nodes'],
    ['tiers', 'Ярусы', 'layer-group'],
];
const TREE_SKINS = [
    ['parchment', 'Пергамент'],
    ['noir', 'Нуар'],
    ['neon', 'Неон'],
    ['storybook', 'Сказка'],
    ['blueprint', 'Чертёж'],
    ['custom', 'Своё'],
];
// Every colour a skin controls, in the order they are offered for editing.
const TREE_CUSTOM_FIELDS = [
    ['bg', 'Фон сверху'], ['bg2', 'Фон снизу'], ['node', 'Карточка'], ['stroke', 'Обводка'],
    ['text', 'Имена'], ['sub', 'Подписи'], ['line', 'Линии'], ['title', 'Заголовок'],
];
const TREE_TITLE_FONTS = [
    ["'Caveat', cursive", 'Рукописный'],
    ["'Inter', 'Segoe UI', sans-serif", 'Строгий'],
    ["Georgia, 'Noto Serif', serif", 'С засечками'],
    ["'Courier New', monospace", 'Машинка'],
    ["'Comic Sans MS', 'Segoe Print', cursive", 'Комиксный'],
];
// Every skin sets the same handful of colours, so a new one is five lines and
// nothing else has to know about it.
const TREE_SKIN_CSS = {
    parchment: { bg:'#f3e3c0', bg2:'#e6d09a', node:'#fffaf0', stroke:'#a9834a', text:'#3b2a17',
                 sub:'#8a6a3f', line:'#9c7743', title:'#5a3f22', titleFont:"'Caveat', cursive", grain:0.05 },
    noir:      { bg:'#17181c', bg2:'#101115', node:'#24262d', stroke:'#4a4e59', text:'#eceef3',
                 sub:'#9aa0ad', line:'#6b7280', title:'#e7c67a', titleFont:"'Caveat', cursive", grain:0 },
    neon:      { bg:'#0e0a1e', bg2:'#150d2c', node:'#1d1638', stroke:'#7b4dff', text:'#f2ecff',
                 sub:'#b9a6ff', line:'#a06bff', title:'#5ef2d6', titleFont:"'Inter', sans-serif", grain:0 },
    storybook: { bg:'#fdf3f6', bg2:'#f7e2ea', node:'#ffffff', stroke:'#d98cae', text:'#4a2a38',
                 sub:'#a06e83', line:'#d98cae', title:'#b04d78', titleFont:"'Caveat', cursive", grain:0 },
    blueprint: { bg:'#0f2b45', bg2:'#0b2138', node:'#12395c', stroke:'#7fc4ff', text:'#e6f3ff',
                 sub:'#9fc9e8', line:'#7fc4ff', title:'#cfe9ff', titleFont:"'Courier New', monospace", grain:0 },
};
// The starting point for "Своё" — the parchment palette, so the first thing you
// see when you switch to it is a tree, not a blank rectangle.
const TREE_CUSTOM_DEFAULT = { ...TREE_SKIN_CSS.parchment, titleFont: "'Caveat', cursive" };
// A tree's own palette wins; a tree with no palette of its own borrows the one
// you last built, so a second custom tree starts where the first left off.
function treeSkinOf(t) {
    if (t.skin !== 'custom') return TREE_SKIN_CSS[t.skin] || TREE_SKIN_CSS.parchment;
    return { ...TREE_CUSTOM_DEFAULT, ...(boards.global?.treeCustom || {}), ...(t.custom || {}) };
}
const TREE_EDGE_KINDS = {
    family:  ['Родство', '#8a6a3f', null],
    romance: ['Любовь', '#d9436f', null],
    friend:  ['Дружба', '#3f9a63', null],
    ally:    ['Союз', '#3f7ad9', [7, 5]],
    enemy:   ['Вражда', '#c0392b', [8, 6]],
    rival:   ['Соперничество', '#d97b1f', [8, 6]],
    other:   ['Связь', '#8a8a8a', [3, 4]],
};
// [key, button label, what it asks the model for, what the busy overlay says]
const TREE_PRESETS = [
    ['family', 'Семейное древо', 'sitemap',
     'Build a FAMILY tree: blood relatives, marriages, adoptions. Use kind "family" for parent→child links (a is the elder, b is the younger) and kind "romance" for spouses and partners.',
     'Строю семейное древо…'],
    ['relations', 'Дерево отношений', 'circle-nodes',
     'Map how everyone in this story relates to everyone else: who trusts whom, who is in love, who cannot stand whom. Use the full range of link kinds.',
     'Разбираю, кто кому кто…'],
    ['factions', 'Фракции и союзы', 'chess-rook',
     'Map the groups, houses, factions or camps in this story and who belongs to which. Put the faction name in each character\'s "group" field, and use kinds "ally" and "enemy" between the groups\' members.',
     'Собираю фракции…'],
    ['love', 'Любовные линии', 'heart',
     'Map only the romantic and sexual entanglements: who wants whom, who is with whom, who is jealous of whom. Use kinds "romance", "rival" and "enemy".',
     'Ищу любовные линии…'],
    // The task text for this one comes from the user; the entry only carries the
    // label, the icon and what to say while it works.
    ['custom', 'Своя инструкция', 'pen-fancy', '', 'Собираю по вашей инструкции…'],
];

// ===== FACES: WHERE THEY COME FROM =====
// Everything Tavern already knows a face for: the characters in the list and the
// personas. Matching is by name, and loosely — a tree calls someone "Зуко
// Хомура" where the card is just "Зуко", and either should find the other.
function avatarCatalogue() {
    const stCtx = typeof getContext === 'function' ? getContext() : {};
    const out = [];
    (stCtx.characters || []).forEach(c => {
        if (!c?.avatar) return;
        out.push({ name: c.name || c.avatar, url: `/thumbnail?type=avatar&file=${encodeURIComponent(c.avatar)}`, kind: 'char' });
    });
    const personas = stCtx.powerUserSettings?.personas || {};
    Object.entries(personas).forEach(([file, name]) => {
        out.push({ name: name || file, url: `/User Avatars/${encodeURIComponent(file)}`, kind: 'persona' });
    });
    return out;
}
const norm = s => String(s || '').toLowerCase().replace(/[^\p{L}\p{N}]+/gu, ' ').trim();
function matchAvatar(name, list) {
    const n = norm(name);
    if (!n) return null;
    let best = list.find(a => norm(a.name) === n);
    if (best) return best;
    // One name inside the other, longest match first so "Ло Трафальгар" does not
    // lose to a character called "Ло".
    const cands = list.filter(a => {
        const an = norm(a.name);
        return an && (n.includes(an) || an.includes(n));
    }).sort((a, b) => norm(b.name).length - norm(a.name).length);
    return cands[0] || null;
}

// Faces are stored with the board, not linked to a file: a tree has to survive
// a character being renamed, deleted, or opened on another device.
async function toAvatarData(src) {
    return new Promise(resolve => {
        const img = new Image();
        img.crossOrigin = 'anonymous';
        img.onload = () => {
            const side = Math.min(img.naturalWidth, img.naturalHeight) || AVATAR_DIM;
            const sx = (img.naturalWidth - side) / 2, sy = (img.naturalHeight - side) / 2;
            const c = document.createElement('canvas');
            c.width = c.height = AVATAR_DIM;
            const ctx = c.getContext('2d');
            // Square crop from the middle — the clip decides the shape later, and
            // a portrait cropped to its centre is nearly always the face.
            ctx.drawImage(img, sx, sy, side, side, 0, 0, AVATAR_DIM, AVATAR_DIM);
            let out;
            try { out = c.toDataURL('image/webp', 0.85); } catch (e) { out = null; }
            if (!out || !out.startsWith('data:image/webp')) out = c.toDataURL('image/jpeg', 0.85);
            resolve(out);
        };
        img.onerror = () => resolve(null);
        img.src = src;
    });
}

function ensureTree(card) {
    if (!card.tree || typeof card.tree !== 'object') card.tree = {};
    const t = card.tree;
    if (!Array.isArray(t.nodes)) t.nodes = [];
    if (!Array.isArray(t.edges)) t.edges = [];
    if (!t.layout || !TREE_LAYOUTS.some(l => l[0] === t.layout)) t.layout = 'hierarchy';
    if (!t.skin || !TREE_SKINS.some(s => s[0] === t.skin)) t.skin = 'parchment';
    if (t.skin === 'custom' && (!t.custom || typeof t.custom !== 'object')) {
        t.custom = { ...TREE_CUSTOM_DEFAULT, ...(boards.global?.treeCustom || {}) };
    }
    if (typeof t.title !== 'string') t.title = 'Связи';
    // ids are what the edges point at, so nothing may go without one
    const used = new Set();
    t.nodes.forEach((n, i) => {
        if (!n.id || used.has(n.id)) n.id = 'n' + (i + 1) + genId().slice(0, 3);
        used.add(n.id);
        if (typeof n.name !== 'string') n.name = '';
    });
    t.edges = t.edges.filter(e => e && used.has(e.a) && used.has(e.b) && e.a !== e.b);
    t.edges.forEach(e => { if (!TREE_EDGE_KINDS[e.kind]) e.kind = 'other'; });
    return t;
}

function mostConnected(nodes, edges) {
    const count = new Map(nodes.map(n => [n.id, 0]));
    edges.forEach(e => {
        count.set(e.a, (count.get(e.a) || 0) + 1);
        count.set(e.b, (count.get(e.b) || 0) + 1);
    });
    let best = nodes[0]?.id, bestN = -1;
    count.forEach((v, k) => { if (v > bestN) { bestN = v; best = k; } });
    return best;
}

// Positions, in a space that is normalised to start at the padding afterwards.
function treeLayout(tree) {
    const nodes = tree.nodes, edges = tree.edges;
    const pos = new Map();
    const rows = [];
    // Portraits are a different shape from a name in a box, and every distance
    // below is measured against these rather than against fixed constants.
    const size = nodeSize(tree);
    const NW = size.w, NH = size.h;
    if (!nodes.length) return { pos, rows, w: 260, h: 120, size };

    if (tree.layout === 'hierarchy') {
        // Generation = longest chain of "family" links above you. Longest rather
        // than shortest so a grandparent who is also listed as a parent's parent
        // never lands on the same row as their child.
        const parents = new Map(nodes.map(n => [n.id, []]));
        edges.forEach(e => { if (e.kind === 'family' && parents.has(e.b)) parents.get(e.b).push(e.a); });
        const depth = new Map();
        const calc = (id, stack) => {
            if (depth.has(id)) return depth.get(id);
            if (stack.has(id)) return 0;                     // a cycle: stop climbing
            stack.add(id);
            const ps = parents.get(id) || [];
            const d = ps.length ? Math.max(...ps.map(p => calc(p, stack))) + 1 : 0;
            stack.delete(id);
            depth.set(id, d);
            return d;
        };
        nodes.forEach(n => calc(n.id, new Set()));
        const levels = [];
        nodes.forEach(n => {
            const d = depth.get(n.id) || 0;
            (levels[d] = levels[d] || []).push(n);
        });
        // Put children under their parents rather than in insertion order — this
        // is what stops the lines from crossing everything.
        levels.forEach((row, d) => {
            const prev = levels[d - 1];
            if (!prev) return;
            const key = n => {
                const idx = (parents.get(n.id) || [])
                    .map(p => prev.findIndex(x => x.id === p)).filter(i => i >= 0);
                return idx.length ? idx.reduce((a, b) => a + b, 0) / idx.length : 1e6;
            };
            row.sort((a, b) => key(a) - key(b));
        });
        const widest = Math.max(...levels.map(r => r.length));
        const fullW = widest * NW + (widest - 1) * GAP_X;
        levels.forEach((row, d) => {
            const rowW = row.length * NW + (row.length - 1) * GAP_X;
            const x0 = (fullW - rowW) / 2;
            row.forEach((n, i) => pos.set(n.id, { x: x0 + i * (NW + GAP_X), y: d * (NH + GAP_Y) }));
        });
    } else if (tree.layout === 'tiers') {
        // Grouped rows: factions, houses, "his side / her side".
        const groups = new Map();
        nodes.forEach(n => {
            const g = (n.group || n.role || 'Остальные').trim() || 'Остальные';
            if (!groups.has(g)) groups.set(g, []);
            groups.get(g).push(n);
        });
        let ordered = [...groups.entries()].sort((a, b) => b[1].length - a[1].length);
        // Everyone in a group of their own is not a tier layout, it is a column.
        // That is what happens when the cast has roles but no factions — so fall
        // back to even rows and drop the labels that say nothing.
        if (ordered.length > nodes.length / 2) {
            const perRow = Math.max(2, Math.ceil(Math.sqrt(nodes.length)));
            ordered = [];
            for (let i = 0; i < nodes.length; i += perRow) ordered.push(['', nodes.slice(i, i + perRow)]);
        }
        const widest = Math.max(...ordered.map(([, r]) => r.length));
        const fullW = widest * NW + (widest - 1) * GAP_X;
        ordered.forEach(([label, row], d) => {
            const rowW = row.length * NW + (row.length - 1) * GAP_X;
            const x0 = (fullW - rowW) / 2;
            const y = d * (NH + GAP_Y);
            if (label) rows.push({ label, y });
            row.forEach((n, i) => pos.set(n.id, { x: x0 + i * (NW + GAP_X), y }));
        });
    } else {
        // radial / web: a ring. The radial one keeps its busiest person in the
        // middle, which is what makes a "one character and everyone around them"
        // picture read at a glance.
        const centred = tree.layout === 'radial';
        const centerId = centred
            ? (nodes.some(n => n.id === tree.center) ? tree.center : mostConnected(nodes, edges))
            : null;
        const ring = nodes.filter(n => n.id !== centerId);
        if (centerId) pos.set(centerId, { x: -NW / 2, y: -NH / 2 });
        if (ring.length <= 2 && !centerId) {
            ring.forEach((n, i) => pos.set(n.id, { x: i * (NW + GAP_X), y: 0 }));
        } else {
            const R = Math.max(centred ? 250 : 200, (ring.length * (NW + 62)) / (2 * Math.PI));
            ring.forEach((n, i) => {
                const a = (i / ring.length) * Math.PI * 2 - Math.PI / 2;
                pos.set(n.id, { x: Math.cos(a) * R - NW / 2, y: Math.sin(a) * R * 0.8 - NH / 2 });
            });
        }
    }

    let x0 = Infinity, y0 = Infinity, x1 = -Infinity, y1 = -Infinity;
    pos.forEach(p => {
        x0 = Math.min(x0, p.x); y0 = Math.min(y0, p.y);
        x1 = Math.max(x1, p.x + NW); y1 = Math.max(y1, p.y + NH);
    });
    const padX = 30, padTop = tree.title ? 62 : 28, padBot = 28;
    pos.forEach(p => { p.x += padX - x0; p.y += padTop - y0; });
    rows.forEach(r => { r.y += padTop - y0; });
    return { pos, rows, w: (x1 - x0) + padX * 2, h: (y1 - y0) + padTop + padBot, size };
}

// A person's box, in whatever size the current photo mode makes them.
function boxOf(p, size) {
    const w = size?.w || NODE_W, h = size?.h || NODE_H;
    return { x: p.x, y: p.y, w, h, cx: p.x + w / 2, cy: p.y + h / 2 };
}

// One edge as an SVG path, plus a way to ask for any point along it — which is
// what lets a label go looking for somewhere it doesn't cover a name.
function treeEdgePath(A, B, layout) {
    if (layout === 'hierarchy' && B.cy > A.cy + 10) {
        const from = { x: A.cx, y: A.y + A.h }, to = { x: B.cx, y: B.y };
        const my = (from.y + to.y) / 2;
        const c1 = { x: from.x, y: my }, c2 = { x: to.x, y: my };
        const at = t => {
            const u = 1 - t;
            return {
                x: u*u*u*from.x + 3*u*u*t*c1.x + 3*u*t*t*c2.x + t*t*t*to.x,
                y: u*u*u*from.y + 3*u*u*t*c1.y + 3*u*t*t*c2.y + t*t*t*to.y,
            };
        };
        return { d: `M${from.x} ${from.y} C${c1.x} ${c1.y} ${c2.x} ${c2.y} ${to.x} ${to.y}`, at, mid: at(0.5) };
    }
    const from = rectEdge(A, B.cx, B.cy), to = rectEdge(B, A.cx, A.cy);
    const dx = to.x - from.x, dy = to.y - from.y, len = Math.hypot(dx, dy) || 1;
    const k = Math.min(70, len * 0.16);
    const ctrl = { x: (from.x + to.x) / 2 - (dy / len) * k, y: (from.y + to.y) / 2 + (dx / len) * k };
    const at = t => quadAt({ from, ctrl, to }, t);
    return { d: `M${from.x} ${from.y} Q${ctrl.x} ${ctrl.y} ${to.x} ${to.y}`, at, mid: at(0.5) };
}

// How much of a label sits on top of somebody's card. Zero means it is clear.
function labelOverlap(p, w, h, boxes) {
    const x0 = p.x - w / 2, x1 = p.x + w / 2, y0 = p.y - h / 2, y1 = p.y + h / 2;
    let worst = 0;
    for (const b of boxes) {
        const ox = Math.min(x1, b.x + b.w) - Math.max(x0, b.x);
        const oy = Math.min(y1, b.y + b.h) - Math.max(y0, b.y);
        if (ox > 0 && oy > 0) worst += ox * oy;
    }
    return worst;
}

// Walks along the line looking for a spot that covers nobody's name, and only
// if there is none does it settle for the least bad one. Sitting on a name is
// the one thing a label must not do: the name is the point of the picture.
function placeEdgeLabel(path, w, h, boxes) {
    const along = [0.5, 0.42, 0.58, 0.34, 0.66, 0.26, 0.74, 0.2, 0.8];
    let best = null, bestScore = Infinity;
    for (const t of along) {
        const p = path.at(t);
        const score = labelOverlap(p, w, h, boxes);
        if (score === 0) return p;
        if (score < bestScore) { bestScore = score; best = p; }
        // Step sideways off the line as well — on a dense web the whole line can
        // run behind cards, and a small nudge clears it.
        const a = path.at(Math.max(0, t - 0.02)), b = path.at(Math.min(1, t + 0.02));
        const dx = b.x - a.x, dy = b.y - a.y, len = Math.hypot(dx, dy) || 1;
        for (const off of [18, -18, 34, -34, 52, -52]) {
            const q = { x: p.x - (dy / len) * off, y: p.y + (dx / len) * off };
            const s2 = labelOverlap(q, w, h, boxes);
            if (s2 === 0) return q;
            if (s2 < bestScore) { bestScore = s2; best = q; }
        }
    }
    return best || path.mid;
}

function fitText(s, max) {
    s = String(s || '').trim();
    return s.length > max ? s.slice(0, max - 1) + '…' : s;
}

function treeSvg(card) {
    const t = ensureTree(card);
    const sk = treeSkinOf(t);
    const { pos, rows, w, h, size } = treeLayout(t);
    const uid = 'mbt' + card.id;

    if (!t.nodes.length) {
        return `<svg viewBox="0 0 320 120" class="mb-tree-svg" xmlns="http://www.w3.org/2000/svg">
            <rect width="320" height="120" rx="14" fill="${sk.bg}" stroke="${sk.stroke}"/>
            <text x="160" y="58" text-anchor="middle" fill="${sk.sub}" font-size="15"
                  font-family="'Inter',sans-serif">Дерево пустое</text>
            <text x="160" y="80" text-anchor="middle" fill="${sk.sub}" font-size="12"
                  font-family="'Inter',sans-serif">Нажмите ещё раз, чтобы заполнить</text>
        </svg>`;
    }

    // Only the kinds actually used get a legend line.
    const kinds = [...new Set(t.edges.map(e => e.kind))].filter(k => TREE_EDGE_KINDS[k]);
    const legendH = kinds.length > 1 ? 34 : 0;
    const H = h + legendH;

    let svg = `<svg viewBox="0 0 ${Math.round(w)} ${Math.round(H)}" class="mb-tree-svg" xmlns="http://www.w3.org/2000/svg">
        <defs>
            <linearGradient id="${uid}bg" x1="0" y1="0" x2="0" y2="1">
                <stop offset="0%" stop-color="${sk.bg}"/><stop offset="100%" stop-color="${sk.bg2}"/>
            </linearGradient>
            <filter id="${uid}sh" x="-20%" y="-20%" width="140%" height="150%">
                <feDropShadow dx="0" dy="2" stdDeviation="2.4" flood-opacity="0.28"/>
            </filter>
        </defs>
        <rect x="0" y="0" width="${Math.round(w)}" height="${Math.round(H)}" rx="16" fill="url(#${uid}bg)" stroke="${sk.stroke}" stroke-width="1.5"/>`;

    if (t.title) {
        svg += `<text x="${Math.round(w / 2)}" y="38" text-anchor="middle" fill="${sk.title}"
            font-size="26" font-family="${sk.titleFont}">${escHtml(fitText(t.title, 42))}</text>`;
    }
    rows.forEach(r => {
        svg += `<text x="14" y="${Math.round(r.y - 8)}" fill="${sk.sub}" font-size="12"
            font-family="'Inter',sans-serif" opacity="0.85">${escHtml(fitText(r.label, 28))}</text>`;
    });

    // Lines first, so they run underneath the boxes. Their labels are held back
    // and painted last: a label that lands where a box is would otherwise
    // disappear behind it, which is exactly where two related people tend to sit.
    let labels = '';
    // Every card on the picture, so a label can be told where not to go. Labels
    // already placed join the list, or two of them would pick the same gap.
    const taken = t.nodes.map(n => pos.get(n.id)).filter(Boolean).map(p => boxOf(p, size));
    t.edges.forEach(e => {
        const pa = pos.get(e.a), pb = pos.get(e.b);
        if (!pa || !pb) return;
        const [, col, dash] = TREE_EDGE_KINDS[e.kind] || TREE_EDGE_KINDS.other;
        const path = treeEdgePath(boxOf(pa, size), boxOf(pb, size), t.layout);
        svg += `<path d="${path.d}" fill="none" stroke="${col}" stroke-width="2.2" stroke-linecap="round"
            ${dash ? `stroke-dasharray="${dash.join(' ')}"` : ''} opacity="0.9"/>`;
        if (e.label) {
            const label = fitText(e.label, 22);
            const tw = label.length * 6.6 + 12, th = 20;
            const at = placeEdgeLabel(path, tw, th, taken);
            taken.push({ x: at.x - tw / 2, y: at.y - th / 2, w: tw, h: th });
            labels += `<rect x="${(at.x - tw / 2).toFixed(1)}" y="${(at.y - th / 2).toFixed(1)}" width="${tw.toFixed(1)}" height="${th}"
                        rx="10" fill="${sk.bg}" stroke="${col}" stroke-width="1"/>
                    <text x="${at.x.toFixed(1)}" y="${(at.y + 4).toFixed(1)}" text-anchor="middle" fill="${sk.text}"
                        font-size="11" font-family="'Inter',sans-serif">${escHtml(label)}</text>`;
        }
    });

    // One clip per face, so a portrait can be a circle, a rounded square or a
    // plain square without touching the picture itself.
    let clips = '';
    t.nodes.forEach((n, i) => {
        if (!n.img || !size.av) return;
        const p = pos.get(n.id);
        if (!p) return;
        const a = size.av;
        const ax = size.mode === 'portrait' ? p.x + (size.w - a) / 2 : p.x + 8;
        const ay = size.mode === 'portrait' ? p.y + 9 : p.y + (size.h - a) / 2;
        clips += `<clipPath id="${uid}av${i}"><rect x="${ax.toFixed(1)}" y="${ay.toFixed(1)}" width="${a}" height="${a}"
            rx="${avatarRadius(size.shape, a)}"/></clipPath>`;
    });
    if (clips) svg = svg.replace('</defs>', clips + '</defs>');

    t.nodes.forEach((n, i) => {
        const p = pos.get(n.id);
        if (!p) return;
        const accent = n.color || sk.line;
        const isCenter = t.layout === 'radial' && n.id === (t.center || mostConnected(t.nodes, t.edges));
        const a = size.av, hasImg = !!(n.img && a);

        if (size.mode === 'portrait') {
            // A face with a name under it. The name is deliberately smaller than
            // in the boxed layouts — here the picture is what identifies someone,
            // and the text is only there to confirm it.
            const ax = p.x + (size.w - a) / 2, ay = p.y + 9;
            svg += `<g filter="url(#${uid}sh)">`;
            if (hasImg) {
                svg += `<image href="${n.img}" x="${ax.toFixed(1)}" y="${ay.toFixed(1)}" width="${a}" height="${a}"
                    preserveAspectRatio="xMidYMid slice" clip-path="url(#${uid}av${i})"/>`;
            } else {
                svg += `<rect x="${ax.toFixed(1)}" y="${ay.toFixed(1)}" width="${a}" height="${a}"
                    rx="${avatarRadius(size.shape, a)}" fill="${sk.node}"/>
                    <text x="${(ax + a / 2).toFixed(1)}" y="${(ay + a / 2 + a * 0.14).toFixed(1)}" text-anchor="middle"
                        fill="${sk.sub}" font-size="${(a * 0.42).toFixed(1)}"
                        font-family="'Inter',sans-serif">${escHtml((n.name || '?').trim().charAt(0).toUpperCase())}</text>`;
            }
            svg += `<rect x="${ax.toFixed(1)}" y="${ay.toFixed(1)}" width="${a}" height="${a}"
                rx="${avatarRadius(size.shape, a)}" fill="none"
                stroke="${isCenter ? sk.title : accent}" stroke-width="${isCenter ? 3 : 2}"/>
                <text x="${(p.x + size.w / 2).toFixed(1)}" y="${(ay + a + 17).toFixed(1)}" text-anchor="middle"
                    fill="${sk.text}" font-size="12" font-weight="600"
                    font-family="'Inter',sans-serif">${escHtml(fitText(n.name || '?', 14))}</text>`;
            if (n.role) {
                svg += `<text x="${(p.x + size.w / 2).toFixed(1)}" y="${(ay + a + 30).toFixed(1)}" text-anchor="middle"
                    fill="${sk.sub}" font-size="10"
                    font-family="'Inter',sans-serif">${escHtml(fitText(n.role, 16))}</text>`;
            }
            svg += `</g>`;
            return;
        }

        // Boxed: the same card as before, with room made on the left for a face
        // when there is one to show.
        const textX = p.x + (a ? 16 + a : 16);
        svg += `<g filter="url(#${uid}sh)">
            <rect x="${p.x.toFixed(1)}" y="${p.y.toFixed(1)}" width="${size.w}" height="${size.h}" rx="12"
                fill="${sk.node}" stroke="${isCenter ? sk.title : sk.stroke}" stroke-width="${isCenter ? 2.4 : 1.4}"/>
            <path d="M${(p.x + 6).toFixed(1)} ${p.y.toFixed(1)} h0 a6 6 0 0 0 -6 6 v${size.h - 12} a6 6 0 0 0 6 6 z" fill="${accent}"/>`;
        if (a) {
            const ax = p.x + 8, ay = p.y + (size.h - a) / 2;
            if (hasImg) {
                svg += `<image href="${n.img}" x="${ax.toFixed(1)}" y="${ay.toFixed(1)}" width="${a}" height="${a}"
                    preserveAspectRatio="xMidYMid slice" clip-path="url(#${uid}av${i})"/>`;
            } else {
                svg += `<rect x="${ax.toFixed(1)}" y="${ay.toFixed(1)}" width="${a}" height="${a}"
                    rx="${avatarRadius(size.shape, a)}" fill="${sk.bg2}"/>`;
            }
            svg += `<rect x="${ax.toFixed(1)}" y="${ay.toFixed(1)}" width="${a}" height="${a}"
                rx="${avatarRadius(size.shape, a)}" fill="none" stroke="${accent}" stroke-width="1.6"/>`;
        }
        svg += `<text x="${textX.toFixed(1)}" y="${(p.y + (n.role ? size.h / 2 - 3 : size.h / 2 + 5)).toFixed(1)}" fill="${sk.text}"
                font-size="14" font-weight="600" font-family="'Inter',sans-serif">${escHtml(fitText(n.name || '?', a ? 15 : 18))}</text>`;
        if (n.role) {
            svg += `<text x="${textX.toFixed(1)}" y="${(p.y + size.h / 2 + 15).toFixed(1)}" fill="${sk.sub}"
                font-size="11.5" font-family="'Inter',sans-serif">${escHtml(fitText(n.role, a ? 18 : 22))}</text>`;
        }
        svg += `</g>`;
    });
    svg += labels;

    if (legendH) {
        let lx = 18;
        const ly = h + 16;
        kinds.forEach(k => {
            const [label, col, dash] = TREE_EDGE_KINDS[k];
            svg += `<line x1="${lx}" y1="${ly}" x2="${lx + 20}" y2="${ly}" stroke="${col}" stroke-width="2.4"
                        stroke-linecap="round" ${dash ? `stroke-dasharray="${dash.join(' ')}"` : ''}/>
                    <text x="${lx + 26}" y="${ly + 4}" fill="${sk.sub}" font-size="11"
                        font-family="'Inter',sans-serif">${escHtml(label)}</text>`;
            lx += 26 + label.length * 6.4 + 18;
        });
    }
    return svg + '</svg>';
}

// What a tree says, in words — for the AI prompt and for anything else that
// needs the content rather than the picture.
function treeAsText(card) {
    const t = card.tree;
    if (!t || !Array.isArray(t.nodes) || !t.nodes.length) return '';
    const byId = new Map(t.nodes.map(n => [n.id, n]));
    const who = t.nodes.map(n => `${n.name}${n.role ? ` (${n.role})` : ''}${n.group ? ` [${n.group}]` : ''}${n.note ? ` — ${n.note}` : ''}`);
    const ties = (t.edges || []).map(e => {
        const a = byId.get(e.a), b = byId.get(e.b);
        if (!a || !b) return '';
        const kind = (TREE_EDGE_KINDS[e.kind] || TREE_EDGE_KINDS.other)[0];
        return `${a.name} → ${b.name}: ${e.label || kind}`;
    }).filter(Boolean);
    return `${t.title || 'Связи'}:\n${who.join('\n')}${ties.length ? '\n' + ties.join('\n') : ''}`;
}

function addTreeCard(tree) {
    const board = getBoard();
    const vc = viewportCenter();
    const card = {
        id: genId(), type: 'tree', content: '', tree, z: maxCardZ() + 1,
        x: Math.round(vc.x - 240), y: Math.round(vc.y - 150), w: 480,
        shape: 'none', color: '#fdf6e3', created: Date.now(),
    };
    ensureTree(card);
    board.cards.push(card);
    save(true);
    if ($('#mb-modal').is(':visible')) renderCard(card, true);
    return card;
}

function repaintTree(card, $card) {
    const $wrap = ($card || $(`.mb-card[data-id="${card.id}"]`)).find('.mb-tree-wrap');
    if ($wrap.length) $wrap.html(treeSvg(card));
    linkGeomDirty = true;
    renderInk();
}

// The toolbar button: what kind of tree, and where it comes from.
function openTreePicker() {
    markHold();
    const $p = $('#mb-tree-picker').empty();
    $p.append('<div class="mb-brush-title">Новое дерево</div>');
    const $g = $('<div class="mb-tree-presets"></div>').appendTo($p);
    $(`<div class="mb-brush-opt wide"><i class="fa-solid fa-pen-to-square"></i><span>Пустое — заполню сам</span></div>`)
        .on('click', e => {
            e.stopPropagation();
            $p.removeClass('open');
            const card = addTreeCard({ title: 'Связи', layout: 'hierarchy', skin: 'parchment', nodes: [], edges: [] });
            openTreePanel(card);
        }).appendTo($g);
    TREE_PRESETS.forEach(([key, label, icon]) => {
        const custom = key === 'custom';
        $(`<div class="mb-brush-opt wide"><i class="fa-solid fa-${icon}"></i><span>${custom ? label : label + ' из чата'}</span></div>`)
            .on('click', e => {
                e.stopPropagation();
                $p.removeClass('open');
                // Nothing written yet: make the tree, open its panel and put the
                // cursor in the box rather than sending an empty instruction.
                if (custom && !(boards.global?.treeCustomPrompt || '').trim()) {
                    const made = addTreeCard({ title: 'Связи', layout: 'web', skin: 'parchment', nodes: [], edges: [] });
                    openTreePanel(made);
                    setTimeout(() => {
                        const box = document.querySelector('#mb-tree-body .mb-note-editor');
                        box?.scrollIntoView({ block: 'center' });
                        box?.focus();
                    }, 120);
                    toastr?.info('Опишите, что собрать, и нажмите кнопку под полем');
                    return;
                }
                generateTree(key);
            })
            .appendTo($g);
    });
    $p.append('<div class="mb-select-hint" style="margin:8px 0 0">Из чата — расширение прочитает последние сообщения (сколько именно, задаётся в настройках) и соберёт дерево само. Потом его можно править руками.</div>');
    anchorPanel($p, document.getElementById('mb-btn-tree'));
}

// ===== TREE EDITOR =====
function openTreePanel(card, $card) {
    notePreviewRepaint = null;
    const t = ensureTree(card);
    const $b = $('#mb-tree-body').empty();
    const touch = () => { repaintTree(card, $card); save(); };

    $b.append('<span class="mb-settings-label" style="margin-top:4px">Заголовок</span>');
    $('<input type="text" class="mb-settings-input">').val(t.title || '')
        .on('input', function() { t.title = this.value; touch(); })
        .on('keydown', e => e.stopPropagation())
        .appendTo($b);

    appendSizeControl($b, card, $card);

    $b.append('<span class="mb-settings-label">Вид</span>');
    const $lg = $('<div class="mb-brush-grid"></div>').appendTo($b);
    TREE_LAYOUTS.forEach(([val, label, icon]) => {
        $(`<div class="mb-brush-opt ${t.layout === val ? 'active' : ''}">
             <i class="fa-solid fa-${icon}"></i><span>${label}</span></div>`)
            .on('click', function() {
                t.layout = val;
                $lg.find('.mb-brush-opt').removeClass('active');
                $(this).addClass('active');
                touch();
            }).appendTo($lg);
    });

    $b.append('<span class="mb-settings-label">Оформление</span>');
    const $sg = $('<div class="mb-skin-row"></div>').appendTo($b);
    TREE_SKINS.forEach(([val, label]) => {
        const sk = val === 'custom' ? treeSkinOf({ skin: 'custom', custom: t.custom }) : TREE_SKIN_CSS[val];
        $(`<div class="mb-skin-opt ${t.skin === val ? 'active' : ''}" data-skin="${val}"
             style="background:linear-gradient(160deg,${sk.bg},${sk.bg2});color:${sk.text};border-color:${sk.stroke}">
             <span class="mb-skin-dot" style="background:${sk.line}"></span>${label}</div>`)
            .on('click', function() {
                t.skin = val;
                ensureTree(card);
                $sg.find('.mb-skin-opt').removeClass('active');
                $(this).addClass('active');
                touch();
                drawCustomSkin();
            }).appendTo($sg);
    });

    // The palette editor, shown only while "Своё" is the chosen look.
    const $cs = $('<div class="mb-skin-custom"></div>').appendTo($b);
    const drawCustomSkin = () => {
        $cs.empty();
        if (t.skin !== 'custom') return;
        const pal = () => (t.custom = { ...TREE_CUSTOM_DEFAULT, ...(boards.global?.treeCustom || {}), ...(t.custom || {}) });
        const setColor = (key, hex) => {
            pal()[key] = hex;
            // Remembered globally, so the next tree you make starts from the
            // palette you built rather than from parchment again.
            if (!boards.global.treeCustom) boards.global.treeCustom = {};
            boards.global.treeCustom[key] = hex;
            touch();
            drawCustomSkin();
            $sg.find('[data-skin="custom"]').each(function() {
                const sk = treeSkinOf(t);
                this.style.background = `linear-gradient(160deg,${sk.bg},${sk.bg2})`;
                this.style.color = sk.text; this.style.borderColor = sk.stroke;
                this.querySelector('.mb-skin-dot').style.background = sk.line;
            });
        };
        $cs.append('<div class="mb-select-hint" style="margin:2px 0 6px">Нажмите на кружок, чтобы поменять цвет. Всё, что вы здесь соберёте, запомнится и станет отправной точкой для следующего дерева.</div>');
        const $grid = $('<div class="mb-palette-grid"></div>').appendTo($cs);
        const cur = treeSkinOf(t);
        TREE_CUSTOM_FIELDS.forEach(([key, label]) => {
            const $sw = $(`<div class="mb-palette-cell">
                <span class="mb-palette-dot" style="background:${cur[key]}"></span>
                <span>${label}</span></div>`);
            $sw.on('click', async () => {
                const c = await mbColorPicker(label, cur[key]);
                if (c) setColor(key, c);
            });
            $grid.append($sw);
        });

        $cs.append('<span class="mb-settings-label">Шрифт заголовка</span>');
        const $fr = $('<div class="mb-skin-row"></div>').appendTo($cs);
        TREE_TITLE_FONTS.forEach(([val, label]) => {
            $(`<div class="mb-skin-opt ${cur.titleFont === val ? 'active' : ''}"
                 style="font-family:${val};background:var(--mb-chip);color:var(--mb-text)">${label}</div>`)
                .on('click', () => setColor('titleFont', val)).appendTo($fr);
        });

        $('<button class="mb-settings-btn secondary"><i class="fa-solid fa-rotate-left"></i> Вернуть исходные цвета</button>')
            .on('click', () => {
                t.custom = { ...TREE_CUSTOM_DEFAULT };
                boards.global.treeCustom = { ...TREE_CUSTOM_DEFAULT };
                touch(); drawCustomSkin();
            }).appendTo($cs);
        $cs.append('<span class="mb-settings-label">Взять за основу</span>');
        const $base = $('<div class="mb-skin-row"></div>').appendTo($cs);
        TREE_SKINS.filter(s => s[0] !== 'custom').forEach(([val, label]) => {
            const sk = TREE_SKIN_CSS[val];
            $(`<div class="mb-skin-opt" style="background:linear-gradient(160deg,${sk.bg},${sk.bg2});color:${sk.text};border-color:${sk.stroke}">${label}</div>`)
                .on('click', () => {
                    t.custom = { ...sk, titleFont: sk.titleFont };
                    boards.global.treeCustom = { ...t.custom };
                    touch(); drawCustomSkin();
                }).appendTo($base);
        });
    };
    drawCustomSkin();

    // ---- faces
    $b.append('<span class="mb-settings-label">Фото персонажей</span>');
    const ph = () => (t.photo = t.photo || {});
    const $pm = $('<div class="mb-brush-grid mb-grid-3"></div>').appendTo($b);
    TREE_PHOTO_MODES.forEach(([val, label, icon]) => {
        $(`<div class="mb-brush-opt ${treePhoto(t).mode === val ? 'active' : ''}">
             <i class="fa-solid fa-${icon}"></i><span>${label}</span></div>`)
            .on('click', function() {
                ph().mode = val;
                $pm.find('.mb-brush-opt').removeClass('active');
                $(this).addClass('active');
                touch(); drawNodes();
            }).appendTo($pm);
    });
    const $shapeRow = $('<div class="mb-skin-row" style="margin-top:8px"></div>').appendTo($b);
    TREE_PHOTO_SHAPES.forEach(([val, label]) => {
        $(`<div class="mb-skin-opt ${treePhoto(t).shape === val ? 'active' : ''}"
             style="background:var(--mb-chip);color:var(--mb-text)">
             <span class="mb-avatar-shape ${val}"></span>${label}</div>`)
            .on('click', function() {
                ph().shape = val;
                $shapeRow.find('.mb-skin-opt').removeClass('active');
                $(this).addClass('active');
                touch();
            }).appendTo($shapeRow);
    });
    const $sz = $('<div class="mb-brush-size"></div>').appendTo($b);
    const $szs = $(`<input type="range" min="70" max="180" step="5" value="${Math.round(treePhoto(t).size * 100)}">`).appendTo($sz);
    const $szv = $(`<b>${Math.round(treePhoto(t).size * 100)}%</b>`).appendTo($sz);
    $szs.on('input', function() {
        ph().size = parseInt(this.value, 10) / 100;
        $szv.text(this.value + '%');
        touch();
    });
    $('<button class="mb-settings-btn secondary"><i class="fa-solid fa-user-check"></i> Подставить аватарки по именам</button>')
        .on('click', async () => {
            const list = avatarCatalogue();
            if (!list.length) { toastr?.info('Не нашлось ни одного персонажа с аватаркой'); return; }
            await showBusy('Ищу лица…');
            let hit = 0;
            try {
                for (const n of t.nodes) {
                    if (n.img) continue;
                    const m = matchAvatar(n.name, list);
                    if (!m) continue;
                    const data = await toAvatarData(m.url);
                    if (data) { n.img = data; hit++; }
                }
                if (hit && treePhoto(t).mode === 'off') ph().mode = 'portrait';
                touch(); drawNodes();
            } finally { hideBusy(); }
            toastr?.[hit ? 'success' : 'info'](hit
                ? `Нашлось лиц: ${hit} из ${t.nodes.length}`
                : 'Совпадений по именам нет — можно поставить фото вручную');
            openTreePanel(card, $card);
        }).appendTo($b);
    $b.append('<div class="mb-select-hint">Ищет среди ваших персонажей и персон по имени. Кто не нашёлся — нажмите на кружок в списке ниже и выберите вручную или загрузите файл.</div>');

    // ---- people
    $b.append('<span class="mb-settings-label">Кто на дереве</span>');
    const $nl = $('<div class="mb-tree-list"></div>').appendTo($b);
    const drawNodes = () => {
        $nl.empty();
        if (!t.nodes.length) $nl.append('<div class="mb-empty-hint">Пока никого. Добавьте первого — или соберите дерево из чата ниже.</div>');
        t.nodes.forEach(n => {
            const $row = $(`<div class="mb-tree-row">
                <span class="mb-tree-face ${n.img ? 'has' : ''}" title="Фото">${n.img
                    ? `<img src="${n.img}" alt="">` : '<i class="fa-solid fa-user"></i>'}</span>
                <span class="mb-tree-swatch" style="background:${n.color || '#a9834a'}" title="Цвет"></span>
                <input class="mb-tree-name" placeholder="Имя">
                <input class="mb-tree-role" placeholder="кто это">
                <i class="fa-solid fa-trash mb-tree-del" title="Убрать"></i>
            </div>`);
            $row.find('.mb-tree-face').on('click', function(e) {
                e.stopPropagation();
                openAvatarPicker(n, this.getBoundingClientRect(), () => { touch(); drawNodes(); });
            });
            $row.find('.mb-tree-name').val(n.name || '').on('input', function() { n.name = this.value; touch(); });
            $row.find('.mb-tree-role').val(n.role || '').on('input', function() { n.role = this.value; touch(); });
            $row.find('input').on('keydown', e => e.stopPropagation());
            $row.find('.mb-tree-swatch').on('click', async function() {
                const c = await mbColorPicker('Цвет узла', n.color || '#a9834a');
                if (c) { n.color = c; $(this).css('background', c); touch(); }
            });
            $row.find('.mb-tree-del').on('click', () => {
                t.nodes = t.nodes.filter(x => x !== n);
                t.edges = t.edges.filter(e => e.a !== n.id && e.b !== n.id);
                drawNodes(); drawEdges(); touch();
            });
            $nl.append($row);
        });
    };
    $('<button class="mb-settings-btn secondary"><i class="fa-solid fa-user-plus"></i> Добавить человека</button>')
        .on('click', () => {
            t.nodes.push({ id: 'n' + genId(), name: '', role: '' });
            drawNodes(); drawEdges(); touch();
        }).appendTo($b);

    // ---- ties
    $b.append('<span class="mb-settings-label">Связи</span>');
    const $el = $('<div class="mb-tree-list"></div>').appendTo($b);
    const nameOf = id => (t.nodes.find(n => n.id === id)?.name || '—');
    const drawEdges = () => {
        $el.empty();
        if (t.nodes.length < 2) { $el.append('<div class="mb-empty-hint">Связи появятся, когда на дереве будет хотя бы двое.</div>'); return; }
        if (!t.edges.length) $el.append('<div class="mb-empty-hint">Связей пока нет.</div>');
        t.edges.forEach(e => {
            const opts = who => t.nodes.map(n =>
                `<option value="${n.id}" ${who === n.id ? 'selected' : ''}>${escHtml(fitText(n.name || '?', 16))}</option>`).join('');
            const kinds = Object.entries(TREE_EDGE_KINDS).map(([k, v]) =>
                `<option value="${k}" ${e.kind === k ? 'selected' : ''}>${v[0]}</option>`).join('');
            const $row = $(`<div class="mb-tree-row edge">
                <select class="mb-tree-sel a">${opts(e.a)}</select>
                <select class="mb-tree-sel kind">${kinds}</select>
                <select class="mb-tree-sel b">${opts(e.b)}</select>
                <input class="mb-tree-label" placeholder="подпись">
                <i class="fa-solid fa-trash mb-tree-del" title="Убрать"></i>
            </div>`);
            $row.find('.a').on('change', function() { e.a = this.value; touch(); });
            $row.find('.b').on('change', function() { e.b = this.value; touch(); });
            $row.find('.kind').on('change', function() { e.kind = this.value; touch(); });
            $row.find('.mb-tree-label').val(e.label || '')
                .on('input', function() { e.label = this.value; touch(); })
                .on('keydown', ev => ev.stopPropagation());
            $row.find('.mb-tree-del').on('click', () => {
                t.edges = t.edges.filter(x => x !== e);
                drawEdges(); touch();
            });
            $el.append($row);
        });
    };
    $('<button class="mb-settings-btn secondary"><i class="fa-solid fa-link"></i> Добавить связь</button>')
        .on('click', () => {
            if (t.nodes.length < 2) { toastr?.info('Сначала добавьте хотя бы двоих'); return; }
            t.edges.push({ a: t.nodes[0].id, b: t.nodes[1].id, kind: 'family', label: '' });
            drawEdges(); touch();
        }).appendTo($b);
    drawNodes(); drawEdges();

    $b.append('<span class="mb-settings-label" style="margin-top:18px">Собрать из чата</span>');
    TREE_PRESETS.filter(p => p[0] !== 'custom').forEach(([key, label, icon]) => {
        $(`<button class="mb-settings-btn secondary"><i class="fa-solid fa-${icon}"></i> ${label}</button>`)
            .on('click', () => generateTree(key, card)).appendTo($b);
    });
    $b.append('<div class="mb-select-hint">Соберёт заново по последним сообщениям чата и заменит содержимое этого дерева. Вид и оформление останутся вашими.</div>');

    $b.append('<span class="mb-settings-label" style="margin-top:16px">Своя инструкция для ИИ</span>');
    appendTreePromptBox($b, card);

    // When a build fails, the reply that caused it is right here rather than in
    // the console — you can read it, and copy it if it needs reporting.
    if (lastTreeReply) {
        $b.append('<span class="mb-settings-label" style="margin-top:16px">Последний неразобранный ответ</span>');
        $('<textarea class="mb-settings-input mb-note-editor" rows="6" readonly></textarea>')
            .val(lastTreeReply.slice(0, 4000))
            .on('keydown click pointerdown', e => e.stopPropagation())
            .appendTo($b);
        $b.append(`<div class="mb-select-hint">Это то, что модель прислала в последний раз, когда дерево собрать не вышло (${lastTreeReply.length} символов). Если ответ обрывается на полуслове — модель упёрлась в лимит длины: уменьшите контекст или поднимите max tokens в пресете.</div>`);
    }

    $('<button class="mb-settings-btn danger" style="margin-top:14px"><i class="fa-solid fa-trash"></i> Удалить дерево с доски</button>')
        .on('click', async () => {
            if (!await mbConfirm('Удалить дерево?', 'Карточка с деревом будет убрана с доски.', { okLabel: 'Удалить', danger: true })) return;
            getBoard().cards = getBoard().cards.filter(c => c.id !== card.id);
            pruneLinks();
            $(`.mb-card[data-id="${card.id}"]`).remove();
            $('#mb-tree-panel').removeClass('open');
            save(true); renderInk();
        }).appendTo($b);

    togglePanel('#mb-tree-panel', true);
}

// Picks a face for one person: whoever Tavern already has, or a file from the
// device. The likely matches for this name float to the top, because with forty
// characters in the list scrolling for the right one is the whole cost.
function openAvatarPicker(node, anchorRect, done) {
    markHold();
    const $p = $('#mb-avatar-picker').empty();
    $p.append(`<div class="mb-brush-title">Фото — ${escHtml(fitText(node.name || 'без имени', 22))}</div>`);

    const list = avatarCatalogue();
    const best = matchAvatar(node.name, list);
    const ordered = best ? [best, ...list.filter(a => a !== best)] : list;
    const $grid = $('<div class="mb-avatar-grid"></div>').appendTo($p);
    if (!ordered.length) $grid.append('<div class="mb-empty-hint">Персонажей с аватарками не нашлось</div>');
    ordered.slice(0, 40).forEach(a => {
        $(`<div class="mb-avatar-opt ${a === best ? 'suggested' : ''}" title="${escHtml(a.name)}">
             <img src="${a.url}" alt="" loading="lazy"><span>${escHtml(fitText(a.name, 12))}</span></div>`)
            .on('click', async e => {
                e.stopPropagation();
                const data = await toAvatarData(a.url);
                if (!data) { toastr?.error('Не удалось прочитать картинку'); return; }
                node.img = data;
                $p.removeClass('open');
                done();
            }).appendTo($grid);
    });

    $('<button class="mb-settings-btn secondary"><i class="fa-solid fa-upload"></i> Загрузить файл</button>')
        .on('click', e => {
            e.stopPropagation();
            const inp = document.createElement('input');
            inp.type = 'file'; inp.accept = 'image/*';
            inp.onchange = async ev => {
                const f = ev.target.files?.[0];
                if (!f) return;
                const raw = await new Promise(res => {
                    const r = new FileReader();
                    r.onload = x => res(x.target.result);
                    r.readAsDataURL(f);
                });
                const data = await toAvatarData(raw);
                if (!data) { toastr?.error('Не удалось прочитать картинку'); return; }
                node.img = data;
                $p.removeClass('open');
                done();
            };
            inp.click();
        }).appendTo($p);
    if (node.img) {
        $('<button class="mb-settings-btn danger"><i class="fa-solid fa-xmark"></i> Убрать фото</button>')
            .on('click', e => { e.stopPropagation(); delete node.img; $p.removeClass('open'); done(); })
            .appendTo($p);
    }
    placePanelAt($p, anchorRect.left + anchorRect.width / 2, anchorRect.bottom);
}

// The custom-instruction box. Lives in two places — the tree panel and the
// picker — so it is written once here.
//
// What the box is for: the presets each carry a sentence telling the model what
// to look for. This replaces that sentence and nothing else — the JSON shape,
// the language rule and the "don't invent relatives" rule are always sent
// anyway, so there is nothing to remember and no format to get wrong.
function appendTreePromptBox($b, card) {
    const $ta = $(`<textarea class="mb-settings-input mb-note-editor" rows="5" spellcheck="false"
        placeholder="Например: собери только тех, кто был на балу, и покажи, кто кого узнал, а кто нет"></textarea>`)
        .val(boards.global?.treeCustomPrompt || '');
    $ta.on('input', function() {
        if (!boards.global) boards.global = { cards: [] };
        boards.global.treeCustomPrompt = this.value;
        save();
    }).on('keydown click pointerdown', e => e.stopPropagation());
    $b.append($ta);
    $b.append(`<div class="mb-select-hint">
        Пишите обычными словами, что построить и по какому признаку — как задание живому человеку:<br>
        • <i>«кто кому кем приходится в клане Учиха, включая мёртвых»</i><br>
        • <i>«только враги главного героя, подпиши, из-за чего вражда»</i><br>
        • <i>«кто с кем спал и кто об этом знает»</i><br>
        • <i>«разбей всех по городам: в group напиши город»</i><br>
        Схему JSON, язык ответа и вид связей расширение добавляет само — их описывать не нужно.
        Полезно указать: <b>сколько</b> человек брать, <b>кого не брать</b>, что писать в подписях связей.
    </div>`);
    $(`<button class="mb-settings-btn"><i class="fa-solid fa-wand-magic-sparkles"></i> Собрать по своей инструкции</button>`)
        .on('click', () => {
            if (!(boards.global?.treeCustomPrompt || '').trim()) {
                toastr?.info('Сначала опишите, что собрать');
                $ta.focus();
                return;
            }
            generateTree('custom', card);
        }).appendTo($b);
    return $ta;
}

// ===== TREES FROM THE CHAT =====
// The model is asked for JSON and nothing else, and everything it sends back is
// treated as untrusted: unknown link kinds become "other", edges pointing at
// people who were never introduced are dropped, and names are matched back to
// ids when the model invents its own.
function parseTreeJson(txt) {
    if (!txt) return null;
    let s = String(txt).replace(/^﻿/, '').trim();
    // Reasoning models like to narrate first. Take the fenced block if there is
    // one, and prefer a fence that actually contains an object.
    const fences = [...s.matchAll(/```(?:json|JSON)?\s*([\s\S]*?)```/g)].map(m => m[1]);
    const candidates = [];
    for (const f of fences) if (f.includes('{')) candidates.push(f);
    candidates.push(s);
    // An unterminated fence — which is what a reply cut short by the token limit
    // looks like — leaves no closing ```, so the raw text has to be tried too.
    // Two passes. The first only accepts a candidate that actually holds people,
    // so a stray `{` in the prose — or the first element of a bare array of
    // people — cannot win over the real answer. The second accepts anything
    // parseable, so the caller still has something concrete to complain about.
    const holdsPeople = d => {
        const u = unwrapTree(d);
        return !!(u && Array.isArray(u.nodes) && u.nodes.length);
    };
    for (const cand of candidates) {
        const obj = extractJsonObject(cand, holdsPeople);
        if (obj) return obj;
    }
    for (const cand of candidates) {
        const obj = extractJsonObject(cand);
        if (obj) return obj;
    }
    return null;
}

// Walks the string looking for a bracket that starts something parseable. Prose
// before the JSON often contains braces of its own, so the first one is not
// necessarily the right one — and some models answer with the bare array of
// people instead of the object that was asked for.
function extractJsonObject(s, accept) {
    for (let i = 0; i < s.length; i++) {
        const c = s[i];
        if (c !== '{' && c !== '[') continue;
        const close = c === '{' ? '}' : ']';
        const tail = s.slice(i);
        const j = tail.lastIndexOf(close);
        const tries = [];
        if (j > 0) tries.push(tail.slice(0, j + 1));
        tries.push(tail);
        for (const raw of tries) {
            const got = tryJson(raw);
            if (got && typeof got === 'object' && (!accept || accept(got))) return got;
        }
    }
    return null;
}

function tryJson(raw) {
    const attempts = [
        t => t,
        // The three things models get wrong most: trailing commas, typographic
        // quotes, and // comments.
        t => t.replace(/,(\s*[}\]])/g, '$1')
              .replace(/[«»“”]/g, '"')
              .replace(/^\s*\/\/.*$/gm, ''),
        // And the fourth: an answer that simply stopped mid-object because the
        // reply hit its token ceiling. Cut back to the last complete entry and
        // close whatever is still open — half a tree is far better than none.
        t => repairTruncatedJson(t),
    ];
    for (const fix of attempts) {
        let cooked;
        try { cooked = fix(raw); } catch (e) { continue; }
        if (!cooked) continue;
        try { return JSON.parse(cooked); } catch (e) {}
    }
    return null;
}

// Trims a cut-off JSON document back to its last complete element and closes the
// structures that are still open.
function repairTruncatedJson(t) {
    // Drop an unterminated string first: everything after the last quote that
    // opens one cannot be salvaged.
    let inStr = false, esc = false;
    const stack = [];
    let lastSafe = -1;          // index just past the last completed element
    for (let i = 0; i < t.length; i++) {
        const c = t[i];
        if (inStr) {
            if (esc) esc = false;
            else if (c === '\\') esc = true;
            else if (c === '"') inStr = false;
            continue;
        }
        if (c === '"') { inStr = true; continue; }
        if (c === '{' || c === '[') stack.push(c);
        else if (c === '}' || c === ']') {
            stack.pop();
            if (stack.length <= 1) lastSafe = i + 1;   // a whole node/edge closed
        } else if (c === ',' && stack.length <= 2) lastSafe = i;
    }
    if (!stack.length) return null;          // nothing was left open; not our case
    if (lastSafe <= 0) return null;
    let out = t.slice(0, lastSafe).replace(/,\s*$/, '');
    // Re-derive what is still open on the trimmed text and close it.
    const open = [];
    inStr = false; esc = false;
    for (let i = 0; i < out.length; i++) {
        const c = out[i];
        if (inStr) {
            if (esc) esc = false;
            else if (c === '\\') esc = true;
            else if (c === '"') inStr = false;
            continue;
        }
        if (c === '"') inStr = true;
        else if (c === '{' || c === '[') open.push(c);
        else if (c === '}' || c === ']') open.pop();
    }
    while (open.length) out += open.pop() === '{' ? '}' : ']';
    return out;
}

// Models wrap the answer in whatever felt natural — {"tree": {...}},
// {"graph": {...}}, "people" instead of "nodes", "relationships" instead of
// "edges". Rather than insist, look for the shape wherever it ended up.
function unwrapTree(data) {
    if (!data || typeof data !== 'object') return null;
    if (Array.isArray(data)) return { nodes: data, edges: [] };
    const nodeKeys = ['nodes', 'people', 'characters', 'persons', 'members', 'узлы', 'персонажи'];
    const edgeKeys = ['edges', 'links', 'relations', 'relationships', 'connections', 'связи', 'ребра', 'рёбра'];
    const pick = keys => keys.map(k => data[k]).find(Array.isArray);
    let nodes = pick(nodeKeys), edges = pick(edgeKeys);
    if (!nodes) {
        // One level down: {"tree": {...}} and friends.
        for (const v of Object.values(data)) {
            if (v && typeof v === 'object' && !Array.isArray(v)) {
                const inner = unwrapTree(v);
                if (inner) return { title: data.title || inner.title, ...inner };
            }
        }
        return null;
    }
    return { title: data.title || data.name || '', nodes, edges: edges || [] };
}

function normalizeTree(data, preset) {
    const shaped = unwrapTree(data);
    if (!shaped) return null;
    data = shaped;
    const nodes = [];
    const byName = new Map();
    (Array.isArray(data.nodes) ? data.nodes : []).slice(0, 40).forEach((n, i) => {
        if (typeof n === 'string') n = { name: n };
        const name = String(n?.name ?? n?.label ?? n?.id ?? '').trim();
        if (!name) return;
        const id = String(n?.id || '').trim() || 'n' + (i + 1);
        const node = {
            id, name,
            role: String(n?.role || '').trim().slice(0, 40),
            group: String(n?.group || '').trim().slice(0, 40),
            note: String(n?.note || '').trim().slice(0, 160),
        };
        nodes.push(node);
        byName.set(name.toLowerCase(), id);
        byName.set(id.toLowerCase(), id);
    });
    const ids = new Set(nodes.map(n => n.id));
    const resolve = v => {
        const s = String(v ?? '').trim();
        if (ids.has(s)) return s;
        return byName.get(s.toLowerCase()) || null;
    };
    const edges = [];
    (Array.isArray(data.edges) ? data.edges : []).slice(0, 120).forEach(e => {
        const a = resolve(e?.a ?? e?.from ?? e?.source);
        const b = resolve(e?.b ?? e?.to ?? e?.target);
        if (!a || !b || a === b) return;
        const kind = TREE_EDGE_KINDS[e?.kind] ? e.kind : 'other';
        edges.push({ a, b, kind, label: String(e?.label || '').trim().slice(0, 30) });
    });
    return {
        title: String(data.title || '').trim().slice(0, 60) || (preset ? preset[1] : 'Связи'),
        layout: preset && preset[0] === 'family' ? 'hierarchy' : (preset && preset[0] === 'factions' ? 'tiers' : 'web'),
        skin: 'parchment',
        nodes, edges,
    };
}

// Kept so a failed attempt can be looked at rather than guessed about.
let lastTreeReply = '';

// A throw here means no reply was produced at all, so sending the request again
// costs nothing but time — the quota is spent on answers, not on refused
// connections. Rate limits and gateway hiccups are routine on a shared endpoint,
// and Tavern's own request service reports every one of them as the same opaque
// "API request failed", so there is nothing to match on. Retry by default and
// give up only on the errors that repeating cannot fix.
const NO_RETRY = /not found|no such|missing|invalid|unauthor|forbidden|\b40[13]\b|api key|profile/i;
// Spread out rather than doubled: what is usually behind this is a per-minute
// rate limit, and three quick tries all land inside the same minute and all fail
// for the same reason. These waits carry the last attempt past the minute mark.
const RETRY_WAITS = [3000, 9000, 20000, 40000];
async function withRetries(fn, busyText) {
    const tries = RETRY_WAITS.length + 1;
    for (let i = 0; i < tries; i++) {
        try { return await fn(); }
        catch (e) {
            const msg = String(e?.message || e);
            if (i === tries - 1 || NO_RETRY.test(msg)) throw e;
            const wait = RETRY_WAITS[i];
            console.warn(LOG, `attempt ${i + 1} failed ("${msg.slice(0, 140)}") — retrying in ${wait}ms`);
            await showBusy(`${busyText} не вышло с ${i + 1}-го раза, жду ${Math.round(wait / 1000)} с и пробую снова (${i + 2}/${tries})`);
            await new Promise(r => setTimeout(r, wait));
        }
    }
}

// Says what actually came back, so the next step is obvious instead of a guess.
function treeFailureHint(res) {
    const s = String(res || '').trim();
    if (!s) return 'модель вернула пустой ответ — возможно, запрос отфильтрован. Попробуйте ещё раз.';
    if (!s.includes('{')) return `модель ответила текстом, а не JSON: «${s.slice(0, 80)}…». Попробуйте ещё раз или уменьшите контекст.`;
    const open = (s.match(/[{[]/g) || []).length, close = (s.match(/[}\]]/g) || []).length;
    if (open > close) return 'ответ оборвался на середине — модель упёрлась в лимит длины ответа. Уменьшите контекст или поднимите max tokens в пресете.';
    return 'JSON пришёл, но в нём нет ни одного человека. Полный ответ — в консоли (F12).';
}

async function generateTree(kind, card) {
    const preset = TREE_PRESETS.find(p => p[0] === kind) || TREE_PRESETS[0];
    const stCtx = typeof getContext === 'function' ? getContext() : {};
    const stored = boards.global?.apiContextSize;
    const ctxSize = Number.isFinite(stored) ? stored : 10;
    const user = stCtx.name1 || 'User';
    const { charName, charDesc, charPersona } = resolveSpeakers(stCtx);
    const notes = (getBoard().cards || [])
        .filter(c => c.type === 'text' || c.type === 'quote')
        .map(c => plainNote(c.content)).filter(Boolean).join('\n').slice(0, 2000);

    // The task itself: a preset's wording, or your own.
    const own = (boards.global?.treeCustomPrompt || '').trim();
    const task = kind === 'custom'
        ? (own || TREE_PRESETS.find(p => p[0] === 'relations')[3])
        : preset[3];

    const schema = '{"title":"...","nodes":[{"id":"n1","name":"Имя","role":"кто это в двух словах","group":"фракция или семья","note":"важная деталь"}],' +
                   '"edges":[{"a":"n1","b":"n2","kind":"family|romance|friend|ally|enemy|rival|other","label":"мать"}]}';
    const rules =
        `Answer with a SINGLE JSON object and NOTHING else — no prose before it, no explanation after it.\n` +
        `Shape: ${schema}\n` +
        `Rules: every edge's "a" and "b" MUST be ids that appear in "nodes". ` +
        `"kind" must be one of family, romance, friend, ally, enemy, rival, other. ` +
        `For "family", "a" is the elder and "b" is the younger — parent to child. ` +
        `Write "name", "role", "group", "label" and "title" in the language the chat is written in. ` +
        `Include at most 24 people: the ones who matter. Keep "note" under 120 characters. ` +
        `Do not invent relatives who were never mentioned — if the chat only implies something, ` +
        `say so in "label" (for example "возможно, брат").`;
    const sys = `You are a story analyst. You read a roleplay chat and extract the cast and how they are connected.\n` +
        `${rules}\nTask: ${task}`;
    // The instruction is repeated in full in the last message — at zero depth —
    // because that is the one place a long chat cannot bury it. With a hundred
    // messages of roleplay in between, a system prompt asking for JSON loses to
    // the sheer weight of the conversation, and the model answers in character.
    // A tree is exactly the thing that wants lorebooks: half the cast can live in
    // them. The same three switches decide what comes along.
    const persona = personaText(stCtx);
    const lore = await loreText(stCtx, loreScanText(stCtx, notes, ctxSize));
    const authorNote = authorNoteText(stCtx);
    const cardOn = sendPref('sendCharCard');

    const ask = `[Characters in play: ${charName}${cardOn && charDesc ? ` — ${charDesc.slice(0, 600)}` : ''}` +
        `${cardOn && charPersona ? `\n${charPersona.slice(0, 300)}` : ''}\nThe user is ${user}.]\n` +
        (persona ? `[${user} is:\n${persona}]\n` : '') +
        (lore ? `[Lore and world entries — people described here count as part of the cast:\n${lore}]\n` : '') +
        (authorNote ? `[Standing note about this story — it is true and current:\n${authorNote}]\n` : '') +
        (notes ? `[Notes pinned on ${user}'s board:\n${notes}]\n` : '') +
        `\n[STOP THE ROLEPLAY. This is a data request, not a scene. Do not answer in character.]\n` +
        `${task}\n\n${rules}\n\n` +
        `Output the JSON object now. The first character of your reply must be "{" and the last must be "}".`;

    await showBusy(preset[4]);
    let res = '';
    try {
        const messages = [
            { role: 'system', content: sys },
            ...chatTurns(stCtx, ctxSize),
            { role: 'user', content: ask },
        ];
        // A tree is a document, not a remark: ask for room enough to finish one,
        // and retry the failures that are worth retrying.
        res = await withRetries(() => fetchFromLLM(messages, null, 6000), preset[4]);
        const data = parseTreeJson(res);
        const tree = data ? normalizeTree(data, preset) : null;
        if (!tree || !tree.nodes.length) {
            console.warn(LOG, 'tree reply was not usable. Raw reply follows:');
            console.warn(res);
            lastTreeReply = res;
            throw new Error(treeFailureHint(res));
        }
        if (card) {
            // Rebuilding an existing tree keeps how it looks; only the content changes.
            const keep = { layout: card.tree?.layout, skin: card.tree?.skin };
            card.tree = { ...tree, layout: keep.layout || tree.layout, skin: keep.skin || tree.skin };
            ensureTree(card);
            repaintTree(card);
            save(true);
            openTreePanel(card);
        } else {
            const made = addTreeCard(tree);
            openTreePanel(made);
        }
        toastr?.success(`Готово: ${tree.nodes.length} чел., ${tree.edges.length} связей`);
    } catch (err) {
        console.error(LOG, err);
        // Tavern reports every failed request as the same "API request failed",
        // including a plain 429 from the provider — which is the usual cause and
        // the one thing the user can simply wait out.
        const msg = String(err?.message || err);
        const hint = /request failed|network|fetch/i.test(msg)
            ? 'провайдер отклонил запрос пять раз подряд. Чаще всего это лимит запросов в минуту (429) — подождите минуту и нажмите ещё раз. Точный код ошибки виден в консоли (F12) во вкладке Network.'
            : msg;
        toastr?.error('Не вышло построить дерево: ' + hint, '', { timeOut: 9000 });
    } finally {
        hideBusy();
    }
}

// ===== NOTE MARKUP =====
// Notes are stored as plain text and always have been; this is a rendering layer
// on top of that, so nothing that already exists on a board changes meaning. The
// editor still shows the raw text — what you type is what is stored.
//
// The point of the exercise is the spoiler: a long description, a secret, or a
// three-page prompt can sit on the board as a single folded line and open when
// it is actually wanted.
const SPOILER_RE = /\[(?:spoiler|спойлер)(?:[=:]([^\]]*))?\]([\s\S]*?)\[\/(?:spoiler|спойлер)\]/gi;

function inlineMarkup(s) {
    return s
        // ||hidden|| — blurred until tapped
        .replace(/\|\|([\s\S]+?)\|\|/g, '<span class="mb-inline-spoiler" title="Показать">$1</span>')
        .replace(/\*\*\*([^*\n]+)\*\*\*/g, '<b><i>$1</i></b>')
        .replace(/\*\*([^*\n]+)\*\*/g, '<b>$1</b>')
        .replace(/\*([^*\n]+)\*/g, '<i>$1</i>')
        .replace(/__([^_\n]+)__/g, '<u>$1</u>')
        .replace(/~~([^~\n]+)~~/g, '<s>$1</s>')
        .replace(/`([^`\n]+)`/g, '<code>$1</code>')
        .replace(/^#{1,3}\s*(.+)$/gm, '<b class="mb-note-h">$1</b>')
        .replace(/^&gt;\s?(.*)$/gm, '<span class="mb-note-quote">$1</span>')
        .replace(/\n/g, '<br>');
}

function renderNote(text) {
    let s = escHtml(text || '');
    // Block spoilers are lifted out first so their bodies don't get line-broken
    // by the inline pass, then dropped back in.
    const blocks = [];
    s = s.replace(SPOILER_RE, (m, title, body) => {
        const t = (title || '').trim() || 'Спойлер';
        const i = blocks.push(
            `<div class="mb-spoiler"><div class="mb-spoiler-head">` +
            `<i class="fa-solid fa-chevron-right mb-spoiler-caret"></i><span>${inlineMarkup(t)}</span></div>` +
            `<div class="mb-spoiler-body"><div class="mb-spoiler-inner">` +
            `${inlineMarkup(body.replace(/^\n+|\n+$/g, ''))}</div></div></div>`) - 1;
        return `@@mbsp${i}@@`;
    });
    s = inlineMarkup(s);
    // Swallow the line breaks around a folded block: it is already a block.
    return s.replace(/(?:<br>)?@@mbsp([0-9]+)@@(?:<br>)?/g, (m, i) => blocks[+i]);
}

// What the character is told a note says. Spoilers are content, not secrets from
// the AI — but the markup itself is noise, so it comes off.
function plainNote(text) {
    return String(text || '')
        .replace(SPOILER_RE, (m, title, body) => `${(title || '').trim() ? (title.trim() + ': ') : ''}${body.trim()}`)
        .replace(/\|\|([\s\S]+?)\|\|/g, '$1')
        .replace(/\*{1,3}([^*\n]+)\*{1,3}/g, '$1')
        .replace(/__([^_\n]+)__/g, '$1')
        .replace(/~~([^~\n]+)~~/g, '$1')
        .replace(/`([^`\n]+)`/g, '$1')
        .replace(/^#{1,3}\s*/gm, '')
        .trim();
}

// A tap that opened a spoiler must not also be read as "start dragging this
// card" — the card's own pointerdown already armed a drag.
function endCardTap() {
    clearTimeout(cardHoldTimer); cardHoldTimer = null;
    if (dragCard) {
        dragCard.el.removeClass('dragging is-dragging').css({ transform: '', 'z-index': dragCard.card.z || 1 });
        dragCard = null;
    }
}

function bindNoteMarkup($card) {
    // The card's own handler bows out of anything that starts on a spoiler, so
    // by the time the finger lifts there is no drag to second-guess — the press
    // was for this and nothing else.
    $card.find('.mb-spoiler-head').on('pointerup', function(e) {
        e.stopPropagation();
        $(this).closest('.mb-spoiler').toggleClass('open');
        if (navigator.vibrate) navigator.vibrate(8);
        // The card just grew or shrank; threads tied to it have to be re-aimed
        // once the fold has finished animating.
        linkGeomDirty = true;
        setTimeout(() => { linkGeomDirty = true; renderInk(); scheduleCull(); }, 320);
        endCardTap();
    });
    $card.find('.mb-inline-spoiler').on('pointerup', function(e) {
        e.stopPropagation();
        $(this).toggleClass('revealed');
        endCardTap();
    });
    // A card can hold several folds; one button opens or closes the lot.
    // Rebuilt from scratch each time, because this runs again after every edit.
    $card.find('.mb-card-act-btn.folds').remove();
    const $folds = $card.find('.mb-spoiler');
    if ($folds.length + $card.find('.mb-inline-spoiler').length > 1) {
        $card.find('.mb-card-actions').append(
            `<div class="mb-card-act-btn folds" title="Раскрыть или свернуть всё скрытое"><i class="fa-solid fa-eye"></i></div>`);
        $card.find('.folds').on('pointerup', function(e) {
            e.stopPropagation();
            const openAll = $card.find('.mb-spoiler.open').length < $folds.length;
            $folds.toggleClass('open', openAll);
            $card.find('.mb-inline-spoiler').toggleClass('revealed', openAll);
            $(this).find('i').attr('class', openAll ? 'fa-solid fa-eye-slash' : 'fa-solid fa-eye');
            linkGeomDirty = true;
            setTimeout(() => { linkGeomDirty = true; renderInk(); }, 320);
        });
    }
}

// ===== INK LAYER (vector strokes) =====
// Strokes are stored as points in board coordinates and re-rendered every frame
// onto a viewport-sized, device-pixel canvas. Two consequences that matter:
// committed lines are as crisp as the live preview at any zoom (a raster board
// canvas had to be upscaled and looked blocky), and saving a drawing is a few KB
// of numbers instead of a multi-megabyte PNG.
const SHAPE_KINDS = ['rect','circle','ellipse','triangle','line','diamond','star'];
let shapeKind = 'rect';

function boardStrokes() {
    const b = getBoard();
    if (!Array.isArray(b.strokes)) b.strokes = [];
    return b.strokes;
}

// Chaikin-style smoothing: draw through the midpoints of consecutive samples with
// quadratic curves, which removes the hand jitter that makes raw polylines look
// twitchy. `pts` is a flat [x,y,x,y,...] array in board coordinates.
function tracePath(ctx, pts, project) {
    const n = pts.length / 2;
    if (n === 0) return;
    const P = i => project({ x: pts[i*2], y: pts[i*2+1] });
    ctx.beginPath();
    const p0 = P(0);
    ctx.moveTo(p0.x, p0.y);
    if (n === 1) { ctx.lineTo(p0.x + 0.01, p0.y); return; }
    if (n === 2) { const p1 = P(1); ctx.lineTo(p1.x, p1.y); return; }
    let prev = p0;
    for (let i = 1; i < n - 1; i++) {
        const cur = P(i), next = P(i + 1);
        const mx = (cur.x + next.x) / 2, my = (cur.y + next.y) / 2;
        ctx.quadraticCurveTo(cur.x, cur.y, mx, my);
        prev = { x: mx, y: my };
    }
    const last = P(n - 1);
    ctx.lineTo(last.x, last.y);
}

function traceShape(ctx, kind, a, b) {
    const x = Math.min(a.x, b.x), y = Math.min(a.y, b.y);
    const w = Math.abs(b.x - a.x), h = Math.abs(b.y - a.y);
    const cx = x + w / 2, cy = y + h / 2;
    ctx.beginPath();
    switch (kind) {
        case 'circle': {
            const r = Math.max(w, h) / 2;
            ctx.arc(cx, cy, r, 0, Math.PI * 2);
            break;
        }
        case 'ellipse':
            ctx.ellipse(cx, cy, w / 2, h / 2, 0, 0, Math.PI * 2);
            break;
        case 'triangle':
            ctx.moveTo(cx, y); ctx.lineTo(x + w, y + h); ctx.lineTo(x, y + h); ctx.closePath();
            break;
        case 'diamond':
            ctx.moveTo(cx, y); ctx.lineTo(x + w, cy); ctx.lineTo(cx, y + h); ctx.lineTo(x, cy); ctx.closePath();
            break;
        case 'line':
            ctx.moveTo(a.x, a.y); ctx.lineTo(b.x, b.y);
            break;
        case 'star': {
            const R = Math.max(w, h) / 2, r = R * 0.42;
            for (let i = 0; i < 10; i++) {
                const ang = -Math.PI / 2 + i * Math.PI / 5;
                const rad = i % 2 ? r : R;
                const px = cx + Math.cos(ang) * rad, py = cy + Math.sin(ang) * rad;
                i ? ctx.lineTo(px, py) : ctx.moveTo(px, py);
            }
            ctx.closePath();
            break;
        }
        default:
            ctx.rect(x, y, w, h);
    }
}

function strokeBounds(pts) {
    let x0 = Infinity, y0 = Infinity, x1 = -Infinity, y1 = -Infinity;
    for (let i = 0; i < pts.length; i += 2) {
        if (pts[i] < x0) x0 = pts[i]; if (pts[i] > x1) x1 = pts[i];
        if (pts[i+1] < y0) y0 = pts[i+1]; if (pts[i+1] > y1) y1 = pts[i+1];
    }
    return [x0, y0, x1, y1];
}

// Brushes differ in more than thickness: alpha, join style, glow and dashing all
// change how a line reads. Everything here is per-stroke, so old strokes keep the
// look they were drawn with.
const BRUSHES = [
    ['pen',        'Перо',        'pen-nib'],
    ['marker',     'Маркер',      'highlighter'],
    ['neon',       'Неон',        'bolt-lightning'],
    ['pencil',     'Карандаш',    'pencil'],
    ['chalk',      'Мел',         'cloud'],
    ['dashed',     'Пунктир',     'ellipsis'],
    ['ribbon',     'Лента',       'ribbon'],
];

function applyBrush(ctx, br, w, color) {
    ctx.setLineDash([]);
    ctx.shadowBlur = 0; ctx.shadowColor = 'transparent';
    ctx.globalAlpha = 1;
    ctx.lineCap = 'round'; ctx.lineJoin = 'round';
    switch (br) {
        case 'marker':
            ctx.globalAlpha = 0.4; ctx.lineWidth = w * 2.6;
            ctx.lineCap = 'butt'; ctx.lineJoin = 'bevel';
            break;
        case 'neon':
            ctx.shadowColor = color; ctx.shadowBlur = w * 3.5;
            ctx.lineWidth = Math.max(0.5, w * 0.7);
            break;
        case 'pencil':
            ctx.globalAlpha = 0.55; ctx.lineWidth = Math.max(0.4, w * 0.75);
            break;
        case 'chalk':
            ctx.globalAlpha = 0.32; ctx.lineWidth = w * 1.6; ctx.lineCap = 'butt';
            break;
        case 'dashed':
            ctx.setLineDash([w * 2.2, w * 2.2]);
            break;
        case 'ribbon':
            ctx.lineWidth = w * 1.8; ctx.lineCap = 'butt'; ctx.lineJoin = 'miter';
            break;
        default:
            break;   // pen: plain round line
    }
}

function paintStroke(ctx, s, project, scaleForWidth) {
    ctx.save();
    ctx.globalCompositeOperation = s.t === 'eraser' ? 'destination-out' : 'source-over';
    ctx.strokeStyle = s.c || '#000';
    ctx.fillStyle = s.c || '#000';
    ctx.lineWidth = Math.max(0.4, (s.t === 'eraser' ? s.w * 5 : s.w) * scaleForWidth);
    ctx.lineCap = 'round'; ctx.lineJoin = 'round';
    // Freehand lines carry a brush; the eraser and the shape tools stay plain.
    if (s.t === 'draw' && s.br && s.br !== 'pen') {
        applyBrush(ctx, s.br, (s.w || 3) * scaleForWidth, s.c || '#000');
    }
    const n = s.p.length / 2;
    if (s.t === 'arrow' && n >= 2) {
        const a = project({ x: s.p[0], y: s.p[1] });
        const b = project({ x: s.p[(n-1)*2], y: s.p[(n-1)*2+1] });
        drawArrowPath(ctx, a, b, s.w * scaleForWidth);
    } else if (s.t === 'shape' && n >= 2) {
        const a = project({ x: s.p[0], y: s.p[1] });
        const b = project({ x: s.p[(n-1)*2], y: s.p[(n-1)*2+1] });
        traceShape(ctx, s.s || 'rect', a, b);
        ctx.stroke();
    } else {
        tracePath(ctx, s.p, project);
        ctx.stroke();
        // Chalk gets a second, offset pass so the edge breaks up instead of
        // reading as a flat translucent band.
        if (s.t === 'draw' && s.br === 'chalk') {
            ctx.globalAlpha *= 0.6;
            ctx.lineWidth *= 0.5;
            ctx.translate(ctx.lineWidth * 0.4, -ctx.lineWidth * 0.3);
            tracePath(ctx, s.p, project);
            ctx.stroke();
        }
    }
    ctx.restore();
    ctx.globalCompositeOperation = 'source-over';
}

// Redraws the whole ink layer for the current camera. Called from the same rAF
// that applies the pan/zoom transform, so it stays in step with the cards.
let inkDirty = true;
let inkPainted = false;
function renderInk() {
    if (!liveCtx || !liveCanvas) return;
    const area = document.getElementById('mb-canvas-area');
    if (!area) return;
    const strokes = boardStrokes();
    const hasLive = isDrawing && strokePts.length >= 2;
    const tl = getBoard().timeline;
    // Threads and the timeline share this layer: both are board furniture that
    // has to sit under the cards and follow the camera exactly as ink does.
    const hasFurniture = boardLinks().length || linkDraft || (tl && tl.on);
    // This runs from the same rAF as the pan transform, so on a board with nothing
    // drawn on it we were clearing two full-screen canvases on every single frame
    // for nothing.
    if (!strokes.length && !hasLive && !hasFurniture) {
        if (inkPainted) { resizeLive(); clearLive(); inkPainted = false; }
        return;
    }
    resizeLive();
    clearLive();
    inkPainted = true;
    const project = p => ({ x: p.x * zoom + panX, y: p.y * zoom + panY });
    renderTimeline(liveCtx, project, zoom);
    renderLinks(liveCtx, project, zoom);
    // Only touch strokes whose bounds intersect the viewport.
    const vx0 = -panX / zoom, vy0 = -panY / zoom;
    const vx1 = (area.clientWidth - panX) / zoom, vy1 = (area.clientHeight - panY) / zoom;
    for (const s of strokes) {
        if (!s.p || s.p.length < 2) continue;
        const b = s.b || strokeBounds(s.p);
        const pad = (s.w || 3) * 3;
        if (b[0] - pad > vx1 || b[1] - pad > vy1 || b[2] + pad < vx0 || b[3] + pad < vy0) continue;
        // `a` marks a stroke drawn on top of the cards — it goes on the second
        // canvas, which sits above them.
        paintStroke(s.a ? topCtx : liveCtx, s, project, zoom);
    }
    if (isDrawing && strokePts.length >= 2) {
        const live = { t: tool, c: drawColor, w: drawSize, s: shapeKind, br: brushKind, p: strokePts };
        paintStroke(drawAbove ? topCtx : liveCtx, live, project, zoom);
    }
    inkDirty = false;
}

// Screen-sized canvases at device resolution: one under the cards, one over them.
function resizeLive() {
    if (!liveCanvas) return;
    const area = document.getElementById('mb-canvas-area');
    if (!area) return;
    // The ink layer is repainted for every pan frame, so on a phone — where the
    // pixel ratio is often 3 — full device resolution costs several times what the
    // extra sharpness is worth on a hand-drawn line.
    const cap = window.innerWidth <= 768 ? 1.5 : 2;
    const dpr = Math.min(window.devicePixelRatio || 1, cap);
    const w = Math.max(1, Math.round(area.clientWidth * dpr));
    const h = Math.max(1, Math.round(area.clientHeight * dpr));
    for (const [cv, cx] of [[liveCanvas, liveCtx], [topCanvas, topCtx]]) {
        if (!cv || !cx) continue;
        if (cv.width !== w || cv.height !== h) { cv.width = w; cv.height = h; }
        cx.setTransform(dpr, 0, 0, dpr, 0, 0);
        cx.lineCap = 'round'; cx.lineJoin = 'round';
    }
}
function clearLive() {
    for (const [cv, cx] of [[liveCanvas, liveCtx], [topCanvas, topCtx]]) {
        if (!cv || !cx) continue;
        cx.save();
        cx.setTransform(1, 0, 0, 1, 0, 0);
        cx.clearRect(0, 0, cv.width, cv.height);
        cx.restore();
    }
}
function toScreen(p) { return { x: p.x * zoom + panX, y: p.y * zoom + panY }; }

// Appends a sample, dropping ones too close to the previous point (in screen
// space, so the threshold behaves the same at every zoom level) and easing each
// new point toward the last. Both together are what make the line come out clean
// instead of tracking every wobble of a finger.
function pushPoint(p) {
    const n = strokePts.length;
    if (n === 0) { strokePts.push(p.x, p.y); return true; }
    const lx = strokePts[n-2], ly = strokePts[n-1];
    const dx = (p.x - lx) * zoom, dy = (p.y - ly) * zoom;
    if (dx*dx + dy*dy < 4) return false;          // < 2 screen px: ignore
    // Ease toward the raw sample rather than taking it outright. 0.7 kills finger
    // jitter while staying close enough to the touch that it doesn't feel laggy.
    const a = 0.7;
    strokePts.push(lx + (p.x - lx) * a, ly + (p.y - ly) * a);
    return true;
}

function cancelStroke() {
    isDrawing = false;
    strokePts = [];
    innerRect = null;
    renderInk();
}
function commitStroke() {
    isDrawing = false;
    innerRect = null;
    if (strokePts.length < 2) { strokePts = []; renderInk(); return; }
    const pts = strokePts.map(v => Math.round(v * 10) / 10); // 0.1px is plenty, keeps JSON small
    const s = { t: tool, c: drawColor, w: drawSize, p: pts, b: strokeBounds(pts) };
    if (tool === 'draw' && brushKind !== 'pen') s.br = brushKind;
    if (drawAbove) s.a = 1;
    if (tool === 'shape') s.s = shapeKind;
    if (tool === 'arrow' || tool === 'shape') {
        // Only the endpoints matter; drop the intermediate samples.
        const n = pts.length;
        s.p = [pts[0], pts[1], pts[n-2], pts[n-1]];
        s.b = strokeBounds(s.p);
    }
    boardStrokes().push(s);
    pushUndo({ type: 'stroke' });
    // The eraser has to bite through the legacy raster layer too, or old drawings
    // would be un-erasable.
    if (tool === 'eraser' && getBoard().drawings && drawCtx) {
        drawCtx.globalCompositeOperation = 'destination-out';
        drawCtx.lineWidth = drawSize * 5;
        drawCtx.lineCap = 'round'; drawCtx.lineJoin = 'round';
        tracePath(drawCtx, pts, p => p);
        drawCtx.stroke();
        drawCtx.globalCompositeOperation = 'source-over';
        saveDrawing();
    }
    strokePts = [];
    renderInk();
    save();
}
// ===== UNDO =====
// The button used to know about pencil strokes and nothing else, so deleting a
// card by accident — the one thing you actually want back — reported that there
// was nothing to undo. Every destructive action now leaves a note here, and the
// button walks back through them in the order they happened, per board.
const undoStack = [];
const UNDO_MAX = 50;
function pushUndo(entry) {
    entry.board = boardKey();
    undoStack.push(entry);
    if (undoStack.length > UNDO_MAX) undoStack.shift();
}
function undoLast() {
    const key = boardKey();
    let i = undoStack.length - 1;
    while (i >= 0 && undoStack[i].board !== key) i--;
    if (i < 0) { toastr?.info('Нечего отменять на этой доске'); return; }
    const e = undoStack.splice(i, 1)[0];
    const board = getBoard();

    if (e.type === 'stroke') {
        const st = boardStrokes();
        if (st.length) st.pop();
        renderInk(); save();
        toastr?.info('Штрих отменён', '', { timeOut: 1200 });
        return;
    }
    if (e.type === 'card') {
        if (!Array.isArray(board.cards)) board.cards = [];
        board.cards.splice(Math.min(e.index, board.cards.length), 0, e.card);
        if (e.links?.length) boardLinks().push(...e.links);
        renderCard(e.card, true);
        linkGeomDirty = true;
        save(); renderInk();
        toastr?.success('Карточка возвращена');
        return;
    }
    if (e.type === 'clear') {
        board.cards = e.cards;
        board.links = e.links;
        board.strokes = e.strokes;
        board.drawings = e.drawings;
        renderBoard();
        save(true); renderInk();
        toastr?.success('Доска восстановлена');
    }
}
// Ends a drag when a second finger arrives. Keeps whatever movement already
// happened rather than snapping the card back.
function cancelDrag() {
    if (!dragCard) return;
    if (dragCard.dx || dragCard.dy) {
        dragCard.card.x = dragCard.origX + dragCard.dx;
        dragCard.card.y = dragCard.origY + dragCard.dy;
        dragCard.el.css({ left: dragCard.card.x, top: dragCard.card.y });
        save();
    }
    dragCard.el.removeClass('dragging is-dragging').css({ transform: '', 'z-index': dragCard.card.z || 1 });
    dragCard = null;
}

// ===== PAN / ZOOM =====
function onPointerDown(e) {
    if (dragCard) return;
    // pointerdown for a second finger can arrive before touchstart updates the
    // counter, so also reject non-primary touch pointers outright.
    if (e.pointerType === 'touch' && e.isPrimary === false) return;
    if (isPinching || (e.pointerType === 'touch' && activeTouches > 1)) return;
    if (activeLink) closeLinkMenu();   // any press on the board dismisses it
    const isDraw = ['draw','arrow','shape','eraser'].includes(tool);
    // Anywhere on the board counts, not just a direct hit on the canvas element:
    // panels and toolbars are excluded, everything else inside the board is fair
    // game so strokes can begin on top of a card.
    const onBoard = e.target.id === 'mb-draw-canvas'
        || (!!e.target.closest?.('#mb-canvas-area')
            && !e.target.closest?.('.mb-settings-panel, .mb-shape-picker, .mb-brush-panel'));
    if (isDraw && onBoard) {
        isDrawing = true;
        innerRect = document.getElementById('mb-canvas-inner').getBoundingClientRect();
        strokePts = [];
        pushPoint(canvasPos(e));
        document.getElementById('mb-canvas-area').setPointerCapture?.(e.pointerId);
        return;
    }
    // The link tool: press on a card and pull a thread out of it. Pressing
    // anywhere else either picks up a thread that is already there, or pans.
    if (tool === 'link' && onBoard) {
        const cardEl = e.target.closest?.('.mb-card');
        if (cardEl) { commitOpenEditor(); beginLink(e, cardEl); return; }
        const hit = linkAt(e.clientX, e.clientY);
        if (hit) { openLinkMenu(hit, e.clientX, e.clientY); return; }
    }
    // Dragging the timeline axis itself. Checked before panning, or the axis
    // would never be grabbable.
    if (tool === 'select' && !e.target.closest?.('.mb-card') && timelineHit(e.clientX, e.clientY)) {
        const tl = boardTimeline();
        tlDrag = { startY: e.clientY, y0: tl.y };
        $('#mb-canvas-area').addClass('grabbing');
        document.getElementById('mb-canvas-area').setPointerCapture?.(e.pointerId);
        return;
    }
    // Panning is also allowed with the link tool: pressing empty board with it
    // does nothing else, and being unable to move the view while tying threads
    // would strand anyone without a second finger.
    if ((tool === 'select' || tool === 'link') && !$(e.target).closest('.mb-card').length) {
        commitOpenEditor();
        $('#mb-canvas-inner .mb-card.mb-touched').removeClass('mb-touched');
        isPanning = true;
        const $area = $('#mb-canvas-area');
        $area.addClass('is-panning grabbing');
        let cx = e.clientX ?? (e.originalEvent?.touches?.[0]?.clientX) ?? 0;
        let cy = e.clientY ?? (e.originalEvent?.touches?.[0]?.clientY) ?? 0;
        panOff = { x: cx - panX, y: cy - panY };
        $area[0].setPointerCapture?.(e.pointerId);
    }
}
let dragRAF = null, panRAF = null;
function onPointerMove(e) {
    if (isPinching) return;
    let cx = e.clientX ?? (e.touches?.[0]?.clientX) ?? 0;
    let cy = e.clientY ?? (e.touches?.[0]?.clientY) ?? 0;

    if (linkDraft) {
        linkDraft.to = canvasPos(e);
        if (!panRAF) panRAF = requestAnimationFrame(() => { renderInk(); panRAF = null; });
        return;
    }
    if (tlDrag) {
        boardTimeline().y = Math.round(tlDrag.y0 + (cy - tlDrag.startY) / zoom);
        if (!panRAF) panRAF = requestAnimationFrame(() => { renderInk(); panRAF = null; });
        return;
    }
    if (isPanning) {
        panX = cx - panOff.x;
        panY = cy - panOff.y;
        if (!panRAF) {
            panRAF = requestAnimationFrame(() => {
                updateTransform();
                panRAF = null;
            });
        }
        return;
    }
    if (dragCard) {
        dragCard.dx = (cx - dragCard.startX) / zoom;
        dragCard.dy = (cy - dragCard.startY) / zoom;
        if (cardHoldTimer && (Math.abs(dragCard.dx) > 4 || Math.abs(dragCard.dy) > 4)) {
            clearTimeout(cardHoldTimer); cardHoldTimer = null;   // it's a drag, not a hold
        }
        // A pinned card is held in place; the gesture is still tracked so the
        // long-press and the tap keep working on it.
        if (dragCard.card.locked) return;
        // Grid and timeline pull on the card while it is still under the finger,
        // so what you see during the drag is where it will actually land.
        applyMagnets(dragCard);
        if (!dragRAF) {
            dragRAF = requestAnimationFrame(() => {
                if (dragCard) {
                    dragCard.el[0].style.transform = `translate3d(${dragCard.dx}px, ${dragCard.dy}px, 0)`;
                    // Threads tied to this card have to follow it, not wait for
                    // the drop.
                    if (boardLinks().some(l => l.a === dragCard.card.id || l.b === dragCard.card.id)) renderInk();
                }
                dragRAF = null;
            });
        }
        return;
    }
    if (isDrawing) {
        if (tool === 'draw' || tool === 'eraser') {
            // Touch move events get coalesced when the main thread is busy;
            // replaying them keeps fast strokes smooth instead of leaving gaps.
            const raw = (typeof e.getCoalescedEvents === 'function') ? e.getCoalescedEvents() : null;
            const evs = (raw && raw.length) ? raw : [e];
            for (const ev of evs) pushPoint(canvasPos(ev));
        } else {
            // arrow / shape: keep the anchor, replace the moving endpoint
            const pos = canvasPos(e);
            strokePts.length = 2;
            strokePts.push(pos.x, pos.y);
        }
        // Painting happens in the shared rAF so a burst of moves costs one repaint.
        if (!panRAF) {
            panRAF = requestAnimationFrame(() => { renderInk(); panRAF = null; });
        }
        return;
    }
}
// Closes any open note editor, committing its text. Relying on the browser to
// blur it when you touch something else is not enough on mobile, where the
// keyboard can keep focus alive and the edit would never be written back.
function commitOpenEditor(except) {
    // Booth captions are editable too, so they belong in the same sweep.
    const open = document.querySelector(
        '.mb-card-content[contenteditable="true"], .mb-booth-caption[contenteditable="true"]');
    if (!open || open === except) return;
    open.blur();
    // Safari/older WebKit can ignore blur() on an element the keyboard owns.
    if (open.getAttribute('contenteditable') === 'true') $(open).triggerHandler('blur');
}

// Second tap on a collage tile asks for a new picture for that tile. The caption
// is not handled here any more — it is text, and all text is typed in the panel.
function openCollagePart(card, $card, e) {
    const hit = document.elementFromPoint(e.clientX, e.clientY);
    if (!hit) return;
    if (hit.closest('.mb-booth-caption')) { openStylePanel(card, $card); return; }
    const cell = hit.closest('.mb-collage-cell');
    if (cell && $card[0].contains(cell)) {
        replaceCollageCell(card, parseInt(cell.dataset.i, 10), $card);
    }
}


function onPointerUp(e) {
    clearTimeout(cardHoldTimer); cardHoldTimer = null;
    if (linkDraft) { finishLink(e); return; }
    if (tlDrag) {
        tlDrag = null;
        $('#mb-canvas-area').removeClass('grabbing');
        save(); renderInk();
        return;
    }
    if (dragCard) {
        // While picking, a tap just adds or removes the card from the selection.
        if (selectMode) {
            const id = dragCard.card.id;
            dragCard.el.removeClass('dragging is-dragging').css({ transform: '', 'z-index': dragCard.card.z || 1 });
            const moved = Math.abs(dragCard.dx) > 2 || Math.abs(dragCard.dy) > 2;
            dragCard = null;
            if (!moved) togglePicked(id);
            return;
        }
        const moved = !dragCard.card.locked && (Math.abs(dragCard.dx) > 2 || Math.abs(dragCard.dy) > 2);
        if (moved) {
            dragCard.card.x = dragCard.origX + dragCard.dx;
            dragCard.card.y = dragCard.origY + dragCard.dy;
            dragCard.el.css({ left: dragCard.card.x, top: dragCard.card.y, transform: '' });
            save();
        } else {
            // A tap (no real movement) selects the card — on touch there is no
            // hover, so this is what reveals the actions and the resize handle.
            dragCard.el.css('transform', '');
            const wasOn = dragCard.el.hasClass('mb-touched');
            $('#mb-canvas-inner .mb-card').removeClass('mb-touched');
            dragCard.el.addClass('mb-touched');
            // A tap reveals the card's buttons; a second tap opens whatever the
            // card is made of. Notes are deliberately not in this list any more:
            // their editor lives on the pencil button. Tapping a note used to
            // summon the keyboard, which meant a spoiler could not be opened at
            // all — the tap that should have unfolded it opened the editor and
            // replaced the spoiler with its raw text.
            if (wasOn && !dragCard.card.locked) {
                if (dragCard.card.type === 'collage') openCollagePart(dragCard.card, dragCard.el, e);
                else if (dragCard.card.type === 'tree') openTreePanel(dragCard.card, dragCard.el);
            }
        }
        dragCard.el.removeClass('dragging is-dragging').css('z-index', dragCard.card.z || 1);
        dragCard = null;
        scheduleCull();
        return;
    }
    if (isPanning) {
        isPanning = false;
        $('#mb-canvas-area').removeClass('is-panning grabbing');
        saveCamera();
    }
    if (isDrawing) commitStroke();
}

// `width` is passed in because the preview draws in screen pixels and the commit
// draws in board pixels.
function drawArrowPath(ctx, from, to, width) {
    ctx.lineWidth = Math.max(0.5, width); ctx.lineCap = 'round';
    ctx.beginPath(); ctx.moveTo(from.x, from.y); ctx.lineTo(to.x, to.y); ctx.stroke();
    const a = Math.atan2(to.y - from.y, to.x - from.x), hl = 12 + width * 2;
    ctx.beginPath(); ctx.moveTo(to.x, to.y);
    ctx.lineTo(to.x - hl * Math.cos(a - 0.4), to.y - hl * Math.sin(a - 0.4));
    ctx.lineTo(to.x - hl * Math.cos(a + 0.4), to.y - hl * Math.sin(a + 0.4));
    ctx.closePath(); ctx.fill();
}

// Cache the inner rect for the duration of a stroke — reading it per pointer event
// forces a layout flush on every move.
let innerRect = null;
function canvasPos(e) {
    const r = innerRect || document.getElementById('mb-canvas-inner').getBoundingClientRect();
    return { x: (e.clientX - r.left) / zoom, y: (e.clientY - r.top) / zoom };
}

function onWheel(e) {
    // Every panel is a child of the canvas area, so its wheel events reach this
    // handler. Without this the board zooms while you are trying to scroll a
    // list — which is what the tall "style of reply" menu did on a mouse, since
    // it is a pop-over rather than one of the side panels.
    if (e.target?.closest?.('.mb-settings-panel, .mb-shape-picker, .mb-brush-panel, .mb-select-options, .mb-dialog-back')) return;
    e.preventDefault();
    const delta = e.deltaY > 0 ? 0.9 : 1.1;
    const newZoom = Math.max(0.05, Math.min(5, zoom * delta));
    const rect = document.getElementById('mb-canvas-area').getBoundingClientRect();
    const mx = e.clientX - rect.left, my = e.clientY - rect.top;
    panX = mx - (mx - panX) * (newZoom / zoom);
    panY = my - (my - panY) * (newZoom / zoom);
    zoom = newZoom;
    updateTransform(); showZoom();
    saveCamera();
}

// Zoom, and only zoom, changes how many device pixels a picture covers — so it
// is the one thing that can change which copy a card should be showing. Panning
// cannot. Debounced past the end of the gesture: swapping sources mid-pinch
// would decode new bitmaps in the middle of the only moment that has to stay
// smooth.
let tierZoom = -1, tierTimer = null;
function scheduleTierCheck() {
    if (Math.abs(zoom - tierZoom) < 0.001) return;
    clearTimeout(tierTimer);
    tierTimer = setTimeout(() => { tierZoom = zoom; refreshImgTiers(); }, 250);
}

function updateTransform() {
    const inner = document.getElementById('mb-canvas-inner');
    if (inner) inner.style.transform = `translate3d(${panX}px, ${panY}px, 0) scale(${zoom})`;
    renderInk();   // the ink layer lives in screen space, so it follows the camera
    scheduleCull();
    scheduleTierCheck();
}

// ===== VIEWPORT CULLING =====
// Boards with a lot of images spend most of their frame budget painting cards that
// are nowhere near the screen. `visibility:hidden` skips the paint without
// touching layout, so stored coordinates and the drag math stay untouched.
let cullTimer = null;
// Anything that rasterizes the board has to hold the culler off for the whole
// operation, not just wake the cards up once at the start: a capture waits for a
// dialog and for images to decode, and a cull landing in one of those gaps used
// to put cards back to sleep and drop them out of the finished picture.
let cullPaused = 0;
function pauseCull() { cullPaused++; }
function resumeCull() { cullPaused = Math.max(0, cullPaused - 1); scheduleCull(); }
function scheduleCull() {
    if (cullTimer) return;
    cullTimer = setTimeout(() => { cullTimer = null; cullCards(); }, 100);
}

// A transparent 1x1 GIF. Pointing an <img> at this is what actually hands the
// decoded bitmap back to the system: `visibility: hidden` skips the paint but the
// full-size pixels stay in memory, and thirty or forty photos of them is what
// leaves a phone thrashing. The real source waits in a data attribute.
const BLANK_PX = 'data:image/gif;base64,R0lGODlhAQABAIAAAAAAAP///ywAAAAAAQABAAACAUwAOw==';

// `boxes` comes from the read pass: the blank pixel must be pinned to exactly the
// size the real picture had, or the card would collapse and every measurement
// that follows — export bounds, culling, the drag math — would be taken against
// the wrong geometry.
function unloadCardPixels(el, boxes) {
    for (const [img, w, h] of boxes) {
        const src = img.getAttribute('src');
        if (!src || src === BLANK_PX) continue;
        img.dataset.mbSrc = src;
        if (w && h) { img.style.width = w + 'px'; img.style.height = h + 'px'; }
        img.setAttribute('src', BLANK_PX);
    }
    el.dataset.mbUnloaded = '1';
}
function restoreCardPixels(el) {
    if (el.dataset.mbUnloaded !== '1') return;
    delete el.dataset.mbUnloaded;
    el.querySelectorAll('img').forEach(img => {
        const src = img.dataset.mbSrc;
        if (!src) return;
        delete img.dataset.mbSrc;
        img.style.width = ''; img.style.height = '';
        img.setAttribute('src', src);
    });
}
function uncullCards() {
    document.querySelectorAll('#mb-canvas-inner .mb-card').forEach(el => {
        el.style.visibility = '';
        restoreCardPixels(el);
    });
}
// Anything that rasterizes the board needs the pictures actually decoded, not
// merely assigned. Call after uncullCards().
async function awaitCardImages() {
    const waits = [];
    document.querySelectorAll('#mb-canvas-inner .mb-card img').forEach(img => {
        if (!img.complete && typeof img.decode === 'function') waits.push(img.decode().catch(() => {}));
    });
    await Promise.all(waits);
}

function cullCards() {
    if (cullPaused) return;
    const area = document.getElementById('mb-canvas-area');
    if (!area || !$('#mb-modal').is(':visible')) return;
    const els = document.querySelectorAll('#mb-canvas-inner .mb-card');
    if (els.length < 12) { uncullCards(); return; } // not worth it on small boards
    const margin = 400 / zoom;
    const x0 = -panX / zoom - margin, y0 = -panY / zoom - margin;
    const x1 = (area.clientWidth - panX) / zoom + margin;
    const y1 = (area.clientHeight - panY) / zoom + margin;
    // Pixels are dropped much further out than paint is: a card coming back into
    // view has to have its picture again *before* it is on screen, or panning
    // would show blanks filling in behind the finger.
    const keep = Math.max(1400, area.clientWidth, area.clientHeight) / zoom;
    const kx0 = -panX / zoom - keep, ky0 = -panY / zoom - keep;
    const kx1 = (area.clientWidth - panX) / zoom + keep;
    const ky1 = (area.clientHeight - panY) / zoom + keep;
    const dragEl = dragCard?.el?.[0];

    // Two passes on purpose. Reading a card's geometry right after writing to the
    // previous one forces the browser to re-resolve layout each time round, which
    // on a big board costs more than the culling saves.
    const plan = [];
    for (const el of els) {
        if (el === dragEl) { plan.push([el, '', true, null]); continue; }
        const x = el.offsetLeft, y = el.offsetTop;
        const w = el.offsetWidth || 220, h = el.offsetHeight || 220;
        const visible = !(x > x1 || y > y1 || x + w < x0 || y + h < y0);
        const keepPixels = !(x > kx1 || y > ky1 || x + w < kx0 || y + h < ky0);
        let boxes = null;
        if (!keepPixels && el.dataset.mbUnloaded !== '1') {
            boxes = [];
            el.querySelectorAll('img').forEach(img => boxes.push([img, img.offsetWidth, img.offsetHeight]));
            if (!boxes.length) boxes = null;
        }
        plan.push([el, visible ? '' : 'hidden', keepPixels, boxes]);
    }
    for (const [el, want, keepPixels, boxes] of plan) {
        if (el.style.visibility !== want) el.style.visibility = want;
        if (keepPixels) restoreCardPixels(el);
        else if (boxes) unloadCardPixels(el, boxes);
    }
}

function showZoom() {
    const ind = document.getElementById('mb-zoom-ind');
    if (!ind) return;
    ind.textContent = Math.round(zoom * 100) + '%';
    ind.classList.add('visible');
    clearTimeout(zoomTimer);
    zoomTimer = setTimeout(() => ind.classList.remove('visible'), 1200);
}

async function init() {
    $('#mb-modal, #mb-quote-popup, #mb-file-input').remove();
    attachWand(); buildUI();
    await load();
    if (!boards || typeof boards !== 'object') boards = {};
    if (!boards.global) boards.global = { cards: [] };
    if (!boards.global.stickers) boards.global.stickers = [];

    const THEMES = ['cork','auto','linen','ink','plum','forest','custom'];
    let t = localStorage.getItem('mb_theme') || 'cork';
    if (!THEMES.includes(t)) t = 'cork';   // watercolor/midnight were retired
    applyTheme(t);
    const $themeOpt = $(`#mb-theme-dropdown .mb-select-options div[data-val="${t}"]`);
    if ($themeOpt.length) $('#mb-theme-dropdown .mb-select-value').text($themeOpt.text());

    renderColorRow();
    collageLayout = localStorage.getItem('mb_collage_layout') || 'booth4';
    $('#mb-btn-collage i').attr('class', `fa-solid fa-${layoutById(collageLayout).icon}`);
    brushKind = localStorage.getItem('mb_brush') || 'pen';
    drawAbove = localStorage.getItem('mb_draw_above') === '1';
    drawSize = parseInt(localStorage.getItem('mb_draw_size'), 10) || drawSize;
    shapeKind = localStorage.getItem('mb_shape_kind') || 'rect';
    gridShow = localStorage.getItem('mb_grid_show') === '1';
    gridSnap = localStorage.getItem('mb_grid_snap') === '1';
    gridSize = parseInt(localStorage.getItem('mb_grid_size'), 10) || gridSize;
    applyGridLayer();
    const shapeIcons = { rect:'square', circle:'circle', ellipse:'egg', triangle:'play', line:'minus', diamond:'diamond', star:'star' };
    $('#mb-btn-shape i').attr('class', `fa-solid fa-${shapeIcons[shapeKind] || 'square'}`);
    if (localStorage.getItem('mb_toolbar_collapsed') === '1') {
        $('#mb-toolbar').addClass('collapsed');
        $('#mb-toolbar-toggle').addClass('collapsed').find('i').attr('class', 'fa-solid fa-chevron-down');
    }

    // The settings panel is built before the boards arrive, so its controls
    // start on defaults. Re-sync them here or the saved style silently reads as
    // "Сбалансированно" and the context slider sends 10 no matter what was set.
    syncSettingsUI();

    preloadCardFonts();
    loadCustomFonts();
    injectCustomFrameCss();
    renderFrameList();
    renderFontList();
    refreshProfilesUI();
    refreshStaleFrames();
    if (typeof eventSource !== 'undefined') {
        eventSource.on(event_types.CHAT_CHANGED, () => {
            if (drawSaveTimer) { serializeDrawing(); save(); }
            if ($('#mb-modal').is(':visible')) renderBoard();
        });
    }
    // Don't lose a debounced write if the tab goes away mid-edit.
    window.addEventListener('pagehide', () => { if (saveTimer) save(true); });
    document.addEventListener('visibilitychange', () => {
        if (document.hidden) { if (saveTimer) save(true); return; }
        // Coming back to the tab: flush anything pending, then check for edits
        // that arrived from another device while we were away.
        if (uploadTimer || uploading) return;
        pullIfNewer(true);
    });
    window.addEventListener('online', () => { if (!serverOk) queueUpload(true); });
    console.log(LOG, 'Initialized');
}

const defaultStickers = [];
function renderStickers() {
    const $grid = $('#mb-sticker-grid');
    $grid.empty();
    const mine = boards.global.stickers || [];
    const all = [...defaultStickers, ...mine];
    if (!all.length) $grid.append('<div class="mb-empty-hint">Стикеров пока нет — загрузите свои ниже.</div>');
    all.forEach((s, i) => {
        const own = i >= defaultStickers.length;
        const $s = $(`<div class="mb-sticker-item"><img src="${s}" draggable="false">
            ${own ? '<span class="mb-sticker-del" title="Удалить стикер">&times;</span>' : ''}</div>`);
        $s.on('click', e => {
            if ($(e.target).closest('.mb-sticker-del').length) return;
            addCard(s, 'sticker');
            $('#mb-stickers').removeClass('open');
        });
        $s.find('.mb-sticker-del').on('click', async e => {
            e.stopPropagation();
            if (!await mbConfirm('Удалить стикер?',
                    'Из галереи. Те, что уже стоят на досках, останутся на месте.',
                    { okLabel: 'Удалить', danger: true })) return;
            const list = boards.global.stickers || [];
            list.splice(i - defaultStickers.length, 1);
            save(true);
            renderStickers();
        });
        $grid.append($s);
    });
}

// ===== TRANSPARENT MARGINS =====
// A sticker exported from most drawing apps is a small picture in the middle of
// a big empty canvas. That emptiness is part of the file, so the card ends up
// mostly nothing: it looks tiny, sits off-centre, and the resize handle is
// somewhere out in the void. Scan the alpha channel and cut the picture out of it.
function trimTransparent(src, alphaFloor = 8) {
    return new Promise(resolve => {
        const img = new Image();
        img.crossOrigin = 'Anonymous';
        img.onload = () => {
            const w = img.naturalWidth, h = img.naturalHeight;
            if (!w || !h) { resolve({ src, trimmed: false }); return; }
            const c = document.createElement('canvas');
            c.width = w; c.height = h;
            const ctx = c.getContext('2d', { willReadFrequently: true });
            ctx.drawImage(img, 0, 0);
            let data;
            try { data = ctx.getImageData(0, 0, w, h).data; }
            catch (e) { resolve({ src, trimmed: false }); return; }   // tainted canvas
            let x0 = w, y0 = h, x1 = -1, y1 = -1;
            for (let y = 0; y < h; y++) {
                for (let x = 0; x < w; x++) {
                    if (data[(y * w + x) * 4 + 3] > alphaFloor) {
                        if (x < x0) x0 = x;
                        if (x > x1) x1 = x;
                        if (y < y0) y0 = y;
                        if (y > y1) y1 = y;
                    }
                }
            }
            if (x1 < 0) { resolve({ src, trimmed: false }); return; }   // fully transparent
            const pad = 2;   // a hair of breathing room so edges don't look shaved
            x0 = Math.max(0, x0 - pad); y0 = Math.max(0, y0 - pad);
            x1 = Math.min(w - 1, x1 + pad); y1 = Math.min(h - 1, y1 + pad);
            const nw = x1 - x0 + 1, nh = y1 - y0 + 1;
            if (nw >= w - 2 && nh >= h - 2) { resolve({ src, trimmed: false }); return; }  // nothing to cut
            const out = document.createElement('canvas');
            out.width = nw; out.height = nh;
            out.getContext('2d').drawImage(c, x0, y0, nw, nh, 0, 0, nw, nh);
            // PNG, not webp: a sticker's transparency is the whole point and
            // must survive the round trip untouched.
            resolve({ src: out.toDataURL('image/png'), trimmed: true, was: [w, h], now: [nw, nh] });
        };
        img.onerror = () => resolve({ src, trimmed: false });
        img.src = src;
    });
}

$(document).ready(() => setTimeout(init, 1500));
