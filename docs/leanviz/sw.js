/**
 * Offline for what you have already looked at.
 *
 * A bundle is 147 MB, so caching it whole is not on the table and never will be. But a reference tool is used
 * in the places references are needed, which includes trains and conference wifi, and the part a person wants
 * again is almost always the part they just had. This caches the shell always and every bundle file on the way
 * past, and falling back to it only when the network cannot be reached.
 *
 * Bundle files under data/ are content for one build: a shard's bytes do not change under a given deploy, and
 * when a deploy replaces them the version below changes with it, which drops the old cache wholesale. The page
 * itself is fetched from the network first so a new deploy is never hidden behind a stale shell.
 */
// Bumping this drops every older cache on activate. It has to change whenever the shell changes, because a
// worker that caches a broken page pins that page on the reader's machine, which is exactly what happened with
// v1: a stylesheet with a bug in it kept being served after the fix was live.
const VERSION = 'leanviz-v3';

// The shell is fetched from the network every time and only falls back to the cache when offline, so a fix is
// never hidden behind it. Nothing is served from cache while the network is available: see the fetch
// handler for why that had to change.
const SHELL = ['./', './index.html', './app.js', './style.css'];

self.addEventListener('install', (ev) => {
  // addAll fails the whole install if any one file 404s, which would leave the previous worker in charge.
  ev.waitUntil(caches.open(VERSION)
    .then(c => Promise.all(SHELL.map(u => c.add(u).catch(() => { /* one missing file must not block the update */ }))))
    .then(() => self.skipWaiting()));
});

self.addEventListener('activate', (ev) => {
  ev.waitUntil(caches.keys()
    .then(keys => Promise.all(keys.filter(k => k !== VERSION).map(k => caches.delete(k))))
    .then(() => self.clients.claim()));
});

self.addEventListener('fetch', (ev) => {
  const url = new URL(ev.request.url);
  if (ev.request.method !== 'GET' || url.origin !== self.location.origin) return;

  // Network first for everything, with the cache as the offline fallback.
  //
  // v2 served anything under /data/ from the cache first, on the reasoning that a bundle's files are immutable
  // for a build. That reasoning was wrong in a way that matters: the paths are stable across builds, so the
  // content goes stale underneath them. The worst case was data/projects.json, which is the list of libraries
  // on the site, so anyone who had visited before a library was added never saw it again. Two libraries were
  // invisible to returning readers that way.
  //
  // Nothing here is content-addressed, so nothing here can be safely served from cache while the network is
  // available. The promise this worker makes is offline access to what you have already opened, not speed, and
  // that promise is kept without ever showing anyone a stale library list.
  ev.respondWith((async () => {
    try {
      const res = await fetch(ev.request);
      if (res.ok) (await caches.open(VERSION)).put(ev.request, res.clone());
      return res;
    } catch (e) {
      const hit = await caches.match(ev.request);
      if (hit) return hit;
      throw e;
    }
  })());
});
