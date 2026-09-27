'use strict';
//
// LeanViz: a static page over the bundle the generator writes. No framework, no build step, no server.
//
// The data model is in docs/format.md and is worth knowing before changing anything here. In short: every
// declaration has a dense integer id; ids run in module dependency order and each module owns one contiguous
// range, so the shard holding an id is a binary search over the module table (moduleOfId). Three flat files,
// fetched once between them, cover everything the page needs about a declaration it is not displaying in full:
// names.txt (name per id), kinds.txt (one character per id) and used.bin (uint32 per id, how many declarations
// reference it). A shard is fetched only when a page shows one of its declarations, and at most sixty are kept.
//
// Rendering is deliberately plain: a hash route picks a page, the page builds an HTML string, and the string is
// assigned to #main. There is no virtual DOM and no state beyond S and two localStorage preferences, so every
// path through this file can be read top to bottom. Anything interpolated into HTML goes through esc().
//
// Which bundle this page is showing. One site can carry several libraries, each in its own directory under
// data/, listed in data/projects.json; ?p=<slug> picks one and the default is the first.
let DATA = 'data/';
const KIND = { a: 'axiom', d: 'def', t: 'theorem', o: 'opaque', q: 'quot', i: 'inductive', c: 'constructor', r: 'recursor', '?': 'unknown' };

/** Everything fetched so far. Populated by init and loadNames; shards is an LRU of module name to promise. */
const S = { manifest: null, modules: null, names: null, kinds: null, used: null, shards: new Map(), namesPromise: null, projects: null, project: null, graph: null, graphPromise: null };

const $ = (sel) => document.querySelector(sel);
// Names the elaborator makes up: proofs split out of a definition, equation lemmas, sizeOf lemmas, matchers,
// compiler stages. They are real declarations, so they stay in the data, but a reader rarely wants them.
// `.eq_1` and `.eq_def` are equation lemmas with a dot rather than an underscore, so the underscore forms
// below missed them; they were the bulk of every pair of declarations sharing a statement.
const GENERATED = /(^|\.)(_proof_\d+|_simp_\d+|_eq_\d+|eq_\d+|eq_def|_unfold|_sizeOf_\d+|sizeOf_spec|_cstage\d*|_spec_\d+|_elambda_\d+|_private|_aux_\d+|match_\d+|proof_\d+|_sparseCasesOn_\d+|_closed_\d+|_lambda_\d+|_rarg|_redArg|_boxed|_override|_hyg\.\d+|injEq|_lemma_\d+|_f|_g)($|\.)|✝/;
let hideGenerated = true;
try { hideGenerated = localStorage.getItem('hideGenerated') !== 'no'; } catch (e) { /* private window */ }
// A project's own declarations sit on top of every library it imports, so searching a small formalization means
// wading through Mathlib. This narrows the search to what the project itself declares.
let ownOnly = false;
try { ownOnly = localStorage.getItem('ownOnly') === 'yes'; } catch (e) { /* private window */ }
const inScope = (id) => !ownOnly || ownIds().has(id);
const isGenerated = (name) => GENERATED.test(name) || /\.\d+$/.test(name);
const keep = (id) => !hideGenerated || !isGenerated(S.names[id]);
const esc = (s) => String(s).replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/"/g, '&quot;');
const fmt = (n) => Number(n).toLocaleString('en-US');

/**
 * Fetch a bundle file. Everything large is stored gzipped, because a static host stores what it is given and the
 * whole site has a size limit; the browser decompresses. A plain path is tried first so a hand-made or older
 * bundle still works.
 */
const PLAIN = new Set(['manifest.json', 'check.json']); // small enough to be worth fetching with curl

async function fetchBundle(path) {
  if (PLAIN.has(path)) {
    const r = await fetch(DATA + path);
    if (!r.ok) throw new Error(`${path}: ${r.status}`);
    return r;
  }
  const gz = await fetch(DATA + path + '.gz');
  if (gz.ok) {
    if (typeof DecompressionStream !== 'function') {
      throw new Error('this browser cannot decompress the bundle; it needs DecompressionStream');
    }
    return new Response(gz.body.pipeThrough(new DecompressionStream('gzip')));
  }
  const plain = await fetch(DATA + path);
  if (!plain.ok) throw new Error(`${path}: ${plain.status}`);
  return plain;
}

async function fetchJson(path) {
  return (await fetchBundle(path)).json();
}

// ---------------------------------------------------------------- data

/**
 * Fetch the three flat per-id files, once per session. Every list, the search box and the picture need a name,
 * a kind and a popularity for ids they are not otherwise loading, and fetching a shard for each would be
 * thousands of requests. About 15 MB for Mathlib, gzipped by any static host.
 */
function loadNames() {
  if (S.namesPromise) return S.namesPromise;
  setStatus('loading names…');
  S.namesPromise = Promise.all([
    fetchBundle('names.txt').then(r => r.text()),
    fetchBundle('kinds.txt').then(r => r.text()),
    fetchBundle('used.bin').then(r => r.arrayBuffer()),
  ]).then(([names, kinds, used]) => {
    S.names = names.split('\n');
    if (S.names[S.names.length - 1] === '') S.names.pop();
    S.kinds = kinds;
    S.used = new Uint32Array(used);
    setStatus('');
  });
  return S.namesPromise;
}

/**
 * The ids the project itself declares, as opposed to everything it imports. A bundle for Fermat carries all of
 * Mathlib underneath it, so without this the page would lead with Mathlib's numbers and Fermat would be
 * invisible on its own landing page.
 */
function ownIds() {
  if (S.own) return S.own;
  let own = new Set(S.manifest.ownModules || []);
  if (!own.size) {
    // A bundle generated before the manifest carried this can still be worked out: every library the project
    // imports claims its own top-level names in `libraries`, and what no entry claims is the project's own.
    const claimed = new Set((S.manifest.libraries || []).flatMap(l => l.prefixes || []));
    if (claimed.size) {
      own = new Set(S.modules.filter(m => !claimed.has(m.n.split('.')[0])).map(m => m.n));
    }
  }
  const ranges = S.modules.filter(m => own.has(m.n)).map(m => [m.s, m.s + m.c]);
  S.own = {
    modules: S.modules.filter(m => own.has(m.n)),
    count: ranges.reduce((a, [lo, hi]) => a + (hi - lo), 0),
    has: (id) => ranges.some(([lo, hi]) => id >= lo && id < hi),
    ids: () => ranges.flatMap(([lo, hi]) => Array.from({ length: hi - lo }, (_, k) => lo + k)),
  };
  return S.own;
}

/** The index in S.modules of the module that owns this id: binary search, since the ranges tile the id space. */
function moduleOfId(id) {
  const m = S.modules;
  let lo = 0, hi = m.length - 1;
  while (lo < hi) {
    const mid = (lo + hi + 1) >> 1;
    if (m[mid].s <= id) lo = mid; else hi = mid - 1;
  }
  return lo;
}

/** A module's declarations, fetched on demand. The cache is bounded: Mathlib has more shards than a tab wants. */
async function shard(mi) {
  const name = S.modules[mi].n;
  if (S.shards.has(name)) return S.shards.get(name);
  const p = fetchJson('m/' + encodeURIComponent(name) + '.json');
  S.shards.set(name, p);
  if (S.shards.size > 60) S.shards.delete(S.shards.keys().next().value);
  return p;
}

async function decl(id) {
  const mi = moduleOfId(id);
  const arr = await shard(mi);
  return arr[id - S.modules[mi].s];
}

function idOfName(name) {
  return S.names.indexOf(name);
}

/** Every declaration with this name. Two modules may each declare one, and they can differ in what matters. */
function idsOfName(name) {
  const out = [];
  for (let i = S.names.indexOf(name); i !== -1; i = S.names.indexOf(name, i + 1)) {
    out.push(i);
  }
  return out;
}

/**
 * Rank declaration names against a query. Substring, case-insensitive when the query is lowercase, in four
 * buckets: exact, the last component starts with it, any component starts with it, anywhere. Within a bucket the
 * most depended-upon come first, which is what makes typing "add_comm" land on the one people mean. Generated
 * helpers sink below everything else rather than being dropped, so they can still be found by name.
 */
// Search filters, which loogle has an open request for and doc-gen4 has another. `k:theorem` keeps one kind,
// `m:Mathlib.Order` keeps a module prefix, `lib:Mathlib` keeps one library, and two bare words match a name
// containing both in any order rather than in the order they were typed.
const FILTER = /^(k|kind|m|mod|module|lib|library|c|concl|conclusion):(\S+)$/i;
function parseQuery(q) {
  const words = [], filters = { kind: null, module: null, library: null, concl: null };
  for (const w of q.trim().split(/\s+/).filter(Boolean)) {
    const m = FILTER.exec(w);
    if (!m) { words.push(w); continue; }
    const key = m[1].toLowerCase(), val = m[2];
    if (key === 'k' || key === 'kind') filters.kind = val.toLowerCase();
    else if (key === 'lib' || key === 'library') filters.library = val.toLowerCase();
    else if (key === 'c' || key === 'concl' || key === 'conclusion') filters.concl = val;
    else filters.module = val;
  }
  return { words, filters };
}

/** Which library a module belongs to, by the prefixes each one claims in the manifest. */
function libraryNameOf(moduleName) {
  const lib = libraryOf(moduleName);
  return (lib && lib.name) || (S.manifest.title || '');
}

function passesFilters(i, f) {
  if (f.kind && kindOf(i) !== f.kind) return false;
  if (f.module || f.library) {
    const mod = S.modules[moduleOfId(i)].n;
    if (f.module && mod !== f.module && !mod.startsWith(f.module + '.')) return false;
    if (f.library && !libraryNameOf(mod).toLowerCase().startsWith(f.library)) return false;
  }
  return true;
}

function search(q) {
  const names = S.names;
  if (!q) return [];
  const { words, filters } = parseQuery(q);
  const hasFilters = filters.kind || filters.module || filters.library || filters.concl;

  // Several words match a name containing all of them, in any order. Ranking then uses the longest word, so
  // "comm add nat" still puts Nat.add_comm where a reader expects it.
  if (words.length > 1) {
    const terms = words.map(w => w.toLowerCase());
    const out = [];
    for (let i = 0; i < names.length && out.length < 400; i++) {
      if (!inScope(i)) continue;
      const hay = names[i].toLowerCase();
      if (!terms.every(term => hay.includes(term))) continue;
      if (hasFilters && !passesFilters(i, filters)) continue;
      out.push(i);
    }
    out.sort((a, b) => S.used[b] - S.used[a]);
    const kept = out.filter(i => !(hideGenerated && isGenerated(names[i])));
    return (kept.length ? kept : out).slice(0, 50);
  }
  q = words[0] || '';
  if (!q) {
    // filters alone are a legitimate query: `k:axiom` is "show me the axioms"
    if (!hasFilters) return [];
    const out = [];
    for (let i = 0; i < names.length && out.length < 400; i++) {
      if (inScope(i) && passesFilters(i, filters) && !(hideGenerated && isGenerated(names[i]))) out.push(i);
    }
    return out.sort((a, b) => S.used[b] - S.used[a]).slice(0, 50);
  }
  const out = [];
  const lower = q.toLowerCase();
  const insensitive = q === lower;
  // rank: exact, then the last component starts with it, then any component starts with it, then substring
  const buckets = [[], [], [], []];
  // The scope test belongs inside this scan and not after it. Ids run in module dependency order, so a
  // project's own declarations are last; the scan stops at 400 substring hits, which it reaches inside Mathlib.
  // Filtering the result would then have nothing of the project left to keep.
  for (let i = 0; i < names.length && buckets[3].length < 400; i++) {
    if (!inScope(i)) continue;
    if (hasFilters && !passesFilters(i, filters)) continue;
    const n = names[i];
    const hay = insensitive ? n.toLowerCase() : n;
    const at = hay.indexOf(lower);
    if (at < 0) continue;
    if (hay === lower) buckets[0].push(i);
    else if (at === hay.lastIndexOf('.') + 1) buckets[1].push(i);
    else if (at === 0 || hay[at - 1] === '.') buckets[2].push(i);
    else buckets[3].push(i);
  }
  const byUse = (a, b) => S.used[b] - S.used[a];
  const late = [];
  for (const b of buckets) {
    b.sort(byUse);
    for (const i of b) {
      if (hideGenerated && isGenerated(names[i])) { late.push(i); continue; }
      out.push(i);
      if (out.length >= 50) return out;
    }
  }
  for (const i of late) { out.push(i); if (out.length >= 50) break; }
  return out;
}

/**
 * A query of `+Name` terms finds the declarations whose statement mentions every one of them: "+Finset.sum
 * +Nat.Prime" is the lemmas relating those two. It needs the mention index inside graph.bin, so the first such
 * query pays for that download.
 */
async function searchMentions(q) {
  const wanted = q.split(/\s+/).filter(t => t.startsWith('+')).map(t => t.slice(1)).filter(Boolean);
  if (!wanted.length) return null;
  const ids = wanted.map(idOfName);
  const missing = wanted.filter((_, i) => ids[i] < 0);
  if (missing.length) return { missing };
  const g = await loadGraph(setStatus);
  const hits = mentioningAll(g, ids).filter(keep).sort((a, b) => S.used[b] - S.used[a]);
  return { hits, wanted };
}

/**
 * `c:Finset.sum` is "everything whose conclusion is about Finset.sum", which is a different question from
 * "everything that mentions it" and usually the one a person hunting for a lemma means. The conclusion head
 * lives in each shard, so this narrows with the mention index first and reads shards only for the candidates.
 */
async function searchConclusion(q) {
  const { words, filters } = parseQuery(q);
  if (!filters.concl) return null;
  const target = idOfName(filters.concl);
  if (target < 0) return { missing: [filters.concl] };
  const terms = words.map(w => w.toLowerCase());
  const { hits, scanned } = await concludedBy(target, 200);
  const kept = hits.filter(i => terms.every(term => S.names[i].toLowerCase().includes(term))
                             && passesFilters(i, filters));
  return { hits: kept, scanned, concl: filters.concl };
}

function searchModules(q) {
  q = parseQuery(q).words.join(' ');
  if (q.length < 2) return [];
  const lower = q.toLowerCase();
  const own = ownOnly ? new Set(ownIds().modules.map(m => m.n)) : null;
  return S.modules.filter(m => (!own || own.has(m.n)) && m.n.toLowerCase().includes(lower))
    .sort((a, b) => b.c - a.c).slice(0, 5);
}

function libraryOf(moduleName) {
  const top = moduleName.split('.')[0];
  const libs = S.manifest.libraries;
  return libs.find(l => l.prefixes.includes(top)) || libs.find(l => l.prefixes.length === 0) || null;
}

function sourceUrl(moduleName, lines) {
  const lib = libraryOf(moduleName);
  if (!lib || !lib.url || !lib.rev) return null;
  let u = `${lib.url}/blob/${lib.rev}/${lib.path}${moduleName.replace(/\./g, '/')}.lean`;
  if (lines) u += `#L${lines[0]}-L${lines[1]}`;
  return u;
}

// ---------------------------------------------------------------- rendering helpers

/**
 * A copy button for a short piece of text. One delegated listener, because these are rendered into pages that
 * are thrown away and rebuilt, and per-element handlers would either go stale or stack up.
 */
function copyButton(text, label = 'copy') {
  return `<button class="more copy" data-copy="${esc(text)}">${esc(label)}</button>`;
}
document.addEventListener('click', (ev) => {
  const b = ev.target.closest('[data-copy]');
  if (!b) return;
  const text = b.dataset.copy;
  const done = () => { const was = b.textContent; b.textContent = 'copied'; setTimeout(() => { b.textContent = was; }, 1600); };
  if (navigator.clipboard) navigator.clipboard.writeText(text).then(done, () => window.prompt('Copy this:', text));
  else window.prompt('Copy this:', text);
});

/**
 * The line you put at the top of a file to use this declaration. Importing the module that declares it is
 * always correct, which is what a reader needs; Lean users often import something higher up instead, and that
 * is a preference rather than a requirement.
 */
/**
 * The transitive import closure of a module, memoised. The module table carries direct imports only, and
 * several questions need the closure: which modules a declaration's references are already covered by, and
 * what would break if a module changed.
 */
try {
  const saved = localStorage.getItem('theme');
  if (saved) document.documentElement.dataset.theme = saved;
} catch (e) { /* private window: the default stands */ }

let mapMetric = 'name';
try { mapMetric = localStorage.getItem('mapMetric') || 'name'; } catch (e) { /* private window */ }

const importClosures = new Map();
function importClosure(mi) {
  let got = importClosures.get(mi);
  if (got) return got;
  got = new Set();
  const stack = [mi];
  while (stack.length) {
    const at = stack.pop();
    for (const im of S.modules[at].i) {
      if (!got.has(im)) { got.add(im); stack.push(im); }
    }
  }
  importClosures.set(mi, got);
  return got;
}

/**
 * The fewest modules you must import to write this statement: `#min_imports` for one declaration, which people
 * have asked import-graph for twice. Every constant the statement mentions lives in some module; a module whose
 * import closure already contains another makes that other one redundant, so what is left is the antichain.
 */
function minimalImports(d, ownModule) {
  const need = new Set((d.t || []).map(moduleOfId));
  need.delete(S.modules.findIndex(m => m.n === ownModule));
  if (!need.size) return [];
  const keep = [...need].filter(a => ![...need].some(b => b !== a && importClosure(b).has(a)));
  return keep.map(i => S.modules[i].n).sort();
}

function importLine(moduleName) {
  const line = `import ${moduleName}`;
  return `<p class="importline"><code>${esc(line)}</code> ${copyButton(line)}</p>`;
}

const declHref = (name) => '#/d/' + encodeURIComponent(name);
const modHref = (name) => '#/m/' + encodeURIComponent(name);
const kindOf = (id) => KIND[S.kinds[id]] || 'unknown';
const kindBadge = (k) => `<span class="kind ${esc(k)}">${esc(k)}</span>`;
const shortName = (name) => { const i = name.lastIndexOf('.'); return i < 0 ? name : name.slice(i + 1); };

function nameLink(id) {
  const n = S.names[id];
  const mod = S.modules[moduleOfId(id)].n;
  return `<li>${kindBadge(kindOf(id))} <a class="nm" href="${declHref(n)}">${esc(n)}</a> <span class="mod">${esc(mod)}</span> <span class="n" title="declarations that reference it">${fmt(S.used[id])}</span></li>`;
}

// Mathlib writes Lean notation in backticks, not LaTeX: of 112,670 docstrings only 1,178 carry inline math, and
// what they use is a short list of symbols plus sub- and superscripts. So this renders that subset rather than
// pulling in a real TeX engine, which would be 300 KB of dependency and a build step for 1% of docstrings.
const TEX = {
  to: '→', mapsto: '↦', rightarrow: '→', longrightarrow: '⟶', leftarrow: '←', hookrightarrow: '↪', twoheadrightarrow: '↠',
  in: '∈', notin: '∉', subseteq: '⊆', subset: '⊂', supseteq: '⊇', cup: '∪', cap: '∩', emptyset: '∅', setminus: '∖',
  sum: '∑', prod: '∏', coprod: '∐', int: '∫', oint: '∮', bigcup: '⋃', bigcap: '⋂', bigoplus: '⨁', bigotimes: '⨂',
  times: '×', otimes: '⊗', oplus: '⊕', cdot: '·', cdots: '⋯', ldots: '…', dots: '…', circ: '∘', pm: '±', mp: '∓',
  le: '≤', leq: '≤', ge: '≥', geq: '≥', ne: '≠', neq: '≠', equiv: '≡', sim: '∼', simeq: '≃', cong: '≅', approx: '≈',
  infty: '∞', partial: '∂', nabla: '∇', forall: '∀', exists: '∃', neg: '¬', land: '∧', lor: '∨', implies: '⟹',
  alpha: 'α', beta: 'β', gamma: 'γ', delta: 'δ', epsilon: 'ε', varepsilon: 'ε', zeta: 'ζ', eta: 'η', theta: 'θ',
  iota: 'ι', kappa: 'κ', lambda: 'λ', mu: 'μ', nu: 'ν', xi: 'ξ', pi: 'π', rho: 'ρ', sigma: 'σ', tau: 'τ',
  phi: 'φ', varphi: 'φ', chi: 'χ', psi: 'ψ', omega: 'ω', Gamma: 'Γ', Delta: 'Δ', Theta: 'Θ', Lambda: 'Λ',
  Sigma: 'Σ', Phi: 'Φ', Psi: 'Ψ', Omega: 'Ω', ell: 'ℓ', hbar: 'ℏ', aleph: 'ℵ', colon: ':', quad: ' ', qquad: '  ',
  lim: 'lim', log: 'log', exp: 'exp', sin: 'sin', cos: 'cos', tan: 'tan', min: 'min', max: 'max', deg: 'deg',
  det: 'det', dim: 'dim', ker: 'ker', gcd: 'gcd', sup: 'sup', inf: 'inf', bmod: 'mod', left: '', right: '',
};
const BLACKBOARD = { R: 'ℝ', C: 'ℂ', N: 'ℕ', Z: 'ℤ', Q: 'ℚ', P: 'ℙ', F: '𝔽', A: '𝔸', H: 'ℍ', K: '𝕂' };
const SUPER = { '0': '⁰', '1': '¹', '2': '²', '3': '³', '4': '⁴', '5': '⁵', '6': '⁶', '7': '⁷', '8': '⁸', '9': '⁹',
  n: 'ⁿ', i: 'ⁱ', '+': '⁺', '-': '⁻', '(': '⁽', ')': '⁾' };
const SUB = { '0': '₀', '1': '₁', '2': '₂', '3': '₃', '4': '₄', '5': '₅', '6': '₆', '7': '₇', '8': '₈', '9': '₉',
  i: 'ᵢ', j: 'ⱼ', n: 'ₙ', m: 'ₘ', k: 'ₖ', a: 'ₐ', x: 'ₓ', '+': '₊', '-': '₋', '(': '₍', ')': '₎' };

/** Render the inline-math subset Mathlib actually uses. Anything unrecognized is left as written. */
function tex(src) {
  let out = '';
  for (let i = 0; i < src.length; i++) {
    const c = src[i];
    if (c === '\\') {
      const m = /^[a-zA-Z]+/.exec(src.slice(i + 1));
      if (!m) { out += src[++i] ?? ''; continue; }
      const name = m[0];
      i += name.length;
      if ((name === 'mathbb' || name === 'mathbf' || name === 'mathfrak') && src[i + 1] === '{') {
        const end = src.indexOf('}', i + 1);
        const inner = src.slice(i + 2, end);
        out += (name === 'mathbb' && BLACKBOARD[inner]) || inner;
        i = end;
      } else if (name === 'text' || name === 'operatorname' || name === 'mathrm') {
        if (src[i + 1] === '{') {
          const end = src.indexOf('}', i + 1);
          out += `<span class="tex-rm">${src.slice(i + 2, end)}</span>`;
          i = end;
        }
      } else if (name === 'frac' && src[i + 1] === '{') {
        const a = balanced(src, i + 1), b = balanced(src, a.end + 1);
        out += `<span class="tex-frac"><span>${tex(a.body)}</span><span>${tex(b.body)}</span></span>`;
        i = b.end;
      } else {
        out += TEX[name] !== undefined ? TEX[name] : '\\' + name;
      }
      continue;
    }
    if ((c === '^' || c === '_') && i + 1 < src.length) {
      const table = c === '^' ? SUPER : SUB;
      let body;
      if (src[i + 1] === '{') { const b = balanced(src, i + 1); body = b.body; i = b.end; }
      else { body = src[i + 1]; i++; }
      const mapped = [...body].every(ch => table[ch]) ? [...body].map(ch => table[ch]).join('') : null;
      out += mapped !== null ? mapped : `<${c === '^' ? 'sup' : 'sub'}>${esc(body)}</${c === '^' ? 'sup' : 'sub'}>`;
      continue;
    }
    out += esc(c);
  }
  return out;
}

/** The braced group starting at `at`, and where it ends. */
function balanced(src, at) {
  let depth = 0;
  for (let i = at; i < src.length; i++) {
    if (src[i] === '{') depth++;
    else if (src[i] === '}' && --depth === 0) return { body: src.slice(at + 1, i), end: i };
  }
  return { body: src.slice(at + 1), end: src.length - 1 };
}

function renderDoc(doc) {
  // the light subset of markdown docstrings actually use: paragraphs, code spans, fenced code
  const parts = doc.split(/```/);
  let html = '';
  parts.forEach((part, i) => {
    if (i % 2 === 1) { html += `<pre>${esc(part.replace(/^[a-z]*\n/, ''))}</pre>`; return; }
    for (const para of part.split(/\n\s*\n/)) {
      const t = para.trim();
      if (!t) continue;
      // code spans first, so `$x$` inside backticks stays literal, then inline math in what is left
      const marks = [];
      const withCode = t.replace(/`([^`]+)`/g, (_, inner) => {
        marks.push(`<code>${esc(inner)}</code>`);
        return `\u0000${marks.length - 1}\u0000`;
      });
      let body = esc(withCode).replace(/\$([^$\n]{1,200})\$/g, (_, math) => `<span class="tex">${tex(unesc(math))}</span>`);
      body = body.replace(/\u0000(\d+)\u0000/g, (_, k) => marks[+k]);
      html += '<p>' + body + '</p>';
    }
  });
  return html;
}

/**
 * Turn the names in a printed statement into links. The generator gives the ids the statement references, so this
 * looks for each of their display forms, longest first so that List.map wins over List, and skips a match whose
 * neighbours make it part of a longer identifier or that falls inside a tag it already produced.
 */
function linkStatement(text, ids) {
  // names referenced from the statement become links; longest first so `List.map` beats `List`
  const names = ids.map(i => S.names[i]).sort((a, b) => b.length - a.length);
  let html = esc(text);
  const isNameChar = (c) => /[\p{L}\p{N}_'.!?₀-₉ₐ-ₜ]/u.test(c);
  for (const n of names) {
    const shown = displayName(n);
    if (!shown) continue;
    const e = esc(shown);
    let at = 0, out = '';
    while (true) {
      const i = html.indexOf(e, at);
      if (i < 0) { out += html.slice(at); break; }
      const before = i > 0 ? html[i - 1] : ' ';
      const after = i + e.length < html.length ? html[i + e.length] : ' ';
      const inTag = html.lastIndexOf('<', i) > html.lastIndexOf('>', i);
      if (inTag || isNameChar(before) || isNameChar(after) || before === '✝') { out += html.slice(at, i + e.length); at = i + e.length; continue; }
      out += html.slice(at, i) + `<a href="${declHref(n)}">${e}</a>`;
      at = i + e.length;
    }
    html = out;
  }
  return html;
}

const unesc = (s) => s.replace(/&amp;/g, '&').replace(/&lt;/g, '<').replace(/&gt;/g, '>').replace(/&quot;/g, '"');

function linkDocNames(html) {
  // a code span that is exactly a known declaration name becomes a link
  return html.replace(/<code>([^<]+)<\/code>/g, (m, inner) => {
    const raw = inner.replace(/&amp;/g, '&').replace(/&lt;/g, '<').replace(/&gt;/g, '>').replace(/&quot;/g, '"');
    if (!/^[\p{L}_][\p{L}\p{N}_'.!?₀-₉]*$/u.test(raw)) return m;
    return idOfName(raw) >= 0 ? `<a href="${declHref(raw)}"><code>${inner}</code></a>` : m;
  });
}

// Symbol to class. One pass over the text, because replacing class by class lets a later pattern match inside
// the markup an earlier one just inserted, which turns a statement into its own HTML.
const SYNTAX = new Map();
for (const [cls, symbols] of [
  ['kw', ['∀', '∃', 'λ', '↦']],
  ['op', ['→', '↔', '∧', '∨', '¬', '⟶', '≫', '⋙', '∘', '×', '⊕', '≃', '≅', '⊗', '∣']],
  ['rel', ['=', '≠', '≤', '≥', '&lt;', '&gt;', '∈', '∉', '⊆', '⊂', '≈', '≡']],
  ['big', ['∑', '∏', '⨆', '⨅', '⋃', '⋂', '∫⁻', '∫', '∀ᶠ', '∃ᶠ']],
]) {
  for (const sym of symbols) SYNTAX.set(sym, cls);
}
const WORDS = new Map([['Type', 'sort'], ['Prop', 'sort'], ['Sort', 'sort'], ['fun', 'kw'], ['let', 'kw'],
  ['if', 'kw'], ['then', 'kw'], ['else', 'kw']]);
const SYNTAX_RE = new RegExp(
  [...[...SYNTAX.keys()].sort((a, b) => b.length - a.length).map(s => s.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')),
   ...[...WORDS.keys()].map(w => `\\b${w}\\b`)].join('|'), 'g');

/**
 * A statement laid out the way a paper states a theorem: what it is about, what it assumes, what it claims. The
 * generator does the splitting, since it has the term; this only arranges it. A statement with neither setting
 * nor hypotheses is just a claim, and gets the plain one-line form rather than a heading over a single row.
 */
/**
 * The source a person actually wrote, fetched from the pinned revision and shown in place.
 *
 * The page has always linked to it, which means leaving. The bundle already knows the repository, the exact
 * commit and the first and last line, and raw.githubusercontent serves with an open CORS header, so the lines
 * can simply be here. This is the other half of the elaborated term: what the kernel checked, and what was
 * typed, side by side.
 */
function sourceBlock(mod, lines) {
  const lib = libraryOf(mod);
  if (!lib || !lib.url || !lib.rev || !lines) return '';
  const raw = `https://raw.githubusercontent.com/${lib.url.replace(/^https?:\/\/github\.com\//, '')}/${lib.rev}/${lib.path}${mod.replace(/\./g, '/')}.lean`;
  return `<h2>Source <small>lines ${lines[0]} to ${lines[1]} of ${esc(mod)}, at the pinned commit</small></h2>
    <div class="card srcwrap"><button class="more" id="showsrc" data-raw="${esc(raw)}"
      data-from="${lines[0]}" data-to="${lines[1]}">show the source</button>
      <pre id="srcout" hidden></pre></div>`;
}

function wireSource() {
  const b = $('#showsrc');
  if (!b) return;
  b.onclick = async () => {
    const out = $('#srcout');
    b.disabled = true;
    b.textContent = 'fetching…';
    try {
      const r = await fetch(b.dataset.raw);
      if (!r.ok) throw new Error(`${r.status}`);
      const all = (await r.text()).split('\n');
      const from = Math.max(1, parseInt(b.dataset.from, 10));
      const to = Math.min(all.length, parseInt(b.dataset.to, 10));
      out.textContent = all.slice(from - 1, to).join('\n');
      out.hidden = false;
      b.remove();
    } catch (e) {
      // A file can move between the commit the bundle pins and now, and a rate limit is a rate limit. Say which.
      b.disabled = false;
      b.textContent = `could not fetch it (${esc(e.message)}); the source link above still works`;
    }
  };
}

function statementBlock(d) {
  const line = (text) => colorStatement(linkStatement(text, d.t));
  if (d.s === undefined) return '<pre><span class="dim">not decodable</span></pre>';
  if (d.sc === undefined || (!d.sg && !d.sh)) return `<pre>${line(d.s)}</pre>`;
  const rows = [];
  if (d.sg) {
    rows.push(`<div class="row"><span class="lead">for</span><div class="terms">${
      d.sg.map(x => `<div>${line(x)}</div>`).join('')}</div></div>`);
  }
  if (d.sh) {
    rows.push(`<div class="row"><span class="lead">assuming</span><div class="terms">${
      d.sh.map((x, i) => `<div><span class="hn">${i + 1}.</span> ${line(x)}</div>`).join('')}</div></div>`);
  }
  rows.push(`<div class="row claim"><span class="lead">then</span><div class="terms"><div>${line(d.sc)}</div></div></div>`);
  return `<div class="theorem">${rows.join('')}
    <details class="asone"><summary>as one line</summary><pre>${line(d.s)}</pre></details></div>`;
}

/**
 * Colour the punctuation of a printed statement: binders, arrows, relations, big operators. Applied to the
 * already-linked HTML, skipping anything inside a tag and inside link text, so a declaration's own name is never
 * chopped in half by a symbol that happens to appear in it.
 */
/**
 * How a definition is defined. This is the term the kernel stores, which is not the source someone wrote:
 * Lean's structure instance syntax arrives as `let __src✝ := …`, side conditions have been lifted into their
 * own `_proof_1` declarations, and inferred arguments are written out. Saying so is not a disclaimer, it is
 * the difference between "what was checked" and "what was typed", and the source link gives the other one.
 *
 * Names are linked against the body's own references (`u`) as well as the statement's, because a body reaches
 * constants the type never mentions.
 */
function bodyBlock(d, src) {
  if (d.v === undefined) return '';
  const refs = (d.u || []).concat(d.t || []);
  const term = colorStatement(linkStatement(d.v, refs));
  const cut = d.vcut
    ? `<p class="dim">This term was too long to print in full and is cut here.${
        src ? ` The <a href="${esc(src)}" target="_blank" rel="noopener">source</a> has all of it.` : ''}</p>`
    : '';
  return `<h2>Definition <small>the term the kernel stores, not the source text</small></h2>
    <pre class="body">${term}</pre>${cut}`;
}

/**
 * What a structure or class is made of. Lean stores no field list: a structure is an inductive with one
 * constructor, and the fields are that constructor's arguments past the type's own parameters. doc-gen4 shows
 * these, and losing them was filed there as a regression, which is a fair measure of how much people use them.
 */
function fieldsBlock(d) {
  if (!d.fd || !d.fd.length) return '';
  const refs = (d.t || []).concat(d.u || []);
  return `<h2>Fields <small>${d.fd.length}${d.ct && d.ct.length === 1 ? `, via <a class="nm" href="${declHref(d.ct[0])}">${esc(d.ct[0])}</a>` : ''}</small></h2>
    <table class="fields">${d.fd.map(f =>
      `<tr><td class="fname">${esc(f.n)}</td><td>${colorStatement(linkStatement(f.t, refs))}</td></tr>`).join('')}</table>`;
}

/** The constructors of an inductive that is not a structure: the ways a value of it can be built. */
function ctorsBlock(d) {
  if (!d.ct || !d.ct.length || (d.fd && d.fd.length)) return '';
  return `<h2>Constructors <small>${d.ct.length}</small></h2>
    <ul class="list">${d.ct.map(c => `<li><a class="nm" href="${declHref(c)}">${esc(c)}</a></li>`).join('')}</ul>`;
}

/**
 * Modifiers a reader acts on. `unsafe` and `partial` mean the kernel did not check this the way it checked
 * everything else, which matters to anyone reasoning about trust; `private` and `protected` change how the name
 * resolves, which matters to anyone typing it. doc-gen4 has open reports for both being invisible.
 */
const MARKS = {
  unsafe: 'unsafe: the kernel does not check this for termination or type soundness',
  partial: 'partial: not proved to terminate, so it is opaque to the kernel',
  private: 'private: not visible outside the module that declares it',
  protected: 'protected: needs its full name even when its namespace is open',
};
function markBadges(d) {
  if (!d.md || !d.md.length) return '';
  return d.md.map(m => `<span class="mark ${esc(m)}" title="${esc(MARKS[m] || m)}">${esc(m)}</span>`).join(' ');
}

function colorStatement(html) {
  let depth = 0;
  return html.split(/(<[^>]*>)/).map(part => {
    if (part.startsWith('<')) {
      if (part.startsWith('<a')) depth++;
      else if (part.startsWith('</a')) depth--;
      return part;
    }
    if (depth > 0) return part;
    return part.replace(SYNTAX_RE, m => `<span class="s-${SYNTAX.get(m) || WORDS.get(m)}">${m}</span>`);
  }).join('');
}

function displayName(n) {
  // mirror the generator's display rules for private names; hygienic names never appear in statements
  const parts = n.split('.');
  if (parts[0] === '_private') { const z = parts.indexOf('0', 1); if (z > 0) return parts.slice(z + 1).join('.'); }
  return n;
}

function setStatus(s) { $('#status').textContent = s; }

/** Say plainly when a link named a library this site does not carry, rather than quietly showing another. */
function warnWrongProject() {
  if (!S.wrongProject || !$('#main')) return;
  const carried = S.projects.map(p => `<a href="?p=${encodeURIComponent(p.slug)}#/">${esc(p.title)}</a>`).join(', ');
  $('#main').insertAdjacentHTML('afterbegin',
    `<div class="card bad-card"><b>There is no library called "${esc(S.wrongProject)}" on this site.</b>
     Showing ${esc(S.project.title)} instead. What is here: ${carried}.</div>`);
}

/** A link per library when the site carries more than one. With a single bundle there is nothing to switch to. */
function renderProjectSwitch() {
  const el = $('#projects');
  if (!el || !S.projects || S.projects.length < 2) return;
  el.innerHTML = S.projects.map(p =>
    `<a class="proj ${p.slug === S.project.slug ? 'on' : ''}" href="?p=${encodeURIComponent(p.slug)}#/" title="${esc(p.title)}: ${fmt(p.declarations)} declarations, Lean ${esc(p.lean)}">${esc(p.title)}</a>`).join('');
  el.hidden = false;
}

/** The "only this project" switch, which only means anything when the project is part of what the bundle holds. */
function wireScope() {
  const wrap = $('#scopewrap'), box = $('#scope'), label = $('#scopename');
  if (!wrap || !box || !S.manifest) return;
  const own = ownIds();
  if (!own.count || own.count >= S.manifest.declarations) return;
  label.textContent = S.manifest.title || 'this project';
  box.checked = ownOnly;
  wrap.hidden = false;
  box.addEventListener('change', () => {
    ownOnly = box.checked;
    try { localStorage.setItem('ownOnly', ownOnly ? 'yes' : 'no'); } catch (e) { /* private window */ }
    const q = $('#q');
    if (q && q.value.trim()) q.dispatchEvent(new Event('input'));
  });
}

/**
 * Ask for a library to be added, and watch the ones already asked for.
 *
 * A static page cannot start a build: that needs a token, and a token in a page is a token anyone can take. So a
 * request is a GitHub issue, which anyone with an account can open and which a workflow reacts to. This page
 * writes the issue for them and then shows the queue, read from the public API.
 */
async function pageAdd() {
  const repo = (S.manifest.repository || '').replace(/^https?:\/\/github\.com\//, '') || 'keithadler/leanviz';
  $('#main').innerHTML = `
    <h1 class="prose">Add a Lean project</h1>
    <p class="dim">Paste a public GitHub repository that builds with Lake. It gets compiled, re-checked by an
      independent kernel, and turned into a site like this one. Small projects take about ten minutes; large ones
      take hours, and a few are too large to finish at all.</p>
    <p><input id="add-repo" class="prefix" placeholder="owner/name, for example ImperialCollegeLondon/FLT" autocomplete="off">
       <button class="more" id="add-go">request it</button></p>
    <p class="dim" id="add-note"></p>
    <h2>Building now</h2>
    <div id="builds"><p class="dim">asking GitHub…</p></div>
    <div id="chomp" class="chomp" aria-hidden="true" hidden></div>
    <h2>Asked for so far</h2>
    <div id="queue"><p class="dim">loading…</p></div>
    <h2>What happens</h2>
    <ol class="tour">
      <li>Your request opens an issue on <a href="https://github.com/${esc(repo)}/issues">the repository</a>, so
        the whole exchange is public.</li>
      <li>A workflow clones the project, fetches its dependencies' build cache, and compiles it. This is the slow
        part, and it is slow because compiling Lean is slow, not because anything here is.</li>
      <li>Tenet re-checks every proof, then the generator reads the compiled files and writes the bundle.</li>
      <li>The issue gets a comment with the link, and the library appears in the switcher above.</li>
    </ol>
    <p class="dim">The site holds about seven libraries, so a new one may evict the least recently added guest.
      Mathlib, Fermat and Navier-Stokes stay.</p>`;

  watchBuilds(repo);

  const go = () => {
    const name = $('#add-repo').value.trim().replace(/^https?:\/\/github\.com\//, '').replace(/\.git$/, '').replace(/\/$/, '');
    if (!/^[\w.-]+\/[\w.-]+$/.test(name)) {
      $('#add-note').textContent = 'That does not look like owner/name.';
      return;
    }
    const url = `https://github.com/${repo}/issues/new?title=${encodeURIComponent('Add library: ' + name)}`
      + `&body=${encodeURIComponent(`Please build https://github.com/${name} for LeanViz.`)}`;
    window.open(url, '_blank', 'noopener');
    $('#add-note').innerHTML = 'Opened a prefilled issue. Submit it there and the build starts on its own.';
  };
  $('#add-go').onclick = go;
  $('#add-repo').onkeydown = (ev) => { if (ev.key === 'Enter') go(); };
  renderQueue(repo);
}

/**
 * Watch the builds actually running, and say where each one is.
 *
 * A request goes to a workflow, and the workflow's steps are public, so the page can show what is happening
 * rather than a spinner that means nothing. The mouth eats while something is genuinely being consumed and
 * stops when nothing is, which is the whole point of the thing it is imitating.
 */
async function watchBuilds(repo) {
  const el = $('#builds');
  if (!el) return;
  let stop = false;
  window.addEventListener('hashchange', () => { stop = true; }, { once: true });

  const STEPS = {
    'Set up job': 'starting up',
    'Work out what was asked for': 'reading the request',
    'Say it has started': 'starting up',
    'Make room': 'clearing disk space',
    'Build the project': 'compiling the project',
    'Re-check it with Tenet': 'rechecking every proof',
    'Generate its bundle': 'reading the compiled files',
    'Build the reader from Tenet\'s source': 'building the reader',
    'Check out the project': 'fetching the repository',
    'Keep it, and keep the site under its limit': 'storing the bundle',
    'Publish the site': 'publishing',
    'Say where it is': 'posting the link',
  };

  // A step this table does not know still has to read as prose, not as an instruction to the runner: the
  // first live build showed "building add-library Make room", which tells a visitor nothing. Unnamed uses
  // of an action are worse, because GitHub calls them "Run actions/checkout@v7".
  const phrase = name => STEPS[name]
    || (/^(Run |Post )/.test(name) ? 'setting up the runner' : name.charAt(0).toLowerCase() + name.slice(1));

  const poll = async () => {
    if (stop || !document.body.contains(el)) return;
    try {
      const r = await fetch(`https://api.github.com/repos/${repo}/actions/workflows/add-library.yml/runs?per_page=5`);
      // A failed request is not an empty history. Folding !r.ok into [] made the page say "Nothing has been
      // built this way yet", which is a claim about the past decided by the weather, and it was false: the
      // unauthenticated limit is 60 an hour per address and a busy visitor reaches it.
      if (!r.ok) {
        const limited = r.status === 403 && r.headers.get('x-ratelimit-remaining') === '0';
        el.innerHTML = `<p class="dim">${limited
          ? 'GitHub is rate limiting this page, so it cannot see what is building. It sorts itself out within the hour.'
          : 'Could not reach GitHub to see what is building.'}</p>`;
        stopChomp();
        if (!stop) setTimeout(poll, 60000);
        return;
      }
      const runs = (await r.json()).workflow_runs || [];
      const live = runs.filter(x => x.status !== 'completed');
      if (!live.length) {
        const last = runs[0];
        // GitHub's own word for the outcome is a noun, so interpolating it raw read "The last run failure on".
        const WORD = { success: 'succeeded', failure: 'failed', cancelled: 'was cancelled', timed_out: 'ran out of time',
                       skipped: 'was skipped', neutral: 'finished', action_required: 'needs a decision' };
        el.innerHTML = last
          ? `<p class="dim">Nothing building right now. The last run
             <a href="${esc(last.html_url)}" target="_blank" rel="noopener">${esc(WORD[last.conclusion] || last.conclusion || last.status)}</a>
             on ${esc(last.created_at.slice(0, 10))}.</p>`
          : '<p class="dim">Nothing has been built this way yet.</p>';
        stopChomp();
      } else {
        const rows = await Promise.all(live.map(async run => {
          let where = run.status.replace('_', ' ');
          try {
            const j = await fetch(run.jobs_url);
            if (j.ok) {
              const job = ((await j.json()).jobs || [])[0];
              const step = (job?.steps || []).find(x => x.status === 'in_progress');
              if (step) where = phrase(step.name);
            }
          } catch (e) { /* the step detail is a nicety, the run itself is the fact */ }
          const mins = Math.round((Date.now() - new Date(run.run_started_at || run.created_at)) / 60000);
          return `<li><span class="kind opaque">building</span>
            <a class="nm" href="${esc(run.html_url)}" target="_blank" rel="noopener">${esc(run.display_title)}</a>
            <span class="mod">${esc(where)}</span><span class="n">${mins} min</span></li>`;
        }));
        el.innerHTML = `<ul class="list">${rows.join('')}</ul>`;
        startChomp();
      }
    } catch (e) {
      el.innerHTML = '<p class="dim">Could not reach GitHub to see what is building.</p>';
      stopChomp();
    }
    if (!stop) setTimeout(poll, 15000);
  };
  poll();
}

let chompTimer = null;

function stopChomp() {
  if (chompTimer) { clearInterval(chompTimer); chompTimer = null; }
  const el = $('#chomp');
  if (el) el.hidden = true;
}

/**
 * The waiting animation: a mouth eating its way through module names, in the manner of the thing WinDirStat did
 * while it counted a disk. It runs only while a build is running, because an animation that never stops is
 * decoration rather than a signal.
 */
function startChomp() {
  const el = $('#chomp');
  if (!el || !S.modules || chompTimer) return;
  el.hidden = false;
  const pool = S.modules.map(m => m.n).filter(n => n.length < 46);
  let row = 0;
  let open = true;
  const line = () => pool[Math.floor(Math.random() * pool.length)] || 'Mathlib';
  let text = line();
  let at = 0;
  const tick = () => {
    if (!document.body.contains(el)) return; // the page moved on
    open = !open;
    at += 2; // two characters a bite, so the counter moves often enough to read as progress
    if (at > text.length) {
      text = line();
      at = 0;
      row++;
    }
    const eaten = text.slice(at);
    el.innerHTML = `<span class="mouth ${open ? 'open' : ''}">${open ? '◔' : '●'}</span>`
      + `<span class="crumbs">${esc(eaten)}</span>`
      + `<span class="ate">${row ? fmt(row) + ' eaten' : 'chewing'}</span>`;
  };
  tick();
  chompTimer = setInterval(tick, 110);
  // stop when the page changes, since an animation nobody is looking at is just a battery drain
  window.addEventListener('hashchange', stopChomp, { once: true });
}

/** The requests already made, newest first, straight from the public issues API. */
async function renderQueue(repo) {
  const el = $('#queue');
  try {
    const r = await fetch(`https://api.github.com/repos/${repo}/issues?state=all&per_page=20`);
    if (!r.ok) throw new Error(`${r.status}`);
    const rows = (await r.json()).filter(i => !i.pull_request && i.title.startsWith('Add library:'));
    if (!rows.length) {
      el.innerHTML = '<p class="dim">Nobody has asked for one yet.</p>';
      return;
    }
    el.innerHTML = `<ul class="list">${rows.map(i => {
      const name = i.title.replace(/^Add library:\s*/, '');
      const done = i.state === 'closed';
      return `<li><span class="kind ${done ? 'inductive' : 'opaque'}">${done ? 'built' : 'queued'}</span>
        <a class="nm" href="${esc(i.html_url)}" target="_blank" rel="noopener">${esc(name)}</a>
        <span class="mod">${esc(new Date(i.created_at).toISOString().slice(0, 10))}</span></li>`;
    }).join('')}</ul>`;
  } catch (e) {
    el.innerHTML = '<p class="dim">Could not read the queue from GitHub just now.</p>';
  }
}

// ---------------------------------------------------------------- the whole graph, on request

/**
 * Load graph.bin: the forward references of every declaration and the reverse of the statement references, as
 * typed arrays. It is the largest file in a bundle, tens of megabytes for Mathlib, so nothing fetches it until a
 * question needs it. Once loaded, a walk over twenty million edges is milliseconds.
 */
function loadGraph(onProgress) {
  if (S.graphPromise) return S.graphPromise;
  S.graphPromise = (async () => {
    onProgress?.('loading the graph…');
    const buf = await (await fetchBundle('graph.bin')).arrayBuffer();
    const head = new Uint8Array(buf, 0, 4);
    if (String.fromCharCode(...head) !== 'LVG1') throw new Error('graph.bin is not in a format this page knows');
    const meta = new Uint32Array(buf, 4, 3);
    const [n, fCount, mCount] = meta;
    let at = 16;
    const fOff = new Uint32Array(buf, at, n + 1); at += 4 * (n + 1);
    const fTo = new Uint32Array(buf, at, fCount); at += 4 * fCount;
    const mOff = new Uint32Array(buf, at, n + 1); at += 4 * (n + 1);
    const mTo = new Uint32Array(buf, at, mCount);
    onProgress?.('');
    S.graph = { n, fOff, fTo, mOff, mTo };
    return S.graph;
  })();
  return S.graphPromise;
}

/** Everything this declaration transitively references, counted. A breadth-first walk over the forward edges. */
function reachFrom(g, start) {
  const seen = new Uint8Array(g.n);
  const queue = [start];
  seen[start] = 1;
  let count = 0;
  for (let i = 0; i < queue.length; i++) {
    const v = queue[i];
    for (let e = g.fOff[v]; e < g.fOff[v + 1]; e++) {
      const t = g.fTo[e];
      if (!seen[t]) { seen[t] = 1; count++; queue.push(t); }
    }
  }
  return count;
}

/**
 * The shortest chain of references from one declaration to another, or null.
 *
 * A plain breadth-first walk, with no pruning on the id order. That ordering holds between modules but not
 * inside one: Monad.rec references Applicative and both are in Init.Prelude, so a prune that skipped ids below
 * the target would quietly miss real chains. Over twenty million edges in typed arrays this is fast enough that
 * the shortcut was never worth its false negatives.
 */
function pathBetween(g, from, to) {
  if (from === to) return [from];
  const prev = new Int32Array(g.n).fill(-1);
  prev[from] = from;
  let frontier = [from];
  while (frontier.length) {
    const next = [];
    for (const v of frontier) {
      for (let e = g.fOff[v]; e < g.fOff[v + 1]; e++) {
        const t = g.fTo[e];
        if (prev[t] !== -1) continue;
        prev[t] = v;
        if (t === to) {
          const chain = [to];
          for (let at = v; at !== from; at = prev[at]) chain.push(at);
          chain.push(from);
          return chain.reverse();
        }
        next.push(t);
      }
    }
    frontier = next;
  }
  return null;
}

/** Declarations whose statement mentions every one of these constants. */
function mentioningAll(g, ids) {
  const lists = ids.map(id => Array.from(g.mTo.subarray(g.mOff[id], g.mOff[id + 1])));
  lists.sort((a, b) => a.length - b.length);
  let hits = lists[0] || [];
  for (let i = 1; i < lists.length && hits.length; i++) {
    const other = new Set(lists[i]);
    hits = hits.filter(x => other.has(x));
  }
  return hits;
}

/**
 * The reference graph with its arrows reversed, built once in the browser rather than shipped.
 *
 * The bundle carries forward edges and, per declaration, the 200 most-used dependents. "How much would fall if
 * this were wrong" needs all of them, transitively, and shipping a reverse copy would roughly double the 32 MB
 * graph for a question most visitors never ask. Inverting 20.9 million edges here costs about 100 MB of typed
 * array, which a desktop has and a phone may not, so the failure is caught and said out loud.
 */
function reverseGraph(g) {
  if (g.rOff) return g;
  const n = g.n, count = new Uint32Array(n + 1);
  for (let v = 0; v < n; v++) {
    for (let e = g.fOff[v]; e < g.fOff[v + 1]; e++) count[g.fTo[e] + 1]++;
  }
  for (let i = 0; i < n; i++) count[i + 1] += count[i];
  const rOff = count.slice();
  const rTo = new Uint32Array(g.fTo.length);
  const at = count.slice();
  for (let v = 0; v < n; v++) {
    for (let e = g.fOff[v]; e < g.fOff[v + 1]; e++) rTo[at[g.fTo[e]]++] = v;
  }
  g.rOff = rOff;
  g.rTo = rTo;
  return g;
}

/** Everything that would be affected if this declaration changed: the reverse of what it rests on. */
function reachTo(g, from) {
  reverseGraph(g);
  const seen = new Uint8Array(g.n);
  const stack = [from];
  seen[from] = 1;
  let count = 0;
  while (stack.length) {
    const v = stack.pop();
    for (let e = g.rOff[v]; e < g.rOff[v + 1]; e++) {
      const u = g.rTo[e];
      if (!seen[u]) { seen[u] = 1; count++; stack.push(u); }
    }
  }
  return count;
}

/**
 * Which declarations conclude a given constant: the instances of a class, the constructions of a type, the
 * lemmas that end in the same shape as this one. The bundle stores each declaration's conclusion head but not
 * the reverse index, because capping it at 200 per head would still cost tens of megabytes; instead the
 * statement-mention index already in graph.bin narrows it to a few hundred candidates, and their shards say
 * which of those actually conclude it. On demand, because it is several fetches.
 */
async function concludedBy(id, limit = 40) {
  const g = await loadGraph(setStatus);
  const candidates = Array.from(g.mTo.subarray(g.mOff[id], g.mOff[id + 1]))
    .filter(keep)
    .sort((a, b) => S.used[b] - S.used[a]);
  const out = [];
  // Walk the most-used first and stop early: the answer is a page of examples, not a census, and each miss
  // costs at most one shard that the next question will reuse.
  for (const c of candidates) {
    if (out.length >= limit || out.length + (candidates.length - candidates.indexOf(c)) < 0) break;
    let rec;
    try { rec = await decl(c); } catch (e) { continue; }
    if (rec && rec.ch === id) out.push(c);
    if (out.length >= limit) break;
  }
  return { hits: out, scanned: candidates.length };
}

// ---------------------------------------------------------------- pages

// ---------------------------------------------------------------- who is reading

const ROLES = {
  new: {
    tab: "I'm new here",
    body: (m) => `
      <h3>What this is</h3>
      <p><b>Lean</b> is a programming language in which mathematics is written so precisely that a computer can check every step. <b>Mathlib</b> is the big shared library of that mathematics: ${fmt(m.declarations)} named pieces, from "adding numbers is commutative" to the derivative of a function, each with a proof the computer has accepted.</p>
      <p>This site is a map of that library. Every named piece, called a <b>declaration</b>, gets a page: what it says, what it was built from, what was built on top of it, and what it ultimately assumes.</p>
      <h3>A two-minute tour</h3>
      <ol class="tour">
        <li>Open <a class="mono" href="${declHref('Nat.add_comm')}">Nat.add_comm</a>. The <b>statement</b> is the claim: for all natural numbers n and m, n + m = m + n. Everything else on the page is about that one line.</li>
        <li>The green badge says what the proof <b>rests on</b>. Every result in Lean is built from earlier results, down to a handful of starting assumptions called axioms. "Rests on no axioms at all" means this fact follows from the definitions alone.</li>
        <li>The <b>picture</b> puts the declaration in the middle. On the left, what it uses. On the right, what uses it. Click any box to move there. This is the part no other tool shows: for any fact in the library, who depends on it.</li>
        <li>Below the picture, <b>Used by</b> lists those dependents with a number: how many further declarations depend on each one. Big numbers are the load-bearing walls of mathematics.</li>
        <li>The <b>source</b> link opens the exact lines where a person wrote this, on GitHub.</li>
      </ol>
      <h3>Words you will see</h3>
      <dl class="gloss">
        <dt>theorem</dt><dd>a claim with a proof</dd>
        <dt>def</dt><dd>a definition: what a word means, such as what "prime" means</dd>
        <dt>inductive</dt><dd>a new kind of thing, such as the natural numbers, with its constructors</dd>
        <dt>axiom</dt><dd>an assumption taken without proof; Lean's logic has three standard ones</dd>
        <dt>sorry</dt><dd>a hole: a proof someone has not finished; anything resting on it is unproven</dd>
        <dt>docstring</dt><dd>the author's plain-language note about a declaration</dd>
        <dt>re-checked by Tenet</dt><dd>a second, independent program re-verified every proof, not only Lean itself</dd>
      </dl>`,
  },
  lean: {
    tab: 'I use Lean',
    body: (m) => `
      <h3>For people who write Lean</h3>
      <p>Search by any fragment of a name; the results rank the most depended-upon first and list matching modules above them. Statements are printed with the usual notation, implicit and instance arguments hidden, universes hidden. It is not Lean's delaborator: what the printer does not know, it prints as plain application, and <code>@[pp_nodot]</code> is not honored yet.</p>
      <ul>
        <li><b>Used by</b> is the thing you cannot get from the docs or from <code>#check</code>: reverse references across all ${fmt(m.modules)} modules, the ${fmt(m.inEdgeCap)} most depended-upon kept per declaration, the total always shown.</li>
        <li><b>Uses</b> is split into constants that appear in the statement and constants that appear only in the proof. The blue edges in the picture are the statement ones.</li>
        <li>The <b>axioms</b> section is <code>#print axioms</code> for every declaration at once, computed over the whole graph, with <code>sorryAx</code> flagged.</li>
        <li><b>Module pages</b> list a file's declarations with one-line statements, its imports and what imports it. The module tree on this page is Mathlib's directory structure with counts.</li>
        <li>Generated helpers (<code>_proof_3</code>, equation lemmas, matchers) are hidden by the switch in the header. They are in the data; flip it to see them.</li>
        <li>Source links go to the pinned commit of each library, so they stay right after Mathlib moves.</li>
      </ul>
      <p>The data comes straight from the compiled <code>.olean</code> files, read by <a href="https://github.com/keithadler/tenet">Tenet</a>, an independent Lean 4 kernel on .NET. No Lean process runs to build this site, and building it takes about two minutes for all of Mathlib.</p>`,
  },
  verify: {
    tab: 'I want to verify a proof',
    body: (m) => `
      <h3>What the verdicts mean</h3>
      <p><a href="#/certificate"><b>The full answer is on its own page</b></a>: what an independent re-check
        establishes, what it leaves untouched, and how to redo it without this site.</p>
      <p>The axiom list on a page is what a proof <i>cites</i>. Whether the proof <i>holds</i> is a separate question, and this site answers it with a second kernel. ${m.check
        ? `<b>This bundle was re-checked:</b> Tenet ${esc(m.check.tenet)} re-derived every one of ${fmt(m.check.checked)} declarations from scratch and rejected ${fmt(m.check.failed)}. Any rejected declaration shows a red card with the kernel's message.`
        : '<b>This bundle was not re-checked</b>, so the pages report citations only.'}</p>
      <ul>
        <li>Tenet is a clean-room implementation of Lean's trusted core. A proof that two independent kernels accept is one you can trust a little more than a proof one kernel accepts.</li>
        <li>The verdict is a file, <a href="${DATA}check.json">check.json</a>, which names every input by SHA-256${m.check ? ` and has hash <code>${esc(m.check.sha256)}</code>` : ''}.</li>
        <li>${m.repository
          ? `It was produced by <a href="${esc(m.repository)}/actions">a public workflow</a> and signed with GitHub's artifact attestation, so who ran what, over which bytes, when, is on a public transparency log. Verify with <code>gh attestation verify check.json --owner ${esc(m.repository.replace(/^https?:\/\/github\.com\//, '').split('/')[0])}</code>.`
          : 'It was produced on a private machine and carries no attestation.'}</li>
        <li>None of that makes a verdict true. A signed report from a buggy kernel is a signed mistake. What holds up is reproduction: the same files through the same checker give the same answer, and Lean's own kernel agrees. To reproduce: <code>dotnet tool install -g tenet</code>, then <code>tenet check &lt;project&gt; --all --report check.json</code>.</li>
        <li>A statement can be checked and still not say what you think it says. Read the statement, follow its constants to their definitions, and read those. That is what the "in the statement" list is for.</li>
      </ul>`,
  },
  project: {
    tab: 'I run a Lean project',
    body: (m) => `
      <h3>A site like this for your own project</h3>
      <p>Anything built with Lake works: a research formalization, a course, a private library. The generator reads the project's compiled files and its dependencies, so your declarations appear alongside the Mathlib they stand on, with source links into your repository at the pinned commit.</p>
      <pre>dotnet build generator -c Release
dotnet generator/bin/Release/net10.0/leanviz.dll /path/to/your/project --out site/data
python3 -m http.server 8787 --directory site</pre>
      <p>Add <code>--check report.json</code> from <code>tenet check</code> and every page carries the verdict. The repository's workflow does the whole thing on a schedule and publishes to GitHub Pages with an attestation; copy it and change the project it checks out.</p>
      <p>For a project that is still in progress, the pages are a progress map: every theorem that rests on <code>sorry</code> is flagged, and "used by" shows how much stands on each unfinished piece.</p>
      <h3>A badge for your README</h3>
      <p>Every bundle writes one, saying what the independent kernel found. It is a file in the bundle, not a
        service that has to stay up.</p>
      <p><img src="${DATA}badge.svg" alt="${esc(m.check ? `Tenet: ${fmt(m.check.checked)} checked, ${fmt(m.check.failed)} rejected` : 'Tenet: not re-checked')}" height="20">
        ${copyButton(`[![Tenet](${location.origin}${location.pathname.replace(/[^/]*$/, '')}${DATA}badge.svg)](${location.origin}${location.pathname.replace(/[^/]*$/, '')}?p=${esc(m.slug || '')})`, 'copy the markdown')}</p>
      <p>Source and instructions: <a href="https://github.com/keithadler/leanviz">github.com/keithadler/leanviz</a>.</p>`,
  },
};

// One delegated listener for the whole session: the tabs are re-rendered, so binding to them would either
// go stale or stack up, and a stacked listener toggles the choice straight back off.
document.addEventListener('click', (ev) => {
  const b = ev.target.closest('.tab');
  if (!b || !S.manifest) return;
  const next = b.dataset.role === currentRole() ? '' : b.dataset.role;
  try { localStorage.setItem('role', next); } catch (e) { /* a private window: the choice just does not stick */ }
  const box = $('.roles');
  if (box) box.outerHTML = renderRoles(S.manifest);
});

function currentRole() {
  try { return localStorage.getItem('role') || ''; } catch (e) { return ''; }
}

function renderRoles(m) {
  const role = currentRole();
  const tabs = Object.entries(ROLES).map(([k, r]) => `<button class="tab ${k === role ? 'on' : ''}" data-role="${k}">${esc(r.tab)}</button>`).join('');
  return `<div class="roles"><div class="tabs">${tabs}</div>${role && ROLES[role] ? `<div class="role-body">${ROLES[role].body(m)}</div>` : '<p class="dim" style="margin:8px 0 0">Pick the one that sounds like you and this page explains itself accordingly.</p>'}</div>`;
}

async function pageHome() {
  const m = S.manifest;
  const own = ownIds();
  // Mathlib's landmarks, shown on every library, so on lean4-cli or a small project most of them were links to
  // "no declaration named that". They are pruned below once the name list is in: not here, because the home
  // page renders before that fetch finishes and idOfName would read a list that is still null.
  const starts = ['Nat.add_comm', 'Real.sqrt', 'deriv', 'MeasureTheory.integral', 'Complex.exp', 'Finset.sum_comm',
    'Polynomial.eval', 'Matrix.det', 'List.map_append'];
  $('#main').innerHTML = `
    <h1 class="prose">${own.count && own.count < m.declarations
      ? `${esc(m.title)}, and everything it rests on`
      : 'Every declaration in Mathlib, and what it rests on'}</h1>
    <p class="dim">Type a name above. A declaration page shows its statement, what it uses, what uses it, and the axioms it rests on, with a picture you can walk one step at a time.</p>
    ${renderRoles(m)}
    <ul class="stats">
      ${own.count && own.count < m.declarations
        ? `<div><b>${fmt(own.count)}</b>declarations in ${esc(m.title)}</div>
           <div><b>${fmt(own.modules.length)}</b>of its modules</div>
           <div><b>${fmt(m.declarations - own.count)}</b>imported from other libraries</div>`
        : `<div><b>${fmt(m.declarations)}</b>declarations</div>
           <div><b>${fmt(m.modules)}</b>modules</div>
           <div><b>${fmt(m.references)}</b>references between them</div>`}
      <div><b>${esc(m.lean)}</b>Lean</div>
    </ul>
    ${checkLine(m)}
    <h2>Start somewhere</h2>
    <p class="start" id="starts">${starts.map(s => `<a class="mono" data-name="${esc(s)}" href="${declHref(s)}">${esc(s)}</a>`).join('')}
      <button class="more" id="surprise">show me something</button></p>
    <h2>Most depended upon <small>${own.count && own.count < m.declarations
      ? `the declarations of ${esc(m.title)} that the rest of it leans on`
      : 'the declarations the rest of the library leans on'}</small></h2>
    <ul class="list" id="top">${'<li class="dim">loading…</li>'}</ul>
    <h2>Search like a power user <small>filters, and words in any order</small></h2>
    <p class="dim">Type <code>k:theorem</code> for one kind, <code>m:Mathlib.Order</code> for a module and what
      is under it, <code>lib:Mathlib</code> for one library, and several bare words to match a name containing
      all of them in any order. They combine: <code>k:def m:Mathlib.Topology compact</code>. A query of only
      filters is a legitimate query, so <code>k:axiom</code> lists the axioms.</p>
    <p class="start">${[['k:axiom', 'every axiom'], ['k:inductive m:Mathlib.Order', 'the order structures'],
      ['comm add nat', 'words in any order']].map(([q, label]) =>
      `<button class="more try" data-try="${esc(q)}">${esc(label)}</button>`).join('')}</p>
    <h2>Other ways in</h2>
    <p class="start"><a href="#/map">the library as a map</a><a href="#/axioms">what it assumes</a><a href="#/certificate">how a proof is certified</a><a href="#/deprecated">what is deprecated</a><a href="#/compare">compare two libraries</a><a href="#/saved">saved</a><a href="#/unused">what nothing uses</a><a href="#/holes">unfinished proofs</a><a href="#/add">add your own project</a></p>
    <h2>${own.count && own.count < m.declarations ? `The modules of ${esc(m.title)}` : 'Or browse by module'}
      <small>${own.count && own.count < m.declarations ? 'what this project declares; its dependencies are still searchable' : ''}</small></h2>
    <div class="tree" id="tree"></div>`;
  renderTree();
  for (const b of $('#main').querySelectorAll('button.try')) {
    b.onclick = () => { const q = $('#q'); q.value = b.dataset.try; q.focus(); q.dispatchEvent(new Event('input')); };
  }
  // Somewhere to click for a person who does not yet know a single name in the library. It has to land on
  // something a human wrote: a theorem, not a compiler artifact, with enough dependents to matter and a
  // docstring if one can be found in a few tries, since the docstring is what makes it readable.
  const surprise = $('#surprise');
  if (surprise) surprise.onclick = async () => {
    surprise.disabled = true;
    await loadNames();
    const pick = () => {
      for (let tries = 0; tries < 4000; tries++) {
        const i = Math.floor(Math.random() * S.names.length);
        if (S.kinds[i] === 't' && keep(i) && S.used[i] >= 3) return i;
      }
      return -1;
    };
    let id = -1;
    for (let round = 0; round < 6; round++) {
      const c = pick();
      if (c < 0) break;
      if (id < 0) id = c;
      try {
        const arr = await shard(moduleOfId(c));
        const rec = arr[c - S.modules[moduleOfId(c)].s];
        if (rec && rec.d) { id = c; break; }
      } catch (e) { /* a shard that will not load is simply not the one we show */ }
    }
    surprise.disabled = false;
    if (id >= 0) location.hash = '#/i/' + id;
    else surprise.textContent = 'nothing to show in this bundle';
  };
  loadNames().then(() => {
    for (const a of $('#starts')?.querySelectorAll('a[data-name]') || []) {
      if (idOfName(a.dataset.name) < 0) a.remove();
    }
    const top = [];
    const scope = own.count && own.count < S.manifest.declarations ? own.ids() : null;
    const pool = scope || { length: S.used.length, [Symbol.iterator]: function* () { for (let i = 0; i < S.used.length; i++) yield i; } };
    for (const i of pool) {
      if (S.kinds[i] === 'c' || S.kinds[i] === 'r' || !keep(i)) continue; // constructors and recursors are used by everything, by construction
      const u = S.used[i];
      if (top.length < 25 || u > S.used[top[top.length - 1]]) {
        let k = top.length;
        while (k > 0 && S.used[top[k - 1]] < u) k--;
        top.splice(k, 0, i);
        if (top.length > 25) top.pop();
      }
    }
    const el = $('#top');
    if (el) el.innerHTML = top.map(nameLink).join('');
  });
}

function checkLine(m) {
  if (!m.check) return `<p class="dim">This bundle was not re-checked by Tenet; the axiom verdicts report what each proof cites, not that it holds.</p>`;
  const c = m.check;
  const verdict = c.failed === 0
    ? `<span class="verdict ok">every one of ${fmt(c.checked)} declarations re-checked by Tenet ${esc(c.tenet)}, none rejected</span>`
    : `<span class="verdict bad">${fmt(c.checked)} declarations re-checked by Tenet ${esc(c.tenet)}, ${fmt(c.failed)} rejected</span>`;
  return `<p>${verdict} <span class="dim">independent kernel, ${Math.round(c.seconds / 60)} min, ${esc(c.date)}</span></p>
    <p class="dim">The verdict is the <a href="${DATA}check.json">check report</a>, SHA-256 <code>${esc(c.sha256 || '')}</code>, over inputs it names by hash.${verifyHint(m)}</p>`;
}

/**
 * Where the attestations are, which is not where the library's source is.
 *
 * An attestation is recorded against the repository whose workflow signed it, and that is always this site's
 * repository: the guest workflow clones someone else's project but runs here. Building the link from the
 * library's own repository sent a reader to a page with nothing on it, and handed them a
 * `gh attestation verify --owner` naming an owner who never signed anything, which fails for any guest
 * belonging to somebody else.
 *
 * Derived from the address of the page rather than written down, so a fork points at the fork.
 */
function siteRepo() {
  const m = /^([^.]+)\.github\.io$/.exec(location.hostname);
  const project = location.pathname.split('/').filter(Boolean)[0];
  if (m && project) return { owner: m[1], url: `https://github.com/${m[1]}/${project}` };
  return null;
}

function verifyHint(m) {
  const site = siteRepo();
  if (!site) return ' It carries no attestation that this page can point you at.';
  return ` It was published by <a href="${esc(site.url)}/actions">a public workflow</a> and signed: download it and run <code>gh attestation verify check.json --owner ${esc(site.owner)} --format json</code>, or see <a href="${esc(site.url)}/attestations">the attestations</a>.`;
}

function renderTree() {
  const own = ownIds();
  const root = { children: new Map(), count: 0, module: null };
  for (const mod of (own.count && own.count < S.manifest.declarations ? own.modules : S.modules)) {
    let at = root;
    for (const part of mod.n.split('.')) {
      if (!at.children.has(part)) at.children.set(part, { children: new Map(), count: 0, module: null });
      at = at.children.get(part);
      at.count += mod.c;
    }
    at.module = mod.n;
    root.count += mod.c;
  }
  const html = (node, depth) => {
    const kids = [...node.children.entries()].sort((a, b) => a[0].localeCompare(b[0]));
    if (kids.length === 0) return '';
    return '<ul' + (depth > 0 ? ' hidden' : '') + '>' + kids.map(([name, k]) => {
      const has = k.children.size > 0;
      const label = k.module ? `<a class="mono" href="${modHref(k.module)}">${esc(name)}</a>` : `<span class="mono">${esc(name)}</span>`;
      return `<li><span class="tog">${has ? '▸' : ''}</span>${label}<span class="cnt">${fmt(k.count)}</span>${html(k, depth + 1)}</li>`;
    }).join('') + '</ul>';
  };
  const tree = $('#tree');
  tree.innerHTML = html(root, 0);
  tree.addEventListener('click', (ev) => {
    const t = ev.target.closest('.tog');
    if (!t) return;
    const ul = t.parentElement.querySelector('ul');
    if (!ul) return;
    ul.hidden = !ul.hidden;
    t.textContent = ul.hidden ? '▸' : '▾';
  });
}

/**
 * Which of a module's imports nothing in it actually reaches.
 *
 * This is `#min_imports` at the file level, and it needs nothing the bundle does not already carry: every
 * declaration's references are in its shard, and the module table gives each import's transitive closure. An
 * import is reported when every constant this module references is still covered after removing it.
 *
 * Reported, not recommended. An import can carry notation, instances, simp lemmas or `open` scopes that no
 * constant reference records, so this says what the reference graph can see and leaves the judgement alone.
 * Lean's own `#min_imports` carries the same caveat.
 */
function unreachedImports(mi, shardRecords) {
  const need = new Set();
  for (const d of shardRecords) {
    for (const r of (d.t || [])) need.add(moduleOfId(r));
    for (const r of (d.u || [])) need.add(moduleOfId(r));
  }
  need.delete(mi);
  const imports = S.modules[mi].i;
  const unreached = [];
  for (const drop of imports) {
    const covered = new Set();
    for (const other of imports) {
      if (other === drop) continue;
      covered.add(other);
      for (const c of importClosure(other)) covered.add(c);
    }
    let redundant = true;
    for (const n of need) {
      if (!covered.has(n)) { redundant = false; break; }
    }
    if (redundant) unreached.push(drop);
  }
  return { unreached, needed: need.size };
}

/** The shortest chain of imports from one module to another, which answers "why does this file pull that in". */
function importChain(from, to) {
  if (from === to) return [from];
  const prev = new Map([[from, -1]]);
  const queue = [from];
  for (let i = 0; i < queue.length; i++) {
    const v = queue[i];
    for (const n of S.modules[v].i) {
      if (prev.has(n)) continue;
      prev.set(n, v);
      if (n === to) {
        const out = [n];
        for (let at = v; at !== -1; at = prev.get(at)) out.push(at);
        return out.reverse();
      }
      queue.push(n);
    }
  }
  return null;
}

async function pageModule(name) {
  const mi = S.modules.findIndex(m => m.n === name);
  if (mi < 0) { $('#main').innerHTML = `<p>No module named <code>${esc(name)}</code>.</p>`; return; }
  const mod = S.modules[mi];
  const arr = await shard(mi);
  const src = sourceUrl(name, null);
  const importers = S.modules.filter(m => m.i.includes(mi)).map(m => m.n);
  $('#main').innerHTML = `
    <h1>${esc(name)}</h1>
    <p class="sub"><span>module, ${fmt(mod.c)} declarations</span>${src ? `<a href="${esc(src)}" target="_blank" rel="noopener">source ↗</a>` : ''}</p>
    ${importLine(name)}
    <div class="cols">
      <div><h2>Imports <small>(${mod.i.length})</small></h2><ul class="list">${mod.i.map(i => `<li><a class="nm" href="${modHref(S.modules[i].n)}">${esc(S.modules[i].n)}</a></li>`).join('')}</ul></div>
      <div><h2>Imported by <small>(${importers.length} directly)</small></h2><ul class="list">${importers.slice(0, 200).map(n => `<li><a class="nm" href="${modHref(n)}">${esc(n)}</a></li>`).join('')}${importers.length > 200 ? `<li class="dim">and ${fmt(importers.length - 200)} more</li>` : ''}</ul></div>
    </div>
    <h2>What changing this would reach <small>every module that imports it, directly or not</small></h2>
    <p class="dim" id="impact">counting…</p>
    <h2>Imports nothing here reaches <small>what the reference graph can see</small></h2>
    <div class="card">
      <p style="margin:0 0 6px"><button class="more" id="unreached">check the imports</button>
        <span id="unreachednote" class="dim"></span></p>
      <div id="unreachedout"></div>
    </div>
    <h2>Why this module imports another <small>the shortest chain</small></h2>
    <div class="card">
      <p style="margin:0"><label class="dim" for="whyimp">chain from ${esc(name)} to</label>
        <input id="whyimp" class="prefix" placeholder="a module name, e.g. Init.Prelude">
        <button class="more" id="whyimpgo">find</button></p>
      <div id="whyimpout"></div>
    </div>
    <h2>Declarations</h2>
    <ul class="list">${arr.map(d => `<li>${kindBadge(d.k)}${d.md && d.md.length ? ' ' + markBadges(d) : ''} <a class="nm ${d.x ? 'dep' : ''}" href="${declHref(d.n)}">${esc(d.n)}</a>${d.x ? ' <span class="depmark" title="deprecated">deprecated</span>' : ''} <span class="stmt-line">${esc(d.s || '')}</span> <span class="n">${fmt(d.bc)}</span></li>`).join('')}</ul>`;
  // "Who imports me" is one hop; "what would a change here reach" is the closure of that, which is the number a
  // refactor is actually deciding on. import-graph has an open request for exactly this over everything.
  const un = $('#unreached');
  if (un) un.onclick = () => {
    un.disabled = true;
    const { unreached, needed } = unreachedImports(mi, arr);
    $('#unreachednote').textContent = `${fmt(mod.i.length)} imports, ${fmt(needed)} modules referenced`;
    $('#unreachedout').innerHTML = unreached.length
      ? `<p class="dim">Nothing declared here references anything only these bring in. They may still be
           carrying notation, instances or simp lemmas, which no constant reference records.</p>
         <ul class="list">${unreached.map(i =>
           `<li><a class="nm" href="${modHref(S.modules[i].n)}">${esc(S.modules[i].n)}</a><span class="n">${fmt(S.modules[i].c)}</span></li>`).join('')}</ul>`
      : '<p class="dim">Every import is reached by something declared here.</p>';
    un.remove();
  };
  const wgo = $('#whyimpgo');
  if (wgo) wgo.onclick = () => {
    const want = $('#whyimp').value.trim();
    const to = S.modules.findIndex(m => m.n === want);
    const out = $('#whyimpout');
    if (to < 0) { out.innerHTML = `<p class="dim">No module named <code>${esc(want)}</code>.</p>`; return; }
    const chain = importChain(mi, to);
    out.innerHTML = chain
      ? `<p class="chain">${chain.map(i => `<a class="nm" href="${modHref(S.modules[i].n)}">${esc(S.modules[i].n)}</a>`).join(' <span class="dim">imports</span> ')}</p>`
      : `<p class="dim"><code>${esc(name)}</code> does not import <code>${esc(want)}</code>, directly or otherwise.</p>`;
  };
  const reached = S.modules.filter((_, other) => other !== mi && importClosure(other).has(mi));
  const decls = reached.reduce((a, m) => a + m.c, 0);
  $('#impact').innerHTML = reached.length
    ? `<b>${fmt(reached.length)}</b> module${reached.length === 1 ? '' : 's'} and <b>${fmt(decls)}</b> declarations
       are downstream of this one, against ${fmt(importers.length)} that import it directly.`
    : 'Nothing imports this module, directly or otherwise.';
}

async function pageDecl(name, byId = null) {
  await loadNames();
  const id = byId !== null ? byId : idOfName(name);
  if (!(id >= 0 && id < S.names.length)) {
    // A link to a declaration is the thing people paste, and the `?p=` that says which library it belongs to
    // is the thing that gets lost on the way: dropped by a client, trimmed by hand, mangled by a preview. What
    // is left lands on the default library and used to dead-end here. The site knows the other libraries, so
    // offer them rather than shrugging.
    const wanted = name ?? String(byId);
    const others = (S.projects || []).filter(x => x.slug !== (S.project || {}).slug);
    $('#main').innerHTML = `
      <h1 class="prose">Not in ${esc(S.manifest.title || 'this library')}</h1>
      <p>There is no declaration named <code>${esc(wanted)}</code> here.</p>
      ${name && others.length ? `<p class="dim">If you followed a link, the part naming the library may have been
        dropped. Try the same name in another:</p>
        <ul class="list">${others.map(x =>
          `<li><a class="nm" href="?p=${encodeURIComponent(x.slug)}#/d/${encodeURIComponent(name)}">${esc(x.title)}</a>
           <span class="mod">${fmt(x.declarations)} declarations</span></li>`).join('')}</ul>`
        : '<p class="dim">Search above, or <a href="#/">start from the home page</a>.</p>'}`;
    return;
  }
  name = S.names[id];
  // The same name can belong to two declarations in modules never imported together, and they can differ in
  // exactly what a reader cares about: one may be a challenge stub whose proof is `sorry`.
  const twins = idsOfName(name).filter(other => other !== id);
  const d = await decl(id);
  const mod = S.modules[moduleOfId(id)].n;
  const axioms = d.a.map(i => S.manifest.axioms[i]);
  const std = new Set(S.manifest.standardAxioms);
  const extra = axioms.filter(a => !std.has(a));
  const hasSorry = extra.includes('sorryAx');
  const verdict = d.k === 'axiom' ? `<span class="verdict warn">an axiom: this is an assumption, not a result</span>`
    : axioms.length === 0 ? `<span class="verdict ok">rests on no axioms at all</span>`
    : extra.length === 0 ? `<span class="verdict ok">rests on nothing beyond propext, Classical.choice and Quot.sound</span>`
    : `<span class="verdict ${hasSorry ? 'bad' : 'warn'}">rests on ${extra.length} assumption${extra.length === 1 ? '' : 's'} beyond the standard three${hasSorry ? ', including sorry' : ''}</span>`;
  const dep = d.x ? `<div class="card dep-card"><b>Deprecated${d.x.since ? ` since ${esc(d.x.since)}` : ''}.</b>
      ${d.x.to ? ` Use <a class="nm" href="${declHref(d.x.to)}">${esc(d.x.to)}</a> instead.` : ''}
      ${d.x.why ? ` ${esc(d.x.why)}` : ''}</div>` : '';
  const rejected = d.f !== undefined
    ? `<div class="card bad-card"><b>Rejected by Tenet's kernel.</b> The checker did not accept this declaration: <code>${esc(d.f)}</code></div>`
    : '';
  const checkedNote = S.manifest.check && d.f === undefined && d.k !== 'axiom'
    ? `<a class="dim" href="#/certificate" title="what an independent re-check does and does not certify">✓ re-checked</a>` : '';
  const src = sourceUrl(mod, d.l);
  const ns = name.lastIndexOf('.');
  const title = ns < 0
    ? esc(name)
    : `<a class="ns" href="#/ns/${encodeURIComponent(name.slice(0, ns))}"
         title="everything in this namespace">${esc(name.slice(0, ns + 1))}</a>${esc(name.slice(ns + 1))}`;

  const usedBy = d.b.filter(keep); // the generator stores the most used first
  const stmt = d.t.filter(keep), proof = d.u.filter(keep);
  // Each list discloses what its own filter took out. One total covering all three lists was reported under
  // "Used by" alone, so a helper hidden from Uses was announced as a dependent that had been hidden. And Uses
  // disclosed nothing at all, which is why its heading said 27 while "count what this rests on" said 29: the
  // heading counted what survived the filter, the graph counts everything, and neither said which it was doing.
  const hiddenBy = d.b.length - usedBy.length;
  const hiddenUses = (d.t.length - stmt.length) + (d.u.length - proof.length);
  const helpers = (k) => k ? `, ${k} generated helper${k === 1 ? '' : 's'} hidden` : '';
  const bySide = (ids) => [...ids].sort((a, b) => S.used[b] - S.used[a]);

  $('#main').innerHTML = `
    <h1>${title}</h1>
    ${twins.length ? `<div class="card twins"><b>${twins.length === 1 ? 'Another declaration has this name.' : `${twins.length} other declarations have this name.`}</b>
      They are in modules never imported together, so each is its own theorem: ${twins.map(t =>
        `<a href="#/i/${t}">${esc(S.modules[moduleOfId(t)].n)}</a>`).join(', ')}.</div>` : ''}
    <p class="sub">${kindBadge(d.k)} ${markBadges(d)} <span>in <a class="mono" href="${modHref(mod)}">${esc(mod)}</a></span>${src ? `<a href="${esc(src)}" target="_blank" rel="noopener">source${d.l ? ` line ${d.l[0]}` : ''} ↗</a>` : ''}</p>
    ${verdict} ${checkedNote} <button class="more cite" id="cite">cite this</button>
    ${dep}
    ${rejected}
    <details class="explain" ${currentRole() === 'new' ? 'open' : ''}><summary>What am I looking at?</summary>
      <p><b>Statement:</b> the claim itself, in Lean's notation. Names in it are links to their definitions. The <b>badge</b> above says what the proof ultimately assumes: nothing beyond Lean's three standard axioms is the normal, good case; <b>sorry</b> means an unfinished proof somewhere underneath.</p>
      <p><b>Neighborhood:</b> this declaration in the middle, what it is built from on the left, what is built on it on the right. Click a box to move there; "show two steps" goes one ring further.</p>
      <p><b>Uses / Used by:</b> the same in list form, with a count of how many declarations depend on each. <b>Axioms:</b> everything assumed, transitively. <b>Source:</b> the lines a person wrote, on GitHub. ${S.manifest.check ? '<b>✓ re-checked:</b> an independent kernel re-verified this proof.' : ''} <a href="#/">More on the home page.</a></p>
    </details>
    ${importLine(mod)}
    <p class="copies">${[
      ['the name', name],
      ['#check', `#check @${name}`],
      ['import', `import ${mod}`],
      ['a link', location.href],
    ].map(([label, text]) => copyButton(text, label)).join(' ')}
      <button class="more" id="savebtn">${isSaved(name) ? 'saved ✓' : 'save'}</button>
      <button class="more" id="export">export what it rests on</button>
      <label class="dim" for="vswith" style="margin-left:6px">compare with</label>
      <input id="vswith" class="prefix" style="max-width:240px" placeholder="another declaration">
      <button class="more" id="vsgo">go</button></p>
    <h2>Statement</h2>
    ${statementBlock(d)}
    ${bodyBlock(d, src)}
    ${fieldsBlock(d)}
    ${ctorsBlock(d)}
    ${(() => {
      const mins = minimalImports(d, mod);
      return mins.length
        ? `<h2>Minimal imports <small>to write this statement, besides ${esc(mod)}</small></h2>
           <p class="dim">The fewest modules whose import closures cover every constant the statement mentions.</p>
           <pre class="minimports">${mins.map(m => esc('import ' + m)).join('\n')}</pre>
           ${copyButton(mins.map(m => 'import ' + m).join('\n'), 'copy all')}`
        : '';
    })()}
    ${d.d ? `<h2>Docstring</h2><div class="doc">${linkDocNames(renderDoc(d.d))}</div>` : ''}
    ${sourceBlock(mod, d.l)}
    <h2>Neighborhood <small>click a node to move there</small></h2>
    <div id="graph"></div>
    <div class="cols">
      <div>
        <h2>Uses <small>${fmt(stmt.length + proof.length)} constants${helpers(hiddenUses)}</small></h2>
        ${stmt.length ? `<p class="dim" style="margin:0 0 4px">in the statement (${stmt.length})</p><ul class="list">${bySide(stmt).map(nameLink).join('')}</ul>` : ''}
        ${proof.length ? `<p class="dim" style="margin:12px 0 4px">only in the ${d.k === 'theorem' ? 'proof' : 'body'} (${proof.length})</p><ul class="list" id="proof-list">${bySide(proof).slice(0, 40).map(nameLink).join('')}</ul>${proof.length > 40 ? `<p><button class="more" id="more-proof">show all ${fmt(proof.length)}</button></p>` : ''}` : ''}
        ${stmt.length + proof.length === 0 ? '<p class="dim">nothing: this is a leaf</p>' : ''}
      </div>
      <div>
        <h2>Used by <small>${fmt(d.bc)} declarations${d.bc > d.b.length ? `, the ${d.b.length} most used shown` : ''}${helpers(hiddenBy)}</small></h2>
        ${usedBy.length ? `<ul class="list">${usedBy.map(nameLink).join('')}</ul>` : '<p class="dim">nothing yet</p>'}
      </div>
    </div>
    ${d.ch !== undefined || d.k === 'inductive' ? `<h2>${d.k === 'inductive' ? 'Produced by' : 'Concluding the same thing'}
      <small>${d.k === 'inductive'
        ? 'declarations whose conclusion is this type; for a class, its instances'
        : `other declarations ending in <code>${esc(displayName(S.names[d.ch]))}</code>`}</small></h2>
      <div class="card">
        <p style="margin:0"><button class="more" id="concl" data-target="${d.k === 'inductive' ? id : d.ch}">find them</button>
          <span id="conclnote" class="dim"></span></p>
        <div id="conclout"></div>
      </div>` : ''}
    <h2>Everything underneath <small>the whole graph, loaded on request</small></h2>
    <div class="card">
      <p style="margin:0 0 8px"><button class="more" id="weigh">count what this rests on</button>
        <span id="weight" class="dim"></span></p>
      <p style="margin:0 0 8px"><button class="more" id="blast">count what would fall if this were wrong</button>
        <span id="blastout" class="dim"></span></p>
      <p style="margin:0"><label class="dim" for="pathto">shortest chain from here to</label>
        <input id="pathto" class="prefix" placeholder="a declaration name, e.g. Classical.choice">
        <button class="more" id="findpath">find</button></p>
      <div id="pathout"></div>
    </div>
    <h2>Axioms <small>${axioms.length === 0 ? 'none' : `${axioms.length} in the transitive closure`}</small></h2>
    <ul class="list">${axioms.map(a => `<li><a class="nm" href="${declHref(a)}">${esc(a)}</a><span class="mod">${std.has(a) ? 'standard: part of Lean\'s logic' : a === 'sorryAx' ? 'an incomplete proof somewhere below' : 'an assumption this declaration carries'}</span>${
      std.has(a) ? '' : `<button class="more why" data-why="${esc(a)}">why</button>`}</li>`).join('')}</ul>
    <div id="whyout"></div>`;
  rememberVisit(name);
  wireSource();
  const save = $('#savebtn');
  if (save) save.onclick = () => { save.textContent = toggleSaved(name) ? 'saved ✓' : 'save'; };
  const vsgo = $('#vsgo');
  if (vsgo) vsgo.onclick = () => {
    const other = $('#vswith').value.trim();
    if (other) location.hash = `#/vs/${encodeURIComponent(name)}/${encodeURIComponent(other)}`;
  };
  // Everything a declaration rests on, as a file. Two issues asked for a way into this data that is not a
  // browser; this is the smallest one, and it needs no server because the graph is already here.
  const ex = $('#export');
  if (ex) ex.onclick = async () => {
    ex.disabled = true;
    ex.textContent = 'building…';
    try {
      const g = await loadGraph(setStatus);
      const seen = new Set([id]), stack = [id], edges = [];
      while (stack.length) {
        const v = stack.pop();
        for (let e = g.fOff[v]; e < g.fOff[v + 1]; e++) {
          const u = g.fTo[e];
          edges.push([v, u]);
          if (!seen.has(u)) { seen.add(u); stack.push(u); }
        }
      }
      const payload = {
        declaration: name,
        library: S.manifest.title,
        lean: S.manifest.lean,
        generated: S.manifest.generated,
        restsOn: seen.size - 1,
        nodes: [...seen].map(i => ({ id: i, name: S.names[i], kind: kindOf(i), module: S.modules[moduleOfId(i)].n })),
        edges: edges.map(([f, to]) => [f, to]),
      };
      const blob = new Blob([JSON.stringify(payload, null, 1)], { type: 'application/json' });
      const url = URL.createObjectURL(blob);
      const a = document.createElement('a');
      a.href = url;
      a.download = `${name.replace(/[^\w.]+/g, '_')}-cone.json`;
      a.click();
      URL.revokeObjectURL(url);
      ex.textContent = `exported ${fmt(seen.size - 1)} constants`;
    } catch (e) {
      ex.disabled = false;
      ex.textContent = 'could not load the graph';
      console.error(e);
    }
  };
  const concl = $('#concl');
  if (concl) concl.onclick = async () => {
    concl.disabled = true;
    concl.textContent = 'looking…';
    try {
      const { hits, scanned } = await concludedBy(parseInt(concl.dataset.target, 10));
      $('#conclout').innerHTML = hits.length
        ? `<ul class="list">${hits.map(nameLink).join('')}</ul>`
        : '<p class="dim">nothing else in this bundle concludes it</p>';
      $('#conclnote').textContent = hits.length
        ? `${hits.length} found, from ${fmt(scanned)} that mention it`
        : `none among ${fmt(scanned)} that mention it`;
      concl.remove();
    } catch (e) {
      concl.disabled = false;
      concl.textContent = 'could not load the graph';
      console.error(e);
    }
  };
  $('#blast').onclick = async () => {
    const b = $('#blast');
    b.disabled = true;
    b.textContent = 'loading…';
    try {
      const g = await loadGraph(setStatus);
      const n = reachTo(g, id);
      $('#blastout').textContent = n === 0
        ? 'nothing depends on this, directly or otherwise'
        : `${fmt(n)} declarations depend on this, directly or otherwise: ${(100 * n / S.names.length).toFixed(n / S.names.length < 0.01 ? 2 : 1)}% of the bundle`;
      b.remove();
    } catch (e) {
      // inverting 20.9 million edges needs about 100 MB; a phone may simply refuse
      b.disabled = false;
      b.textContent = 'could not build the reverse graph here (it needs about 100 MB)';
      console.error(e);
    }
  };
  $('#weigh').onclick = async () => {
    const b = $('#weigh');
    b.disabled = true;
    b.textContent = 'loading…';
    try {
      const g = await loadGraph(setStatus);
      const count = reachFrom(g, id);
      $('#weight').textContent = `rests on ${fmt(count)} constants in all, ${fmt(d.t.length + d.u.length)} of them directly`;
      b.remove();
    } catch (e) {
      b.textContent = 'could not load the graph';
      console.error(e);
    }
  };
  $('#findpath').onclick = async () => {
    const want = $('#pathto').value.trim();
    const out = $('#pathout');
    const target = idOfName(want);
    if (target < 0) { out.innerHTML = `<p class="dim">No declaration named <code>${esc(want)}</code>.</p>`; return; }
    out.innerHTML = '<p class="dim">looking…</p>';
    try {
      const g = await loadGraph(setStatus);
      const chain = pathBetween(g, id, target);
      out.innerHTML = chain
        ? `<p class="dim">${chain.length - 1} step${chain.length === 2 ? '' : 's'}:</p><ul class="chain">${chain.map((c, i) =>
            `<li${i === chain.length - 1 ? ' class="last"' : ''}>${kindBadge(kindOf(c))} <a class="nm" href="${declHref(S.names[c])}">${esc(S.names[c])}</a>
             <span class="mod">${esc(S.modules[moduleOfId(c)].n)}</span></li>`).join('')}</ul>`
        : `<p class="dim"><code>${esc(name)}</code> does not depend on <code>${esc(want)}</code>, directly or through anything else.</p>`;
    } catch (e) {
      out.innerHTML = '<p class="dim">could not load the graph</p>';
      console.error(e);
    }
  };
  $('#pathto').onkeydown = (ev) => { if (ev.key === 'Enter') $('#findpath').click(); };
  $('#cite').onclick = () => {
    // What a reader needs to check the claim later: the declaration, the library and the revision it came from.
    const lib = S.manifest.libraries.find(l => l.prefixes.length === 0) || {};
    const text = `${name} (${d.k}), ${mod}, ${S.manifest.title || 'Lean'} at ${(lib.rev || '').slice(0, 12) || S.manifest.lean}`
      + `, via ${location.href}`;
    navigator.clipboard?.writeText(text).then(
      () => { $('#cite').textContent = 'copied'; setTimeout(() => { const c = $('#cite'); if (c) c.textContent = 'cite this'; }, 2000); },
      () => { window.prompt('Copy this:', text); });
  };
  // "This rests on sorryAx" is a fact without a reason until you can see the chain that carries it. The graph
  // is already loaded for the weight and the chain search; this asks it the one question the page implies.
  for (const b of $('#main').querySelectorAll('button.why')) {
    b.onclick = async () => {
      const want = b.dataset.why, out = $('#whyout');
      b.disabled = true;
      out.innerHTML = '<p class="dim">looking…</p>';
      try {
        const g = await loadGraph(setStatus);
        const chain = pathBetween(g, id, idOfName(want));
        out.innerHTML = chain
          ? `<p class="dim">Why <code>${esc(want)}</code>: ${chain.length - 1} step${chain.length === 2 ? '' : 's'}.</p>
             <p class="chain">${chain.map(i => `<a class="nm" href="#/i/${i}">${esc(displayName(S.names[i]))}</a>`).join(' <span class="dim">→</span> ')}</p>`
          : `<p class="dim">No chain found to <code>${esc(want)}</code>, which should not happen if it is listed above.</p>`;
      } catch (e) {
        out.innerHTML = '<p class="dim">could not load the graph</p>';
        console.error(e);
      }
      b.disabled = false;
    };
  }
  const more = $('#more-proof');
  if (more) more.onclick = () => { $('#proof-list').innerHTML = bySide(proof).map(nameLink).join(''); more.remove(); };
  renderGraph(id, name, bySide(stmt), bySide(proof), usedBy);
  const two = $('#two-steps');
  if (two) two.onclick = async () => {
    two.disabled = true;
    two.textContent = 'loading…';
    try {
      await renderGraph(id, name, bySide(stmt), bySide(proof), usedBy, true);
    } catch (e) {
      two.textContent = 'could not load the second step';
      console.error(e);
    }
  };
}

/**
 * Declarations nothing references. Cheap, because the in-degree table is already loaded: a filter over it. Useful
 * to a maintainer looking for dead weight, and to anyone wondering what a library proved and never used.
 */
async function pageUnused(prefix) {
  await loadNames();
  prefix = (prefix || '').replace(/^\/*/, '');
  const hits = [];
  for (let i = 0; i < S.used.length; i++) {
    if (S.used[i] !== 0 && S.used[i] !== undefined) continue;
    if (!keep(i)) continue;
    const k = kindOf(i);
    if (k === 'constructor' || k === 'recursor') continue; // made by the kernel, not by a person
    if (prefix && !S.names[i].startsWith(prefix)) continue;
    hits.push(i);
  }
  hits.sort((a, b) => S.names[a].localeCompare(S.names[b]));
  $('#main').innerHTML = `
    <h1 class="prose">Nothing uses these</h1>
    <p class="dim">${fmt(hits.length)} declarations that no other declaration references${prefix ? ` under <code>${esc(prefix)}</code>` : ''}.
    Generated helpers, constructors and recursors are left out. A top-level theorem belongs here; a lemma usually does not.</p>
    <p><input id="unused-prefix" class="prefix" placeholder="filter by name, e.g. Mathlib.Analysis" value="${esc(prefix)}"></p>
    <ul class="list">${hits.slice(0, 500).map(nameLink).join('')}</ul>
    ${hits.length > 500 ? `<p class="dim">and ${fmt(hits.length - 500)} more; narrow with the filter</p>` : ''}`;
  const box = $('#unused-prefix');
  box.onkeydown = (ev) => { if (ev.key === 'Enter') location.hash = '#/unused/' + encodeURIComponent(box.value.trim()); };
}

/**
 * Every declaration resting on `sorry`, which for an unfinished formalization is its progress map: what is still
 * conditional, and how much stands on each hole. Mathlib has none, so the page says so plainly.
 */
/**
 * Every axiom the library rests on, how much rests on it, and for the unusual ones, what.
 *
 * A declaration page answers this one declaration at a time, which means the question "what does this library
 * assume beyond Lean's three axioms" could only be answered by opening every page in it. The counts are
 * computed over the whole graph when the bundle is built, so this page is a read rather than a search.
 */
/**
 * A namespace, which is the unit people actually think in: `Nat`, `Finset`, `CategoryTheory.Limits`. Modules
 * are files and the map is directories; neither is the name a mathematician would use for a body of work.
 */
/**
 * Two declarations side by side: what they share, and what is theirs alone.
 *
 * "Are these the same lemma wearing different clothes" and "what does this one need that the other does not"
 * are questions people ask constantly and answer by opening two tabs. The graph already in the bundle answers
 * both exactly, so the answer can be a number rather than an impression.
 */
async function pageVersus(arg) {
  await loadNames();
  const [a, b] = (arg || '').split('/').map(x => decodeURIComponent(x || '')).filter(Boolean);
  if (!a || !b) {
    $('#main').innerHTML = `<h1 class="prose">Compare two declarations</h1>
      <p class="dim">Put two names in the address: <code>#/vs/Nat.add_comm/Nat.mul_comm</code>.
      You will also find a "compare with" box on any declaration page.</p>`;
    return;
  }
  const ia = idOfName(a), ib = idOfName(b);
  if (ia < 0 || ib < 0) {
    $('#main').innerHTML = `<h1 class="prose">Compare</h1><p>No declaration named
      <code>${esc(ia < 0 ? a : b)}</code> in this bundle.</p>`;
    return;
  }
  $('#main').innerHTML = `<h1 class="prose">${esc(a)} and ${esc(b)}</h1><p class="dim">loading the graph…</p>`;
  const [da, db, g] = await Promise.all([decl(ia), decl(ib), loadGraph(setStatus)]);
  const cone = (id) => { const s = new Set([id]); const st = [id];
    while (st.length) { const v = st.pop();
      for (let e = g.fOff[v]; e < g.fOff[v + 1]; e++) { const u = g.fTo[e]; if (!s.has(u)) { s.add(u); st.push(u); } } }
    s.delete(id); return s; };
  const ca = cone(ia), cb = cone(ib);
  const both = [...ca].filter(x => cb.has(x));
  const onlyA = [...ca].filter(x => !cb.has(x));
  const onlyB = [...cb].filter(x => !ca.has(x));
  const list = (ids) => `<ul class="list">${ids.filter(keep).sort((x, y) => S.used[y] - S.used[x])
    .slice(0, 60).map(nameLink).join('') || '<li class="dim">nothing</li>'}</ul>`;
  const side = (name, d) => `<div>
    <h2><a class="nm" href="${declHref(name)}">${esc(name)}</a></h2>
    <p class="sub">${kindBadge(d.k)} <span>in ${esc(S.modules[moduleOfId(idOfName(name))].n)}</span></p>
    <pre>${colorStatement(linkStatement(d.s || '', d.t || []))}</pre></div>`;
  $('#main').innerHTML = `
    <h1 class="prose">${esc(a)} and ${esc(b)}</h1>
    <div class="cols">${side(a, da)}${side(b, db)}</div>
    <ul class="stats">
      <div><b>${fmt(both.length)}</b>they both rest on</div>
      <div><b>${fmt(onlyA.length)}</b>only ${esc(shortName(a))}</div>
      <div><b>${fmt(onlyB.length)}</b>only ${esc(shortName(b))}</div>
      <div><b>${((100 * both.length) / Math.max(1, new Set([...ca, ...cb]).size)).toFixed(0)}%</b>overlap</div>
    </ul>
    <div class="cols">
      <div><h2>Only ${esc(shortName(a))} needs</h2>${list(onlyA)}</div>
      <div><h2>Only ${esc(shortName(b))} needs</h2>${list(onlyB)}</div>
    </div>
    <h2>Both rest on <small>the ${Math.min(60, both.length)} most depended-upon</small></h2>
    ${list(both)}`;
}

/**
 * A reading list, kept in this browser. A reference tool is used across days, and "the thing I was looking at
 * on Tuesday" is otherwise gone. Nothing leaves the machine; there is no account and nowhere to send it.
 */
const SAVED_KEY = 'saved';
function savedNames() {
  try { return JSON.parse(localStorage.getItem(SAVED_KEY) || '[]'); } catch (e) { return []; }
}
function isSaved(name) { return savedNames().includes(name); }
function toggleSaved(name) {
  const now = savedNames();
  const at = now.indexOf(name);
  if (at >= 0) now.splice(at, 1); else now.unshift(name);
  try { localStorage.setItem(SAVED_KEY, JSON.stringify(now.slice(0, 500))); } catch (e) { /* private window */ }
  return at < 0;
}
function rememberVisit(name) {
  try {
    const seen = JSON.parse(localStorage.getItem('seen') || '[]').filter(x => x !== name);
    seen.unshift(name);
    localStorage.setItem('seen', JSON.stringify(seen.slice(0, 100)));
  } catch (e) { /* private window: this is a convenience, not state anything depends on */ }
}
async function pageSaved() {
  await loadNames();
  const saved = savedNames();
  let seen = [];
  try { seen = JSON.parse(localStorage.getItem('seen') || '[]'); } catch (e) { /* fine */ }
  const rows = (names) => names.length
    ? `<ul class="list">${names.map(n => { const i = idOfName(n);
        return `<li>${i >= 0 ? kindBadge(kindOf(i)) : ''} <a class="nm" href="${declHref(n)}">${esc(n)}</a>${
          i >= 0 ? `<span class="mod">${esc(S.modules[moduleOfId(i)].n)}</span>` : '<span class="mod">not in this library</span>'}</li>`;
      }).join('')}</ul>`
    : '<p class="dim">nothing yet</p>';
  $('#main').innerHTML = `
    <h1 class="prose">Saved</h1>
    <p class="dim">Kept in this browser only. There is no account and nothing is sent anywhere, so clearing site
      data clears this too.</p>
    <h2>Saved <small>${saved.length}</small></h2>${rows(saved)}
    ${saved.length ? `<p>${copyButton(saved.join('\n'), 'copy the names')}</p>` : ''}
    <h2>Recently opened <small>${seen.length}</small></h2>${rows(seen.slice(0, 40))}`;
}

async function pageNamespace(ns) {
  await loadNames();
  if (!ns) { $('#main').innerHTML = '<p>Name a namespace, for example <a href="#/ns/Nat">#/ns/Nat</a>.</p>'; return; }
  const prefix = ns + '.';
  const members = [], subs = new Map();
  const byKind = new Map();
  for (let i = 0; i < S.names.length; i++) {
    const n = S.names[i];
    if (!n.startsWith(prefix)) continue;
    if (!keep(i)) continue;
    const rest = n.slice(prefix.length);
    const dot = rest.indexOf('.');
    if (dot < 0) members.push(i); else subs.set(rest.slice(0, dot), (subs.get(rest.slice(0, dot)) || 0) + 1);
    byKind.set(kindOf(i), (byKind.get(kindOf(i)) || 0) + 1);
  }
  const total = members.length + [...subs.values()].reduce((a, b) => a + b, 0);
  if (!total) { $('#main').innerHTML = `<p>Nothing in this bundle is named <code>${esc(ns)}.…</code></p>`; return; }
  const parts = ns.split('.');
  const top = members.slice().sort((a, b) => S.used[b] - S.used[a]).slice(0, 40);
  $('#main').innerHTML = `
    <h1>${parts.map((_, i) => `<a class="ns" href="#/ns/${encodeURIComponent(parts.slice(0, i + 1).join('.'))}">${esc(parts[i])}</a>`).join('.')}</h1>
    <p class="sub"><span>namespace, ${fmt(total)} declarations</span>${idOfName(ns) >= 0 ? `<a href="${declHref(ns)}">the declaration itself ↗</a>` : ''}</p>
    <ul class="stats">${[...byKind.entries()].sort((a, b) => b[1] - a[1]).slice(0, 5)
      .map(([k, c]) => `<div><b>${fmt(c)}</b>${esc(k)}${c === 1 ? '' : 's'}</div>`).join('')}</ul>
    ${subs.size ? `<h2>Inside it <small>${subs.size} sub-namespaces</small></h2>
      <ul class="list">${[...subs.entries()].sort((a, b) => b[1] - a[1]).map(([s, c]) =>
        `<li><a class="nm" href="#/ns/${encodeURIComponent(ns + '.' + s)}">${esc(s)}</a><span class="n">${fmt(c)}</span></li>`).join('')}</ul>` : ''}
    <h2>Most depended upon here <small>${members.length} named directly in ${esc(ns)}</small></h2>
    <ul class="list">${top.map(nameLink).join('') || '<li class="dim">nothing directly in this namespace</li>'}</ul>`;
}

/** Everything deprecated, with what replaced it: the list you work through when upgrading. */
async function pageDeprecated() {
  await loadNames();
  $('#main').innerHTML = `<h1 class="prose">Deprecated</h1><p class="dim">reading every module…</p>`;
  const rows = [];
  for (let mi = 0; mi < S.modules.length; mi++) {
    let arr;
    try { arr = await shard(mi); } catch (e) { continue; }
    for (const d of arr) {
      if (d.x) rows.push(d);
    }
    if (mi % 800 === 0) $('#main').querySelector('p').textContent = `reading… ${fmt(rows.length)} so far`;
  }
  rows.sort((a, b) => b.bc - a.bc);
  $('#main').innerHTML = `
    <h1 class="prose">Deprecated</h1>
    <p class="dim">${fmt(rows.length)} declarations are marked <code>@[deprecated]</code>, most depended-upon first.
      The number on the right is how much still uses each one, which is the order to fix them in.</p>
    <ul class="list">${rows.slice(0, 500).map(d => `<li><a class="nm dep" href="${declHref(d.n)}">${esc(d.n)}</a>
      <span class="mod">${d.x.to ? `use <a class="nm" href="${declHref(d.x.to)}">${esc(d.x.to)}</a>` : 'no replacement named'}${
        d.x.since ? ` · since ${esc(d.x.since)}` : ''}</span><span class="n">${fmt(d.bc)}</span></li>`).join('')}</ul>
    ${rows.length > 500 ? `<p class="dim">the 500 most depended-upon shown, of ${fmt(rows.length)}</p>` : ''}`;
}

/**
 * What one library has that another does not. Every bundle carries a name list and a digest per declaration,
 * which is all this needs: names in one and not the other, and names in both whose statement or body has
 * changed. Nothing else can answer it, because nothing else holds two whole libraries at once.
 */
async function pageCompare(arg) {
  const [a, b] = (arg || '').split('/').filter(Boolean);
  const list = S.projects || [];
  if (!a || !b) {
    $('#main').innerHTML = `<h1 class="prose">Compare two libraries</h1>
      <p class="dim">What one has that the other does not, and what they say differently about the same name.</p>
      ${list.length < 2 ? '<p>This site carries one library.</p>' : `<ul class="list">${
        list.flatMap(x => list.filter(y => y.slug !== x.slug).map(y =>
          `<li><a class="nm" href="#/compare/${x.slug}/${y.slug}">${esc(x.title)} against ${esc(y.title)}</a></li>`)).join('')}</ul>`}`;
    return;
  }
  $('#main').innerHTML = `<h1 class="prose">${esc(a)} against ${esc(b)}</h1><p class="dim">fetching both name lists…</p>`;
  const load = async (slug) => {
    const un = async (f) => new Response(
      (await fetch(`data/${slug}/${f}.gz`)).body.pipeThrough(new DecompressionStream('gzip')));
    const names = (await (await un('names.txt')).text()).replace(/\n$/, '').split('\n');
    const dig = new Uint8Array(await (await un('digest.bin')).arrayBuffer());
    const by = new Map();
    for (let i = 0; i < names.length; i++) {
      // a name two modules both declare gets one entry; the comparison is about names, not occurrences
      // the whole 64-bit digest as a string: half of it would still be unlikely to collide, but "unlikely"
      // is not a reason to throw away four bytes that are already in hand
      if (!by.has(names[i])) {
        let h = '';
        for (let k = 0; k < 8; k++) h += dig[8 * i + k].toString(16).padStart(2, '0');
        by.set(names[i], h);
      }
    }
    return by;
  };
  let A, B, ma, mb;
  try {
    [A, B, ma, mb] = await Promise.all([load(a), load(b),
      (await fetch(`data/${a}/manifest.json`)).json(), (await fetch(`data/${b}/manifest.json`)).json()]);
  }
  catch (e) { $('#main').innerHTML = `<h1 class="prose">Compare</h1><p>Could not read both libraries: <code>${esc(e.message)}</code></p>`; return; }
  // The digest covers a name, its statement and, for a definition, its body. A bundle built before bodies
  // existed hashed less, so comparing it with a newer one marks every definition as changed: 217,503 of them
  // between two bundles that actually agree. That is a difference decided by the generator rather than by the
  // libraries, and reporting it as content would be a lie with a number attached.
  const sameInputs = (ma.definitionBodies === undefined) === (mb.definitionBodies === undefined);
  const onlyA = [], onlyB = [], changed = [];
  for (const [n, h] of A) { if (!B.has(n)) onlyA.push(n); else if (B.get(n) !== h) changed.push(n); }
  for (const n of B.keys()) if (!A.has(n)) onlyB.push(n);
  const show = (title, names2, slug, note) => `<h2>${title} <small>${fmt(names2.length)}</small></h2>
    ${note ? `<p class="dim">${note}</p>` : ''}
    <ul class="list">${names2.slice(0, 300).sort().map(n =>
      `<li><a class="nm" href="?p=${encodeURIComponent(slug)}#/d/${encodeURIComponent(n)}">${esc(n)}</a></li>`).join('')}</ul>
    ${names2.length > 300 ? `<p class="dim">300 of ${fmt(names2.length)} shown</p>` : ''}`;
  $('#main').innerHTML = `
    <h1 class="prose">${esc(a)} against ${esc(b)}</h1>
    <ul class="stats">
      <div><b>${fmt(onlyA.length)}</b>only in ${esc(a)}</div>
      <div><b>${fmt(onlyB.length)}</b>only in ${esc(b)}</div>
      <div><b>${sameInputs ? fmt(changed.length) : '—'}</b>say something different</div>
      <div><b>${fmt(A.size)}</b>names in ${esc(a)}</div>
    </ul>
    ${show(`Only in ${esc(a)}`, onlyA, a)}
    ${show(`Only in ${esc(b)}`, onlyB, b)}
    ${sameInputs
      ? show('Same name, different statement', changed, a,
         'The digest covers the name, the statement and, for a definition, its body. A difference here means the two libraries do not agree about what this declaration says.')
      : `<h2>Same name, different statement</h2>
         <div class="card bad-card"><b>Not comparable.</b> These two bundles were built by different versions of
         the generator: ${esc(ma.definitionBodies === undefined ? a : b)} predates definition bodies, so its digest
         covers less than the other's. Every definition would appear to have changed, which would be a number
         about the generator rather than about the libraries. Rebuild the older bundle to compare them.</div>`}`;
}

/**
 * What re-checking a library does and does not certify.
 *
 * This is the page most likely to be read as a bigger claim than it is, so it says the limits before it says
 * the result. A second kernel accepting a proof raises the cost of a wrong answer; it does not make the answer
 * true, and an attestation records who ran what rather than whether they were right. Tenet is an independent
 * kernel, not a verified one, which is exactly the distinction con-leche exists to close and this does not.
 */
async function pageCertificate() {
  const m = S.manifest;
  const c = m.check;
  const site = siteRepo();
  const owner = site ? site.owner : '';
  const lib = (m.libraries || []).find(l => (l.prefixes || []).length === 0) || {};
  const repro = [
    `git clone ${lib.url || '<the project>'} project`,
    lib.rev ? `git -C project checkout ${lib.rev}` : null,
    'cd project && lake exe cache get && lake build && cd ..',
    'dotnet tool install -g tenet',
    'tenet check project --all --report check.json',
  ].filter(Boolean).join('\n');
  $('#main').innerHTML = `
    <h1 class="prose">Certifying a proof</h1>
    <p class="dim">What an independent re-check establishes, and what it leaves untouched. The second list is
      the important one.</p>

    ${c ? `<p><span class="verdict ok">${fmt(c.checked)} declarations re-derived by Tenet ${esc(c.tenet)}, ${fmt(c.failed)} rejected</span></p>`
        : '<p><span class="verdict warn">This library has not been re-checked, so its pages report what proofs cite and nothing more.</span></p>'}

    <h2>What it establishes</h2>
    <ol class="tour">
      <li><b>A second kernel agrees.</b> Lean built these files and accepted them. Tenet then read the compiled
        <code>.olean</code> files and re-derived every declaration from the type theory, sharing no code with
        Lean. A mistake in Lean's C++ kernel is one Tenet would not repeat, because it was written from the
        rules rather than translated from the implementation.</li>
      <li><b>Over exactly these bytes.</b> The verdict is a file,
        <a href="${DATA}check.json">check.json</a>, naming every input by SHA-256${c ? `, and the report itself
        hashes to <code>${esc(c.sha256)}</code>` : ''}. Change one byte of one input and the verdict no longer
        describes it.</li>
      <li><b>Run in the open.</b> ${site
        ? `It was published by <a href="${esc(site.url)}/actions">a public workflow</a> and signed with
           GitHub's artifact attestation, so who ran what, over which bytes, when, is on a public transparency
           log that neither I nor GitHub can quietly rewrite.`
        : 'This bundle was produced on a private machine and carries no attestation, so you have only my word for how it was made.'}</li>
      <li><b>And it can be redone without me.</b> Same inputs, same checker, same answer. The commands are below
        and they do not involve this site.</li>
    </ol>

    <h2>What it does not establish</h2>
    <ul>
      <li><b>Not that the theorem is true.</b> Only that the proof term type-checks against the stated theorem.
        If the statement does not say what you think it says, a green verdict is worth nothing. Read the
        statement, follow its constants to their definitions, and read those: that is what the "in the statement"
        list on every page is for.</li>
      <li><b>Not that Tenet is correct.</b> Tenet is an <i>independent</i> kernel, not a <i>verified</i> one.
        There is no machine-checked proof that it accepts only sound derivations. Two independent programs
        agreeing is evidence, not proof, and they can share a mistake if they share a misreading of the rules.
        <a href="?p=conleche#/d/ConLeche.model_exists">con-leche</a> is what a verified checker looks like, and
        the difference is the point.</li>
      <li><b>Not that a signature makes anything true.</b> An attestation says who ran what. A signed report
        from a buggy checker is a signed mistake, and it is signed just as firmly as a correct one.</li>
      <li><b>Not that the axioms are ones you accept.</b> A proof resting only on <code>propext</code>,
        <code>Classical.choice</code> and <code>Quot.sound</code> still rests on those.
        <a href="#/axioms">See what this library assumes.</a></li>
      <li><b>Not anything about code that was not checked.</b> <code>unsafe</code> and <code>partial</code>
        definitions are not checked the way everything else is, and they are marked as such on their pages.</li>
    </ul>

    <h2>Redo it yourself</h2>
    <p class="dim">Nothing here talks to this site. It downloads the project, builds it, and checks it on your
      machine, and you compare the report to the one above.</p>
    <pre>${esc(repro)}</pre>
    ${copyButton(repro, 'copy the commands')}
    ${site ? `<p style="margin-top:14px">Then check the published report is the one the workflow produced.
      <code>verify</code> says nothing at all when it succeeds, so ask for the verdict:</p>
      <pre>${esc(`gh attestation verify check.json --owner ${owner} --format json`)}</pre>
      ${copyButton(`gh attestation verify check.json --owner ${owner} --format json`, 'copy')}` : ''}

    ${c ? `<h2>This run</h2>
      <ul class="list">
        <li><span class="nm">checker</span><span class="mod">Tenet ${esc(c.tenet)}, an independent Lean 4 kernel on .NET</span></li>
        <li><span class="nm">Lean</span><span class="mod">${esc(c.lean)}</span></li>
        <li><span class="nm">declarations</span><span class="mod">${fmt(c.checked)} re-derived, ${fmt(c.failed)} rejected</span></li>
        <li><span class="nm">took</span><span class="mod">${fmt(Math.round(c.seconds))} seconds</span></li>
        <li><span class="nm">on</span><span class="mod">${esc(c.date || m.generated)}</span></li>
        ${lib.rev ? `<li><span class="nm">source</span><span class="mod">${esc(lib.name || '')} at ${esc(lib.rev)}</span></li>` : ''}
      </ul>` : ''}`;
}

async function pageAxioms() {
  await loadNames();
  const m = S.manifest;
  const use = m.axiomUse;
  if (!use) {
    $('#main').innerHTML = `<h1 class="prose">Axioms</h1>
      <p class="dim">This bundle was generated before the axiom census existed. Regenerate it to see this page.</p>`;
    return;
  }
  const std = new Set(m.standardAxioms);
  const rows = m.axioms.map((name, i) => ({ name, n: use[i], standard: std.has(name) }))
    .sort((a, b) => (a.standard === b.standard ? b.n - a.n : (a.standard ? 1 : -1)));
  const beyond = rows.filter(r => !r.standard && r.n > 0);
  const unused = rows.filter(r => r.n === 0).length;
  const holders = m.axiomHolders || {};
  const section = (r) => {
    const ids = (holders[r.name] || []).filter(keep);
    return `<h2><a class="nm" href="${declHref(r.name)}">${esc(r.name)}</a>
      <small>${fmt(r.n)} declaration${r.n === 1 ? '' : 's'} rest${r.n === 1 ? 's' : ''} on it${
        r.name === 'sorryAx' ? ', an unfinished proof' : ''}</small></h2>
      ${ids.length ? `<ul class="list">${ids.map(nameLink).join('')}</ul>${
        r.n > ids.length ? `<p class="dim">the ${ids.length} most depended-upon shown, of ${fmt(r.n)}</p>` : ''}`
        : '<p class="dim">no list stored for this one</p>'}`;
  };
  $('#main').innerHTML = `
    <h1 class="prose">Axioms</h1>
    <p class="dim">What ${esc(m.title || 'this library')} assumes without proof. Lean's logic has three standard
      axioms and everything below them is ordinary mathematics; anything else is worth a look.</p>
    <p>${beyond.length === 0
      ? '<span class="verdict ok">nothing rests on an axiom beyond the standard three</span>'
      : `<span class="verdict ${beyond.some(r => r.name === 'sorryAx') ? 'bad' : 'warn'}">${
          m.beyondStandard === undefined ? `${beyond.length} axioms beyond the standard three are in use`
          : `${fmt(m.beyondStandard)} of ${fmt(m.declarations)} declarations rest on something beyond the standard three`
        }</span>`}</p>
    ${beyond.length && m.beyondStandard !== undefined ? `<p class="dim">Across ${beyond.length} such axioms. Most of
      what appears here is a compiler or build-tool internal reached through <code>unsafe</code> code rather than a
      mathematical assumption; <code>sorryAx</code> is the one that means an unfinished proof.</p>` : ''}
    <h2>The standard three</h2>
    <ul class="list">${rows.filter(r => r.standard).map(r =>
      `<li><a class="nm" href="${declHref(r.name)}">${esc(r.name)}</a><span class="mod">part of Lean's logic</span><span class="n">${fmt(r.n)}</span></li>`).join('')}</ul>
    ${beyond.length ? `<h2 class="prose">Beyond them</h2>${beyond.map(section).join('')}` : ''}
    ${unused ? `<p class="dim">${unused} further axiom${unused === 1 ? ' is' : 's are'} declared in this bundle
      and nothing in it rests on ${unused === 1 ? 'it' : 'them'}.</p>` : ''}`;
}

async function pageHoles() {
  await loadNames();
  const holes = S.manifest.holes || null;
  if (holes === null) {
    $('#main').innerHTML = `<h1 class="prose">Unfinished proofs</h1>
      <p class="dim">This bundle was generated before the hole list existed. Regenerate it to see this page.</p>`;
    return;
  }
  if (holes.length === 0) {
    $('#main').innerHTML = `<h1 class="prose">Unfinished proofs</h1>
      <p><span class="verdict ok">nothing here rests on sorry</span></p>
      <p class="dim">Every declaration in ${esc(S.manifest.title || 'this library')} has a complete proof. This page is
      where an in-progress formalization shows what is left.</p>`;
    return;
  }
  const byModule = new Map();
  for (const id of holes) {
    const m = S.modules[moduleOfId(id)].n;
    if (!byModule.has(m)) byModule.set(m, []);
    byModule.get(m).push(id);
  }
  const mods = [...byModule.entries()].sort((a, b) => b[1].length - a[1].length);
  $('#main').innerHTML = `
    <h1 class="prose">Unfinished proofs</h1>
    <p><span class="verdict bad">${fmt(holes.length)} declarations rest on sorry</span></p>
    <p class="dim">Each is conditional: anything below it in the library is conditional too. The number on the right
    is how many declarations lean on that one.</p>
    ${mods.map(([m, ids]) => `<h2>${esc(m)} <small>${ids.length}</small></h2>
      <ul class="list">${ids.sort((a, b) => S.used[b] - S.used[a]).map(nameLink).join('')}</ul>`).join('')}`;
}

/**
 * The library as areas rather than names: a treemap of the module tree, each box sized by how many declarations
 * are under it, clicking to descend. The overview MathlibExplorer offered, kept current and leading somewhere.
 */
async function pageMap(prefix = '') {
  const root = { children: new Map(), count: 0, module: null, mods: 0, modIds: [] };
  for (let mx = 0; mx < S.modules.length; mx++) {
    const mod = S.modules[mx];
    let at = root;
    for (const part of mod.n.split('.')) {
      if (!at.children.has(part)) at.children.set(part, { children: new Map(), count: 0, module: null, mods: 0, name: part, modIds: [] });
      at = at.children.get(part);
      at.count += mod.c;
      at.mods++;
    }
    at.module = mod.n;
    root.count += mod.c;
    root.mods++;
    // every node on the path owns this module, which is what a metric is summed over
    let walk = root;
    walk.modIds.push(mx);
    for (const part of mod.n.split('.')) { walk = walk.children.get(part); walk.modIds.push(mx); }
  }
  let node = root, path = [];
  for (const part of prefix.split('.').filter(Boolean)) {
    if (!node.children.has(part)) break;
    node = node.children.get(part);
    path.push(part);
  }
  // A leaf is a file, not an area. Drilling into one used to draw an empty treemap with "0 parts", which is a
  // dead end at the bottom of every path; a file's contents are the module page's job.
  if (node !== root && node.children.size === 0 && node.module) {
    location.replace('#' + modHref(node.module).slice(1));
    return;
  }
  const kids = [...node.children.values()].sort((a, b) => b.count - a.count);
  const W = 1000, H = 560;
  const MIN = 9; // a box thinner than this cannot be hit with a mouse, let alone read

  // Lay everything out once to find out how much of it is too small to draw, then redraw with the remainder
  // pooled into one box. Mathlib.Analysis has 44 parts and every one is legible; a namespace with 300 children
  // is otherwise a row of slivers nobody can click, and the smallest of them are a pixel wide.
  // The rect is drawn two pixels inside its box, so the size to judge is the drawn one. Measuring the layout
  // instead left one sliver on every crowded view: nine wide in the layout, seven on the screen.
  const tooSmall = (b) => (b.w - 2) < MIN || (b.h - 2) < MIN;
  const layout = (tailSet) => {
    const kept = kids.filter(k => !tailSet.has(k));
    const items = kept.map(k => ({ v: k.count, k }));
    if (tailSet.size) {
      let pooled = 0;
      for (const k of tailSet) pooled += k.count;
      items.push({ v: pooled, k: { name: '', count: pooled, children: new Map(), mods: 0, pool: tailSet.size } });
    }
    return squarify(items, 0, 0, W, H);
  };
  // A part with no declarations has no area, and squarify drops anything with none, so it appeared neither on
  // the map nor in the list under it: Mathlib.Tactic.ToAdditive is a real module that simply declares nothing
  // public, and the map behaved as though it did not exist. It goes straight into the tail, which is a list.
  const tailSet = new Set(kids.filter(k => k.count === 0));
  let boxes = layout(tailSet);
  // Pooling makes the survivors bigger, which can make more of them fit, so this settles rather than assuming
  // one pass. The pooled box is checked too: a tail nobody can click is no better than the slivers it replaced,
  // and the way to grow it is to put the next smallest part into it.
  for (let pass = 0; pass < 40; pass++) {
    const small = boxes.filter(tooSmall);
    if (!small.length) break;
    const others = small.filter(b => !b.k.pool).map(b => b.k);
    if (others.length) {
      for (const k of others) tailSet.add(k);
    } else {
      const kept = kids.filter(k => !tailSet.has(k));
      if (kept.length <= 1) break;   // nothing left to give it
      tailSet.add(kept[kept.length - 1]);
    }
    boxes = layout(tailSet);
  }
  const tail = kids.filter(k => tailSet.has(k));
  const hue = (s) => { let h = 0; for (const c of s) h = (h * 31 + c.charCodeAt(0)) % 360; return h; };
  const pct = (c) => node.count ? (100 * c / node.count) : 0;
  // Colour by something you are looking for rather than by name. import-graph has an open request to show the
  // files holding sorries in a different colour; the same machinery answers "where are the unfinished proofs",
  // "where is the deprecated surface" and "what is unsafe", which are the three a maintainer actually asks.
  // Colour by something you are looking for rather than by name. import-graph has an open request to show the
  // files holding sorries in a different colour; the same machinery answers "where is the dead weight", and
  // both are questions about a whole library that no single page can answer.
  const holes = new Set(S.manifest.holes || []);
  const METRICS = {
    name: { label: 'by area' },
    holes: { label: 'unfinished proofs', hue: 0, hit: (i) => holes.has(i) },
    unused: { label: 'nothing depends on it', hue: 40, hit: (i) => S.used[i] === 0 && keep(i) },
  };
  const metric = METRICS[mapMetric] ? mapMetric : 'name';
  const density = (k) => {
    if (metric === 'name' || !k.modIds || !k.modIds.length) return 0;
    const hit = METRICS[metric].hit;
    let n = 0, total = 0;
    for (const mi of k.modIds) {
      const m = S.modules[mi];
      total += m.c;
      for (let i = m.s; i < m.s + m.c; i++) if (hit(i)) n++;
    }
    return total ? n / total : 0;
  };
  const box = (b) => {
    const k = b.k;
    if (k.pool) {
      return `<a href="#smaller"><title>${k.pool} smaller parts, ${fmt(k.count)} declarations between them</title>
        <rect class="pool" x="${b.x + 1}" y="${b.y + 1}" width="${Math.max(0, b.w - 2)}" height="${Math.max(0, b.h - 2)}"></rect>
        ${b.w > 70 && b.h > 24 ? `<text x="${b.x + 8}" y="${b.y + 19}">${k.pool} smaller</text>
          <text class="n" x="${b.x + 8}" y="${b.y + 34}">${fmt(k.count)}</text>` : ''}</a>`;
    }
    const full = [...path, k.name].join('.');
    const leaf = k.children.size === 0 && k.module;
    const href = leaf ? modHref(k.module) : `#/map/${encodeURIComponent(full)}`;
    const detail = [
      `${fmt(k.count)} declaration${k.count === 1 ? '' : 's'}`,
      `${pct(k.count).toFixed(pct(k.count) < 1 ? 2 : 1)}% of ${esc(path.length ? path.join('.') : (S.manifest.title || 'the library'))}`,
      leaf ? 'a module: opens the file' : `${k.children.size} part${k.children.size === 1 ? '' : 's'}, ${fmt(k.mods)} module${k.mods === 1 ? '' : 's'}`,
    ].concat(metric === 'name' ? [] : [`${(100 * density(k)).toFixed(density(k) < 0.01 ? 2 : 1)}% ${METRICS[metric].label}`]).join(' · ');
    return `<a href="${href}" data-tip="${esc(full)}|${detail}" aria-label="${esc(full)}: ${esc(detail)}">
      <rect class="${leaf ? 'leaf' : ''}" x="${b.x + 1}" y="${b.y + 1}" width="${Math.max(0, b.w - 2)}" height="${Math.max(0, b.h - 2)}"
            fill="${metric === 'name'
        ? `hsl(${hue(k.name)} 45% 45% / ${leaf ? '.22' : '.35'})`
        : `hsl(${METRICS[metric].hue} 70% ${Math.round(58 - 34 * Math.min(1, density(k) * 4))}% / ${0.12 + 0.78 * Math.min(1, density(k) * 4)})`}"
      stroke="var(--line)"></rect>
      ${b.w > 60 && b.h > 24 ? `<text x="${b.x + 8}" y="${b.y + 19}">${esc(k.name)}</text>
        <text class="n" x="${b.x + 8}" y="${b.y + 34}">${fmt(k.count)}</text>` : ''}</a>`;
  };
  $('#main').innerHTML = `
    <h1 class="prose">${path.length ? esc(path.join('.')) : (esc(S.manifest.title || 'The library'))}</h1>
    <p class="dim">${fmt(node.count)} declarations in ${kids.length} ${path.length ? 'parts' : 'top-level areas'}.
      Hover a box for what is in it, click to go in. A paler box is a file rather than an area.
      Colour: ${Object.entries(METRICS).map(([k2, v]) =>
        `<a class="metric ${k2 === metric ? 'on' : ''}" href="#/map/${encodeURIComponent(path.join('.'))}"
            data-metric="${k2}">${esc(v.label)}</a>`).join(' ')}
      ${path.map((_, i) => `<a href="#/map/${encodeURIComponent(path.slice(0, i + 1).join('.'))}">${esc(path[i])}</a>`).join(' / ')}
      ${path.length ? ` <a href="#/map/${encodeURIComponent(path.slice(0, -1).join('.'))}">up one</a>` : ''}
      ${node.module ? ` <a href="${modHref(node.module)}">open the module</a>` : ''}</p>
    <div class="mapwrap">
      <svg class="treemap" viewBox="0 0 ${W} ${H}" xmlns="http://www.w3.org/2000/svg">${boxes.map(box).join('')}</svg>
      <div class="maptip" id="maptip" hidden></div>
    </div>
    ${tail.length ? `<h2 id="smaller" class="prose">The smaller parts <small>${tail.length}, too small to draw${
        tail.some(k => k.count === 0) ? `, ${tail.filter(k => k.count === 0).length} declaring nothing at all` : ''}</small></h2>
      <ul class="list">${tail.sort((a, b) => b.count - a.count).map(k => {
        const full = [...path, k.name].join('.');
        const leaf = k.children.size === 0 && k.module;
        return `<li><a class="nm" href="${leaf ? modHref(k.module) : `#/map/${encodeURIComponent(full)}`}">${esc(k.name)}</a>
          <span class="mod">${leaf ? 'module' : `${k.children.size} parts`}</span><span class="n">${fmt(k.count)}</span></li>`;
      }).join('')}</ul>` : ''}`;
  wireMapTip();
  for (const a of $('#main').querySelectorAll('a.metric')) {
    a.onclick = (ev) => { ev.preventDefault(); mapMetric = a.dataset.metric;
      try { localStorage.setItem('mapMetric', mapMetric); } catch (e) { /* private window */ }
      pageMap(prefix); };
  }
}

/**
 * A tooltip for the treemap. The browser's own is a plain string after a delay, which is no use on a picture
 * whose whole point is that you sweep across it; this one follows the pointer and can say several things.
 */
function wireMapTip() {
  const wrap = $('.mapwrap'), tip = $('#maptip');
  if (!wrap || !tip) return;
  wrap.addEventListener('mousemove', (ev) => {
    const a = ev.target.closest('a[data-tip]');
    if (!a) { tip.hidden = true; return; }
    const [name, detail] = a.dataset.tip.split('|');
    tip.innerHTML = `<b>${esc(name)}</b><span>${esc(detail)}</span>`;
    tip.hidden = false;
    const r = wrap.getBoundingClientRect();
    const x = ev.clientX - r.left, y = ev.clientY - r.top;
    // keep it inside the picture rather than letting it push the page sideways
    tip.style.left = Math.min(x + 14, wrap.clientWidth - tip.offsetWidth - 6) + 'px';
    tip.style.top = Math.max(6, y - tip.offsetHeight - 12) + 'px';
  });
  wrap.addEventListener('mouseleave', () => { tip.hidden = true; });
}

/** Squarified treemap: lay values out as boxes whose areas are proportional and whose shapes stay close to square. */
function squarify(items, x, y, w, h) {
  const out = [];
  let rest = items.filter(i => i.v > 0);
  const total = rest.reduce((a, i) => a + i.v, 0);
  if (!total) return out;
  let scale = (w * h) / total;
  while (rest.length) {
    const vertical = w >= h;
    const side = vertical ? h : w;
    let row = [], best = Infinity;
    for (const item of rest) {
      const next = [...row, item];
      const sum = next.reduce((a, i) => a + i.v, 0) * scale;
      const thick = sum / side;
      const worst = Math.max(...next.map(i => Math.max((i.v * scale / thick) / thick, thick / (i.v * scale / thick))));
      if (worst > best && row.length) break;
      row = next;
      best = worst;
    }
    const sum = row.reduce((a, i) => a + i.v, 0) * scale;
    const thick = Math.min(vertical ? w : h, sum / side);
    let at = 0;
    for (const item of row) {
      const len = (item.v * scale) / thick;
      out.push(vertical
        ? { x, y: y + at, w: thick, h: len, k: item.k }
        : { x: x + at, y, w: len, h: thick, k: item.k });
      at += len;
    }
    if (vertical) { x += thick; w -= thick; } else { y += thick; h -= thick; }
    rest = rest.slice(row.length);
    if (w <= 0 || h <= 0) break;
  }
  return out;
}

// ---------------------------------------------------------------- the picture

/**
 * The neighborhood picture: the declaration in the middle, what it uses on the left, what uses it on the right,
 * each column capped and ordered by how depended-upon its members are. With deep, one further ring on each side,
 * dashed, built from the first ring's own shards, which is why it is a button rather than the default.
 */
async function renderGraph(id, name, stmt, proof, usedBy, deep = false) {
  const CAP = 14;
  const left = [...stmt.slice(0, CAP).map(i => ({ id: i, stmt: true })), ...proof.slice(0, Math.max(0, CAP - stmt.length)).map(i => ({ id: i, stmt: false }))];
  const right = usedBy.slice(0, CAP).map(i => ({ id: i }));
  // the second step: for each first-step node, its own few most-used neighbors in the same direction, deduplicated
  const seen = new Set([id, ...left.map(n => n.id), ...right.map(n => n.id)]);
  const left2 = [], right2 = [];
  if (deep) {
    const PER = 3, MAX2 = 24;
    for (const n of left) {
      const d = await decl(n.id);
      const cands = [...d.t, ...d.u].sort((a, b) => S.used[b] - S.used[a]);
      let k = 0;
      for (const c of cands) {
        if (seen.has(c) || k >= PER || left2.length >= MAX2 || !keep(c)) continue;
        seen.add(c); left2.push({ id: c, from: n.id }); k++;
      }
    }
    for (const n of right) {
      const d = await decl(n.id);
      let k = 0;
      for (const c of d.b) {
        if (seen.has(c) || k >= PER || right2.length >= MAX2 || !keep(c)) continue;
        seen.add(c); right2.push({ id: c, from: n.id }); k++;
      }
    }
  }
  const rows = Math.max(left.length, right.length, left2.length, right2.length, 1);
  const W = 1140, rowH = deep ? 26 : 30, H = Math.max(160, rows * rowH + 84);
  const colW = deep ? 250 : 360, midX = W / 2;
  const cy = H / 2;
  // anchor: 'c' centered on x, 'r' right edge at x (the uses column), 'l' left edge at x (the used-by column)
  const box = (x, y, id, cls, anchor) => {
    const label = displayName(S.names[id]);
    const shown = label.length > 44 ? '…' + label.slice(-42) : label;
    const w = Math.min(colW - 10, Math.max(60, shown.length * 7.4 + 22));
    const x0 = anchor === 'c' ? x - w / 2 : anchor === 'r' ? x - w : x;
    const color = `var(--k-${kindOf(id)})`;
    return { x: x0, y: y - 11, w, h: 22, html: `<a class="node ${cls}" href="${declHref(S.names[id])}"><title>${esc(S.names[id])} (${kindOf(id)}, used by ${fmt(S.used[id])})</title><rect x="${x0}" y="${y - 11}" width="${w}" height="${22}"></rect><line class="swatch" x1="${x0 + 1}" y1="${y - 8}" x2="${x0 + 1}" y2="${y + 8}" stroke="${color}"></line><text x="${x0 + 10}" y="${y + 4}">${esc(shown)}</text></a>` };
  };
  const nodes = [], edges = [];
  const center = box(midX, cy, id, 'center', 'c');
  const y0 = (n) => cy - ((n - 1) * rowH) / 2;
  const gap = deep ? 110 : 150;
  const at = new Map();
  const curve = (a, b, cls) => `<path class="edge ${cls}" d="M${a.x + a.w},${a.y + 11} C${a.x + a.w + 40},${a.y + 11} ${b.x - 40},${b.y + 11} ${b.x},${b.y + 11}"></path>`;
  left.forEach((n, i) => {
    const b = box(midX - gap, y0(left.length) + i * rowH, n.id, '', 'r');
    nodes.push(b); at.set(n.id, b);
    edges.push(curve(b, center, n.stmt ? 'stmt' : ''));
  });
  right.forEach((n, i) => {
    const b = box(midX + gap, y0(right.length) + i * rowH, n.id, '', 'l');
    nodes.push(b); at.set(n.id, b);
    edges.push(curve(center, b, ''));
  });
  left2.forEach((n, i) => {
    const b = box(midX - gap - colW - 20, y0(left2.length) + i * rowH, n.id, 'far', 'r');
    nodes.push(b);
    edges.push(curve(b, at.get(n.from), 'far'));
  });
  right2.forEach((n, i) => {
    const b = box(midX + gap + colW + 20, y0(right2.length) + i * rowH, n.id, 'far', 'l');
    nodes.push(b);
    edges.push(curve(at.get(n.from), b, 'far'));
  });
  const note = (x, text) => `<text class="lbl" x="${x}" y="18" text-anchor="middle">${esc(text)}</text>`;
  const legend = ['theorem', 'def', 'inductive', 'constructor', 'axiom'].map((k, i) =>
    `<line class="swatch" x1="${16 + i * 112}" y1="${H - 12}" x2="${16 + i * 112}" y2="${H - 24}" stroke="var(--k-${k})"></line><text class="lbl" x="${24 + i * 112}" y="${H - 14}">${k}</text>`).join('');
  const W2 = deep ? W + 2 * (colW + 20) : W;
  const shift = deep ? colW + 20 : 0;
  $('#graph').innerHTML = `${deep ? '' : '<p style="margin:0 0 6px"><button class="more" id="two-steps">show two steps</button></p>'}<div class="graph-scroll"><svg class="graph" viewBox="${-shift} 0 ${W2} ${H}"${deep ? ` style="width:${W2}px;height:${H}px"` : ''} xmlns="http://www.w3.org/2000/svg">
    ${note(midX - colW + 80, left.length ? `uses (${stmt.length ? 'blue edges: in the statement' : 'in the body'})` : 'uses nothing')}
    ${note(midX + colW - 80, right.length ? `used by (${fmt(S.used[id])} in all, most used first)` : 'used by nothing')}
    ${legend}
    ${edges.join('')}${nodes.map(n => n.html).join('')}${center.html}</svg></div>`;
  if (deep) {
    const sc = $('.graph-scroll');
    sc.scrollLeft = Math.max(0, (W2 - sc.clientWidth) / 2); // start centered on the declaration
  }
}

// ---------------------------------------------------------------- routing and search box

async function route() {
  const h = location.hash || '#/';
  const ml = $('#maplink');
  if (ml) ml.classList.toggle('on', h.startsWith('#/map'));
  // A shard is a fetch away, so say something rather than leaving the last page up or the screen blank.
  const slow = setTimeout(() => { $('#main').innerHTML = '<p class="dim">loading…</p>'; }, 180);
  try {
    if (h.startsWith('#/i/')) await pageDecl(null, parseInt(h.slice(4), 10));
    else if (h.startsWith('#/d/')) await pageDecl(decodeURIComponent(h.slice(4)));
    else if (h.startsWith('#/m/')) await pageModule(decodeURIComponent(h.slice(4)));
    else if (h.startsWith('#/unused')) await pageUnused(decodeURIComponent(h.slice(9)));
    else if (h.startsWith('#/holes')) await pageHoles();
    else if (h.startsWith('#/axioms')) await pageAxioms();
    else if (h.startsWith('#/certificate') || h.startsWith('#/verify')) await pageCertificate();
    else if (h.startsWith('#/ns/')) await pageNamespace(decodeURIComponent(h.slice(5)));
    else if (h.startsWith('#/deprecated')) await pageDeprecated();
    else if (h.startsWith('#/vs/')) await pageVersus(h.slice(5));
    else if (h.startsWith('#/saved')) await pageSaved();
    else if (h.startsWith('#/compare')) await pageCompare(decodeURIComponent(h.slice(9).replace(/^\//, '')));
    else if (h.startsWith('#/map')) await pageMap(decodeURIComponent(h.slice(6)));
    else if (h.startsWith('#/add')) await pageAdd();
    else await pageHome();
    window.scrollTo(0, 0);
  } catch (e) {
    $('#main').innerHTML = `<p>Something went wrong: <code>${esc(e.message)}</code></p>`;
    console.error(e);
  } finally {
    clearTimeout(slow);
  }
}

/**
 * One key to reach anything. A reference tool is used dozens of times an hour by the people who use it at all,
 * and reaching for the mouse to change page is the tax that makes a tool feel slow.
 */
const COMMANDS = [
  { k: 'go home', h: '#/' },
  { k: 'the map', h: '#/map' },
  { k: 'what it assumes: axioms', h: '#/axioms' },
  { k: 'how a proof is certified, and what that does not mean', h: '#/certificate' },
  { k: 'what is deprecated', h: '#/deprecated' },
  { k: 'saved and recently opened', h: '#/saved' },
  { k: 'compare two libraries', h: '#/compare' },
  { k: 'unfinished proofs', h: '#/holes' },
  { k: 'what nothing uses', h: '#/unused' },
  { k: 'add a Lean project', h: '#/add' },
  { k: 'toggle light and dark', do: () => toggleTheme() },
  { k: 'toggle generated helpers', do: () => { const g = $('#gen'); g.checked = !g.checked; g.dispatchEvent(new Event('change')); } },
];

function wirePalette() {
  const wrap = document.createElement('div');
  wrap.id = 'palette';
  wrap.hidden = true;
  wrap.innerHTML = `<div class="pal-card"><input id="pal-q" placeholder="Go to, or search a declaration" autocomplete="off">
    <div id="pal-list"></div></div>`;
  document.body.appendChild(wrap);
  const q = wrap.querySelector('#pal-q'), list = wrap.querySelector('#pal-list');
  let rows = [], at = 0;
  const draw = () => {
    list.innerHTML = rows.map((r, i) =>
      `<a class="${i === at ? 'active' : ''}" href="${r.h || '#'}">${esc(r.k)}${r.sub ? `<span class="mod">${esc(r.sub)}</span>` : ''}</a>`).join('')
      || '<a class="dim">nothing</a>';
  };
  const fill = async () => {
    const text = q.value.trim().toLowerCase();
    rows = COMMANDS.filter(c => !text || c.k.toLowerCase().includes(text));
    if (text.length >= 2 && S.names) {
      rows = rows.concat(search(q.value.trim()).slice(0, 8).map(i =>
        ({ k: S.names[i], h: '#/i/' + i, sub: S.modules[moduleOfId(i)].n })));
    }
    at = 0;
    draw();
  };
  const open = () => { wrap.hidden = false; q.value = ''; fill(); q.focus(); loadNames(); };
  const close = () => { wrap.hidden = true; };
  document.addEventListener('keydown', (ev) => {
    if ((ev.metaKey || ev.ctrlKey) && ev.key.toLowerCase() === 'k') { ev.preventDefault(); wrap.hidden ? open() : close(); return; }
    if (wrap.hidden) return;
    if (ev.key === 'Escape') { close(); }
    else if (ev.key === 'ArrowDown') { at = Math.min(at + 1, rows.length - 1); draw(); ev.preventDefault(); }
    else if (ev.key === 'ArrowUp') { at = Math.max(at - 1, 0); draw(); ev.preventDefault(); }
    else if (ev.key === 'Enter' && rows[at]) {
      ev.preventDefault();
      const r = rows[at];
      close();
      if (r.do) r.do(); else location.hash = r.h;
    }
  });
  q.addEventListener('input', fill);
  wrap.addEventListener('click', (ev) => { if (ev.target === wrap) close(); else if (ev.target.closest('a')) close(); });
}

/** Light and dark. The page has been dark only, which is a preference imposed rather than offered. */
function toggleTheme() {
  // Flip what the reader is actually looking at, which is the operating system's choice until they override it.
  // Comparing against the attribute alone meant that on a light system the first click wrote "light" over an
  // implicit light and nothing happened: a button that does nothing the first time you press it.
  const current = document.documentElement.dataset.theme
    || (window.matchMedia && window.matchMedia('(prefers-color-scheme: dark)').matches ? 'dark' : 'light');
  const now = current === 'dark' ? 'light' : 'dark';
  document.documentElement.dataset.theme = now;
  try { localStorage.setItem('theme', now); } catch (e) { /* private window */ }
}

function wireSearch() {
  const q = $('#q'), box = $('#results');
  let active = -1, timer = null;
  let mods = [];
  const render = (ids) => {
    if (ids.length === 0 && mods.length === 0) { box.hidden = true; return; }
    box.innerHTML = mods.map(m => `<a href="${modHref(m.n)}"><span class="kind">module</span> <span class="nm">${esc(m.n)}</span><span class="mod">${fmt(m.c)} declarations</span></a>`).join('')
      + ids.map((i, k) => `<a href="#/i/${i}" class="${k === active ? 'active' : ''}">${kindBadge(kindOf(i))} <span class="nm">${esc(S.names[i])}</span><span class="mod">${esc(S.modules[moduleOfId(i)].n)}</span></a>`).join('');
    box.hidden = false;
  };
  let last = [];
  q.addEventListener('input', () => {
    clearTimeout(timer);
    timer = setTimeout(async () => {
      await loadNames();
      active = -1;
      const text = q.value.trim();
      if (text.startsWith('+')) {
        box.innerHTML = '<a class="dim">searching statements…</a>';
        box.hidden = false;
        const r = await searchMentions(text);
        if (r?.missing) {
          box.innerHTML = `<a class="dim">no declaration named ${esc(r.missing.join(', '))}</a>`;
          return;
        }
        mods = [];
        last = (r?.hits || []).filter(inScope).slice(0, 50);  // these are all the hits, not a prefix of them
        render(last);
        if (r && r.hits.length > 50) box.insertAdjacentHTML('beforeend', `<a class="dim">and ${fmt(r.hits.length - 50)} more</a>`);
        return;
      }
      if (/(^|\s)(c|concl|conclusion):/i.test(text)) {
        box.innerHTML = '<a class="dim">reading conclusions…</a>';
        box.hidden = false;
        const r = await searchConclusion(text);
        if (r?.missing) {
          box.innerHTML = `<a class="dim">no declaration named ${esc(r.missing.join(', '))}</a>`;
          return;
        }
        mods = [];
        last = (r?.hits || []).slice(0, 50);
        render(last);
        if (r && !r.hits.length) box.innerHTML = `<a class="dim">nothing concluding ${esc(r.concl)} among ${fmt(r.scanned)} that mention it</a>`;
        box.hidden = false;
        return;
      }
      last = search(text);
      mods = searchModules(text);
      render(last);
    }, 120);
  });
  q.addEventListener('keydown', (ev) => {
    if (ev.key === 'ArrowDown') { active = Math.min(active + 1, last.length - 1); render(last); ev.preventDefault(); }
    else if (ev.key === 'ArrowUp') { active = Math.max(active - 1, 0); render(last); ev.preventDefault(); }
    else if (ev.key === 'Enter' && last.length) { location.hash = declHref(S.names[last[Math.max(active, 0)]]); box.hidden = true; }
    else if (ev.key === 'Escape') { box.hidden = true; }
  });
  q.addEventListener('focus', () => loadNames());
  document.addEventListener('click', (ev) => { if (!ev.target.closest('.search')) box.hidden = true; });
  box.addEventListener('click', () => { box.hidden = true; });
}

/**
 * Keyboard navigation. Slash focuses the search, j and k walk the current list, Enter opens what is focused,
 * u and b step to the first thing this declaration uses or that uses it, g goes home, ? shows the keys.
 */
function wireKeys() {
  let row = -1;
  const rows = () => [...document.querySelectorAll('#main .list li a.nm, #results a')];
  const focusRow = (d) => {
    const all = rows();
    if (!all.length) return false;
    row = Math.max(0, Math.min(all.length - 1, row + d));
    all.forEach((a, i) => a.classList.toggle('kbd', i === row));
    all[row].scrollIntoView({ block: 'center' });
    return true;
  };
  document.addEventListener('keydown', (ev) => {
    const typing = /^(INPUT|TEXTAREA)$/.test(ev.target.tagName);
    if (ev.key === '/' && !typing) { ev.preventDefault(); $('#q').focus(); $('#q').select(); return; }
    if (typing) return;
    if (ev.metaKey || ev.ctrlKey || ev.altKey) return;
    switch (ev.key) {
      case 'j': if (focusRow(1)) ev.preventDefault(); break;
      case 'k': if (focusRow(-1)) ev.preventDefault(); break;
      case 'Enter': { const a = rows()[row]; if (a) { ev.preventDefault(); location.hash = a.getAttribute('href').slice(1); } break; }
      case 'g': location.hash = '#/'; break;
      case 'u': case 'b': {
        const list = document.querySelectorAll('#main .list');
        const which = ev.key === 'u' ? list[list.length - 2] : list[list.length - 1];
        const a = which && which.querySelector('a.nm');
        if (a) { ev.preventDefault(); location.hash = a.getAttribute('href').slice(1); }
        break;
      }
      case '?': showKeys(); break;
      case 'Escape': { const k = $('#keys'); if (k) k.remove(); break; }
    }
  });
  window.addEventListener('hashchange', () => { row = -1; });
}

function showKeys() {
  if ($('#keys')) { $('#keys').remove(); return; }
  const help = document.createElement('div');
  help.id = 'keys';
  help.innerHTML = `<div class="keys-card"><h3>Keys</h3><dl class="gloss">
    <dt>/</dt><dd>search</dd>
    <dt>j, k</dt><dd>move through the list</dd>
    <dt>Enter</dt><dd>open what is highlighted</dd>
    <dt>u</dt><dd>go to the first thing this uses</dd>
    <dt>b</dt><dd>go to the first thing that uses this</dd>
    <dt>g</dt><dd>home</dd>
    <dt>?</dt><dd>these keys</dd>
    <dt>Esc</dt><dd>close</dd></dl></div>`;
  help.addEventListener('click', () => help.remove());
  document.body.appendChild(help);
}

(async function init() {
  try {
    // projects.json is how a site with more than one library says so; a site with one bundle in data/ and no
    // such file keeps working, which is what the generator wrote before and what a hand-made bundle looks like.
    try {
      S.projects = await (await fetch('data/projects.json')).json();
    } catch (e) {
      S.projects = null;
    }
    if (S.projects && S.projects.length) {
      const want = new URLSearchParams(location.search).get('p');
      S.project = S.projects.find(p => p.slug === want) || S.projects[0];
      DATA = `data/${S.project.slug}/`;
      // A link naming a library this site does not carry must say so. Falling back silently would show Mathlib
      // to someone who followed a link promising something else, which reads as a lie rather than a mistake.
      if (want && S.project.slug !== want) {
        S.wrongProject = want;
      }
    }
    [S.manifest, S.modules] = await Promise.all([fetchJson('manifest.json'), fetchJson('modules.json')]);
  } catch (e) {
    $('#main').innerHTML = `<p>No bundle found under <code>${esc(DATA)}</code>. Run the generator first.</p>`;
    console.error(e);
    return;
  }
  renderProjectSwitch();
  const lib = S.manifest.libraries.find(l => l.prefixes.length === 0);
  const c = S.manifest.check;
  $('#foot').textContent = `${lib ? lib.name + ' at ' + (lib.rev || '').slice(0, 10) + ', ' : ''}Lean ${S.manifest.lean}, generated ${S.manifest.generated}.`
    + (c ? ` Re-checked by Tenet ${c.tenet}: ${fmt(c.checked)} declarations, ${fmt(c.failed)} rejected.` : ' Not re-checked.');
  wireSearch();
  wireScope();
  wirePalette();
  // Offline for what has already been looked at. Registered after the page works, never before: a service
  // worker that fails must cost the reader nothing, and on a file:// or an unsupported browser it simply is not
  // there. The scope is this directory, which is what a project page under a user's github.io needs.
  if ('serviceWorker' in navigator && location.protocol.startsWith('http')) {
    navigator.serviceWorker.register('sw.js').then((reg) => {
      // Take the update as soon as it exists rather than on some later visit: a reader holding a worker that
      // cached a broken stylesheet should not have to know what a service worker is to get the fix.
      reg.update().catch(() => {});
      reg.addEventListener('updatefound', () => {
        const w = reg.installing;
        if (w) w.addEventListener('statechange', () => { if (w.state === 'activated') location.reload(); });
      });
    }).catch(() => { /* not fatal, and not worth a message */ });
  }
  wireKeys();
  const sw = $('#gen');
  sw.checked = hideGenerated;
  sw.addEventListener('change', () => {
    hideGenerated = sw.checked;
    try { localStorage.setItem('hideGenerated', hideGenerated ? 'yes' : 'no'); } catch (e) { /* fine */ }
    route();
  });
  window.addEventListener('hashchange', route);
  await route();
  warnWrongProject();
  window.addEventListener('hashchange', warnWrongProject);
})();
