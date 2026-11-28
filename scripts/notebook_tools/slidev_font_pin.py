#!/usr/bin/env python3
"""Épinglage déterministe des polices de rendu Slidev (#24171) — option `--pin-fonts`.

POURQUOI. Les compteurs de `scan_slidev_composition.py` (hors-canvas,
chevauchements, occupation) dérivent des largeurs de glyphes et des hauteurs de
ligne, donc des polices SYSTÈME de la machine qui mesure. Mesuré sans pin sur
`S8-semantic-web` (30 slides, même Chromium 156.0.8078.4) : la pile du thème
`"Segoe UI", Calibri, Arial, sans-serif` résout Segoe UI, Calibri et Arial sur
le siège Windows 11, Arial seule dans un conteneur ubuntu 24.04 ; `line-height:
normal` y mesure 21 px contre 18 px (à 16 px) ; la pile monospace sert Consolas
(373,87 px) contre Liberation Mono (408,07 px) sur le même échantillon ; les deux
rapports portent des empreintes d'environnement différentes. Les quatre
compteurs de constat de CE deck y tombent à zéro des deux côtés — une propriété
du deck (il ne déborde pas), pas une preuve de comparabilité ; le cinquième les
départage : `n_chevauchements_eteints` lit 8 sur le siège Windows, 0 dans le
conteneur (8 et 8 sous pin) — 3 px par boîte de ligne décident une slide dense.
Un compteur n'est opposable qu'entre conditions égales.

QUOI. Le pin remplace, pour la durée du scan, chaque famille système par une
police LIVRÉE (`fonts/`, OFL 1.1 et licence DejaVu) dont les métriques sont
réglées sur la référence Windows, puis relit après la mesure quelles polices ont
servi : toute police système restante est nommée dans `font_pin.escaped`.

COMMENT (mesuré sur Chromium 156.0.8078.4, siège Windows 11) :
  1. MASQUAGE — une face `@font-face` déclarée sous le nom d'une famille
     installée (« Segoe UI », « Consolas »…) gagne sur la police locale. Une
     famille de pile devient composable : Selawik sur sa couverture, DejaVu
     Sans sur le complément (`unicode-range`).
  2. MÉTRIQUES — `ascent/descent/line-gap-override` (+ `size-adjust` rapporté
     au facteur pour le monospace) reproduisent la boîte de ligne de la
     référence à 18 px : Segoe UI 24/19, Cascadia Code 21/17, Georgia 21/17.
  3. GÉNÉRIQUES — `sans-serif`, `monospace`, `system-ui`… ne peuvent être ni
     masqués par `@font-face` ni détournés par CDP `Page.setFontFamilies` vers
     une famille `@font-face` (les deux essayés, les deux inertes). Ils sont
     réparés par style inline, élément par élément, juste avant la mesure.
  4. DÈS LE DOCUMENT — la feuille est ADOPTÉE par le document
     (`adoptedStyleSheets`) par un script d'initialisation Playwright, avant
     tout script du deck : Mermaid mesure son texte à l'insertion, un pin posé
     après le rendu arriverait trop tard.
     Elle n'entre PAS par la réponse HTML. Un document renvoyé par une route
     Playwright (`fetch` + `fulfill`) perd son espace d'adressage : Chromium
     refuse alors ses scripts de module — « blocked by CORS policy: The request
     client is not a secure context and the resource is in more-private address
     space `local` » — dès que l'origine n'est pas un contexte sûr. Mesuré
     (Chromium 156.0.8078.4) : deux scans en échec (rc 2, `nav.total absent`)
     sur un deck servi sur 172.24.240.1, le même deck servi sur `localhost`
     passant. Le document du deck est donc servi par son serveur, tel quel ;
     seules les URL des polices du pin passent par une route.
  5. AVANCÉES — le navigateur se lance avec `LAUNCH_ARGS`. Sous Linux,
     Chromium hinte les avancées de glyphes : des largeurs entières, qui
     s'écartent de Windows de −2,1 % à +8,7 % selon la taille pour une MÊME
     police livrée (mesuré : +8,74 % sur une phrase de 33 signes à 11,52 px,
     +6,68 % sur 15 signes monospace à 16 px). `--font-render-hinting=none`
     les rend linéaires : écart résiduel ≤ 0,06 % (quantification au 1/64 px).
     Sur Windows l'argument est sans effet (mesuré, vingt chaînes identiques
     à l'unité près). Les boîtes de ligne, elles, sont égales avec ou sans lui.

BORNE. Le pin égalise les machines, il ne restitue pas Windows :
  - Approche : Segoe UI crène 8 292 paires (table `kern`), Selawik aucune. Un
    texte à crénage est plus large sous le pin (mesuré : +17,28 px à 18 px sur
    une chaîne de stress).
  - Glyphes hors couverture des polices livrées (emoji, usage privé U+E000…)
    : repli système, listé dans `escaped` — `verified` vaut alors `false`.
  - Italique : aucune face italique livrée, le navigateur l'incline.
  - Les génériques hors de `#slide-content` ne sont pas réparés (le conteneur
    de mesure de Mermaid est rattaché au corps).

Code retour : le pin ne peut être appliqué (polices absentes ou altérées,
feuille non injectée, faces non chargées) => exit 3. Un glyphe échappé ne
touche pas au code retour du deck, seulement à `font_pin.verified`.

Rebuild des plages Unicode (nécessite fonttools) :
    python scripts/notebook_tools/slidev_font_pin.py --rebuild-ranges
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path

FONT_DIR = Path(__file__).resolve().parent / "fonts"
RANGES_FILE = FONT_DIR / "unicode_ranges.json"
URL_PREFIX = "/__slidev_font_pin/"
PIN_VERSION = "1"
INJECTION = "feuille adoptée par le document avant tout script du deck (script d'initialisation)"

# Arguments de lancement du navigateur : ils font partie du pin, car ils changent
# les largeurs mesurées. Sous Linux, Chromium hinte les avancées de glyphes
# (largeurs entières) et s'écarte de Windows de −2,1 % à +8,7 % selon la taille,
# pour une MÊME police livrée ; `none` rend les avancées linéaires (écart
# résiduel ≤ 0,06 %, quantification au 1/64 px). Sur Windows, no-op mesuré.
# Ils entrent dans `signature()` : changer cette liste change l'empreinte.
LAUNCH_ARGS = ("--font-render-hinting=none",)

# Plages livrées = cmap EXACT de chaque police principale (clé -> clé du LOCK).
RANGE_FONTS = {"selawik": "selawik", "gelasio": "serif", "dejavu_serif": "serif_fallback"}
RANGE_KEYS = tuple(sorted(RANGE_FONTS))

# Octets livrés, verrouillés : clé -> (fichier, taille, sha256). Lu sur le
# disque à chaque installation ; un écart = pin inapplicable (exit 3).
LOCK = {
    "selawik": ("selawik-regular.ttf", 44224,
                "e9d98518d8ac2817782a9a382430463a2e0793ea68350b695bb727d9a830ee1c"),
    "selawik_bold": ("selawik-bold.ttf", 44068,
                     "f0db5e174a90e0956ad7d2844bdca1d5e6da92ec65b2c04e57ba9b180668c904"),
    "sans_fallback": ("dejavu-sans.ttf", 757076,
                      "7da195a74c55bef988d0d48f9508bd5d849425c1770dba5d7bfc6ce9ed848954"),
    "mono": ("dejavu-sans-mono.ttf", 340712,
             "b4a6c3e4faab8773f4ff761d56451646409f29abedd68f05d38c2df667d3c582"),
    "serif": ("gelasio-variable.ttf", 168556,
              "4daecea457258c9ebeb8bc99ed3fd24353618bfad3ea4b93fa0b5d0468fc04e4"),
    "serif_fallback": ("dejavu-serif.ttf", 380132,
                       "42d1edeb7952f31b1f96d767ed7030b08a39e0c372b0071641518864e2bffb51"),
}

# Provenance : version LUE dans la table `name` du fichier livré.
UPSTREAM = {
    "selawik": "Selawik 1.01 — github.com/microsoft/Selawik (OFL 1.1)",
    "selawik_bold": "Selawik 1.01 bold — github.com/microsoft/Selawik (OFL 1.1)",
    "sans_fallback": "DejaVu Sans 2.37 — dejavu-fonts (licence DejaVu)",
    "mono": "DejaVu Sans Mono 2.37 — dejavu-fonts (licence DejaVu)",
    "serif": "Gelasio 1.008 (variable, wght 400-700) — SorkinType/Gelasio via google/fonts (OFL 1.1)",
    "serif_fallback": "DejaVu Serif 2.37 — dejavu-fonts (licence DejaVu)",
}

# Métriques de référence, en % d'em, du siège Windows (upm 2048 partout).
#   sans  Segoe UI      hhea 2210/-514/0            -> 107.91 / 25.10 / 0
#   mono  Cascadia Code avance 1200/2048 = 0.58594 em, boîte 21 / base 17 à 18 px ;
#         DejaVu Sans Mono avance 1233/2048 -> size-adjust 1200/1233 = 97.324 %,
#         overrides rapportés au facteur : 17/(18×0.97324) = 97.042 %, 4/(18×0.97324) = 22.833 %
#   serif Georgia       hhea 1878/-449/0            -> 91.70 / 21.92 / 0
METRICS = {
    "sans": {"ascent": 107.91, "descent": 25.10, "lineGap": 0.0, "sizeAdjust": None},
    "mono": {"ascent": 97.0417, "descent": 22.8333, "lineGap": 0.0, "sizeAdjust": 97.3236},
    "serif": {"ascent": 91.70, "descent": 21.92, "lineGap": 0.0, "sizeAdjust": None},
}
REFERENCE = {
    "sans": "Segoe UI (hhea 2210/-514/0 sur upm 2048 : boîte 24 / base 19 à 18 px)",
    "mono": "Cascadia Code (avance 1200/2048 em : boîte 21 / base 17 à 18 px)",
    "serif": "Georgia (hhea 1878/-449/0 : boîte 21 / base 17 à 18 px)",
}
NORMALISATION = {
    "sans": "toute famille sans est ramenée à la référence Segoe UI (un texte déclaré "
            "en Arial ou en Verdana mesure comme Segoe UI)",
    "mono": "toute famille monospace est ramenée à la référence Cascadia Code",
    "serif": "toute famille serif est ramenée à la référence Georgia",
}

# Familles masquées. Tout nom écrit ici est servi par le pin, quelle que soit
# la police locale ; une web font du deck portant le même nom est masquée aussi.
SANS_NAMES = (
    "Segoe UI", "Calibri", "Arial", "Helvetica", "Helvetica Neue", "Roboto", "Noto Sans",
    "Trebuchet MS", "Verdana", "Tahoma", "Liberation Sans", "DejaVu Sans",
    "ui-sans-serif", "-apple-system", "BlinkMacSystemFont",
)
MONO_NAMES = (
    "Cascadia Code", "Cascadia Mono", "Consolas", "Menlo", "Monaco", "SFMono-Regular",
    "Liberation Mono", "Courier New", "Courier", "DejaVu Sans Mono", "Noto Sans Mono",
    "Roboto Mono", "Source Code Pro", "Fira Code", "Fira Mono", "JetBrains Mono",
    "Ubuntu Mono", "ui-monospace",
)
SERIF_NAMES = (
    "Georgia", "Times New Roman", "Times", "Cambria", "Liberation Serif", "DejaVu Serif",
    "Noto Serif", "ui-serif",
)

# Mots-clés génériques -> nom masqué de remplacement. Un générique en TÊTE de
# pile (première famille résolue) est le seul cas réparé : en queue, il ne sert
# que les glyphes hors couverture de tout le reste, déjà signalés par `escaped`.
GENERIC_REPAIR = {
    "sans-serif": '"Segoe UI"', "system-ui": '"Segoe UI"', "ui-sans-serif": '"Segoe UI"',
    "-apple-system": '"Segoe UI"', "blinkmacsystemfont": '"Segoe UI"',
    "monospace": '"Consolas"', "ui-monospace": '"Consolas"',
    "serif": '"Georgia"', "ui-serif": '"Georgia"',
}

# Familles telles que CDP les nomme pour les fichiers livrés.
PINNED_FAMILIES = frozenset(
    {"Selawik", "DejaVu Sans", "DejaVu Sans Mono", "Gelasio", "DejaVu Serif"})

BORNE = (
    "Le pin égalise les machines, il ne restitue pas Windows : pas de crénage "
    "(Segoe UI en a, Selawik non), glyphes hors couverture des polices livrées "
    "en repli système (voir escaped), italique incliné par le navigateur. "
    "verified=false nomme ce qui a échappé ; cela ne change pas le code retour du deck."
)


class FontPinError(RuntimeError):
    """Le pin ne peut pas être appliqué (exit 3 du scanner)."""


def font_manifest() -> dict:
    """Vérifie les octets livrés contre le verrou et retourne la provenance."""
    manifest = {}
    for key, (name, size, digest) in LOCK.items():
        path = FONT_DIR / name
        try:
            blob = path.read_bytes()
        except OSError as exc:
            raise FontPinError(f"police livrée illisible : {name} ({exc})") from exc
        actual = hashlib.sha256(blob).hexdigest()
        if len(blob) != size or actual != digest:
            raise FontPinError(
                f"police livrée altérée : {name} ({len(blob)} octets, sha256 {actual[:12]}…) "
                f"— attendu {size} octets, {digest[:12]}…")
        manifest[key] = {"file": name, "bytes": size, "sha256": digest, "upstream": UPSTREAM[key]}
    return manifest


def load_ranges() -> dict:
    """Plages Unicode des faces composites (générées par --rebuild-ranges)."""
    try:
        ranges = json.loads(RANGES_FILE.read_text(encoding="utf-8"))
    except (OSError, ValueError) as exc:
        raise FontPinError(f"plages Unicode illisibles : {RANGES_FILE.name} ({exc})") from exc
    missing = [k for k in RANGE_KEYS if not ranges.get(k)]
    if missing:
        raise FontPinError(f"plages Unicode incomplètes : {', '.join(missing)}")
    return ranges


def _fmt(value: float) -> str:
    return ("%.3f" % value).rstrip("0").rstrip(".")


def _face(family: str, key: str, weight: int, metrics: dict, unicode_range: str | None) -> str:
    parts = [
        'font-family: "%s"' % family.replace('"', ""),
        "src: url(%s%s) format(truetype)" % (URL_PREFIX, LOCK[key][0]),
        "font-style: normal",
        "font-weight: %d" % weight,
        "font-display: block",
    ]
    if unicode_range:
        parts.append("unicode-range: %s" % unicode_range)
    if metrics["sizeAdjust"]:
        parts.append("size-adjust: %s%%" % _fmt(metrics["sizeAdjust"]))
    parts += [
        "ascent-override: %s%%" % _fmt(metrics["ascent"]),
        "descent-override: %s%%" % _fmt(metrics["descent"]),
        "line-gap-override: %s%%" % _fmt(metrics["lineGap"]),
    ]
    return "@font-face { %s; }\n" % "; ".join(parts)


def build_css(ranges: dict | None = None) -> str:
    """Feuille du pin : une famille composite par nom de pile, poids par poids.

    Dans une famille, un caractère est servi par la DERNIÈRE face déclarée dont
    `unicode-range` le contient : la face de repli est donc déclarée SANS plage
    AVANT la face principale, qui porte le cmap exact de sa police. Le repli ne
    garde que le complément — pas de plage de complément à calculer ni à livrer.

    Chaque face porte UN poids : une face à plage de poids (`font-weight: 400
    700`) sur une police variable empêche les autres faces de la famille de
    servir le moindre glyphe (mesuré : 7 glyphes échappés au système).
    """
    ranges = ranges or load_ranges()
    out = []
    for name in SANS_NAMES:
        out.append(_face(name, "sans_fallback", 400, METRICS["sans"], None))
        out.append(_face(name, "selawik", 400, METRICS["sans"], ranges["selawik"]))
        out.append(_face(name, "sans_fallback", 700, METRICS["sans"], None))
        out.append(_face(name, "selawik_bold", 700, METRICS["sans"], ranges["selawik"]))
    for name in MONO_NAMES:
        # Pas de face de repli pour le monospace : DejaVu Sans Mono couvre déjà
        # les symboles de code (flèches, encadrements) ; une face sans plage
        # déclarée coûterait le cmap entier (256 plages × 18 noms) pour les
        # quelques emoji qu'elle ne couvre pas de toute façon.
        out.append(_face(name, "mono", 400, METRICS["mono"], None))
        out.append(_face(name, "mono", 700, METRICS["mono"], None))
    for name in SERIF_NAMES:
        out.append(_face(name, "sans_fallback", 400, METRICS["serif"], None))
        out.append(_face(name, "serif_fallback", 400, METRICS["serif"], ranges["dejavu_serif"]))
        out.append(_face(name, "serif", 400, METRICS["serif"], ranges["gelasio"]))
        out.append(_face(name, "sans_fallback", 700, METRICS["serif"], None))
        out.append(_face(name, "serif_fallback", 700, METRICS["serif"], ranges["dejavu_serif"]))
        out.append(_face(name, "serif", 700, METRICS["serif"], ranges["gelasio"]))
    return "".join(out)


def shadow_names() -> list:
    return sorted(set(SANS_NAMES) | set(MONO_NAMES) | set(SERIF_NAMES))


def signature(css: str, manifest: dict, launch_args=LAUNCH_ARGS) -> str:
    """Empreinte du pin : version, feuille, octets des polices, args de lancement."""
    payload = {"version": PIN_VERSION, "css": css,
               "launch_args": list(launch_args),
               "fonts": {k: v["sha256"] for k, v in sorted(manifest.items())}}
    return hashlib.sha256(json.dumps(payload, sort_keys=True).encode("utf-8")).hexdigest()


def classify_fonts(rendered: dict) -> dict:
    """Classe un relevé `rendered_fonts` : épinglé, web font du deck, échappé.

    CDP sert `custom=True` à toute face @font-face : la nôtre comme celle d'un
    deck (KaTeX…). Seul un glyphe de police SYSTÈME est une fuite.
    """
    counts = {"pinned": 0, "deck": 0}
    escaped = []
    for font in rendered.get("fonts", []):
        if font.get("custom"):
            counts["pinned" if font["family"] in PINNED_FAMILIES else "deck"] += font["glyphs"]
        else:
            escaped.append({"family": font["family"], "glyphs": font["glyphs"]})
    return {**counts, "escaped": escaped}


# Feuille adoptée par le document à sa création. Une règle interdite dans une
# feuille construite (@import, @namespace) fait lever `replaceSync` : l'erreur
# reste lisible par `ensure_loaded`, et le scan sort en 3 au lieu de mesurer
# sans pin.
_JS_INIT = """
(() => {
  if (window.__slidevFontPin) return;
  try {
    const sheet = new CSSStyleSheet();
    sheet.replaceSync(%s);
    document.adoptedStyleSheets = [...document.adoptedStyleSheets, sheet];
    window.__slidevFontPin = { sheet: sheet };
  } catch (e) {
    window.__slidevFontPin = { error: String(e) };
  }
})();
"""

_JS_FACES = """
async (shadowed) => {
  // `shadowed` arrive EN MINUSCULES (`_shadowed_lower`) : `document.fonts`
  // rend le nom tel qu'écrit dans la feuille, la comparaison est sans casse.
  const mine = [...document.fonts].filter(
    f => shadowed.includes(f.family.replace(/^["']|["']$/g, '').toLowerCase()));
  const unloaded = [];
  for (const f of mine) {
    try { await f.load(); } catch (e) {}
    if (f.status !== 'loaded') unloaded.push(f.family + ' ' + f.weight);
  }
  // Injectée = la feuille du pin est TOUJOURS adoptée : un script du deck qui
  // réécrirait `adoptedStyleSheets` la ferait disparaître.
  const pin = window.__slidevFontPin;
  return {
    declared: mine.length,
    unloaded,
    injected: !!(pin && pin.sheet && document.adoptedStyleSheets.includes(pin.sheet)),
    error: pin && pin.error ? pin.error : null,
  };
}
"""

_JS_REPAIR = """
() => {
  const SHADOWED = %s;
  const REPAIR = %s;
  const root = document.querySelector('#slide-content');
  if (!root) return {error: 'contenu de slide absent'};
  // Slidev garde le deck entier ici : un `.slidev-page` par slide, une seule
  // affichée. La slide d'un élément réparé est l'index de SA page.
  const pages = Array.from(document.querySelectorAll('#slide-content .slidev-page'));
  const pageOf = el => {
    const page = el.closest('.slidev-page');
    const i = page ? pages.indexOf(page) : -1;
    return i === -1 ? 'hors-page' : String(i + 1);
  };
  const shadowed = new Set(SHADOWED);
  const deck = new Set();
  document.fonts.forEach(f => {
    const n = f.family.replace(/^["']|["']$/g, '').toLowerCase();
    if (!shadowed.has(n)) deck.add(n);
  });
  // Une famille non disponible est sautée par le moteur : sonde canvas.
  const ctx = document.createElement('canvas').getContext('2d');
  const ABSENT = '__slidev_font_pin_absent__';
  const RULER = 'MMMMMWWWWWiiilli|@~';
  const available = (() => {
    const cache = new Map();
    return (name) => {
      const k = name.toLowerCase();
      if (!cache.has(k)) {
        ctx.font = '32px "' + ABSENT + '"';
        const base = ctx.measureText(RULER).width;
        ctx.font = '32px "' + name + '", "' + ABSENT + '"';
        cache.set(k, Math.abs(ctx.measureText(RULER).width - base) > 0.01);
      }
      return cache.get(k);
    };
  })();
  let scanned = 0;
  const repaired = [];
  const byPage = {};
  for (const el of [root].concat(Array.from(root.querySelectorAll('*')))) {
    if (el.dataset.slidevFontPin) continue;
    scanned++;
    const stack = getComputedStyle(el).fontFamily;
    const fams = [];
    let cur = '', quote = null;
    for (const ch of stack) {
      if (quote) { if (ch === quote) quote = null; else cur += ch; }
      else if (ch === '"' || ch === "'") quote = ch;
      else if (ch === ',') { fams.push(cur.trim()); cur = ''; }
      else cur += ch;
    }
    if (cur.trim()) fams.push(cur.trim());
    // La première famille RÉSOLUE décide : un générique en tête est réparé.
    const hit = fams.find(f => {
      const k = f.toLowerCase();
      return REPAIR[k] !== undefined || shadowed.has(k) || deck.has(k) || available(f);
    });
    if (!hit || REPAIR[hit.toLowerCase()] === undefined) continue;
    el.style.setProperty('font-family', fams.map(
      f => REPAIR[f.toLowerCase()] !== undefined ? REPAIR[f.toLowerCase()] : '"' + f + '"'
    ).join(', '), 'important');
    el.dataset.slidevFontPin = hit;
    repaired.push(stack);
    const page = pageOf(el);
    byPage[page] = (byPage[page] || 0) + 1;
  }
  return {scanned, repaired: repaired.length, by_page: byPage, samples: repaired.slice(0, 5)};
}
"""


class FontPin:
    """Le pin de polices : feuille à adopter, polices servies, état du scan.

    Construit (et vérifié : `FontPinError`) SANS navigateur — `attach(page)`
    le branche sur une page, avant tout `page.goto`."""

    def __init__(self):
        self.manifest = font_manifest()
        self.ranges = load_ranges()
        self.css = build_css(self.ranges)
        self._signature = signature(self.css, self.manifest)
        self.shadowed = shadow_names()
        # `document.fonts` rend le nom tel qu'écrit dans la feuille (`Segoe
        # UI`) : toute comparaison de famille côté navigateur se fait en
        # minuscules, des deux côtés. Une comparaison sensible à la casse ne
        # contrôlait que les noms déjà écrits en minuscules (mesuré : 16 faces
        # déclarées sur 144).
        self._shadowed_lower = [name.lower() for name in self.shadowed]
        self._file_names = frozenset(v[0] for v in LOCK.values())
        self.repaired_slides: dict = {}
        self.font_requests = 0

    @property
    def signature(self) -> str:
        return self._signature

    @property
    def n_faces(self) -> int:
        return len(re.findall(r"@font-face \{", self.css))

    @property
    def launch_args(self) -> list:
        """À passer à `chromium.launch(args=…)` : les conditions du pin en font partie."""
        return list(LAUNCH_ARGS)

    def handle(self, route) -> None:
        """Route Playwright : sert les octets verrouillés d'une police du pin."""
        url = route.request.url
        pos = url.find(URL_PREFIX)
        if pos == -1:  # hors du préfixe : le pin ne décide de rien
            route.continue_()
            return
        name = url[pos + len(URL_PREFIX):].split("?")[0].split("#")[0]
        if name not in self._file_names:
            route.fulfill(status=404, body="")
            return
        self.font_requests += 1
        route.fulfill(status=200, content_type="font/ttf", body=(FONT_DIR / name).read_bytes(),
                      headers={"Cache-Control": "max-age=31536000"})

    def attach(self, page) -> None:
        """Branche le pin sur une page, AVANT tout `page.goto`.

        La feuille entre par un script d'initialisation : elle est adoptée par
        le document à sa création, donc avant tout script du deck. Seules les
        URL des polices du pin passent par une route — le document du deck est
        servi par son serveur, tel quel (docstring, point 4)."""
        page.add_init_script(script=_JS_INIT % json.dumps(self.css))
        page.route("**" + URL_PREFIX + "**", self.handle)

    def ensure_loaded(self, page) -> dict:
        """Force le chargement de TOUTES les faces du pin ; nomme celles qui restent."""
        return page.evaluate(_JS_FACES, self._shadowed_lower)

    def apply(self, page) -> dict:
        """Répare les piles à générique en tête dans TOUT `#slide-content`.

        Slidev y garde le deck entier (`#slideshow` → un `.slidev-page` par
        slide, une seule affichée) : le premier passage répare toutes les pages
        d'un coup — mesuré sur S8, 1 901 éléments parcourus à la slide 1 comme à
        la 30 — et un élément déjà réparé est marqué (`data-slidev-font-pin`),
        donc sauté. Les passages suivants ne rattrapent que ce que le deck a
        recréé. Chaque réparation est attribuée à SA page (`repaired_by_slide`,
        clé = index du `.slidev-page`, `hors-page` sinon), jamais à la slide
        pendant laquelle le passage a eu lieu.
        """
        result = page.evaluate(_JS_REPAIR % (json.dumps(self._shadowed_lower), json.dumps(GENERIC_REPAIR)))
        for key, count in (result.get("by_page") or {}).items():
            self.repaired_slides[key] = self.repaired_slides.get(key, 0) + count
        return result

    def verify(self, rendered_slides: list) -> dict:
        escaped = []
        pinned = deck = 0
        for entry in rendered_slides:
            if "error" in entry:
                continue
            verdict = classify_fonts(entry)
            pinned += verdict["pinned"]
            deck += verdict["deck"]
            escaped += [{"slide": entry.get("slide"), **e} for e in verdict["escaped"]]
        return {"glyphs_pinned": pinned, "glyphs_deck": deck, "escaped": escaped,
                "verified": not escaped}

    def report(self, loaded: dict, rendered_slides: list) -> dict:
        return {
            "enabled": True,
            "applied": bool(loaded) and not loaded.get("unloaded") and loaded.get("injected", False),
            "version": PIN_VERSION,
            "signature": self._signature,
            "reference": REFERENCE,
            "normalisation": NORMALISATION,
            "n_faces": self.n_faces,
            "n_families": len(self.shadowed),
            "fonts": {k: {"file": v["file"], "bytes": v["bytes"], "sha256": v["sha256"],
                          "upstream": v["upstream"]} for k, v in sorted(self.manifest.items())},
            "faces": loaded,
            "injection": INJECTION,
            "launch_args": self.launch_args,
            "font_requests": self.font_requests,
            # Clé = index du `.slidev-page` de l'élément (1-based), ou
            # `hors-page` ; tri numérique, `hors-page` en dernier.
            "repaired_by_slide": {
                k: v for k, v in sorted(
                    self.repaired_slides.items(),
                    key=lambda kv: (1, 0) if not kv[0].isdigit() else (0, int(kv[0])))},
            **self.verify(rendered_slides),
            "borne": BORNE,
        }


def install_font_pin(page) -> FontPin:
    """Vérifie les polices (lève `FontPinError`), puis branche le pin sur la page."""
    pin = FontPin()
    pin.attach(page)
    return pin


def cmap_of(font_path) -> set:
    """Codepoints d'un fichier, lus par fonttools (jamais par le scanner)."""
    from fontTools.ttLib import TTFont

    return set(TTFont(str(font_path), lazy=True).getBestCmap())


def unicode_ranges_of(font_path) -> str:
    """`unicode-range` CSS couvrant exactement la cmap d'un fichier (fonttools)."""
    return _compress(cmap_of(font_path))


def _compress(codepoints: set) -> str:
    out = []
    start = prev = None
    for code in sorted(codepoints):
        if start is None:
            start = prev = code
        elif code == prev + 1:
            prev = code
        else:
            out.append((start, prev))
            start = prev = code
    if start is not None:
        out.append((start, prev))
    return ", ".join("U+%X" % a if a == b else "U+%X-%X" % (a, b) for a, b in out)


def parse_ranges(css_ranges: str) -> set:
    """Ensemble des codepoints d'une chaîne `unicode-range`."""
    covered = set()
    for part in css_ranges.split(", "):
        match = re.fullmatch(r"U\+([0-9A-F]+)(?:-([0-9A-F]+))?", part)
        if not match:
            raise FontPinError(f"plage Unicode ill formée : {part!r}")
        a = int(match.group(1), 16)
        b = int(match.group(2), 16) if match.group(2) else a
        covered.update(range(a, b + 1))
    return covered


def rebuild_ranges() -> dict:
    """Réécrit `unicode_ranges.json` depuis les cmap des fichiers livrés."""
    ranges = {key: unicode_ranges_of(FONT_DIR / LOCK[font][0]) for key, font in RANGE_FONTS.items()}
    RANGES_FILE.write_text(json.dumps(ranges, indent=1, sort_keys=True) + "\n",
                           encoding="utf-8", newline="\n")
    return ranges


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--rebuild-ranges", action="store_true", help="régénère fonts/unicode_ranges.json (fonttools)")
    parser.add_argument("--print-css", action="store_true", help="imprime la feuille du pin sur stdout")
    args = parser.parse_args()
    if args.rebuild_ranges:
        ranges = rebuild_ranges()
        print(json.dumps({k: len(v.split(", ")) for k, v in ranges.items()}))
        return 0
    if args.print_css:
        sys.stdout.write(build_css())
        return 0
    parser.print_help()
    return 0


if __name__ == "__main__":
    sys.exit(main())
