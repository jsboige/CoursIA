#!/usr/bin/env python3
"""Garde post-deploiement : verifie que les liens critiques du site publie resolvent.

Issue #21628 (fille de l'EPIC #10921). Les gardes de liens du depot
(`HTML_404`, `ipynb_links`, #18970) verifient le contenu SOURCE -- ils ne
testent pas le site DEPLOYE. Le rendu Quarto transforme les chemins
(`.md` -> `.html`, globs, freeze) : une regression de navigation ou de
rendu n'est visible qu'apres publication.

Ce garde extrait les `href` internes des pages critiques du site publie
(racine, index des notebooks, parcours, page catalogue), resout les liens
relatifs et teste chaque URL unique par HTTP, en conservant toutes ses
pages sources. Depuis #25055, il porte aussi la classe structurelle des
liens `.ipynb` bruts : un href interne `.ipynb` sur une page publiee
signale un carnet absent de la liste de rendu Quarto (le lien repond
alors 404 ou sert le JSON source) -- detecte sans appel HTTP, donc hors
plafond. Il ne teste QUE la resolution des liens :
le rendu lui-meme reste l'affaire de l'audit visuel Playwright de l'EPIC
(reserve aux lanes CoursIA-2).

Baseline mesuree le 2026-10-20 (lane myia-po-2028:CoursIA, #10921
c.6296125400) : 17/17 liens critiques en HTTP 200.
Violation fondee le 2026-11-07 (audit visuel #25055) : la page catalogue
exposait 45 liens `.ipynb` bruts, invisibles au garde parce que la page
n'etait pas couverte ; le merge de #24283 laisse 1 residuel
(SL-11-Capstone-NeuroSymbolic, 200 en JSON brut) -- le controle positif
de la classe structurelle.

Exit codes :
  0 -- tous les liens internes resolvent (2xx/3xx)
  1 -- au moins un lien interne casse (404/410/autre 4xx-5xx)
  2 -- instrument casse (page critique inaccessible ou illisible)
"""

from __future__ import annotations

import argparse
import concurrent.futures
import http.client
import json
import re
import sys
import urllib.error
import urllib.parse
import urllib.request
from dataclasses import dataclass, field

EXIT_OK = 0
EXIT_BROKEN_LINK = 1
EXIT_INSTRUMENT = 2

DEFAULT_BASE_URL = "https://jsboige.github.io/CoursIA"

# Pages critiques : leur contenu porte la navigation de l'apprenant.
# La liste est volontairement courte -- ce garde mesure la navigation
# publiee, pas les 1181 pages du site.
# La page catalogue est incluse depuis #25055 : sa violation des liens
# (44 .ipynb en 404 + 1 en JSON brut) n'avait ete vue par aucun organe
# parce qu'elle n'etait pas couverte.
DEFAULT_PAGES = (
    "/",
    "/MyIA.AI.Notebooks/index.html",
    "/parcours.html",
    "/COURSE_CATALOG.generated.html",
    # Les 16 README de series (#10921, sous-grain garde/series, 2026-11-10) :
    # la mesure qui fonde cette extension y a trouve 54 liens casses sur 674
    # -- tous corrects sur github.com, casses sur Pages (repertoires sans
    # index, fichiers hors render-list). La passe post-rendu
    # (quarto_site_link_targets.py) repare ces deux familles ; ces pages
    # restent couvertes pour tenir la regression (une nouvelle serie qui
    # recommence doit rougir ici, pas attendre la prochaine mesure a la
    # main).
    "/MyIA.AI.Notebooks/CaseStudies/README.html",
    "/MyIA.AI.Notebooks/Complexity/README.html",
    "/MyIA.AI.Notebooks/Compression/README.html",
    "/MyIA.AI.Notebooks/cross-series/README.html",
    "/MyIA.AI.Notebooks/GameTheory/README.html",
    "/MyIA.AI.Notebooks/GenAI/README.html",
    "/MyIA.AI.Notebooks/IIT/README.html",
    "/MyIA.AI.Notebooks/ML/README.html",
    "/MyIA.AI.Notebooks/NLP/README.html",
    "/MyIA.AI.Notebooks/Physique/README.html",
    "/MyIA.AI.Notebooks/Probas/README.html",
    "/MyIA.AI.Notebooks/QuantConnect/README.html",
    "/MyIA.AI.Notebooks/RL/README.html",
    "/MyIA.AI.Notebooks/Search/README.html",
    "/MyIA.AI.Notebooks/Sudoku/README.html",
    "/MyIA.AI.Notebooks/SymbolicAI/README.html",
)

USER_AGENT = "coursia-site-links-guard/1.0 (+#21628)"
TIMEOUT_SECONDS = 20.0
# La page catalogue seule expose ~1650 liens uniques ; les 16 README de
# series en ajoutent ~674 (mesure 2026-11-10) ; la borne doit couvrir la
# somme, sinon le verdict serait structurellement incomplet (la troncature
# sort en rc 2). La troncature reste le signal qui surveille la croissance
# du site.
MAX_LINKS = 2600
# Sondes HTTP concurrentes (ThreadPoolExecutor) : ~2600 sondes (catalogue
# + 16 README de series) sequentielles a ~1 s seraient au ras du timeout
# de 10 min du workflow ; a 8 workers, le pire cas approchait deja la
# moitie -- 12 gardent la marge sans marteler l'origine.
PROBE_WORKERS = 12

_HREF_RE = re.compile(r'href="([^"]+)"', re.IGNORECASE)


@dataclass
class CheckResult:
    """Resultat agregé d'une passe."""

    checked: int = 0
    ok: int = 0
    broken: list[dict] = field(default_factory=list)
    raw_ipynb: list[dict] = field(default_factory=list)
    instrument_errors: list[str] = field(default_factory=list)

    def to_dict(self) -> dict:
        return {
            "checked": self.checked,
            "ok": self.ok,
            "broken": self.broken,
            "raw_ipynb": self.raw_ipynb,
            "instrument_errors": self.instrument_errors,
        }


def _same_origin(left: urllib.parse.SplitResult,
                 right: urllib.parse.SplitResult) -> bool:
    """Compare les origines HTTP en normalisant hôte et port par défaut."""
    if left.scheme.lower() not in ("http", "https"):
        return False
    if left.scheme.lower() != right.scheme.lower():
        return False
    try:
        default_port = 443 if left.scheme.lower() == "https" else 80
        left_port = default_port if left.port is None else left.port
        right_port = default_port if right.port is None else right.port
        return (left.hostname == right.hostname and left.hostname is not None
                and left_port == right_port)
    except ValueError:
        return False


def extract_internal_hrefs(html: str, page_url: str) -> list[str]:
    """Extrait les href internes d'une page, resolus en URLs absolues.

    Interne = meme origine que `page_url`. Les ancres pures (`#...`) et les
    schemas non-HTTP (mailto:, javascript:, data:) sont ignores. Le resultat
    est deduplique et trie pour un rapport stable.
    """
    origin = urllib.parse.urlsplit(page_url)
    found: set[str] = set()
    for raw in _HREF_RE.findall(html):
        href = raw.strip()
        if not href or href.startswith("#"):
            continue
        if re.match(r"^(mailto|javascript|data|tel):", href, re.IGNORECASE):
            continue
        absolute = urllib.parse.urljoin(page_url, href)
        split = urllib.parse.urlsplit(absolute)
        if not _same_origin(split, origin):
            continue
        # Fragment et query retires : on teste la ressource, pas l'ancre.
        found.add(urllib.parse.urlunsplit(
            (split.scheme, split.netloc, split.path, "", "")))
    return sorted(found)


def fetch_text(url: str, timeout: float = TIMEOUT_SECONDS) -> str:
    """GET une page et rend son texte (utf-8, remplacement tolerant).

    Le chemin est quote : une page publiee peut porter des caracteres
    accentues ou des espaces dans son chemin.
    """
    split = urllib.parse.urlsplit(url)
    path = urllib.parse.quote(split.path, safe="/%")
    request = urllib.request.Request(
        urllib.parse.urlunsplit((split.scheme, split.netloc, path, "", "")),
        headers={"User-Agent": USER_AGENT})
    with urllib.request.urlopen(request, timeout=timeout) as response:
        return response.read().decode("utf-8", "replace")


def probe_status(url: str, timeout: float = TIMEOUT_SECONDS) -> int:
    """GET une URL et rend son status HTTP (suit les redirections).

    GET plutot que HEAD : GitHub Pages sert des 404 sur HEAD pour certaines
    routes ou seule la methode GET est mappee.

    Le chemin est quote : la page publiee porte des href accentues et
    espaces ("Créateur de mail personnalisé.html") que le client HTTP
    refuse tels quels (InvalidURL) -- un refus du client n'est pas un
    lien casse, c'est une URL a encoder.
    """
    split = urllib.parse.urlsplit(url)
    path = urllib.parse.quote(split.path, safe="/%")
    request = urllib.request.Request(
        urllib.parse.urlunsplit((split.scheme, split.netloc, path, "", "")),
        headers={"User-Agent": USER_AGENT})
    try:
        with urllib.request.urlopen(request, timeout=timeout) as response:
            return response.status
    except urllib.error.HTTPError as exc:
        return exc.code


def _probe_safe(url: str, timeout: float) -> int | str:
    """Sonde qui ne leve jamais : status, ou message d'erreur instrument.

    Utilisee dans le pool de threads -- une exception qui traverse
    ThreadPoolExecutor.map serait re-levee a la consommation et tuerait
    la passe entiere au premier lien en echec reseau. Les erreurs client
    (http.client.InvalidURL, ValueError) sont traitees comme des defauts
    d'instrument : elles ne disent rien du lien, elles disent que la
    sonde n'a pas abouti.
    """
    try:
        return probe_status(url, timeout)
    except (urllib.error.URLError, OSError,
            http.client.HTTPException, ValueError) as exc:
        return f"{type(exc).__name__}: {exc}"


def run_check(base_url: str = DEFAULT_BASE_URL,
              pages: tuple[str, ...] = DEFAULT_PAGES,
              max_links: int = MAX_LINKS,
              timeout: float = TIMEOUT_SECONDS) -> CheckResult:
    """Execute la passe complete : pages critiques -> liens internes -> status."""
    result = CheckResult()
    base = base_url.rstrip("/")
    links: dict[str, set[str]] = {}
    for page in pages:
        page_url = base + page
        try:
            html = fetch_text(page_url, timeout)
        except (urllib.error.URLError, OSError,
                http.client.HTTPException, ValueError) as exc:
            result.instrument_errors.append(
                f"critical page unreachable: {page_url} ({exc})")
            continue
        # Classe structurelle (#25055) : un href interne .ipynb sur une page
        # PUBLIEE n'a rien a y faire. Quarto reecrit en .html les carnets de
        # sa liste de rendu ; un .ipynb restant = carnet non rendu. Le lien
        # repond alors soit 404 (fantome), soit 200 en JSON brut (source
        # brute au lieu d'une page lisible) -- la sonde HTTP seul laisse
        # passer la seconde moitie. Detectee hors plafond : aucun appel HTTP.
        for href in _HREF_RE.findall(html):
            href = href.strip()
            if not href or href.startswith("#"):
                continue
            absolute = urllib.parse.urljoin(page_url, href)
            split = urllib.parse.urlsplit(absolute)
            origin = urllib.parse.urlsplit(page_url)
            if (_same_origin(split, origin)
                    and urllib.parse.unquote(split.path).endswith(".ipynb")):
                result.raw_ipynb.append({
                    "href": href,
                    "source_page": page_url,
                })
        for url in extract_internal_hrefs(html, page_url):
            links.setdefault(url, set()).add(page_url)

    if result.instrument_errors:
        return result

    # Deduplication des liens .ipynb bruts (un meme href peut apparaitre
    # plusieurs fois dans la page) pour un rapport stable.
    unique_raw: list[dict] = []
    seen_raw: set[tuple[str, str]] = set()
    for entry in result.raw_ipynb:
        key = (entry["href"], entry["source_page"])
        if key in seen_raw:
            continue
        seen_raw.add(key)
        unique_raw.append(entry)
    result.raw_ipynb = unique_raw

    # Sondes HTTP concurrentes : la page catalogue seule porte ~1650 liens
    # uniques ; des sondes sequentielles depasseraient le timeout workflow.
    candidates = sorted(links)[:max_links]
    with concurrent.futures.ThreadPoolExecutor(max_workers=PROBE_WORKERS) as pool:
        statuses = list(pool.map(
            lambda url: _probe_safe(url, timeout), candidates))

    for url, status in zip(candidates, statuses):
        if isinstance(status, str):
            # Symetrie avec fetch_text : une erreur reseau en cours de sonde
            # (timeout, reset, DNS) est un defaut d'instrument, jamais un lien
            # casse — sinon le traceback ferait sortir le process en rc 1.
            result.instrument_errors.append(f"probe failed: {url} ({status})")
            continue
        result.checked += 1
        if 200 <= status < 400:
            result.ok += 1
        else:
            result.broken.append({
                "url": url,
                "status": status,
                "source_pages": sorted(links[url]),
            })

    if len(links) > max_links:
        # Troncature signalee, pas silencieuse : le verdict ne couvre alors
        # pas tout le site, ce qui est par definition un verdict d'instrument
        # incomplet (rc 2), pas un vert.
        result.instrument_errors.append(
            f"truncated: {len(links)} liens extraits, borne max_links="
            f"{max_links} — verdict incomplet, augmenter la borne")
    return result


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Verifie que les liens critiques du site publie resolvent "
                    "(garde post-deploiement, issue #21628).")
    parser.add_argument("--base-url", default=DEFAULT_BASE_URL,
                        help=f"racine du site publie (default: {DEFAULT_BASE_URL})")
    parser.add_argument("--page", action="append", dest="pages",
                        help="page critique a scanner (repetable ; default: "
                             "racine, index notebooks, parcours)")
    parser.add_argument("--max-links", type=int, default=MAX_LINKS,
                        help=f"borne du nombre de liens testes (default: {MAX_LINKS})")
    parser.add_argument("--timeout", type=float, default=TIMEOUT_SECONDS,
                        help=f"timeout HTTP par requete, secondes "
                             f"(default: {TIMEOUT_SECONDS:g})")
    parser.add_argument("--json", action="store_true",
                        help="sortie JSON (verdict + detail des liens casses)")
    args = parser.parse_args(argv)

    pages = tuple(args.pages) if args.pages else DEFAULT_PAGES
    result = run_check(args.base_url, pages, args.max_links, args.timeout)

    if args.json:
        print(json.dumps(result.to_dict(), indent=2, ensure_ascii=False))
    else:
        print(f"[site-links] checked={result.checked} ok={result.ok} "
              f"broken={len(result.broken)} raw_ipynb={len(result.raw_ipynb)}")
        for entry in result.broken:
            sources = ", ".join(entry["source_pages"])
            print(f"[site-links] BROKEN {entry['status']} {entry['url']} "
                  f"(source: {sources})")
        for entry in result.raw_ipynb:
            print(f"[site-links] RAW-IPYNB {entry['href']} "
                  f"(source: {entry['source_page']}) -- carnet non rendu "
                  f"par Quarto : ajouter a la liste de rendu, pas de probe HTTP")
        for err in result.instrument_errors:
            print(f"[site-links] INSTRUMENT {err}", file=sys.stderr)

    if result.instrument_errors:
        return EXIT_INSTRUMENT
    if result.broken or result.raw_ipynb:
        return EXIT_BROKEN_LINK
    return EXIT_OK


if __name__ == "__main__":
    sys.exit(main())