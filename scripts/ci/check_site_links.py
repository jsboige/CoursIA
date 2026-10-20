#!/usr/bin/env python3
"""Garde post-deploiement : verifie que les liens critiques du site publie resolvent.

Issue #21628 (fille de l'EPIC #10921). Les gardes de liens du depot
(`HTML_404`, `ipynb_links`, #18970) verifient le contenu SOURCE -- ils ne
testent pas le site DEPLOYE. Le rendu Quarto transforme les chemins
(`.md` -> `.html`, globs, freeze) : une regression de navigation ou de
rendu n'est visible qu'apres publication.

Ce garde extrait les `href` internes des pages critiques du site publie
(racine, index des notebooks, parcours), resout les liens relatifs et
teste chaque URL unique par HTTP. Il ne teste QUE la resolution des liens :
le rendu lui-meme reste l'affaire de l'audit visuel Playwright de l'EPIC
(reserve aux lanes CoursIA-2).

Baseline mesuree le 2026-10-20 (lane myia-po-2028:CoursIA, #10921
c.6296125400) : 17/17 liens critiques en HTTP 200.

Exit codes :
  0 -- tous les liens internes resolvent (2xx/3xx)
  1 -- au moins un lien interne casse (404/410/autre 4xx-5xx)
  2 -- instrument casse (page critique inaccessible ou illisible)
"""

from __future__ import annotations

import argparse
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
DEFAULT_PAGES = (
    "/",
    "/MyIA.AI.Notebooks/index.html",
    "/parcours.html",
)

USER_AGENT = "coursia-site-links-guard/1.0 (+#21628)"
TIMEOUT_SECONDS = 20.0
# Un site Pages peut avoir beaucoup de liens ; on borne pour rester un
# garde de navigation, pas un crawler.
MAX_LINKS = 120

_HREF_RE = re.compile(r'href="([^"]+)"', re.IGNORECASE)


@dataclass
class CheckResult:
    """Resultat agregé d'une passe."""

    checked: int = 0
    ok: int = 0
    broken: list[dict] = field(default_factory=list)
    instrument_errors: list[str] = field(default_factory=list)

    def to_dict(self) -> dict:
        return {
            "checked": self.checked,
            "ok": self.ok,
            "broken": self.broken,
            "instrument_errors": self.instrument_errors,
        }


def extract_internal_hrefs(html: str, page_url: str) -> list[str]:
    """Extrait les href internes d'une page, resolus en URLs absolues.

    Interne = meme origine que `page_url`. Les ancres pures (`#...`) et les
    schemas non-HTTP (mailto:, javascript:, data:) sont ignores. Le resultat
    est deduplique et trie pour un rapport stable.
    """
    origin = urllib.parse.urlsplit(page_url)
    origin_root = f"{origin.scheme}://{origin.netloc}"
    found: set[str] = set()
    for raw in _HREF_RE.findall(html):
        href = raw.strip()
        if not href or href.startswith("#"):
            continue
        if re.match(r"^(mailto|javascript|data|tel):", href, re.IGNORECASE):
            continue
        absolute = urllib.parse.urljoin(page_url, href)
        split = urllib.parse.urlsplit(absolute)
        if f"{split.scheme}://{split.netloc}" != origin_root:
            continue
        # Fragment et query retires : on teste la ressource, pas l'ancre.
        found.add(urllib.parse.urlunsplit(
            (split.scheme, split.netloc, split.path, "", "")))
    return sorted(found)


def fetch_text(url: str, timeout: float = TIMEOUT_SECONDS) -> str:
    """GET une page et rend son texte (utf-8, remplacement tolerant)."""
    request = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
    with urllib.request.urlopen(request, timeout=timeout) as response:
        return response.read().decode("utf-8", "replace")


def probe_status(url: str, timeout: float = TIMEOUT_SECONDS) -> int:
    """GET une URL et rend son status HTTP (suit les redirections).

    GET plutot que HEAD : GitHub Pages sert des 404 sur HEAD pour certaines
    routes ou seule la methode GET est mappee.
    """
    request = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
    try:
        with urllib.request.urlopen(request, timeout=timeout) as response:
            return response.status
    except urllib.error.HTTPError as exc:
        return exc.code


def run_check(base_url: str = DEFAULT_BASE_URL,
              pages: tuple[str, ...] = DEFAULT_PAGES,
              max_links: int = MAX_LINKS,
              timeout: float = TIMEOUT_SECONDS) -> CheckResult:
    """Execute la passe complete : pages critiques -> liens internes -> status."""
    result = CheckResult()
    base = base_url.rstrip("/")
    links: set[str] = set()
    for page in pages:
        page_url = base + page
        try:
            html = fetch_text(page_url, timeout)
        except (urllib.error.URLError, OSError) as exc:
            result.instrument_errors.append(
                f"critical page unreachable: {page_url} ({exc})")
            continue
        links.update(extract_internal_hrefs(html, page_url))

    if result.instrument_errors:
        return result

    for url in sorted(links)[:max_links]:
        result.checked += 1
        status = probe_status(url, timeout)
        if 200 <= status < 400:
            result.ok += 1
        else:
            result.broken.append({"url": url, "status": status})
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
              f"broken={len(result.broken)}")
        for entry in result.broken:
            print(f"[site-links] BROKEN {entry['status']} {entry['url']}")
        for err in result.instrument_errors:
            print(f"[site-links] INSTRUMENT {err}", file=sys.stderr)

    if result.instrument_errors:
        return EXIT_INSTRUMENT
    if result.broken:
        return EXIT_BROKEN_LINK
    return EXIT_OK


if __name__ == "__main__":
    sys.exit(main())