#!/usr/bin/env python3
"""
reconcile_writings_wolfram.py - Reconciliation des slugs 404 du corpus Wolfram

EPIC Origami #19742, pli 1-bis. Le pli 1 (#19766) a consigne 22 textes
non-distillites, dont 17 slug 404 sur writings.stephenwolfram.com.
Hypothese : le sitemap du site (wrisitemap-pt-post-1.xml) permet de
retrouver les slugs actuels.

Le script :
1. Telecharge le sitemap (245 URLs).
2. Matche chaque titre du corpus YAML a l'index inverse du sitemap.
3. Emet un rapport (terminal + fichier JSON) : ancien titre -> nouvelle URL.

Aucun fichier du depot n'est modifie par ce script en mode normal
(uniquement le rapport JSON dans un chemin gitignored si demande).

Cible : 17/17 trouves ou diagnostic des non trouves (paywall / journal /
autre categorie).
"""

import argparse
import json
import re
import sys
import urllib.request
import xml.etree.ElementTree as ET
from pathlib import Path

SITEMAP_URL = "https://writings.stephenwolfram.com/wrisitemap-pt-post-1.xml"
SITEMAP_LOCAL = Path(__file__).parent / "sitemap_writings.xml"
NS = {"sm": "http://www.sitemaps.org/schemas/sitemap/0.9"}

CORPUS_PATH = Path(__file__).parent / "wolfram_corpus.yaml"

FALLBACK_CORPUS = [
    ("A New Kind of Science: A 15-Year View", 2017),
    ("What We've Built Is a Computational Language", 2020),
    ("A Class of Models with the Potential to Represent Fundamental Physics", 2020),
    ("A Project to Find the Fundamental Theory of Physics", 2020),
    ("The Concept of the Ruliad", 2021),
    ("The Physicalization of Metamathematics", 2022),
    ("Can AI Solve Science", 2024),
    ("What's Really Going On in Machine Learning", 2024),
    ("Why Does Biological Evolution Work", 2024),
    ("Foundations of Biological Evolution", 2024),
    ("What's Special about Life", 2025),
    ("The Ruliology of Lambdas", 2025),
    ("P vs. NP and the Difficulty of Computation", 2026),
    ("What Is Ruliology", 2026),
    ("What Ultimately Is There", 2026),
    ("What Can We Learn about Engineering and Innovation from Half a Century of the Game of Life", 2025),
]


def download_sitemap(target: Path, timeout: int = 30) -> Path:
    """Telecharge le sitemap writings si pas deja en cache."""
    if target.exists() and target.stat().st_size > 1000:
        return target
    target.parent.mkdir(parents=True, exist_ok=True)
    req = urllib.request.Request(SITEMAP_URL, headers={"User-Agent": "CoursIA-pli1bis/0.1"})
    with urllib.request.urlopen(req, timeout=timeout) as resp:
        target.write_bytes(resp.read())
    return target


def normalize(text: str) -> str:
    """Normalise pour comparaison : lowercase, retire non-alnum."""
    return re.sub(r"[^a-z0-9]+", "", text.lower())


def parse_corpus_yaml(path: Path) -> list[tuple[str, int]]:
    """Parser minimal YAML pour eviter PyYAML.

    Format : ``- [YYYY] Title``.
    """
    if not path.exists():
        return []
    items = []
    pat = re.compile(r"^\s*-\s*\[(\d{4})\]\s+(.+)$")
    for line in path.read_text(encoding="utf-8").splitlines():
        m = pat.match(line)
        if m:
            items.append((m.group(2).strip(), int(m.group(1))))
    return items


def load_sitemap_urls(sitemap_path: Path) -> list[tuple[int, str, str, str]]:
    """Charge les URL du sitemap -> [(year, title, url, slug), ...]."""
    tree = ET.parse(sitemap_path)
    urls = []
    for url in tree.getroot().findall("sm:url", NS):
        loc = url.find("sm:loc", NS).text.strip()
        m = re.match(r"https?://[^/]+/(\d{4})/\d{2}/([^/]+)/?", loc)
        if m:
            year = int(m.group(1))
            slug = m.group(2)
            title = slug.replace("-", " ")
            urls.append((year, title, loc, slug))
    return urls


def find_best_match(
    title_query: str,
    year_query: int,
    urls: list[tuple[int, str, str, str]],
    year_fuzz: int = 1,
) -> tuple[int, str, str, str] | None:
    """Trouve le meilleur match pour (title, year) avec tolerance d'annee."""
    q = normalize(title_query)
    candidates = []
    for year, title, url, slug in urls:
        if abs(year - year_query) > year_fuzz:
            continue
        t = normalize(title)
        if q in t:
            score = len(q) - abs(year - year_query)
            candidates.append((score, year, title, url, slug))
    if not candidates:
        return None
    candidates.sort(key=lambda x: -x[0])
    return candidates[0][1:]


def reconcile(
    corpus: list[tuple[str, int]],
    urls: list[tuple[int, str, str, str]],
    year_fuzz: int = 1,
) -> dict:
    """Reconciliation du corpus contre le sitemap."""
    found, not_found = [], []
    for title, year in corpus:
        result = find_best_match(title, year, urls, year_fuzz=year_fuzz)
        if result:
            ryear, rtitle, rurl, rslug = result
            found.append(
                {
                    "query_title": title,
                    "query_year": year,
                    "matched_year": ryear,
                    "matched_title": rtitle,
                    "matched_url": rurl,
                    "matched_slug": rslug,
                }
            )
        else:
            not_found.append({"query_title": title, "query_year": year})
    return {
        "sitemap_url": SITEMAP_URL,
        "sitemap_size": len(urls),
        "corpus_size": len(corpus),
        "year_fuzz": year_fuzz,
        "found": found,
        "not_found": not_found,
        "found_count": len(found),
        "not_found_count": len(not_found),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--offline", action="store_true",
                        help="Utiliser le sitemap telecharge sans re-telecharger.")
    parser.add_argument("--output", type=Path, default=None,
                        help="Fichier JSON de sortie (defaut: stdout).")
    parser.add_argument("--year-fuzz", type=int, default=1,
                        help="Tolerance d'annee (defaut: 1).")
    args = parser.parse_args()

    if args.offline and SITEMAP_LOCAL.exists():
        sitemap = SITEMAP_LOCAL
    else:
        try:
            sitemap = download_sitemap(SITEMAP_LOCAL)
        except Exception as e:
            print(f"ERREUR telechargement sitemap : {e}", file=sys.stderr)
            return 2

    corpus = parse_corpus_yaml(CORPUS_PATH) or FALLBACK_CORPUS
    urls = load_sitemap_urls(sitemap)
    report = reconcile(corpus, urls, year_fuzz=args.year_fuzz)

    if args.output:
        args.output.write_text(json.dumps(report, indent=2, ensure_ascii=False), encoding="utf-8")
        print(f"Rapport ecrit : {args.output}")
    else:
        print(json.dumps(report, indent=2, ensure_ascii=False))

    coverage = report["found_count"] / report["corpus_size"] if report["corpus_size"] else 0
    print(f"\n=== Bilan ===", file=sys.stderr)
    print(f"Trouves : {report['found_count']}/{report['corpus_size']} ({coverage:.0%})", file=sys.stderr)
    if report["not_found"]:
        print(f"Non trouves ({report['not_found_count']}) :", file=sys.stderr)
        for item in report["not_found"]:
            print(f"  - ({item['query_year']}) {item['query_title']}", file=sys.stderr)

    return 0


if __name__ == "__main__":
    sys.exit(main())