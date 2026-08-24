#!/usr/bin/env python3
"""Unit tests for qc_research_monitor.py -- le semis de l'Epic #11698.

Pins la dedup contre les issues existantes, ajout apres l'incident du
run 32690576863 (2026-08-24) : semis de l'article 21195 en #12748 reussi,
puis push de l'etat rejete fetch-first (checkout au SHA du declenchement
schedule 04:35, runner obtenu 08:08, ~65 merges/jour sur main entre les
deux). L'etat JSON sur main restait a 144 IDs, donc le run suivant aurait
re-seme l'article en double. La verite terrain est l'issue existante, pas
le JSON non commitE.

Run: python -m pytest scripts/tests/test_qc_research_monitor.py
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from notebook_tools.qc_research_monitor import (  # noqa: E402
    find_existing_issue,
    parse_articles,
)

SITEMAP_XML = """<?xml version="1.0" encoding="UTF-8"?>
<urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9">
  <url><loc>https://www.quantconnect.com/research/21195/bitcoin-regime-signal-for-growth-equities/</loc><lastmod>2026-08-22</lastmod></url>
  <url><loc>https://www.quantconnect.com/research/21160/momentum-in-capital-gain-stocks/</loc><lastmod>2026-08-15</lastmod></url>
  <url><loc>https://www.quantconnect.com/forum/list/discussions/</loc></url>
  <url><loc>https://www.quantconnect.com/research/</loc></url>
</urlset>
"""


def test_parse_articles_filters_non_research_and_sorts_desc():
    articles = parse_articles(SITEMAP_XML)
    # les entrees forum/list et la racine /research/ ne sont pas des articles
    assert [a["id"] for a in articles] == [21195, 21160]
    assert articles[0]["slug"] == "bitcoin-regime-signal-for-growth-equities"
    assert articles[0]["lastmod"] == "2026-08-22"


def test_find_existing_issue_replays_run_32690576863():
    # Scénario exact du 2026-08-24 : l'article 21195 semé en #12748 (CLOSED,
    # verdict IGNORE par po-2024) alors que l'état JSON commité est resté à
    # 144 IDs. La dédup doit rapprocher 21195 -> 12748 et empêcher le re-semis.
    known = [
        {"number": 11698,
         "title": "[EPIC] Moissonnage quantconnect.com/research/ — distillation intelligente vs duplication"},
        {"number": 12748,
         "title": "[QC-research] Bitcoin regime signal for growth equities (#21195)"},
        {"number": 12034,
         "title": "[QC-research] Momentum in capital gain stocks (#21160)"},
    ]
    articles = parse_articles(SITEMAP_XML)
    dedup = find_existing_issue(articles, known)
    assert dedup == {21195: 12748, 21160: 12034}


def test_find_existing_issue_ignores_titles_without_article_suffix():
    # L'EPIC et l'issue technique du cron ne portent pas le suffixe "(#<id>)"
    # et ne doivent pas être prises pour des semis d'articles.
    known = [
        {"number": 11698, "title": "[EPIC] Moissonnage quantconnect.com/research/ — (doublon de (#4000) ?"},
        {"number": 12035, "title": "[QC-research] Livrer le cron qc-research-monitor (scan hebdo)"},
    ]
    dedup = find_existing_issue(parse_articles(SITEMAP_XML), known)
    assert dedup == {}


def test_find_existing_issue_empty_known():
    assert find_existing_issue(parse_articles(SITEMAP_XML), []) == {}


def test_find_existing_issue_trailing_space_in_title():
    # gh --json title peut rendre un titre avec espace final selon la source
    known = [{"number": 12748,
              "title": "[QC-research] Bitcoin regime signal for growth equities (#21195) "}]
    dedup = find_existing_issue(parse_articles(SITEMAP_XML), known)
    assert dedup == {21195: 12748}
