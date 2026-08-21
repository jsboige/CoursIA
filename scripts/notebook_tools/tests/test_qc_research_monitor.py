"""Tests unitaires du parser sitemap + helpers de qc_research_monitor (Epic #11698).

La partie reseau (fetch sitemap) et la creation d'issues sont couvertes par le
dry-run local documente dans la PR — pas par ces tests.
"""

import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from qc_research_monitor import (  # noqa: E402
    load_state,
    parse_articles,
    title_from_slug,
)

SITEMAP_FIXTURE = """<?xml version="1.0" encoding="UTF-8"?>
<urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9">
<url>
<loc>https://www.quantconnect.com/forum/list/8/research</loc>
<lastmod>2026-08-17T12:19:33+00:00</lastmod>
</url>
<url>
<loc>https://www.quantconnect.com/research/21160/momentum-in-capital-gain-stocks/</loc>
<lastmod>2026-08-17T12:19:33+00:00</lastmod>
</url>
<url>
<loc>https://www.quantconnect.com/research/20966/filing-language-stability-as-a-selection-signal/</loc>
<lastmod>2026-06-02T10:00:00+00:00</lastmod>
</url>
<url>
<loc>https://www.quantconnect.com/research/15925/the-importance-of-benchmarking/</loc>
</url>
</urlset>
"""


def test_parse_extracts_articles_ignores_forum_listings():
    arts = parse_articles(SITEMAP_FIXTURE)
    assert len(arts) == 3
    assert all("/research/" in a["url"] for a in arts)
    assert not any("forum" in a["url"] for a in arts)


def test_parse_sorts_by_id_descending():
    arts = parse_articles(SITEMAP_FIXTURE)
    ids = [a["id"] for a in arts]
    assert ids == sorted(ids, reverse=True)
    assert ids == [21160, 20966, 15925]


def test_parse_handles_missing_lastmod():
    arts = parse_articles(SITEMAP_FIXTURE)
    bench = [a for a in arts if a["id"] == 15925][0]
    assert bench["lastmod"] == ""
    with_mod = [a for a in arts if a["id"] == 21160][0]
    assert with_mod["lastmod"] == "2026-08-17T12:19:33+00:00"


def test_title_from_slug():
    assert title_from_slug("momentum-in-capital-gain-stocks") == "Momentum in capital gain stocks"
    assert title_from_slug("the-importance-of-benchmarking") == "The importance of benchmarking"


def test_load_state_missing_file_is_bootstrap(tmp_path):
    state = load_state(tmp_path / "absent.json")
    assert state == {"seeded": {}}


def test_load_state_existing_seed_is_loaded(tmp_path):
    p = tmp_path / "seeded.json"
    p.write_text(json.dumps({"seeded": {"21160": {"issue": 12034}}}), encoding="utf-8")
    state = load_state(p)
    assert "21160" in state["seeded"]


def test_load_state_empty_seed_is_bootstrap(tmp_path):
    p = tmp_path / "seeded.json"
    p.write_text(json.dumps({"seeded": {}}), encoding="utf-8")
    assert load_state(p) == {"seeded": {}}
