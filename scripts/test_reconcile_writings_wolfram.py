#!/usr/bin/env python3
"""Tests unitaires pour reconcile_writings_wolfram."""

import json
import sys
import xml.etree.ElementTree as ET
from pathlib import Path
from unittest.mock import MagicMock

# Permettre l'import du module depuis scripts/bibliography/
sys.path.insert(0, str(Path(__file__).parent / "bibliography"))

from reconcile_writings_wolfram import (  # noqa: E402
    download_sitemap,
    find_best_match,
    load_sitemap_urls,
    normalize,
    parse_corpus_yaml,
    reconcile,
)


SITEMAP_URL = "https://writings.stephenwolfram.com/wrisitemap-pt-post-1.xml"
SITEMAP_NS = "{http://www.sitemaps.org/schemas/sitemap/0.9}"


def make_sitemap_xml(urls: list[str]) -> str:
    """Construit un sitemap XML minimal pour les tests."""
    body = "".join(f"<url><loc>{u}</loc></url>" for u in urls)
    return (
        '<?xml version="1.0" encoding="UTF-8"?>'
        f'<urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9">{body}</urlset>'
    )


def test_normalize_strips_punctuation():
    assert normalize("Hello, World!") == "helloworld"
    assert normalize("A Physicalization of Metamathematics") == "aphysicalizationofmetamathematics"
    assert normalize("  spaces  ") == "spaces"


def test_find_best_match_exact_substring():
    urls = [
        (2019, "what weve built is a computational language",
         "https://writings.stephenwolfram.com/2019/05/what-weve-built-is-a-computational-language-and-thats-very-important/",
         "what-weve-built-is-a-computational-language-and-thats-very-important"),
    ]
    result = find_best_match("What We've Built Is a Computational Language", 2020, urls, year_fuzz=1)
    assert result is not None
    ryear, rtitle, rurl, rslug = result
    assert ryear == 2019
    assert "computational" in rtitle


def test_find_best_match_no_match():
    urls = [
        (2020, "totally unrelated title", "https://example.com/2020/totally-unrelated/", "totally-unrelated"),
    ]
    result = find_best_match("A Class of Models", 2020, urls)
    assert result is None


def test_find_best_match_year_strict():
    """year_fuzz=0 ne tolere pas le decalage d'annee."""
    urls = [
        (2019, "what weve built", "https://example.com/2019/what-weve-built/", "what-weve-built"),
    ]
    # year_query=2020, year_fuzz=0 -> pas de match
    assert find_best_match("What We've Built", 2020, urls, year_fuzz=0) is None
    # year_query=2020, year_fuzz=1 -> match
    assert find_best_match("What We've Built", 2020, urls, year_fuzz=1) is not None


def test_parse_corpus_yaml(tmp_path):
    yaml_path = tmp_path / "test.yaml"
    yaml_path.write_text(
        "# Header\n"
        "- [2020] Some Title\n"
        "not a match\n"
        "- [2024] Another Title\n",
        encoding="utf-8",
    )
    items = parse_corpus_yaml(yaml_path)
    assert items == [("Some Title", 2020), ("Another Title", 2024)]


def test_parse_corpus_yaml_missing(tmp_path):
    """Fichier absent -> liste vide (le fallback s'applique)."""
    assert parse_corpus_yaml(tmp_path / "missing.yaml") == []


def test_load_sitemap_urls(tmp_path):
    xml = make_sitemap_xml([
        "https://writings.stephenwolfram.com/2024/03/can-ai-solve-science/",
        "https://writings.stephenwolfram.com/2024/08/whats-really-going-on-in-machine-learning-some-minimal-models/",
    ])
    sitemap_path = tmp_path / "sitemap.xml"
    sitemap_path.write_text(xml, encoding="utf-8")
    urls = load_sitemap_urls(sitemap_path)
    assert len(urls) == 2
    assert urls[0][0] == 2024
    assert urls[0][1] == "can ai solve science"
    assert urls[1][0] == 2024


def test_reconcile_full_flow(tmp_path):
    xml = make_sitemap_xml([
        "https://writings.stephenwolfram.com/2024/03/can-ai-solve-science/",
        "https://writings.stephenwolfram.com/2024/05/why-does-biological-evolution-work-a-minimal-model-for-biological-evolution-and-other-adaptive-processes/",
    ])
    sitemap_path = tmp_path / "sitemap.xml"
    sitemap_path.write_text(xml, encoding="utf-8")
    urls = load_sitemap_urls(sitemap_path)

    corpus = [
        ("Can AI Solve Science", 2024),
        ("Why Does Biological Evolution Work", 2024),
        ("Unknown Essay", 2026),
    ]
    report = reconcile(corpus, urls)
    assert report["found_count"] == 2
    assert report["not_found_count"] == 1
    assert report["not_found"][0]["query_title"] == "Unknown Essay"


def test_corpus_yaml_exists_and_parses():
    """Le fichier de corpus du depot doit exister et parser sans erreur."""
    corpus_path = Path(__file__).parent / "bibliography" / "wolfram_corpus.yaml"
    assert corpus_path.exists(), f"Missing corpus YAML: {corpus_path}"
    items = parse_corpus_yaml(corpus_path)
    assert len(items) >= 17, f"Corpus trop court ({len(items)} < 17)"