"""Tests unitaires du parser sitemap + helpers de qc_research_monitor (Epic #11698).

La partie reseau (fetch sitemap) et la creation d'issues sont couvertes par le
dry-run local documente dans la PR — pas par ces tests.
"""

import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from qc_research_monitor import (  # noqa: E402
    TEMPLATE_PATH,
    find_existing_issue,
    issue_body,
    load_state,
    parse_articles,
    title_from_slug,
)

# Racine du repo : scripts/notebook_tools/tests/ -> 3 niveaux au-dessus.
REPO_ROOT = Path(__file__).resolve().parents[3]

# Fixture dediee aux tests de dedup : contient l'article 21195 (semi rejouable
# du run 32690576863 le 2026-08-24) + une entree forum + la racine /research/,
# qui doivent etre filtres comme non-articles.
SITEMAP_DEDUP_FIXTURE = """<?xml version="1.0" encoding="UTF-8"?>
<urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9">
  <url><loc>https://www.quantconnect.com/research/21195/bitcoin-regime-signal-for-growth-equities/</loc><lastmod>2026-08-22</lastmod></url>
  <url><loc>https://www.quantconnect.com/research/21160/momentum-in-capital-gain-stocks/</loc><lastmod>2026-08-15</lastmod></url>
  <url><loc>https://www.quantconnect.com/forum/list/discussions/</loc></url>
  <url><loc>https://www.quantconnect.com/research/</loc></url>
</urlset>
"""

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


# --- Controle par faux negatif (reprise #12036) : le chemin du template doit
# resoudre sur l'arbre, sinon le cron semait des issues a corps vide sans
# erreur (garde `if exists()` silencieuse). Sans ce test, le defaut repasse au
# prochain deplacement de fichier. ---

def test_template_path_resolves_on_the_tree():
    """TEMPLATE_PATH pointe sur un fichier reellement present dans le repo.

    Le cron tourne depuis la racine (workflow qc-research-monitor.yml) : le
    chemin relatif doit exister tel quel, resolu depuis REPO_ROOT.
    """
    assert (REPO_ROOT / TEMPLATE_PATH).is_file(), (
        f"{TEMPLATE_PATH} introuvable depuis la racine — le cron creerait "
        f"des issues a corps vide (reprise #12036)"
    )


def test_issue_body_is_non_empty_and_carries_the_template():
    """Le corps genere combine l'en-tete d'article et le contenu du template.

    Controle le faux negatif exact de la reprise : un corps vide (template
    absent lu en silence) passait tous les autres tests.
    """
    article = {
        "id": 21160,
        "slug": "momentum-in-capital-gain-stocks",
        "url": "https://www.quantconnect.com/research/21160/momentum-in-capital-gain-stocks/",
        "lastmod": "2026-08-17T12:19:33+00:00",
    }
    import os
    old_cwd = os.getcwd()
    os.chdir(REPO_ROOT)
    try:
        body = issue_body(article)
    finally:
        os.chdir(old_cwd)
    assert "## Article source" in body
    assert article["url"] in body
    assert len(body) > len("## Article source") + 200, (
        "corps trop court : le template n'a pas ete concatene"
    )


def test_issue_body_fails_loud_when_template_missing(tmp_path, monkeypatch):
    """Un template introuvable leve, plutot que de produire un corps vide."""
    import qc_research_monitor as mod
    monkeypatch.setattr(mod, "TEMPLATE_PATH", tmp_path / "absent.md")
    article = {"id": 1, "slug": "x", "url": "u", "lastmod": ""}
    try:
        mod.issue_body(article)
    except FileNotFoundError as e:
        assert "template introuvable" in str(e)
    else:
        raise AssertionError("issue_body doit lever FileNotFoundError")


# --- Dedup anti re-semis (reprise #11698, incident run 32690576863) ---
# L'etat JSON commitE restait a 144 IDs alors que l'article 21195 avait deja
# ete seme en #12748 : la verite terrain est l'issue existante (suffixe "(#<id>)"
# deterministe dans le titre), pas le JSON d'etat non commitE.

def test_parse_articles_filters_non_research_and_sorts_desc():
    articles = parse_articles(SITEMAP_DEDUP_FIXTURE)
    # les entrees forum/list et la racine /research/ ne sont pas des articles
    assert [a["id"] for a in articles] == [21195, 21160]
    assert articles[0]["slug"] == "bitcoin-regime-signal-for-growth-equities"
    assert articles[0]["lastmod"] == "2026-08-22"


def test_find_existing_issue_replays_run_32690576863():
    # Scenario exact du 2026-08-24 : l'article 21195 seme en #12748 (CLOSED,
    # verdict IGNORE par po-2024) alors que l'etat JSON commite est reste a
    # 144 IDs. La dedup doit rapprocher 21195 -> 12748 et empecher le re-semis.
    known = [
        {"number": 11698,
         "title": "[EPIC] Moissonnage quantconnect.com/research/ — distillation intelligente vs duplication"},
        {"number": 12748,
         "title": "[QC-research] Bitcoin regime signal for growth equities (#21195)"},
        {"number": 12034,
         "title": "[QC-research] Momentum in capital gain stocks (#21160)"},
    ]
    articles = parse_articles(SITEMAP_DEDUP_FIXTURE)
    dedup = find_existing_issue(articles, known)
    assert dedup == {21195: 12748, 21160: 12034}


def test_find_existing_issue_ignores_titles_without_article_suffix():
    # L'EPIC et l'issue technique du cron ne portent pas le suffixe "(#<id>)"
    # et ne doivent pas etre prises pour des semis d'articles.
    known = [
        {"number": 11698, "title": "[EPIC] Moissonnage quantconnect.com/research/ — (doublon de (#4000) ?"},
        {"number": 12035, "title": "[QC-research] Livrer le cron qc-research-monitor (scan hebdo)"},
    ]
    dedup = find_existing_issue(parse_articles(SITEMAP_DEDUP_FIXTURE), known)
    assert dedup == {}


def test_find_existing_issue_empty_known():
    assert find_existing_issue(parse_articles(SITEMAP_DEDUP_FIXTURE), []) == {}


def test_find_existing_issue_trailing_space_in_title():
    # gh --json title peut rendre un titre avec espace final selon la source
    known = [{"number": 12748,
              "title": "[QC-research] Bitcoin regime signal for growth equities (#21195) "}]
    dedup = find_existing_issue(parse_articles(SITEMAP_DEDUP_FIXTURE), known)
    assert dedup == {21195: 12748}
