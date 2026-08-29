#!/usr/bin/env python3
"""Tests de rattachement de `series_saturation.py` (#13435).

Le defaut vise : `_DECL_RE` comptait un renvoi purement referentiel
(`voir #N`, bare `EPIC #N`) comme une declaration de travail -- la PR se
voyait rattachee a la zone dominante de l'issue citee, ce qui amortissait le
poids d'une issue neutre et gonflait l'expansion apparente d'une zone deja
saturee (reserve Hermes sur #13419, mesure : 19/459 rattachements sur la
fenetre 14 j du 2026-08-29).

Un detecteur se valide par ses faux negatifs (anti-regression.md) : les
controles ci-dessous epinglent les DEUX sens -- le renvoi de contexte NE
rattache PAS, la declaration (et la forme structurelle) rattache.
"""
from __future__ import annotations

import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT / "scripts"))

import series_saturation as ss  # noqa: E402


def _pr(body: str = "", title: str = "", number: int = 9999) -> dict:
    return {"body": body, "title": title, "number": number}


def test_context_ref_voir_does_not_attach():
    """Controle positif du fix : `voir #N` seul ne rattache pas (#13435)."""
    cited = ss.cited_issues(_pr(body="Contexte historique : voir #12373 pour le recit."))
    assert 12373 not in cited, f"`voir #N` ne doit pas rattacher, cite={cited}"


def test_context_bare_epic_does_not_attach():
    """Un bare `EPIC #N` en prose ne declare pas servir la zone."""
    cited = ss.cited_issues(_pr(body="Pourquoi ce bump etait attendu. L'EPIC #4960 suit son cours ailleurs."))
    assert 4960 not in cited, f"bare `EPIC #N` ne doit pas rattacher, cite={cited}"


def test_context_ombrelle_does_not_attach():
    cited = ss.cited_issues(_pr(body="Cadre general (ombrelle #11268), hors perimetre de cette PR."))
    assert 11268 not in cited, f"`ombrelle #N` ne doit pas rattacher, cite={cited}"


def test_declaration_see_attaches():
    """La classe declaration rattache toujours (regression guard du split)."""
    cited = ss.cited_issues(_pr(body="Contribution partielle. See #12373."))
    assert 12373 in cited, f"`See #N` doit rattacher, cite={cited}"


def test_declaration_closes_attaches():
    cited = ss.cited_issues(_pr(body="Closes #11168."))
    assert 11168 in cited


def test_declaration_refs_attaches():
    cited = ss.cited_issues(_pr(body="Refs : #12373 (epic)."))
    assert 12373 in cited, "`Refs :` doit rattacher meme suivi de `(epic)` en parenthese"


def test_structural_enfant_de_attaches():
    """Les formes structurelles restent des declarations (via _PARENT_RE)."""
    cited = ss.cited_issues(_pr(body="Enfant de l'Epic #12373, paire 4/9."))
    assert 12373 in cited, f"`Enfant de l'Epic #N` doit rattacher, cite={cited}"


def test_structural_paire_de_attaches():
    cited = ss.cited_issues(_pr(body="Paire 3/9 de l'EPIC #12373."))
    assert 12373 in cited, f"`Paire N/N de l'EPIC #N` doit rattacher, cite={cited}"


def test_title_ref_still_attaches():
    """Les refs du titre ne dependent pas du split (_REF_RE inchange)."""
    cited = ss.cited_issues(_pr(body="Rien de special.", title="fix(mgs,#12373): livraison"))
    assert 12373 in cited


def test_prev_grain_line_masked():
    """La clause `prev:` du tag Grain reste masquee (adjacence != sujet)."""
    cited = ss.cited_issues(_pr(body="Grain: MED/lean -- lane x:y -- prev: MED/lean #10999\n\nCloses #12373."))
    assert 10999 not in cited, "prev: ne doit jamais rattacher"
    assert 12373 in cited


def test_saturation_does_not_map_zone_from_context_ref():
    """Integration : une PR `voir #N` seule ne cree pas d'entree issue->zone."""
    prs = [{
        "number": 4242,
        "title": "feat(x): unrelated work",
        "body": "Incidemment, voir #12373 pour le contexte.",
        "files": [{"path": "MyIA.AI.Notebooks/Search/Part4-Metaheuristics/Foo.ipynb",
                   "additions": 10, "deletions": 0}],
    }]
    zones, i2f = ss.saturation(prs)
    assert 12373 not in i2f, f"renvoi contexte ne doit pas mapper l'issue a une zone, i2f={i2f}"
    assert "MyIA.AI.Notebooks/Search/Part4-Metaheuristics" in zones


def test_saturation_maps_zone_from_declaration():
    """Integration miroir : `See #N` + depot dans la zone rattache #N."""
    prs = [{
        "number": 4243,
        "title": "feat(x): work",
        "body": "See #12373.",
        "files": [{"path": "MyIA.AI.Notebooks/Search/Part4-Metaheuristics/Foo.ipynb",
                   "additions": 10, "deletions": 0}],
    }]
    zones, i2f = ss.saturation(prs)
    assert i2f.get(12373) == "MyIA.AI.Notebooks/Search/Part4-Metaheuristics"


if __name__ == "__main__":
    import pytest
    sys.exit(pytest.main([__file__, "-v"]))
