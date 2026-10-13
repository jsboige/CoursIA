#!/usr/bin/env python3
"""Unit tests for ``scripts/variation_base_main.py`` (--base main filter, #18940).

Le filtre elimine les PRs empilees sur une branche de feature du comptage
G-VAR-2/3. Le contrat est :
  - PR avec ``baseRefName == "main"`` : conservee
  - PR avec ``baseRefName`` absent : conservee (retrocompat, donnees
    historiques ou producer anterieur au fix)
  - PR avec ``baseRefName`` present et != ``"main"`` : filtree
  - PR avec ``baseRefName`` present et == ``"main"`` : conservee

Le controle positif (#18910) : une PR empilee sur ``test/18775-k07-budget-mensuel``
ne doit plus apparaitre comme ``prev_pr`` d'une PR adjacente.

Run: ``python -m pytest scripts/tests/test_variation_base_main.py``.
"""
from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from variation_base_main import filter_base_main, MAIN_BRANCH  # noqa: E402


# ---------------------------------------------------------------------------
# Cas nominaux
# ---------------------------------------------------------------------------

def test_keeps_pr_with_baseRefName_main():
    """Cas standard : PR livree directement dans main. Conservee."""
    prs = [{"number": 1, "body": "x", "mergedAt": "2026-10-02T00:00:00Z",
            "baseRefName": "main"}]
    out = filter_base_main(prs)
    assert out == prs


def test_drops_pr_with_baseRefName_feature_branch():
    """Cas central #18910 : PR empilee sur une branche de feature. Filtree."""
    prs = [{"number": 18910, "body": "Grain: LIGHT/guard -- lane po-2024",
            "mergedAt": "2026-10-02T01:39:00Z",
            "baseRefName": "test/18775-k07-budget-mensuel"}]
    out = filter_base_main(prs)
    assert out == []


def test_keeps_pr_without_baseRefName_for_backward_compat():
    """Retrocompat : un producer anterieur au fix n'ajoutait pas
    baseRefName. La PR est preservee pour ne pas casser l'execution."""
    prs = [{"number": 1, "body": "x", "mergedAt": "2026-10-02T00:00:00Z"}]
    out = filter_base_main(prs)
    assert out == prs


def test_mixed_set_filters_only_stacked_prs():
    """Un set mixte : 2 main + 1 empilee + 1 retrocompat. La empilee
    seule doit disparaitre, les autres restent dans l'ordre."""
    prs = [
        {"number": 1, "baseRefName": "main", "mergedAt": "2026-10-02T00:00:00Z"},
        {"number": 2, "baseRefName": "test/stack", "mergedAt": "2026-10-02T00:01:00Z"},
        {"number": 3, "mergedAt": "2026-10-02T00:02:00Z"},  # no baseRefName
        {"number": 4, "baseRefName": "main", "mergedAt": "2026-10-02T00:03:00Z"},
    ]
    out = filter_base_main(prs)
    assert [p["number"] for p in out] == [1, 3, 4]


def test_preserves_order():
    """L'ordre des PRs conservees est preserve -- les detecteurs en aval
    (sequence_as_of, light_cap_status) supposent un ordre chronologique."""
    prs = [
        {"number": 1, "baseRefName": "main"},
        {"number": 2, "baseRefName": "main"},
        {"number": 3, "baseRefName": "main"},
    ]
    out = filter_base_main(prs)
    assert [p["number"] for p in out] == [1, 2, 3]


# ---------------------------------------------------------------------------
# Cas limites
# ---------------------------------------------------------------------------

def test_empty_list_returns_empty():
    assert filter_base_main([]) == []


def test_main_branch_constant_is_main():
    """Le nom canonique de la branche par defaut est 'main'. Un changement
    de ce nom (rare) impose une revue explicite -- c'est pourquoi il vit
    dans une constante exportee."""
    assert MAIN_BRANCH == "main"


def test_other_release_branch_is_filtered():
    """Une PR sur 'release/1.0' n'est pas dans main : filtree."""
    prs = [{"number": 1, "baseRefName": "release/1.0"}]
    out = filter_base_main(prs)
    assert out == []


def test_non_dict_entry_is_kept_with_warning():
    """Une entree corrompue (non-dict) est preservee pour ne pas perdre un
    grain en silence. Le warn hook permet de tracer la corruption."""
    captured = []
    prs = ["not-a-dict", {"number": 1, "baseRefName": "main"}]
    out = filter_base_main(prs, warn=captured.append)
    # L'entree non-dict est preservee, le PR main aussi.
    assert len(out) == 2
    assert any("non-dict" in m for m in captured)


def test_non_list_input_raises_typeerror():
    """Le filtre defend son contrat d'entree : tout ce qui n'est pas une
    liste leve TypeError plutot que de masquer le defaut en aval."""
    import pytest
    with pytest.raises(TypeError):
        filter_base_main({"number": 1})  # type: ignore[arg-type]
    with pytest.raises(TypeError):
        filter_base_main("not a list")  # type: ignore[arg-type]


# ---------------------------------------------------------------------------
# Controles positifs et temoin negatif
# ---------------------------------------------------------------------------

def test_dropped_count_is_reported_via_warn():
    """Le warn hook recoit un message indiquant combien de PRs empilees
    ont ete filtreees -- utile pour diagnostiquer un pic d'empilements."""
    captured = []
    prs = [
        {"number": 1, "baseRefName": "feature/a"},
        {"number": 2, "baseRefName": "feature/b"},
        {"number": 3, "baseRefName": "main"},
    ]
    filter_base_main(prs, warn=captured.append)
    assert len(captured) == 1
    assert "2 PR(s)" in captured[0]
    assert "empil" in captured[0].lower()


def test_no_warning_when_no_stacked_prs():
    """Aucun warn n'est emis si toutes les PRs sont dans main ou sans
    baseRefName -- l'absence de signal est la regle."""
    captured = []
    prs = [
        {"number": 1, "baseRefName": "main"},
        {"number": 2},  # retrocompat
    ]
    filter_base_main(prs, warn=captured.append)
    assert captured == []


def test_positive_control_18910_specifically_excluded():
    """Temoin positif #18910 : la PR 18910 (base test/18775-...) ne doit
    plus apparaitre apres filtre. Le numero est explicite dans le test
    pour qu'une relecture du code rattache ce test au constat."""
    prs = [
        {"number": 18910, "baseRefName": "test/18775-k07-budget-mensuel",
         "body": "Grain: LIGHT/guard -- lane myia-po-2024:CoursIA-2"},
        {"number": 18822, "baseRefName": "main",
         "body": "Grain: MED/refactor -- lane myia-po-2024:CoursIA-2"},
    ]
    out = filter_base_main(prs)
    numbers = [p["number"] for p in out]
    assert 18910 not in numbers
    assert 18822 in numbers
