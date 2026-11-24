"""Tests de scripts/ci/check_series_inventory_claims.py (#20445 volet 4).

Controles positifs ancres sur l'instance fondatrice #19494 (plan Percolation) :
le body d'origine omettait 03b/03c et citait un 04-Lean jamais livre.
"""
from __future__ import annotations

import sys
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO / "scripts" / "ci"))

from check_series_inventory_claims import (  # noqa: E402
    analyse,
    body_citations,
    list_series_notebooks,
    main,
    parse_expect,
)


@pytest.fixture
def percolation(tmp_path: Path) -> Path:
    """Mini-serie Percolation reproduisant l'etat reel de main (6 carnets)."""
    series = tmp_path / "Probas" / "Applications" / "Percolation"
    series.mkdir(parents=True)
    for name in (
        "Percolation-01-Supercritique-Python.ipynb",
        "Percolation-02-Lean.ipynb",
        "Percolation-03-Critique-Python.ipynb",
        "Percolation-03b-Critique-L128-L256.ipynb",
        "Percolation-03c-Critique-L512.ipynb",
        "Percolation-04-Sharpness-Python.ipynb",
    ):
        (series / name).write_text("{}", encoding="utf-8")
    return tmp_path


BODY_19494_ORIG = """
Etat actuel : Percolation-01-Supercritique-Python et Percolation-02-Lean.
Les trois carnets suivants :
- Percolation-03-Critique-Python
- Percolation-04-Sharpness-Python
- Percolation-04-Sharpness-Lean
"""


def test_body_citations_bare_name_and_extension() -> None:
    cited = body_citations("cite `Percolation-02-Lean` et Percolation-01-Supercritique-Python.ipynb")
    assert "Percolation-02-Lean" in cited
    assert "Percolation-01-Supercritique-Python" in cited


def test_list_series_excludes_archive(percolation: Path) -> None:
    arch = percolation / "Probas" / "Applications" / "Percolation" / "_archive"
    arch.mkdir()
    (arch / "Percolation-00-Ancien.ipynb").write_text("{}", encoding="utf-8")
    notebooks = list_series_notebooks(Path("Probas/Applications/Percolation"), percolation)
    assert len(notebooks) == 6
    assert all("_archive" not in str(p) for p in notebooks)


def test_founding_case_19494_both_directions(percolation: Path) -> None:
    """Body d'origine : 03b/03c omis, 04-Lean cite mais jamais livre."""
    notebooks = list_series_notebooks(Path("Probas/Applications/Percolation"), percolation)
    findings = analyse(BODY_19494_ORIG, notebooks)
    verdicts = {f["notebook"]: f["verdict"] for f in findings}
    assert verdicts.get("Percolation-03b-Critique-L128-L256") == "ON_DISK_NOT_CITED"
    assert verdicts.get("Percolation-03c-Critique-L512") == "ON_DISK_NOT_CITED"
    assert verdicts.get("Percolation-04-Sharpness-Lean") == "CITED_NOT_ON_DISK"
    assert len(findings) == 3


def test_all_cited_all_real_is_ok(percolation: Path) -> None:
    body = "Carnets : " + " ".join(
        p.stem for p in sorted((percolation / "Probas" / "Applications" / "Percolation").glob("*.ipynb"))
    )
    notebooks = list_series_notebooks(Path("Probas/Applications/Percolation"), percolation)
    assert analyse(body, notebooks) == []


def test_substring_is_not_a_citation(percolation: Path) -> None:
    """Citer Search-03 ne cite pas Search-03b : correspondance par stem exact."""
    notebooks = list_series_notebooks(Path("Probas/Applications/Percolation"), percolation)
    body = "Seul Percolation-03-Critique-Python est livre."  # ne cite pas 03b
    findings = analyse(body, notebooks)
    names = {f["notebook"] for f in findings if f["verdict"] == "ON_DISK_NOT_CITED"}
    assert "Percolation-03b-Critique-L128-L256" in names


def test_prose_tokens_never_ghosts(percolation: Path) -> None:
    """README, main, lake... : la prose quelconque ne declenche pas CITED_NOT_ON_DISK."""
    notebooks = list_series_notebooks(Path("Probas/Applications/Percolation"), percolation)
    findings = analyse("Voir le README de la serie sur main, regle du lake.", notebooks)
    # Aucune citation -> les 6 reels sont ON_DISK_NOT_CITED (comportement voulu),
    # mais AUCUN token de prose ne devient un fantome CITED_NOT_ON_DISK.
    assert [f for f in findings if f["verdict"] == "CITED_NOT_ON_DISK"] == []
    assert len([f for f in findings if f["verdict"] == "ON_DISK_NOT_CITED"]) == 6


def test_accented_multiword_notebook_cited(tmp_path: Path) -> None:
    """Repro #21289 (review Hermes) : nom accentue + espaces, cite -> reconnu.

    Le tokenizer ASCII cassait `Createur de mail personnalise` en morceaux et
    rapportait a tort le carnet comme manquant.
    """
    series = tmp_path / "GenAI" / "SemanticKernel"
    series.mkdir(parents=True)
    (series / "Créateur de mail personnalisé.ipynb").write_text("{}", encoding="utf-8")
    notebooks = list_series_notebooks(Path("GenAI/SemanticKernel"), tmp_path)
    body = "Le carnet `Créateur de mail personnalisé` est livre sur main."
    assert analyse(body, notebooks) == []


def test_accent_fold_matches_both_directions(tmp_path: Path) -> None:
    """Body sans accents vs fichier accentue (et l'inverse) : meme carnet."""
    series = tmp_path / "GenAI" / "SemanticKernel"
    series.mkdir(parents=True)
    (series / "Créateur de mail personnalisé.ipynb").write_text("{}", encoding="utf-8")
    notebooks = list_series_notebooks(Path("GenAI/SemanticKernel"), tmp_path)
    assert analyse("Createur de mail personnalise est livre.", notebooks) == []

    plain = tmp_path / "Autre" / "Serie"
    plain.mkdir(parents=True)
    (plain / "Createur de mail personnalise.ipynb").write_text("{}", encoding="utf-8")
    notebooks2 = list_series_notebooks(Path("Autre/Serie"), tmp_path)
    assert analyse("Le carnet Créateur de mail personnalisé est livre.", notebooks2) == []


def test_expect_suppresses_with_reason(percolation: Path) -> None:
    """04-Lean planifie : exemption avec motif, sortie 0."""
    body_file = percolation / "body.txt"
    body_file.write_text(BODY_19494_ORIG + "\n03b et 03c cites aussi\nPercolation-03b-Critique-L128-L256 Percolation-03c-Critique-L512", encoding="utf-8")
    rc = main(
        [
            "--body-file", str(body_file),
            "--series", "Probas/Applications/Percolation",
            "--repo-root", str(percolation),
            "--expect", "Percolation-04-Sharpness-Lean=plan item 3, exploratoire",
        ]
    )
    assert rc == 0


def test_expect_without_reason_refused() -> None:
    with pytest.raises(SystemExit, match="sans motif"):
        parse_expect(["Percolation-04-Sharpness-Lean"])


def test_missing_series_is_unknown_not_red(tmp_path: Path) -> None:
    """Serie introuvable : infrastructure, jamais un rouge forge (#14849)."""
    body_file = tmp_path / "body.txt"
    body_file.write_text("x", encoding="utf-8")
    rc = main(
        [
            "--body-file", str(body_file),
            "--series", "Nulle/Part",
            "--repo-root", str(tmp_path),
        ]
    )
    assert rc == 0
