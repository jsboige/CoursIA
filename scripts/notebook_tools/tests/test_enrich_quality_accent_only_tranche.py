"""Une tranche qui n'ajoute que des diacritiques n'est pas une reecriture.

``scan_survival`` (classe (b)) comptait la survie des lignes de base
**verbatim**. Or une tranche d'accentuation -- le travail de la ruling #16638
-- ne laisse subsister aucune ligne verbatim : la survie s'effondre, et
l'organe annonce « la base a ete reecrite » (MD_REWRITE, HIGH) sur un carnet
qui n'a change que ses diacritiques.

Mesure (2026-10-30, PR #23268, trois carnets de ``Search/Part3``) :
44 cellules markdown, **identiques sur squelette NFKD**, 0 differant au-dela
des diacritiques ; survie verbatim 9/44 (20 %) et 17/101 (17 %) -- exactement
les chiffres rendus par la CI ; survie sur squelette 100 %.

La classe (c) (``scan_diacritics``) mesure deja la perte d'accent, sur le
squelette : elle rend 0 finding sur cette tranche. Les deux classes ne
peuvent pas etre vraies ensemble -- d'ou la correction : la survie se mesure
sur le squelette (accents et ligatures indifférents), la casse reste
significative.

Ces tests pinnent l'invariant, avec leurs controles negatifs : une
reecriture genuine reste signalee (MD_REWRITE), une perte d'accent reste
signalee (DIACRITICS_LOSS).
"""

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from enrich_quality_ci import regressions  # noqa: E402
from scan_enrich_quality import scan_notebook  # noqa: E402

# Trois lignes substantielles sans diacritiques (base) et leur version
# accentuee (tete). Les deux versions sont le MEME squelette NFKD.
BASE_LINES = [
    "Le modele utilise une heuristique de recherche locale.",
    "Chaque noeud du graphe porte un cout associe.",
    "La resolution s'obtient par exploration en profondeur.",
]
HEAD_LINES = [
    "Le modèle utilise une heuristique de recherche locale.",
    "Chaque nœud du graphe porte un coût associé.",
    "La résolution s'obtient par exploration en profondeur.",
]

# Base accentuee, tete desaccentuee : la classe (c) doit toujours crier.
ACCENTED_LINES = [
    "Les résultats sont détaillés dans le modèle Final.",
    "La résolution cherchée reste válida pour chaque noeud.",
    "L'évaluation précise mène à une décision mesurable.",
]
DEACCENTED_LINES = [
    "Les resultats sont detailes dans le modele Final.",
    "La resolution cherchee reste valide pour chaque noeud.",
    "L'evaluation precise mene a une decision mesurable.",
]


def _md(text: str) -> dict:
    return {"cell_type": "markdown", "metadata": {}, "source": [text]}


def _write(path: Path, lines: list[str]) -> str:
    cells = [_md(t) for t in lines]
    path.write_text(json.dumps({"cells": cells, "metadata": {},
                                "nbformat": 4, "nbformat_minor": 5}),
                     encoding="utf-8")
    return str(path)


def _categories(base: str, head: str) -> list[str]:
    report = scan_notebook(Path(head), base=Path(base),
                            repo_root=Path(base).parent)
    return [f["category"] for f in report["findings"]]


@pytest.fixture
def accent_only(tmp_path):
    """La tete est la base accentuee -- rien d'autre n'a bouge."""
    base = _write(tmp_path / "base.ipynb", BASE_LINES)
    head = _write(tmp_path / "head.ipynb", HEAD_LINES)
    return base, head


def test_accent_only_tranche_is_not_a_regression(accent_only):
    """Le carnet n'a change que ses diacritiques : aucun finding neuf."""
    base, head = accent_only
    assert regressions(base, head, Path(base).parent) == []


def test_accent_only_tranche_raises_no_survival_finding(accent_only):
    """Ni MD_REWRITE ni MD_SURVIVAL_LOW sur une tranche d'accentuation."""
    base, head = accent_only
    categories = _categories(base, head)
    assert "MD_REWRITE" not in categories
    assert "MD_SURVIVAL_LOW" not in categories


def test_genuine_rewrite_still_raises_md_rewrite(tmp_path):
    """CONTROLE NEGATIF : une reecriture reelle reste signalee."""
    base = _write(tmp_path / "base.ipynb", BASE_LINES)
    head = _write(tmp_path / "head.ipynb", [
        "Un tout autre contenu remplace les phrases d'origine.",
        "Des idees nouvelles, sans aucun rapport avec la base.",
        "Le texte de tete ne reprend rien de ce que dit la base.",
    ])
    categories = _categories(base, head)
    assert "MD_REWRITE" in categories


def test_accent_removal_still_raises_diacritics_loss(tmp_path):
    """CONTROLE NEGATIF : la classe (c) reste audible apres la correction."""
    base = _write(tmp_path / "base.ipynb", ACCENTED_LINES)
    head = _write(tmp_path / "head.ipynb", DEACCENTED_LINES)
    categories = _categories(base, head)
    assert "DIACRITICS_LOSS" in categories


# Base ou la ligature est ecrite "oe", tete ou elle est ecrite "oe" : la
# ligature n'est pas un diacritique, et NFD ne la decompose pas. C'est le
# point qui distingue la normalisation NFKD employee ici d'une simple
# suppression des marques combinantes : sur ce jeu de lignes, la variante NFD
# ne voit AUCUNE ligne survivre et l'organe annonce MD_REWRITE sur un carnet
# qui n'a change que sa typographie.
LIGATURE_BASE_LINES = [
    "Le graphe contient un noeud racine et ses voisins.",
    "L'oeuvre complete demande une relecture attentive.",
    "La manoeuvre collective repose sur des efforts cumules.",
    "Le coeur du modele bat sur un noeud central.",
    "L'Oeuvre Collective explore une autre structure.",
]
LIGATURE_HEAD_LINES = [
    "Le graphe contient un nœud racine et ses voisins.",
    "L'œuvre complète demande une relecture attentive.",
    "La manœuvre collective repose sur des efforts cumulés.",
    "Le cœur du modèle bat sur un nœud central.",
    "L'Œuvre Collective explore une autre structure.",
]


def test_ligature_only_change_is_not_a_rewrite(tmp_path):
    """Une tranche qui change une ligature n'est pas une reecriture.

    CONTROLE NEGATIF IMPLICITE : ce test echoue sur une normalisation qui
    ne decompose que les diacritiques (NFD) -- les quatre lignes cessent
    alors de survivre et MD_REWRITE part sur un carnet qui n'a change que
    sa typographie.
    """
    base = _write(tmp_path / "base.ipynb", LIGATURE_BASE_LINES)
    head = _write(tmp_path / "head.ipynb", LIGATURE_HEAD_LINES)
    categories = _categories(base, head)
    assert "MD_REWRITE" not in categories
    assert "MD_SURVIVAL_LOW" not in categories


def test_ligature_only_change_is_not_a_regression(tmp_path):
    """Le meme jeu, passe par le point d'entree du gate : aucun finding."""
    base = _write(tmp_path / "base.ipynb", LIGATURE_BASE_LINES)
    head = _write(tmp_path / "head.ipynb", LIGATURE_HEAD_LINES)
    assert regressions(base, head, Path(base).parent) == []


def test_genuine_rewrite_with_ligature_is_still_flagged(tmp_path):
    """CONTROLE NEGATIF : le pli ne doit pas devenir un angle mort.

    Une reecriture reelle qui CONTIENT une ligature doit toujours etre
    signalee -- le repli des ligatures porte sur la typographie, pas sur le
    fond, et ne doit pas rendre une vraie reecriture invisible.
    """
    base = _write(tmp_path / "base.ipynb", LIGATURE_BASE_LINES)
    head = _write(tmp_path / "head.ipynb", [
        "Le cœur de l'oeuvre ne se laisse pas deviner ainsi.",
        "La manœuvre collective repose sur d'autres efforts.",
        "Un texte entierement neuf remplace les phrases de base.",
        "Le modèle bat sur un nœud tout autre.",
        "L'oeuvre Collective explore une autre structure.",
    ])
    categories = _categories(base, head)
    assert "MD_REWRITE" in categories
