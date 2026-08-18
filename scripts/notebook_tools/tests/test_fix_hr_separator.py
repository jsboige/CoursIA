"""Tests de `fix_hr_separator` — chaque cas dangereux a son controle.

Le risque de cet outil n'est pas de rater une conversion (le notebook reste
simplement hors du render) mais d'en faire une de trop : convertir un
soulignement setext ou un vrai frontmatter changerait le rendu ou casserait
les metadonnees. Les tests sont donc majoritairement des controles NEGATIFS.
"""
import importlib.util
import json
import sys
from pathlib import Path

_SPEC = importlib.util.spec_from_file_location(
    "fix_hr_separator", Path(__file__).resolve().parents[1] / "fix_hr_separator.py"
)
fix = importlib.util.module_from_spec(_SPEC)
_SPEC.loader.exec_module(fix)


def conv(text, first=False):
    return fix.convert_cell(text, first)


def test_separateur_apres_ligne_vide_converti():
    src = "Du texte.\n\n---\n\nAutre texte."
    out, n = conv(src)
    assert n == 1
    assert "***" in out and "\n---\n" not in out


def test_separateur_en_tete_de_cellule_converti():
    src = "---\n\n## Titre\n\nProse."
    out, n = conv(src)
    assert n == 1
    assert out.startswith("***")


def test_soulignement_setext_non_touche():
    """`---` colle a du texte = titre H2, pas un separateur."""
    src = "Un titre de section\n---\n\nProse."
    out, n = conv(src)
    assert n == 0
    assert out == src


def test_bloc_de_code_non_touche():
    src = "Exemple :\n\n```yaml\n\n---\n\n```\n\nFin."
    out, n = conv(src)
    assert n == 0
    assert out == src


def test_vrai_frontmatter_de_tete_non_touche():
    src = '---\ntitle: "Mon notebook"\nauthor: Moi\n---\n'
    out, n = conv(src, first=True)
    assert n == 0
    assert out == src


def test_frontmatter_hors_premiere_cellule_est_converti():
    """Seule la PREMIERE cellule markdown peut porter un frontmatter legitime."""
    src = '---\ntitle: "pas un frontmatter ici"\n---\n'
    out, n = conv(src, first=False)
    assert n >= 1


def test_source_liste_reste_une_liste_avec_newlines():
    src = ["Du texte.\n", "\n", "---\n", "\n", "Suite."]
    out, n = conv(src)
    assert n == 1
    assert isinstance(out, list)
    assert "".join(out) == "Du texte.\n\n***\n\nSuite."


def test_plusieurs_separateurs_dans_une_cellule():
    src = "A\n\n---\n\nB\n\n---\n\nC"
    out, n = conv(src)
    assert n == 2
    assert out.count("***") == 2


def test_process_ecrit_et_reste_idempotent(tmp_path):
    nb = {
        "cells": [
            {"cell_type": "markdown", "source": "# Titre\n"},
            {"cell_type": "markdown", "source": "Prose.\n\n---\n\nSuite.\n"},
            {"cell_type": "code", "source": "x = 1\n", "outputs": [],
             "execution_count": 1, "metadata": {}},
        ],
        "metadata": {}, "nbformat": 4, "nbformat_minor": 5,
    }
    p = tmp_path / "n.ipynb"
    p.write_text(json.dumps(nb), encoding="utf-8")

    assert fix.process(p, apply=False) == 1          # detecte
    assert fix.process(p, apply=True) == 1           # convertit
    assert fix.process(p, apply=False) == 0          # idempotent
    after = json.loads(p.read_text(encoding="utf-8"))
    assert "***" in after["cells"][1]["source"]
    assert after["cells"][2]["source"] == "x = 1\n"  # code intact


def test_controle_positif_le_notebook_de_l_incident(tmp_path):
    """Controle POSITIF : la forme exacte qui a fait tomber le site #11451.

    Sans lui, un `0 a convertir` serait indiscernable d'un detecteur casse.
    """
    nb = {
        "cells": [
            {"cell_type": "markdown", "source": "# SL-8\n"},
            {"cell_type": "markdown",
             "source": "---\n\n## 3. Extraction des donnees\n\nAvant de miner.\n"},
            {"cell_type": "markdown",
             "source": "---\n\n### Interpretation : Extraction\n\nL'extraction convertit.\n"},
        ],
        "metadata": {}, "nbformat": 4, "nbformat_minor": 5,
    }
    p = tmp_path / "sl8.ipynb"
    p.write_text(json.dumps(nb), encoding="utf-8")
    assert fix.process(p, apply=False) == 2, (
        "controle positif ECHOUE : la forme de l'incident #11451 n'est pas "
        "detectee -> l'outil est casse, son 'rien a convertir' est sans valeur"
    )
