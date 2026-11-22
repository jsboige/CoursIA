"""Tests de l'organe de recit de fabrication (#27409).

L'organe compte, dans les **cellules markdown** des carnets, les marqueurs du
recit de fabrication. Ces tests verrouillent deux choses : le jeu de marqueurs
lui-meme (un marqueur absent fait sous-mesurer l'« avant »), et le fait que
seules les cellules markdown sont comptees.
"""
from __future__ import annotations

import importlib.util
import json
import sys
from pathlib import Path

MODULE_PATH = (
    Path(__file__).resolve().parents[1] / "check_production_narrative.py"
)
SPEC = importlib.util.spec_from_file_location("check_production_narrative", MODULE_PATH)
assert SPEC and SPEC.loader
organ = importlib.util.module_from_spec(SPEC)
sys.modules["check_production_narrative"] = organ
SPEC.loader.exec_module(organ)


def _nb(markdown: list[str], code: list[str] | None = None) -> dict:
    cells = [{"cell_type": "markdown", "source": [t]} for t in markdown]
    cells += [
        {"cell_type": "code", "source": [t], "execution_count": None, "outputs": []}
        for t in (code or [])
    ]
    return {"cells": cells, "metadata": {}, "nbformat": 4, "nbformat_minor": 5}


def _ecrire(tmp_path: Path, nb: dict) -> str:
    chemin = tmp_path / "carnet.ipynb"
    chemin.write_text(json.dumps(nb, ensure_ascii=False), encoding="utf-8")
    return str(chemin)


def test_les_deux_marqueurs_manquants_sont_dans_le_jeu_de_marqueurs() -> None:
    # Sans ces deux jetons, la mesure « avant » sous-compte de 3 marqueurs
    # reels : le verdict de revue et l'intertitre de production.
    assert "RECOVERABLE-USER-HAND" in organ.MARQUEURS
    assert "Cadre de production" in organ.MARQUEURS


def test_un_verdict_de_revue_et_un_intertitre_de_production_sont_comptes(
    tmp_path: Path,
) -> None:
    chemin = _ecrire(
        tmp_path,
        _nb(
            [
                "Verdict SOTA : `RECOVERABLE-USER-HAND`.",
                "**Cadre de production** : EPIC #4960, volet B.",
            ]
        ),
    )
    resultat = organ.mesure_fichier(chemin)
    assert resultat["total"] == 2
    assert resultat["marqueurs"]["RECOVERABLE-USER-HAND"] == 1
    assert resultat["marqueurs"]["Cadre de production"] == 1


def test_une_cellule_de_code_n_est_pas_comptée(tmp_path: Path) -> None:
    chemin = _ecrire(tmp_path, _nb([], ["# Cadre de production"]))
    assert organ.mesure_fichier(chemin)["total"] == 0


def test_les_renvois_pedagogiques_ne_sont_pas_comptes(tmp_path: Path) -> None:
    chemin = _ecrire(
        tmp_path,
        _nb(["regle #2161", "protocole #13309", "incident #1186 motive la mesure"]),
    )
    assert organ.mesure_fichier(chemin)["total"] == 0
