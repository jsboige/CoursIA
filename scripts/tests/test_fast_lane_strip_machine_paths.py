"""Garde « bannière NuGet » de la voie rapide (#26932, tranche 51).

Le kernel .NET Interactive réinjecte à chaque exécution un message de
chargement d'extensions :

    Loading extensions from `<chemin absolu>/<paquet>/<version>/interactive-extensions/dotnet/<x>.dll`

C'est une fuite de type A (le chemin du cache NuGet de la machine). Tant que
seul le hook pre-commit la retirait, une lane sans hook laissait la classe
entrer sur `main` sans témoin.

Ces tests verrouillent le garde lui-même, pas l'organe : un garde déclaré
mais muet (mauvais chemin, mauvaise option, rc neutralisé) laisserait la
classe revenir sans que rien ne le dise.
"""
from __future__ import annotations

import json
import pathlib
import sys

REPO_ROOT = pathlib.Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT / "scripts" / "ci"))

import fast_lane  # noqa: E402
import fast_lane_registry  # noqa: E402

BANNER = (
    "Loading extensions from `/root/.nuget/packages/skiasharp/3.119.4/"
    "interactive-extensions/dotnet/SkiaSharp.DotNet.Interactive.dll`"
)

GARDE = fast_lane_registry.TRANCHE51[0]


def _carnet(tmp_path, texte: str) -> str:
    """Un carnet minimal portant une sortie `text/plain`."""
    chemin = tmp_path / "carnet.ipynb"
    chemin.write_text(json.dumps({
        "cells": [{
            "cell_type": "code",
            "execution_count": 1,
            "metadata": {},
            "source": ["1 + 1\n"],
            "outputs": [{
                "output_type": "stream",
                "name": "stdout",
                "text": [texte],
            }],
        }],
        "metadata": {},
        "nbformat": 4,
        "nbformat_minor": 5,
    }, ensure_ascii=False), encoding="utf-8")
    return str(chemin)


def test_le_garde_est_declare_bloquant_et_borne_aux_carnets():
    """Un garde non bloquant, ou borne au mauvais perimetre, ne protege rien."""
    assert GARDE.blocking is True, "le garde doit rougir la PR"
    assert GARDE.iterates_paths is True
    assert GARDE.iterate_paths == ["MyIA.AI.Notebooks/**/*.ipynb"]
    assert "--scan" in GARDE.argv and "--check" in GARDE.argv
    assert "{changed_paths}" in GARDE.argv, (
        "le placeholder est ce qui borne le garde au carnet touche")
    assert "scripts/notebook_tools/strip_machine_paths.py" in " ".join(GARDE.argv)


def test_un_carnet_qui_porte_la_banniere_le_fait_echouer(tmp_path):
    """Le cas nominal : la banniere doit faire rougir la PR."""
    rc, log = fast_lane.run_iter(
        GARDE.argv, [_carnet(tmp_path, BANNER)], {},
        warn_rc=GARDE.warn_rc)
    assert rc == 1, f"la banniere n'a pas ete vue :\n{log}"
    assert "leak line" in log


def test_un_carnet_propre_ne_le_fait_pas_echouer(tmp_path):
    """Un carnet sans chemin machine ne doit rien declencher."""
    rc, log = fast_lane.run_iter(
        GARDE.argv, [_carnet(tmp_path, "2\n")], {},
        warn_rc=GARDE.warn_rc)
    assert rc == 0, f"un carnet propre a declenche le garde :\n{log}"


def test_un_carnet_absent_ne_rougit_pas_la_pr(tmp_path):
    """Un carnet supprime par la PR ne peut pas rougir la PR.

    rc=2 de l'organe = chemin absent : il est neutre (warn_rc), comme pour
    tous les autres gardes iteratifs de la voie rapide.
    """
    rc, log = fast_lane.run_iter(
        GARDE.argv, [str(tmp_path / "absent.ipynb")], {},
        warn_rc=GARDE.warn_rc)
    assert rc == 0, f"un carnet absent a declenche le garde :\n{log}"


def test_le_garde_est_selectionne_par_un_carnet_modifie(monkeypatch):
    """Le garde doit etre declenche par le bon evenement : un carnet modifie."""
    change = ["MyIA.AI.Notebooks/Search/Part4-Metaheuristics/MGS-04-Islands.ipynb"]
    assert fast_lane.guard_applies(GARDE, change)
    assert not fast_lane.guard_applies(
        GARDE, ["docs/reference/procedures-recurrentes.md"])
