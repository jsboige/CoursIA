"""Sorties ecrites par l'executeur QC-Py : flux conserves, y compris sur echec.

Deux defauts distincts sont couverts ici, tous deux mesures sur #22181 :

1. `_stream_output` decoupait le texte d'un flux sans garder ses fins de ligne
   (`text.split("\\n")`), ce qui recollait un rapport multiligne en une seule
   ligne (#21836, QC-Py-27) ;
2. la branche d'echec de `execute_notebook` ne construisait ses sorties
   qu'a partir des entrees `error` : un `timeout` n'en emet aucune, donc la
   cellule sortait avec un `execution_count` conserve et `outputs == []`,
   l'aspect exact d'une sortie effacee a la main (QC-Py-32, cellule de boucle
   DQN : 1337 -> 0 caracteres, reproduit aux defauts de 120 s puis de 900 s).
"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[3]))
# L'executeur importe `_papermill_meta` en voisin de fichier : son dossier doit
# etre sur le chemin quand pytest importe le module depuis la racine du depot.
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scripts.notebook_tools.execute_qcpy_docker import (  # noqa: E402
    _build_outputs,
    _stream_output,
)


def _result(streams=(), errors=(), result=None, display_data=()):
    return {
        "status": "ok",
        "streams": list(streams),
        "errors": list(errors),
        "result": result,
        "display_data": list(display_data),
    }


def test_stream_output_keeps_line_endings():
    out = _stream_output("ligne 1\nligne 2\n")
    assert out["output_type"] == "stream"
    assert out["text"] == ["ligne 1\n", "ligne 2\n"]


def test_timeout_keeps_streams_captured_before_interruption():
    """Le cas mesure : un timeout n'emet pas d'erreur, ses flux doivent rester."""
    res = _result(streams=["Entrainement DQN: 200 episodes\n", "Ep 20 | reward=-68.23\n"])
    res["status"] = "timeout"
    outs = _build_outputs(res, exec_count=8)
    assert len(outs) == 2
    assert "".join(outs[0]["text"]).startswith("Entrainement DQN")


def test_error_keeps_streams_and_error_entries():
    res = _result(
        streams=["avant l'exception\n"],
        errors=[{"ename": "ValueError", "evalue": "boom", "traceback": ["tb"]}],
    )
    outs = _build_outputs(res, exec_count=3)
    assert [o["output_type"] for o in outs] == ["stream", "error"]
    assert outs[1]["ename"] == "ValueError"


def test_success_includes_result_and_display_data():
    res = _result(
        streams=["ok\n"],
        result={"text/plain": ["42"]},
        display_data=[{"image/png": "aGVsbG8="}],
    )
    outs = _build_outputs(res, exec_count=1)
    assert [o["output_type"] for o in outs] == [
        "stream",
        "execute_result",
        "display_data",
    ]
    assert outs[1]["execution_count"] == 1
