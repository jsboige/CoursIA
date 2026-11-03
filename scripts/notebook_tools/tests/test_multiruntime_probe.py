"""Tests for scripts/notebook_tools/multiruntime_probe.py — multi-runtime probe.

L'organe execute une cellule de carnet sous plusieurs runtimes .NET et compare
les mesures. Ces tests pinning sa logique PURE, sans kernel et sans runtime :
la lecture de la cellule cible, l'extraction des mesures dans la sortie, et le
verdict de comparaison.

Aucun kernel vivant, aucun reseau, aucun runtime .NET : rapide et deterministe.
"""
import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import multiruntime_probe as probe  # noqa: E402


# --- fixtures ---------------------------------------------------------------

BLOC_FR = """=== La famine, mesuree (5 runs par configuration) ===

[A] ExecuteSynchronously, SANS RunContinuationsAsynchronously
    runs     = [171,09, 206,23, 153,49, 181,81, 137,07] ms
    mediane  = 171,09 ms
    min/max  = 137,07 / 206,23 ms

[A] ExecuteSynchronously, SANS RunContinuationsAsynchronously -- threads natif/reprise
    [31/31, 33/33, 35/35, 37/37, 39/39]
    -> identiques : la reprise s'execute en ligne sur le thread natif.

[B] ExecuteSynchronously, AVEC RunContinuationsAsynchronously
    runs     = [1,83, 0,03, 0,03, 0,03, 0,04] ms
    mediane  = 0,03 ms
    min/max  = 0,03 / 1,83 ms
"""


def _write_nb(path: Path, cells):
    path.write_text(json.dumps({"cells": cells, "metadata": {}}), encoding="utf-8")
    return path


def _code_cell(source):
    src = source if isinstance(source, list) else [source]
    return {"cell_type": "code", "source": src, "execution_count": None, "outputs": []}


# --- extraction des mesures -------------------------------------------------

def test_parse_block_extrait_les_series_fr():
    """La culture FR (virgule decimale) ne doit pas casser le decoupage."""
    blocs = probe.parse_block(BLOC_FR)
    assert set(blocs) == {"A", "B"}
    assert blocs["A"]["runs"] == [171.09, 206.23, 153.49, 181.81, 137.07]
    assert blocs["A"]["median"] == pytest.approx(171.09)
    assert blocs["A"]["min"] == pytest.approx(137.07)
    assert blocs["A"]["max"] == pytest.approx(206.23)
    assert blocs["A"]["mechanism"] == "identiques"
    assert blocs["A"]["threads"] == ["31/31", "33/33", "35/35", "37/37", "39/39"]


def test_parse_block_accepte_la_culture_en():
    """Un kernel rendu en culture EN donne des points : la meme extraction."""
    en = BLOC_FR.replace("171,09", "171.09").replace("206,23", "206.23")
    blocs = probe.parse_block(en)
    assert blocs["A"]["runs"][0] == pytest.approx(171.09)
    assert blocs["A"]["runs"][1] == pytest.approx(206.23)


def test_parse_provenance_lit_la_preuve_de_runtime():
    preuve = ("RUNTIME_DESCRIPTION .NET 11.0.0-rc.3.26522.148\n"
              "RUNTIME_VERSION 11.0.0\n"
              "RUNTIME_DIR C:\\Users\\x\\.dotnet-r11\\shared\\Microsoft.NETCore.App\\11.0.0-rc.3\n")
    parsed = probe.parse_provenance(preuve)
    assert parsed["description"] == ".NET 11.0.0-rc.3.26522.148"
    assert parsed["version"] == "11.0.0"
    assert "dotnet-r11" in parsed["dir"]


# --- verdict ----------------------------------------------------------------

def _mesure(median, min_, max_):
    return {"median": median, "min": min_, "max": max_}


def test_verdict_delta_etabli_si_les_intervalles_sont_disjoints():
    verdict, delta = probe.verdict_for(
        "A", _mesure(100.0, 90.0, 110.0), _mesure(80.0, 70.0, 85.0))
    assert verdict == "DELTA ETABLI"
    assert delta == pytest.approx(-20.0)


def test_verdict_inconclusif_si_les_intervalles_se_chevauchent():
    verdict, delta = probe.verdict_for(
        "A", _mesure(100.0, 77.64, 82.02), _mesure(76.72, 71.37, 91.67))
    assert verdict.startswith("INCONCLUSIF")
    assert delta == pytest.approx(-23.28, abs=0.01)


def test_verdict_non_resolu_sous_le_plancher_de_resolution():
    """Une grandeur sub-milliseconde n'est pas comparable : le bruit decide."""
    verdict, _ = probe.verdict_for(
        "B", _mesure(0.02, 0.01, 0.03), _mesure(0.01, 0.01, 0.02))
    assert verdict.startswith("NON RESOLU")


def test_verdict_measure_absente():
    verdict, delta = probe.verdict_for("A", None, _mesure(1.0, 1.0, 1.0))
    assert verdict.startswith("INCONCLUSIF")
    assert delta is None


# --- lecture du carnet ------------------------------------------------------

def test_read_cell_source_et_ne_modifie_rien(tmp_path):
    """L'organe LIT la cellule : le carnet du depot reste byte-identique."""
    nb = _write_nb(tmp_path / "nb.ipynb", [
        {"cell_type": "markdown", "source": ["titre"]},
        _code_cell("Console.WriteLine(1);"),
    ])
    avant = nb.read_bytes()
    source = probe.read_cell_source(str(nb), 1, None)
    assert source == "Console.WriteLine(1);"
    assert nb.read_bytes() == avant


def test_read_cell_source_par_id(tmp_path):
    nb = _write_nb(tmp_path / "nb.ipynb", [
        {"cell_type": "code", "id": "abc", "source": ["Console.WriteLine(2);"]},
    ])
    assert probe.read_cell_source(str(nb), None, "abc") == "Console.WriteLine(2);"


def test_read_cell_source_cellule_introuvable(tmp_path):
    nb = _write_nb(tmp_path / "nb.ipynb", [_code_cell("Console.WriteLine(3);")])
    with pytest.raises(SystemExit):
        probe.read_cell_source(str(nb), 7, None)
