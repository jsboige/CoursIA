#!/usr/bin/env python3
"""Tests des deux organes de coherence jumeau introduits par la PR #21496.

``check_twin_widget_state.py`` — la resynchronisation T4 recopie les sorties du
carnet source dans le jumeau sans ``metadata.widgets`` : le jumeau affiche des
vues de widget dont le ``model_id`` n'existe pas dans son propre etat.

``sync_csv_from_twin.py`` — le CSV ``text_<lang>`` est la source de T4 ; quand
il porte l'ancien texte suivi du nouveau (concatenation), le re-rendu ecrirait
les deux versions bout a bout.

Couverture :
- widget : les trois verdicts (OK / DANGLING_FROM_SOURCE / DANGLING_UNRESOLVABLE)
  et l'effet de ``apply_source_state`` ;
- CSV : les cinq verdicts de ``classify`` et un aller-retour ``main()`` qui
  n'aligne QUE la cellule concatenee, en laissant intacte une cellule dont le
  CSV porte un contenu propre (``CSV_ONLY_CONTENT``).

stdlib + pytest, hermetique (fixtures dans ``tmp_path``, aucun reseau).
"""

from __future__ import annotations

import csv
import io
import json
import sys
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))

import check_twin_widget_state as widget  # noqa: E402
import sync_csv_from_twin as synccsv  # noqa: E402

VIEW = "application/vnd.jupyter.widget-view+json"
STATE = "application/vnd.jupyter.widget-state+json"


def make_nb(cells, models=None):
    """Carnet minimal : cellules (id, source, model_id de sortie) et etat widgets."""
    nb = {"cells": [], "metadata": {"kernelspec": {"name": "python3"}}, "nbformat": 4,
          "nbformat_minor": 5}
    for cid, source, model_id in cells:
        outputs = []
        if model_id is not None:
            outputs.append({"output_type": "display_data",
                            "data": {VIEW: {"model_id": model_id, "version_major": 2,
                                            "version_minor": 0}}})
        nb["cells"].append({"id": cid, "cell_type": "code", "source": [source],
                            "outputs": outputs, "execution_count": 1})
    if models is not None:
        nb["metadata"]["widgets"] = {
            STATE: {"version_major": 2, "version_minor": 0,
                    "state": {m: {"model_name": "x"} for m in models}}}
    return nb


# --------------------------------------------------------------------------
# check_twin_widget_state
# --------------------------------------------------------------------------

def test_verdict_ok_quand_chaque_reference_resout():
    nb = make_nb([("c1", "x", "m1")], models=["m1", "m2"])
    report = widget.analyse(nb, nb)
    assert report["verdict"] == "OK"
    assert report["dangling"] == []


def test_verdict_dangling_from_source_quand_l_etat_du_source_resout():
    source = make_nb([("c1", "x", "m1")], models=["m1"])
    twin = make_nb([("c1", "x", "m1")], models=["autre"])
    report = widget.analyse(source, twin)
    assert report["verdict"] == "DANGLING_FROM_SOURCE"
    assert report["resolvable_from_source"] == 1
    assert report["unresolvable"] == []
    assert report["orphan_models_in_twin"] == 1


def test_verdict_dangling_unresolvable_quand_aucun_etat_ne_resout():
    source = make_nb([("c1", "x", "m1")], models=["m1"])
    twin = make_nb([("c1", "x", "inconnu")], models=["autre"])
    report = widget.analyse(source, twin)
    assert report["verdict"] == "DANGLING_UNRESOLVABLE"
    assert len(report["unresolvable"]) == 1


def test_apply_source_state_rend_le_jumeau_coherent():
    source = make_nb([("c1", "x", "m1")], models=["m1"])
    twin = make_nb([("c1", "x", "m1")], models=["autre"])
    assert widget.apply_source_state(source, twin) is True
    assert widget.analyse(source, twin)["verdict"] == "OK"


def test_apply_refuse_quand_le_source_n_a_pas_d_etat():
    """Pas d'etat cote source : refus, et le jumeau reste intact (aucune ecriture)."""
    source = make_nb([("c1", "x", None)])
    twin = make_nb([("c1", "x", "m1")], models=["m1"])
    before = json.dumps(twin, sort_keys=True)
    assert widget.apply_source_state(source, twin) is False
    assert json.dumps(twin, sort_keys=True) == before
    # le jumeau se resout dans son propre etat : il n'a besoin d'aucun secours
    # du source, et le refus de recopie ne degrade donc rien
    assert widget.analyse(source, twin)["verdict"] == "OK"


def test_sortie_du_script_est_non_nulle_sur_dangling(tmp_path):
    source = tmp_path / "src.ipynb"
    twin = tmp_path / "twin.ipynb"
    source.write_text(json.dumps(make_nb([("c1", "x", "m1")], models=["m1"])),
                      encoding="utf-8")
    twin.write_text(json.dumps(make_nb([("c1", "x", "m1")], models=["autre"])),
                    encoding="utf-8")
    assert widget.main(["--source", str(source), "--twin", str(twin)]) == 1
    assert widget.main(["--source", str(source), "--twin", str(twin), "--apply"]) == 0
    assert widget.main(["--source", str(source), "--twin", str(twin)]) == 0


# --------------------------------------------------------------------------
# sync_csv_from_twin
# --------------------------------------------------------------------------

COLUMNS = ["notebook", "cell_id", "cell_type", "src_lang", "src_hash",
           "text_en", "hash_en", "src_hash_en"]


def write_csv(path, rows):
    buf = io.StringIO()
    writer = csv.DictWriter(buf, fieldnames=COLUMNS, lineterminator="\n")
    writer.writeheader()
    for row in rows:
        writer.writerow({k: row.get(k, "") for k in COLUMNS})
    path.write_bytes(buf.getvalue().encode("utf-8"))


def make_md_nb(cells):
    nb = {"cells": [], "metadata": {}, "nbformat": 4, "nbformat_minor": 5}
    for cid, source in cells:
        nb["cells"].append({"id": cid, "cell_type": "markdown", "source": [source],
                            "outputs": [], "execution_count": None})
    return nb


@pytest.mark.parametrize("csv_text,twin_text,expected", [
    ("Same text", "Same text", "IN_SYNC"),
    ("Old text\nNew text", "New text", "CONCATENATED"),
    ("Completely different", "New text", "CSV_ONLY_CONTENT"),
    ("", "New text", "CSV_EMPTY"),
    ("anything", "", "NO_TWIN_TEXT"),
])
def test_classify(csv_text, twin_text, expected):
    row = {"text_en": csv_text}
    assert synccsv.classify(row, twin_text, "en") == expected


def test_apply_n_aligne_que_la_cellule_concatenee(tmp_path):
    pivot_path = tmp_path / "serie.ipynb"
    twin_path = tmp_path / "serie_en.ipynb"
    csv_path = tmp_path / "serie.csv"

    pivot_path.write_text(json.dumps(make_md_nb([("c1", "Pivot un"), ("c2", "Pivot deux")])),
                          encoding="utf-8")
    twin_path.write_text(json.dumps(make_md_nb([("c1", "New one"), ("c2", "Twin two")])),
                         encoding="utf-8")
    write_csv(csv_path, [
        {"notebook": "MyIA.AI.Notebooks/Serie/serie.ipynb", "cell_id": "c1",
         "cell_type": "markdown", "src_lang": "fr", "src_hash": "0" * 16,
         "text_en": "Old one New one", "hash_en": "1" * 16},
        {"notebook": "MyIA.AI.Notebooks/Serie/serie.ipynb", "cell_id": "c2",
         "cell_type": "markdown", "src_lang": "fr", "src_hash": "2" * 16,
         "text_en": "Un contenu propre au CSV", "hash_en": "3" * 16},
    ])
    before = csv_path.read_bytes()

    rc = synccsv.main(["--csv", str(csv_path), "--pivot", str(pivot_path),
                       "--twin", str(twin_path), "--apply"])
    assert rc == 1, "la cellule CSV_ONLY_CONTENT reste hors phase : rc doit etre 1"

    rows = {r["cell_id"]: r for r in csv.DictReader(io.StringIO(csv_path.read_text(encoding="utf-8")))}
    assert rows["c1"]["text_en"] == "New one"
    assert rows["c1"]["hash_en"] == synccsv.cell_hash("New one")
    assert rows["c1"]["src_hash"] == synccsv.cell_hash("Pivot un")
    assert rows["c2"]["text_en"] == "Un contenu propre au CSV", "CSV_ONLY_CONTENT ne s'ecrit pas"
    assert rows["c2"]["hash_en"] == "3" * 16
    assert before != csv_path.read_bytes()


def test_mode_constat_n_ecrit_pas(tmp_path):
    pivot_path = tmp_path / "s.ipynb"
    twin_path = tmp_path / "s_en.ipynb"
    csv_path = tmp_path / "s.csv"
    pivot_path.write_text(json.dumps(make_md_nb([("c1", "P")])), encoding="utf-8")
    twin_path.write_text(json.dumps(make_md_nb([("c1", "N")])), encoding="utf-8")
    write_csv(csv_path, [{"notebook": "x/s.ipynb", "cell_id": "c1", "cell_type": "markdown",
                          "text_en": "Ancien N", "hash_en": "0" * 16}])
    before = csv_path.read_bytes()
    assert synccsv.main(["--csv", str(csv_path), "--pivot", str(pivot_path),
                         "--twin", str(twin_path)]) == 1
    assert csv_path.read_bytes() == before


def test_round_trip_refuse_un_csv_non_byte_identique(tmp_path):
    pivot_path = tmp_path / "s.ipynb"
    twin_path = tmp_path / "s_en.ipynb"
    csv_path = tmp_path / "s.csv"
    pivot_path.write_text(json.dumps(make_md_nb([("c1", "P")])), encoding="utf-8")
    twin_path.write_text(json.dumps(make_md_nb([("c1", "N")])), encoding="utf-8")
    # CRLF : le round-trip doit rester byte-identique, donc l'ecriture est permise
    buf = io.StringIO()
    writer = csv.DictWriter(buf, fieldnames=COLUMNS, lineterminator="\r\n")
    writer.writeheader()
    writer.writerow({"notebook": "x/s.ipynb", "cell_id": "c1", "cell_type": "markdown",
                     "text_en": "Ancien N", "hash_en": "0" * 16})
    csv_path.write_bytes(buf.getvalue().encode("utf-8"))
    rc = synccsv.main(["--csv", str(csv_path), "--pivot", str(pivot_path),
                       "--twin", str(twin_path), "--apply"])
    assert rc == 0
    assert b"\r\n" in csv_path.read_bytes(), "le terminateur d'origine est preserve"
