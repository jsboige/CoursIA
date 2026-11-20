# Tests du mode --realign-legacy de sync_csv_from_twin.py (#27148).
#
# Classe visee : CSV_ONLY_CONTENT portant l'anglais pre-francisation
# (text_en = titre court d'origine) alors que le jumeau porte la traduction
# complete relue. Le mode aligne explicitement depuis le jumeau, motif non
# vide exige et journalise (double verrou #10332 documente au docstring).
from __future__ import annotations

import csv
import importlib.util
import io
import json
import pathlib
import sys

import pytest

HERE = pathlib.Path(__file__).resolve().parent
SCRIPT = HERE.parent / "translation" / "sync_csv_from_twin.py"

_spec = importlib.util.spec_from_file_location("sync_csv_from_twin", SCRIPT)
sync = importlib.util.module_from_spec(_spec)
sys.modules["sync_csv_from_twin"] = sync
_spec.loader.exec_module(sync)

# text_en d'origine, d'avant la francisation du pivot (le cas #27148).
LEGACY_EN = "## Initial configuration"
# La traduction complete relue que porte le jumeau.
TWIN_EN = "## Initial configuration of the environment\n\nThis notebook loads the data and sets the random seed."
PIVOT_FR = "## Configuration initiale de l'environnement\n\nCe carnet charge les donnees et fixe la graine aleatoire."

FIELDS = ["notebook", "cell_id", "text", "hash", "src_hash",
          "text_en", "hash_en", "src_hash_en"]


def _write_notebook(path: pathlib.Path, text: str) -> None:
    path.write_text(json.dumps({
        "cells": [{"id": "cell-1", "cell_type": "markdown", "source": [text]}]
    }), encoding="utf-8")


def _write_csv(path: pathlib.Path, text_en: str) -> None:
    # Genere par DictWriter : garantit le round-trip byte-identique exigé par
    # _read_csv (rc 2 sinon).
    row = {"notebook": " serie/Notebook-Python.ipynb", "cell_id": "cell-1",
           "text": PIVOT_FR, "hash": "x" * 16, "src_hash": "y" * 16,
           "text_en": text_en, "hash_en": "z" * 16, "src_hash_en": "w" * 16}
    buf = io.StringIO()
    writer = csv.DictWriter(buf, fieldnames=FIELDS, lineterminator="\n")
    writer.writeheader()
    writer.writerow(row)
    path.write_bytes(buf.getvalue().encode("utf-8"))


@pytest.fixture()
def pair(tmp_path: pathlib.Path):
    csv_path = tmp_path / "serie.csv"
    # Le pivot vit dans serie/ : la ligne CSV (repo-relative) et le chemin
    # absolu passe en --pivot designent alors le MEME carnet. Le filtre
    # discriminant par chemin complet (#27148) exige cette correspondance.
    serie = tmp_path / "serie"
    serie.mkdir()
    pivot = serie / "Notebook-Python.ipynb"
    twin = serie / "Notebook-Python_en.ipynb"
    _write_csv(csv_path, LEGACY_EN)
    _write_notebook(pivot, PIVOT_FR)
    _write_notebook(twin, TWIN_EN)
    return csv_path, pivot, twin


def _argv(pair, *extra: str) -> list[str]:
    csv_path, pivot, twin = pair
    return ["--csv", str(csv_path), "--pivot", str(pivot),
            "--twin", str(twin), *extra]


def _rows(csv_path: pathlib.Path) -> list[dict[str, str]]:
    with csv_path.open(encoding="utf-8", newline="") as fh:
        return list(csv.DictReader(fh))


def test_default_mode_still_refuses_csv_only_content(pair, capsys):
    """Sans le mode, --apply ne desarme pas la garde : rien n'est ecrit."""
    csv_path, _, _ = pair
    before = csv_path.read_bytes()
    rc = sync.main(_argv(pair, "--apply"))
    assert rc == 1
    assert csv_path.read_bytes() == before
    assert "[CSV_ONLY_CONTENT] cell-1" in capsys.readouterr().out


def test_realign_legacy_aligns_csv_only_content(pair, capsys):
    """Avec motif + apply : ALIGNED_LEGACY, CSV ecrase depuis le jumeau."""
    csv_path, _, _ = pair
    rc = sync.main(_argv(pair, "--apply", "--realign-legacy",
                         "anglais pre-francisation, jumeau relu (#27148)"))
    assert rc == 0
    out = capsys.readouterr().out
    assert "[ALIGNED_LEGACY] cell-1" in out
    assert "remplace : '## Initial configuration'" in out
    assert "1 legacy" in out
    row = _rows(csv_path)[0]
    assert row["text_en"] == TWIN_EN
    assert row["hash_en"] == sync.cell_hash(TWIN_EN)
    assert row["src_hash"] == sync.cell_hash(PIVOT_FR)


def test_realign_legacy_reports_motif_in_json(pair, capsys):
    rc = sync.main(_argv(pair, "--apply", "--json", "--realign-legacy", "motif-audit"))
    assert rc == 0
    payload = json.loads(capsys.readouterr().out)
    assert payload["realign_legacy_motif"] == "motif-audit"
    assert payload["aligned_legacy"] == 1
    entry = payload["cells"][0]
    assert entry["verdict"] == "ALIGNED_LEGACY"
    assert entry["from"] == "CSV_ONLY_CONTENT"
    assert entry["replaced_preview"] == LEGACY_EN


def test_realign_legacy_requires_non_empty_motif(pair):
    csv_path, _, _ = pair
    before = csv_path.read_bytes()
    rc = sync.main(_argv(pair, "--apply", "--realign-legacy", "   "))
    assert rc == 2
    assert csv_path.read_bytes() == before


def test_realign_legacy_without_apply_writes_nothing(pair, capsys):
    """Constat seul : le mode sans --apply ne modifie pas le CSV."""
    csv_path, _, _ = pair
    before = csv_path.read_bytes()
    rc = sync.main(_argv(pair, "--realign-legacy", "constat"))
    assert rc == 1
    assert csv_path.read_bytes() == before


def test_realign_legacy_leaves_in_sync_untouched(pair):
    """Une ligne IN_SYNC n'est pas reecrite (round-trip identique)."""
    csv_path, _, _ = pair
    sync.main(_argv(pair, "--apply", "--realign-legacy", "passe 1"))
    after_first = csv_path.read_bytes()
    rc = sync.main(_argv(pair, "--apply", "--realign-legacy", "passe 2"))
    assert rc == 0
    assert csv_path.read_bytes() == after_first


def test_filter_never_matches_same_basename_sibling(tmp_path, capsys):
    """Regression #27148 : deux carnets distincts partageant le basename
    research.ipynb dans le meme CSV -- une paire pivot/jumeau ne reecrit
    QUE les lignes de son pivot. Le filtre historique par basename
    reecrivait aussi les lignes du carnet homonyme (cross-contamination
    mesuree sur partner-course.csv, c.7026312711)."""
    serie_a = tmp_path / "crypto"
    serie_b = tmp_path / "transitoire"
    serie_a.mkdir()
    serie_b.mkdir()
    pivot = serie_b / "research.ipynb"
    twin = serie_b / "research_en.ipynb"
    _write_notebook(pivot, PIVOT_FR)
    _write_notebook(twin, TWIN_EN)
    csv_path = tmp_path / "partner.csv"
    rows = []
    for nb, seed_letter in (("crypto/research.ipynb", "a"),
                            ("transitoire/research.ipynb", "e")):
        rows.append({"notebook": nb, "cell_id": "cell-1",
                     "text": PIVOT_FR, "hash": seed_letter * 16,
                     "src_hash": chr(ord(seed_letter) + 1) * 16,
                     "text_en": LEGACY_EN,
                     "hash_en": chr(ord(seed_letter) + 2) * 16,
                     "src_hash_en": chr(ord(seed_letter) + 3) * 16})
    buf = io.StringIO()
    writer = csv.DictWriter(buf, fieldnames=FIELDS, lineterminator="\n")
    writer.writeheader()
    writer.writerows(rows)
    csv_path.write_bytes(buf.getvalue().encode("utf-8"))

    rc = sync.main(["--csv", str(csv_path), "--pivot", str(pivot),
                    "--twin", str(twin), "--apply", "--realign-legacy",
                    "regression basename (#27148)"])
    assert rc == 0
    out = capsys.readouterr().out
    assert "[ALIGNED_LEGACY] cell-1" in out
    out_rows = {r["notebook"]: r for r in _rows(csv_path)}
    # La ligne du pivot est alignee depuis le jumeau...
    assert out_rows["transitoire/research.ipynb"]["text_en"] == TWIN_EN
    # ...celle du carnet homonyme est intacte (ancien filtre : reecrite aussi).
    assert out_rows["crypto/research.ipynb"]["text_en"] == LEGACY_EN
