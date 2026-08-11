"""Tests for #10329 etapes 2-5 -- mode --full et detection hors-perimetre.

Plan #10329 (5 etapes) -- cette PR livre les etapes 2, 4, 5 :

  - Etape 2 : extract_cells_to_csv.py --full (mode plein perimetre, rafraichit
    TOUTES les lignes du CSV en --update, pas seulement les notebooks en input).
  - Etape 4 : translation-sync.yml workflow_dispatch input mode=full|incremental.
  - Etape 5 : check_translation_sync.py --report-out-of-scope detecte les
    notebooks FR jamais reference dans aucun CSV.

Garde-fou : ces tests hermetiques (stdlib + tmp_path) pinning le contrat pour
que toute regression de l'un des 3 modes soit attrapee en CI avant merge.

Mirrors the style of test_translation_sync_t4_scope.py (c.200 PR #10364) and
test_translation_full_mode TDD principle : on teste les 3 invariants
independamment plutot que le run complet.

Source unique de verite :
- extract_cells_to_csv.py (T1, mode --update + --full)
- check_translation_sync.py (T2, mode --report-out-of-scope)
- check_perimeter.py (matrice perimetre, #10109)
"""
from __future__ import annotations

import csv
import json
import shutil
import sys
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
TRANSLATION_DIR = HERE.parent
sys.path.insert(0, str(TRANSLATION_DIR))

import check_perimeter as p  # noqa: E402
import check_translation_sync as cts  # noqa: E402
import extract_cells_to_csv as e  # noqa: E402


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------


def _make_notebook(
    path: Path,
    cell_id: str,
    text_fr: str = "## Titre",
    cell_type: str = "markdown",
) -> None:
    """Ecrit un notebook .ipynb minimaliste (1 cellule) a ``path``.

    Le schema respecte nbformat 4 : ``cells`` est une liste de dicts avec
    ``cell_type``, ``id``, ``metadata``, ``source`` (list[str]) et ``execution_count``.
    Le notebook n'est pas executable (kernel absent) -- suffisant pour T1
    qui ne fait que parser le JSON.
    """
    path.parent.mkdir(parents=True, exist_ok=True)
    nb = {
        "cells": [
            {
                "cell_type": cell_type,
                "id": cell_id,
                "metadata": {},
                "source": [text_fr],
                "execution_count": None,
                "outputs": [],
            }
        ],
        "metadata": {
            "kernelspec": {"display_name": "Python 3", "language": "python", "name": "python3"},
            "language_info": {"name": "python"},
        },
        "nbformat": 4,
        "nbformat_minor": 5,
    }
    path.write_text(json.dumps(nb, ensure_ascii=False), encoding="utf-8")


def _make_csv(path: Path, header: list[str], rows: list[dict]) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8", newline="") as f:
        w = csv.DictWriter(f, fieldnames=header, lineterminator="\n")
        w.writeheader()
        for row in rows:
            # Force POSIX paths sur toutes les colonnes (les scripts de prod
            # retournent des paths POSIX via as_posix() ; on doit matcher).
            row = {k: (v.replace("\\", "/") if isinstance(v, str) else v) for k, v in row.items()}
            w.writerow(row)
    return path


PIVOT_HEADER = [
    "notebook", "cell_id", "cell_type", "src_lang", "src_hash", "text_fr", "hash_fr",
]


# ---------------------------------------------------------------------------
# Etape 2 -- mode --full (extract_cells_to_csv.py)
# ---------------------------------------------------------------------------


def test_full_mode_refreshes_existing_rows(tmp_path, monkeypatch):
    """Mode --full + --update rafraichit TOUTES les lignes du CSV, pas
    seulement celles des notebooks passes en input.

    Invariant : src_hash est mis a jour pour toutes les lignes existantes,
    meme si on ne passe aucun notebook en input (le scan large couvre les
    repertoires series).
    """
    # 2 notebooks FR dans la serie.
    nb_a = tmp_path / "series" / "A.ipynb"
    nb_b = tmp_path / "series" / "B.ipynb"
    _make_notebook(nb_a, "cellA1", text_fr="## A")
    _make_notebook(nb_b, "cellB1", text_fr="## B")

    # CSV existant : les 2 notebooks sont references, AVEC un faux src_hash
    # (sha256 bidon) qui ne match pas le notebook reel.
    csv_path = _make_csv(
        tmp_path / "synced.csv",
        PIVOT_HEADER,
        [
            {"notebook": str(nb_a.relative_to(tmp_path)), "cell_id": "cellA1",
             "cell_type": "markdown", "src_lang": "fr", "src_hash": "STALE_HASH_A",
             "text_fr": "## A", "hash_fr": "STALE_FR_HASH_A"},
            {"notebook": str(nb_b.relative_to(tmp_path)), "cell_id": "cellB1",
             "cell_type": "markdown", "src_lang": "fr", "src_hash": "STALE_HASH_B",
             "text_fr": "## B", "hash_fr": "STALE_FR_HASH_B"},
        ],
    )

    # On lance --update --full SANS input notebooks specifiques -- le mode full
    # doit quand meme rafraichir les 2 lignes existantes (en lisant le CSV,
    # en determinant le repertoire de serie depuis les chemins notebook,
    # puis en iterant recursivement).
    monkeypatch.setattr(sys, "argv", [
        "extract_cells_to_csv.py",
        "--repo-root", str(tmp_path),
        str(tmp_path),                  # input = racine tmp_path
        "--update", str(csv_path),
        "--full",
    ])
    rc = e.main()
    assert rc == 0, f"main returned {rc}"

    # Lecture post-run : src_hash doit avoir ete recalcule.
    with csv_path.open(encoding="utf-8") as f:
        rows = list(csv.DictReader(f))
    assert len(rows) == 2
    hashes = {r["notebook"]: r["src_hash"] for r in rows}
    assert hashes[nb_a.relative_to(tmp_path).as_posix()] != "STALE_HASH_A", (
        "mode --full aurait du rafraichir le src_hash de A"
    )
    assert hashes[nb_b.relative_to(tmp_path).as_posix()] != "STALE_HASH_B", (
        "mode --full aurait du rafraichir le src_hash de B"
    )


def test_full_mode_appends_new_notebooks_in_scope(tmp_path, monkeypatch):
    """Mode --full + --update detecte les notebooks FR NOUVEAUX dans le
    repertoire de serie (jamaient references dans le CSV) et les append.

    C'est le scenario fondateur de #10329 : un notebook FR cree sans qu'un
    run incremental ne l'ait vu passer (PR mergee sans trigger push, ou
    notebook dans une serie sans CSV dedie). Le mode --full le rattrape.
    """
    # CSV existant : 1 notebook.
    nb_old = tmp_path / "series" / "Old.ipynb"
    _make_notebook(nb_old, "cellOld", text_fr="## Old")
    csv_path = _make_csv(
        tmp_path / "synced.csv",
        PIVOT_HEADER,
        [
            {"notebook": str(nb_old.relative_to(tmp_path)), "cell_id": "cellOld",
             "cell_type": "markdown", "src_lang": "fr",
             "src_hash": "STALE_HASH", "text_fr": "## Old", "hash_fr": "STALE_FR"},
        ],
    )

    # NOUVEAU notebook FR cree dans la meme serie (meme parent dir).
    nb_new = tmp_path / "series" / "New.ipynb"
    _make_notebook(nb_new, "cellNew", text_fr="## New")

    monkeypatch.setattr(sys, "argv", [
        "extract_cells_to_csv.py",
        "--repo-root", str(tmp_path),
        str(tmp_path),
        "--update", str(csv_path),
        "--full",
    ])
    rc = e.main()
    assert rc == 0

    with csv_path.open(encoding="utf-8") as f:
        rows = list(csv.DictReader(f))

    notebooks = {r["notebook"] for r in rows}
    assert nb_new.relative_to(tmp_path).as_posix() in notebooks, (
        f"mode --full aurait du append New.ipynb dans le CSV ; "
        f"got notebooks={notebooks}"
    )


def test_incremental_mode_does_not_refresh_unrelated_rows(tmp_path, monkeypatch):
    """Mode incremental (sans --full) NE rafraichit QUE les lignes des
    notebooks passes en input. Les autres lignes du CSV restent intactes.

    C'est l'inverse du test_full_mode_refreshes_existing_rows : le mode
    historique (post-#4957) doit preserver son comportement.
    """
    nb_a = tmp_path / "series" / "A.ipynb"
    nb_b = tmp_path / "series" / "B.ipynb"
    _make_notebook(nb_a, "cellA1", text_fr="## A")
    _make_notebook(nb_b, "cellB1", text_fr="## B")
    csv_path = _make_csv(
        tmp_path / "synced.csv",
        PIVOT_HEADER,
        [
            {"notebook": str(nb_a.relative_to(tmp_path)), "cell_id": "cellA1",
             "cell_type": "markdown", "src_lang": "fr", "src_hash": "STALE_A",
             "text_fr": "## A", "hash_fr": "FR_A"},
            {"notebook": str(nb_b.relative_to(tmp_path)), "cell_id": "cellB1",
             "cell_type": "markdown", "src_lang": "fr", "src_hash": "STALE_B",
             "text_fr": "## B", "hash_fr": "FR_B"},
        ],
    )
    # Input = seulement A. B ne doit PAS etre rafraichi.
    monkeypatch.setattr(sys, "argv", [
        "extract_cells_to_csv.py",
        str(nb_a),
        "--update", str(csv_path),
        "--repo-root", str(tmp_path),
    ])
    rc = e.main()
    assert rc == 0

    with csv_path.open(encoding="utf-8") as f:
        rows = list(csv.DictReader(f))
    by_nb = {r["notebook"]: r for r in rows}
    assert by_nb[nb_a.relative_to(tmp_path).as_posix()]["src_hash"] != "STALE_A"
    assert by_nb[nb_b.relative_to(tmp_path).as_posix()]["src_hash"] == "STALE_B", (
        "mode incremental aurait du laisser B intact (input = A seulement)"
    )


# ---------------------------------------------------------------------------
# Etape 5 -- detection hors-perimetre (check_translation_sync.py)
# ---------------------------------------------------------------------------


def test_find_out_of_scope_returns_notebooks_not_in_any_csv(tmp_path):
    """Un notebook FR dans MyIA.AI.Notebooks/ qui n'est reference dans
    aucun CSV apparait dans la liste MISSING_FROM_COV."""
    # 2 notebooks FR.
    nb_known = tmp_path / "series" / "Known.ipynb"
    nb_unknown = tmp_path / "series" / "Unknown.ipynb"
    _make_notebook(nb_known, "k1", text_fr="## Known")
    _make_notebook(nb_unknown, "u1", text_fr="## Unknown")

    # Set des notebooks connus (1 seul, pas Unknown). Force POSIX pour
    # matcher le format retourne par find_out_of_scope_notebooks.
    known = {nb_known.relative_to(tmp_path).as_posix()}

    out = cts.find_out_of_scope_notebooks(tmp_path, known)
    rel_paths = {d["notebook"] for d in out}
    assert nb_unknown.relative_to(tmp_path).as_posix() in rel_paths
    assert nb_known.relative_to(tmp_path).as_posix() not in rel_paths
    assert all(d["verdict"] == "MISSING_FROM_CSV" for d in out)


def test_find_out_of_scope_excludes_translated_notebooks(tmp_path):
    """Les notebooks *_<lang>.ipynb (traduits) ne sont JAMAIS signales
    MISSING_FROM_COV -- c'est aux notebooks FR pivots que s'applique
    la detection."""
    # 1 FR pivot + 1 EN traduit.
    nb_fr = tmp_path / "series" / "Foo.ipynb"
    nb_en = tmp_path / "series" / "Foo_en.ipynb"
    _make_notebook(nb_fr, "f1", text_fr="## Foo FR")
    _make_notebook(nb_en, "f1", text_fr="## Foo EN")

    out = cts.find_out_of_scope_notebooks(tmp_path, known_notebooks=set())
    rel_paths = {d["notebook"] for d in out}
    assert nb_fr.relative_to(tmp_path).as_posix() in rel_paths
    assert nb_en.relative_to(tmp_path).as_posix() not in rel_paths, (
        "Foo_en.ipynb ne doit PAS etre signale MISSING_FROM_COV"
    )


def test_find_out_of_scope_excludes_output_and_agent(tmp_path):
    """Les notebooks _output.ipynb / _agent.ipynb sont ignores (cf
    iter_notebooks() d'extract_cells_to_csv.py)."""
    nb_out = tmp_path / "series" / "Foo_output.ipynb"
    nb_agent = tmp_path / "series" / "Foo_agent.ipynb"
    _make_notebook(nb_out, "x", text_fr="x")
    _make_notebook(nb_agent, "y", text_fr="y")

    out = cts.find_out_of_scope_notebooks(tmp_path, known_notebooks=set())
    rel_paths = {d["notebook"] for d in out}
    assert str(nb_out.relative_to(tmp_path)) not in rel_paths
    assert str(nb_agent.relative_to(tmp_path)) not in rel_paths


def test_report_out_of_scope_in_main_output(tmp_path, capsys, monkeypatch):
    """Le flag --report-out-of-scope ajoute une cle 'out_of_scope' + 'out_of_scope_count'
    au rapport JSON stdout."""
    # 1 notebook orphelin.
    nb = tmp_path / "Orphan.ipynb"
    _make_notebook(nb, "o1", text_fr="## Orphan")
    nb_rel = str(nb.relative_to(tmp_path))

    # CSV vide (mais existant) sous tmp_path/translations/.
    csv_path = _make_csv(
        tmp_path / "synced.csv",
        PIVOT_HEADER,
        [],
    )
    (tmp_path / "translations").mkdir(exist_ok=True)
    shutil.copy(csv_path, tmp_path / "translations" / "synced.csv")

    # On appelle main() avec --report-out-of-scope + --notebooks-root.
    monkeypatch.chdir(tmp_path)
    monkeypatch.setattr(sys, "argv", [
        "check_translation_sync.py",
        str(tmp_path / "translations"),
        "--check",
        "--report-out-of-scope",
        "--notebooks-root", str(tmp_path),
        "--repo-root", str(tmp_path),
    ])
    rc = cts.main()
    # --check => exit 0 meme si anomalies (MISSING_FROM_CSV est non-bloquant).
    assert rc == 0

    captured = capsys.readouterr()
    report = json.loads(captured.out)
    assert "out_of_scope" in report
    assert "out_of_scope_count" in report
    assert report["out_of_scope_count"] >= 1
    assert nb_rel in {d["notebook"] for d in report["out_of_scope"]}


# ---------------------------------------------------------------------------
# Garde-fou integration -- le mode full ne casse PAS le run incremental
# ---------------------------------------------------------------------------


def test_full_and_incremental_yield_consistent_results(tmp_path, monkeypatch):
    """Garde-fou : un CSV apres run incremental (sur 1 notebook) puis run
    --full (sans input notebook specifique) doit aboutir au meme src_hash
    que si on avait lance directement --full.

    Evite qu'un round-trip incremental -> full corrompe les donnees.
    """
    nb = tmp_path / "series" / "Only.ipynb"
    _make_notebook(nb, "only1", text_fr="## Only")
    csv_path = _make_csv(
        tmp_path / "synced.csv",
        PIVOT_HEADER,
        [
            {"notebook": str(nb.relative_to(tmp_path)), "cell_id": "only1",
             "cell_type": "markdown", "src_lang": "fr", "src_hash": "STALE",
             "text_fr": "## Only", "hash_fr": "STALE_FR"},
        ],
    )
    monkeypatch.setattr(sys, "argv", [
        "extract_cells_to_csv.py",
        "--repo-root", str(tmp_path),
        str(nb), "--update", str(csv_path),
    ])
    rc = e.main()
    assert rc == 0
    with csv_path.open(encoding="utf-8") as f:
        rows_after_incr = list(csv.DictReader(f))
    hash_after_incr = rows_after_incr[0]["src_hash"]

    # Reset le CSV, on relance en --full direct.
    csv_path2 = _make_csv(
        tmp_path / "synced2.csv",
        PIVOT_HEADER,
        [
            {"notebook": str(nb.relative_to(tmp_path)), "cell_id": "only1",
             "cell_type": "markdown", "src_lang": "fr", "src_hash": "STALE",
             "text_fr": "## Only", "hash_fr": "STALE_FR"},
        ],
    )
    monkeypatch.setattr(sys, "argv", [
        "extract_cells_to_csv.py",
        "--repo-root", str(tmp_path),
        str(tmp_path), "--update", str(csv_path2), "--full",
    ])
    rc = e.main()
    assert rc == 0
    with csv_path2.open(encoding="utf-8") as f:
        rows_after_full = list(csv.DictReader(f))
    hash_after_full = rows_after_full[0]["src_hash"]

    assert hash_after_incr == hash_after_full, (
        f"incoherence : incremental={hash_after_incr} vs full={hash_after_full}"
    )


if __name__ == "__main__":
    pytest.main([__file__, "-v"])