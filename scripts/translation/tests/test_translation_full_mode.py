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


def test_full_mode_does_not_absorb_notebooks_outside_series(tmp_path, monkeypatch):
    """#21514 : un input CLI large ne doit PAS faire absorber au CSV les
    carnets d'une autre serie.

    La borne de scan du mode --full est le repertoire de serie derive des
    lignes du CSV ; l'input CLI n'est qu'un repli quand aucune borne n'est
    derivable. Mesure fondatrice : `--update <csv> --full` avec
    "MyIA.AI.Notebooks" faisait passer compression.csv de 31 a 49 978 lignes.
    """
    nb_in = tmp_path / "series" / "In.ipynb"
    nb_out = tmp_path / "other-series" / "Out.ipynb"
    _make_notebook(nb_in, "in1", text_fr="## In")
    _make_notebook(nb_out, "out1", text_fr="## Out")

    csv_path = _make_csv(
        tmp_path / "synced.csv",
        PIVOT_HEADER,
        [
            {"notebook": nb_in.relative_to(tmp_path).as_posix(), "cell_id": "in1",
             "cell_type": "markdown", "src_lang": "fr", "src_hash": "STALE_IN",
             "text_fr": "## In", "hash_fr": "FR_IN"},
        ],
    )

    # Input = la RACINE qui contient les deux series (forme que le workflow
    # T1_MODE=full passait reellement : "MyIA.AI.Notebooks").
    monkeypatch.setattr(sys, "argv", [
        "extract_cells_to_csv.py",
        "--repo-root", str(tmp_path),
        str(tmp_path),
        "--update", str(csv_path),
        "--full",
    ])
    assert e.main() == 0

    with csv_path.open(encoding="utf-8") as f:
        rows = list(csv.DictReader(f))
    notebooks = {r["notebook"] for r in rows}
    assert notebooks == {nb_in.relative_to(tmp_path).as_posix()}, (
        f"le mode --full ne doit appender que les carnets de la serie du CSV ; "
        f"got notebooks={notebooks}"
    )
    assert rows[0]["src_hash"] != "STALE_IN", "la ligne de la serie doit rester rafraichie"


def test_full_mode_falls_back_to_cli_input_without_derivable_bound(tmp_path, monkeypatch):
    """#21518 reserve 3 : sans borne derivable du CSV, l'input CLI reste la
    racine de scan (garantie de non-regression du repli).

    Toutes les lignes du CSV pointent un notebook a la RACINE du depot
    (chemin sans separateur, donc ``len(parts) < 2``) : aucun repertoire de
    serie n'est derivable. L'input CLI doit alors etre honore exactement
    comme avant #21514 (scan recursif plein perimetre).
    """
    nb_root = tmp_path / "Root.ipynb"
    _make_notebook(nb_root, "root1", text_fr="## Root")
    nb_new = tmp_path / "fresh" / "Fresh.ipynb"
    _make_notebook(nb_new, "fresh1", text_fr="## Fresh")

    csv_path = _make_csv(
        tmp_path / "synced.csv",
        PIVOT_HEADER,
        [
            {"notebook": nb_root.name, "cell_id": "root1",
             "cell_type": "markdown", "src_lang": "fr", "src_hash": "STALE_ROOT",
             "text_fr": "## Root", "hash_fr": "FR_ROOT"},
        ],
    )

    monkeypatch.setattr(sys, "argv", [
        "extract_cells_to_csv.py",
        "--repo-root", str(tmp_path),
        str(tmp_path),                  # input = seule racine disponible
        "--update", str(csv_path),
        "--full",
    ])
    assert e.main() == 0

    with csv_path.open(encoding="utf-8") as f:
        rows = list(csv.DictReader(f))
    by_nb = {r["notebook"]: r for r in rows}
    assert by_nb[nb_root.name]["src_hash"] != "STALE_ROOT", (
        "sans borne derivable, l'input CLI doit rester la racine de scan"
    )
    assert nb_new.relative_to(tmp_path).as_posix() in by_nb, (
        "le repli doit conserver le comportement plein perimetre de l'input CLI ; "
        f"got notebooks={set(by_nb)}"
    )


def test_full_mode_note_does_not_report_covered_input_as_ignored(
    tmp_path, monkeypatch, capsys
):
    """#21518 reserve 2 : un input CLI COUVERT par une borne n'est pas « ignore ».

    Le filtre historique testait l'appartenance EXACTE : un input situe
    SOUS une borne etait annonce « ignore » sur stderr alors que ses carnets
    etaient bien scannes via la borne. Le log operateur mentait.
    """
    nb_a = tmp_path / "series" / "A.ipynb"
    _make_notebook(nb_a, "a1", text_fr="## A")
    # Carnet sous le sous-dossier passe en input : il prouve que ce chemin
    # est reellement scanne (via la borne `series`), donc que l'annoncer
    # « ignore » serait faux.
    nb_deep = tmp_path / "series" / "sub" / "Deep.ipynb"
    _make_notebook(nb_deep, "d1", text_fr="## Deep")
    csv_path = _make_csv(
        tmp_path / "synced.csv",
        PIVOT_HEADER,
        [
            {"notebook": nb_a.relative_to(tmp_path).as_posix(), "cell_id": "a1",
             "cell_type": "markdown", "src_lang": "fr", "src_hash": "STALE_A",
             "text_fr": "## A", "hash_fr": "FR_A"},
        ],
    )

    # Inputs = racine (parent de la borne, reellement ecartee comme racine)
    # + un SOUS-dossier de la serie (couvert par la borne, donc scanne).
    sub_input = tmp_path / "series" / "sub"
    monkeypatch.setattr(sys, "argv", [
        "extract_cells_to_csv.py",
        "--repo-root", str(tmp_path),
        str(tmp_path),
        str(sub_input),
        "--update", str(csv_path),
        "--full",
    ])
    assert e.main() == 0

    with csv_path.open(encoding="utf-8") as f:
        rows = list(csv.DictReader(f))
    notebooks = {r["notebook"] for r in rows}
    assert nb_deep.relative_to(tmp_path).as_posix() in notebooks, (
        "le carnet du sous-dossier est scanne via la borne : "
        f"got notebooks={notebooks}"
    )

    err = capsys.readouterr().err
    assert "non utilisé(s) comme racine de scan" in err, (
        f"la NOTE doit nommer les racines ecartees ; stderr={err!r}"
    )
    note = next(line for line in err.splitlines() if "non utilisé(s)" in line)
    assert str(sub_input) not in note, (
        "un input COUVERT par une borne voit ses carnets scannes : il ne doit pas "
        f"etre annonce ecarte ; note={note!r}"
    )
    assert str(tmp_path) in note, (
        f"la racine (parent de la borne) doit rester annoncee ; note={note!r}"
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
