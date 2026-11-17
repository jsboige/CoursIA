"""Tests de la garde d'integrite du ledger des renommages.

Chaque fixture reproduit une forme mesuree : les cycles legitimes a dates
croissantes (iterations ICT de structure de dossier sur main), et les deux
signatures d'artefact d'union visees par le GO (cle source dupliquee,
aller-retour colle sans dates croissantes).
"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from check_rename_ledger import check_ledger, main  # noqa: E402

HEADER = "ancien\tnouveau\tdate\tlane"


def _ledger(*rows: str, header: str = HEADER, trailing_newline: bool = True) -> str:
    body = "\n".join([header, *rows])
    return body + "\n" if trailing_newline else body


def test_clean_ledger_passes():
    text = _ledger(
        "a/serie-01.ipynb\ta/serie-02.ipynb\t2026-11-01\tmyia-po-2027:CoursIA",
        "b/serie-02.ipynb\tb/serie-03.ipynb\t2026-11-02\tmyia-po-2027:CoursIA",
    )
    code, failures, notes = check_ledger(text)
    assert code == 0, failures
    assert failures == []
    assert notes == []


def test_ict_shaped_cycle_passes_as_legitimate():
    # Forme mesuree sur main : le meme carnet remonte deux fois la structure
    # de dossier, dates strictement croissantes autour de la boucle.
    text = _ledger(
        "A/N.ipynb\tB/N.ipynb\t2026-10-26\tmyia-po-2027:CoursIA",
        "B/N.ipynb\tC/N.ipynb\t2026-10-28\tmyia-po-2027:CoursIA",
        "C/N.ipynb\tA/N.ipynb\t2026-11-15\tmyia-po-2027:CoursIA",
    )
    code, failures, notes = check_ledger(text)
    assert code == 0, failures
    assert any("cycle legitime" in note for note in notes)


def test_increasing_roundtrip_passes_as_legitimate():
    text = _ledger(
        "X.ipynb\tY.ipynb\t2026-01-01\tlane-a",
        "Y.ipynb\tX.ipynb\t2026-02-01\tlane-b",
    )
    code, failures, notes = check_ledger(text)
    assert code == 0, failures
    assert any("cycle legitime" in note for note in notes)


def test_same_day_roundtrip_fails():
    # Signature d'union : deux branches ont chacune renomme dans l'autre sens,
    # le driver colle les deux lignes, les dates ne montent pas.
    text = _ledger(
        "X.ipynb\tY.ipynb\t2026-11-15\tlane-a",
        "Y.ipynb\tX.ipynb\t2026-11-15\tlane-b",
    )
    code, failures, _ = check_ledger(text)
    assert code == 1
    assert any("sans dates croissantes" in f for f in failures)


def test_repeated_date_in_cycle_fails():
    # Une boucle est temporellement coherente ssi ses dates sont toutes
    # distinctes (tri strictement croissant possible). Deux aretes de meme
    # date dans la boucle : deux branches ont renomme le meme jour, collees
    # par l'union. Limite documentee : un artefact a dates toutes distinctes
    # est indiscernable d'une histoire et passe.
    text = _ledger(
        "A.ipynb\tB.ipynb\t2026-10-26\tlane-a",
        "B.ipynb\tC.ipynb\t2026-10-28\tlane-b",
        "C.ipynb\tA.ipynb\t2026-10-26\tlane-c",
    )
    code, failures, _ = check_ledger(text)
    assert code == 1
    assert any("sans dates croissantes" in f for f in failures)


def test_descending_pair_is_legitimate_history():
    # Y->X le 10-01 puis X->Y le 11-15 : dates distinctes, la boucle lue par
    # dates croissantes raconte une histoire coherente (le carnet est revenu).
    text = _ledger(
        "X.ipynb\tY.ipynb\t2026-11-15\tlane-a",
        "Y.ipynb\tX.ipynb\t2026-10-01\tlane-b",
    )
    code, failures, _ = check_ledger(text)
    assert code == 0, failures


def test_duplicate_source_fails():
    text = _ledger(
        "N.ipynb\tA/N.ipynb\t2026-11-15\tlane-a",
        "N.ipynb\tB/N.ipynb\t2026-11-15\tlane-b",
    )
    code, failures, _ = check_ledger(text)
    assert code == 1
    assert any("cle source dupliquee" in f for f in failures)


def test_self_rename_fails():
    text = _ledger("N.ipynb\tN.ipynb\t2026-11-15\tlane-a")
    code, failures, _ = check_ledger(text)
    assert code == 1
    assert any("auto-renommage" in f for f in failures)


def test_blank_line_fails():
    text = _ledger(
        "a.ipynb\tb.ipynb\t2026-11-01\tlane-a",
        "",
        "c.ipynb\td.ipynb\t2026-11-02\tlane-a",
    )
    code, failures, _ = check_ledger(text)
    assert code == 1
    assert any("ligne vide" in f for f in failures)


def test_trailing_newline_is_not_a_blank_line():
    # Un fichier fini par \n est la forme normale produite par append_ledger :
    # la ligne vide de fin n'est pas un constat.
    text = _ledger("a.ipynb\tb.ipynb\t2026-11-01\tlane-a")
    code, failures, _ = check_ledger(text)
    assert code == 0, failures


def test_wrong_column_count_fails():
    text = _ledger("a.ipynb\tb.ipynb\t2026-11-01")
    code, failures, _ = check_ledger(text)
    assert code == 1
    assert any("colonne" in f for f in failures)


def test_bad_date_fails():
    text = _ledger("a.ipynb\tb.ipynb\t15/11/2026\tlane-a")
    code, failures, _ = check_ledger(text)
    assert code == 1
    assert any("YYYY-MM-DD" in f for f in failures)


def test_bad_header_fails():
    text = _ledger("a.ipynb\tb.ipynb\t2026-11-01\tlane-a",
                   header="ancien\tnouveau\tquand\tlane")
    code, failures, _ = check_ledger(text)
    assert code == 1
    assert any("en-tete" in f for f in failures)


def test_missing_file_returns_2(tmp_path: Path, capsys):
    code = main(["--ledger", str(tmp_path / "absent.tsv")])
    assert code == 2
    assert "illisible" in capsys.readouterr().err


def test_main_json_output(tmp_path: Path, capsys):
    import json
    ledger = tmp_path / "ledger.tsv"
    ledger.write_text(_ledger("X.ipynb\tY.ipynb\t2026-11-15\tlane-a",
                              "Y.ipynb\tX.ipynb\t2026-11-15\tlane-b"),
                      encoding="utf-8")
    code = main(["--ledger", str(ledger), "--json"])
    assert code == 1
    payload = json.loads(capsys.readouterr().out)
    assert payload["failures"]
