# Tests de l'organe check_cell_id_churn (issue #22595, suite de #22588).
#
# L'organe signale le churn d'identifiants de cellules : un id present en base,
# absent a la tete, dont la source reapparait a l'identique sous un autre id
# (la signature de « supprime + recree » qui churne le CSV de traduction, cle
# par cell_id). Une suppression reel (source absente de la tete) ne doit PAS
# etre signalee.

import json
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from check_cell_id_churn import detect_churn, main  # noqa: E402


def cell(cid, src, ctype="code"):
    return {"id": cid, "cell_type": ctype, "source": src, "metadata": {}}


# --- detect_churn : le coeur -------------------------------------------------


def test_flag_on_delete_and_recreate():
    # id A en base, absent a la tete ; sa source reapparait sous l'id C.
    base = [cell("aaaa0001", "x = 1\n"), cell("bbbb0002", "Title\n", "markdown")]
    head = [cell("bbbb0002", "Title\n", "markdown"), cell("cccc0003", "x = 1\n")]
    res = detect_churn(base, head)
    assert len(res["churned"]) == 1
    assert res["churned"][0]["base_id"] == "aaaa0001"
    assert res["churned"][0]["head_ids"] == ["cccc0003"]
    assert res["removed"] == 1 and res["added"] == 1


def test_none_when_id_preserved():
    base = [cell("aaaa0001", "x = 1\n")]
    head = [cell("aaaa0001", "x = 1\n")]
    assert detect_churn(base, head)["churned"] == []


def test_none_on_inplace_edit():
    # l'id est conserve : c'est une edition en place, pas un delete+recreate.
    base = [cell("aaaa0001", "x = 1\n")]
    head = [cell("aaaa0001", "x = 2\n")]
    assert detect_churn(base, head)["churned"] == []


def test_none_on_genuine_deletion():
    # la source de l'id retire n'existe plus nulle part a la tete.
    base = [cell("aaaa0001", "x = 1\n"), cell("bbbb0002", "y = 2\n")]
    head = [cell("bbbb0002", "y = 2\n")]
    assert detect_churn(base, head)["churned"] == []
    assert detect_churn(base, head)["removed"] == 1


def test_source_as_list_of_lines_is_joined():
    # la source en liste de lignes est reassemblee avant comparaison.
    base = [cell("aaaa0001", ["x = 1\n", "y = 2\n"])]
    head = [cell("cccc0003", "x = 1\ny = 2\n")]
    res = detect_churn(base, head)
    assert [c["base_id"] for c in res["churned"]] == ["aaaa0001"]


def test_counts_added_removed():
    base = [cell("a", "1"), cell("b", "2")]
    head = [cell("b", "2"), cell("c", "3"), cell("d", "4")]
    res = detect_churn(base, head)
    assert res["added"] == 2 and res["removed"] == 1 and res["churned"] == []


# --- main() : bout-en-bout sur un vrai depot git ----------------------------


def _git(cwd, *args):
    subprocess.run(["git", *args], cwd=cwd, check=True,
                   capture_output=True, text=True, encoding="utf-8")


def _write_nb(path, cells):
    path.write_text(json.dumps({"cells": cells, "metadata": {},
                                "nbformat": 4, "nbformat_minor": 5}),
                    encoding="utf-8")


def _init_repo(tmp_path):
    _git(tmp_path,"init", "-q")
    _git(tmp_path,"config", "user.email", "lane@test")
    _git(tmp_path,"config", "user.name", "lane")
    _git(tmp_path,"config", "commit.gpgsign", "false")


def test_main_flags_churn_end_to_end(tmp_path, monkeypatch):
    monkeypatch.chdir(tmp_path)
    _init_repo(tmp_path)
    _write_nb(tmp_path / "nb.ipynb",
              [cell("aaaa0001", "x = 1\n"), cell("bbbb0002", "t\n", "markdown")])
    _git(tmp_path,"add", "nb.ipynb")
    _git(tmp_path,"commit", "-q", "-m", "base")
    # supprime aaaa0001, re-cree sa source verbatim sous cccc0003
    _write_nb(tmp_path / "nb.ipynb",
              [cell("bbbb0002", "t\n", "markdown"), cell("cccc0003", "x = 1\n")])
    _git(tmp_path,"add", "nb.ipynb")
    _git(tmp_path,"commit", "-q", "-m", "head")

    assert main(["nb.ipynb", "--base", "HEAD~1"]) == 1


def test_main_clean_end_to_end(tmp_path, monkeypatch):
    monkeypatch.chdir(tmp_path)
    _init_repo(tmp_path)
    _write_nb(tmp_path / "nb.ipynb",
              [cell("aaaa0001", "x = 1\n"), cell("bbbb0002", "t\n", "markdown")])
    _git(tmp_path,"add", "nb.ipynb")
    _git(tmp_path,"commit", "-q", "-m", "base")
    # id aaaa0001 conserve, une seule cellule vraiment nouvelle
    _write_nb(tmp_path / "nb.ipynb",
              [cell("aaaa0001", "x = 1\n"), cell("bbbb0002", "t\n", "markdown"),
               cell("dddd0004", "z = 3\n")])
    _git(tmp_path,"add", "nb.ipynb")
    _git(tmp_path,"commit", "-q", "-m", "head")

    assert main(["nb.ipynb", "--base", "HEAD~1"]) == 0
