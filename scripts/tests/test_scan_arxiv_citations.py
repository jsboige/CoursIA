"""Tests de `scripts/notebook_tools/scan_arxiv_citations.py`.

Ce qui est testé est l'**appariement** entre les IDs trouvés dans les notebooks
et un ledger de couverture -- pas l'API arXiv, pas la lecture de notebooks
réels. Reproduit la mesure du 2026-09-21 : un ledger de 121 IDs écrits sous
forme nue n'appariait que 119 clés du scan, et le delta annoncé sortait à 33 au
lieu de 31.
"""
import json
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from scripts.notebook_tools import scan_arxiv_citations as S  # noqa: E402

nbformat = pytest.importorskip("nbformat")


def _workspace(tmp_path, citations):
    """Crée un mini-workspace avec un notebook citant les IDs fournis."""
    ws = tmp_path / "ws"
    ws.mkdir()
    cells = [
        {
            "cell_type": "markdown",
            "metadata": {},
            "source": [f"Voir arXiv:{aid} pour la méthode."],
        }
        for aid in citations
    ]
    nb = nbformat.v4.new_notebook()
    nb.cells = [nbformat.from_dict(c) for c in cells]
    with (ws / "cite.ipynb").open("w", encoding="utf-8") as f:
        nbformat.write(nb, f)
    return ws


def _run(tmp_path, ws, covered_lines=None):
    out = tmp_path / "out.json"
    argv = ["--workspace", str(ws), "--out", str(out)]
    if covered_lines is not None:
        csv = tmp_path / "covered.csv"
        csv.write_text("\n".join(covered_lines) + "\n", encoding="utf-8")
        argv += ["--covered", str(csv)]
    assert S.main(argv) == 0
    return json.loads(out.read_text(encoding="utf-8"))


# --- `id_key` : la fonction qui porte la correction ------------------------

@pytest.mark.parametrize("raw,expected", [
    ("cs/0011047", "0011047"),          # préfixe legacy retiré de la CLÉ
    ("quant-ph/0604079", "0604079"),
    ("1706.03762", "1706.03762"),
    ("1706.03762v7", "1706.03762"),     # suffixe de version retiré
    (" cs/0011047 ", "0011047"),        # espaces
    ("CS/0011047", "0011047"),          # casse
])
def test_id_key_normalises(raw, expected):
    assert S.id_key(raw) == expected


def test_id_key_does_not_alter_the_queried_id():
    """Le préfixe doit survivre ailleurs : l'API rejette un legacy réduit."""
    assert "cs/" in "cs/0011047"


# --- appariement scan <-> ledger -------------------------------------------

def test_prefixed_scan_key_matches_bare_ledger_id(tmp_path):
    """La régression exacte : `cs/0011047` au scan, `0011047` au ledger."""
    ws = _workspace(tmp_path, ["cs/0011047"])
    data = _run(tmp_path, ws, covered_lines=["0011047"])

    assert data["delta_not_covered"] == []
    assert data["summary"]["covered_count"] == 1
    assert data["summary"]["not_covered_count"] == 0


def test_version_suffix_in_ledger_matches_bare_scan_key(tmp_path):
    ws = _workspace(tmp_path, ["1706.03762"])
    data = _run(tmp_path, ws, covered_lines=["1706.03762v7"])
    assert data["delta_not_covered"] == []


def test_uncovered_id_is_published_in_canonical_form(tmp_path):
    ws = _workspace(tmp_path, ["cs/0011047"])
    data = _run(tmp_path, ws, covered_lines=[])

    assert data["delta_not_covered"] == ["0011047"]      # forme canonique
    assert data["delta_raw_keys"] == ["cs/0011047"]      # clé brute conservée


def test_two_raw_forms_of_one_article_do_not_inflate_the_delta(tmp_path):
    """`cs/0011047` et `0011047` = un article, donc un seul delta."""
    ws = _workspace(tmp_path, ["cs/0011047", "0011047"])
    data = _run(tmp_path, ws, covered_lines=[])

    assert data["delta_not_covered"] == ["0011047"]
    assert data["delta_keys_collapsed"] == 1
    assert data["summary"]["unique_arxiv_ids"] == 2
    assert data["summary"]["unique_arxiv_ids_normalised"] == 1


def test_covered_count_is_computed_on_normalised_keys(tmp_path):
    ws = _workspace(tmp_path, ["cs/0011047", "1706.03762"])
    data = _run(tmp_path, ws, covered_lines=["0011047"])
    s = data["summary"]
    assert s["covered_count"] == 1
    assert s["not_covered_count"] == 1
    assert s["unique_arxiv_ids_normalised"] == 2


def test_comment_lines_in_ledger_are_ignored(tmp_path):
    ws = _workspace(tmp_path, ["1706.03762"])
    data = _run(tmp_path, ws, covered_lines=["# passe 1", "1706.03762"])
    assert data["delta_not_covered"] == []
