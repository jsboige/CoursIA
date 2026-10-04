#!/usr/bin/env python3
"""Tests pour check_credited_examples.py (extension check_pr_exercises.py).

Issue #18740 acceptance : l'organe distingue correctement :
1. Les cellules ``### Exemple ...`` (avec ou sans ``:`` dans le titre)
   des cellules ``### Exercice ...`` (qu'on ignore).
2. La presence d'un attribution ``#NNNN`` (regex stricte avec ``#`` obligatoire).
3. La perte entre base et head, avec et sans exemption ``exemples-loss:``.
4. Le format de titre contenant un ``:`` (cas SK-08 guidé 1).
"""
from __future__ import annotations

import json
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent))
from check_credited_examples import (  # noqa: E402
    _CREDIT_INLINE_RE,
    _EXEMPTION_LINE_PREFIX_RE,
    _blob_absent_from_ref,
    _cell_title,
    _exemption_markers,
    _extract_credit,
    _is_example_header,
    _norm_title,
    count_credited_examples,
    diff_examples,
)


def _mk_md_cell(text: str, cell_id: str, credited_from: str | None = None) -> dict:
    """Construit une cellule markdown avec source = liste de lignes."""
    md = {}
    if credited_from is not None:
        md["credited_from"] = credited_from
    return {
        "cell_type": "markdown",
        "id": cell_id,
        "metadata": md,
        "source": [ln + "\n" for ln in text.splitlines()],
    }


def _mk_nb(cells: list[dict]) -> dict:
    return {"cells": cells, "nbformat": 4, "nbformat_minor": 5}


# --- 1. _is_example_header ---------------------------------------------------

def test_is_example_header_simple():
    assert _is_example_header("### Exemple 1\n\nfoo") is True


def test_is_example_header_with_colon():
    assert _is_example_header("### Exemple : truc\n\nfoo") is True


def test_is_example_header_with_numbered_prefix():
    assert _is_example_header("## 5. Exemple guidé\n\nfoo") is True


def test_is_example_header_exercice_excluded():
    """Les cellules Exercice ne sont PAS comptées comme exemple (sinon
    check_pr_exercises.py se contredit lui-même)."""
    assert _is_example_header("### Exercice 1\n\nfoo") is False


def test_is_example_header_empty():
    assert _is_example_header("") is False


def test_is_example_header_other_heading_first():
    """Un header d'abord non-Exemple arrete la recherche."""
    src = "### Question 1\n\n### Exemple bidon\n"
    assert _is_example_header(src) is False


# --- 2. _extract_credit ------------------------------------------------------

def test_extract_credit_metadata_explicit():
    c = _mk_md_cell("### Exemple 1\n", "c1", credited_from="#18553")
    assert _extract_credit(c) == "#18553"


def test_extract_credit_inline_credite():
    c = _mk_md_cell("### Exemple guidé\n\ncrédité #18553\n", "c1")
    assert _extract_credit(c) == "#18553"


def test_extract_credit_inline_hash_only():
    c = _mk_md_cell("### Exemple\n\n#18553\n", "c1")
    assert _extract_credit(c) == "#18553"


def test_extract_credit_no_number():
    c = _mk_md_cell("### Exemple banal\n\nPas de credit\n", "c1")
    assert _extract_credit(c) is None


def test_extract_credit_bare_number_no_hash_rejected():
    """Sans ``#`` devant le numero, on ne considere PAS comme attribution.
    C'est le bug fondateur de la v1 : ``Exemple 2`` etait confondu avec ``#2``."""
    c = _mk_md_cell("### Exemple 2 : autre chose\n", "c1")
    assert _extract_credit(c) is None


def test_extract_credit_non_markdown_cell_ignored():
    c = {"cell_type": "code", "id": "c1", "source": ["#18553\n"], "metadata": {}}
    assert _extract_credit(c) is None


# --- 3. _cell_title ----------------------------------------------------------

def test_cell_title_strips_markdown_and_label():
    c = _mk_md_cell("### Exemple : truc\n\nfoo", "c1")
    assert _cell_title(c) == "truc"


def test_cell_title_with_numbered_prefix():
    c = _mk_md_cell("## 5. Exemple guidé 1\n", "c1")
    assert _cell_title(c) == "guidé 1"


def test_cell_title_keeps_inner_colon():
    """Le titre 'guidé 1 : Analyseur' doit etre preserve tel quel."""
    c = _mk_md_cell("### Exemple : guidé 1 : Analyseur de capacites MCP\n", "c1")
    assert _cell_title(c) == "guidé 1 : Analyseur de capacites MCP"


def test_cell_title_empty_for_code_cell():
    c = {"cell_type": "code", "id": "c1", "source": ["x = 1\n"], "metadata": {}}
    assert _cell_title(c) == ""


# --- 4. count_credited_examples ---------------------------------------------

def test_count_three_examples():
    nb = _mk_nb([
        _mk_md_cell("### Exemple : truc\n\ncrédité #1\n", "a"),
        _mk_md_cell("### Exemple 2\n\n#2\n", "b"),
        _mk_md_cell("### Exercice 1\n\n#3\n", "c"),  # Exercice -> ignore
        _mk_md_cell("### Exemple sans credit\n", "d"),  # Exemple mais pas de credit -> ignore
    ])
    assert len(count_credited_examples(nb)) == 2


def test_count_dedup_by_cell_id():
    nb = _mk_nb([_mk_md_cell("### Exemple\n\n#1\n", "a")])
    assert count_credited_examples(nb) == [{
        "cell_id": "a", "title": "", "credit": "#1",
    }]


# --- 5. diff_examples --------------------------------------------------------

def test_diff_lost_kept_added():
    base = [
        {"cell_id": "a", "title": "T1", "credit": "#1"},
        {"cell_id": "b", "title": "T2", "credit": "#1"},
        {"cell_id": "c", "title": "T3", "credit": "#1"},
    ]
    head = [
        {"cell_id": "a", "title": "T1", "credit": "#1"},  # kept
        {"cell_id": "d", "title": "T4", "credit": "#2"},  # added
    ]
    d = diff_examples(base, head)
    assert len(d["lost"]) == 2  # b, c
    assert len(d["added"]) == 1
    assert len(d["kept"]) == 1
    assert {x["cell_id"] for x in d["lost"]} == {"b", "c"}


def test_diff_no_change():
    base = [{"cell_id": "a", "title": "T1", "credit": "#1"}]
    head = list(base)
    d = diff_examples(base, head)
    assert d["lost"] == [] and d["added"] == [] and len(d["kept"]) == 1


# --- 6. _exemption_markers (regression bug #18740) ---------------------------

def test_exemption_simple_title():
    body = "exemples-loss: section assumee -- NB.ipynb section: foo : bar"
    out = _exemption_markers(body)
    assert len(out) == 1
    assert out[0]["notebook"] == "NB.ipynb"
    assert out[0]["title"] == "foo"
    assert out[0]["reason"] == "bar"


def test_exemption_title_with_inner_colon_sk08():
    """Cas fondateur : SK-08 guidé 1 ``guidé 1 : Analyseur de capacites MCP``.
    Le dernier ``:`` sépare TITLE de REASON ; les ``:`` internes restent dans TITLE.
    Avant le fix, le titre etait tronqué a ``guidé 1``."""
    body = (
        "exemples-loss: section assumee -- 08-SemanticKernel-MCP.ipynb "
        "section: guidé 1 : Analyseur de capacites MCP : refonte, déplacement daté"
    )
    out = _exemption_markers(body)
    assert len(out) == 1
    assert out[0]["notebook"] == "08-SemanticKernel-MCP.ipynb"
    assert out[0]["title"] == "guidé 1 : Analyseur de capacites MCP"
    assert out[0]["reason"] == "refonte, déplacement daté"


def test_exemption_multiple_lines():
    body = (
        "intro libre\n"
        "exemples-loss: section assumee -- A.ipynb section: t1 : r1\n"
        "exemples-loss: section assumee -- A.ipynb section: t2 : r2\n"
        "fin\n"
    )
    out = _exemption_markers(body)
    assert len(out) == 2
    assert [o["title"] for o in out] == ["t1", "t2"]


def test_exemption_no_marker():
    assert _exemption_markers("# header\n\nlibre\n") == []


def test_exemption_irrelevant_marker_ignored():
    # seul le prefixe "exemples-loss: section assumee --" est reconnu
    body = "plan-loss: section assumee -- A.ipynb section: t : r"
    assert _exemption_markers(body) == []


# --- 7. _norm_title ----------------------------------------------------------

def test_norm_title_lowercase_and_strip():
    assert _norm_title("  Guidé 1  ") == "guidé 1"


def test_norm_title_collapse_whitespace():
    assert _norm_title("guidé\t1 : x") == "guidé 1 : x"


# --- 8. Regex shapes ---------------------------------------------------------

def test_credit_inline_regex_requires_hash():
    """Le ``#`` est obligatoire ; le motif v1 matchait ``Exemple 2``."""
    assert _CREDIT_INLINE_RE.search("#18553")
    assert _CREDIT_INLINE_RE.search("crédité #18553")
    assert not _CREDIT_INLINE_RE.search("Exemple 2 : truc")


def test_exemption_line_prefix_shape():
    """Le prefixe reconnait le format canonique (avant split)."""
    m = _EXEMPTION_LINE_PREFIX_RE.match(
        "exemples-loss: section assumee -- NB section: rest"
    )
    assert m is not None
    assert m.group("nb") == "NB"
    assert m.group("rest") == "rest"


# --- 7. _blob_absent_from_ref : absence legitime != autre erreur git ---------

def _mk_git_repo(tmp_path: Path) -> Path:
    """Mini depot git avec un commit initial contenant un notebook."""
    import subprocess
    repo = tmp_path / "repo"
    repo.mkdir()
    nb = repo / "nb.ipynb"
    nb.write_text(json.dumps(_mk_nb([
        _mk_md_cell("### Exemple : truc\n\ncrédité #1\n", "a"),
    ])), encoding="utf-8")
    for cmd in (
        ["git", "init", "-q"],
        ["git", "config", "user.email", "t@t"],
        ["git", "config", "user.name", "t"],
        ["git", "add", "nb.ipynb"],
        ["git", "commit", "-qm", "init"],
    ):
        subprocess.run(cmd, cwd=repo, check=True, capture_output=True)
    return repo


def test_blob_absent_false_when_path_present(tmp_path):
    import subprocess
    repo = _mk_git_repo(tmp_path)
    sha = subprocess.run(
        ["git", "rev-parse", "HEAD"], cwd=repo,
        capture_output=True, text=True, check=True,
        encoding="utf-8", errors="replace",
    ).stdout.strip()
    # la sonde tourne depuis le depot (cwd), le chemin relatif existe
    p = subprocess.run(
        ["git", "-C", str(repo), "cat-file", "-e", f"{sha}:nb.ipynb"],
        capture_output=True,
    )
    assert p.returncode == 0
    # comportement de la sonde via un appel direct dans le cwd du repo
    import os
    old = os.getcwd()
    os.chdir(repo)
    try:
        assert _blob_absent_from_ref("HEAD", "nb.ipynb") is False
    finally:
        os.chdir(old)


def test_blob_absent_true_when_path_missing(tmp_path):
    import os
    repo = _mk_git_repo(tmp_path)
    old = os.getcwd()
    os.chdir(repo)
    try:
        # chemin jamais commis : absence legitime -> True (fichier ajoute)
        assert _blob_absent_from_ref("HEAD", "autre.ipynb") is True
    finally:
        os.chdir(old)


def test_blob_absent_false_for_invalid_ref(tmp_path):
    import os
    repo = _mk_git_repo(tmp_path)
    old = os.getcwd()
    os.chdir(repo)
    try:
        # ref inconnue : PAS une absence (rc 128) -> False, le git show
        # qui suit doit echouer bruyamment au lieu de produire un faux zero
        assert _blob_absent_from_ref("refs/heads/inexistante", "nb.ipynb") is False
    finally:
        os.chdir(old)


def test_blob_absent_true_when_path_on_disk_missing_from_ref(tmp_path):
    """Non-regression review 5407534311 : notebook AJOUTE (present sur
    disque, absent de la base). La prose git est « exists on disk, but not
    in » — l'ancien filtre sur « does not exist » rendait False et le git
    show plantait la CLI sur chaque notebook ajoute."""
    import os
    repo = _mk_git_repo(tmp_path)
    (repo / "ajoute.ipynb").write_text(json.dumps(_mk_nb([
        _mk_md_cell("### Exemple : truc\n\ncrédité #1\n", "a"),
    ])), encoding="utf-8")
    old = os.getcwd()
    os.chdir(repo)
    try:
        assert _blob_absent_from_ref("HEAD", "ajoute.ipynb") is True
    finally:
        os.chdir(old)


def test_cli_added_notebook_on_disk_zero_base_examples(tmp_path, capsys):
    """Non-regression review 5407534311, niveau CLI : un notebook ajoute
    (present sur disque, absent de la base) rend 0 exemple de base, sans
    exception."""
    import os
    repo = _mk_git_repo(tmp_path)
    (repo / "ajoute.ipynb").write_text(json.dumps(_mk_nb([
        _mk_md_cell("### Exemple : truc\n\ncrédité #1\n", "a"),
    ])), encoding="utf-8")
    old = os.getcwd()
    os.chdir(repo)
    try:
        from check_credited_examples import main
        rc = main(["ajoute.ipynb", "--base", "HEAD", "--json"])
        assert rc == 0
        out = json.loads(capsys.readouterr().out)
        assert out["base_examples"] == []
        assert len(out["head_examples"]) == 1
    finally:
        os.chdir(old)


if __name__ == "__main__":
    import pytest
    sys.exit(pytest.main([__file__, "-v"]))