#!/usr/bin/env python3
"""Tests de ``notebook_lib_versions`` (organe de recensement des versions, #23073).

Couvre :
    * les trois formes de litteral : NuGet ``#r``, pip ``==``, URL de build Tweety ;
    * la portee CELLULES DE CODE seulement -- une mention en markdown ne compte pas ;
    * les six classes : OK, CONVERGE, ALLOWED, NO_CANONICAL, UNKNOWN,
      CANONICAL_UNRESOLVED ;
    * la resolution ``canonical_from`` (valeur non recopiee dans le manifeste) et ses
      deux echecs (fichier absent, regex sans correspondance) ;
    * ``iter_notebooks`` par motifs et l'exclusion des ``.ipynb_checkpoints`` ;
    * les codes de sortie de ``main`` : 0 par defaut, 1 sous ``--strict`` avec un
      CONVERGE, 2 sur manifeste invalide.

Run:
    pytest scripts/notebook_tools/tests/test_notebook_lib_versions.py
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

SCRIPT_DIR = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(SCRIPT_DIR))

import notebook_lib_versions as nlv  # noqa: E402


def _write_notebook(path: Path, cells: list[tuple[str, str]]) -> Path:
    """Ecrit un carnet minimal : [(cell_type, source)]."""
    doc = {
        "cells": [
            {
                "cell_type": kind,
                "metadata": {},
                "source": source.splitlines(keepends=True),
                **({"outputs": [], "execution_count": None} if kind == "code" else {}),
            }
            for kind, source in cells
        ],
        "metadata": {},
        "nbformat": 4,
        "nbformat_minor": 5,
    }
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(doc), encoding="utf-8")
    return path


def _manifest(libraries: dict | None = None, allowlist: list | None = None) -> dict:
    return {"schema_version": 1, "libraries": libraries or {}, "allowlist": allowlist or []}


# --- formes de litteral ----------------------------------------------------

@pytest.mark.parametrize(
    "source, package, version",
    [
        ('#r "nuget: IKVM, 8.15.0"', "IKVM", "8.15.0"),
        ('#r "nuget: IKVM,8.15.0"', "IKVM", "8.15.0"),
        ("#r \"Nuget: pythonnet , 3.1.0\"", "pythonnet", "3.1.0"),
        ("#r 'nuget: MathNet.Numerics, 5.0.0'", "MathNet.Numerics", "5.0.0"),
    ],
)
def test_nuget_forms(tmp_path, source, package, version):
    nb = _write_notebook(tmp_path / "n.ipynb", [("code", source)])
    pins = nlv.scan_notebook(nb, repo_root=tmp_path)
    assert [(p.package, p.version, p.ecosystem) for p in pins] == [(package, version, nlv.ECOSYSTEM_NUGET)]


def test_nuget_without_version_is_not_a_pin(tmp_path):
    nb = _write_notebook(tmp_path / "n.ipynb", [('code', '#r "nuget: IKVM"')])
    assert nlv.scan_notebook(nb, repo_root=tmp_path) == []


@pytest.mark.parametrize(
    "source",
    [
        "!pip install torch==2.5.1",
        "%pip install torch==2.5.1",
        "pip install torch==2.5.1",
        "!{sys.executable} -m pip install torch==2.5.1",
    ],
)
def test_pip_forms(tmp_path, source):
    nb = _write_notebook(tmp_path / "n.ipynb", [("code", source)])
    pins = nlv.scan_notebook(nb, repo_root=tmp_path)
    assert [(p.package, p.version, p.ecosystem) for p in pins] == [("torch", "2.5.1", nlv.ECOSYSTEM_PIP)]


def test_pip_multiple_packages_on_one_line(tmp_path):
    nb = _write_notebook(tmp_path / "n.ipynb", [("code", "!pip install torch==2.5.1 lean-dojo==2.2.0")])
    pins = nlv.scan_notebook(nb, repo_root=tmp_path)
    assert {p.package for p in pins} == {"torch", "lean-dojo"}


def test_pip_unpinned_is_ignored(tmp_path):
    nb = _write_notebook(tmp_path / "n.ipynb", [("code", "!pip install ortools numpy scipy")])
    assert nlv.scan_notebook(nb, repo_root=tmp_path) == []


def test_tweety_build_url(tmp_path):
    nb = _write_notebook(tmp_path / "n.ipynb", [("code", "url = 'https://tweetyproject.org/builds/1.30/tweety.zip'")])
    pins = nlv.scan_notebook(nb, repo_root=tmp_path)
    assert [(p.package, p.version, p.ecosystem) for p in pins] == [("Tweety", "1.30", nlv.ECOSYSTEM_TWEETY)]


# --- portee : cellules de code seulement ------------------------------------

def test_markdown_mention_is_not_counted(tmp_path):
    nb = _write_notebook(
        tmp_path / "n.ipynb",
        [
            ("markdown", 'On epingle `#r "nuget: IKVM, 8.14.0"` dans ce cours.'),
            ("code", 'print("rien")'),
        ],
    )
    assert nlv.scan_notebook(nb, repo_root=tmp_path) == []


def test_cell_index_counts_all_cells(tmp_path):
    nb = _write_notebook(
        tmp_path / "n.ipynb",
        [("markdown", "# titre"), ("code", 'print(1)'), ("code", '#r "nuget: IKVM, 8.15.0"')],
    )
    pins = nlv.scan_notebook(nb, repo_root=tmp_path)
    assert [p.cell for p in pins] == [2]  # index sur TOUTES les cellules, pas sur les seules cellules de code


def test_unreadable_notebook_does_not_raise(tmp_path):
    bad = tmp_path / "bad.ipynb"
    bad.write_text("{not json", encoding="utf-8")
    assert nlv.scan_notebook(bad, repo_root=tmp_path) == []


# --- canoniques ------------------------------------------------------------

def test_canonical_literal(tmp_path):
    assert nlv.resolve_canonical({"canonical": "8.15.0"}, tmp_path) == ("8.15.0", None)


def test_canonical_null_is_arbitration_not_failure(tmp_path):
    assert nlv.resolve_canonical({"canonical": None, "basis": "egalite"}, tmp_path) == (None, None)


def test_canonical_from_reads_series_organ(tmp_path):
    organ = tmp_path / "scripts" / "dl.py"
    organ.parent.mkdir(parents=True)
    organ.write_text('TWEETY_VERSION = "1.30"  # commentaire\n', encoding="utf-8")
    entry = {"canonical_from": {"file": "scripts/dl.py", "regex": 'TWEETY_VERSION\\s*=\\s*"([^"]+)"'}}
    assert nlv.resolve_canonical(entry, tmp_path) == ("1.30", None)


def test_canonical_from_missing_file_is_a_failure(tmp_path):
    entry = {"canonical_from": {"file": "absent.py", "regex": "(.*)"}, "canonical": "1.30"}
    version, problem = nlv.resolve_canonical(entry, tmp_path)
    assert version is None and "introuvable" in problem


def test_canonical_from_unmatched_regex_is_a_failure(tmp_path):
    organ = tmp_path / "dl.py"
    organ.write_text("VERSION = 'x'\n", encoding="utf-8")
    entry = {"canonical_from": {"file": "dl.py", "regex": 'TWEETY_VERSION\\s*=\\s*"([^"]+)"'}}
    version, problem = nlv.resolve_canonical(entry, tmp_path)
    assert version is None and "sans correspondance" in problem


# --- classification --------------------------------------------------------

def _pin(package="IKVM", version="8.15.0", notebook="nb.ipynb", ecosystem=nlv.ECOSYSTEM_NUGET) -> nlv.Pin:
    return nlv.Pin(package, version, ecosystem, notebook, 0, "#r ...")


def test_class_ok(tmp_path):
    res = nlv.classify([_pin(version="8.15.0")], _manifest({"IKVM": {"canonical": "8.15.0"}}), tmp_path)
    assert [s["class"] for s in res["pins"]] == ["OK"]


def test_class_converge(tmp_path):
    res = nlv.classify([_pin(version="8.14.0")], _manifest({"IKVM": {"canonical": "8.15.0"}}), tmp_path)
    assert [s["class"] for s in res["pins"]] == ["CONVERGE"]
    assert res["classes"] == {"CONVERGE": 1}


def test_class_allowed_needs_matching_scope(tmp_path):
    manifest = _manifest(
        {"IKVM": {"canonical": "8.15.0"}},
        [{"package": "IKVM", "version": "8.14.0", "notebooks": ["old/*.ipynb"], "reason": "epinglage voulu"}],
    )
    in_scope = nlv.classify([_pin(version="8.14.0", notebook="old/n.ipynb")], manifest, tmp_path)
    out_scope = nlv.classify([_pin(version="8.14.0", notebook="new/n.ipynb")], manifest, tmp_path)
    assert [s["class"] for s in in_scope["pins"]] == ["ALLOWED"]
    assert [s["class"] for s in out_scope["pins"]] == ["CONVERGE"]


def test_class_no_canonical_is_distinct_from_unresolved(tmp_path):
    res = nlv.classify([_pin(version="1.0")], _manifest({"IKVM": {"canonical": None, "basis": "egalite"}}), tmp_path)
    assert [s["class"] for s in res["pins"]] == ["NO_CANONICAL"]
    # Aucune "canonique non resolue" : le manifeste n'a pas echoue, il attend un arbitrage.
    assert res["canonical"]["IKVM"] == {"version": None, "problem": None}


def test_class_unknown_package(tmp_path):
    res = nlv.classify([_pin(package="Inconnu")], _manifest({}), tmp_path)
    assert [s["class"] for s in res["pins"]] == ["UNKNOWN"]


def test_class_canonical_unresolved(tmp_path):
    entry = {"canonical_from": {"file": "absent.py", "regex": "(.*)"}}
    res = nlv.classify([_pin(version="8.15.0")], _manifest({"IKVM": entry}), tmp_path)
    assert [s["class"] for s in res["pins"]] == ["CANONICAL_UNRESOLVED"]
    assert res["canonical"]["IKVM"]["problem"]


def test_dispersion_counts_notebooks_per_version(tmp_path):
    pins = [_pin(version="8.14.0", notebook="a.ipynb"), _pin(version="8.15.0", notebook="b.ipynb"), _pin(version="8.15.0", notebook="b.ipynb")]
    res = nlv.classify(pins, _manifest({"IKVM": {"canonical": "8.15.0"}}), tmp_path)
    assert res["dispersion"] == {"IKVM": {"8.14.0": 1, "8.15.0": 1}}  # un carnet compte une fois


# --- corpus ---------------------------------------------------------------

def test_iter_notebooks_by_pattern_skips_checkpoints(tmp_path):
    _write_notebook(tmp_path / "a" / "keep.ipynb", [("code", "x")])
    _write_notebook(tmp_path / "a" / ".ipynb_checkpoints" / "skip-checkpoint.ipynb", [("code", "x")])
    (tmp_path / "a" / "not-nb.txt").write_text("x", encoding="utf-8")
    found = nlv.iter_notebooks(["a/**/*.ipynb"], repo_root=tmp_path)
    assert [p.name for p in found] == ["keep.ipynb"]


# --- codes de sortie ------------------------------------------------------

def _run(tmp_path, monkeypatch, argv):
    monkeypatch.setattr(nlv, "iter_notebooks", lambda patterns=None: [])
    return nlv.main(argv)


def test_main_default_rc0_even_with_converge(tmp_path, monkeypatch, capsys):
    nb = _write_notebook(tmp_path / "nb" / "n.ipynb", [("code", '#r "nuget: IKVM, 8.14.0"')])
    manifest = tmp_path / "m.json"
    manifest.write_text(json.dumps(_manifest({"IKVM": {"canonical": "8.15.0"}})), encoding="utf-8")
    rc = nlv.main(["--manifest", str(manifest), "--paths", str(tmp_path / "nb" / "*.ipynb")])
    assert rc == 0
    assert "CONVERGE" in capsys.readouterr().out


def test_main_strict_rc1_on_converge(tmp_path, capsys):
    _write_notebook(tmp_path / "nb" / "n.ipynb", [("code", '#r "nuget: IKVM, 8.14.0"')])
    manifest = tmp_path / "m.json"
    manifest.write_text(json.dumps(_manifest({"IKVM": {"canonical": "8.15.0"}})), encoding="utf-8")
    assert nlv.main(["--manifest", str(manifest), "--paths", str(tmp_path / "nb" / "*.ipynb"), "--strict"]) == 1


def test_main_strict_rc0_when_all_ok(tmp_path):
    _write_notebook(tmp_path / "nb" / "n.ipynb", [("code", '#r "nuget: IKVM, 8.15.0"')])
    manifest = tmp_path / "m.json"
    manifest.write_text(json.dumps(_manifest({"IKVM": {"canonical": "8.15.0"}})), encoding="utf-8")
    assert nlv.main(["--manifest", str(manifest), "--paths", str(tmp_path / "nb" / "*.ipynb"), "--strict"]) == 0


def test_main_rc2_on_invalid_manifest(tmp_path):
    bad = tmp_path / "bad.json"
    bad.write_text(json.dumps({"nope": 1}), encoding="utf-8")
    assert nlv.main(["--manifest", str(bad)]) == 2


def test_main_json_is_parseable(tmp_path, capsys):
    _write_notebook(tmp_path / "nb" / "n.ipynb", [("code", '#r "nuget: IKVM, 8.15.0"')])
    manifest = tmp_path / "m.json"
    manifest.write_text(json.dumps(_manifest({"IKVM": {"canonical": "8.15.0"}})), encoding="utf-8")
    assert nlv.main(["--manifest", str(manifest), "--paths", str(tmp_path / "nb" / "*.ipynb"), "--json"]) == 0
    doc = json.loads(capsys.readouterr().out)
    assert doc["notebooks"] == 1 and doc["classes"] == {"OK": 1}