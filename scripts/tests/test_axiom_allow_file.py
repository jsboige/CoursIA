#!/usr/bin/env python3
"""Tests du parsing ALLOW (@path) du gate proof-integrity (#21905).

Cible : scripts/lean/allow_list.py (le parsing que axiom_check_step.py
consomme) + le cablage workflow -> fichier source de verite.

Le cas d'ecran : l'entree Conway.Life.p4_base_exhaustive...ax_1_1 (U+271D
latin cross) du fichier doit survivre au round-trip byte-identique -- c'est
le sujet de l'issue : le matching du gate est exact-string, un sanitize
silencieux du suffixe ferait rouge un gate vert (ou inversement au
prochain nettoyage de la liste).
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO / "scripts" / "lean"))

from allow_list import parse_allow  # noqa: E402

CONWAY_FILE = REPO / "scripts" / "lean" / "allow_axioms_conway.txt"
CONWAY_WF = REPO / ".github" / "workflows" / "lean-conway.yml"

LATIN_CROSS = "✝"  # ✝ -- le suffixe emis par Lean, U+271D (pas U+2020)


# ---------------------------------------------------------------- le parseur


def test_plain_comma_list_unchanged():
    assert parse_allow("a,b", REPO) == ["a", "b"]
    assert parse_allow(" a , b ,,", REPO) == ["a", "b"]


def test_empty_allow_is_empty_list():
    assert parse_allow("", REPO) == []
    assert parse_allow("   ", REPO) == []


def test_file_form_reads_names_strips_comments_and_blanks(tmp_path):
    f = tmp_path / "allow.txt"
    f.write_text(
        "# header comment\n"
        "ax.a\n"
        "\n"
        "ax.b  # trailing comment\n"
        "ax.c\n",
        encoding="utf-8",
    )
    assert parse_allow(f"@{f}", REPO) == ["ax.a", "ax.b", "ax.c"]


def test_file_form_resolves_against_repo_root(tmp_path):
    sub = tmp_path / "scripts" / "lean"
    sub.mkdir(parents=True)
    (sub / "allow_axioms_conway.txt").write_text("ax.a\n", encoding="utf-8")
    assert parse_allow("@scripts/lean/allow_axioms_conway.txt", tmp_path) == ["ax.a"]


def test_file_form_cwd_fallback(tmp_path, monkeypatch):
    (tmp_path / "allow.txt").write_text("ax.a\n", encoding="utf-8")
    monkeypatch.chdir(tmp_path)
    # repo_root ne contient PAS allow.txt : seul le repli cwd trouve le fichier
    assert parse_allow("@allow.txt", REPO) == ["ax.a"]


def test_missing_file_fails_closed(tmp_path):
    with pytest.raises(SystemExit) as exc:
        parse_allow("@scripts/lean/does_not_exist.txt", tmp_path)
    assert "ALLOW" in str(exc.value)


def test_file_entry_with_latin_cross_survives_byte_identical(tmp_path):
    name = f"Conway.Life.p4_base_exhaustive._native.native_decide.ax_1_1{LATIN_CROSS}"
    f = tmp_path / "allow.txt"
    f.write_text(f"{name}\n", encoding="utf-8")
    assert parse_allow(f"@{f}", REPO) == [name]


# --------------------------- le fichier source de verite (Conway)


def _conway_file_names() -> list[str]:
    return parse_allow("@scripts/lean/allow_axioms_conway.txt", REPO)


def test_conway_file_parses_to_77_unique_names():
    names = _conway_file_names()
    assert len(names) == 77
    assert len(set(names)) == 77
    assert all(n for n in names)


def test_conway_file_carries_exactly_one_latin_cross_entry():
    names = _conway_file_names()
    crossed = [n for n in names if LATIN_CROSS in n]
    assert crossed == [
        f"Conway.Life.p4_base_exhaustive._native.native_decide.ax_1_1{LATIN_CROSS}"
    ]


def test_conway_file_has_no_wildcard_entry():
    # regle no-wildcard du gate : un nouveau native_decide = un nouveau rouge
    assert "*" not in _conway_file_names()


# ------------------------------------------------- le cablage du workflow


def test_workflow_audit_job_points_at_the_file():
    text = CONWAY_WF.read_text(encoding="utf-8")
    refs = re.findall(r'allow-axioms:\s*"([^"]+)"', text)
    assert "@scripts/lean/allow_axioms_conway.txt" in refs
    # le bloc proof-integrity-audit (le job des 77 noms) pointe au fichier
    m = re.search(
        r"proof-integrity-audit:.*?allow-axioms:\s*\"([^\"]+)\"",
        text,
        re.DOTALL,
    )
    assert m is not None
    assert m.group(1) == "@scripts/lean/allow_axioms_conway.txt"


def test_workflow_no_longer_carries_an_inline_native_decide_list():
    text = CONWAY_WF.read_text(encoding="utf-8")
    inline = [s for s in re.findall(r'allow-axioms:\s*"([^"]+)"', text) if "native_decide" in s]
    assert inline == []
