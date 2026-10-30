#!/usr/bin/env python3
"""Contrat de l'allow-list et du matching des ancres proof-integrity.

Cible : le parsing ``ALLOW`` (``@path``), le cablage workflow -> fichier,
la normalisation des deux cotes dans ``LeanVerifier.check_axioms`` et la
coherence des comptes publies dans la documentation.

L'entree Conway.Life.p4_base_exhaustive...ax_1_1 (croix latine U+271D) doit
survivre au round-trip byte-identique du parseur. Les tests du gate prouvent
que les formes decoree et non decoree correspondent dans les deux sens, tout
en refusant une ancre reellement differente.
"""
from __future__ import annotations

import importlib.util
import re
import sys
from pathlib import Path
from unittest.mock import patch

import pytest

REPO = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO / "scripts" / "lean"))

from allow_list import parse_allow  # noqa: E402

CONWAY_FILE = REPO / "scripts" / "lean" / "allow_axioms_conway.txt"
CONWAY_WF = REPO / ".github" / "workflows" / "lean-conway.yml"
ANCHOR_DOC = REPO / "docs" / "lean" / "lean-anchor-naming.md"
DOCS_README = REPO / "docs" / "README.md"
LEAN_SERVER = (
    REPO
    / "MyIA.AI.Notebooks"
    / "SymbolicAI"
    / "Lean"
    / "agent_tests"
    / "lean_server.py"
)

LATIN_CROSS = "✝"  # Croix latine U+271D, distincte de la dague U+2020.
CONWAY_ANCHOR = "Conway.Life.p4_base_exhaustive._native.native_decide.ax_1_1"
DOC_COUNT_RE = re.compile(
    r"`scripts/lean/allow_axioms_conway\.txt`\s+contient\s+"
    r"\*\*(\d+)\s+entrées\*\*"
)
WORKFLOW_COUNT_RE = re.compile(
    r"#\s*allow-axioms:\s*(\d+)\s+native_decide\s+axioms\b"
)

_SPEC = importlib.util.spec_from_file_location("_anchor_contract_lean_server", LEAN_SERVER)
assert _SPEC is not None and _SPEC.loader is not None
lean_server = importlib.util.module_from_spec(_SPEC)
_SPEC.loader.exec_module(lean_server)


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


def test_conway_file_parses_to_79_unique_names():
    names = _conway_file_names()
    assert len(names) == 79
    assert len(set(names)) == 79
    assert all(n for n in names)


def test_conway_file_has_exactly_one_non_ascii_entry():
    names = _conway_file_names()
    non_ascii = [n for n in names if any(ord(c) > 127 for c in n)]
    assert non_ascii == [f"{CONWAY_ANCHOR}{LATIN_CROSS}"]


def test_conway_file_has_no_wildcard_entry():
    # regle no-wildcard du gate : un nouveau native_decide = un nouveau rouge
    assert "*" not in _conway_file_names()


# -------------------------------------- le matching réel du gate


def _check_anchor(listed: str, emitted: str) -> dict:
    """Exécute le vrai filtrage du gate sur une sortie Lean contrôlée."""
    stdout = (
        "'Conway.Life.p4_base_exhaustive' depends on axioms: "
        f"[{emitted}]"
    )
    # Le seam de lancement de Lean est `_organ_run` : depuis la migration
    # confinee (#15666), ce module ne spawn aucun processus lui-meme et
    # n'importe plus `subprocess`. Patcher `_resolve_lake_command` /
    # `subprocess.run` ne decouvre plus rien -- et leve une AttributeError
    # plutot qu'un echec de test lisible.
    assert hasattr(lean_server, "_organ_run"), (
        "lean_server n'expose plus `_organ_run` : le seam de lancement de Lean "
        "a change, ce test doit etre reecrit sur le nouveau seam."
    )
    verifier = lean_server.LeanVerifier(str(REPO))
    with patch.object(
        lean_server,
        "_organ_run",
        return_value=(0, stdout, ""),
    ):
        return verifier.check_axioms(
            "Conway.Life.p4_base_exhaustive",
            whitelist=[listed],
            fail_on_sorry=True,
            declarations=["Conway.Life.p4_base_exhaustive"],
        )


@pytest.mark.parametrize(
    ("listed", "emitted"),
    [
        (f"{CONWAY_ANCHOR}{LATIN_CROSS}", CONWAY_ANCHOR),
        (CONWAY_ANCHOR, f"{CONWAY_ANCHOR}{LATIN_CROSS}"),
    ],
    ids=["allow-list-decoree", "nom-extrait-decore"],
)
def test_gate_matching_normalizes_both_sides(listed, emitted):
    """La décoration peut être sur l'allow-list ou sur le nom extrait.

    Les deux cas doivent passer. Un matching exact-string échoue dans les
    deux sens, ce qui rend ce contrôle probant pour la comparaison normalisée.
    """
    result = _check_anchor(listed, emitted)
    assert result["success"] is True
    assert result["forbidden"] == []


def test_gate_matching_rejects_a_really_different_anchor():
    """La normalisation ne doit pas autoriser une ancre réellement distincte."""
    emitted = f"{CONWAY_ANCHOR.replace('ax_1_1', 'ax_1_2')}{LATIN_CROSS}"
    result = _check_anchor(f"{CONWAY_ANCHOR}{LATIN_CROSS}", emitted)
    assert result["success"] is False
    assert result["forbidden"] == [emitted]


@pytest.mark.parametrize("suffix", ["?", "!"])
def test_normalization_preserves_lean_identifier_suffixes(suffix):
    """Les suffixes `?` et `!` appartiennent au nom, pas à la décoration."""
    name = f"Foo.allowed{suffix}"
    assert lean_server.normalize_axiom_name(name) == name


# -------------------------------------- cohérence de la documentation


@pytest.mark.parametrize("document", [ANCHOR_DOC, DOCS_README])
def test_documentation_describes_normalized_matching(document):
    """La documentation et son index décrivent le matching réellement appliqué."""
    text = document.read_text(encoding="utf-8")
    flattened = re.sub(r"\s+", " ", text)
    assert "normalisé des deux côtés" in flattened
    assert not re.search(
        r"compare\s+\*\*exact-string\*\*|matching exact-string|ni normalisation",
        flattened,
        flags=re.IGNORECASE,
    )


def test_allow_list_header_does_not_claim_exact_string_matching():
    """L'en-tête de l'allow-list ne doit pas contredire le gate.

    L'en-tête renvoie à la documentation des ancres : si elle décrit un
    matching normalisé, un « matching exact-string » dans le même en-tête
    enverrait le lecteur vers une convention que le gate n'applique pas.
    Le commentaire est ignore par ``parse_allow`` -- la correction est donc
    sans effet sur le gate, et c'est bien le but : la phrase doit être vraie.
    """
    text = CONWAY_FILE.read_text(encoding="utf-8")
    flattened = re.sub(r"\s+", " ", text)
    assert not re.search(
        r"matching exact-string|ni normalisation",
        flattened,
        flags=re.IGNORECASE,
    ), "l'en-tête de l'allow-list affirme un matching que le gate n'applique pas"
    assert "normalise les deux cotes" in flattened.lower()


def _documented_count(text: str) -> int:
    """Exige une seule mention du compte, dans la forme documentaire attendue."""
    matches = DOC_COUNT_RE.findall(text)
    assert len(matches) == 1, (
        "la documentation doit citer exactement une fois le compte de "
        "scripts/lean/allow_axioms_conway.txt"
    )
    return int(matches[0])


def test_doc_count_matches_allow_file():
    """Le compte de la documentation ne peut pas dériver du fichier parsé."""
    text = ANCHOR_DOC.read_text(encoding="utf-8")
    assert _documented_count(text) == len(_conway_file_names())


def test_workflow_count_matches_allow_file():
    """Le compte du commentaire workflow est mesuré contre le même fichier."""
    text = CONWAY_WF.read_text(encoding="utf-8")
    matches = WORKFLOW_COUNT_RE.findall(text)
    assert len(matches) == 1
    assert int(matches[0]) == len(_conway_file_names())


# ------------------------------------------------- le cablage du workflow


def test_workflow_audit_job_points_at_the_file():
    text = CONWAY_WF.read_text(encoding="utf-8")
    refs = re.findall(r'allow-axioms:\s*"([^"]+)"', text)
    assert "@scripts/lean/allow_axioms_conway.txt" in refs
    # le bloc proof-integrity-audit (le job des 79 noms) pointe au fichier
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
