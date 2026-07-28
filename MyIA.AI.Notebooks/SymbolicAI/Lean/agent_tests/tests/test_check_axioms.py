"""Unit tests for ``LeanVerifier.check_axioms`` and declaration enumeration (#8677).

Covers the two correctness gates of ``pr-review-discipline.md`` §B.3:

* ``#print axioms`` is emitted per **declaration** (namespace-qualified), not
  per module segment -- the command expects a declaration name.
* ``sorryAx`` reveals a (possibly transitive) ``sorry`` in the dependency chain
  and fails integrity when ``fail_on_sorry=True`` (the CI review gate), while
  the prover default ``fail_on_sorry=False`` preserves historical behaviour
  (Level 2 tracks sorry textually, so Level 3 stays green).

No real Lean build is required: ``subprocess.run``, the lake resolver and the
declaration enumerator are mocked so the gate logic is exercised deterministically.

Run from ``agent_tests/``::

    python -m pytest tests/test_check_axioms.py -q
"""

from __future__ import annotations

import sys
from pathlib import Path
from unittest.mock import patch

import pytest

# Make the package importable regardless of how pytest is invoked.
HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT))

import lean_server  # noqa: E402
from lean_server import LeanVerifier, _enumerate_module_declarations  # noqa: E402

# Lean single-quotes the declaration name in ``#print axioms`` output.
Q = "'"


def _axiom_line(name: str, axioms: list) -> str:
    inner = ", ".join(axioms) if axioms else ""
    return f"{Q}{name}{Q} depends on axioms [{inner}]"


class _FakeCompletedProcess:
    def __init__(self, stdout: str = "", stderr: str = "", returncode: int = 0):
        self.stdout = stdout
        self.stderr = stderr
        self.returncode = returncode


# ──────────────────────────────────────────────────────────────────────────
# _enumerate_module_declarations
# ──────────────────────────────────────────────────────────────────────────

def test_enumeration_namespace_tracking(tmp_path):
    src = (
        "namespace Foo\n"
        "theorem bar : True := trivial\n"
        "theorem baz : True := trivial\n"
        "end Foo\n"
        "def quux : Nat := 0\n"
    )
    mod = tmp_path / "Knots"
    mod.mkdir()
    (mod / "Basic.lean").write_text(src, encoding="utf-8")
    decls = _enumerate_module_declarations(tmp_path, "Knots.Basic")
    assert decls == ["Foo.bar", "Foo.baz", "quux"]


def test_enumeration_attributes_and_dotted_name(tmp_path):
    src = (
        "@[simp] theorem Private.thing : True := trivial\n"
        "theorem plain : True := trivial\n"
    )
    (tmp_path / "M.lean").write_text(src, encoding="utf-8")
    decls = _enumerate_module_declarations(tmp_path, "M")
    assert decls == ["Private.thing", "plain"]


def test_enumeration_missing_source_returns_empty(tmp_path):
    assert _enumerate_module_declarations(tmp_path, "Does.Not.Exist") == []


# ──────────────────────────────────────────────────────────────────────────
# _extract_axioms
# ──────────────────────────────────────────────────────────────────────────

def test_extract_axioms_parses_depends_on_format():
    out = "\n".join(
        [
            _axiom_line("A.foo", ["Classical.choice", "propext"]),
            _axiom_line("A.bar", []),
        ]
    )
    assert set(LeanVerifier._extract_axioms(out)) == {"Classical.choice", "propext"}


def test_extract_axioms_detects_sorry_axiom():
    out = _axiom_line("X.y", ["sorryAx"])
    assert LeanVerifier._extract_axioms(out) == ["sorryAx"]


def test_extract_axioms_ignores_non_axiom_lines():
    out = "error: unknown identifier 'Nope'\nrandom diagnostics line\n"
    assert LeanVerifier._extract_axioms(out) == []


# ──────────────────────────────────────────────────────────────────────────
# check_axioms gate logic (subprocess mocked)
# ──────────────────────────────────────────────────────────────────────────

def _check_with_output(decls, fake_stdout, *, fail_on_sorry=False, project_dir=".", returncode=0):
    verifier = LeanVerifier(project_dir)
    with patch.object(lean_server, "_enumerate_module_declarations", return_value=decls), \
            patch.object(lean_server, "_resolve_lake_command", return_value=(["lean"], {})), \
            patch.object(lean_server.subprocess, "run",
                         return_value=_FakeCompletedProcess(fake_stdout, returncode=returncode)):
        return verifier.check_axioms("Knots.Basic", fail_on_sorry=fail_on_sorry)


def test_clean_proof_passes_gate():
    out = _axiom_line("Knots.Basic.t1", ["Classical.choice", "propext"])
    r = _check_with_output(["Knots.Basic.t1"], out, fail_on_sorry=True)
    assert r["success"] is True
    assert r["has_sorry"] is False
    assert r["enumerated"] is True
    assert r["declarations"] == ["Knots.Basic.t1"]


def test_transitive_sorry_fails_ci_gate():
    out = _axiom_line("Knots.Basic.t1", ["sorryAx"])
    r = _check_with_output(["Knots.Basic.t1"], out, fail_on_sorry=True)
    assert r["success"] is False
    assert r["has_sorry"] is True


def test_transitive_sorry_prover_path_stays_green():
    # fail_on_sorry=False (prover): Level 2 tracks sorry textually, so Level 3
    # must NOT flip to red on a sorryAx -- historical behaviour preserved.
    out = _axiom_line("Knots.Basic.t1", ["sorryAx"])
    r = _check_with_output(["Knots.Basic.t1"], out, fail_on_sorry=False)
    assert r["success"] is True
    assert r["has_sorry"] is True


def test_forbidden_axiom_fails_both_paths():
    out = _axiom_line("Knots.Basic.t1", ["of_eq_true"])
    r_prover = _check_with_output(["Knots.Basic.t1"], out, fail_on_sorry=False)
    r_gate = _check_with_output(["Knots.Basic.t1"], out, fail_on_sorry=True)
    assert r_prover["success"] is False
    assert r_gate["success"] is False
    assert r_gate["forbidden"] == ["of_eq_true"]


def test_no_declarations_ci_gate_fails_loud():
    r = _check_with_output([], "", fail_on_sorry=True)
    assert r["success"] is False
    assert r["error"] == "no_declarations_enumerated"
    assert r["enumerated"] is False


def test_no_declarations_prover_path_stays_green():
    r = _check_with_output([], "", fail_on_sorry=False)
    assert r["success"] is True
    assert r["enumerated"] is False


# ──────────────────────────────────────────────────────────────────────────
# Build-dead gate (trou #8681, ai-01 c.32) : un build MORT ne valide jamais
# ──────────────────────────────────────────────────────────────────────────

def test_dead_build_fails_ci_gate():
    """returncode != 0 (build cassé) + output vide -> success=False.

    Avant le fix #8681, ce cas renvoyait success=True car _extract_axioms([])
    donnait forbidden=[]/has_sorry=False : un build mort validait l'intégrité.
    L'énumération compte 1 déclaration (elle lit le source, pas le build), donc
    le garde ``no_declarations_enumerated`` ne couvrait pas ce cas.
    """
    r = _check_with_output(
        ["Knots.Basic.t1"], "", fail_on_sorry=True, returncode=1,
    )
    assert r["success"] is False
    assert r["error"] == "build_failed_returncode_1"
    assert r["enumerated"] is True  # le source enumerait bien la déclaration
    assert r["axioms"] == []


def test_dead_build_fails_prover_path_too():
    """Le gate de build mort s'applique AUSSI au chemin prover (fail_on_sorry=False).

    Un build cassé ne doit JAMAIS valider l'intégrité, même dans le chemin prover
    qui préserve le vert historique sur sorryAx : le vert historique suppose un
    build vivant. returncode != 0 = défaillance, pas un gap de preuve.
    """
    r = _check_with_output(
        ["Knots.Basic.t1"], "", fail_on_sorry=False, returncode=2,
    )
    assert r["success"] is False
    assert r["error"] == "build_failed_returncode_2"


def test_dead_build_with_misleading_output_still_fails():
    """Si returncode != 0, on n'analyse même pas l'output (qui pourrait être
    partiel/muettoxique). On ne fait pas confiance à un process mort."""
    # output contient une ligne axiom valide, mais returncode=1 -> échec quand même
    out = _axiom_line("Knots.Basic.t1", ["Classical.choice", "propext"])
    r = _check_with_output(
        ["Knots.Basic.t1"], out, fail_on_sorry=True, returncode=1,
    )
    assert r["success"] is False
    assert r["error"] == "build_failed_returncode_1"
    assert r["axioms"] == []
