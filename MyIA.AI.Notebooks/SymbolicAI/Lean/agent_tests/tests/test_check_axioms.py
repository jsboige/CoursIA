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
    """Build a ``#print axioms`` line as Lean actually emits it.

    Lean 4 emits ``'Foo.bar' depends on axioms: [A, B, C]`` (with a colon
    before the bracketed list). The previous no-colon form
    (``depends on axioms [...]``) matched only the test fixture and never
    the real output -- the regex in ``lean_server.py`` is now anchored on
    the literal colon, and the fixture follows suit so a change in Lean's
    output format would break the test (#8677 criterion 4).
    """
    inner = ", ".join(axioms) if axioms else ""
    return f"{Q}{name}{Q} depends on axioms: [{inner}]"


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


# ── #8722: the two defects that made the gate false-fail ──────────────────

def test_enumeration_dotted_name_inside_namespace_is_qualified(tmp_path):
    """#8722 cause 1: a dotted source name in a namespace is NOT absolute.

    ``def Knot.crossingNumber`` written inside ``namespace Knots`` declares
    ``Knots.Knot.crossingNumber`` -- the old ``if "." in name`` heuristic
    emitted the bare ``Knot.crossingNumber`` (unknown to Lean), failing the
    whole module's axiom check.
    """
    src = (
        "namespace Knots\n"
        "def Knot.crossingNumber (k : Nat) : Nat := 0\n"
        "def KnotDiagram.edges (d : Nat) : List Nat := []\n"
        "end Knots\n"
    )
    (tmp_path / "Knots").mkdir()
    (tmp_path / "Knots" / "Basic.lean").write_text(src, encoding="utf-8")
    decls = _enumerate_module_declarations(tmp_path, "Knots.Basic")
    assert decls == ["Knots.Knot.crossingNumber", "Knots.KnotDiagram.edges"]


def test_enumeration_ignores_docstring_prose_at_column_zero(tmp_path):
    """#8722 cause 2: docstring prose starting with a decl keyword is a phantom.

    A ``/- ... lemma statement working for *any* KnotDiagram ... -/`` block is
    prose, not a declaration. Before comment-stripping it was enumerated as
    ``Knots.statement`` (unknown), failing the module. The fix reuses
    ``strip_lean_comments`` (same helper as ``count_real_sorries``, #6171).
    """
    src = (
        "namespace Knots\n"
        "/-! ## 13. Polymorphic section\n"
        "\n"
        "lemma statement working for *any* KnotDiagram whose well-formedness\n"
        "theorem at the same time it proves it (the lemma + body are inseparable).\n"
        "-/\n"
        "theorem real_lemma : True := trivial\n"
        "end Knots\n"
    )
    (tmp_path / "Knots").mkdir()
    (tmp_path / "Knots" / "Basic.lean").write_text(src, encoding="utf-8")
    decls = _enumerate_module_declarations(tmp_path, "Knots.Basic")
    # The two prose lines ("lemma statement...", "theorem at the same time...")
    # must NOT appear; only the real declaration survives, properly qualified.
    assert decls == ["Knots.real_lemma"]


def test_enumeration_root_prefix_strips_to_absolute(tmp_path):
    """``_root_.`` is the ONLY absolute escape in Lean 4 (#8722 cause 1, edge).

    ``def _root_.globalName`` inside any namespace still declares ``globalName``
    at the root, unqualified.
    """
    src = (
        "namespace Knots\n"
        "def _root_.globalHelper : Nat := 0\n"
        "def _root_.Outer.inner : Nat := 0\n"
        "theorem local_thm : True := trivial\n"
        "end Knots\n"
    )
    (tmp_path / "Knots").mkdir()
    (tmp_path / "Knots" / "Basic.lean").write_text(src, encoding="utf-8")
    decls = _enumerate_module_declarations(tmp_path, "Knots.Basic")
    assert decls == ["globalHelper", "Outer.inner", "Knots.local_thm"]


def test_enumeration_end_pops_only_on_a_name_match(tmp_path):
    """An unmatched ``end`` must NOT pop the namespace stack (#8722).

    ``namespace`` is the only construct the enumerator pushes, but ``end``
    closes others too (``section Foo ... end Foo``), and one can survive
    comment stripping. Popping unconditionally unbalances the stack and
    under-qualifies every declaration that follows -- which ``#print axioms``
    then reports as an unknown constant, failing the whole module.

    Authored by po-2023:CoursIA-2 in #8726; carried here after #8725 shipped
    the same repair without this case.
    """
    src = (
        "namespace Outer\n"
        "namespace Inner\n"
        "theorem deep : True := trivial\n"
        "end Other\n"  # closes nothing we opened -- must not pop Inner
        "theorem still_inner : True := trivial\n"
        "end Inner\n"
        "theorem back_in_outer : True := trivial\n"
        "end Outer\n"
    )
    (tmp_path / "Knots").mkdir()
    (tmp_path / "Knots" / "Basic.lean").write_text(src, encoding="utf-8")
    decls = _enumerate_module_declarations(tmp_path, "Knots.Basic")
    assert decls == [
        "Outer.Inner.deep",
        "Outer.Inner.still_inner",
        "Outer.back_in_outer",
    ]


def test_enumeration_skips_private_declarations(tmp_path):
    """``private`` names are not addressable, so they must not be emitted (#8722).

    Lean 4 mangles a private declaration to ``_private.<Module>.<hash>.<name>``.
    Emitting the source name makes ``#print axioms`` answer ``unknown constant``
    and fails the ENTIRE module -- observed on ``Knots.Invariant``, whose three
    private list helpers (``mem_set_fwd``, ``mem_drop_out``, ``mem_set_self``)
    sank a module in which every public theorem had checked out fine.

    The other modifiers must keep working: ``protected``/``noncomputable``/
    ``partial`` names stay addressable and must still be enumerated.
    """
    src = (
        "namespace Knots\n"
        "private theorem mem_set_fwd : True := trivial\n"
        "theorem public_thm : True := trivial\n"
        "private noncomputable def hidden : Nat := 0\n"
        "protected theorem prot_thm : True := trivial\n"
        "noncomputable def slow : Nat := 0\n"
        "end Knots\n"
    )
    (tmp_path / "Knots").mkdir()
    (tmp_path / "Knots" / "Basic.lean").write_text(src, encoding="utf-8")
    decls = _enumerate_module_declarations(tmp_path, "Knots.Basic")
    assert decls == ["Knots.public_thm", "Knots.prot_thm", "Knots.slow"]


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

def _check_with_output(decls, fake_stdout, *, fail_on_sorry=False, project_dir=".",
                        returncode=0, whitelist=None):
    verifier = LeanVerifier(project_dir)
    with patch.object(lean_server, "_enumerate_module_declarations", return_value=decls), \
            patch.object(lean_server, "_resolve_lake_command", return_value=(["lean"], {})), \
            patch.object(lean_server.subprocess, "run",
                         return_value=_FakeCompletedProcess(fake_stdout, returncode=returncode)):
        return verifier.check_axioms("Knots.Basic", fail_on_sorry=fail_on_sorry,
                                     whitelist=whitelist)


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


# ──────────────────────────────────────────────────────────────────────────
# Real Lean output (verbatim, c.938v5 #8677 criterion 4 — anchor the regex)
# ──────────────────────────────────────────────────────────────────────────

# Real Lean 4 #print axioms output for knot_lean/Knots.Basic, captured by
# ai-01's rebuild on 2026-07-28 (msg-20260728T165702). Test must break if
# Lean changes the format -- if it doesn't, the test doesn't test Lean.
REAL_KNOTS_BASIC_OUTPUT = (
    "'Knots.mirror_wf_preserves' depends on axioms: [propext, Quot.sound]\n"
    "'Knots.mirror_edges_perm'   depends on axioms: [propext, Quot.sound]\n"
    "'Knots.count_lift_append'   depends on axioms: [propext, Quot.sound]\n"
    "'Knots.unknot_wf' does not depend on any axioms\n"
)


def test_extract_axioms_handles_real_lean_format():
    """La regex doit matcher le format REEL de Lean (avec deux-points).

    C'est précisément le cas qui a faussé le gate en c.938v4 : la regex
    ``r"depends on axioms \\[([^\\]]*)\\]"`` (sans deux-points) matchait
    uniquement la fixture de test et rendait ``[]`` sur toute sortie Lean
    reelle -> ``forbidden=[]``, ``success=True`` structurellement. PR #8681
    c.938v5 ancre la regex sur le deux-points et la fixture suit.
    """
    from lean_server import LeanVerifier

    axioms = LeanVerifier._extract_axioms(REAL_KNOTS_BASIC_OUTPUT)
    # mirror_wf_preserves / mirror_edges_perm / count_lift_append -> propext + Quot.sound
    assert set(axioms) == {"propext", "Quot.sound"}
    assert "unknot_wf" not in axioms  # "does not depend on any axioms" emits nothing


def test_real_lean_output_passes_whitelist_with_quot_sound():
    """Sur la sortie reelle, gate SUCCESS une fois Quot.sound whitelisté.

    C'est la validation qui manquait en c.938v4 : prouver que le gate peut
    rougir ET verdir sur du Lean réel, pas seulement sur des fixtures.
    """
    r = _check_with_output(
        ["Knots.mirror_wf_preserves", "Knots.mirror_edges_perm",
         "Knots.count_lift_append", "Knots.unknot_wf"],
        REAL_KNOTS_BASIC_OUTPUT,
        fail_on_sorry=True,
        whitelist=[
            "Classical.choice", "propext", "funext",
            "Quot.lift", "Quot.mk", "Quot.sound",
        ],
    )
    assert r["success"] is True
    assert set(r["axioms"]) == {"propext", "Quot.sound"}
    assert r["forbidden"] == []  # propext + Quot.sound whitelisted
    assert r["has_sorry"] is False


def test_real_lean_output_fails_when_quot_sound_not_whitelisted():
    """Même sortie reelle, whitelist SANS Quot.sound -> rouge.

    C'est le test « deliberement casse » : si on retire une entree de la
    whitelist par accident, le gate rougit sur la sortie Lean reelle. Le
    test verifie que la regex capture bien ``Quot.sound`` (sinon le test
    passerait au vert, prouvant que le gate est cassé).
    """
    r = _check_with_output(
        ["Knots.mirror_wf_preserves", "Knots.mirror_edges_perm",
         "Knots.count_lift_append", "Knots.unknot_wf"],
        REAL_KNOTS_BASIC_OUTPUT,
        fail_on_sorry=True,
        whitelist=[
            "Classical.choice", "propext", "funext",
            "Quot.lift", "Quot.mk",
            # Quot.sound deliberately omitted
        ],
    )
    assert r["success"] is False
    assert "Quot.sound" in r["forbidden"], (
        f"Quot.sound must appear in forbidden when not whitelisted; got {r['forbidden']!r}"
    )


def test_extract_axioms_does_not_match_no_colon_format():
    """Une fixture no-colon ne doit PAS matcher la nouvelle regex.

    Test anti-régression : si quelqu'un re-introduit le format sans
    deux-points (l'ancien comportement buggy), ce test le détecte.
    """
    from lean_server import LeanVerifier

    no_colon_fixture = "'Foo.bar' depends on axioms [propext, Quot.sound]"
    axioms = LeanVerifier._extract_axioms(no_colon_fixture)
    # Sans deux-points, Lean n'aurait jamais émis ça -- la regex doit retourner []
    assert axioms == [], (
        f"La regex anchored sur ':' ne doit PAS matcher le format obsolète ; got {axioms!r}"
    )
