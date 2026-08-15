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


# ── #10486: Lean identifiers are Unicode, the enumerator was ASCII-only ────

def test_enumeration_keeps_subscripts_and_suffixed_names(tmp_path):
    """Truncation mode of #10486: an ASCII class cuts the name mid-identifier.

    ``mapsElations₂_gen1`` was enumerated as ``mapsElations`` -- the ``₂``
    (U+2082) ended the match. The truncated name reaches ``#print axioms``,
    Lean answers ``unknown constant``, and #8681 voids the whole module: that
    is the red observed on ``galois_lean``'s ``Sporadic.L34``.

    The ``!``/``?`` suffixes truncate the same way. See the companion test
    below for why that case is quieter, and worse.
    """
    src = (
        "namespace Sporadic.L34\n"
        "theorem mapsElations₂_gen1 : True := trivial\n"
        "theorem h₁₂ : True := trivial\n"
        "def parseRLE! (s : String) : Nat := 0\n"
        "def head? (l : List Nat) : Option Nat := none\n"
        "end Sporadic.L34\n"
    )
    (tmp_path / "M.lean").write_text(src, encoding="utf-8")
    assert _enumerate_module_declarations(tmp_path, "M") == [
        "Sporadic.L34.mapsElations₂_gen1",
        "Sporadic.L34.h₁₂",
        "Sporadic.L34.parseRLE!",
        "Sporadic.L34.head?",
    ]


def test_enumeration_sees_names_starting_with_a_greek_letter(tmp_path):
    """Silent half of #10486, and the dangerous one.

    A name whose FIRST character is non-ASCII matched nothing at all, so the
    declaration was never enumerated -- and a declaration that is never
    enumerated is never axiom-checked. Nothing goes red: a ``sorry`` inside
    ``π`` would have sailed through the gate. Measured on ``sensitivity_lean``,
    which holds ``π``, ``ε`` and ``dualBases_e_ε``.
    """
    src = (
        "namespace Sens\n"
        "def π : Nat := 3\n"
        "def ε : Nat := 0\n"
        "theorem dualBases_e_ε : True := trivial\n"
        "end Sens\n"
    )
    (tmp_path / "M.lean").write_text(src, encoding="utf-8")
    assert _enumerate_module_declarations(tmp_path, "M") == [
        "Sens.π",
        "Sens.ε",
        "Sens.dualBases_e_ε",
    ]


def test_enumeration_bang_variant_is_not_aliased_onto_its_sibling(tmp_path):
    """The quiet mode of #10486, and the one that keeps a gate falsely green.

    ``foo`` / ``foo!`` / ``foo?`` is a standard Lean idiom, so a truncation very
    often lands on a *real* neighbouring declaration instead of on nothing. That
    is the case live on ``main``: ``conway_lean``'s ``Conway.Life.RLE`` -- which
    IS in the wired, blocking ``target-modules`` of ``lean-conway.yml`` --
    declares ``parseRLE`` (line 188) and ``parseRLE!`` (line 199). The
    enumerator emitted ``parseRLE`` twice and ``parseRLE!`` never, so the gate
    checked one declaration twice, reported green, and never once inspected the
    axiom closure of the other. No red, no signal, a hole.

    Both must be emitted, distinctly.
    """
    src = (
        "namespace Conway.Life.RLE\n"
        "def parseRLE (s : String) : Except String Nat := .ok 0\n"
        "def parseRLE! (s : String) : Nat := 0\n"
        "end Conway.Life.RLE\n"
    )
    (tmp_path / "M.lean").write_text(src, encoding="utf-8")
    decls = _enumerate_module_declarations(tmp_path, "M")
    assert decls == [
        "Conway.Life.RLE.parseRLE",
        "Conway.Life.RLE.parseRLE!",
    ]
    assert len(set(decls)) == 2, "the ! variant must not collapse onto its sibling"


def test_enumeration_tracks_an_accented_namespace(tmp_path):
    """#10486, third site: a truncated NAMESPACE mis-qualifies its contents.

    ``namespace imbriqué`` (real, in ``conway_lean``'s ``Conway.Doomsday``)
    opened as ``imbriqu``. The stack itself stays balanced -- ``end imbriqué``
    truncates identically, so the push and the pop agree -- which is precisely
    why this went unnoticed: nothing looks structurally wrong. The damage is the
    prefix handed to every declaration *inside* the block, which becomes a name
    Lean does not know.
    """
    src = (
        "namespace imbriqué\n"
        "theorem inside : True := trivial\n"
        "end imbriqué\n"
        "theorem after : True := trivial\n"
    )
    (tmp_path / "M.lean").write_text(src, encoding="utf-8")
    assert _enumerate_module_declarations(tmp_path, "M") == [
        "imbriqué.inside",
        "after",
    ]


def test_enumeration_name_quantifier_stays_greedy(tmp_path):
    """Guards the fix against the lazy-quantifier "fix".

    Making the name quantifier lazy (``*?``) satisfies every Unicode example
    above while collapsing each name to its first character -- turning a handful
    of phantom names into *all* names phantom. This pins the greedy behaviour so
    that regression cannot land silently.
    """
    src = "theorem MapsElations : True := trivial\n"
    (tmp_path / "M.lean").write_text(src, encoding="utf-8")
    assert _enumerate_module_declarations(tmp_path, "M") == ["MapsElations"]


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


def test_no_declarations_ci_gate_fails_loud(tmp_path):
    """CI gate: an empty enumeration the gate cannot explain still fails loud.

    The verdict is unchanged since #8677; only the *reason* is now specific
    (here: the source file does not exist at all), so a red says which hole it
    is instead of blaming the parser generically.
    """
    r = _check_with_output([], "", fail_on_sorry=True, project_dir=str(tmp_path))
    assert r["success"] is False
    assert r["error"] == "source_not_found"
    assert r["empty_reason"] == "source_not_found"
    assert r["enumerated"] is False


def test_no_declarations_prover_path_stays_green(tmp_path):
    r = _check_with_output([], "", fail_on_sorry=False, project_dir=str(tmp_path))
    assert r["success"] is True
    assert r["enumerated"] is False
    assert r["empty_reason"] == "source_not_found"


# ──────────────────────────────────────────────────────────────────────────
# Empty enumeration: five causes, ONE pass (ai-01 c.63, #8677 / #8782)
#
# ``_enumerate_module_declarations`` returns ``[]`` both when the gate CANNOT
# RUN and when the module GENUINELY DECLARES NOTHING. Merging them into a single
# ``no_declarations_enumerated`` failure is what forced ``target-modules`` to be
# hand-curated (5 of 14 modules for knot, 2 of 26 for conway) instead of a
# lakefile glob -- an aggregator like ``Knots.lean`` or ``Conway.lean`` made the
# whole gate red. These tests pin each cause to its verdict.
#
# Nothing is mocked below: every empty-enumeration case returns before the
# ``lake env lean`` call, so the real enumerator, the real classifier and the
# real branch run against a real fixture on disk. A mock here would prove the
# mock.
# ──────────────────────────────────────────────────────────────────────────

def _lake_fixture(tmp_path: Path, module: str, src: str) -> Path:
    """Write ``src`` as ``module`` inside a minimal lake root, return the root.

    The ``lakefile.lean`` makes ``_has_lakefile`` true so ``check_axioms`` does
    not re-root upward out of the fixture.
    """
    (tmp_path / "lakefile.lean").write_text("-- fixture\n", encoding="utf-8")
    dest = tmp_path / (module.replace(".", "/") + ".lean")
    dest.parent.mkdir(parents=True, exist_ok=True)
    dest.write_text(src, encoding="utf-8")
    return tmp_path


def _check_real(tmp_path: Path, module: str, src: str, *, fail_on_sorry: bool):
    root = _lake_fixture(tmp_path, module, src)
    return LeanVerifier(str(root)).check_axioms(module, fail_on_sorry=fail_on_sorry)


@pytest.mark.parametrize("fail_on_sorry", [True, False])
def test_declaration_free_aggregator_passes(tmp_path, fail_on_sorry):
    """A root aggregator (imports + docstring, zero declarations) is a PASS.

    This is the shape ``code-style.md`` already names as legitimate -- "les
    *root aggregators* (ex. ``CooperativeGames.lean``, ``Grothendieck.lean``,
    ``Finiteness.lean`` -- imports-only + docstring FR, 0 declaration) sont
    FR-only *by design*". With zero declarations there is nothing that could
    depend on ``sorryAx`` and no axiom to whitelist: the module is vacuously
    clean, and failing it was a false red on both paths.
    """
    src = (
        "import Grothendieck.SheafBasics\n"
        "import Grothendieck.SieveOps\n"
        "\n"
        "/-!\n"
        "# Grothendieck : point d'entree du lake\n"
        "Ce module n'expose que des imports.\n"
        "-/\n"
    )
    r = _check_real(tmp_path, "Grothendieck", src, fail_on_sorry=fail_on_sorry)
    assert r["success"] is True
    assert r["empty_reason"] == "declaration_free_module"
    assert r["enumerated"] is False
    assert r["has_sorry"] is False
    assert r["forbidden"] == []


def test_mathlib_cartography_module_passes(tmp_path):
    """``#check @...`` is a *command*, not a declaration (``Grothendieck/MathlibMap.lean``).

    A cartography module maps what Mathlib already provides; it declares
    nothing of its own, so ``#print axioms`` has no name to ask about. Same
    shape in the already-wired ``conway_lean/Conway/MathlibMap.lean``.
    """
    src = (
        "import Mathlib.CategoryTheory.Sites.Sieves\n"
        "\n"
        "/-- Un index vivant de ce que Mathlib 4 fournit. -/\n"
        "#check @CategoryTheory.Sieve.pullback\n"
        "#check @CategoryTheory.Sieve.pullback_inter\n"
    )
    r = _check_real(tmp_path, "Grothendieck.MathlibMap", src, fail_on_sorry=True)
    assert r["success"] is True
    assert r["empty_reason"] == "declaration_free_module"


def test_prose_module_with_only_bindings_passes(tmp_path):
    """``namespace`` / ``open`` / ``variable`` bind names but declare nothing.

    The shape of ``Grothendieck/DirectImage.lean``: prose plus the binders that
    let the prose typecheck, bridging to Mathlib's own ``pushforward`` /
    ``pullback``. Zero declarations, therefore zero axioms to audit.
    """
    src = (
        "import Mathlib.CategoryTheory.Sites.Sheaf\n"
        "\n"
        "namespace Grothendieck\n"
        "open CategoryTheory\n"
        "variable {C D : Type*} [Category C] [Category D]\n"
        "end Grothendieck\n"
    )
    r = _check_real(tmp_path, "Grothendieck.DirectImage", src, fail_on_sorry=True)
    assert r["success"] is True
    assert r["empty_reason"] == "declaration_free_module"


def test_declaration_keyword_inside_comment_stays_declaration_free(tmp_path):
    """Prose beginning with ``theorem`` must not fake a declaration (#8722 dual).

    #8722 fixed the enumerator so docstring prose at column 0 is no longer
    enumerated as a phantom declaration. The classifier reuses the same
    comment-stripped text and the same ``_DECL_HEAD_RE``, so a module whose only
    ``theorem``-looking lines are prose is genuinely declaration-free -- it must
    not be re-routed to a fail-loud reason by a second, sloppier parser.
    """
    src = (
        "import Knots.Basic\n"
        "/-!\n"
        "theorem statement working for *any* KnotDiagram is deferred here.\n"
        "def the reader should consult Knots.Basic instead.\n"
        "-/\n"
    )
    r = _check_real(tmp_path, "Knots", src, fail_on_sorry=True)
    assert r["success"] is True
    assert r["empty_reason"] == "declaration_free_module"


_OPEN_EXAMPLE = (
    "import Mathlib.Tactic\n"
    "/-- Un exemple laisse ouvert. -/\n"
    "example : True := by sorry\n"
)


def test_sorry_without_declaration_fails_the_ci_gate(tmp_path):
    """A live ``sorry`` with no declaration must NOT ride the pass out.

    ``example`` is deliberately excluded from enumeration (it may be anonymous),
    so ``example : True := by sorry`` yields an empty enumeration -- and
    ``#print axioms`` can never see it either, since it defines no constant.
    Letting it through the declaration-free pass would be a green over an
    unexamined ``sorry``, the exact failure #8677 exists to prevent. This is
    what makes "the declaration-free pass cannot mask a sorry" an enforced
    invariant rather than an argument.
    """
    r = _check_real(tmp_path, "Knots.Scratch", _OPEN_EXAMPLE, fail_on_sorry=True)
    assert r["success"] is False
    assert r["error"] == "sorry_without_declaration"
    assert r["empty_reason"] == "sorry_without_declaration"
    assert r["has_sorry"] is True


def test_sorry_without_declaration_prover_path_reports_but_stays_green(tmp_path):
    """Same source, prover path: flagged, not fatal -- like ``sorryAx`` is.

    The module already draws this line for the axiom output (a ``sorryAx`` sets
    ``has_sorry`` and fails only under ``fail_on_sorry``); a textual sorry in a
    declaration-free source is reported through the *same* field so the two
    cannot diverge. Level 2 tracks sorry textually, so Level 3 stays green.
    """
    r = _check_real(tmp_path, "Knots.Scratch", _OPEN_EXAMPLE, fail_on_sorry=False)
    assert r["success"] is True
    assert r["has_sorry"] is True
    assert r["empty_reason"] == "sorry_without_declaration"


def test_sorry_in_docstring_prose_does_not_trip_the_guard(tmp_path):
    """The guard runs on comment-STRIPPED text, so prose about sorries is fine.

    Live shape, measured 2026-07-30: all three declaration-free Grothendieck
    modules contain the token ``sorry`` -- inside ``Tous les `sorry`s elimines a
    la creation``. A guard that read raw source would fail exactly the modules
    this change exists to unblock, and would do it while quoting their own
    claim of cleanliness back at them.
    """
    src = (
        "import Grothendieck.SheafBasics\n"
        "/-!\n"
        "# Cartographie\n"
        "Epic #1646. Tous les `sorry`s elimines a la creation.\n"
        "-/\n"
    )
    r = _check_real(tmp_path, "Grothendieck.SchemesTour", src, fail_on_sorry=True)
    assert r["success"] is True
    assert r["empty_reason"] == "declaration_free_module"


def test_all_private_module_fails_loud_with_its_own_reason(tmp_path):
    """All-private is NOT declaration-free -- it is a genuine blind spot.

    ``private`` names are skipped by the enumerator (#8722: Lean mangles them to
    ``_private.<Module>.<hash>.<name>``, so ``#print axioms`` answers ``unknown
    constant``). A module whose declarations are *all* private therefore
    enumerates empty while having real content -- and ``private`` being
    module-scoped, the public declarations that would reach those axioms
    transitively cannot live outside this module. The gate genuinely cannot see
    them, so it must say so rather than pass.
    """
    src = (
        "namespace Knots\n"
        "private theorem mem_set_fwd : True := trivial\n"
        "private noncomputable def hidden : Nat := 0\n"
        "end Knots\n"
    )
    r = _check_real(tmp_path, "Knots.Invariant", src, fail_on_sorry=True)
    assert r["success"] is False
    assert r["error"] == "all_private_declarations"
    assert r["enumerated"] is False


def test_all_private_module_prover_path_stays_green(tmp_path):
    """The prover path keeps its historical green on a gate-cannot-run reason.

    Level 2 tracks sorry textually, so Level 3 must not flip red on a blind
    spot (#8677). Only the CI gate (``fail_on_sorry=True``) fails loud here --
    unlike ``sorry_without_declaration`` above, which fails on both paths
    because it is a live defect rather than a blind spot.
    """
    src = "private theorem hidden : True := trivial\n"
    r = _check_real(tmp_path, "Knots.Invariant", src, fail_on_sorry=False)
    assert r["success"] is True
    assert r["empty_reason"] == "all_private_declarations"


def test_parse_gap_is_the_drift_alarm(tmp_path):
    """``no_declarations_enumerated`` now means "the two parsers disagreed".

    The classifier matches on ``_DECL_HEAD_RE`` -- the *same* regex the
    enumerator uses -- so while they agree this verdict is unreachable: any
    source with a non-private declaration head makes the enumerator return that
    declaration, never an empty list. That is the point. The branch is the alarm
    for the day someone adds a filter to one and not the other; it stays
    fail-loud so the drift surfaces as a red rather than as a silent green.

    Asserted directly on the classifier, since no fixture can reach it through
    ``check_axioms`` today -- claiming otherwise would need a mock, and a mocked
    disagreement proves nothing about the real one.
    """
    root = _lake_fixture(
        tmp_path,
        "Knots.Mixed",
        "private theorem hidden : True := trivial\ntheorem visible : True := trivial\n",
    )
    # Precondition: with both parsers in agreement, this source enumerates.
    assert _enumerate_module_declarations(root, "Knots.Mixed") == ["visible"]
    # The classifier's verdict IF it were ever reached on such a source.
    assert lean_server._classify_empty_enumeration(root, "Knots.Mixed") == (
        "no_declarations_enumerated"
    )


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


# ──────────────────────────────────────────────────────────────────────────
# Multi-line wrapped axiom list (#8738) — the dangerous class the gate was blind to
# ──────────────────────────────────────────────────────────────────────────

# The end-to-end gate test below reuses ``REAL_MULTILINE_NATIVE_DECIDE_OUTPUT``
# (defined further down — verbatim Lean output exposing #8738): a long axiom name
# (``<decl>._native.native_decide.ax_1_1``) wraps the bracketed list across lines
# without re-emitting the ``'decl' depends on axioms:`` prefix, which the old
# line-by-line parser (#8681) silently dropped. Fix #8740 (``re.finditer`` on the
# full output) lets ``[^\]]*`` span newlines. The unit-parser coverage of this
# shape (same fixture) lives in ``test_extract_axioms_handles_multiline_lists``.


def test_check_axioms_multiline_native_decide_fails_gate():
    """#8738 criterion 2 (end-to-end): the gate fails on a native_decide multi-line list.

    Before #8740, the line-by-line parser returned ``forbidden=[]`` on this
    output, so ``success=True``: the gate certified a module that genuinely
    depends on ``native_decide`` -- the failure mode the gate exists to catch.
    The three standard axioms are in the default whitelist, so only the
    ``native_decide`` axiom is forbidden, which must drive ``success`` to
    False. This is the end-to-end gate test the issue's acceptance criterion 2
    asks for.
    """
    # Uses the DEFAULT whitelist (no explicit whitelist kwarg), unlike
    # ``test_real_lean_output_fails_when_native_decide_not_whitelisted`` which
    # passes one explicitly. Two distinct code paths: if the default whitelist
    # is broken, only this test catches it.
    r = _check_with_output(
        ["Knots.figureEight_not_tricolorable"],
        REAL_MULTILINE_NATIVE_DECIDE_OUTPUT,
        fail_on_sorry=True,
    )
    assert r["success"] is False
    assert len(r["forbidden"]) == 1
    assert "native_decide" in r["forbidden"][0]


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


# ──────────────────────────────────────────────────────────────────────────
# #8738 — multi-line axiom lists (Lean's pretty-print wraps long names)
# ──────────────────────────────────────────────────────────────────────────

# Verbatim output from ai-01's reproduction on knot_lean/Knots.Invariant:1054,
# BEFORE the #8731 elimination of native_decide (msg-20260728T165702 in #8738).
# The four axioms (propext, Classical.choice, Quot.sound, plus the
# native_decide witness) overflow Lean's ~100-col pretty-printer, so Lean
# wraps the list across continuation lines WITHOUT re-emitting the
# "'Knots...' depends on axioms:" prefix. Iterating line-by-line (#8681)
# drops the declaration entirely; re.finditer on the whole output lets
# [^\\]]* span newlines.
REAL_MULTILINE_NATIVE_DECIDE_OUTPUT = (
    "'Knots.figureEight_not_tricolorable' depends on axioms: [propext,\n"
    " Classical.choice,\n"
    " Quot.sound,\n"
    " Knots.figureEight_not_tricolorable._native.native_decide.ax_1_1]\n"
)


def test_extract_axioms_handles_multiline_lists():
    """#8738 — la regex doit capturer les axiomes sur les listes multi-lignes.

    Format reel de Lean quand la liste d'axiomes depasse la largeur
    pretty-print (~100 colonnes) : ``'Knots.X' depends on axioms: [A,\n
    B,\n C,\n D]`` -- continuation sans re-emission du prefixe. L'iteration
    ligne-a-ligne de #8681 ratait les 3 lignes de continuation ; le fix
    ``re.finditer`` traverse les newlines via ``[^\\]]*``.
    """
    axioms = LeanVerifier._extract_axioms(REAL_MULTILINE_NATIVE_DECIDE_OUTPUT)
    assert set(axioms) == {
        "propext",
        "Classical.choice",
        "Quot.sound",
        "Knots.figureEight_not_tricolorable._native.native_decide.ax_1_1",
    }, f"tous les axiomes multi-lignes doivent etre captures ; got {axioms!r}"


def test_extract_axioms_mixed_single_and_multiline_lists():
    """#8738 — mix single-line et multi-line dans la meme sortie.

    Le cas reel : ``Knots.Invariant`` a 31 declarations, la majorite
    tient sur une ligne, mais celle qui utilise ``native_decide`` wrappe.
    La regex doit traiter les deux formes sans confusion.
    """
    out = (
        _axiom_line("Knots.mirror_wf_preserves", ["propext", "Quot.sound"])
        + "\n"
        + REAL_MULTILINE_NATIVE_DECIDE_OUTPUT
    )
    axioms = LeanVerifier._extract_axioms(out)
    assert "Knots.figureEight_not_tricolorable._native.native_decide.ax_1_1" in axioms, (
        f"l'axiome multi-ligne doit etre capture ; got {axioms!r}"
    )
    assert "propext" in axioms and "Quot.sound" in axioms


def test_real_lean_output_fails_when_native_decide_not_whitelisted():
    """#8738 — gate E2E rougit sur le module contenant ``native_decide``.

    Test bout-en-bout qui valide le critere d'acceptance de #8738 :
    ``check_axioms`` sur la sortie verbatim ci-dessus doit retourner
    ``success: False`` avec l'axiome natif dans ``forbidden``, sans meme
    avoir besoin d'un vrai build Lean (la sortie reelle suffit).
    """
    decls = ["Knots.figureEight_not_tricolorable"]
    whitelist = [
        "Classical.choice", "propext", "funext",
        "Quot.lift", "Quot.mk", "Quot.sound",
        # Knots.figureEight_not_tricolorable._native.native_decide.ax_1_1
        # deliberement omis -> gate rouge
    ]
    r = _check_with_output(decls, REAL_MULTILINE_NATIVE_DECIDE_OUTPUT,
                           fail_on_sorry=True, whitelist=whitelist)
    assert r["success"] is False
    assert "Knots.figureEight_not_tricolorable._native.native_decide.ax_1_1" in r["forbidden"], (
        f"native_decide doit apparaitre dans forbidden ; got {r['forbidden']!r}"
    )
