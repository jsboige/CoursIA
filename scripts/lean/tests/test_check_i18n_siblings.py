#!/usr/bin/env python3
"""Tests for check_i18n_siblings.py (Lean i18n #4980 sibling byte-identity).

Dual-mode: runnable directly (``python scripts/lean/tests/test_check_i18n_siblings.py``)
or under pytest (auto-collected by scripts-tests.yml on any ``scripts/**`` change).
"""
from __future__ import annotations

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from check_i18n_siblings import (  # noqa: E402
    _drift_detail,
    check_en_built,
    check_pair,
    enclosing_lake,
    find_en_files,
    fr_import_siblings,
    fr_sibling,
    imports_fr_sibling,
    is_half_done,
    is_repo_boilerplate,
    main,
    normalize_body,
    split_decls,
    strip_comments,
)

REPO_ROOT = Path(__file__).resolve().parents[3]
# Le lake a descendu sous `Lean/GOL/` (#23164). Ce chemin est en dur : s'il
# n'est pas suivi, la garde ne trouve plus le lake et se tait (cf. le `skip`
# explicite du test conway ci-dessous, qui rend cette disparition visible).
CONWAY_DIR = (
    REPO_ROOT
    / "MyIA.AI.Notebooks" / "SymbolicAI" / "Lean" / "GOL" / "conway_lean" / "Conway"
)


def test_strip_comments_removes_block_line_and_docstring():
    src = (
        '/-- doc -/\n'
        'def f := 1 -- trailing comment\n'
        '/- multi\nline block -/\n'
        'def g := 2\n'
    )
    out = strip_comments(src)
    assert "doc" not in out
    assert "trailing comment" not in out
    assert "multi" not in out and "block" not in out
    assert "def f := 1" in out
    assert "def g := 2" in out


def test_strip_comments_nested_block():
    src = "/- outer /- inner -/ still outer -/def h := 3\n"
    out = strip_comments(src)
    assert "outer" not in out and "inner" not in out
    assert "def h := 3" in out


def test_strip_comments_preserves_string_with_double_dash():
    # A "--" inside a string literal must NOT be treated as a line comment.
    src = 'def s := "a -- b"\ndef t := 4\n'
    out = strip_comments(src)
    assert '"a -- b"' in out
    assert "def t := 4" in out


def test_normalize_drops_structural_lines():
    fr = (
        "import Mathlib.Data.List.Basic\n"
        "namespace Conway\n"
        "def f (n : Nat) := n + 1\n"
        "end Conway\n"
    )
    en = (
        "import Conway.Foo\n"
        "namespace Conway_en\n"
        "open Conway\n"
        "def f (n : Nat) := n + 1\n"
        "end Conway_en\n"
    )
    assert normalize_body(fr) == normalize_body(en)


def test_normalize_ignores_docstring_language():
    fr = "/-- Additionne un. -/\ndef f (n : Nat) := n + 1\n"
    en = "/-- Adds one. -/\ndef f (n : Nat) := n + 1\n"
    assert normalize_body(fr) == normalize_body(en)


def test_normalize_preserves_indentation_drift():
    # Tactic-block indentation is meaningful; a real indentation change must show.
    a = "theorem t : True := by\n  trivial\n"
    b = "theorem t : True := by\n    trivial\n"
    assert normalize_body(a) != normalize_body(b)


def test_normalize_collapses_en_suffix_variant():
    # prefixed-suffix variant (game_theory_lean): EN refers to `_en`-suffixed
    # entities; body must still compare equal to the FR canonical.
    fr = "def Efficiency (G : TUGame N) : Prop := G.v = 0\n"
    en = "def Efficiency (G : TUGame_en N) : Prop := G.v = 0\n"
    assert normalize_body(fr) == normalize_body(en)


def test_normalize_en_suffix_does_not_mask_real_drift():
    fr = "def f (G : TUGame N) : Nat := 42\n"
    en = "def f (G : TUGame_en N) : Nat := 43\n"
    assert normalize_body(fr) != normalize_body(en)


def test_fr_import_advisory_detects_only_declaring_same_lake_imports(tmp_path):
    lake = tmp_path / "fixture_lean"
    base = lake / "Alpha" / "Base.lean"
    base.parent.mkdir(parents=True)
    (lake / "lakefile.toml").write_text('name = "fixture"\n', encoding="utf-8")
    base.write_text("namespace Alpha.Base\ndef value := 1\n", encoding="utf-8")
    base.with_name("Base_en.lean").write_text(
        "namespace Alpha.Base_en\ndef value := 1\n", encoding="utf-8")
    alias_target = lake / "Alias.lean"
    alias_target.write_text("namespace Alias\ndef value := 1\n", encoding="utf-8")
    alias_target.with_name("Alias_en.lean").write_text(
        "namespace Alias_en\ndef value := 1\n", encoding="utf-8")

    hybrid = lake / "Alpha" / "Hybrid_en.lean"
    hybrid.write_text(
        "import Alpha.Base as Alias Mathlib.Data.Nat.Basic\n"
        "namespace Alpha.Hybrid_en\ndef own := Alpha.Base.value\n",
        encoding="utf-8",
    )
    assert fr_import_siblings(hybrid) == ["Alpha.Base"]

    # A prose-only mirror remains an exempt consumer, even with the same import.
    prose = lake / "Alpha" / "Prose_en.lean"
    prose.write_text(
        "import Alpha.Base\nnamespace Alpha.Prose_en\nend Alpha.Prose_en\n",
        encoding="utf-8",
    )
    assert fr_import_siblings(prose) == []

    # Declarations under an unsuffixed namespace do not meet the predicate.
    unsuffixed = lake / "Alpha" / "Unsuffixed_en.lean"
    unsuffixed.write_text(
        "import Alpha.Base\nnamespace Alpha.Unsuffixed\ndef own := 1\n",
        encoding="utf-8",
    )
    assert fr_import_siblings(unsuffixed) == []

    # External Mathlib modules and same-lake modules without twins are ignored.
    no_twin = lake / "Alpha" / "NoTwin.lean"
    no_twin.write_text("namespace Alpha.NoTwin\ndef value := 1\n", encoding="utf-8")
    no_twin_user = lake / "Alpha" / "NoTwinUser_en.lean"
    no_twin_user.write_text(
        "import Alpha.NoTwin Mathlib.Data.Nat.Basic\n"
        "namespace Alpha.NoTwinUser_en\ndef own := 1\n",
        encoding="utf-8",
    )
    assert fr_import_siblings(no_twin_user) == []


def test_fr_import_advisory_is_opt_in_and_non_gating(tmp_path, capsys):
    lake = tmp_path / "fixture_lean"
    module = lake / "Alpha" / "Hybrid_en.lean"
    module.parent.mkdir(parents=True)
    (lake / "lakefile.toml").write_text(
        'name = "fixture"\n[[lean_lib]]\nname = "Alpha"\nglobs = ["Alpha.*"]\n',
        encoding="utf-8",
    )
    (module.parent / "Base.lean").write_text("namespace Alpha.Base\ndef x := 1\n")
    (module.parent / "Base_en.lean").write_text("namespace Alpha.Base_en\ndef x := 1\n")
    (module.parent / "Hybrid.lean").write_text(
        "namespace Alpha.Hybrid\ndef x := 2\n", encoding="utf-8")
    module.write_text(
        "import Alpha.Base\nnamespace Alpha.Hybrid_en\ndef x := 2\n",
        encoding="utf-8",
    )

    assert main([str(module)]) == 0
    assert "FR-IMPORT" not in capsys.readouterr().out
    assert main([str(module), "--fr-import-advisory"]) == 0
    output = capsys.readouterr().out
    assert "FR-IMPORT" in output and "Alpha.Base" in output
    assert "advisory" in output


def test_check_pair_matching(tmp_path):
    fr = tmp_path / "Foo.lean"
    en = tmp_path / "Foo_en.lean"
    fr.write_text(
        "/-- Le module français. -/\n"
        "namespace Conway\n"
        "def answer : Nat := 42\n"
        "end Conway\n",
        encoding="utf-8",
    )
    en.write_text(
        "/-- The English mirror. -/\n"
        "import Conway.Foo\n"
        "namespace Conway_en\n"
        "open Conway\n"
        "def answer : Nat := 42\n"
        "end Conway_en\n",
        encoding="utf-8",
    )
    status, detail = check_pair(fr, en)
    assert status == "OK", detail


def test_check_pair_drift_detected(tmp_path):
    fr = tmp_path / "Bar.lean"
    en = tmp_path / "Bar_en.lean"
    fr.write_text("namespace Conway\ndef answer : Nat := 42\nend Conway\n",
                  encoding="utf-8")
    en.write_text("namespace Conway_en\ndef answer : Nat := 43\nend Conway_en\n",
                  encoding="utf-8")
    status, detail = check_pair(fr, en)
    assert status == "DRIFT"
    assert "42" in detail and "43" in detail


def test_drift_detail_lists_unique_blocks(tmp_path):
    """_drift_detail surfaces structural divergence directly: which declaration
    blocks exist ONLY in FR vs ONLY in EN. This replaces the noisy ``difflib``
    unified diff on bodies and is the actionable diagnostic for any reviewer
    investigating a DRIFT — no need to mentally diff two text dumps."""
    fr = tmp_path / "M.lean"
    en = tmp_path / "M_en.lean"
    fr.write_text(
        "namespace M\n"
        "def shared : Nat := 1\n"
        "def fr_only : Nat := 42\n"
        "end M\n",
        encoding="utf-8",
    )
    en.write_text(
        "namespace M\n"
        "def shared : Nat := 1\n"
        "def en_only : Nat := 99\n"
        "end M\n",
        encoding="utf-8",
    )
    status, detail = check_pair(fr, en)
    assert status == "DRIFT"
    assert "only in FR" in detail
    assert "fr_only" in detail
    assert "only in EN" in detail
    assert "en_only" in detail
    # The shared block must NOT appear in the diagnostic — it's not unique.
    assert "shared" not in detail


def test_drift_detail_handles_multiset_with_duplicates(tmp_path):
    """Multiset semantics: if FR has 2 copies of a block and EN has 1, the
    multiset difference FR−EN has the same block once (1 copy shared, 1 copy
    surplus). Critical for sibling pairs with repeated helper lemmas."""
    fr = tmp_path / "Dup.lean"
    en = tmp_path / "Dup_en.lean"
    fr.write_text(
        "namespace Dup\n"
        "def helper : Nat := 0\n"
        "def helper : Nat := 0\n"
        "def fr_extra : Nat := 7\n"
        "end Dup\n",
        encoding="utf-8",
    )
    en.write_text(
        "namespace Dup\n"
        "def helper : Nat := 0\n"
        "end Dup\n",
        encoding="utf-8",
    )
    fr_blocks = split_decls(normalize_body(fr.read_text(encoding="utf-8")))
    en_blocks = split_decls(normalize_body(en.read_text(encoding="utf-8")))
    detail = _drift_detail(
        fr_blocks, en_blocks, fr, en)
    # FR has {helper×2, fr_extra×1}, EN has {helper×1}.
    # Multiset diff FR−EN = {helper×1, fr_extra×1} → 2 blocks only in FR.
    assert "2 block(s) only in FR" in detail
    assert "fr_extra" in detail
    assert "helper" in detail
    # No block is unique to EN.
    assert "only in EN" not in detail


def test_drift_detail_multiset_match_returns_difflib_dump():
    """When multisets of declaration blocks match but bodies still diverge
    at line level (intra-block whitespace / indentation drift), fall back to
    a ``difflib`` dump so the diagnostic remains useful. Rare in practice but
    defensive: keep the door open."""
    fr_path = Path("/tmp/fr.lean")
    en_path = Path("/tmp/en.lean")
    # Same block content in both multisets — multiset equal but bodies could
    # differ at line level. Pass identical content to reach the fallback path
    # (multisets equal, parts empty → ``difflib`` dump returned).
    fr_blocks = ["def x : Nat :=\n  1"]
    en_blocks = ["def x : Nat :=\n  1"]
    detail = _drift_detail(fr_blocks, en_blocks, fr_path, en_path)
    # difflib unified diff on identical inputs returns empty list — empty
    # string from "\n".join([]). The diagnostic must remain non-crashing;
    # content is empty, but the function must not raise.
    assert isinstance(detail, str)


def test_reorder_stays_drift_not_ok(tmp_path):
    # #6731 ConeKernel doctrine guard. A pure reorder of otherwise
    # byte-identical declaration blocks is a REPAIRABLE divergence: #6731
    # moved the EN `separatingFunctional_none_neg` block back to the
    # FR-canonical position (an inert +57/-57 block move). Because it is
    # repairable, it MUST surface as DRIFT — an investigation trigger — and
    # never be consecrated as a pass-verdict. The `OK-REORDERED`
    # (order-insensitive) verdict proposed by #6728/#6729 was rejected:
    # consecrating a recoverable divergence would mask real drift and let a
    # genuine reorder-plus-edit slip through. This test pins reorder -> DRIFT
    # so the rejected doctrine cannot be silently re-introduced.
    fr = tmp_path / "Cone.lean"
    en = tmp_path / "Cone_en.lean"
    fr.write_text(
        "namespace Cone\n"
        "theorem gen_apply_linear : True := trivial\n"
        "theorem separatingFunctional_none_neg : True := trivial\n"
        "theorem gen_apply_some : True := trivial\n"
        "end Cone\n",
        encoding="utf-8",
    )
    en.write_text(
        "namespace Cone_en\n"
        "theorem gen_apply_linear : True := trivial\n"
        "theorem gen_apply_some : True := trivial\n"
        "theorem separatingFunctional_none_neg : True := trivial\n"
        "end Cone_en\n",
        encoding="utf-8",
    )
    status, detail = check_pair(fr, en)
    assert status == "DRIFT", detail
    # the moved lemma must appear in the diff so the investigation is actionable
    assert "separatingFunctional_none_neg" in detail


def test_normalize_strips_self_qualifiers_arrow_fp():
    # Arrow_en/#6716 false-positive repro: FR defs at top level disambiguate
    # with `_root_.X`; the EN mirror lives in `namespace SocialChoice_en` and
    # must write `SocialChoice_en.X`. Same reference, two scopes.
    fr = (
        "def is_strictly_best (x : Nat) : Prop := x = 0\n"
        "theorem t (x : Nat) : Prop := _root_.is_strictly_best x\n"
    )
    en = (
        "namespace SocialChoice_en\n"
        "def is_strictly_best (x : Nat) : Prop := x = 0\n"
        "theorem t (x : Nat) : Prop := SocialChoice_en.is_strictly_best x\n"
        "end SocialChoice_en\n"
    )
    assert normalize_body(fr) == normalize_body(en)


def test_self_qualifier_does_not_mask_foreign_prefix():
    # A qualified reference to a namespace NOT declared in the file is body
    # content — it must still surface as drift.
    fr = "theorem t : Prop := Other.f 1\n"
    en = "theorem t : Prop := f 1\n"
    assert normalize_body(fr) != normalize_body(en)


def test_check_pair_consumer_pattern_lattice_fp(tmp_path):
    # Lattice_en false-positive repro: the EN sibling imports the FR canonical
    # module and reuses its defs (no redeclaration); only the theorems it does
    # state must match.
    fr = tmp_path / "Lattice.lean"
    en = tmp_path / "Lattice_en.lean"
    fr.write_text(
        "namespace StableMarriage\n"
        "def joinSpouse (x : Nat) : Nat := x + 1\n"
        "def meetSpouse (x : Nat) : Nat := x - 1\n"
        "theorem join_comm (x : Nat) : joinSpouse x = joinSpouse x := rfl\n"
        "end StableMarriage\n",
        encoding="utf-8",
    )
    en.write_text(
        "import StableMarriage.Lattice\n"
        "namespace StableMarriage_en\n"
        "open StableMarriage\n"
        "theorem join_comm (x : Nat) : joinSpouse x = joinSpouse x := rfl\n"
        "end StableMarriage_en\n",
        encoding="utf-8",
    )
    status, detail = check_pair(fr, en)
    assert status == "OK-CONSUMER", detail
    assert "2 FR declaration block(s) reused" in detail


def test_consumer_pattern_still_flags_novel_en_block(tmp_path):
    # An EN block with no FR counterpart is real drift even under the
    # consumer pattern.
    fr = tmp_path / "Cone.lean"
    en = tmp_path / "Cone_en.lean"
    fr.write_text(
        "namespace Cone\n"
        "theorem a : True := trivial\n"
        "end Cone\n",
        encoding="utf-8",
    )
    en.write_text(
        "import Cooperative.Cone\n"
        "namespace Cone_en\n"
        "theorem a : True := by exact trivial\n"
        "end Cone_en\n",
        encoding="utf-8",
    )
    status, detail = check_pair(fr, en)
    assert status == "DRIFT"
    assert "no FR counterpart" in detail


def test_split_decls_attribute_line_starts_block():
    body = (
        "def f : Nat := 1\n"
        "@[simp]\n"
        "theorem t : True := trivial\n"
    )
    blocks = split_decls(body)
    assert len(blocks) == 2
    assert blocks[1].startswith("@[simp]")


def test_imports_fr_sibling_matches_last_segment():
    assert imports_fr_sibling("import StableMarriage.Lattice\n", "Lattice")
    assert not imports_fr_sibling("import StableMarriage.Defs\n", "Lattice")


def test_fr_sibling_naming(tmp_path):
    en = tmp_path / "Widget_en.lean"
    assert fr_sibling(en).name == "Widget.lean"


def test_find_en_files_skips_excluded(tmp_path):
    good = tmp_path / "Good_en.lean"
    good.write_text("x", encoding="utf-8")
    lake = tmp_path / ".lake" / "packages" / "Vendored_en.lean"
    lake.parent.mkdir(parents=True)
    lake.write_text("x", encoding="utf-8")
    found = {p.name for p in find_en_files([tmp_path])}
    assert "Good_en.lean" in found
    assert "Vendored_en.lean" not in found


def test_real_conway_pairs_are_byte_identical():
    """The merged conway_lean rollout must stay clean — regression guard."""
    if not CONWAY_DIR.is_dir():
        # Un `return` muet fait passer la garde pour verte alors qu'elle n'a
        # rien regarde : si le lake bouge encore, on veut le voir dans le
        # rapport, pas un PASS qui ne mesure rien.
        pytest.skip(f"lake conway absente de ce checkout : {CONWAY_DIR}")
    en_files = find_en_files([CONWAY_DIR])
    assert en_files, "expected conway_lean *_en.lean pairs to exist"
    failures = []
    for en in en_files:
        fr = fr_sibling(en)
        if not fr.exists():
            failures.append(f"ORPHAN {en.name}")
            continue
        status, detail = check_pair(fr, en)
        if status == "DRIFT":
            failures.append(f"DRIFT {en.name}\n{detail}")
    assert not failures, "\n".join(failures)


# --- Orphan-trap guard (#6749): an `_en` mirror `lake build` never compiles ---


def test_check_en_built_flags_orphan_toml(tmp_path):
    """The #6749 trap: a root-level `_en` absent from `roots` is UNBUILT."""
    lake = tmp_path / "mylake"
    lake.mkdir()
    (lake / "lakefile.toml").write_text(
        '[[lean_lib]]\nname = "L"\nroots = ["Basic", "Nash", "Nash_en"]\n',
        encoding="utf-8",
    )
    (lake / "Basic_en.lean").write_text("-- orphan\n", encoding="utf-8")
    built, why = check_en_built(lake / "Basic_en.lean", tmp_path)
    assert built is False
    assert "Basic_en" in why and "never compiled" in why


def test_check_en_built_passes_when_in_roots(tmp_path):
    """A root-level `_en` explicitly listed in `roots` is built (no flag)."""
    lake = tmp_path / "mylake"
    lake.mkdir()
    (lake / "lakefile.toml").write_text(
        '[[lean_lib]]\nname = "L"\nroots = ["Nash", "Nash_en"]\n',
        encoding="utf-8",
    )
    (lake / "Nash_en.lean").write_text("-- covered\n", encoding="utf-8")
    built, why = check_en_built(lake / "Nash_en.lean", tmp_path)
    assert built is True and why == ""


def test_check_en_built_glob_covers_submodule(tmp_path):
    """A submodule `_en` under a `.submodules`/`.*` parent glob is built — the
    guard must NOT flag it (matches game_theory_lean `RepeatedGames.*`)."""
    lake = tmp_path / "glake"
    (lake / "Foo").mkdir(parents=True)
    (lake / "lakefile.lean").write_text(
        "lean_lib «Foo» where\n  globs := #[.submodules `Foo]\n",
        encoding="utf-8",
    )
    (lake / "Foo" / "Bar_en.lean").write_text("-- sub\n", encoding="utf-8")
    built, _ = check_en_built(lake / "Foo" / "Bar_en.lean", tmp_path)
    assert built is True


def test_check_en_built_skips_without_lakefile(tmp_path):
    """No enclosing lakefile → undeterminable → skip (None), never false-flag."""
    (tmp_path / "Loose_en.lean").write_text("-- x\n", encoding="utf-8")
    built, why = check_en_built(tmp_path / "Loose_en.lean", tmp_path)
    assert built is None
    assert "lakefile" in why


def test_enclosing_lake_walks_up_to_nearest(tmp_path):
    """`enclosing_lake` returns the nearest ancestor lakefile, stopping at root."""
    lake = tmp_path / "l"
    (lake / "sub").mkdir(parents=True)
    lf = lake / "lakefile.lean"
    lf.write_text("lean_lib «L» where\n", encoding="utf-8")
    found = enclosing_lake(lake / "sub" / "X_en.lean", tmp_path)
    assert found == lf
    assert enclosing_lake(tmp_path / "Nowhere_en.lean", tmp_path) is None


def test_licence_header_is_repository_boilerplate():
    """The Apache-2.0 header is identical in every pair by construction: it is
    boilerplate, not prose, and must not be read as an untranslated body."""
    assert is_repo_boilerplate(
        "Copyright (c) 2026 CoursIA. All rights reserved.\n"
        "Released under Apache 2.0 license as described in the file LICENSE."
    )
    # A body that merely starts like the header is NOT boilerplate: the match
    # is anchored on both ends.
    assert not is_repo_boilerplate(
        "Copyright (c) 2026 CoursIA. All rights reserved.\n"
        "Released under Apache 2.0 license as described in the file LICENSE.\n"
        "The arcs of a diagram: partition of the edge labels."
    )
    assert not is_repo_boilerplate(
        "Les arcs d'un diagramme : partition des étiquettes d'arêtes."
    )


def test_half_done_ignores_shared_licence_header(tmp_path):
    """A pair whose only shared body is the licence header is NOT half-done."""
    fr = tmp_path / "Baz.lean"
    en = tmp_path / "Baz_en.lean"
    header = ("/-\nCopyright (c) 2026 CoursIA. All rights reserved.\n"
              "Released under Apache 2.0 license as described in the file "
              "LICENSE.\n-/\n")
    fr.write_text(header + "/-- Les arcs d'un diagramme. -/\n"
                  "namespace Conway\ndef answer : Nat := 42\nend Conway\n",
                  encoding="utf-8")
    en.write_text(header + "/-- The arcs of a diagram. -/\n"
                  "namespace Conway_en\ndef answer : Nat := 42\nend Conway_en\n",
                  encoding="utf-8")
    flagged, n_identical = is_half_done(fr, en)
    assert not flagged
    assert n_identical == 0


def test_half_done_still_flags_shared_prose(tmp_path):
    """Negative control: a genuinely shared prose body is still reported.

    The boilerplate exclusion must not silence the advisory it refines."""
    fr = tmp_path / "Qux.lean"
    en = tmp_path / "Qux_en.lean"
    header = ("/-\nCopyright (c) 2026 CoursIA. All rights reserved.\n"
              "Released under Apache 2.0 license as described in the file "
              "LICENSE.\n-/\n")
    shared = ("/-- Les arcs d'un diagramme : partition des etiquettes d'aretes "
              "par la fermeture des paires de passage-dessus. -/\n")
    fr.write_text(header + shared + "namespace Conway\n"
                  "def answer : Nat := 42\nend Conway\n", encoding="utf-8")
    en.write_text(header + shared + "namespace Conway_en\n"
                  "def answer : Nat := 42\nend Conway_en\n", encoding="utf-8")
    flagged, n_identical = is_half_done(fr, en)
    assert flagged
    assert n_identical == 1


def test_real_grothendieck_godement_pairs_are_not_half_done():
    """Measured 2026-11-02 (lane myia-po-2028:CoursIA-2): the nine Grothendieck
    ``Godement*_en`` mirrors are OK-CONSUMER siblings whose module docstring is
    translated; the HALF-DONE hit came from the shared licence header alone.
    They must no longer be reported."""
    groth = (REPO_ROOT / "MyIA.AI.Notebooks" / "SymbolicAI" / "Lean" / "GROTH"
             / "grothendieck_lean" / "Grothendieck")
    # Nine pairs, two of them nested: the ninth lives in the SheafCohomology
    # sub-folder, so entries carry their relative path when it differs (#24161).
    names = ["Godement", "GodementAcyclicity", "GodementCanonicalDiff",
             "GodementComplex", "GodementExactness", "GodementFunctor",
             "GodementMono", "GodementResolution",
             "SheafCohomology/Godement"]
    for name in names:
        fr = groth / f"{name}.lean"
        en = groth / f"{name}_en.lean"
        assert fr.exists() and en.exists(), name
        flagged, n_identical = is_half_done(fr, en)
        assert not flagged, f"{name}: {n_identical} shared body(ies)"


def _run_direct() -> int:
    import tempfile

    passed = 0
    for name, fn in sorted(globals().items()):
        if not name.startswith("test_") or not callable(fn):
            continue
        argcount = fn.__code__.co_argcount
        try:
            if argcount == 0:
                fn()
            else:
                with tempfile.TemporaryDirectory() as d:
                    fn(Path(d))
            print(f"PASS {name}")
            passed += 1
        except AssertionError as exc:
            print(f"FAIL {name}: {exc}")
            return 1
    print(f"\n{passed} tests passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(_run_direct())


@pytest.mark.parametrize("namespace,expected", [
    ("Knots_en.AnyMoves", ["Knots.Basic"]),
    ("Outer.Inner_en.More", ["Knots.Basic"]),
    ("Knots_en", ["Knots.Basic"]),
    ("Knots_enriched.AnyMoves", []),
    ("Knots.AnyMoves", []),
])
def test_fr_import_advisory_reconnait_namespace_qualifie(tmp_path, namespace, expected):
    lake = tmp_path / "lake"
    knots = lake / "Knots"
    knots.mkdir(parents=True)
    (lake / "lakefile.lean").write_text("", encoding="utf-8")
    (knots / "Basic.lean").write_text("", encoding="utf-8")
    (knots / "Basic_en.lean").write_text("", encoding="utf-8")
    hybrid = knots / "Hybrid_en.lean"
    hybrid.write_text(
        f"import Knots.Basic\nnamespace {namespace}\ndef own := 1\n",
        encoding="utf-8",
    )
    assert fr_import_siblings(hybrid) == expected


@pytest.mark.parametrize("literal", [
    '"un texte\nnamespace Knots_en.AnyMoves\nfin"',
    'r#"un texte avec "guillemets" et /- commentaire fictif\nnamespace Knots_en.AnyMoves\nfin"#',
    'r##"un texte avec "# et -- faux commentaire\nnamespace Knots_en.AnyMoves\nfin"##',
])
def test_fr_import_ignore_namespace_dans_chaine(tmp_path, literal):
    lake = tmp_path / "lake"
    knots = lake / "Knots"
    knots.mkdir(parents=True)
    (lake / "lakefile.lean").write_text("", encoding="utf-8")
    for name in ("Basic.lean", "Basic_en.lean"):
        (knots / name).write_text("", encoding="utf-8")
    hybrid = knots / "Hybrid_en.lean"
    hybrid.write_text(
        f'import Knots.Basic\ndef message := {literal}\n', encoding="utf-8"
    )
    assert fr_import_siblings(hybrid) == []


def test_fr_import_reste_visible_apres_chaine_raw_et_commentaires(tmp_path):
    lake = tmp_path / "lake"
    knots = lake / "Knots"
    knots.mkdir(parents=True)
    (lake / "lakefile.lean").write_text("", encoding="utf-8")
    for name in ("Basic.lean", "Basic_en.lean"):
        (knots / name).write_text("", encoding="utf-8")
    hybrid = knots / "Hybrid_en.lean"
    hybrid.write_text(
        'import Knots.Basic -- import reel\n'
        'def message := r#"guillemet " puis /- jamais ouvert"#\n'
        '/- namespace Faux_en.Foo /- nested -/ -/\n'
        'namespace Knots_en.AnyMoves\ndef own := 1\n', encoding="utf-8"
    )
    assert fr_import_siblings(hybrid) == ["Knots.Basic"]


@pytest.mark.parametrize("content", [
    'def text := r#"\nimport Knots.Basic\n"#\nnamespace Knots_en.AnyMoves\n',
    'import Knots.Basic\nnamespace Knots_en.AnyMoves\n#eval r#"\ndef fictif := 1\n"#\n',
    'import Knots.Basic\n/- namespace Knots_en.AnyMoves /- def faux := 1 -/ -/\n',
])
def test_fr_import_ignore_code_fictif_dans_chaines_et_commentaires(tmp_path, content):
    lake = tmp_path / "lake"
    knots = lake / "Knots"
    knots.mkdir(parents=True)
    (lake / "lakefile.lean").write_text("", encoding="utf-8")
    for name in ("Basic.lean", "Basic_en.lean"):
        (knots / name).write_text("", encoding="utf-8")
    hybrid = knots / "Hybrid_en.lean"
    hybrid.write_text(content, encoding="utf-8")
    assert fr_import_siblings(hybrid) == []


@pytest.mark.parametrize("literal", ["'\"'", "'\\\"'", "'\\x22'", "'\\u0022'", "'\\\\'"])
def test_fr_import_survit_aux_caracteres_lean(tmp_path, literal):
    lake = tmp_path / "lake"
    knots = lake / "Knots"
    knots.mkdir(parents=True)
    (lake / "lakefile.lean").write_text("", encoding="utf-8")
    for name in ("Basic.lean", "Basic_en.lean"):
        (knots / name).write_text("", encoding="utf-8")
    hybrid = knots / "Hybrid_en.lean"
    hybrid.write_text(
        f'import Knots.Basic\ndef quote : Char := {literal}\n'
        'namespace Knots_en.AnyMoves\ndef own := 1\n', encoding="utf-8"
    )
    assert fr_import_siblings(hybrid) == ["Knots.Basic"]


def test_fr_import_ignore_chaine_raw_sans_diese(tmp_path):
    lake = tmp_path / "lake"
    knots = lake / "Knots"
    knots.mkdir(parents=True)
    (lake / "lakefile.lean").write_text("", encoding="utf-8")
    for name in ("Basic.lean", "Basic_en.lean"):
        (knots / name).write_text("", encoding="utf-8")
    hybrid = knots / "Hybrid_en.lean"
    hybrid.write_text(
        'import Knots.Basic\ndef text := r"texte\\"\n'
        'namespace Knots_en.AnyMoves\ndef own := 1\n', encoding="utf-8"
    )
    assert fr_import_siblings(hybrid) == ["Knots.Basic"]


def test_fr_import_preserve_identifiant_avec_apostrophe(tmp_path):
    lake = tmp_path / "lake"
    knots = lake / "Knots"
    knots.mkdir(parents=True)
    (lake / "lakefile.lean").write_text("", encoding="utf-8")
    for name in ("Basic.lean", "Basic_en.lean"):
        (knots / name).write_text("", encoding="utf-8")
    hybrid = knots / "Hybrid_en.lean"
    hybrid.write_text(
        "import Knots.Basic\nnamespace Knots_en.AnyMoves\ndef value' := 1\n",
        encoding="utf-8",
    )
    assert fr_import_siblings(hybrid) == ["Knots.Basic"]


def test_fr_import_survit_aux_identifiants_lean_echappes(tmp_path):
    lake = tmp_path / "lake"
    knots = lake / "Knots"
    knots.mkdir(parents=True)
    (lake / "lakefile.lean").write_text("", encoding="utf-8")
    for name in ("Basic.lean", "Basic_en.lean"):
        (knots / name).write_text("", encoding="utf-8")
    hybrid = knots / "Hybrid_en.lean"
    hybrid.write_text(
        'import Knots.Basic\ndef «x"y» := 1\n'
        'namespace Knots_en.AnyMoves\ndef own := 1\n', encoding="utf-8"
    )
    assert fr_import_siblings(hybrid) == ["Knots.Basic"]


def test_fr_import_ignore_identifiant_echappe_multiligne(tmp_path):
    lake = tmp_path / "lake"
    knots = lake / "Knots"
    knots.mkdir(parents=True)
    (lake / "lakefile.lean").write_text("", encoding="utf-8")
    for name in ("Basic.lean", "Basic_en.lean"):
        (knots / name).write_text("", encoding="utf-8")
    hybrid = knots / "Hybrid_en.lean"
    hybrid.write_text(
        'import Knots.Basic\ndef «x\nnamespace Knots_en.AnyMoves\n'
        'def fictif := 1» := 1\n', encoding="utf-8"
    )
    assert fr_import_siblings(hybrid) == []
