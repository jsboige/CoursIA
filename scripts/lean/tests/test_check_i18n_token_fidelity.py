#!/usr/bin/env python3
"""Tests for check_i18n_token_fidelity.py (Lean i18n #4980 token fidelity).

Dual-mode: runnable directly (``python scripts/lean/tests/test_check_i18n_token_fidelity.py``)
or under pytest (auto-collected by scripts-tests.yml on any ``scripts/**`` change).
"""
from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
sys.stdout.reconfigure(encoding="utf-8", errors="replace")

from check_i18n_token_fidelity import (  # noqa: E402
    ADVISORY,
    HARD,
    _best_shift,
    code_spans,
    collapse_en,
    compare_bodies,
    compare_files,
    declaration_names,
    designation_exemptions,
    is_i18n_convention_block,
    is_mirror_metadata_header,
    is_technical,
    number_is_carried_elsewhere,
    number_parts,
    scan_comments,
    span_is_decl_ref,
)

REPO_ROOT = Path(__file__).resolve().parents[3]
KNOTS = (
    REPO_ROOT
    / "MyIA.AI.Notebooks" / "SymbolicAI" / "Lean" / "KNOTS" / "knot_lean" / "Knots"
)


# --- scanning -------------------------------------------------------------

def test_scan_comments_finds_line_block_and_doc():
    src = (
        "/-! doc -/\n"
        "def a := 1 -- ligne\n"
        "/- bloc\nsur deux lignes -/\n"
    )
    kinds = [c[1] for c in scan_comments(src)]
    assert kinds == ["doc", "line", "block"]


def test_scan_comments_ignores_string_content():
    src = 'def s := "un -- deux"\ndef t := 2 -- vrai commentaire\n'
    bodies = [c[2].strip() for c in scan_comments(src)]
    assert bodies == ["vrai commentaire"]


def test_scan_comments_anchor_follows_the_code():
    src = "def a := 1\n-- c1\ndef b := 2\n-- c2\n"
    comments = scan_comments(src)
    assert [c[3] for c in comments] == sorted(c[3] for c in comments)
    assert comments[0][3] < comments[1][3]


def test_scan_comments_anchor_is_insensitive_to_indentation():
    flat = scan_comments("def a := 1\n-- c\n")
    wrapped = scan_comments("def a :=\n    1\n-- c\n")
    assert flat[0][3] == wrapped[0][3]


def test_scan_comments_block_nesting():
    src = "/- outer /- inner -/ still outer -/\n"
    bodies = [c[2] for c in scan_comments(src)]
    assert len(bodies) == 1
    assert "inner" in bodies[0] and "still outer" in bodies[0]


# --- token extraction -----------------------------------------------------

def test_code_spans_normalize_wrapped_spans():
    body = "voir `(20*100 - 25*100)\n    = -6000` pour le detail"
    spans = code_spans(body)
    assert spans == ["(20*100 - 25*100) = -6000"]


def test_code_spans_ignore_numbers_outside_backticks():
    body = "l'arc 11 et `arcPartition`"
    assert code_spans(body) == ["arcPartition"]


def test_number_parts_split_a_date_but_keep_a_decimal():
    # A date is split on its separators (the two formats give the same parts);
    # a decimal is NOT split, otherwise ``1.5`` and ``5.1`` compare equal.
    assert sorted(number_parts("le 2026-10-27 et 1.5")) == sorted(
        ["2026", "10", "27", "1.5"])
    assert sorted(number_parts("le 27/10/2026")) == sorted(["2026", "10", "27"])
    assert number_parts("pi 1,5") == ["1.5"]


def test_number_parts_split_a_ratio_on_its_slash():
    # A slash is a separator (a ratio, a fraction), a dot is a decimal point.
    assert sorted(number_parts("la trame 0/1")) == sorted(["0", "1"])
    assert sorted(number_parts("lignes 65-979")) == sorted(["65", "979"])


def test_number_parts_exclude_code_spans():
    assert number_parts("valeur `(20*100)`") == []


def test_number_is_carried_elsewhere_by_word():
    assert number_is_carried_elsewhere("1", "the 0/one/several frame")
    assert not number_is_carried_elsewhere("1", "the frame")


def test_number_is_carried_elsewhere_by_date_format():
    # A number is excused only when it belongs to a FULL DATE on one side and
    # the other side carries a full date too: the mere presence of a year
    # excuses nothing (review of #24148).
    assert number_is_carried_elsewhere("7", "April 7, 2026")
    assert number_is_carried_elsewhere("04", "April 7, 2026", "le 2026-04-07")
    assert not number_is_carried_elsewhere("04", "April 7, 2026")
    assert not number_is_carried_elsewhere("04", "plain text")


def test_number_is_carried_elsewhere_by_french_word():
    # The FR side spells a small number in a French word; the EN side carries
    # the digit. Both spell the same number, so the digit is not a loss.
    assert number_is_carried_elsewhere("0", "la position vide a un nim-sum nul")
    assert number_is_carried_elsewhere("2", "deux aretes")
    assert number_is_carried_elsewhere("3", "trois aretes")
    assert number_is_carried_elsewhere("5", "cinq noeuds")


def test_number_is_not_carried_by_the_french_article():
    # "un" is the French indefinite article, not the number one: matching it
    # would excuse every "1" wherever an article happens to sit.
    assert not number_is_carried_elsewhere("1", "un arete")
    assert not number_is_carried_elsewhere("1", "une trame")


def test_a_bare_year_excuses_no_small_number():
    # Regression of the review of #24148: ``2026`` alone used to excuse every
    # one- or two-digit number of the other side.
    findings = compare_bodies("il y a 3 aretes", "the set in 2026", set())
    hard = [f for f in findings if f["severity"] == HARD]
    assert "3" in [f["token"] for f in hard]


def test_a_decimal_is_not_its_mirror():
    # Regression of the review of #24148: splitting on the decimal separator
    # made ``1.5`` and ``5.1`` compare equal.
    findings = compare_bodies("pi=1.5", "pi=5.1", set())
    hard = [f for f in findings if f["severity"] == HARD]
    assert "1.5" in [f["token"] for f in hard]
    assert "5.1" in [f["token"] for f in hard]


def test_is_technical():
    assert is_technical("arcPartition")
    assert is_technical("augCone_dual_iff")
    assert is_technical("JSON")
    assert not is_technical("Lean")
    assert not is_technical("FR")
    assert not is_technical("EN")


def test_collapse_en_is_symmetric():
    assert collapse_en("Knots_en") == "Knots"
    assert collapse_en("Knots") == "Knots"


def test_declaration_names():
    src = "def arcPartition : Nat := 0\ntheorem foo_bar : True := by trivial\n"
    assert declaration_names(src) == {"arcPartition", "foo_bar"}


def test_span_is_decl_ref():
    decls = {"arcPartition", "labelAt"}
    assert span_is_decl_ref("arcPartition x", decls)
    assert span_is_decl_ref("`Knots/Conway.lean`", decls) is False


def test_designation_exemptions_drop_the_cross_designation():
    drop_fr, drop_en = designation_exemptions(
        "voir `Knots/Conway.lean`",
        "see `Conway_en.lean`",
    )
    assert drop_fr == {"Knots/Conway.lean"}
    assert drop_en == {"Conway_en.lean"}


# --- comparison -----------------------------------------------------------

def test_compare_bodies_reports_a_lost_declaration_reference():
    findings = compare_bodies(
        "le lemme `arcPartition` fait le lien",
        "the lemma makes the link",
        {"arcPartition"},
    )
    hard = [f for f in findings if f["severity"] == HARD]
    assert [f["token"] for f in hard] == ["arcPartition"]


def test_compare_bodies_a_dropped_generic_span_is_advisory():
    findings = compare_bodies(
        "voir `-- ...` pour la syntaxe",
        "see the syntax",
        set(),
    )
    assert findings
    assert all(f["severity"] == ADVISORY for f in findings)


def test_compare_bodies_reports_a_lost_number():
    findings = compare_bodies(
        "l'ensemble compte 22 aretes",
        "the set has edges",
        set(),
    )
    hard = [f for f in findings if f["severity"] == HARD]
    assert [f["token"] for f in hard] == ["22"]


def test_compare_bodies_accepts_a_translated_number_in_words():
    findings = compare_bodies(
        "la trame 0/1/plusieurs",
        "the 0/one/several frame",
        set(),
    )
    assert not [f for f in findings if f["severity"] == HARD]


def test_compare_bodies_accepts_a_french_word_for_the_digit():
    # The Nim anchor (review of #24148): the FR says "nim-sum nul", the EN says
    # "nim-sum 0". A faithful translation -- the digit is carried by the French
    # word on the other side, so it is not a loss.
    findings = compare_bodies(
        "la position vide a un nim-sum nul",
        "the empty position has nim-sum 0",
        set(),
    )
    assert not [
        f for f in findings if f["severity"] == HARD and f["kind"] == "number"]


def test_compare_bodies_a_lost_number_stays_hard_without_the_word():
    # Control negative: "2" is in the lexicon, but the EN side carries neither
    # "two" nor "deux", so the number is genuinely lost and stays HARD. The
    # French lexicon mitigates a carried number, it does not excuse a lost one.
    findings = compare_bodies(
        "l'ensemble compte 2 aretes",
        "the set has edges",
        set(),
    )
    hard = [f for f in findings
            if f["severity"] == HARD and f["kind"] == "number"]
    assert [f["token"] for f in hard] == ["2"]


def test_module_docstring_decl_reference_is_advisory():
    # Control positive Generators_en.lean (review of #24148): the EN module
    # docstring names a module declaration (`termA2`) the FR summary does not.
    # The declaration is defined in the file (both twins); a summary naming a
    # different subset of the module's declarations is a divergence, not a
    # loss. In a module docstring it is advisory.
    findings = compare_bodies(
        "le pont vers la structure : `relA1_iff_generated`",
        "the bridge: `termA2` and `relA1_iff_generated`",
        {"termA2", "relA1_iff_generated"},
        is_module=True,
    )
    assert findings
    assert all(f["severity"] == ADVISORY for f in findings)


def test_local_docstring_decl_reference_stays_hard():
    # Narrow-control for the module-docstring exemption: the SAME declaration
    # reference dropped from a LOCAL docstring (attached to a definition, not
    # the file summary) is still a real fidelity loss and stays hard.
    findings = compare_bodies(
        "le lemme `arcPartition` fait le lien",
        "the lemma makes the link",
        {"arcPartition"},
        is_module=False,
    )
    hard = [f for f in findings if f["severity"] == HARD]
    assert [f["token"] for f in hard] == ["arcPartition"]


def test_compare_bodies_ignores_a_dropped_header_metadata():
    # The header of a mirror states its own metadata; it is excluded from
    # the comparison by compare_files, not by compare_bodies.
    findings = compare_bodies("EPIC #4980, tranche 1", "tranche 1", set())
    assert any(f["kind"] == "number" for f in findings)


def test_the_mirror_header_is_recognized_by_the_bodies():
    # The EN body declares the mirror, the FR body does not: the pair is a
    # metadata header and comparing it would report every token of one side
    # as the loss of the other. When BOTH sides declare it, the comparison is
    # meaningful and the exclusion does not apply.
    assert is_mirror_metadata_header(
        "le lemme `arcPartition`",
        "English mirror of `Foo.lean` (EPIC #4980, tranche 1)",
    )
    assert not is_mirror_metadata_header(
        "ce fichier est le miroir de `Foo.lean` (EPIC #4980, tranche 1)",
        "English mirror of `Foo.lean` (EPIC #4980, tranche 1)",
    )
    assert not is_mirror_metadata_header(
        "le lemme `arcPartition`",
        "the lemma makes the link",
    )


def test_the_sibling_and_companion_headers_are_recognized():
    # "sibling of" / "companion to" name the canonical .lean file; the EN body
    # declares the mirror, the FR body does not -> the pair is a metadata
    # header (review of #24143: examples/*, differential_lean/*).
    assert is_mirror_metadata_header(
        "le lemme `arcPartition`",
        "English sibling of `basic_logic.lean` (i18n #4980): docstrings",
    )
    assert is_mirror_metadata_header(
        "le lemme `arcPartition`",
        "English companion to `DifferentialTour.lean` (FR canonical) "
        "per the i18n #4980 sibling-pair convention",
    )


def test_a_bare_sibling_tag_is_not_a_mirror_declaration():
    # Control negative: the "(EN sibling)" tag on a title line names no .lean
    # file, so it is too weak to single out a metadata header; the comparison
    # stays meaningful (the broadened marker must not over-trigger).
    assert not is_mirror_metadata_header(
        "le lemme `arcPartition`",
        "Lean Examples - Basic Logic (EN sibling)",
    )


def test_ok_consumer_sibling_is_excluded_wholesale(tmp_path):
    # OK-CONSUMER sibling: the EN file imports the FR canonical and reuses its
    # declarations (the proven Lattice shape). The FR per-declaration docstrings
    # then have no EN counterpart by design, so comparing them positionally
    # would publish a false HARD finding for each. The exclusion reuses the
    # sibling organ's "OK-CONSUMER" verdict (check_i18n_siblings.check_pair)
    # and skips the comparison: the report is flagged and carries no findings.
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
    rep = compare_files(fr, en)
    assert rep["ok_consumer"] is True
    assert rep["findings"] == []


def test_redeclaring_en_is_not_ok_consumer(tmp_path):
    # Control: an EN mirror that redeclares (no import of the FR module) is
    # DRIFT, not OK-CONSUMER, so the comparison runs and the flag is not set.
    fr = tmp_path / "Cone.lean"
    en = tmp_path / "Cone_en.lean"
    fr.write_text(
        "namespace Cone\n"
        "def a (x : Nat) : Nat := x + 1\n"
        "end Cone\n",
        encoding="utf-8",
    )
    en.write_text(
        "namespace Cone_en\n"
        "def a (x : Nat) : Nat := x + 2\n"
        "end Cone_en\n",
        encoding="utf-8",
    )
    rep = compare_files(fr, en)
    assert rep.get("ok_consumer") is not True


def test_i18n_convention_block_is_recognized():
    # Control Conway/Doomsday.lean (review of #24148): a `### i18n` convention
    # note documents the sibling-pair convention (here an option-A exception);
    # it is metadata, so it is recognized and excluded from the comparison.
    assert is_i18n_convention_block(
        "### i18n -- convention #4980 ratifiee 2026-07-04\n"
        "Ce sous-module suit l'option A (bilingue inline FR/EN).")
    assert is_i18n_convention_block("voir le bloc ### i18n ci-dessus")
    assert not is_i18n_convention_block(
        "le lemme `arcPartition` fait le lien")


def test_i18n_convention_block_plain_heading_is_recognized():
    # The sibling-pair convention is also written as a plain heading, without
    # the `### ` marker: 45 `_en.lean` files open on it (e.g.
    # GameTheory/SocialChoice/{Framework,Basic}_en.lean). Its metadata numbers
    # (dates, `#4980`, commit shas) were compared against the FR canonical
    # header and reported as HARD losses that no translation could fix.
    assert is_i18n_convention_block(
        "Convention i18n : fichier EN sibling -- preserve le verbatim\n"
        "Convention i18n Lean ratifiee par ai-01 (2026-07-04, issue #4980)")
    assert is_i18n_convention_block(
        "English sibling of `Conway.lean` per the i18n convention EPIC #4980")


def test_a_bare_prose_mention_of_the_convention_does_not_exempt_the_comment():
    # NanoClaw review of #24765, point 3: under the original any-position
    # motif, translatable prose that merely MENTIONED the convention silenced
    # the whole comment it lived in. The exemption classifies a note ABOUT the
    # convention, not every sentence citing its name: the plain spelling must
    # head a line or carry the EPIC citation, otherwise the comment is
    # compared like any other translatable prose.
    assert not is_i18n_convention_block(
        "Aucun `sorry`. Ce fichier suit la convention i18n du depot.")
    assert not is_i18n_convention_block(
        "The module follows the i18n convention used across the series.")
    # The two metadata shapes the corpus actually writes stay exempt: the
    # citation form (control ApprovalPayment.lean:56, Containment.lean:6,
    # ReidemeisterCombinatorial.lean:52 and :976) ...
    assert is_i18n_convention_block(
        "Aucun `sorry`. Convention i18n #4980 : ce fichier porte le namespace")
    assert is_i18n_convention_block(
        "corps byte-identique (convention i18n EPIC #4980).")
    # ... and the `###` title that names it (control KochenSpecker.lean:78).
    assert is_i18n_convention_block(
        "### Hommage MathOverflow + Mathlib i18n convention #4980")


def test_best_shift_aligns_a_constant_offset():
    fr = {0, 10, 20}
    en = {2, 12, 22}
    assert _best_shift(fr, en) == 2
    assert _best_shift(fr, fr) == 0


# --- file level -----------------------------------------------------------

def test_compare_files_excludes_the_header(tmp_path=None):
    fr = tmp_path / "Foo.lean" if tmp_path else Path("/tmp/Foo.lean")
    en = tmp_path / "Foo_en.lean" if tmp_path else Path("/tmp/Foo_en.lean")
    fr.parent.mkdir(parents=True, exist_ok=True)
    fr.write_text(
        "/- Entete FR mentionnant EPIC #4980 -/\n"
        "def arcPartition : Nat := 0\n"
        "/- le lemme `arcPartition` -/\n",
        encoding="utf-8",
    )
    en.write_text(
        "/- English mirror of `Foo.lean` (EPIC #4980, tranche 1) -/\n"
        "def arcPartition : Nat := 0\n"
        "/- the lemma makes the link -/\n",
        encoding="utf-8",
    )
    report = compare_files(fr, en)
    hard = [f for f in report["findings"] if f["severity"] == HARD]
    assert [f["token"] for f in hard] == ["arcPartition"]
    # The header pair is excluded, the lemma pair is compared: the coverage
    # counters say what was actually measured.
    assert report["pairs_excluded"] == 1
    assert report["pairs_compared"] == 1


def test_compare_files_reports_an_unpaired_comment(tmp_path=None):
    fr = tmp_path / "Bar.lean" if tmp_path else Path("/tmp/Bar.lean")
    en = tmp_path / "Bar_en.lean" if tmp_path else Path("/tmp/Bar_en.lean")
    fr.parent.mkdir(parents=True, exist_ok=True)
    fr.write_text("def a : Nat := 0\n", encoding="utf-8")
    en.write_text("def a : Nat := 0\n-- commentaire propre au miroir\n",
                  encoding="utf-8")
    report = compare_files(fr, en)
    assert any(u["kind"] == "unpaired-comment" for u in report["unpaired"])


def test_compare_files_module_docstring_decl_is_advisory(tmp_path=None):
    # End-to-end for the module-docstring exemption (control
    # Generators_en.lean, review of #24148): the EN file's module docstring
    # (its first block-doc comment) names a module declaration the FR summary
    # does not. Detected as the module docstring by its anchor, the reference
    # is advisory, not a hard loss.
    fr = tmp_path / "Generators.lean" if tmp_path else Path("/tmp/G.lean")
    en = tmp_path / "Generators_en.lean" if tmp_path else Path("/tmp/G_en.lean")
    fr.parent.mkdir(parents=True, exist_ok=True)
    fr.write_text(
        "/-!\n"
        "# Generators : le pont vers la structure\n"
        "`relA1_iff_generated` relie les tables -/\n"
        "def termA2 : Nat := 0\n"
        "def relA1_iff_generated : Prop := True\n",
        encoding="utf-8",
    )
    en.write_text(
        "/-!\n"
        "# Generators : the bridge to the structure\n"
        "`termA2` and `relA1_iff_generated` relate the tables -/\n"
        "def termA2 : Nat := 0\n"
        "def relA1_iff_generated : Prop := True\n",
        encoding="utf-8",
    )
    report = compare_files(fr, en)
    hard = [f for f in report["findings"] if f["severity"] == HARD]
    assert hard == [], hard


def test_compare_files_excludes_an_unpaired_i18n_block(tmp_path=None):
    # End-to-end for the `### i18n` exemption (control Conway/Doomsday.lean,
    # review of #24148): a `### i18n` convention note present in the FR file,
    # absent from the EN mirror, is metadata -- it is NOT reported as a lost /
    # unpaired comment. The narrow guard: a genuine non-i18n orphan on the same
    # file is still reported, so the exemption is scoped to the convention note.
    fr = tmp_path / "Doomsday.lean" if tmp_path else Path("/tmp/D.lean")
    en = tmp_path / "Doomsday_en.lean" if tmp_path else Path("/tmp/D_en.lean")
    fr.parent.mkdir(parents=True, exist_ok=True)
    fr.write_text(
        "/- Conway's Doomsday Algorithm (original EN) -/\n"
        "def dayOfWeek : Nat := 0\n"
        "/-\n"
        "`Conway.Doomsday` -- l'algorithme du Doomsday\n"
        "  ### i18n -- convention #4980\n"
        "  Ce sous-module suit l'option A (bilingue inline FR/EN).\n"
        "-/\n"
        "def anchor : Nat := 1\n"
        "-- une note propre au fichier FR\n",
        encoding="utf-8",
    )
    en.write_text(
        "/- English mirror of `Doomsday.lean` (FR canonical) -/\n"
        "def dayOfWeek : Nat := 0\n",
        encoding="utf-8",
    )
    report = compare_files(fr, en)
    unpaired_bodies = " ".join(u["body"] for u in report["unpaired"])
    assert "i18n" not in unpaired_bodies
    assert "une note propre au fichier FR" in unpaired_bodies


# --- fenced code blocks ---------------------------------------------------

def test_a_fenced_block_does_not_swallow_the_prose_after_it():
    """A fence carries an ODD number of backticks: the scanner must not pair
    its closing backtick with the next opening one and read the prose in
    between as a code span.  Measured: 130 HARD findings on a mirror pair
    that is faithful (review of #24143, ``Knots/Invariant``)."""
    body = (
        "Intro\n"
        "```\n"
        "theorem bar : True := trivial\n"
        "```\n"
        "Le lemme `bar` existe et vaut 3.\n"
    )
    assert code_spans(body) == ["bar"]


def test_a_divergence_after_a_fenced_block_is_still_reported():
    """Dropping the fenced block must not blind the comparison to the prose
    that follows it."""
    findings = compare_bodies(
        "```\ntheorem bar : True := trivial\n```\nle compte est 22 aretes",
        "```\ntheorem bar : True := trivial\n```\nthe set has edges",
        set(),
    )
    hard = [f for f in findings if f["severity"] == HARD]
    assert [f["token"] for f in hard] == ["22"]


# --- the repository itself ------------------------------------------------

def test_arcpartition_sibling_is_token_faithful():
    """The pair relecture of #24138 must not report a hard finding."""
    fr = KNOTS / "ArcPartition.lean"
    en = KNOTS / "ArcPartition_en.lean"
    if not fr.exists() or not en.exists():
        return
    report = compare_files(fr, en)
    hard = [f for f in report["findings"] if f["severity"] == HARD]
    assert hard == [], hard


if __name__ == "__main__":
    import tempfile

    failures = 0
    for name, fn in sorted(globals().items()):
        if not name.startswith("test_") or not callable(fn):
            continue
        try:
            if "tmp_path" in fn.__code__.co_varnames[: fn.__code__.co_argcount]:
                with tempfile.TemporaryDirectory() as tmp:
                    fn(Path(tmp))
            else:
                fn()
            print("ok   %s" % name)
        except AssertionError as exc:
            failures += 1
            print("FAIL %s : %s" % (name, exc))
    raise SystemExit(1 if failures else 0)
