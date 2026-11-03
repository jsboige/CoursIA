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
