#!/usr/bin/env python3
"""Tests for the `EN sibling of `X`` mirror-header form (Lean i18n #4980).

`check_i18n_token_fidelity.py` recognised two mirror-header forms:
`English mirror of `X.lean`` and `miroir de `X.lean``. A third form is
used by the `sensitivity_lean` family:

    EN sibling of `Sensitivity/VectorSpace.lean` (FR-first canonical).

That header is metadata (ratification date, issue ids, convention note) with
no FR counterpart, so comparing it against the FR canonical reports the
EN-side metadata as a "loss" -- 39 spurious HARD findings on that family
alone.

Excluding it unconditionally would be wrong: the same form sometimes
*translates* the FR summary, and then a genuinely dropped FR token would be
hidden. The organ therefore excludes the pair ONLY when the EN side drops
nothing the FR side carries.

These tests cover both sides of that contract.

They also pin the two decisions taken on the structural review of #24591:

* the comparison is computed LAZILY -- a pair excluded as a plain mirror
  header never pays for a comparison whose result is thrown away;
* the `sibling` branch is evaluated BEFORE the plain mirror-header
  exclusion, so a body carrying BOTH declarations and dropping a FR token
  is reported instead of being silently excluded (the exclusion must never
  hide a real loss).
"""
from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
sys.stdout.reconfigure(encoding="utf-8", errors="replace")

import check_i18n_token_fidelity as org  # noqa: E402
from check_i18n_token_fidelity import (  # noqa: E402
    HARD,
    compare_files,
)

REPO_ROOT = Path(__file__).resolve().parents[3]
SENSITIVITY = (
    REPO_ROOT
    / "MyIA.AI.Notebooks" / "SymbolicAI" / "Lean" / "sensitivity_lean"
    / "Sensitivity"
)

# A block comment (NOT a `/-! -/` module docstring): the module docstring is
# compared as a summary, where a divergent number is advisory.
FR_BODY = "/- Le theoreme `foo` repose sur 7 assertions. -/\n"
EN_BODY_METADATA_ONLY = (
    "/- EN sibling of `Bar.lean` (FR-first canonical).\n"
    "  Ratified 2026-07-04, issue #4980.\n"
    "  The theorem `foo` rests on 7 assertions. -/\n"
)
EN_BODY_DROPS_A_TOKEN = (
    "/- EN sibling of `Bar.lean` (FR-first canonical).\n"
    "  The theorem `foo` rests on some assertions. -/\n"
)
# The classic mirror-header form (`English mirror of`): excluded by design,
# and it must not pay for a comparison.
EN_BODY_PLAIN_MIRROR = (
    "/- English mirror of `Bar.lean` (FR-first canonical).\n"
    "  Ratified 2026-07-04, issue #4980. -/\n"
)
# A body carrying BOTH declarations, and dropping the FR number.
EN_BODY_HYBRID_DROPS_A_TOKEN = (
    "/- EN sibling of `Bar.lean` (FR-first canonical).\n"
    "  English mirror of `Bar.lean`.\n"
    "  The theorem `foo` rests on some assertions. -/\n"
)
THEOREM = "theorem foo : True := trivial\n"


def _write_pair(tmp_path: Path, en_body: str) -> tuple[Path, Path]:
    fr = tmp_path / "Foo.lean"
    en = tmp_path / "Foo_en.lean"
    fr.write_text(FR_BODY + THEOREM, encoding="utf-8")
    en.write_text(en_body + THEOREM, encoding="utf-8")
    return fr, en


def test_a_sibling_header_that_loses_nothing_is_excluded(tmp_path):
    """The metadata-only sibling header: no FR token is dropped, so the pair
    is excluded instead of reporting the EN metadata as a loss."""
    fr, en = _write_pair(tmp_path, EN_BODY_METADATA_ONLY)
    report = compare_files(fr, en)
    assert report["pairs_excluded"] == 1, report
    assert report["pairs_compared"] == 0, report
    hard = [f for f in report["findings"] if f["severity"] == HARD]
    assert hard == [], hard


def test_a_sibling_header_that_drops_a_fr_token_is_still_compared(tmp_path):
    """Control POSITIVE: the exclusion must not blind the organ.

    The EN side here also translates the FR summary -- and drops the number
    `7` on the way. The loss is a real one and must still be reported.
    """
    fr, en = _write_pair(tmp_path, EN_BODY_DROPS_A_TOKEN)
    report = compare_files(fr, en)
    assert report["pairs_excluded"] == 0, report
    assert report["pairs_compared"] == 1, report
    hard = [f for f in report["findings"] if f["severity"] == HARD]
    fr_side = [f["token"] for f in hard if f["side"] == "FR"]
    assert fr_side == ["7"], hard


def test_a_plain_mirror_header_is_excluded_without_comparing(tmp_path,
                                                            monkeypatch):
    """Cost: a pair excluded as a plain mirror header pays for NO
    comparison at all (review of #24591, yellow 1).

    The comparison used to be computed before the exclusion test and thrown
    away right after -- doubling the work on every excluded header of the
    `--all` corpus (188 pairs out of 9541, measured on the repository).
    """
    calls: list[tuple[str, str]] = []
    original = org.compare_bodies

    def counting(fr_body, en_body, decls=None, is_module=False):
        calls.append((fr_body, en_body))
        return original(fr_body, en_body, decls, is_module=is_module)

    monkeypatch.setattr(org, "compare_bodies", counting)
    fr, en = _write_pair(tmp_path, EN_BODY_PLAIN_MIRROR)
    report = compare_files(fr, en)
    assert report["pairs_excluded"] == 1, report
    assert report["pairs_compared"] == 0, report
    assert calls == [], calls


def test_a_hybrid_body_that_drops_a_fr_token_is_still_compared(tmp_path):
    """Precedence: the `sibling` branch is evaluated FIRST (review of
    #24591, yellow 2).

    A body carrying BOTH declarations (`EN sibling of` AND `English mirror
    of`) and dropping the FR number is reported, not silently excluded: the
    exclusion must never hide a real loss.
    """
    fr, en = _write_pair(tmp_path, EN_BODY_HYBRID_DROPS_A_TOKEN)
    report = compare_files(fr, en)
    assert report["pairs_excluded"] == 0, report
    assert report["pairs_compared"] == 1, report
    hard = [f for f in report["findings"] if f["severity"] == HARD]
    fr_side = [f["token"] for f in hard if f["side"] == "FR"]
    assert fr_side == ["7"], hard


def test_the_sensitivity_family_carries_no_hard_finding():
    """Integration control on the family that carried the 39 spurious
    findings (`VectorSpace`, `Operator`, `Hypercube`, `MainTheorem`)."""
    for name in ("VectorSpace", "Operator", "Hypercube", "MainTheorem"):
        fr = SENSITIVITY / f"{name}.lean"
        en = SENSITIVITY / f"{name}_en.lean"
        assert fr.exists() and en.exists(), (fr, en)
        report = compare_files(fr, en)
        hard = [f for f in report["findings"] if f["severity"] == HARD]
        assert hard == [], (name, hard)


if __name__ == "__main__":
    import tempfile

    with tempfile.TemporaryDirectory() as _tmp:
        test_a_sibling_header_that_loses_nothing_is_excluded(Path(_tmp))
    print("ok")
