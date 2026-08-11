"""Tests for the structured bridge_verdict field (#10439).

Pins the registry-schema mechanism that lets a pair carry a formal bridge
verdict (SOTA-OK / RECOVERABLE-* / INTRINSIC) so a verdict already rendered in
prose ceases to be invisible to detectors -- and ceases to re-flag the pair as
a "parity gap" at every scan.

Covers:
  - validate_pair_fields: valid + invalid cases (out-of-enum verdict, INTRINSIC
    without reason, invalid parity_level).
  - --summary-by-verdict: counts pairs by verdict and computes the "actionable"
    denominator (total - INTRINSIC - SOTA-OK) without manual subtraction.
  - Fail-loud: an out-of-enum bridge_verdict makes --summary-by-verdict and
    --check exit with code 2, never silently ignored.
"""
from __future__ import annotations

import os
import sys

import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from check_twin_parity import (  # noqa: E402
    BRIDGE_VERDICTS,
    validate_pair_fields,
)


# --- validate_pair_fields -----------------------------------------------------

def test_no_verdict_is_valid():
    """A pair without bridge_verdict (the common case) is valid -- the field is
    optional, the pair stays 'actionnable'."""
    assert validate_pair_fields({"name": "X", "parity_level": "semantic"}) == []


def test_intrinsics_with_reason_is_valid():
    assert validate_pair_fields(
        {"name": "X", "bridge_verdict": "INTRINSIC", "bridge_verdict_reason": "why"}
    ) == []


@pytest.mark.parametrize("verdict", sorted(BRIDGE_VERDICTS))
def test_all_five_verdicts_accepted(verdict):
    """Each of the 5 sota-not-workaround verdicts is a valid value (with a reason
    when INTRINSIC)."""
    pair = {"name": "X", "bridge_verdict": verdict}
    if verdict == "INTRINSIC":
        pair["bridge_verdict_reason"] = "why"
    assert validate_pair_fields(pair) == []


def test_intrinsics_without_reason_is_rejected():
    """The verdict without the reasoning is worth nothing (#10439)."""
    errs = validate_pair_fields({"name": "X", "bridge_verdict": "INTRINSIC"})
    assert len(errs) == 1
    assert "bridge_verdict_reason" in errs[0]


def test_out_of_enum_verdict_rejected():
    errs = validate_pair_fields({"name": "X", "bridge_verdict": "NOPE"})
    assert len(errs) == 1
    assert "hors enum" in errs[0]


def test_blank_reason_is_treated_as_missing():
    """A whitespace-only reason must not satisfy the INTRINSIC requirement."""
    errs = validate_pair_fields(
        {"name": "X", "bridge_verdict": "INTRINSIC", "bridge_verdict_reason": "   "}
    )
    assert len(errs) == 1


# --- --summary-by-verdict + fail-loud (integration via main) ------------------

def _write_registry(tmp_path, pairs_yaml: str):
    """Materialize a minimal file-per-entry registry under tmp_path."""
    reg = tmp_path / "twin_pairs.d"
    reg.mkdir()
    (reg / "_schema.yaml").write_text("# schema doc\n", encoding="utf-8")
    (reg / "pair.yaml").write_text(pairs_yaml, encoding="utf-8")
    return reg


_OK_PAIR = '''\
- name: "Test Pair"
  family: Test
  python: a.ipynb
  csharp: b.ipynb
  parity_level: semantic
  audits:
    - date: "2026-01-01"
      by: test
      python_sha: abc
      csharp_sha: def
'''


def test_summary_by_verdict_counts_actionable(tmp_path, capsys):
    """INTRINSIC + SOTA-OK are subtracted from the actionable denominator."""
    reg = _write_registry(tmp_path, _OK_PAIR + '''\
- name: "Intrinsic Pair"
  family: Test
  python: c.ipynb
  csharp: d.ipynb
  parity_level: semantic
  bridge_verdict: INTRINSIC
  bridge_verdict_reason: "non-bridgeable"
  audits:
    - date: "2026-01-01"
      by: test
      python_sha: abc
      csharp_sha: def
''')
    from check_twin_parity import main
    rc = main(["--registry", str(reg), "--summary-by-verdict", "--json"])
    assert rc == 0
    import json
    out = json.loads(capsys.readouterr().out)
    assert out["counts"]["INTRINSIC"] == 1
    # 2 pairs total, 1 INTRINSIC -> 1 actionable
    assert out["actionable"] == 1
    assert out["total"] == 2


def test_summary_fail_loud_on_bad_verdict(tmp_path, capsys):
    """An out-of-enum verdict must fail-loud (exit 2), never be silently ignored
    in the summary."""
    reg = _write_registry(tmp_path, _OK_PAIR.replace(
        '  parity_level: semantic\n',
        '  parity_level: semantic\n  bridge_verdict: NOPE\n', 1))
    from check_twin_parity import main
    rc = main(["--registry", str(reg), "--summary-by-verdict"])
    assert rc == 2
    err = capsys.readouterr().err
    assert "SCHEMA ERROR" in err
    assert "NOPE" in err


def test_check_fail_loud_on_bad_verdict(tmp_path, capsys):
    """The normal --check mode also fails loud on a schema error (the registry is
    corrupt regardless of which mode reads it)."""
    reg = _write_registry(tmp_path, _OK_PAIR.replace(
        '  parity_level: semantic\n',
        '  parity_level: semantic\n  bridge_verdict: INTRINSIC\n', 1))  # INTRINSIC sans reason
    from check_twin_parity import main
    rc = main(["--registry", str(reg), "--check"])
    assert rc == 2
    assert "SCHEMA ERROR" in capsys.readouterr().err


if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-v"]))
