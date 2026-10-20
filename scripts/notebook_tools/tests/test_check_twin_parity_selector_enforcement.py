"""Tests for check_twin_parity --pair/--family enforcement (#21281, reliquat #20578).

Before this fix, three modes silently IGNORED --pair/--family:

| Mode                              | --pair         | --family       | Selecteur inconnu              |
|-----------------------------------|----------------|----------------|--------------------------------|
| --per-pair                        | ignored        | applied        | "Aucune paire pour...", rc 0   |
| --summary-by-verdict              | ignored        | ignored        | rc 0, "Summary by verdict"     |
| --coverage                        | ignored        | ignored        | rc 0, recensement complet      |

The most dangerous case: --check --per-pair --family <inconnue> returned rc 0 on
zero pairs evaluated -- the "success on zero pairs" anti-pattern that #20578
removed from --check.

This fix enforces two distinct policies:

1. **--per-pair --base <ref>** : APPLIQUE --pair (single-pair evaluation) and
   --family (existing filter, now with rc 2 on unknown).  A lane that wants to
   replay the gate on a single pair no longer pays the 157-pair walk.
2. **--coverage / --summary-by-verdict** : REFUSE --pair/--family at argparse
   level (p.error, rc 2).  These are full-coverage modes where a selector
   denotes nothing.

These tests pin the enforcement at the argparse layer (no real git walk) so
they run in <1s and survive a registry of 157 pairs.
"""
from __future__ import annotations

import os
import sys
from pathlib import Path

import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from check_twin_parity import main  # noqa: E402


# ---------------------------------------------------------------------------
# --coverage : refus a l'analyse de --pair/--family
# ---------------------------------------------------------------------------


def test_coverage_refuses_pair_at_argparse(monkeypatch, capsys):
    """--coverage --pair Inexistante : argparse refuse (rc 2), pas de silence."""
    monkeypatch.setattr(sys, "argv",
                        ["check_twin_parity.py", "--coverage", "--pair", "Inexistante"])
    with pytest.raises(SystemExit) as exc:
        main()
    assert exc.value.code == 2
    err = capsys.readouterr().err
    assert "--coverage est un mode de recensement integral" in err
    assert "--pair" in err


def test_coverage_refuses_family_at_argparse(monkeypatch, capsys):
    """--coverage --family Quelconque : argparse refuse (rc 2)."""
    monkeypatch.setattr(sys, "argv",
                        ["check_twin_parity.py", "--coverage", "--family", "Quelconque"])
    with pytest.raises(SystemExit) as exc:
        main()
    assert exc.value.code == 2
    err = capsys.readouterr().err
    assert "--coverage est un mode de recensement integral" in err
    assert "--family" in err


# ---------------------------------------------------------------------------
# --summary-by-verdict : refus a l'analyse de --pair/--family
# ---------------------------------------------------------------------------


def test_summary_by_verdict_refuses_pair_at_argparse(monkeypatch, capsys):
    """--summary-by-verdict --pair Inexistante : argparse refuse (rc 2)."""
    monkeypatch.setattr(sys, "argv",
                        ["check_twin_parity.py", "--summary-by-verdict",
                         "--pair", "Inexistante"])
    with pytest.raises(SystemExit) as exc:
        main()
    assert exc.value.code == 2
    err = capsys.readouterr().err
    assert "--summary-by-verdict est un mode de recensement integral" in err


def test_summary_by_verdict_refuses_family_at_argparse(monkeypatch, capsys):
    """--summary-by-verdict --family Quelconque : argparse refuse (rc 2)."""
    monkeypatch.setattr(sys, "argv",
                        ["check_twin_parity.py", "--summary-by-verdict",
                         "--family", "Quelconque"])
    with pytest.raises(SystemExit) as exc:
        main()
    assert exc.value.code == 2
    err = capsys.readouterr().err
    assert "--summary-by-verdict est un mode de recensement integral" in err


# ---------------------------------------------------------------------------
# --per-pair --family inconnue : rc 2 (etait rc 0 sur zero paires evaluees)
# ---------------------------------------------------------------------------


def test_per_pair_unknown_family_returns_rc2(monkeypatch, capsys):
    """--check --per-pair --base HEAD --family Inexistante : rc 2 + liste
    des familles connues, pas rc 0 sur le recensement integral."""
    monkeypatch.setattr(sys, "argv",
                        ["check_twin_parity.py", "--check", "--per-pair",
                         "--base", "HEAD", "--family", "Inexistante"])
    rc = main()
    assert rc == 2
    err = capsys.readouterr().err
    assert "--family" in err
    assert "inconnue" in err
    assert "Familles connues" in err


def test_per_pair_unknown_pair_returns_rc2(monkeypatch, capsys):
    """--check --per-pair --base HEAD --pair Inexistante : rc 2 + liste des
    noms connus (symetrique du cas famille, point 3 de la review -- la
    branche la plus neuve du diff etait la seule non epinglee)."""
    monkeypatch.setattr(sys, "argv",
                        ["check_twin_parity.py", "--check", "--per-pair",
                         "--base", "HEAD", "--pair", "Inexistante"])
    rc = main()
    assert rc == 2
    err = capsys.readouterr().err
    assert "--pair" in err
    assert "inconnue" in err
    assert "Noms connus" in err


# ---------------------------------------------------------------------------
# Non-regression : --summary-by-verdict --json reste valide
# ---------------------------------------------------------------------------


def test_summary_by_verdict_no_selector_still_works(monkeypatch, capsys):
    """--summary-by-verdict --json (sans selecteur) : rc 0, JSON sur stdout.

    Non-regression : le mode de recensement integral sans selecteur reste
    fonctionnel, on n'a ferme que les selecteurs sans portee (#21281).
    """
    monkeypatch.setattr(sys, "argv",
                        ["check_twin_parity.py", "--summary-by-verdict", "--json"])
    rc = main()
    assert rc == 0
    out = capsys.readouterr().out
    # JSON valide avec les cles attendues
    import json as _json
    parsed = _json.loads(out)
    assert parsed["mode"] == "summary_by_verdict"
    assert "counts" in parsed
    assert "total" in parsed


if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-v"]))
