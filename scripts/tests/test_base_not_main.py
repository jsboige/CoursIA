#!/usr/bin/env python3
"""Unit tests for the pure core of base_not_main.py (#10918 part a).

``build_comment`` is network-free; the gh wiring is exercised end-to-end in CI
on real PRs. The two comment variants encode the acceptance behaviour: a base
with an open PR towards main is a legitimate stack (noted), a base with none is
an orphan in formation (remedy named).
"""

import sys
import os

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from base_not_main import build_comment, MARKER_START, MARKER_END  # noqa: E402


def test_comment_stack_when_open_pr_exists():
    body = build_comment("feature/c8266-sendov-theoremes", 1, "Lean-20 notebook")
    assert MARKER_START in body and MARKER_END in body
    assert "stack legitime" in body
    assert "1 PR ouverte" in body
    assert "aucune PR ouverte" not in body


def test_comment_orphan_risk_when_no_open_pr():
    body = build_comment("fix/gitleaks-pin-8243", 0, "Z3-Python-13 enrichment")
    assert "Aucune PR ouverte" in body
    assert "orphelin" in body
    assert "rebaser cette PR sur `main`" in body
