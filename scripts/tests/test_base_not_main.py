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


# ---------------------------------------------------------------------------
# Couverture CI perdue sur une base empilee (#16194)
# ---------------------------------------------------------------------------
#
# L'advisory disait la cible de livraison, jamais la couverture perdue : un
# reviewer a lu le premier et en a conclu l'inverse sur #15940. Ces tests
# tiennent la mesure qui rend le trou visible.

from base_not_main import (  # noqa: E402
    _branch_filter_matches,
    _glob_to_regex,
    _paths_filter_matches,
    build_comment as _bc,
    workflows_skipped_by_base,
)


def test_glob_star_does_not_cross_a_slash():
    """`scripts/*` ne doit PAS matcher `scripts/a/b.py` : fnmatch dirait oui,
    GitHub dit non, et le workflow serait compte comme declenche a tort."""
    assert _glob_to_regex("scripts/*").match("scripts/a.py")
    assert not _glob_to_regex("scripts/*").match("scripts/a/b.py")


def test_glob_doublestar_crosses_slashes():
    assert _glob_to_regex("scripts/**").match("scripts/a/b.py")
    assert _glob_to_regex("scripts/**").match("scripts/a.py")
    assert _glob_to_regex("**/*.py").match("a/b/c.py")


def test_glob_question_mark_is_one_non_slash_char():
    assert _glob_to_regex("a?c.py").match("abc.py")
    assert not _glob_to_regex("a?c.py").match("a/c.py")


def test_branch_filter_gated_on_main_excludes_an_embedded_base():
    cfg = {"branches": ["main"]}
    assert _branch_filter_matches(cfg, "main")
    assert not _branch_filter_matches(cfg, "fix/15398-slidev-overlay")


def test_no_branch_filter_matches_every_base():
    assert _branch_filter_matches({"types": ["opened"]}, "fix/whatever")
    assert _branch_filter_matches(None, "fix/whatever")


def test_branches_ignore_main_runs_on_every_base_but_main():
    cfg = {"branches-ignore": ["main"]}
    assert not _branch_filter_matches(cfg, "main")
    assert _branch_filter_matches(cfg, "feature/x")


def test_paths_filter_is_satisfied_by_the_changed_files():
    cfg = {"paths": ["scripts/**", "tests/**"]}
    assert _paths_filter_matches(cfg, ["scripts/post_bake_slides.py"])
    assert not _paths_filter_matches(cfg, ["README.md"])


def test_paths_ignore_alone_runs_unless_all_files_are_ignored():
    cfg = {"paths-ignore": ["docs/**"]}
    assert _paths_filter_matches(cfg, ["docs/a.md", "scripts/b.py"])
    assert not _paths_filter_matches(cfg, ["docs/a.md", "docs/b.md"])


def _write_wf(directory, name, body):
    (directory / name).write_text(body, encoding="utf-8")


def test_skipped_needs_both_the_branch_gate_and_a_satisfied_paths_filter(tmp_path):
    """Le coeur de la mesure : un workflow n'est compte que si sa conjonction
    est satisfaite pour `main` ET pas pour la base. Sinon on annoncerait au
    reviewer une perte qui n'en est pas une."""
    _write_wf(tmp_path, "gated.yml", """
on:
  pull_request:
    branches: [main]
    paths: ['scripts/**']
""")
    _write_wf(tmp_path, "unfiltered.yml", """
on:
  pull_request:
    types: [opened]
""")
    _write_wf(tmp_path, "gated_but_offtopic.yml", """
on:
  pull_request:
    branches: [main]
    paths: ['lean/**']
""")
    skipped = workflows_skipped_by_base(
        tmp_path, "fix/stacked-base", ["scripts/a.py"])
    assert skipped == ["gated.yml"]


def test_skipped_is_empty_when_the_base_is_main(tmp_path):
    _write_wf(tmp_path, "gated.yml", """
on:
  pull_request:
    branches: [main]
""")
    assert workflows_skipped_by_base(tmp_path, "main", ["scripts/a.py"]) == []


def test_founding_instance_scripts_tests_is_lost_on_a_stacked_base():
    """Temoin #15751 : la PR empilee modifiait l'outil ET sa propre suite, et
    `Scripts Tests (CPU)` n'a jamais tourne -- les deux fichiers matchaient
    `paths: scripts/**` terme a terme ; c'est le filtre de branche qui a tout
    eteint. Teste sur l'arbre reel, comme le lock test de l'umbrella."""
    from pathlib import Path
    wfdir = Path(__file__).resolve().parents[2] / ".github" / "workflows"
    skipped = workflows_skipped_by_base(
        wfdir, "fix/15398-slidev-overlay",
        ["scripts/post_bake_slides.py", "scripts/tests/test_post_bake_slides.py"])
    assert "scripts-tests.yml" in skipped
    assert "pr-gate.yml" in skipped


def test_comment_names_the_missing_workflows():
    body = _bc("feature/x", 1, "t", ["scripts-tests.yml", "pr-gate.yml"])
    assert "Couverture CI perdue" in body
    assert "**2 workflow(s)**" in body
    assert "`scripts-tests.yml`" in body
    assert "Un check absent n'est pas un check vert" in body
    assert "stack legitime" in body  # la section d'origine survit


def test_comment_is_unchanged_when_nothing_is_skipped():
    """Retro-compatibilite : le corps sans mesure reste byte-identique."""
    assert _bc("feature/x", 1, "t") == _bc("feature/x", 1, "t", [])
    assert "Couverture CI perdue" not in _bc("feature/x", 1, "t")
