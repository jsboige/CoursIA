#!/usr/bin/env python3
"""Unit tests for check_concurrency_conj.py (#13488).

Acceptance 1 (positive control): a fixture workflow carrying the full
conjunction (push:main + group portant github.ref + cancel-in-progress:true
literal) MUST appear in the offenders list. The fixture is the founding
incident measured on 2026-08-28 by #13372.

Acceptance 2 (negative control): the three workflows fixed by #13372
(banner-guard, markdown-rendering-guard, series-naming-gate) and the
allowlisted quarto-pages-deploy MUST NOT appear.

Acceptance 3 (allowlist discipline): the allowlist is by file name, no glob;
a name absent from the allowlist with the conjunction is an offender.
"""

import os
import sys
import tempfile
import textwrap
from pathlib import Path

import pytest

# scripts/ci/ is the package root for the CI guard family.
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "ci"))

from check_concurrency_conj import (  # noqa: E402
    ALLOWLIST,
    _branches_include_main,
    _cancel_is_literal_true,
    _group_has_github_ref,
    offenders,
)


# --- Fixtures (acceptance 1: positive control) --------------------------------

CONJUNCTION_YML = textwrap.dedent("""\
    name: conj-pos
    on:
      push:
        branches: [main]
    concurrency:
      group: conj-pos-${{ github.ref }}
      cancel-in-progress: true
    jobs:
      j:
        runs-on: ubuntu-latest
        steps:
          - run: echo hi
""")


MALFORMED_YML = textwrap.dedent("""\
    name: malformed
    on:
      push:
        branches: [main]
      invalid_yaml_indicator: : :
    concurrency:
      group: malformed-${{ github.ref }}
      cancel-in-progress: true
    jobs:
      j:
        runs-on: ubuntu-latest
        steps:
          - run: echo hi
""")


def _write_workflow(tmpdir: Path, name: str, body: str) -> Path:
    wf = tmpdir / ".github" / "workflows"
    wf.mkdir(parents=True, exist_ok=True)
    target = wf / name
    target.write_text(body, encoding="utf-8")
    return target


# --- Predicate unit tests -----------------------------------------------------


def test_branches_include_main_list():
    assert _branches_include_main({"push": {"branches": ["main"]}}) is True


def test_branches_include_main_scalar():
    assert _branches_include_main({"push": {"branches": "main"}}) is True


def test_branches_include_main_default():
    """push: with no branches filter covers main (default)."""
    assert _branches_include_main({"push": {}}) is True


def test_branches_include_main_wildcard():
    assert _branches_include_main({"push": {"branches": ["*"]}}) is True


def test_branches_include_main_absent():
    assert _branches_include_main({"push": {"branches": ["dev"]}}) is False


def test_branches_include_main_no_push():
    assert _branches_include_main({"pull_request": {"branches": ["main"]}}) is False


def test_parse_workflow_malformed_returns_none():
    """Regression test for #13732: yaml.YAMLObject is not an exception class.

    Before the fix, the clause `except yaml.YAMLObject:` could never trigger
    (YAMLObject is the base class for custom tags, not an exception). A
    malformed workflow therefore raised uncaught (YAMLError) and the caller
    could not tell a parsing failure from a benign non-dict parse. After the
    fix to `except yaml.YAMLError:`, malformed input is converted to `None`,
    matching the comment on _parse_workflow that says "Returns the parsed
    dict or None".
    """
    from check_concurrency_conj import _parse_workflow
    yaml = __import__("yaml")
    result = _parse_workflow(MALFORMED_YML, yaml)
    assert result is None, (
        f"malformed YAML should parse to None, got {result!r}; the "
        "YAMLError exception class is the one PyYAML actually raises "
        "on malformed input."
    )


def test_group_has_github_ref_positive():
    assert _group_has_github_ref("foo-${{ github.ref }}") is True


def test_group_has_github_ref_nested():
    """Any github.ref occurrence is enough, even nested in a conditional."""
    assert _group_has_github_ref(
        "${{ github.event_name == 'pull_request' && github.ref || github.sha }}"
    ) is True


def test_group_has_github_ref_negative():
    assert _group_has_github_ref("foo-${{ github.sha }}") is False


def test_group_has_github_ref_none():
    assert _group_has_github_ref(None) is False


def test_cancel_is_literal_true_bool():
    """The literal-true case is the one that breaks on cascade."""
    assert _cancel_is_literal_true(True) is True


def test_cancel_is_literal_true_template_string():
    """Template strings are the fix from #13372 -- accept as not-literal."""
    assert _cancel_is_literal_true("${{ github.event_name == 'pull_request' }}") is False


# --- Acceptance 1: positive control -------------------------------------------


def test_conjunction_workflow_is_offender(tmp_path: Path):
    """The conjunction MUST produce an offender (acceptance 1, positive control)."""
    _write_workflow(tmp_path, "conj-pos.yml", CONJUNCTION_YML)
    offs = offenders(workflows_dir=str(tmp_path / ".github" / "workflows"))
    names = [o["file"] for o in offs]
    assert "conj-pos.yml" in names, (
        f"workflow carrying the full conjunction was not flagged; "
        f"offenders={names}. Acceptance 1 broken."
    )


def test_conjunction_workflow_cites_fix_form(tmp_path: Path):
    """The error message must name the canonical replacement."""
    _write_workflow(tmp_path, "conj-pos.yml", CONJUNCTION_YML)
    offs = offenders(workflows_dir=str(tmp_path / ".github" / "workflows"))
    o = next(o for o in offs if o["file"] == "conj-pos.yml")
    assert "github.event_name == 'pull_request'" in o["fix"]
    assert o["line_group"] > 0, "must cite the concurrency block line"


# --- Acceptance 2: negative control -------------------------------------------


def test_banner_guard_after_fix13372_is_clean(tmp_path: Path):
    """banner-guard was fixed by #13372 (cancel conditioned on pull_request)."""
    body = textwrap.dedent("""\
        name: banner-guard
        on:
          push:
            branches: [main]
          pull_request:
        concurrency:
          group: banner-guard-${{ github.event_name == 'pull_request' && github.ref || github.sha }}
          cancel-in-progress: ${{ github.event_name == 'pull_request' }}
        jobs:
          j:
            runs-on: ubuntu-latest
            steps:
              - run: echo hi
    """)
    _write_workflow(tmp_path, "banner-guard.yml", body)
    offs = offenders(workflows_dir=str(tmp_path / ".github" / "workflows"))
    names = [o["file"] for o in offs]
    assert "banner-guard.yml" not in names, (
        f"banner-guard (fixed by #13372) flagged; offenders={names}."
    )


def test_quarto_pages_deploy_allowlist_is_respected(tmp_path: Path):
    """quarto-pages-deploy is allowlisted (deploy supersedes prior)."""
    body = textwrap.dedent("""\
        name: pages-deploy
        on:
          push:
            branches: [main]
        concurrency:
          group: pages-deploy-${{ github.event_name }}-${{ github.ref }}
          cancel-in-progress: true
        jobs:
          deploy:
            runs-on: ubuntu-latest
            steps:
              - run: echo deploy
    """)
    _write_workflow(tmp_path, "quarto-pages-deploy.yml", body)
    offs = offenders(workflows_dir=str(tmp_path / ".github" / "workflows"))
    names = [o["file"] for o in offs]
    assert "quarto-pages-deploy.yml" not in names, (
        f"quarto-pages-deploy (allowlisted) flagged; offenders={names}."
    )


def test_workflow_without_push_main_is_clean(tmp_path: Path):
    """cancel-in-progress:true without push:main is harmless (per #13488 body)."""
    body = textwrap.dedent("""\
        name: pr-only
        on:
          pull_request:
        concurrency:
          group: pr-only-${{ github.ref }}
          cancel-in-progress: true
        jobs:
          j:
            runs-on: ubuntu-latest
            steps:
              - run: echo hi
    """)
    _write_workflow(tmp_path, "pr-only.yml", body)
    offs = offenders(workflows_dir=str(tmp_path / ".github" / "workflows"))
    names = [o["file"] for o in offs]
    assert "pr-only.yml" not in names


# --- Acceptance 3: allowlist discipline ---------------------------------------


def test_allowlist_is_by_name_no_glob():
    """Allowlist must be exact file names -- no glob, no partial match."""
    assert "quarto-pages-deploy.yml" in ALLOWLIST
    # No glob / wildcard characters.
    for name in ALLOWLIST:
        assert "*" not in name
        assert "?" not in name
        assert "[" not in name


def test_non_allowlisted_with_conjunction_is_offender(tmp_path: Path):
    """A new workflow with the conjunction but no allowlist entry is flagged.

    The cliquet -- any new file carrying the bug is caught.
    """
    body = textwrap.dedent("""\
        name: new-buggy
        on:
          push:
            branches: [main]
        concurrency:
          group: new-buggy-${{ github.ref }}
          cancel-in-progress: true
        jobs:
          j:
            runs-on: ubuntu-latest
            steps:
              - run: echo hi
    """)
    _write_workflow(tmp_path, "new-buggy-deploy.yml", body)  # not allowlisted
    offs = offenders(workflows_dir=str(tmp_path / ".github" / "workflows"))
    names = [o["file"] for o in offs]
    assert "new-buggy-deploy.yml" in names, (
        "non-allowlisted new workflow with the conjunction was not flagged; "
        "the gate is dead."
    )
