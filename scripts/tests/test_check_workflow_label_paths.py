"""Tests for scripts/check_workflow_label_paths.py (issue #8822).

The guard enforces a STRUCTURAL invariant (a paths-filtered label-poser must
list its own file under ``paths:``), so it is blocking by design. These tests
prove the two controls #8822 demands:

- ACCEPTANCE 1 (positive control): a label-posing + paths-filtered workflow
  that does NOT self-cover FAILS the guard. A gate never seen to fail is not a
  gate (#8681).
- ACCEPTANCE 2 (negative control): already-self-covered workflows pass, and the
  ~48 path-filtered workflows that pose NO label are not flagged (the guard
  fires only on the conjunction label AND paths -- #8782).

Plus the denominator contract (ACCEPTANCE 3): scanning nothing fails loudly, so
a guard that enumerated zero workflows cannot read as a quiet pass (#8678/#8680).

Pure functions on tmp_path workflow fixtures -- no I/O on the real repo. The
real-repo run (proving the measured 1/1 violator ``exercises-advisory.yml`` goes
red before the one-liner and green after) is captured in the PR body, not here.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

# test_X.py lives in scripts/tests/; parent.parent from the file = scripts/
# (the home of check_workflow_label_paths.py). Matches the established pattern
# of test_check_docs_links.py for scripts/-root guard modules.
_scripts_dir = Path(__file__).resolve().parent.parent
if str(_scripts_dir) not in sys.path:
    sys.path.insert(0, str(_scripts_dir))

import check_workflow_label_paths as guard  # noqa: E402

WORKFLOWS = Path(".github/workflows")


def _wf(repo_root: Path, name: str, body: str) -> Path:
    """Write a workflow fixture under <repo_root>/.github/workflows/<name>."""
    p = repo_root / WORKFLOWS / name
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(body, encoding="utf-8")
    return p


# A label-posing run step (the two ways the guard detects: gh label create +
# --add-label). Both appear in exercises-advisory.yml on `main`.
_LABEL_RUN = """\
        run: |
          gh label create "x" --force 2>/dev/null || true
          gh pr edit "$PR" --add-label "x" || true
"""


def _workflow(paths: list[str] | None, run: str | None = None) -> str:
    """Build a workflow body with the given on.pull_request.paths (or none)."""
    if paths is None:
        on = "on:\n  pull_request:\n    branches: [main]\n"
    else:
        globs = "\n".join(f"      - {p!r}" for p in paths)
        on = f"on:\n  pull_request:\n    branches: [main]\n    paths:\n{globs}\n"
    jobs = ""
    if run is not None:
        jobs = (
            "permissions:\n  pull-requests: write\n"
            "jobs:\n  x:\n    runs-on: ubuntu-latest\n    steps:\n"
            "      - run: echo hi\n"
            f"{run}"
        )
    else:
        jobs = "jobs:\n  x:\n    runs-on: ubuntu-latest\n    steps:\n      - run: echo hi\n"
    return on + "workflow_dispatch:\n\n" + jobs


# ---------------------------------------------------------------------------
# ACCEPTANCE 1 -- positive control: a non-self-covering label-poser FAILS
# ---------------------------------------------------------------------------


class TestPositiveControl:
    def test_violating_workflow_is_flagged(self, tmp_path):
        """A label-poser filtered by paths that omits its own file FAILS.

        This is the defect demonstrated on PR #8820: exercises-advisory.yml has
        `paths: ['**/*.ipynb']` (notebooks only), poses a label, but its own
        `.github/workflows/exercises-advisory.yml` is not in paths -- so it
        cannot re-run to remove the label once the .ipynb leaves the diff.
        """
        _wf(
            tmp_path, "advisory.yml",
            _workflow(paths=["**/*.ipynb"], run=_LABEL_RUN),
        )
        result = guard.scan(tmp_path)
        assert len(result.violations) == 1
        v = result.violations[0]
        assert v.path == ".github/workflows/advisory.yml"
        assert v.poses_label is True
        assert v.has_paths is True
        assert v.self_covered is False
        assert v.violation is True

    def test_main_exits_nonzero_on_violation(self, tmp_path, capsys):
        """Blocking (criterion 4): a violation makes main() return 1, not 0."""
        _wf(
            tmp_path, "advisory.yml",
            _workflow(paths=["**/*.ipynb"], run=_LABEL_RUN),
        )
        rc = guard.main(["--root", str(tmp_path)])
        assert rc == 1

    def test_glob_star_only_within_segment(self, tmp_path):
        """`*.yml` (single star, no `**`) must NOT match a path with a `/` --
        it matches only the basename, so `.github/workflows/x.yml` is not
        covered. Guards against a too-greedy matcher that would false-pass.
        """
        _wf(
            tmp_path, "guard.yml",
            _workflow(paths=["*.yml"], run=_LABEL_RUN),
        )
        result = guard.scan(tmp_path)
        # `*.yml` does not match `.github/workflows/guard.yml` (has separators),
        # so this is a real violation.
        assert len(result.violations) == 1


# ---------------------------------------------------------------------------
# ACCEPTANCE 2 -- negative control: self-covered + out-of-scope are NOT flagged
# ---------------------------------------------------------------------------


class TestNegativeControl:
    def test_self_covered_literal_path_passes(self, tmp_path):
        """Listing the workflow's own literal path satisfies the guard."""
        own = ".github/workflows/advisory.yml"
        _wf(
            tmp_path, "advisory.yml",
            _workflow(paths=["**/*.ipynb", own], run=_LABEL_RUN),
        )
        result = guard.scan(tmp_path)
        assert result.violations == []
        ok = [v for v in result.verdicts if v.poses_label and v.has_paths]
        assert ok and ok[0].self_covered is True

    def test_self_covered_via_doublestar_glob_passes(self, tmp_path):
        """.github/workflows/** also self-covers (the dominant repo convention:
        e.g. banner-guard.yml uses its literal path, but the glob form must
        also pass -- 20 self-covered workflows, varied spellings)."""
        for glob in [
            ".github/workflows/**",
            ".github/**",
            ".github/workflows/advisory.yml",
        ]:
            d = tmp_path / glob.replace("/", "_").replace("*", "X")
            _wf(
                d, "advisory.yml",
                _workflow(paths=["**/*.ipynb", glob], run=_LABEL_RUN),
            )
            result = guard.scan(d)
            assert result.violations == [], f"glob {glob!r} should self-cover"

    def test_label_poser_without_paths_not_flagged(self, tmp_path):
        """A label-poser with NO paths filter always runs -- it can always
        clean up its own label. stale-base-warning.yml and variation-tag-guard.yml
        are this shape (the two other label-posers); they are out of scope."""
        _wf(
            tmp_path, "nopath.yml",
            _workflow(paths=None, run=_LABEL_RUN),
        )
        result = guard.scan(tmp_path)
        assert result.violations == []
        v = result.verdicts[0]
        assert v.poses_label is True
        assert v.has_paths is False  # not subject to the guard

    def test_documentation_comment_not_counted_as_label_poser(self, tmp_path):
        """A workflow that only DOCUMENTS the gh pattern in a header comment
        (no active label command) must NOT be counted as a label-poser. This is
        the self-referential case: label-paths-guard.yml explains the convention
        in comments but poses no label -- without comment-stripping the guard
        would inflate its own denominator (#8822: count precisely)."""
        body = (
            "# Issue #8822. A workflow that runs `gh pr edit --add-label` or\n"
            "# `gh label create` and is filtered by paths must self-cover.\n"
            "# This guard enforces that.\n"
            "on:\n  pull_request:\n    branches: [main]\n"
            "    paths:\n      - '.github/workflows/**'\n"
            "workflow_dispatch:\n\n"
            "jobs:\n  x:\n    runs-on: ubuntu-latest\n"
            "    steps:\n      - run: python scripts/check_x.py\n"
        )
        _wf(tmp_path, "selfdoc.yml", body)
        result = guard.scan(tmp_path)
        v = result.verdicts[0]
        # The only mention is in comments -- NOT an active label command.
        assert v.poses_label is False
        assert v.has_paths is True
        assert result.violations == []

    def test_paths_filtered_no_label_not_flagged(self, tmp_path):
        """A paths-filtered workflow that poses NO label is not flagged --
        the guard fires only on label AND paths conjointly (#8782: don't fire
        out of scope). 48 such workflows exist in the repo."""
        _wf(
            tmp_path, "plain.yml",
            _workflow(paths=["src/**"], run=None),
        )
        result = guard.scan(tmp_path)
        assert result.violations == []
        v = result.verdicts[0]
        assert v.poses_label is False
        assert v.has_paths is True

    def test_paths_ignore_only_not_treated_as_filter(self, tmp_path):
        """`paths-ignore` excludes rather than includes -- the workflow still
        runs on all non-ignored paths, so it can clean up. Must NOT be treated
        as a constraining `paths:` filter (would false-flag)."""
        body = (
            "on:\n  pull_request:\n    branches: [main]\n"
            "    paths-ignore:\n      - '**/*.md'\n"
            "workflow_dispatch:\n\n"
            "permissions:\n  pull-requests: write\n"
            "jobs:\n  x:\n    runs-on: ubuntu-latest\n    steps:\n"
            "      - run: gh pr edit \"$PR\" --add-label \"x\" || true\n"
        )
        _wf(tmp_path, "ignored.yml", body)
        result = guard.scan(tmp_path)
        # paths-ignore is not a constraining filter -> has_paths is False ->
        # not subject (a label-poser, but always able to clean up).
        assert result.violations == []
        v = result.verdicts[0]
        assert v.poses_label is True
        assert v.has_paths is False

    def test_main_exits_zero_when_clean(self, tmp_path, capsys):
        """Blocking guard returns 0 only when every label-poser self-covers."""
        _wf(
            tmp_path, "advisory.yml",
            _workflow(
                paths=["**/*.ipynb", ".github/workflows/advisory.yml"],
                run=_LABEL_RUN,
            ),
        )
        rc = guard.main(["--root", str(tmp_path)])
        assert rc == 0

    def test_json_mode_stdout_is_pure_json(self, tmp_path, capsys):
        """--json must emit ONLY a JSON document on stdout -- a trailing PASS
        line would corrupt json.loads. The verdict (PASS/FAIL) goes to stderr."""
        _wf(
            tmp_path, "ok.yml",
            _workflow(
                paths=["**/*.ipynb", ".github/workflows/ok.yml"],
                run=_LABEL_RUN,
            ),
        )
        rc = guard.main(["--root", str(tmp_path), "--json"])
        assert rc == 0
        captured = capsys.readouterr()
        # stdout must be valid JSON (no PASS/FAIL contamination).
        payload = json.loads(captured.out)
        assert "summary" in payload
        # The verdict is a stderr diagnostic, not stdout data.
        assert "PASS" in captured.err


# ---------------------------------------------------------------------------
# ACCEPTANCE 3 -- denominator printed + FAIL if zero scanned
# ---------------------------------------------------------------------------


class TestDenominator:
    def test_zero_scanned_fails_loudly(self, tmp_path, capsys):
        """A guard that scans nothing is blind -- it must FAIL, not pass
        silently (#8678/#8680). Wrong root / missing dir -> exit 1."""
        # tmp_path has no .github/workflows/ -> 0 examined.
        rc = guard.main(["--root", str(tmp_path)])
        assert rc == 1
        err = capsys.readouterr().err
        assert "scanned 0 workflows" in err

    def test_json_payload_exposes_denominator(self, tmp_path, capsys):
        """The JSON summary prints examined/label_posers/path_filtered/non_covered
        -- the four numbers that make the guard's coverage auditable at a
        glance (criterion 3: the denominator must be visible)."""
        _wf(
            tmp_path, "v.yml",
            _workflow(paths=["**/*.ipynb"], run=_LABEL_RUN),
        )
        _wf(
            tmp_path, "ok.yml",
            _workflow(
                paths=["**/*.ipynb", ".github/workflows/ok.yml"],
                run=_LABEL_RUN,
            ),
        )
        _wf(
            tmp_path, "plain.yml",
            _workflow(paths=["src/**"], run=None),
        )
        guard.main(["--root", str(tmp_path), "--json"])
        payload = json.loads(capsys.readouterr().out)
        s = payload["summary"]
        assert s["examined"] == 3
        assert s["label_posers"] == 2  # v.yml + ok.yml
        assert s["path_filtered_label_posers"] == 2
        assert s["non_covered"] == 1  # only v.yml
        assert len(payload["violations"]) == 1
        assert payload["violations"][0]["path"] == ".github/workflows/v.yml"

    def test_mixed_dir_only_violators_flagged(self, tmp_path):
        """A directory with several workflows flags exactly the violating
        ones -- the guard does not collapse or over-report."""
        _wf(tmp_path, "bad.yml",
            _workflow(paths=["**/*.ipynb"], run=_LABEL_RUN))            # violation
        _wf(tmp_path, "good.yml",
            _workflow(paths=["**/*.ipynb", ".github/workflows/good.yml"],
                      run=_LABEL_RUN))                                   # self-covered
        _wf(tmp_path, "nolabel.yml",
            _workflow(paths=["src/**"], run=None))                      # not subject
        _wf(tmp_path, "nopath.yml",
            _workflow(paths=None, run=_LABEL_RUN))                      # not subject
        result = guard.scan(tmp_path)
        paths = {v.path for v in result.violations}
        assert paths == {".github/workflows/bad.yml"}


# ---------------------------------------------------------------------------
# Glob matcher unit tests (the self-cover decision rests on this)
# ---------------------------------------------------------------------------


class TestGlobMatcher:
    def test_doublestar_across_segments(self):
        assert guard._path_matches([".github/workflows/**"],
                                   ".github/workflows/x.yml")
        assert guard._path_matches([".github/**"],
                                   ".github/workflows/x.yml")

    def test_single_star_within_segment(self):
        assert guard._path_matches(["*.yml"], "x.yml")
        assert not guard._path_matches(["*.yml"], "dir/x.yml")

    def test_literal_path(self):
        assert guard._path_matches([".github/workflows/x.yml"],
                                   ".github/workflows/x.yml")
        assert not guard._path_matches([".github/workflows/x.yml"],
                                       ".github/workflows/y.yml")

    def test_leading_slash_ignored(self):
        # GitHub paths are repo-root-relative; a leading / is a no-op.
        assert guard._path_matches(["/.github/workflows/x.yml"],
                                   ".github/workflows/x.yml")
