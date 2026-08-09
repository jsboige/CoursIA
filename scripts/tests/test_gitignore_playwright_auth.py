"""Tests for the defense-in-depth .gitignore pattern guarding Playwright `.auth/*.json` (issue #10144).

The pattern `**/*[Pp]laywright*/.auth/*.json` is added to the root `.gitignore`
as a safety net. The local `.gitignore` files of each Playwright subfolder
(e.g. ``MyIA.AI.Notebooks/.../Playwright-OWUI/.gitignore``) remain the
primary guard for that directory, but this rule catches new directories
(`Playwright-XYZ/.auth/*`) whose local `.gitignore` might be omitted.

These tests do NOT depend on the repository state — they instantiate a
fixture repo with a copy of the root `.gitignore` and ask ``git check-ignore``
for verdict on a battery of paths.

See https://github.com/jsboige/CoursIA/issues/10144 for the original finding.
"""
from __future__ import annotations

import shutil
import subprocess
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[2]
ROOT_GITIGNORE = REPO_ROOT / ".gitignore"


def _have_git() -> bool:
    return shutil.which("git") is not None


def _make_fixture_repo(tmp_path: Path) -> Path:
    """Copy the root .gitignore into a fresh tmp repo + init git there."""
    repo = tmp_path / "fixture_repo"
    repo.mkdir()
    (repo / ".gitignore").write_text(ROOT_GITIGNORE.read_text(encoding="utf-8"), encoding="utf-8")
    subprocess.run(["git", "init", "--quiet"], cwd=repo, check=True)
    subprocess.run(["git", "config", "user.email", "test@example.com"], cwd=repo, check=True)
    subprocess.run(["git", "config", "user.name", "Test"], cwd=repo, check=True)
    # Stage .gitignore so git check-ignore can resolve it
    subprocess.run(["git", "add", ".gitignore"], cwd=repo, check=True)
    return repo


def _check_ignore(repo: Path, target_path: str) -> tuple[bool, str]:
    """Return (ignored, rule_trace). ignored=True iff a rule catches the path."""
    result = subprocess.run(
        ["git", "check-ignore", "-v", target_path],
        cwd=repo,
        capture_output=True,
        text=True,
        check=False,
    )
    if result.returncode == 0:
        return True, result.stdout.strip()
    if result.returncode == 1:
        return False, ""
    raise RuntimeError(f"git check-ignore failed: {result.stderr}")


@pytest.mark.skipif(not _have_git(), reason="git not available")
def test_real_playwright_owui_auth_owui_json_ignored(tmp_path: Path) -> None:
    """The real Playwright-OWUI/.auth/owui.json MUST be ignored.

    G.1 firsthand: this is the real path produced by ``auth.setup.ts`` from the
    Playwright-OWUI series. Without a matching rule, the JWT would be committable.
    """
    repo = _make_fixture_repo(tmp_path)
    target = "MyIA.AI.Notebooks/GenAI/Plateformes-Conversationnelles/Open-WebUI/Playwright-OWUI/.auth/owui.json"
    # We cannot import the local .gitignore of Playwright-OWUI in this fixture
    # (it lives outside the root), so we test the root pattern only.
    # The local gitignore covers the real path on main; the root covers
    # any future Playwright-* variant.
    ignored, trace = _check_ignore(repo, target)
    # The root pattern is `**/*[Pp]laywright*/.auth/*.json` — does it match?
    # `**/MyIA.../Playwright-OWUI/.auth/owui.json` should match.
    assert ignored, f"Root pattern did NOT catch {target} (trace={trace!r})"
    # Verify the catch comes from the defense-in-depth rule, not from a wildcard.
    assert "[Pp]laywright" in trace, f"Wrong rule matched: {trace!r}"


@pytest.mark.skipif(not _have_git(), reason="git not available")
def test_invented_playwright_xyz_auth_ignored(tmp_path: Path) -> None:
    """A future directory Playwright-XYZ/.auth/*.json MUST be ignored even WITHOUT
    a local .gitignore. This is the core defense-in-depth claim of #10144.
    """
    repo = _make_fixture_repo(tmp_path)
    target = "anywhere/Playwright-XYZ/.auth/foo.json"
    ignored, trace = _check_ignore(repo, target)
    assert ignored, f"Root pattern did NOT catch invented {target} (trace={trace!r})"
    assert "[Pp]laywright" in trace, f"Wrong rule matched: {trace!r}"


@pytest.mark.skipif(not _have_git(), reason="git not available")
def test_lowercase_playwright_xyz_auth_ignored(tmp_path: Path) -> None:
    """The root .gitignore already has `**/playwright/.auth/` (lowercase) for
    the original tooling path. The new pattern should match this too.
    """
    repo = _make_fixture_repo(tmp_path)
    target = "anywhere/playwright/.auth/state.json"
    ignored, trace = _check_ignore(repo, target)
    assert ignored, f"Root pattern did NOT catch lowercase {target} (trace={trace!r})"
    # Could match either the old `**/playwright/.auth/` or the new defense rule;
    # both are fine — the important thing is that it IS ignored.


@pytest.mark.skipif(not _have_git(), reason="git not available")
def test_non_playwright_auth_NOT_ignored(tmp_path: Path) -> None:
    """A `.auth/x.json` outside any Playwright context MUST NOT be ignored
    by the new pattern (would be a false positive that could hide legitimate
    tracked files).
    """
    repo = _make_fixture_repo(tmp_path)
    target = "anywhere/random_dir/.auth/x.json"
    ignored, _trace = _check_ignore(repo, target)
    assert not ignored, "Root pattern caught a non-Playwright `.auth/` path — false positive"


@pytest.mark.skipif(not _have_git(), reason="git not available")
def test_any_p_laywright_first_char_variants_ignored(tmp_path: Path) -> None:
    """First-letter case variants (`P` or `p` followed by `laywright`) MUST be
    caught by either the bracketed `[Pp]laywright` rule or the existing lowercase
    `**/playwright/.auth/` rule. Order-dependence means we accept whichever
    matches — the important thing is ``git check-ignore`` returns ignored=True.

    NOTE: Only the FIRST character is covered by the bracket (and the lowercase
    rule). Mid-word case swaps like `pLaywright` (lowercase p + uppercase L) are
    NOT caught. This is a deliberate, bounded scope — the threat model is
    Playwright series names that follow the conventional PascalCase or
    lowercase spellings, not arbitrary mid-word case flips.
    """
    repo = _make_fixture_repo(tmp_path)
    for variant in (
        "anywhere/Playwright-XYZ/.auth/foo.json",   # PascalCase — bracket
        "anywhere/playwright-xyz/.auth/bar.json",   # lowercase — old rule
        "anywhere/PlaywrightFoo/.auth/x.json",      # PascalCase + concat — bracket
        "anywhere/playwrightFoo/.auth/y.json",      # lowercase + concat — old rule
    ):
        ignored, trace = _check_ignore(repo, variant)
        assert ignored, f"First-letter pattern did NOT catch {variant} (trace={trace!r})"
        # Either the new bracketed rule OR the existing lowercase rule may match;
        # both are valid (and the lowercase one takes precedence for some variants).
        assert (
            "[Pp]laywright" in trace or "playwright/.auth" in trace
        ), f"Wrong rule matched {variant}: {trace!r}"


@pytest.mark.skipif(not _have_git(), reason="git not available")
def test_existing_storage_state_pattern_unchanged(tmp_path: Path) -> None:
    """The pre-existing `**/storage-state*.json` pattern (line 760) must still
    match. This is a regression guard against the new rule accidentally
    shadowing it via order-dependence.
    """
    repo = _make_fixture_repo(tmp_path)
    target = "anywhere/storage-state.json"
    ignored, trace = _check_ignore(repo, target)
    assert ignored, f"Existing pattern `**/storage-state*.json` lost effect on {target}"
    assert "storage-state" in trace, f"Wrong rule matched: {trace!r}"
