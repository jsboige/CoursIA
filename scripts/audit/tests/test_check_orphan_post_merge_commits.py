"""Tests for scripts/audit/check_orphan_post_merge_commits.py (#8795/#6724).

The tool detects work pushed onto a PR's head branch AFTER that PR was merged,
where the content never reached `main`. Two anti-false-positive filters are the
heart of its correctness, and both are covered here:

  - Filtre 1 (squash-merge originals): commits unreachable from base that are
    dated BEFORE ``mergedAt`` are NOT findings -- they are the originals a squash
    folded into the merge commit. Only commits dated AFTER ``mergedAt`` count.
  - Filtre 2 (re-landed content): a post-merge commit whose files already match
    base (cherry-picked / re-landed by another route) is NOT a finding -- the
    content *is* on main, just via a different commit.

All git-backed tests build a hermetic mini-repo under ``tmp_path`` (no dependency
on the live repo state, no network). Commit timestamps are pinned via
``GIT_AUTHOR_DATE`` / ``GIT_COMMITTER_DATE`` so the time-based filter (filtre 1)
is deterministic.
"""
import importlib.util
import json
import os
import subprocess
import sys
from datetime import datetime, timedelta, timezone
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
CHECK_PATH = HERE.parent / "check_orphan_post_merge_commits.py"


def _load():
    spec = importlib.util.spec_from_file_location("check_orphan", CHECK_PATH)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


# --------------------------------------------------------------------------- #
# Hermetic git helpers
# --------------------------------------------------------------------------- #
_BASE_CFG = ("-c", "user.name=t", "-c", "user.email=t@e", "-c", "commit.gpgsign=false")


def _g(repo: Path, *args: str, date: str | None = None) -> str:
    """Run git in ``repo`` with a neutral identity + optional pinned date."""
    env = os.environ.copy()
    if date:
        env["GIT_AUTHOR_DATE"] = date
        env["GIT_COMMITTER_DATE"] = date
    cmd = ["git", "-C", str(repo), *_BASE_CFG, *args]
    proc = subprocess.run(cmd, capture_output=True, text=True, env=env)
    assert proc.returncode == 0, f"git {args} failed: {proc.stderr.strip()}"
    return proc.stdout.strip()


def _git_repo(tmp_path: Path) -> Path:
    repo = tmp_path / "repo"
    repo.mkdir()
    _g(repo, "init", "-q")
    _g(repo, "commit", "-q", "--allow-empty", "-m", "init",
       date="2026-07-29T09:00:00+00:00")
    _g(repo, "branch", "-M", "main")
    return repo


def _commit(repo: Path, message: str, files: dict | None = None,
            date: str = "2026-07-29T10:00:00+00:00") -> str:
    for rel, content in (files or {}).items():
        p = repo / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(content, encoding="utf-8")
    _g(repo, "add", "-A")
    _g(repo, "commit", "-q", "-m", message, date=date)
    return _g(repo, "rev-parse", "HEAD")


# --------------------------------------------------------------------------- #
# parse_ts
# --------------------------------------------------------------------------- #
def test_parse_ts_z_suffix_is_utc_aware():
    mod = _load()
    dt = mod.parse_ts("2026-07-29T11:00:00Z")
    assert dt == datetime(2026, 7, 29, 11, 0, 0, tzinfo=timezone.utc)
    assert dt.tzinfo is not None


def test_parse_ts_naive_becomes_utc():
    mod = _load()
    dt = mod.parse_ts("2026-07-29T11:00:00")
    assert dt.tzinfo == timezone.utc


def test_parse_ts_explicit_offset_preserved():
    mod = _load()
    dt = mod.parse_ts("2026-07-29T13:00:00+02:00")
    assert dt.utcoffset() == timedelta(hours=2)


def test_parse_ts_whitespace_tolerant():
    mod = _load()
    dt = mod.parse_ts("  2026-07-29T11:00:00Z  ")
    assert dt == datetime(2026, 7, 29, 11, 0, 0, tzinfo=timezone.utc)


# --------------------------------------------------------------------------- #
# filter_by_age
# --------------------------------------------------------------------------- #
def test_filter_by_age_zero_returns_all():
    mod = _load()
    prs = [{"mergedAt": "2026-07-29T11:00:00Z"}, {"mergedAt": "2020-01-01T00:00:00Z"}]
    assert mod.filter_by_age(prs, 0) == prs


def test_filter_by_age_keeps_recent_drops_old():
    mod = _load()
    now = mod.parse_ts("2026-07-29T12:00:00Z")
    recent = {"number": 1, "mergedAt": "2026-07-28T00:00:00Z"}   # 1 day old
    old = {"number": 2, "mergedAt": "2026-06-01T00:00:00Z"}       # ~58 days old
    assert mod.filter_by_age([recent, old], 14, now=now) == [recent]


def test_filter_by_age_drops_pr_without_mergedAt():
    mod = _load()
    assert mod.filter_by_age([{"number": 1}], 14) == []


# --------------------------------------------------------------------------- #
# run_git / branch_exists
# --------------------------------------------------------------------------- #
def test_run_git_returns_stripped_stdout(tmp_path):
    mod = _load()
    repo = _git_repo(tmp_path)
    out = mod.run_git(repo, "rev-parse", "--abbrev-ref", "HEAD")
    assert out == "main"


def test_run_git_raises_giterror_on_bad_ref(tmp_path):
    mod = _load()
    repo = _git_repo(tmp_path)
    with pytest.raises(mod.GitError):
        mod.run_git(repo, "show", "no-such-ref-xyz")


def test_run_git_check_false_returns_empty_on_failure(tmp_path):
    mod = _load()
    repo = _git_repo(tmp_path)
    # check=False must NOT raise; bad ref -> empty stdout
    out = mod.run_git(repo, "rev-parse", "--verify", "--quiet", "no-such-ref", check=False)
    assert out == ""


def test_branch_exists_true_for_main_false_for_missing(tmp_path):
    mod = _load()
    repo = _git_repo(tmp_path)
    assert mod.branch_exists(repo, "main") is True
    assert mod.branch_exists(repo, "definitely-not-a-branch-42") is False


# --------------------------------------------------------------------------- #
# commits_not_in_base / files_touched / content_missing_from_base
# --------------------------------------------------------------------------- #
def test_commits_not_in_base_returns_newest_first(tmp_path):
    mod = _load()
    repo = _git_repo(tmp_path)
    _g(repo, "checkout", "-q", "-b", "feat")
    s1 = _commit(repo, "older", {"a.txt": "1"}, date="2026-07-29T10:00:00+00:00")
    s2 = _commit(repo, "newer", {"b.txt": "2"}, date="2026-07-29T11:00:00+00:00")
    commits = mod.commits_not_in_base(repo, "main", "feat")
    assert [c["sha"] for c in commits] == [s2, s1]
    assert all({"committed_at", "subject"} <= set(c) for c in commits)


def test_commits_not_in_base_empty_when_fast_forwarded(tmp_path):
    mod = _load()
    repo = _git_repo(tmp_path)
    _g(repo, "checkout", "-q", "-b", "feat")
    _commit(repo, "x", {"a.txt": "1"})
    _g(repo, "checkout", "-q", "main")
    _g(repo, "merge", "-q", "--ff-only", "feat")  # main now contains feat -> no diff
    assert mod.commits_not_in_base(repo, "main", "feat") == []


def test_files_touched_is_union_sorted(tmp_path):
    mod = _load()
    repo = _git_repo(tmp_path)
    _g(repo, "checkout", "-q", "-b", "feat")
    s1 = _commit(repo, "c1", {"a.txt": "1", "b.txt": "1"})
    s2 = _commit(repo, "c2", {"b.txt": "2", "c.txt": "2"})
    assert mod.files_touched(repo, [s1, s2]) == ["a.txt", "b.txt", "c.txt"]


def test_content_missing_true_when_branch_diverges(tmp_path):
    mod = _load()
    repo = _git_repo(tmp_path)
    _g(repo, "checkout", "-q", "-b", "feat")
    _commit(repo, "x", {"a.txt": "branch-only"})
    assert mod.content_missing_from_base(repo, "main", "feat", ["a.txt"]) is True


def test_content_missing_false_when_identical(tmp_path):
    mod = _load()
    repo = _git_repo(tmp_path)
    _g(repo, "checkout", "-q", "-b", "feat")
    _commit(repo, "x", {"a.txt": "same"})
    _g(repo, "checkout", "-q", "main")
    _commit(repo, "y", {"a.txt": "same"})  # re-landed -> trees match for a.txt
    assert mod.content_missing_from_base(repo, "main", "feat", ["a.txt"]) is False


def test_content_missing_empty_paths_is_false(tmp_path):
    mod = _load()
    repo = _git_repo(tmp_path)
    assert mod.content_missing_from_base(repo, "main", "main", []) is False


# --------------------------------------------------------------------------- #
# analyse_pr -- the four statuses + the two anti-FP filters
# --------------------------------------------------------------------------- #
def _pr(number, head, merged_at="2026-07-29T11:00:00Z", title="T"):
    return {"number": number, "headRefName": head, "mergedAt": merged_at,
            "title": title}


def test_analyse_pr_orphan_is_a_finding(tmp_path):
    """Genuine orphan: a post-merge commit whose content never reached main."""
    mod = _load()
    repo = _git_repo(tmp_path)
    _g(repo, "checkout", "-q", "-b", "feat")
    _commit(repo, "merged content", {"merged.txt": "hello"},
            date="2026-07-29T10:00:00+00:00")        # BEFORE merge (11:00)
    c2 = _commit(repo, "stranded orphan", {"orphan.txt": "lost"},
                 date="2026-07-29T12:00:00+00:00")   # AFTER merge (11:00)
    _g(repo, "checkout", "-q", "main")
    _commit(repo, "land merged content only", {"merged.txt": "hello"},
            date="2026-07-29T11:30:00+00:00")        # main re-lands c1 but NOT c2
    res = mod.analyse_pr(repo, _pr(1, "feat"), "main", "")
    assert res["status"] == "orphan"
    assert res["post_merge"] == 1
    assert res["unreachable_total"] == 2
    assert "orphan.txt" in res["paths"]
    assert res["commits"][0]["sha"] == c2


def test_analyse_pr_clean_squash_originals_dated_before_merge(tmp_path):
    """Filtre 1: an unreachable original dated BEFORE mergedAt is not a finding."""
    mod = _load()
    repo = _git_repo(tmp_path)
    _g(repo, "checkout", "-q", "-b", "feat")
    _commit(repo, "original (squashed) content", {"merged.txt": "hello"},
            date="2026-07-29T10:00:00+00:00")        # BEFORE merge (11:30)
    _g(repo, "checkout", "-q", "main")
    _commit(repo, "squash lands the same content", {"merged.txt": "hello"},
            date="2026-07-29T11:00:00+00:00")        # unreachable from main, by design
    res = mod.analyse_pr(repo, _pr(2, "feat", merged_at="2026-07-29T11:30:00Z"),
                         "main", "")
    assert res["status"] == "clean"
    assert res["post_merge"] == 0
    assert res["unreachable_total"] == 1            # the original is unreachable...


def test_analyse_pr_clean_relanded_content(tmp_path):
    """Filtre 2: a post-merge commit whose files already match base is not a finding."""
    mod = _load()
    repo = _git_repo(tmp_path)
    _g(repo, "checkout", "-q", "-b", "feat")
    _commit(repo, "merged", {"merged.txt": "hello"},
            date="2026-07-29T10:00:00+00:00")
    _commit(repo, "post-merge but re-landed", {"orphan.txt": "lost"},
            date="2026-07-29T12:00:00+00:00")        # AFTER merge (11:00)
    _g(repo, "checkout", "-q", "main")
    _commit(repo, "land merged", {"merged.txt": "hello"},
            date="2026-07-29T11:30:00+00:00")
    _commit(repo, "land orphan too (cherry-pick elsewhere)",
            {"orphan.txt": "lost"},
            date="2026-07-29T12:30:00+00:00")        # identical content -> trees match
    res = mod.analyse_pr(repo, _pr(3, "feat"), "main", "")
    assert res["status"] == "clean"
    assert res["post_merge"] == 1                    # it IS post-merge...
    assert "already present" in res["reason"]        # ...but content is on base


def test_analyse_pr_branch_gone(tmp_path):
    """A PR whose head branch no longer exists is flagged as undetectable, not a finding."""
    mod = _load()
    repo = _git_repo(tmp_path)
    res = mod.analyse_pr(repo, _pr(4, "deleted-branch"), "main", "")
    assert res["status"] == "branch_gone"
    assert res["branch_ref"] == "deleted-branch"


def test_analyse_pr_skipped_missing_mergedAt(tmp_path):
    mod = _load()
    repo = _git_repo(tmp_path)
    res = mod.analyse_pr(repo, {"number": 5, "headRefName": "feat"}, "main", "")
    assert res["status"] == "skipped"


def test_analyse_pr_skipped_missing_head(tmp_path):
    mod = _load()
    repo = _git_repo(tmp_path)
    res = mod.analyse_pr(repo, {"number": 6, "mergedAt": "2026-07-29T11:00:00Z"},
                         "main", "")
    assert res["status"] == "skipped"


def test_analyse_pr_remote_prefix_applied(tmp_path):
    """A non-empty remote prepends ``remote/`` to the branch ref."""
    mod = _load()
    repo = _git_repo(tmp_path)
    _g(repo, "checkout", "-q", "-b", "feat")
    _commit(repo, "x", {"a.txt": "1"})
    # Simulate a remote tracking ref so branch_exists succeeds for origin/feat.
    _g(repo, "update-ref", "refs/remotes/origin/feat", _g(repo, "rev-parse", "feat"))
    pr = {"number": 7, "headRefName": "feat", "mergedAt": "2026-07-29T11:00:00Z",
          "title": "T"}
    res = mod.analyse_pr(repo, pr, "main", "origin")
    assert res["branch_ref"] == "origin/feat"


# --------------------------------------------------------------------------- #
# format_report
# --------------------------------------------------------------------------- #
def test_format_report_counts_and_orphan_detail():
    mod = _load()
    results = [
        {"status": "orphan", "number": 1, "head": "feat", "merged_at": "t",
         "title": "T", "branch_ref": "origin/feat", "base_ref": "main",
         "unreachable_total": 1, "post_merge": 1,
         "commits": [{"sha": "abcdef0", "committed_at": "t", "subject": "sub"}],
         "paths": ["orphan.txt"]},
        {"status": "clean", "number": 2, "head": "g", "merged_at": "t",
         "title": "T", "branch_ref": "origin/g"},
        {"status": "branch_gone", "number": 3, "head": "h", "merged_at": "t",
         "title": "T", "branch_ref": "origin/h"},
        {"status": "skipped", "number": 4, "reason": "x"},
    ]
    out = mod.format_report(results)
    assert "ORPHAN  PR #1  feat" in out
    assert "orphelines: 1" in out
    assert "propres: 1" in out
    assert "branche supprimee: 1" in out
    assert "ignorees: 1" in out
    # The delete-branch cautionary note appears when a branch is gone.
    assert "JAMAIS --delete-branch" in out


def test_format_report_no_orphans_omits_orphan_block():
    mod = _load()
    out = mod.format_report([{"status": "clean", "number": 1, "head": "f",
                              "merged_at": "t", "title": "T",
                              "branch_ref": "origin/f"}])
    assert "ORPHAN" not in out
    assert "orphelines: 0" in out


# --------------------------------------------------------------------------- #
# load_prs (--from-json)
# --------------------------------------------------------------------------- #
def test_load_prs_from_json_list(tmp_path):
    mod = _load()
    prs = tmp_path / "prs.json"
    prs.write_text(json.dumps([{"number": 1}]), encoding="utf-8")
    args = mod.build_parser().parse_args(["--from-json", str(prs)])
    assert mod.load_prs(args) == [{"number": 1}]


def test_load_prs_from_json_dict_with_prs_key(tmp_path):
    mod = _load()
    prs = tmp_path / "prs.json"
    prs.write_text(json.dumps({"prs": [{"number": 1}]}), encoding="utf-8")
    args = mod.build_parser().parse_args(["--from-json", str(prs)])
    assert mod.load_prs(args) == [{"number": 1}]


def test_load_prs_missing_file_raises_giterror(tmp_path):
    mod = _load()
    args = mod.build_parser().parse_args(["--from-json", str(tmp_path / "absent.json")])
    with pytest.raises(mod.GitError):
        mod.load_prs(args)


# --------------------------------------------------------------------------- #
# main() end-to-end via --from-json (no gh / no network)
# --------------------------------------------------------------------------- #
def _prs_file(tmp_path, prs):
    p = tmp_path / "prs.json"
    p.write_text(json.dumps(prs), encoding="utf-8")
    return p


def test_main_clean_pr_exits_0(tmp_path, capsys):
    mod = _load()
    repo = _git_repo(tmp_path)
    prs = _prs_file(tmp_path, [_pr(1, "main")])
    rc = mod.main(["--repo-path", str(repo), "--from-json", str(prs),
                   "--base-ref", "main", "--remote", "", "--days", "0"])
    assert rc == 0


def test_main_orphan_advisory_exits_0(tmp_path):
    """By default the tool is advisory: an orphan does NOT fail the run."""
    mod = _load()
    repo = _git_repo(tmp_path)
    _g(repo, "checkout", "-q", "-b", "feat")
    _commit(repo, "merged", {"merged.txt": "hello"}, date="2026-07-29T10:00:00+00:00")
    _commit(repo, "orphan", {"orphan.txt": "lost"}, date="2026-07-29T12:00:00+00:00")
    _g(repo, "checkout", "-q", "main")
    _commit(repo, "land", {"merged.txt": "hello"}, date="2026-07-29T11:30:00+00:00")
    prs = _prs_file(tmp_path, [_pr(1, "feat")])
    rc = mod.main(["--repo-path", str(repo), "--from-json", str(prs),
                   "--base-ref", "main", "--remote", "", "--days", "0"])
    assert rc == 0


def test_main_orphan_strict_exits_1(tmp_path):
    """With --strict, a genuine orphan fails the run (exit 1)."""
    mod = _load()
    repo = _git_repo(tmp_path)
    _g(repo, "checkout", "-q", "-b", "feat")
    _commit(repo, "merged", {"merged.txt": "hello"}, date="2026-07-29T10:00:00+00:00")
    _commit(repo, "orphan", {"orphan.txt": "lost"}, date="2026-07-29T12:00:00+00:00")
    _g(repo, "checkout", "-q", "main")
    _commit(repo, "land", {"merged.txt": "hello"}, date="2026-07-29T11:30:00+00:00")
    prs = _prs_file(tmp_path, [_pr(1, "feat")])
    rc = mod.main(["--repo-path", str(repo), "--from-json", str(prs),
                   "--base-ref", "main", "--remote", "", "--days", "0", "--strict"])
    assert rc == 1


def test_main_bad_json_exits_2(tmp_path, capsys):
    mod = _load()
    repo = _git_repo(tmp_path)
    bad = tmp_path / "bad.json"
    bad.write_text("{not valid json", encoding="utf-8")
    rc = mod.main(["--repo-path", str(repo), "--from-json", str(bad),
                   "--base-ref", "main", "--remote", "", "--days", "0"])
    assert rc == 2
    assert "JSON illisible" in capsys.readouterr().err


def test_main_json_out_written(tmp_path):
    mod = _load()
    repo = _git_repo(tmp_path)
    prs = _prs_file(tmp_path, [_pr(1, "main")])
    out = tmp_path / "out.json"
    rc = mod.main(["--repo-path", str(repo), "--from-json", str(prs),
                   "--base-ref", "main", "--remote", "", "--days", "0",
                   "--json-out", str(out)])
    assert rc == 0
    data = json.loads(out.read_text(encoding="utf-8"))
    assert "results" in data
    assert data["results"][0]["status"] == "clean"
