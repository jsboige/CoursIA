"""Tests for scripts/audit/check_orphan_merged_pr.py (#10981).

The tool re-examines MERGED PRs whose base != main and verifies, POST-merge,
that the PR's mergeCommit is an ancestor of main. This is the check that
base_not_main.py (advisory at PR time) delegated to the human — "verifier au
moment du merge" — and that nothing executed. The founding incident (2026-08-14)
is #10972: a stack-legit PR whose base leg was squash-merged 24s before the PR
landed into that base, orphaning the deliverable (the site broke in prod).

The three anti-false-positive filters are covered here:

  - Filtre 1 (ancestor): a mergeCommit that IS an ancestor of base_ref is clean
    (content reached main via a --merge preserving SHAs, or directly).
  - Filtre 2 (in flight): the base still has an open PR towards main -> the
    content will arrive, verdict is stable (no race), not an orphan.
  - Filtre 3 (re-landed): the PR's files already match base (cherry-pick /
    re-PR elsewhere) -> not an orphan, the content IS on main.

All git-backed tests build a hermetic mini-repo under ``tmp_path``. The key
scenario -- squash-merge of the base leg BEFORE the PR lands into it -- uses
the exact timestamps of the real #10972 sequence so the reproduction is
faithful.
"""
import importlib.util
import json
import os
import subprocess
from datetime import datetime, timedelta, timezone
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
CHECK_PATH = HERE.parent / "check_orphan_merged_pr.py"


def _load():
    spec = importlib.util.spec_from_file_location("check_orphan_merged_pr", CHECK_PATH)
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
       date="2026-08-14T09:00:00+00:00")
    _g(repo, "branch", "-M", "main")
    return repo


def _commit(repo: Path, message: str, files: dict | None = None,
            date: str = "2026-08-14T10:00:00+00:00") -> str:
    for rel, content in (files or {}).items():
        p = repo / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(content, encoding="utf-8")
    _g(repo, "add", "-A")
    _g(repo, "commit", "-q", "-m", message, date=date)
    return _g(repo, "rev-parse", "HEAD")


def _pr(number: int, head: str, base: str = "feature/base",
        merged_at: str = "2026-08-14T16:41:39Z", merge_commit: str = "",
        files: list | None = None, title: str = "T") -> dict:
    return {"number": number, "headRefName": head, "baseRefName": base,
            "mergedAt": merged_at,
            "mergeCommit": {"oid": merge_commit} if merge_commit else None,
            "files": [{"path": p} for p in (files or [])], "title": title}


# --------------------------------------------------------------------------- #
# parse_ts / commit_exists / is_ancestor / content_missing_from_base
# --------------------------------------------------------------------------- #
def test_parse_ts_z_suffix_is_utc_aware():
    mod = _load()
    dt = mod.parse_ts("2026-08-14T16:41:39Z")
    assert dt == datetime(2026, 8, 14, 16, 41, 39, tzinfo=timezone.utc)


def test_commit_exists_true_false(tmp_path):
    mod = _load()
    repo = _git_repo(tmp_path)
    sha = _g(repo, "rev-parse", "HEAD")
    assert mod.commit_exists(repo, sha) is True
    assert mod.commit_exists(repo, "deadbeef" * 5) is False


def test_is_ancestor_true_for_self_and_lineage(tmp_path):
    mod = _load()
    repo = _git_repo(tmp_path)
    first = _g(repo, "rev-parse", "HEAD")
    _g(repo, "checkout", "-q", "-b", "feat")
    second = _commit(repo, "x", {"a.txt": "1"})
    assert mod.is_ancestor(repo, first, "main") is True
    assert mod.is_ancestor(repo, second, "main") is False  # feat ahead of main


def test_content_missing_true_when_absent_false_when_identical(tmp_path):
    mod = _load()
    repo = _git_repo(tmp_path)
    _g(repo, "checkout", "-q", "-b", "base")
    mc = _commit(repo, "pr lands", {"site/rendered.html": "html"}, date="2026-08-14T16:41:39+00:00")
    assert mod.content_missing_from_base(repo, "main", mc, ["site/rendered.html"]) is True
    _g(repo, "checkout", "-q", "main")
    _commit(repo, "re-landed", {"site/rendered.html": "html"}, date="2026-08-14T17:00:00+00:00")
    assert mod.content_missing_from_base(repo, "main", mc, ["site/rendered.html"]) is False


# --------------------------------------------------------------------------- #
# The founding scenario (#10972, real timestamps) -- criterion 1: must turn red
# --------------------------------------------------------------------------- #
def test_orphan_after_base_squash_merge(tmp_path):
    """Exact reproduction of #10972: base leg squash-merged, THEN the PR lands
    into the base 24s later. mergeCommit is not an ancestor of main -> orphan."""
    mod = _load()
    repo = _git_repo(tmp_path)
    # 16:23:30  base branch with leg content
    _g(repo, "checkout", "-q", "-b", "feature/base")
    _commit(repo, "base leg work", {"_quarto.yml": "cfg"}, date="2026-08-14T16:23:30+00:00")
    base_sha = _g(repo, "rev-parse", "HEAD")
    # 16:41:15  #10965: base -> main squash-merged (creates a NEW commit on main,
    #           base branch is NO LONGER an ancestor of main)
    _g(repo, "checkout", "-q", "main")
    _commit(repo, "squash of base leg", {"_quarto.yml": "cfg"}, date="2026-08-14T16:41:15+00:00")
    # 16:41:39  #10972: PR merged INTO the (now orphaned) base
    _g(repo, "checkout", "-q", "feature/base")
    mc = _commit(repo, "PR site-render infra", {"site/rendered.html": "html"},
                 date="2026-08-14T16:41:39+00:00")
    pr = _pr(10972, "feature/site-render-infra-10923", base="feature/base",
             merge_commit=mc, files=["site/rendered.html", "_quarto.yml"])
    res = mod.analyse_pr(repo, pr, "main", "")
    assert res["status"] == "orphan"
    assert res["merge_commit"] == mc
    assert "recovery" in res


def test_orphan_strict_exits_1_main(tmp_path):
    """main() with --strict returns 1 on a genuine orphan (criterion 1: red)."""
    mod = _load()
    repo = _git_repo(tmp_path)
    _g(repo, "checkout", "-q", "-b", "feature/base")
    _commit(repo, "base leg work", {"_quarto.yml": "cfg"})
    _g(repo, "checkout", "-q", "main")
    _commit(repo, "squash of base leg", {"_quarto.yml": "cfg"})
    _g(repo, "checkout", "-q", "feature/base")
    mc = _commit(repo, "PR lands", {"site/rendered.html": "html"})
    prs = tmp_path / "prs.json"
    prs.write_text(json.dumps([_pr(1, "feature/site", merge_commit=mc,
                                   files=["site/rendered.html"])]), encoding="utf-8")
    rc = mod.main(["--repo-path", str(repo), "--from-json", str(prs),
                   "--base-ref", "main", "--repo", "", "--days", "0", "--strict"])
    assert rc == 1


# --------------------------------------------------------------------------- #
# Filtre 1 -- mergeCommit ancestor of main (--merge preserve-SHA) -- clean
# --------------------------------------------------------------------------- #
def test_clean_when_merge_commit_is_ancestor(tmp_path):
    """If the base leg was merged with --merge (SHAs preserved), the PR's
    mergeCommit IS an ancestor of main -> clean, no false positive."""
    mod = _load()
    repo = _git_repo(tmp_path)
    _g(repo, "checkout", "-q", "-b", "feature/base")
    _commit(repo, "base leg work", {"_quarto.yml": "cfg"})
    _g(repo, "checkout", "-q", "-b", "feature/site2")
    _commit(repo, "PR work", {"site/rendered.html": "html"})
    _g(repo, "checkout", "-q", "feature/base")
    # PR merges into base (merge commit on base), then base --merge into main
    _g(repo, "merge", "-q", "--no-ff", "feature/site2", "-m", "merge PR into base",
       date="2026-08-14T16:41:39+00:00")
    mc = _g(repo, "rev-parse", "HEAD")
    _g(repo, "checkout", "-q", "main")
    _g(repo, "merge", "-q", "--no-ff", "feature/base", "-m", "merge base into main",
       date="2026-08-14T17:00:00+00:00")
    pr = _pr(10, "feature/site2", base="feature/base", merge_commit=mc,
             files=["site/rendered.html"])
    res = mod.analyse_pr(repo, pr, "main", "")
    assert res["status"] == "clean"
    assert "ancestor" in res["reason"]


# --------------------------------------------------------------------------- #
# Filtre 2 -- stack in flight (base still has an open PR towards main)
# --------------------------------------------------------------------------- #
def test_conservative_orphan_without_repo_slug(tmp_path):
    """Without a repo slug, the tool cannot query gh for open PRs on the base,
    so it conservatively falls through to the content check. A base that
    genuinely lacks the content on main -> orphan. (With a slug, the same
    scenario is in_flight -- covered by test_in_flight_status_when_open_prs.)"""
    mod = _load()
    repo = _git_repo(tmp_path)
    _g(repo, "checkout", "-q", "-b", "feature/base")
    _commit(repo, "base leg work", {"_quarto.yml": "cfg"})
    _g(repo, "checkout", "-q", "-b", "feature/site")
    mc = _commit(repo, "PR work", {"site/rendered.html": "html"})
    pr = _pr(11, "feature/site", base="feature/base", merge_commit=mc,
             files=["site/rendered.html"])
    res = mod.analyse_pr(repo, pr, "main", "")
    assert res["status"] == "orphan"


def test_in_flight_status_when_open_prs_to_main(monkeypatch, tmp_path):
    """With a repo slug, the gh call for open PRs on the base returns >= 1 ->
    in_flight (NOT orphan). Stubs open_prs_to_main (a gh call)."""
    mod = _load()
    repo = _git_repo(tmp_path)
    _g(repo, "checkout", "-q", "-b", "feature/base")
    _commit(repo, "base leg work", {"_quarto.yml": "cfg"})
    _g(repo, "checkout", "-q", "-b", "feature/site")
    mc = _commit(repo, "PR work", {"site/rendered.html": "html"})
    pr = _pr(12, "feature/site", base="feature/base", merge_commit=mc,
             files=["site/rendered.html"])
    monkeypatch.setattr(mod, "open_prs_to_main", lambda repo_slug, base: 1)

    res = mod.analyse_pr(repo, pr, "main", "fake/repo")
    assert res["status"] == "in_flight"
    assert res["open_prs_to_main"] == 1


def test_orphan_when_open_prs_to_main_zero(monkeypatch, tmp_path):
    """With a repo slug, gh returns 0 open PRs on the base AND the content is
    missing from main -> orphan (the #10972 case with the stack now dead)."""
    mod = _load()
    repo = _git_repo(tmp_path)
    _g(repo, "checkout", "-q", "-b", "feature/base")
    _commit(repo, "base leg work", {"_quarto.yml": "cfg"})
    _g(repo, "checkout", "-q", "main")
    _commit(repo, "squash of base leg", {"_quarto.yml": "cfg"})
    _g(repo, "checkout", "-q", "feature/base")
    mc = _commit(repo, "PR work", {"site/rendered.html": "html"})
    pr = _pr(13, "feature/site", base="feature/base", merge_commit=mc,
             files=["site/rendered.html"])
    monkeypatch.setattr(mod, "open_prs_to_main", lambda repo_slug, base: 0)

    res = mod.analyse_pr(repo, pr, "main", "fake/repo")
    assert res["status"] == "orphan"
    assert res["merge_commit"] == mc


# --------------------------------------------------------------------------- #
# Filtre 3 -- content re-landed via another route (cherry-pick)
# --------------------------------------------------------------------------- #
def test_clean_when_content_relanded(tmp_path):
    """Filtre 3: the PR's files already match main (cherry-picked elsewhere) ->
    clean, not an orphan, even though the mergeCommit is not an ancestor."""
    mod = _load()
    repo = _git_repo(tmp_path)
    _g(repo, "checkout", "-q", "-b", "feature/base")
    _commit(repo, "base leg work", {"_quarto.yml": "cfg"})
    _g(repo, "checkout", "-q", "-b", "feature/site")
    mc = _commit(repo, "PR work", {"site/rendered.html": "html"})
    _g(repo, "checkout", "-q", "main")
    # base leg squash-merged, and the PR content cherry-picked (new commit)
    _commit(repo, "squash of base leg", {"_quarto.yml": "cfg"})
    _commit(repo, "cherry-pick of PR content", {"site/rendered.html": "html"})
    pr = _pr(14, "feature/site", base="feature/base", merge_commit=mc,
             files=["site/rendered.html"])
    res = mod.analyse_pr(repo, pr, "main", "")
    assert res["status"] == "clean"
    assert "re-landed" in res["reason"]


# --------------------------------------------------------------------------- #
# skipped cases
# --------------------------------------------------------------------------- #
def test_skipped_when_base_is_main(tmp_path):
    mod = _load()
    repo = _git_repo(tmp_path)
    pr = _pr(15, "feature/x", base="main")
    res = mod.analyse_pr(repo, pr, "main", "")
    assert res["status"] == "skipped"
    assert "base is main" in res["reason"]


def test_skipped_when_no_merge_commit(tmp_path):
    mod = _load()
    repo = _git_repo(tmp_path)
    pr = _pr(16, "feature/x", base="feature/base", merge_commit="")
    res = mod.analyse_pr(repo, pr, "main", "")
    assert res["status"] == "skipped"
    assert "no mergeCommit" in res["reason"]


def test_skipped_when_merge_commit_unreachable(tmp_path):
    mod = _load()
    repo = _git_repo(tmp_path)
    pr = _pr(17, "feature/x", base="feature/base", merge_commit="deadbeef" * 5)
    res = mod.analyse_pr(repo, pr, "main", "")
    assert res["status"] == "skipped"
    assert "unreachable" in res["reason"]


# --------------------------------------------------------------------------- #
# format_report
# --------------------------------------------------------------------------- #
def test_format_report_counts_and_orphan_detail():
    mod = _load()
    results = [
        {"status": "orphan", "number": 1, "base": "feature/base", "head": "f",
         "merged_at": "t", "title": "T", "merge_commit": "a" * 40,
         "paths": ["site/rendered.html"], "recovery": "git merge origin/f"},
        {"status": "clean", "number": 2, "base": "feature/b", "head": "g",
         "merged_at": "t", "title": "T", "reason": "x"},
        {"status": "in_flight", "number": 3, "base": "feature/c", "head": "h",
         "merged_at": "t", "title": "T", "open_prs_to_main": 1, "reason": "y"},
        {"status": "skipped", "number": 4, "reason": "base is main"},
    ]
    out = mod.format_report(results)
    assert "ORPHAN  PR #1" in out
    assert "orphelins: 1" in out
    assert "en vol: 1" in out
    assert "propres: 1" in out
    assert "ignorees: 1" in out


# --------------------------------------------------------------------------- #
# load_prs / filter_by_age / main()
# --------------------------------------------------------------------------- #
def test_load_prs_from_json_list(tmp_path):
    mod = _load()
    prs = tmp_path / "prs.json"
    prs.write_text(json.dumps([{"number": 1}]), encoding="utf-8")
    args = mod.build_parser().parse_args(["--from-json", str(prs)])
    assert mod.load_prs(args) == [{"number": 1}]


def test_filter_by_age_zero_returns_all():
    mod = _load()
    prs = [{"mergedAt": "2026-08-14T16:41:39Z"}, {"mergedAt": "2020-01-01T00:00:00Z"}]
    assert mod.filter_by_age(prs, 0) == prs


def test_main_clean_exits_0(tmp_path):
    mod = _load()
    repo = _git_repo(tmp_path)
    prs = tmp_path / "prs.json"
    prs.write_text(json.dumps([_pr(1, "feature/x", base="main")]), encoding="utf-8")
    rc = mod.main(["--repo-path", str(repo), "--from-json", str(prs),
                   "--base-ref", "main", "--repo", "", "--days", "0"])
    assert rc == 0


def test_main_orphan_advisory_exits_0(tmp_path):
    mod = _load()
    repo = _git_repo(tmp_path)
    _g(repo, "checkout", "-q", "-b", "feature/base")
    _commit(repo, "base leg", {"_quarto.yml": "cfg"})
    _g(repo, "checkout", "-q", "main")
    _commit(repo, "squash base leg", {"_quarto.yml": "cfg"})
    _g(repo, "checkout", "-q", "feature/base")
    mc = _commit(repo, "PR", {"site/rendered.html": "html"})
    prs = tmp_path / "prs.json"
    prs.write_text(json.dumps([_pr(1, "feature/site", merge_commit=mc,
                                   files=["site/rendered.html"])]), encoding="utf-8")
    rc = mod.main(["--repo-path", str(repo), "--from-json", str(prs),
                   "--base-ref", "main", "--repo", "", "--days", "0"])
    assert rc == 0  # advisory by default


def test_main_bad_json_exits_2(tmp_path, capsys):
    mod = _load()
    repo = _git_repo(tmp_path)
    bad = tmp_path / "bad.json"
    bad.write_text("{not valid json", encoding="utf-8")
    rc = mod.main(["--repo-path", str(repo), "--from-json", str(bad),
                   "--base-ref", "main", "--repo", "", "--days", "0"])
    assert rc == 2
    assert "JSON illisible" in capsys.readouterr().err


def test_main_json_out_written(tmp_path):
    mod = _load()
    repo = _git_repo(tmp_path)
    prs = tmp_path / "prs.json"
    prs.write_text(json.dumps([_pr(1, "feature/x", base="main")]), encoding="utf-8")
    out = tmp_path / "out.json"
    rc = mod.main(["--repo-path", str(repo), "--from-json", str(prs),
                   "--base-ref", "main", "--repo", "", "--days", "0",
                   "--json-out", str(out)])
    assert rc == 0
    data = json.loads(out.read_text(encoding="utf-8"))
    assert data["results"][0]["status"] == "skipped"


# --------------------------------------------------------------------------- #
# Adjudications (#11159) — registre versionne, statut ADJUGE distinct
# --------------------------------------------------------------------------- #
def test_adjudged_when_merge_commit_in_registry(tmp_path):
    """Le #10972 original, mais son mergeCommit est dans le registre d'adjudications
    -> statut ADJUGE (pas ORPHAN), motif reporte, cle = mergeCommit."""
    mod = _load()
    repo = _git_repo(tmp_path)
    _g(repo, "checkout", "-q", "-b", "feature/base")
    _commit(repo, "base leg work", {"_quarto.yml": "cfg"})
    _g(repo, "checkout", "-q", "main")
    _commit(repo, "squash of base leg", {"_quarto.yml": "cfg"})
    _g(repo, "checkout", "-q", "feature/base")
    mc = _commit(repo, "PR site-render infra", {"site/rendered.html": "html"})
    pr = _pr(10972, "feature/site-render-infra-10923", base="feature/base",
             merge_commit=mc, files=["site/rendered.html", "_quarto.yml"])
    adjudications = {mc: {"motif": "contenu promu au bloc racine de _quarto.yml (L624-629)",
                          "adjudicated_by": "ai-01", "date": "2026-08-16"}}
    res = mod.analyse_pr(repo, pr, "main", "", adjudications)
    assert res["status"] == "adjudge"
    assert res["merge_commit"] == mc
    assert "promu au bloc racine" in res["motif"]
    assert res["adjudicated_by"] == "ai-01"


def test_unadjudged_orphan_still_orphan_with_registry(tmp_path):
    """Un nouvel orphelin non adjuge ressort toujours en ORPHAN meme quand le
    registre existe — le registre ne desarme pas le detecteur."""
    mod = _load()
    repo = _git_repo(tmp_path)
    _g(repo, "checkout", "-q", "-b", "feature/base")
    _commit(repo, "base leg work", {"_quarto.yml": "cfg"})
    _g(repo, "checkout", "-q", "main")
    _commit(repo, "squash of base leg", {"_quarto.yml": "cfg"})
    _g(repo, "checkout", "-q", "feature/base")
    mc = _commit(repo, "PR work", {"site/rendered.html": "html"})
    pr = _pr(999, "feature/new-orphan", base="feature/base", merge_commit=mc,
             files=["site/rendered.html"])
    # Le registre contient un AUTRE mergeCommit (le #10972 historique)
    adjudications = {"3a178b0f02bc0de7c12f09f48ef88f878ed87280":
                     {"motif": "autre orphelin", "adjudicated_by": "ai-01",
                      "date": "2026-08-16"}}
    res = mod.analyse_pr(repo, pr, "main", "", adjudications)
    assert res["status"] == "orphan"
    assert res["merge_commit"] == mc


def test_adjudication_without_motive_rejected(tmp_path):
    """Entree de registre sans motif -> RuntimeError (exit 2) : jamais un mute
    silencieux, l'adjudication de complaisance reste visible."""
    mod = _load()
    reg = tmp_path / "adjudications.json"
    reg.write_text(json.dumps({"a" * 40: {"adjudicated_by": "ai-01",
                                          "date": "2026-08-16"}}), encoding="utf-8")
    with pytest.raises(RuntimeError, match="motif"):
        mod.load_adjudications(reg)


def test_adjudication_bad_json_rejected(tmp_path):
    mod = _load()
    reg = tmp_path / "adjudications.json"
    reg.write_text("{not json", encoding="utf-8")
    with pytest.raises(RuntimeError, match="illisible"):
        mod.load_adjudications(reg)


def test_format_report_lists_adjudges_separately_and_counts():
    mod = _load()
    results = [
        {"status": "orphan", "number": 1, "base": "feature/base", "head": "f",
         "merged_at": "t", "title": "T", "merge_commit": "b" * 40,
         "paths": ["x"], "recovery": "git merge origin/f"},
        {"status": "adjudge", "number": 2, "base": "feature/base", "head": "g",
         "merged_at": "t", "title": "T2", "merge_commit": "a" * 40,
         "paths": ["y"], "motif": "contenu promu au bloc racine",
         "adjudicated_by": "ai-01", "adjudicated_at": "2026-08-16"},
    ]
    out = mod.format_report(results)
    assert "ADJUGE  PR #2" in out
    assert "motif: contenu promu au bloc racine" in out
    assert "orphelins: 1" in out
    assert "adjuges: 1" in out


def test_main_adjudged_does_not_fail_strict(tmp_path):
    """main() avec registre qui adjuge le seul orphelin -> --strict exit 0 :
    le compte orphelins retombe a 0, l'adjudication n'est pas un finding."""
    mod = _load()
    repo = _git_repo(tmp_path)
    _g(repo, "checkout", "-q", "-b", "feature/base")
    _commit(repo, "base leg work", {"_quarto.yml": "cfg"})
    _g(repo, "checkout", "-q", "main")
    _commit(repo, "squash of base leg", {"_quarto.yml": "cfg"})
    _g(repo, "checkout", "-q", "feature/base")
    mc = _commit(repo, "PR work", {"site/rendered.html": "html"})
    prs = tmp_path / "prs.json"
    prs.write_text(json.dumps([_pr(10972, "feature/site", merge_commit=mc,
                                   files=["site/rendered.html"])]), encoding="utf-8")
    reg = tmp_path / "adjudications.json"
    reg.write_text(json.dumps({mc: {"motif": "contenu promu au bloc racine",
                                    "adjudicated_by": "ai-01",
                                    "date": "2026-08-16"}}), encoding="utf-8")
    rc = mod.main(["--repo-path", str(repo), "--from-json", str(prs),
                   "--base-ref", "main", "--repo", "", "--days", "0",
                   "--adjudications", str(reg), "--strict"])
    assert rc == 0


def test_main_registry_corrupt_exits_2(tmp_path):
    """Un registre mal forme (motif manquant) -> exit 2 : le garde-fou est
    declenche, pas une adjudication silencieuse."""
    mod = _load()
    repo = _git_repo(tmp_path)
    prs = tmp_path / "prs.json"
    prs.write_text(json.dumps([_pr(1, "feature/x", base="main")]), encoding="utf-8")
    reg = tmp_path / "adjudications.json"
    reg.write_text(json.dumps({"a" * 40: {"adjudicated_by": "x"}}), encoding="utf-8")
    rc = mod.main(["--repo-path", str(repo), "--from-json", str(prs),
                   "--base-ref", "main", "--repo", "", "--days", "0",
                   "--adjudications", str(reg)])
    assert rc == 2
