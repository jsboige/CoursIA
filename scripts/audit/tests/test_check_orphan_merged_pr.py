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


def _gh_auth_available() -> bool:
    """Les tests `_main` ci-dessous passent par mod.main(), dont la
    découverte de slug en fallback interroge `gh repo view` même avec
    --repo "" (check_orphan_merged_pr.py main(), `args.repo or ...`), puis
    analyse_pr requête les PRs ouvertes sur la base quand un slug existe.
    Sur un runner sans gh authentifié, le RuntimeError est avalé en exit 2
    et le test échoue sans faute du code. Skip propre, pas FAILED — même
    politique que test_check_unaddressed_nits.py (review NanoClaw #14322,
    concern 2) ; constaté au câblage CI de cette suite (#14615 famille 2).
    """
    import shutil
    if shutil.which("gh") is None:
        return False
    return subprocess.run(
        ["gh", "auth", "status"], capture_output=True
    ).returncode == 0


requires_gh_auth = pytest.mark.skipif(
    not _gh_auth_available(),
    reason="gh absent/unauthed -- main() (découverte slug + requête PRs "
           "ouvertes sur la base) exige gh authentifié (#14615 famille 2)",
)


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
    proc = subprocess.run(cmd, capture_output=True, text=True, env=env,
                          encoding="utf-8", errors="replace")
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
        files: list | None = None, title: str = "T",
        rest_files: list | None = None, body: str = "") -> dict:
    return {"number": number, "headRefName": head, "baseRefName": base,
            "mergedAt": merged_at,
            "mergeCommit": {"oid": merge_commit} if merge_commit else None,
            "files": [{"path": p} for p in (files or [])], "title": title,
            "rest_files": rest_files, "body": body}


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
    """Classifieur (#12723) : absent -> lost ; present (meme contenu evolue)
    -> present, jamais lost. L'identite n'entre plus en ligne de compte."""
    mod = _load()
    repo = _git_repo(tmp_path)
    _g(repo, "checkout", "-q", "-b", "base")
    mc = _commit(repo, "pr lands", {"site/rendered.html": "html"}, date="2026-08-14T16:41:39+00:00")
    cls = mod.classify_delivered_paths(repo, "main", ["site/rendered.html"])
    assert cls["lost"] == ["site/rendered.html"]
    _g(repo, "checkout", "-q", "main")
    _commit(repo, "re-landed then evolved", {"site/rendered.html": "html-v2-evolved"},
            date="2026-08-14T17:00:00+00:00")
    cls = mod.classify_delivered_paths(repo, "main", ["site/rendered.html"])
    assert cls["lost"] == [] and cls["present"] == 1


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


@requires_gh_auth
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
    assert "re-atterris" in res["reason"]


def test_filter3_present_but_evolved_is_clean(tmp_path):
    """#12723, formes FP #11931/#11638 (FAIL-BEFORE) : les chemins livres
    EXISTENT sur main (re-atterris puis EVOLUES par des commits ulterieurs).
    L'ancien filtre 3 comparait l'IDENTITE de tout le lot -> diff non-quiet ->
    orphelin a tort (ce sont les FP labellises en prod). #12723 exige
    l'EXISTENCE par chemin ('comparer les chemins, pas les SHA') : present,
    meme evolue, n'est pas une perte."""
    mod = _load()
    repo = _git_repo(tmp_path)
    _g(repo, "checkout", "-q", "-b", "feature/base")
    _commit(repo, "base leg work", {"_quarto.yml": "cfg"})
    _g(repo, "checkout", "-q", "-b", "feature/site")
    mc = _commit(repo, "PR work", {"site/rendered.html": "v1"})
    _g(repo, "checkout", "-q", "main")
    _commit(repo, "squash of base leg", {"_quarto.yml": "cfg"})
    _commit(repo, "cherry-pick of PR content", {"site/rendered.html": "v1"})
    _commit(repo, "later evolution of the same file", {"site/rendered.html": "v2-evolved"})
    pr = _pr(11931, "feature/site", base="feature/base", merge_commit=mc,
             files=["site/rendered.html"])
    res = mod.analyse_pr(repo, pr, "main", "")
    assert res["status"] == "clean"


def test_renamed_path_is_not_a_loss(tmp_path):
    """#12723 : chemin livre absent de main mais dont le BASENAME vit ailleurs
    sur main (deplacement de serie, meme nom autre dossier) -> statut renamed,
    PAS orphan — 'un garde qui sur-accuse est desarme apres deux faux positifs'.
    Scope honnete : le matching est basename EXACT ; un zero-pad qui change le
    basename lui-meme (4b -> 04b) est hors portee (le fuzzy matcher sur-accuserait
    plus qu'il ne sauverait)."""
    mod = _load()
    repo = _git_repo(tmp_path)
    _g(repo, "checkout", "-q", "-b", "feature/base")
    _commit(repo, "base leg work", {"_quarto.yml": "cfg"})
    _g(repo, "checkout", "-q", "-b", "feature/site")
    mc = _commit(repo, "PR work", {"Search/MGS-26-EquilibriumOptimizer.ipynb": "nb"})
    _g(repo, "checkout", "-q", "main")
    _commit(repo, "squash base leg", {"_quarto.yml": "cfg"})
    _commit(repo, "moved to another series dir", {"Metaheuristiques/MGS-26-EquilibriumOptimizer.ipynb": "nb"})
    pr = _pr(11931, "feature/site", base="feature/base", merge_commit=mc,
             files=["Search/MGS-26-EquilibriumOptimizer.ipynb"])
    res = mod.analyse_pr(repo, pr, "main", "")
    assert res["status"] == "renamed"
    assert res["renamed"] == {"Search/MGS-26-EquilibriumOptimizer.ipynb":
                              ["Metaheuristiques/MGS-26-EquilibriumOptimizer.ipynb"]}


def test_normalize_rest_uses_filename_not_path():
    """Regression live-run (#12723) : l'API REST pulls/{n}/files rend le champ
    ``filename``, pas ``path``. Ne lire que ``path`` faisait disparaitre tous
    les fichiers -> toute PR rendue 'clean' (#12423 rendu propre alors que son
    notebook est absent de main)."""
    mod = _load()
    out = mod.normalize_pr_files([
        {"sha": "d", "filename": "Search/MGS-26.ipynb", "status": "added"},
        {"path": "Graphql/form.ipynb"},   # GraphQL : pas de statut
        "bare/string.ipynb",
        {"sha": "x", "filename": "README.old.md", "status": "removed"},
    ])
    assert out == [
        {"path": "Search/MGS-26.ipynb", "status": "added"},
        {"path": "Graphql/form.ipynb", "status": "modified"},
        {"path": "bare/string.ipynb", "status": "modified"},
        {"path": "README.old.md", "status": "removed"},  # filtre en aval
    ]


def test_removed_files_are_not_required_on_main(tmp_path):
    """Une PR qui RETIRE un fichier (statut REST removed) ne doit pas exiger sa
    presence sur main : l'absence EST la livraison."""
    mod = _load()
    repo = _git_repo(tmp_path)
    _g(repo, "checkout", "-q", "-b", "feature/base")
    _commit(repo, "base leg work", {"_quarto.yml": "cfg"})
    _g(repo, "checkout", "-q", "-b", "feature/site")
    mc = _commit(repo, "PR removes legacy", {"README.old.md": ""})
    _g(repo, "checkout", "-q", "main")
    _commit(repo, "squash base leg", {"_quarto.yml": "cfg"})
    pr = _pr(12000, "feature/site", base="feature/base", merge_commit=mc,
             rest_files=[{"path": "README.old.md", "status": "removed"}])
    res = mod.analyse_pr(repo, pr, "main", "")
    assert res["status"] == "clean"


def test_orphan_records_only_lost_paths(tmp_path):
    """#12423 : le finding porte les chemins PERDUS (absents, non renommes),
    pas l'ensemble des fichiers de la PR."""
    mod = _load()
    repo = _git_repo(tmp_path)
    _g(repo, "checkout", "-q", "-b", "feature/base")
    _commit(repo, "base leg work", {"_quarto.yml": "cfg"})
    _g(repo, "checkout", "-q", "-b", "feature/site")
    mc = _commit(repo, "PR work", {"Search/MGS-26-EquilibriumOptimizer.ipynb": "nb",
                                   "Search/README.md": "r"})
    _g(repo, "checkout", "-q", "main")
    _commit(repo, "squash base leg", {"_quarto.yml": "cfg"})
    _commit(repo, "readme re-landed elsewhere", {"Search/README.md": "r"})
    pr = _pr(12423, "feature/site", base="feature/base", merge_commit=mc,
             files=["Search/MGS-26-EquilibriumOptimizer.ipynb", "Search/README.md"])
    res = mod.analyse_pr(repo, pr, "main", "")
    assert res["status"] == "orphan"
    assert res["paths"] == ["Search/MGS-26-EquilibriumOptimizer.ipynb"]


def test_parse_issue_refs_closes_and_see():
    mod = _load()
    refs = mod.parse_issue_refs("## Summary\n\nCloses #12408\n\nSee #12373 epic. Refs #99.")
    assert refs["closes"] == [12408]
    assert refs["see"] == [12373, 99]
    assert mod.issue_signal_targets(refs) == [12408]
    # repli : See quand aucune Closes
    assert mod.issue_signal_targets({"closes": [], "see": [12373]}) == [12373]


def _fake_gh_subprocess(calls: list):
    """subprocess.run factice : git -> REEL (le mini-repo local hermetique doit
    rester analyse par les vrais is_ancestor/ls-tree), gh/git-remote -> capture.

    Un fake global (returncode 0 partout) ferait passer is_ancestor pour vrai
    (merge-base --is-ancestor rend 0) et rendrait TOUT statut clean — le test
    ne testerait plus rien."""
    real_run = subprocess.run

    def run(cmd, **kw):
        if cmd and cmd[0] == "git" and "ls-remote" not in cmd:
            return real_run(cmd, **kw)
        calls.append(list(cmd))
        return type("P", (), {"returncode": 0, "stdout": "[]", "stderr": ""})()
    return run


def test_issue_comment_names_the_target_issue_not_the_pr():
    """Le commentaire depose sur l'issue cite l'ISSUE (Closes #12418), pas le
    numero de PR — 'porte Closes #12423' serait un mensonge lisible."""
    mod = _load()
    r = {"number": 12423, "title": "T", "base": "feature/x",
         "paths": ["Search/MGS-26.ipynb"],
         "issue_refs": {"closes": [12418], "see": [12300]}}
    body = mod.build_issue_comment(r, 12418)
    assert "Closes #12418" in body
    assert "Closes #12423" not in body
    body2 = mod.build_issue_comment(r, 12300)
    assert "See #12300" in body2 and "See #12423" not in body2


def test_comment_upsert_uses_numeric_rest_id(monkeypatch, tmp_path):
    """Regression #12723 (diag) : l'upsert doit PATCHer par id NUMERIQUE REST.
    Lister via gh pr view --json comments (ids GraphQL IC_...) et PATCHer par
    URL REST = 404 silencieux — le bug qui a gelee le registre
    orphan-branch-scan 9 jours ('report updated' imprime, jamais atterri)."""
    mod = _load()
    repo = _git_repo(tmp_path)
    _g(repo, "checkout", "-q", "-b", "feature/base")
    _commit(repo, "base leg work", {"_quarto.yml": "cfg"})
    _g(repo, "checkout", "-q", "-b", "feature/site")
    mc = _commit(repo, "PR work", {"site/rendered.html": "html"})
    _g(repo, "checkout", "-q", "main")
    _commit(repo, "squash base leg", {"_quarto.yml": "cfg"})
    pr = _pr(12423, "feature/site", base="feature/base", merge_commit=mc,
             files=["site/rendered.html"])

    calls: list[list[str]] = []
    monkeypatch.setattr(mod, "_gh_json", lambda args: (
        [{"id": 5300849238, "body": mod.MARKER_START + " old"}]
        if args[:1] == ["api"] and "/comments" in args[1] else None))
    monkeypatch.setattr(mod.subprocess, "run", _fake_gh_subprocess(calls))
    r = mod.analyse_pr(repo, pr, "main", "")
    assert r["status"] == "orphan"
    mod.apply_findings("jsboige/CoursIA", [r], [], dry_run=False)
    patches = [c for c in calls if "PATCH" in c]
    assert patches, "le PATCH numerique doit etre emis"
    url_args = [a for a in patches[0] if "issues/comments/" in a]
    assert url_args, f"URL REST attendue dans le PATCH: {patches[0]}"
    cid = url_args[0].split("?")[0].rstrip("/").rsplit("/", 1)[-1]
    assert cid.isdigit(), f"l'id du PATCH doit etre numerique (REST), pas un node-id: {cid}"


def test_unlabel_repaired_labeled_pr(monkeypatch, tmp_path):
    """#12723 : une PR labellisee devenue propre (contenu re-atterri puis
    evolue — le cas #11931/#11638) est DE-LABELLISEE avec note de resolution :
    le label signifie 'toujours absent', pas 'absent un jour'."""
    mod = _load()
    repo = _git_repo(tmp_path)
    _g(repo, "checkout", "-q", "-b", "feature/base")
    _commit(repo, "base leg work", {"_quarto.yml": "cfg"})
    _g(repo, "checkout", "-q", "-b", "feature/site")
    mc = _commit(repo, "PR work", {"CSP/CSP-5-Optimization.ipynb": "v1"})
    _g(repo, "checkout", "-q", "main")
    _commit(repo, "squash base leg", {"_quarto.yml": "cfg"})
    _commit(repo, "relanded", {"CSP/CSP-5-Optimization.ipynb": "v1"})
    _commit(repo, "evolved", {"CSP/CSP-5-Optimization.ipynb": "v9"})

    fake_pr = {"number": 11931, "baseRefName": "feature/base",
               "headRefName": "feature/site", "mergedAt": "2026-08-15T10:00:00Z",
               "mergeCommit": {"oid": mc}, "files": [{"path": "CSP/CSP-5-Optimization.ipynb"}],
               "title": "T", "body": "See #11891"}

    def fake_gh(args):
        if args[:2] == ["pr", "view"]:
            return fake_pr
        if args[:1] == ["api"]:
            return []  # pas de commentaire marker existant -> post
        return None

    monkeypatch.setattr(mod, "labeled_merged_prs", lambda repo_slug: [11931])
    monkeypatch.setattr(mod, "_gh_json", fake_gh)
    edits: list[list[str]] = []
    monkeypatch.setattr(mod.subprocess, "run", _fake_gh_subprocess(edits))
    mod.unlabel_repaired("jsboige/CoursIA", repo, "main",
                         orphan_numbers=set(), dry_run=False)
    removed = [c for c in edits if "--remove-label" in c and "11931" in c]
    assert removed, "le label doit etre retire de la PR redevue propre"
    # la de-labellisation vient du filtre 3 REEL (contenu re-atterri sur main),
    # pas d'un subprocess factice qui ferait tout passer pour clean
    assert mod.analyse_pr(repo, fake_pr, "main", "")["status"] == "clean"


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


@requires_gh_auth
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


@requires_gh_auth
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
