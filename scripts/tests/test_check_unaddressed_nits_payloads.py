"""Projections du transport de B.0 (#22757)."""
import importlib.util
import json
import sys
from datetime import datetime, timezone
from pathlib import Path


SCRIPT = Path(__file__).resolve().parents[1] / "check_unaddressed_nits.py"
spec = importlib.util.spec_from_file_location("check_unaddressed_nits_payloads", SCRIPT)
mod = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = mod
spec.loader.exec_module(mod)


def test_pr_view_projection_preserve_le_verdict_et_reduit_le_payload():
    raw = {
        "number": 41,
        "title": "PR de test",
        "body": "",
        "mergedAt": "2026-08-14T20:00:00Z",
        "author": {"login": "jsboige", "avatarUrl": "large"},
        "comments": [{
            "author": {"login": "jsboige", "avatarUrl": "large"},
            "createdAt": "2026-08-14T09:00:00Z",
            "body": "Attention 2 nits:\r\n- splitter\r\n- attribution",
            "reactions": {"totalCount": 12, "nodes": ["bruit"] * 30},
        }, {
            "author": {"login": "jsboige", "avatarUrl": "large"},
            "createdAt": "2026-08-14T12:00:00Z",
            "body": "Les 2 nits sont adresses.",
            "reactions": {"totalCount": 12, "nodes": ["bruit"] * 30},
        }],
        "reviews": [{
            "author": {"login": "jsboige", "avatarUrl": "large"},
            "submittedAt": "2026-08-14T13:00:00Z",
            "body": "Approved",
            "state": "APPROVED",
            "id": "PRR_opaque",
            "commit": {"oid": "a" * 40},
        }],
        "commits": [{
            "oid": "a" * 40,
            "committedDate": "2026-08-14T19:00:00Z",
            "messageBody": "large body" * 500,
            "authors": [{"login": "jsboige"}] * 30,
        }],
        "url": "https://example.invalid/pull/41",
        "state": "MERGED",
        "headRefOid": "a" * 40,
    }
    args = ["pr", "view", "41", "--json", "fields"]
    projected = mod._project_gh_payload(args, raw)

    before = mod.analyse(raw, [], datetime(2026, 8, 14, 20, tzinfo=timezone.utc))
    after = mod.analyse(projected, [], datetime(2026, 8, 14, 20, tzinfo=timezone.utc))
    assert after == before
    assert before["blocked"] is False
    assert len(json.dumps(projected)) < len(json.dumps(raw))
    assert projected["comments"][0]["body"] == raw["comments"][0]["body"]
    assert projected["commits"] == [{"oid": "a" * 40,
                                     "committedDate": "2026-08-14T19:00:00Z"}]

    unresolved = dict(raw, comments=raw["comments"][:1])
    unresolved_projection = mod._project_gh_payload(args, unresolved)
    unresolved_before = mod.analyse(
        unresolved, [], datetime(2026, 8, 14, 20, tzinfo=timezone.utc))
    unresolved_after = mod.analyse(
        unresolved_projection, [], datetime(2026, 8, 14, 20, tzinfo=timezone.utc))
    assert unresolved_before["blocked"] is True
    assert unresolved_after == unresolved_before


def test_gh_json_projette_avant_retour_au_cache(monkeypatch):
    raw = {
        "number": 41,
        "comments": [{"author": {"login": "user", "name": "long"},
                      "body": "nit", "createdAt": "date", "reactions": [1]}],
        "reviews": [], "commits": [],
    }

    class Completed:
        stdout = json.dumps(raw)

    monkeypatch.setattr(mod.subprocess, "run", lambda *a, **k: Completed())
    result = mod.gh_json(["pr", "view", "41", "--json", "comments,reviews,commits"])
    assert result["comments"] == [{
        "author": {"login": "user"}, "body": "nit", "createdAt": "date"}]


def test_projections_rest_conservent_les_preuves_utilisees():
    commit = {
        "commit": {"message": "titre\ncorps", "tree": {"sha": "tree"},
                   "author": {"name": "bruit"}},
        "files": [{"filename": "x.py", "sha": "blob", "status": "modified",
                   "previous_filename": "old.py",
                   "patch": "@@ -1,0 +1,3 @@\n+" + "bruit " * 100
                           + "\n+def preuve():\n+" + "bruit " * 100
                           + "\n+++ autre/fichier.py\n+class Exemple:",
                   "additions": 1, "changes": 2}],
        "stats": {"total": 2},
    }
    projected_commit = mod._project_gh_payload(
        ["api", "repos/jsboige/CoursIA/commits/sha"], commit)
    assert projected_commit == {
        "commit": {"message": "titre", "tree": {"sha": "tree"}},
        "files": [{"filename": "x.py", "sha": "blob", "status": "modified",
                   "previous_filename": "old.py",
                   "patch": "+def preuve():\n+class Exemple:"}],
    }
    assert mod._introduced_symbols({
        "x.py": commit["files"][0]["patch"]}) == mod._introduced_symbols({
            "x.py": projected_commit["files"][0]["patch"]})

    tree = {"truncated": False, "tree": [{"path": "x.py", "sha": "blob",
                                           "type": "blob", "mode": "100644"}]}
    assert mod._project_gh_payload(
        ["api", "repos/jsboige/CoursIA/git/trees/tree?recursive=1"], tree) == {
            "truncated": False,
            "tree": [{"path": "x.py", "sha": "blob", "type": "blob"}],
        }

    reviews = [{"id": 7, "user": {"login": "reviewer", "name": "long"},
                "body": "ignored"}]
    assert mod._project_gh_payload(
        ["api", "repos/jsboige/CoursIA/pulls/41/reviews", "--paginate"], reviews) == [
            {"id": 7, "user": {"login": "reviewer"}}]
    timeline = [{"event": "review_dismissed",
                 "actor": {"login": "other", "avatar_url": "long"},
                 "dismissed_review": {"review_id": 7, "state": "COMMENTED"},
                 "created_at": "date"}]
    assert mod._project_gh_payload(
        ["api", "repos/jsboige/CoursIA/issues/41/timeline", "--paginate"],
        timeline) == [{"event": "review_dismissed", "actor": {"login": "other"},
                       "dismissed_review": {"review_id": 7}}]


def test_projection_pulls_commits_conserve_sha_et_les_deux_dates():
    # #17315 : _pr_commits_rest ne lit que sha, commit.author.date et
    # commit.committer.date. La projection doit reproduire EXACTEMENT
    # cette normalisation, sur la forme slurp (liste de pages) comme sur
    # la page unique.
    raw_pages = [
        [{
            "sha": "a" * 40,
            "commit": {
                "message": "message long " * 50,
                "author": {"name": "bruit", "email": "x", "date": "2026-11-01T10:00:00Z"},
                "committer": {"name": "bruit", "email": "x", "date": "2026-11-01T11:00:00Z"},
                "tree": {"sha": "t" * 40}, "verification": {"verified": False},
            },
            "parents": [{"sha": "b" * 40}], "html_url": "bruit",
        }, {
            "sha": "c" * 40,
            "commit": {
                "author": {"date": None},
                "committer": {"date": "2026-11-02T09:00:00Z"},
            },
        }],
    ]

    def normalize(pages):
        flat = []
        for page in pages:
            flat.extend(page if isinstance(page, list) else [page])
        return [{"oid": c.get("sha") or "",
                 "committedDate": (c.get("commit") or {}).get("committer", {}).get("date"),
                 "authoredDate": (c.get("commit") or {}).get("author", {}).get("date")}
                for c in flat]

    projected = mod._project_gh_payload(
        ["api", "repos/jsboige/CoursIA/pulls/41/commits", "--paginate", "--slurp"],
        raw_pages)
    assert projected == [[
        {"sha": "a" * 40,
         "commit": {"author": {"date": "2026-11-01T10:00:00Z"},
                    "committer": {"date": "2026-11-01T11:00:00Z"}}},
        {"sha": "c" * 40,
         "commit": {"author": {"date": None},
                    "committer": {"date": "2026-11-02T09:00:00Z"}}},
    ]]
    assert normalize(projected) == normalize(raw_pages)


def test_projection_issue_unique_conserve_le_contrat_issueinfo():
    # #13725 : le discriminant PR-vs-issue est la PRESENCE de la cle
    # `pull_request`. #14218 : voie 3 lit title et body. Tout le reste
    # (~40 champs de presentation REST) est du transport mort.
    raw = {
        "number": 19742, "state": "open",
        "created_at": "2026-10-07T08:00:00Z",
        "title": "Epic Origami", "body": "corps " + "long " * 4000,
        "labels": [{"name": "l%d" % i} for i in range(10)],
        "assignees": [{"login": "a"}] * 5, "reactions": {"total_count": 99},
        "milestone": {"title": "M"}, "comments": 42, "locked": False,
    }
    projected = mod._project_gh_payload(
        ["api", "repos/jsboige/CoursIA/issues/19742"], raw)
    assert set(projected) == {"state", "created_at", "title", "body"}
    assert projected["body"] == raw["body"]
    info_raw = mod.IssueInfo(raw)
    info_proj = mod.IssueInfo(projected)
    assert (info_proj.state, info_proj.created_at, info_proj.title,
            info_proj.body) == (info_raw.state, info_raw.created_at,
                                info_raw.title, info_raw.body)

    pr_payload = dict(raw, pull_request={"url": "https://example.invalid/x",
                                         "html_url": "bruit"})
    projected_pr = mod._project_gh_payload(
        ["api", "repos/jsboige/CoursIA/issues/19742"], pr_payload)
    assert "pull_request" in projected_pr  # le discriminant survit
    assert projected_pr["pull_request"] == {"url": "https://example.invalid/x"}
    assert mod._gh_fetch_issue.__doc__  # symbole vivant, garde de typo

    # les endpoints voisins ne sont PAS captures par la branche issue seule :
    # /timeline reste servi par SA branche (event/actor/dismissed_review),
    # jamais par la projection issue (aucune cle state/body n'apparait).
    timeline = [{"event": "cross-referenced", "created_at": "date"}]
    assert mod._project_gh_payload(
        ["api", "repos/jsboige/CoursIA/issues/19742/timeline"], timeline) == [
            {"event": "cross-referenced"}]
