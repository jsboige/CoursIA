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
