"""Lecture des fichiers REST pour l'attestation locale Lean."""

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "scripts" / "lean"))
import attest_local_build as alb  # noqa: E402


def test_pr_files_reads_rest_filename_and_previous_filename(monkeypatch):
    calls = []

    def fake_gh(repo, path):
        calls.append(path)
        if path.endswith("page=1"):
            return [{"filename": f"docs/{i}.md", "status": "modified"}
                    for i in range(99)] + [
                {"filename": "new/A.lean", "previous_filename": "old/A.lean",
                 "status": "renamed"}]
        return [{"filename": "lake/B.lean", "status": "modified"}]

    monkeypatch.setattr(alb, "gh_json", fake_gh)
    files = alb.pr_files("owner/repo", 123)
    assert files[-3:] == ["new/A.lean", "old/A.lean", "lake/B.lean"]
    assert len(calls) == 2
    assert calls[-1].endswith("per_page=100&page=2")


def test_pr_files_rejects_unreadable_or_incomplete_entries(monkeypatch):
    monkeypatch.setattr(alb, "gh_json", lambda *_: [{"status": "modified"}])
    with pytest.raises(alb.OrganError, match="filename"):
        alb.pr_files("owner/repo", 123)
    monkeypatch.setattr(alb, "gh_json", lambda *_: [
        {"filename": "new/A.lean", "status": "renamed"}])
    with pytest.raises(alb.OrganError, match="previous_filename"):
        alb.pr_files("owner/repo", 123)


def test_pr_files_refuses_github_3000_file_cap(monkeypatch):
    monkeypatch.setattr(alb, "gh_json", lambda *_: [
        {"filename": f"lake/{i}.lean", "status": "modified"} for i in range(100)])
    with pytest.raises(alb.OrganError, match="tronquee"):
        alb.pr_files("owner/repo", 123)
