"""Tests for scripts/series_progress_manager.py — series improvement session tracker."""

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import series_progress_manager as spm


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

SAMPLE_SESSION = {
    "series_id": "test-series-001",
    "target_path": "MyIA.AI.Notebooks/ML/ML.Net",
    "workflow": "enrich",
    "started_at": "2026-05-29T10:00:00",
    "updated_at": "2026-05-29T10:30:00",
    "statistics": {
        "total": 3,
        "completed": 1,
        "in_progress": 1,
        "pending": 1,
        "failed": 0,
    },
    "notebooks": {
        "ML-2.ipynb": {
            "status": "completed",
            "initial_score": 60,
            "final_score": 85,
        },
        "ML-3.ipynb": {
            "status": "in_progress",
        },
        "ML-4.ipynb": {
            "status": "pending",
        },
    },
}


def _write_session(progress_dir: Path, data: dict) -> Path:
    """Write a session JSON file into the progress directory."""
    progress_dir.mkdir(parents=True, exist_ok=True)
    session_file = progress_dir / f"{data['series_id']}-progress.json"
    session_file.write_text(json.dumps(data, indent=2), encoding="utf-8")
    return session_file


# ---------------------------------------------------------------------------
# find_session
# ---------------------------------------------------------------------------

class TestFindSession:
    def test_finds_existing_session(self, tmp_path, monkeypatch):
        monkeypatch.setattr(spm, "PROGRESS_DIR", tmp_path / "progress")
        _write_session(tmp_path / "progress", SAMPLE_SESSION)
        result = spm.find_session("test-series-001")
        assert result is not None
        assert result.exists()

    def test_returns_none_for_missing(self, tmp_path, monkeypatch):
        monkeypatch.setattr(spm, "PROGRESS_DIR", tmp_path / "progress")
        _write_session(tmp_path / "progress", SAMPLE_SESSION)
        result = spm.find_session("nonexistent")
        assert result is None

    def test_returns_none_when_dir_missing(self, tmp_path, monkeypatch):
        monkeypatch.setattr(spm, "PROGRESS_DIR", tmp_path / "nope")
        result = spm.find_session("anything")
        assert result is None


# ---------------------------------------------------------------------------
# list_sessions
# ---------------------------------------------------------------------------

class TestListSessions:
    def test_lists_active_session(self, tmp_path, monkeypatch, capsys):
        monkeypatch.setattr(spm, "PROGRESS_DIR", tmp_path / "progress")
        _write_session(tmp_path / "progress", SAMPLE_SESSION)
        spm.list_sessions()
        output = capsys.readouterr().out
        assert "test-series-001" in output
        assert "1/3" in output

    def test_no_sessions(self, tmp_path, monkeypatch, capsys):
        monkeypatch.setattr(spm, "PROGRESS_DIR", tmp_path / "progress")
        (tmp_path / "progress").mkdir(parents=True)
        spm.list_sessions()
        output = capsys.readouterr().out
        assert "Aucune session" in output

    def test_no_progress_dir(self, tmp_path, monkeypatch, capsys):
        monkeypatch.setattr(spm, "PROGRESS_DIR", tmp_path / "missing")
        spm.list_sessions()
        output = capsys.readouterr().out
        assert "Aucune session" in output

    def test_completed_session_shows_termine(self, tmp_path, monkeypatch, capsys):
        monkeypatch.setattr(spm, "PROGRESS_DIR", tmp_path / "progress")
        done = {**SAMPLE_SESSION, "statistics": {"total": 1, "completed": 1, "in_progress": 0, "pending": 0, "failed": 0}}
        _write_session(tmp_path / "progress", done)
        spm.list_sessions()
        output = capsys.readouterr().out
        assert "TERMINE" in output

    def test_failed_count_shown(self, tmp_path, monkeypatch, capsys):
        monkeypatch.setattr(spm, "PROGRESS_DIR", tmp_path / "progress")
        failed = {**SAMPLE_SESSION, "statistics": {"total": 2, "completed": 1, "in_progress": 0, "pending": 0, "failed": 1}}
        _write_session(tmp_path / "progress", failed)
        spm.list_sessions()
        output = capsys.readouterr().out
        assert "1 echecs" in output


# ---------------------------------------------------------------------------
# show_status
# ---------------------------------------------------------------------------

class TestShowStatus:
    def test_shows_detailed_status(self, tmp_path, monkeypatch, capsys):
        monkeypatch.setattr(spm, "PROGRESS_DIR", tmp_path / "progress")
        _write_session(tmp_path / "progress", SAMPLE_SESSION)
        spm.show_status("test-series-001")
        output = capsys.readouterr().out
        assert "ML-2.ipynb" in output
        assert "ML-3.ipynb" in output
        assert "ML-4.ipynb" in output
        assert "[OK]" in output
        assert "[..]" in output
        assert "[--]" in output

    def test_session_not_found(self, tmp_path, monkeypatch, capsys):
        monkeypatch.setattr(spm, "PROGRESS_DIR", tmp_path / "progress")
        (tmp_path / "progress").mkdir(parents=True)
        spm.show_status("missing")
        output = capsys.readouterr().out
        assert "non trouvee" in output

    def test_failed_notebook_shows_error(self, tmp_path, monkeypatch, capsys):
        monkeypatch.setattr(spm, "PROGRESS_DIR", tmp_path / "progress")
        data = {**SAMPLE_SESSION, "notebooks": {
            "broken.ipynb": {"status": "failed", "error": "timeout after 180s"}
        }}
        _write_session(tmp_path / "progress", data)
        spm.show_status("test-series-001")
        output = capsys.readouterr().out
        assert "[!!]" in output
        assert "timeout" in output


# ---------------------------------------------------------------------------
# cancel_session
# ---------------------------------------------------------------------------

class TestCancelSession:
    def test_cancels_and_backs_up(self, tmp_path, monkeypatch, capsys):
        monkeypatch.setattr(spm, "PROGRESS_DIR", tmp_path / "progress")
        session_file = _write_session(tmp_path / "progress", SAMPLE_SESSION)
        assert session_file.exists()
        spm.cancel_session("test-series-001")
        output = capsys.readouterr().out
        assert "annulee" in output
        assert not session_file.exists()
        backup = session_file.with_suffix(".json.cancelled")
        assert backup.exists()

    def test_cancel_missing(self, tmp_path, monkeypatch, capsys):
        monkeypatch.setattr(spm, "PROGRESS_DIR", tmp_path / "progress")
        (tmp_path / "progress").mkdir(parents=True)
        spm.cancel_session("ghost")
        output = capsys.readouterr().out
        assert "non trouvee" in output


# ---------------------------------------------------------------------------
# generate_report
# ---------------------------------------------------------------------------

class TestGenerateReport:
    def test_generates_markdown_report(self, tmp_path, monkeypatch, capsys):
        monkeypatch.setattr(spm, "PROGRESS_DIR", tmp_path / "progress")
        # Redirect report output dir
        reports_dir = tmp_path / "reports"
        _write_session(tmp_path / "progress", SAMPLE_SESSION)
        # Patch the report path
        original_path = spm.Path
        monkeypatch.setattr(spm, "Path", lambda p: reports_dir.parent / p if isinstance(p, str) else original_path(p))

        # Actually just generate and check stdout
        spm.generate_report("test-series-001")
        output = capsys.readouterr().out
        assert "ML-2.ipynb" in output
        assert "60" in output
        assert "85" in output

    def test_report_missing_session(self, tmp_path, monkeypatch, capsys):
        monkeypatch.setattr(spm, "PROGRESS_DIR", tmp_path / "progress")
        (tmp_path / "progress").mkdir(parents=True)
        spm.generate_report("ghost")
        output = capsys.readouterr().out
        assert "non trouvee" in output
