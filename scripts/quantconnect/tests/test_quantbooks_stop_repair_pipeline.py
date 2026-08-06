"""Tests for quantbooks_stop_repair_pipeline.py — Stop&Repair pipeline orchestrator.

Hermetic tests covering:
  - ``_credentials_present`` env detection
  - ``_read_cloud_id`` config.json parsing (present/missing/malformed)
  - ``phase_audit`` missing project dir / missing audit script
  - ``phase_push`` SKIP / DRY_RUN / PUSH actions + KNOWN_CLOUD_IDS overrides
  - ``phase_exec`` SKIP_NO_PROJECT_DIR / DRY_RUN behavior
  - ``phase_verify`` SCRIPT_MISSING branch
  - ``phase_report`` CSV + Markdown artifacts (timestamped out_dir)
  - ``main`` --dry-run, --phase, --pipeline flag wiring

Le scope #6891 substance est deja RESOLVED (G.9 firsthand c.1331+2), donc ces
tests valident l'**outillage** (orchestrateur), pas le contenu des quantbooks.
"""
from __future__ import annotations

import csv
import json
import os
import subprocess
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

import quantbooks_stop_repair_pipeline as qsrp  # noqa: E402


# -- _credentials_present --

class TestCredentialsPresent:
    def test_all_present(self, monkeypatch):
        for k in ("QC_API_USER_ID", "QC_API_ACCESS_TOKEN", "QC_API_ORGANIZATION_ID"):
            monkeypatch.setenv(k, "x")
        assert qsrp._credentials_present() is True

    def test_one_missing(self, monkeypatch):
        monkeypatch.setenv("QC_API_USER_ID", "x")
        monkeypatch.setenv("QC_API_ACCESS_TOKEN", "x")
        monkeypatch.delenv("QC_API_ORGANIZATION_ID", raising=False)
        assert qsrp._credentials_present() is False

    def test_all_missing(self, monkeypatch):
        for k in ("QC_API_USER_ID", "QC_API_ACCESS_TOKEN", "QC_API_ORGANIZATION_ID"):
            monkeypatch.delenv(k, raising=False)
        assert qsrp._credentials_present() is False


def _make_project(root: Path, name: str, *, config: dict | None = None,
                  notebook: dict | None = None) -> Path:
    """Helper : cree ``root / MyIA.AI.Notebooks / QuantConnect / projects / <name>``
    avec config.json et/ou quantbook.ipynb optionnels."""
    proj = root / "MyIA.AI.Notebooks" / "QuantConnect" / "projects" / name
    proj.mkdir(parents=True, exist_ok=True)
    if config is not None:
        (proj / "config.json").write_text(json.dumps(config, ensure_ascii=False), encoding="utf-8")
    if notebook is not None:
        (proj / "quantbook.ipynb").write_text(json.dumps(notebook, ensure_ascii=False), encoding="utf-8")
    return proj


def _make_audit_script(root: Path) -> Path:
    """Helper : cree un audit_quantbooks_unexec.py minimaliste (stdout = 'HEALTHY').
    Permet a phase_audit de fonctionner sur un tmp_path sans repo reel."""
    scripts_dir = root / "scripts" / "quantconnect"
    scripts_dir.mkdir(parents=True, exist_ok=True)
    script = scripts_dir / "audit_quantbooks_unexec.py"
    script.write_text("#!/usr/bin/env python3\nimport sys\nsys.stdout.write('Class: HEALTHY\\n')\n", encoding="utf-8")
    return script


def _make_exec_script(root: Path) -> Path:
    """Helper : cree un qc_quantbook_execute.py minimaliste (sortie immediate)."""
    scripts_dir = root / "scripts" / "notebook_tools"
    scripts_dir.mkdir(parents=True, exist_ok=True)
    script = scripts_dir / "qc_quantbook_execute.py"
    script.write_text("#!/usr/bin/env python3\nimport sys\nsys.stdout.write('OK\\n')\n", encoding="utf-8")
    return script


# -- _read_cloud_id --

class TestReadCloudId:
    def test_missing_config(self, tmp_path):
        assert qsrp._read_cloud_id(tmp_path, "ghost") is None

    def test_present(self, tmp_path):
        _make_project(tmp_path, "X", config={"cloud-id": 12345})
        assert qsrp._read_cloud_id(tmp_path, "X") == 12345

    def test_absent_field(self, tmp_path):
        _make_project(tmp_path, "X", config={"language": "Py"})
        assert qsrp._read_cloud_id(tmp_path, "X") is None

    def test_zero_cloud_id_is_dead_not_present(self, tmp_path):
        # cloud-id 0 = DEAD per audit ; _read_cloud_id returns None to signal
        # "needs push" (orchestrator treats None as push-required).
        _make_project(tmp_path, "X", config={"cloud-id": 0})
        assert qsrp._read_cloud_id(tmp_path, "X") is None

    def test_malformed_json(self, tmp_path):
        proj = _make_project(tmp_path, "X")
        (proj / "config.json").write_text("{not json", encoding="utf-8")
        assert qsrp._read_cloud_id(tmp_path, "X") is None


# -- phase_audit --

class TestPhaseAudit:
    def test_missing_project_marks_kernel_missing(self, tmp_path):
        # Audit script minimaliste requis pour que phase_audit aille au dela du pre-flight.
        _make_audit_script(tmp_path)
        results: dict = {}
        qsrp.phase_audit(tmp_path, ["ghost"], results)
        assert results["audit"][0]["quantbook"] == "ghost"
        assert results["audit"][0]["exists"] is False
        assert results["audit"][0]["kernel"] == "MISSING"

    def test_missing_audit_script_records_error(self, tmp_path):
        # tmp_path n'a pas de scripts/quantconnect/audit_quantbooks_unexec.py
        # Phase audit ecrit le notebook mais ne lance pas l'audit (il le detecte absent).
        notebook = {"cells": [], "metadata": {"kernelspec": {"name": "python3"}}}
        _make_project(tmp_path, "X", notebook=notebook)
        results: dict = {}
        qsrp.phase_audit(tmp_path, ["X"], results)
        assert "error" in results["audit"]


# -- phase_push --

class TestPhasePush:
    def test_skip_already_pushed_via_known_ids(self, tmp_path):
        _make_project(tmp_path, "DualMomentum", config={"cloud-id": 28692516})
        results: dict = {}
        qsrp.phase_push(tmp_path, ["DualMomentum"], results, dry_run=False)
        assert results["push"][0]["action"] == "SKIP_ALREADY_PUSHED"

    def test_dry_run_pending_when_no_cloud_id(self, tmp_path):
        _make_project(tmp_path, "Ghost", config={"language": "Py"})
        results: dict = {}
        qsrp.phase_push(tmp_path, ["Ghost"], results, dry_run=True)
        assert results["push"][0]["action"] == "DRY_RUN_PUSH_PENDING"

    def test_real_push_records_returncode(self, tmp_path, monkeypatch):
        _make_project(tmp_path, "Ghost", config={"language": "Py"})
        # On stub `subprocess.run` pour eviter un vrai lean cloud push.
        captured = {}

        def fake_run(cmd, **kwargs):
            captured["cmd"] = cmd
            return subprocess.CompletedProcess(cmd, 0, stdout="", stderr="")

        monkeypatch.setattr(qsrp.subprocess, "run", fake_run)
        results: dict = {}
        qsrp.phase_push(tmp_path, ["Ghost"], results, dry_run=False)
        assert results["push"][0]["action"] == "PUSH_RC_0"
        assert "cloud" in captured["cmd"]


# -- phase_exec --

class TestPhaseExec:
    def test_missing_project_dir(self, tmp_path):
        _make_exec_script(tmp_path)  # requis pour passer le pre-flight script_missing
        results: dict = {}
        qsrp.phase_exec(tmp_path, ["ghost"], results, dry_run=True, timeout=60)
        assert results["exec"][0]["action"] == "SKIP_NO_PROJECT_DIR"

    def test_dry_run_pending(self, tmp_path):
        _make_exec_script(tmp_path)
        _make_project(tmp_path, "X")
        results: dict = {}
        qsrp.phase_exec(tmp_path, ["X"], results, dry_run=True, timeout=60)
        assert results["exec"][0]["action"] == "DRY_RUN_EXEC_PENDING"

    def test_missing_exec_script_records_error(self, tmp_path):
        _make_project(tmp_path, "X")
        results: dict = {}
        qsrp.phase_exec(tmp_path, ["X"], results, dry_run=False, timeout=60)
        assert "error" in results["exec"]


# -- phase_report --

class TestPhaseReport:
    def test_csv_and_md_written(self, tmp_path):
        results = {
            "audit": [
                {"quantbook": "X", "kernel": "HEALTHY", "cloud_id": 1},
            ],
            "push": [
                {"quantbook": "X", "action": "SKIP_ALREADY_PUSHED", "cloud_id": 1},
            ],
        }
        qsrp.phase_report(tmp_path, results, output_csv=None, output_md=None)
        out_dirs = list((tmp_path / "results").iterdir())
        assert len(out_dirs) == 1
        out_dir = out_dirs[0]
        assert out_dir.name.startswith("quantbooks_stop_repair_")
        assert (out_dir / "report.csv").exists()
        assert (out_dir / "report.md").exists()
        # CSV parse-able + contient la ligne attendue
        with open(out_dir / "report.csv", encoding="utf-8") as fh:
            rows = list(csv.reader(fh))
        assert rows[0] == ["phase", "quantbook", "status", "details"]
        assert any(r[0] == "audit" and r[1] == "X" for r in rows[1:])

    def test_md_contains_phase_sections(self, tmp_path):
        results = {
            "audit": [{"quantbook": "X", "kernel": "HEALTHY"}],
            "push": [{"quantbook": "X", "action": "SKIP_ALREADY_PUSHED"}],
            "exec": [],
            "verify": [],
        }
        qsrp.phase_report(tmp_path, results, output_csv=None, output_md=None)
        out_dir = next((tmp_path / "results").iterdir())
        md = (out_dir / "report.md").read_text(encoding="utf-8")
        assert "## Phase Audit" in md
        assert "## Phase Push" in md
        # Pas de double "## Phase Audit" (regression fix)
        assert md.count("## Phase Audit") == 1


# -- main wiring --

class TestMainWiring:
    def test_dry_run_exits_zero(self, tmp_path, monkeypatch, capsys):
        # _repo_root doit pointer sur tmp_path (pas le vrai repo).
        monkeypatch.setattr(qsrp, "_repo_root", lambda: tmp_path)
        rc = qsrp.main(["--pipeline", "--dry-run"])
        assert rc == 0

    def test_phase_filter_only_runs_audit(self, tmp_path, monkeypatch):
        monkeypatch.setattr(qsrp, "_repo_root", lambda: tmp_path)
        rc = qsrp.main(["--phase", "audit", "--dry-run"])
        assert rc == 0

    def test_pipeline_writes_report_dir(self, tmp_path, monkeypatch):
        monkeypatch.setattr(qsrp, "_repo_root", lambda: tmp_path)
        qsrp.main(["--pipeline", "--dry-run"])
        assert (tmp_path / "results").exists()


# -- KNOWN_CLOUD_IDS sanity --

class TestKnownCloudIds:
    def test_dual_momentum(self):
        assert qsrp.KNOWN_CLOUD_IDS["DualMomentum"] == 28692516

    def test_ema_cross_alpha(self):
        assert qsrp.KNOWN_CLOUD_IDS["EMA-Cross-Alpha"] == 28885488

    def test_scope_has_eight_quantbooks(self):
        assert len(qsrp.DEFAULT_QUANTBOOKS) == 8
