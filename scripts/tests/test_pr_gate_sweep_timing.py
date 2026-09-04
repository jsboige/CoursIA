"""Execute the stale-sweep timing heredoc verbatim (#12728).

The instrument must separate run creation -> job start (queue) from job start
-> measurement time (observed execution). It deliberately ignores
``run_started_at``, which GitHub can set equal to ``created_at`` while the job
is still waiting for a runner.
"""

from __future__ import annotations

import json
import os
import re
import subprocess
from datetime import datetime, timedelta, timezone
from pathlib import Path

import yaml

REPO_ROOT = Path(__file__).resolve().parents[2]
WORKFLOW = REPO_ROOT / ".github" / "workflows" / "pr-gate-stale-sweep.yml"
JOB_NAME = "Re-aggregate stale PR gate verdicts"


def _extract_instrument() -> str:
    with WORKFLOW.open(encoding="utf-8") as stream:
        document = yaml.safe_load(stream)
    # L'instrument de timing est l'unique etape `if: always()` -- localisee
    # par contenu, pas par index (une etape d'amorcage precede desormais le
    # selecteur, #14267).
    candidates = [
        s
        for s in document["jobs"]["sweep"]["steps"]
        if s.get("if") == "always()"
    ]
    assert len(candidates) == 1, "expected exactly one if: always() step"
    step = candidates[0]
    run = step["run"]
    assert "jobs?filter=latest&per_page=100" in run
    assert "jobs?filter=all" not in run
    match = re.search(r"python - <<'PY'\n(.*?)\nPY\n?$", run, re.S)
    assert match, "timing heredoc missing from pr-gate-stale-sweep.yml"
    return match.group(1)


INSTRUMENT = _extract_instrument()


def _iso(value: datetime) -> str:
    return value.astimezone(timezone.utc).isoformat().replace("+00:00", "Z")


def _run_instrument(tmp_path: Path, run: dict, jobs: list[dict]):
    summary = tmp_path / "summary.md"
    env = dict(
        os.environ,
        RUN_JSON=json.dumps(run),
        JOBS_JSON=json.dumps({"jobs": jobs}),
        JOB_NAME=JOB_NAME,
        GITHUB_STEP_SUMMARY=str(summary),
    )
    completed = subprocess.run(
        ["python", "-c", INSTRUMENT],
        capture_output=True,
        text=True,
        encoding="utf-8",
        env=env,
        check=False,
    )
    return completed, summary


def test_job_start_measures_queue_and_ignores_run_started_at(tmp_path):
    now = datetime.now(timezone.utc)
    created = now - timedelta(minutes=12)
    started = now - timedelta(minutes=2)
    run = {
        "created_at": _iso(created),
        # This misleading run-level timestamp is intentionally equal to creation.
        "run_started_at": _iso(created),
    }
    jobs = [{"name": JOB_NAME, "started_at": _iso(started)}]

    completed, summary = _run_instrument(tmp_path, run, jobs)

    assert completed.returncode == 0
    assert "queue_seconds=600" in completed.stdout
    execution_match = re.search(
        r"\bobserved_execution_seconds=(\d+)\b", completed.stdout
    )
    assert execution_match
    execution_seconds = int(execution_match.group(1))
    assert 120 <= execution_seconds < 130
    rendered = summary.read_text(encoding="utf-8")
    assert "Queue: **600 s**" in rendered
    assert f"Observed execution: **{execution_seconds} s**" in rendered
    assert "`run_started_at` is not used" in rendered


def test_missing_job_timestamp_warns_without_fabricating_zero(tmp_path):
    now = datetime.now(timezone.utc)
    run = {"created_at": _iso(now), "run_started_at": _iso(now)}
    jobs = [{"name": JOB_NAME, "started_at": None}]

    completed, summary = _run_instrument(tmp_path, run, jobs)

    assert completed.returncode == 0
    assert "::warning::stale-sweep timing unavailable: missing job.started_at" in completed.stdout
    assert "queue_seconds=0" not in completed.stdout
    assert not summary.exists()


def test_ambiguous_job_match_warns_instead_of_selecting_one(tmp_path):
    now = datetime.now(timezone.utc)
    run = {"created_at": _iso(now)}
    jobs = [
        {"name": JOB_NAME, "started_at": _iso(now)},
        {"name": JOB_NAME, "started_at": _iso(now)},
    ]

    completed, summary = _run_instrument(tmp_path, run, jobs)

    assert completed.returncode == 0
    assert "expected one current job" in completed.stdout
    assert not summary.exists()
