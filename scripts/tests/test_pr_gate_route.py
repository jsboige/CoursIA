#!/usr/bin/env python3
"""Tests for scripts/ci/pr_gate_route.py -- dead `queued` attempts (#17680).

Fondateur (mesure 2026-09-23/24, ai-01) : trois tentatives de rerun du workflow
`PR gate` restees `queued` (liste de jobs vide) pendant 19h30, dont celle de
#17099 -- PR READY, gate rc=0, mais `mergeStateStatus: BLOCKED` sans aucun
rouge. La route inline traitait TOUT `status != completed` comme « en vol »,
et le sweep voyait son `gh run rerun` refuse par l'API sur un run non termine :
impasse complete. La route est extraite dans le script pour etre testable --
ces tests sont le critere d'acceptation de l'issue.

Run:
    python -m pytest scripts/tests/test_pr_gate_route.py
"""
from __future__ import annotations

import sys
from datetime import datetime, timedelta, timezone
from pathlib import Path

import yaml

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT / "scripts" / "ci"))

import pr_gate_route as route  # noqa: E402

WORKFLOW = REPO_ROOT / ".github" / "workflows" / "pr-gate-rerun.yml"
SWEEP = REPO_ROOT / ".github" / "workflows" / "pr-gate-stale-sweep.yml"

NOW = datetime(2026, 9, 24, 14, 0, 0, tzinfo=timezone.utc)


def run_payload(
    status="queued",
    conclusion=None,
    run_started_at=None,
    updated_at=None,
    created_at="2026-09-23T18:52:00Z",
    rid=35895035044,
):
    return {
        "id": rid,
        "name": "PR gate",
        "status": status,
        "conclusion": conclusion,
        "run_started_at": run_started_at,
        "updated_at": updated_at,
        "created_at": created_at,
    }


# --- decision pure (classify) ------------------------------------------------


def test_classify_queued_beyond_threshold_is_dead():
    """Une tentative queued de plus de N heures n'est plus « en vol » -- c'est
    le coeur de #17680 : le statut seul ne distingue pas une tentative morte
    d'une saine, l'horloge si."""
    run = run_payload(
        run_started_at=None,
        updated_at="2026-09-23T18:52:00Z",  # ~19h avant NOW
    )
    action, reason = route.classify(run, NOW, timedelta(hours=2))
    assert action == "cancel_rerun"
    assert "#17680" in reason


def test_classify_recent_queued_is_in_flight():
    run = run_payload(run_started_at="2026-09-24T13:55:00Z")  # 5 min avant NOW
    action, _ = route.classify(run, NOW, timedelta(hours=2))
    assert action == "skip"


def test_classify_in_progress_is_in_flight_even_after_hours():
    """Seule la file d'attente peut mourir de faim silencieusement ; un run
    in_progress a un runner et rapportera."""
    run = run_payload(status="in_progress", run_started_at="2026-09-20T00:00:00Z")
    action, _ = route.classify(run, NOW, timedelta(hours=2))
    assert action == "skip"


def test_classify_completed_failure_reruns_and_success_skips():
    assert route.classify(run_payload(status="completed", conclusion="failure"), NOW, timedelta(hours=2))[0] == "rerun"
    assert route.classify(run_payload(status="completed", conclusion="success"), NOW, timedelta(hours=2))[0] == "skip"


def test_classify_boundary_exactly_at_threshold_stays_in_flight():
    """Exactement N heures = pas encore morte (comparaison stricte) : biaiser
    vers « en vol » quand l'horloge est a la limite."""
    run = run_payload(run_started_at=(NOW - timedelta(hours=2)).isoformat())
    action, _ = route.classify(run, NOW, timedelta(hours=2))
    assert action == "skip"


def test_attempt_started_at_falls_back_when_never_started():
    """Une tentative queued jamais demarree n'a pas de run_started_at : l'horloge
    tombe sur updated_at (transition vers queued), puis created_at."""
    assert route.attempt_started_at(
        run_payload(run_started_at=None, updated_at="2026-09-24T10:00:00Z")
    ) == datetime(2026, 9, 24, 10, 0, tzinfo=timezone.utc)
    assert route.attempt_started_at(
        run_payload(run_started_at=None, updated_at=None, created_at="2026-09-24T09:00:00Z")
    ) == datetime(2026, 9, 24, 9, 0, tzinfo=timezone.utc)


# --- route end-to-end (main, gh fake) ----------------------------------------


class FakeGh:
    """Dispatch gh_api/_run_gh par path ; enregistre les cancel."""

    def __init__(self, run=None, check_runs=(), statuses=()):
        self.run = run
        self.check_runs = list(check_runs)
        self.statuses = list(statuses)  # consommes par les sondes post-cancel
        self.cancels = []
        self.lookups = []

    def api(self, path):
        self.lookups.append(path)
        if "actions/runs?" in path:
            return {"workflow_runs": [self.run] if self.run else []}
        if "check-runs" in path:
            return {"check_runs": [{"name": name} for name in self.check_runs]}
        if "/actions/runs/" in path:
            if self.statuses:
                return {"status": self.statuses.pop(0)}
            return {"status": "completed"}
        raise AssertionError(f"chemin inattendu: {path}")

    def run_gh(self, args):
        if args[-1].endswith("/cancel"):
            self.cancels.append(args[-1])
            import types

            return types.SimpleNamespace(returncode=0, stdout="", stderr="")
        raise AssertionError(f"appel _run_gh inattendu: {args}")


def _drive(monkeypatch, tmp_path, fake, sha="abc123", extra=None):
    out = tmp_path / "gh_output"
    monkeypatch.setenv("GITHUB_OUTPUT", str(out))
    monkeypatch.setattr(route, "gh_api", fake.api)
    monkeypatch.setattr(route, "_run_gh", fake.run_gh)
    monkeypatch.setattr(route, "_now", lambda: NOW)
    monkeypatch.setattr(route, "_status_of", lambda repo, rid: fake.api(f"repos/x/actions/runs/{rid}").get("status"))
    argv = ["--repo", "jsboige/CoursIA", "--sha", sha, "--pr-number", "17680",
            "--wait-max-sec", "5", "--poll-sec", "0"]
    if extra:
        argv += extra
    rc = route.main(argv)
    action = ""
    run_id = ""
    for line in out.read_text(encoding="utf-8").splitlines():
        if line.startswith("action="):
            action = line.split("=", 1)[1]
        if line.startswith("run_id="):
            run_id = line.split("=", 1)[1]
    return rc, action, run_id


def test_stale_queued_attempt_is_cancelled_then_rerun(monkeypatch, tmp_path):
    """Critere d'acceptation 1 de #17680 : une tentative queued vieille de plus
    de N heures -> action=rerun APRES cancel (le run doit etre completed pour
    que l'API accepte le rerun)."""
    fake = FakeGh(
        run=run_payload(run_started_at=None, updated_at="2026-09-23T18:52:00Z"),
        statuses=["queued", "cancelling", "completed"],
    )
    rc, action, run_id = _drive(monkeypatch, tmp_path, fake)
    assert rc == 0
    assert action == "rerun"
    assert run_id == "35895035044"
    assert fake.cancels == ["repos/jsboige/CoursIA/actions/runs/35895035044/cancel"]


def test_recent_queued_attempt_skips_without_cancel(monkeypatch, tmp_path):
    """Critere d'acceptation 2 : tentative queued recente -> action=skip, et
    AUCUN cancel emis."""
    fake = FakeGh(run=run_payload(run_started_at=(NOW - timedelta(minutes=5)).isoformat()))
    _rc, action, _rid = _drive(monkeypatch, tmp_path, fake)
    assert action == "skip"
    assert fake.cancels == []


def test_revive_timeout_downgrades_to_skip(monkeypatch, tmp_path):
    """Le cancel ne converge pas vers completed dans la borne : skip honnete
    (le rerun serait refuse de toute facon), le prochain sweep re-dispatch."""
    statuses = ["cancelling"] * 50
    fake = FakeGh(
        run=run_payload(run_started_at=None, updated_at="2026-09-23T18:52:00Z"),
        statuses=statuses,
    )
    _rc, action, _rid = _drive(monkeypatch, tmp_path, fake, extra=["--wait-max-sec", "0"])
    assert action == "skip"
    assert fake.cancels  # le cancel a bien ete tente


def test_completed_failure_routes_rerun_no_cancel(monkeypatch, tmp_path):
    fake = FakeGh(run=run_payload(status="completed", conclusion="failure"))
    _rc, action, _rid = _drive(monkeypatch, tmp_path, fake)
    assert action == "rerun"
    assert fake.cancels == []


def test_no_run_with_existing_check_run_refuses_twin(monkeypatch, tmp_path):
    """Garde anti-jumeau #11519 preserve par l'extraction : un check-run
    « PR gate » deja present sur la tete sans run pull_request -> skip."""
    fake = FakeGh(run=None, check_runs=["PR gate"])
    _rc, action, _rid = _drive(monkeypatch, tmp_path, fake)
    assert action == "skip"


def test_no_run_without_check_run_aggregates_absent(monkeypatch, tmp_path):
    fake = FakeGh(run=None, check_runs=[])
    _rc, action, _rid = _drive(monkeypatch, tmp_path, fake)
    assert action == "aggregate_absent"


# --- wiring ------------------------------------------------------------------


def _load(path):
    return yaml.safe_load(path.read_text(encoding="utf-8"))


def test_rerun_workflow_resolves_via_the_script():
    """La route extraite doit etre celle que le workflow appelle -- un retour
    au bash inline re-ouvrirait l'angle mort non testable (#17680)."""
    data = _load(WORKFLOW)
    resolve = data["jobs"]["resolve"]
    text = str(resolve)
    assert "scripts/ci/pr_gate_route.py" in text, (
        "le resolve n'appelle plus pr_gate_route.py : la decision de route "
        "doit vivre dans le script teste, pas en bash inline"
    )
    assert "actions: write" in str(data.get("permissions", {})) or \
        data.get("permissions", {}).get("actions") == "write"


def test_twin_guard_string_lives_in_the_route_script():
    """La garde anti-jumeau a demenage avec la route : le message pinné doit
    exister dans le script (le wiring noop-guard pointe ici aussi)."""
    text = (REPO_ROOT / "scripts" / "ci" / "pr_gate_route.py").read_text(encoding="utf-8")
    assert "refusing to POST beside it (#11519 twin)" in text


def test_sweep_refusal_falls_back_to_dispatching_the_harness():
    """Le sweep ne peut pas annuler lui-meme (pas de checkout python dans sa
    boucle) : un rerun refuse doit dispatcher le harnais, dont la route sait
    revivre une tentative morte -- sinon l'impasse decrite dans #17680
    persiste cote organes autonomes."""
    text = SWEEP.read_text(encoding="utf-8")
    assert "gh workflow run pr-gate-rerun.yml" in text, (
        "le fallback #17680 a disparu du sweep : un rerun refuse (tentative "
        "queued morte) laisse la PR bloquee sans aucun organe pour la revivre"
    )
    assert "-f pr_number=" in text and "-f head_sha=" in text


def test_false_skip_message_stays_gone_everywhere():
    """Le message mensonger pre-#16624 ne doit revenir ni dans le workflow ni
    dans le script extrait."""
    for path in (WORKFLOW, REPO_ROOT / "scripts" / "ci" / "pr_gate_route.py"):
        assert "the gate will run on its own" not in path.read_text(encoding="utf-8")
