"""Tests for scripts/ci/check_scheduler_liveness.py (#15332).

The founding measurement: 2026-09-09, the last `event=schedule` run of the whole
repository is 01:13:03Z and four hours later nothing planned had fired, while
workflows stayed active and merges kept flowing. Two things must therefore hold:

  1. a 60-min organ with no scheduled run for 4 h reads DEAD -- not OK;
  2. the observer survives that outage (its heartbeat is a `push`, added to
     pr-gate-sweep-health-advisory.yml), and an instrument-wide probe failure
     is reported as INSTRUMENT_UNKNOWN rather than as a fleet-wide green.

The served-vs-declared ratio is rendered as a named warning and does NOT red the
organ: a permanently red check on a chronic condition gets ignored (repo
doctrine). The age predicates are what redden.
"""
from __future__ import annotations

import sys
from datetime import datetime, timedelta, timezone
from pathlib import Path

CI_DIR = Path(__file__).resolve().parents[1] / "ci"
sys.path.insert(0, str(CI_DIR))

import check_scheduler_liveness as sl  # noqa: E402

NOW = datetime(2026, 9, 9, 5, 14, tzinfo=timezone.utc)

HOURLY = sl.Organ("pr-gate-stale-sweep.yml", 60.0, "cron '7 * * * *'")
DAILY = sl.Organ("epic-neglect-sweep.yml", 1440.0, "cron '37 8 * * *'")


def times_ago(*minutes: float) -> list[datetime]:
    """Run times, newest first, from minutes-ago offsets."""
    return [NOW - timedelta(minutes=m) for m in minutes]


# --- verdicts de base --------------------------------------------------------

def test_fresh_run_is_ok():
    r = sl.evaluate(HOURLY, times_ago(10, 70, 130), NOW)
    assert r.verdict == "OK" and r.age_min == 10 and r.n_runs == 3


def test_degraded_delivery_is_late_not_ok():
    # 2x-4x declared: visible, but not red (chronic condition, repo doctrine).
    r = sl.evaluate(HOURLY, times_ago(150, 210), NOW)
    assert r.verdict == "LATE"


def test_founding_outage_reads_dead():
    # #15332: 4 h with no scheduled run for a 60-min organ. This is the case
    # that must never read OK again.
    r = sl.evaluate(HOURLY, times_ago(241, 301, 361), NOW)
    assert r.verdict == "DEAD"


def test_empty_history_is_dead_and_named():
    r = sl.evaluate(HOURLY, [], NOW)
    assert r.verdict == "DEAD" and r.n_runs == 0
    assert "schedule" in r.detail and "#15332" in r.detail


def test_daily_organ_floor_does_not_prematurely_red():
    # A daily organ 3 h late is normal jitter, not death.
    assert sl.evaluate(DAILY, times_ago(180, 1620), NOW).verdict == "OK"
    # Two days missed: degraded but alive.
    assert sl.evaluate(DAILY, times_ago(2900, 4340), NOW).verdict == "LATE"
    # Beyond 4x declared: dead.
    assert sl.evaluate(DAILY, times_ago(6000, 7440), NOW).verdict == "DEAD"


def test_floor_protects_high_frequency_organs_from_jitter():
    # 20-min organ: DEAD_FLOOR (90 min) dominates 4x declared (80 min).
    organ = sl.Organ("fast.yml", 20.0)
    assert sl.verdict_for(85.0, organ.declared_min) == "LATE"
    assert sl.verdict_for(95.0, organ.declared_min) == "DEAD"


# --- cadence servie ----------------------------------------------------------

def test_served_interval_is_the_median_gap():
    # 60-min declared, ~180 min served: the #15332 observation.
    r = sl.evaluate(HOURLY, times_ago(60, 240, 420, 600), NOW)
    assert r.served_min == 180
    assert any("SERVIE degradee" in w for w in r.warnings)


def test_served_cadence_does_not_red_the_organ():
    # Alive and degraded: the warning is rendered, the verdict stays non-red.
    r = sl.evaluate(HOURLY, times_ago(60, 240, 420), NOW)
    assert r.verdict == "OK" and r.warnings


def test_served_interval_needs_two_points():
    assert sl.served_interval_minutes(times_ago(10)) is None
    r = sl.evaluate(HOURLY, times_ago(10), NOW)
    assert r.served_min is None and not r.warnings


def test_declared_cadence_served_is_not_warned():
    r = sl.evaluate(HOURLY, times_ago(5, 65, 125), NOW)
    assert not r.warnings


# --- sonde -------------------------------------------------------------------

def test_parse_times_sorts_newest_first():
    payload = '[{"createdAt": "2026-09-09T01:00:00Z"}, {"createdAt": "2026-09-09T03:00:00Z"}]'
    t = sl.parse_times(payload)
    assert t[0] == datetime(2026, 9, 9, 3, 0, tzinfo=timezone.utc)


def test_probe_failure_is_unknown_not_dead(monkeypatch):
    class R:
        returncode = 1
        stdout = ""
        stderr = "gh: rate limit exceeded"
    monkeypatch.setattr(sl.subprocess, "run", lambda *a, **k: R())
    times, error = sl.probe("jsboige/CoursIA", HOURLY.workflow)
    assert times is None and "rc=1" in error


def test_probe_payload_corruption_is_unknown(monkeypatch):
    class R:
        returncode = 0
        stdout = "not json"
        stderr = ""
    monkeypatch.setattr(sl.subprocess, "run", lambda *a, **k: R())
    times, error = sl.probe("jsboige/CoursIA", HOURLY.workflow)
    assert times is None and "illisible" in error


# --- CLI ---------------------------------------------------------------------

def _stub_probe(mapping, monkeypatch):
    def fake(repo, workflow):
        return mapping.get(workflow, ([], ""))
    monkeypatch.setattr(sl, "probe", fake)


def fresh(hours: float = 0.0) -> list[datetime]:
    """Run time anchored on the REAL clock -- main() reads the wall clock."""
    return [datetime.now(timezone.utc) - timedelta(hours=hours)]


def test_cli_all_unknown_is_instrument_unknown_exit_1(monkeypatch, capsys):
    mapping = {o.workflow: (None, "sonde gh indisponible: OSError") for o in sl.REGISTRY}
    _stub_probe(mapping, monkeypatch)
    assert sl.main(["--repo", "x/y"]) == 1
    assert "INSTRUMENT_UNKNOWN" in capsys.readouterr().err


def test_cli_all_empty_histories_is_instrument_unknown(monkeypatch, capsys):
    # gh succeeds but every history is empty (wrong repo / missing
    # Actions:read) -- that signature must not be read as a fleet-wide death.
    mapping = {o.workflow: ([], "") for o in sl.REGISTRY}
    _stub_probe(mapping, monkeypatch)
    assert sl.main(["--repo", "x/y"]) == 1
    assert "INSTRUMENT_UNKNOWN" in capsys.readouterr().err


def test_cli_dead_organ_exits_1(monkeypatch):
    mapping = {o.workflow: (fresh(), "") for o in sl.REGISTRY}
    mapping[HOURLY.workflow] = (fresh(10), "")
    _stub_probe(mapping, monkeypatch)
    assert sl.main(["--repo", "x/y"]) == 1


def test_cli_healthy_fleet_exits_0(monkeypatch, capsys):
    mapping = {o.workflow: (fresh(), "") for o in sl.REGISTRY}
    _stub_probe(mapping, monkeypatch)
    assert sl.main(["--repo", "x/y"]) == 0
    assert "scheduler-liveness" in capsys.readouterr().out


def test_cli_json_surface(monkeypatch, capsys):
    mapping = {o.workflow: (fresh(), "") for o in sl.REGISTRY}
    _stub_probe(mapping, monkeypatch)
    import json

    assert sl.main(["--repo", "x/y", "--json"]) == 0
    payload = json.loads(capsys.readouterr().out)
    assert payload["dead"] == 0 and len(payload["organs"]) == len(sl.REGISTRY)
