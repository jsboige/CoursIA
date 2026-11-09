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

def _stub_state(mapping, monkeypatch):
    """Etat de workflow par fichier (#22937 volet 6).

    Une valeur `dict` est rendue telle quelle ; un tuple `(None, motif)` simule
    une lecture en echec (403/404/timeout). Defaut pour un fichier absent :
    `active` -- le verdict d'age est alors inchange.
    """

    def fake(repo, workflow):
        value = mapping.get(workflow, {"state": "active", "updated_at": ""})
        if isinstance(value, tuple):
            return value
        return value, ""

    monkeypatch.setattr(sl, "probe_workflow_state", fake)


def _stub_probe(mapping, monkeypatch):
    def fake(repo, workflow):
        return mapping.get(workflow, ([], ""))
    monkeypatch.setattr(sl, "probe", fake)
    # L'etat du workflow est lu pour CHAQUE organe (#22937 volet 6) : sans ce
    # stub, ces tests appelleraient le vrai `gh`. Defaut = actif, donc le
    # verdict d'age est inchange pour tous les tests anterieurs.
    _stub_state({}, monkeypatch)


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


# --- severite d'un DEAD (#18292) ---------------------------------------------
#
# Mesure du 2026-09-28: un DEAD de livraison 'schedule' recopie en rouge sur la
# jambe `push` a rougi 37 des 45 commits de main du jour, sans qu'aucun ne soit
# casse. La jambe `push` passe donc `--dead-exit warning`. Le VERDICT ne bouge
# pas et aucun seuil ne monte -- seule la severite imprimee change.

def _one_dead_fleet(monkeypatch):
    """Six organs, exactly one DEAD (the hourly sweep at 10 h)."""
    mapping = {o.workflow: (fresh(), "") for o in sl.REGISTRY}
    mapping[HOURLY.workflow] = (fresh(10), "")
    _stub_probe(mapping, monkeypatch)


def test_cli_dead_default_stays_error_and_exit_1(monkeypatch, capsys):
    _one_dead_fleet(monkeypatch)
    assert sl.main(["--repo", "x/y"]) == 1
    err = capsys.readouterr().err
    assert "::error::[scheduler-liveness] pr-gate-stale-sweep.yml" in err


def test_cli_dead_exit_warning_names_it_green(monkeypatch, capsys):
    _one_dead_fleet(monkeypatch)
    assert sl.main(["--repo", "x/y", "--dead-exit", "warning"]) == 0
    err = capsys.readouterr().err
    # Nomme, pas tu: le DEAD est toujours imprime, seul son marqueur change.
    assert "::warning::[scheduler-liveness] pr-gate-stale-sweep.yml" in err
    assert "::error::[scheduler-liveness] pr-gate-stale-sweep.yml" not in err
    assert "avertissement sur cette jambe" in err


def test_severity_does_not_move_a_threshold():
    # Le litmus anti-gaming: --dead-exit ne touche ni les seuils ni le verdict.
    assert sl.DEAD_FACTOR == 4 and sl.DEAD_FLOOR_MIN == 90.0
    assert sl.verdict_for(241.0, 60.0) == "DEAD"
    assert sl.verdict_for(239.0, 60.0) == "LATE"


def test_instrument_unknown_keeps_its_red_in_warning_mode(monkeypatch, capsys):
    # C'est la MESURE qui est en panne, pas la cadence qu'on excuse.
    mapping = {o.workflow: (None, "sonde gh indisponible: OSError") for o in sl.REGISTRY}
    _stub_probe(mapping, monkeypatch)
    assert sl.main(["--repo", "x/y", "--dead-exit", "warning"]) == 1
    assert "INSTRUMENT_UNKNOWN" in capsys.readouterr().err


# --- sweep du meme push (#18292) ---------------------------------------------
#
# Course, pas cadence: sur `push`, cette jambe et le sweep partent du MEME
# commit. La sonde d'age cherche le dernier succes TERMINE et lisait donc celui
# du merge precedent (instance fondatrice: run 36461754953 vs sweep 36461754984,
# meme head_sha).

SHA = "36461754953a" * 2


def _run(sha, status, conclusion=""):
    return {"headSha": sha, "status": status, "conclusion": conclusion}


def test_sweep_alive_covers_the_founding_race():
    runs = [_run("76461754984b", "completed", "success"), _run(SHA, "in_progress")]
    assert sl.sweep_run_alive_for_sha(runs, SHA) == (True, "in_progress")


def test_sweep_queued_and_success_are_alive():
    assert sl.sweep_run_alive_for_sha([_run(SHA, "queued")], SHA) == (True, "queued")
    assert sl.sweep_run_alive_for_sha(
        [_run(SHA, "completed", "success")], SHA
    ) == (True, "completed/success")


def test_sweep_failure_for_this_sha_is_not_service():
    # Un sweep en echec ne vaut pas service rendu: la sonde d'age garde le
    # droit de rougir.
    assert sl.sweep_run_alive_for_sha([_run(SHA, "completed", "failure")], SHA) == (False, "")


def test_sweep_other_sha_does_not_excuse_this_commit():
    # Le coeur du fix: un run vivant pour un AUTRE commit ne dit rien de celui-ci.
    assert sl.sweep_run_alive_for_sha([_run("deadbeef" * 5, "in_progress")], SHA) == (False, "")


def test_sweep_empty_history_and_missing_sha_are_not_alive():
    assert sl.sweep_run_alive_for_sha([], SHA) == (False, "")
    assert sl.sweep_run_alive_for_sha([{"status": "in_progress"}], SHA) == (False, "")


def test_sweep_rerun_of_same_sha_first_live_run_wins():
    runs = [
        _run(SHA, "completed", "cancelled"),
        _run("deadbeef" * 5, "in_progress"),
        _run(SHA, "in_progress"),
    ]
    assert sl.sweep_run_alive_for_sha(runs, SHA) == (True, "in_progress")


def test_sweep_probe_payload_must_be_a_list(monkeypatch):
    class R:
        returncode = 0
        stdout = '{"headSha": "x"}'
        stderr = ""
    monkeypatch.setattr(sl.subprocess, "run", lambda *a, **k: R())
    runs, error = sl.probe_sweep_runs("jsboige/CoursIA")
    assert runs is None and "liste de runs attendue" in error


def test_sweep_probe_failure_is_named(monkeypatch):
    class R:
        returncode = 1
        stdout = ""
        stderr = "gh: rate limit exceeded"
    monkeypatch.setattr(sl.subprocess, "run", lambda *a, **k: R())
    runs, error = sl.probe_sweep_runs("jsboige/CoursIA")
    assert runs is None and "rc=1" in error


def _stub_sweep_probe(payload, monkeypatch):
    def fake(repo):
        return payload
    monkeypatch.setattr(sl, "probe_sweep_runs", fake)


def test_cli_sweep_alive_positive_control_exits_0(monkeypatch, capsys):
    # Controle positif d'acceptance: rejouer la situation du run 36461754953
    # (sweep du meme head_sha en cours) doit rendre une sonde d'age verte.
    _stub_probe_never_called(monkeypatch)
    _stub_sweep_probe(([_run(SHA, "in_progress")], ""), monkeypatch)
    assert sl.main(["--repo", "x/y", "--sweep-alive-for-sha", SHA]) == 0
    assert "sweep vivant" in capsys.readouterr().out


def test_cli_sweep_alive_negative_control_exits_3(monkeypatch, capsys):
    # Controle negatif: aucun run du sweep pour ce commit -> repli sur l'age,
    # donc rc 3 (et non 0): le mode ne peut pas masquer un sweep mort.
    _stub_sweep_probe(([_run("deadbeef" * 5, "completed", "success")], ""), monkeypatch)
    assert sl.main(["--repo", "x/y", "--sweep-alive-for-sha", SHA]) == 3
    assert "repli sur le critere d'age" in capsys.readouterr().out


def test_cli_sweep_alive_probe_failure_exits_4(monkeypatch, capsys):
    _stub_sweep_probe((None, "gh rc=1: rate limit exceeded"), monkeypatch)
    assert sl.main(["--repo", "x/y", "--sweep-alive-for-sha", SHA]) == 4
    assert "repli sur le critere d'age" in capsys.readouterr().err


def test_cli_sweep_alive_short_circuits_the_cadence_probe(monkeypatch):
    _stub_probe_never_called(monkeypatch)
    _stub_sweep_probe(([], ""), monkeypatch)
    assert sl.main(["--repo", "x/y", "--sweep-alive-for-sha", SHA]) == 3


def _stub_probe_never_called(monkeypatch):
    """Fails loudly if the race mode still walks the cadence registry."""

    def boom(repo, workflow):
        raise AssertionError("--sweep-alive-for-sha ne doit pas sonder la cadence")

    monkeypatch.setattr(sl, "probe", boom)


# --- workflow desactive != cron mort (#22937 volet 6) ------------------------
#
# Mesure du 2026-10-24T11:46:51Z : linux-runner-starvation-advisory.yml et
# coursia-waiter-starvation-advisory.yml ont ete passes en `disabled_manually`
# par un operateur. Un workflow desactive ne recoit plus ni `schedule` ni
# `workflow_run` : son dernier run vieillit mecaniquement, et l'organe rendait
# `DEAD ... dernier run 4324 min` la ou la cause est un geste d'operateur. Deux
# causes, deux remedes -- la desactivation doit etre nommee, pas confondue avec
# une panne de livraison.

STARVATION = sl.Organ("linux-runner-starvation-advisory.yml", 30.0, "cron '19,49 * * * *'")

# Le payload REST mesure le 2026-10-24 (forme exacte renvoyee par
# GET /repos/jsboige/CoursIA/actions/workflows/<file>).
DISABLED_PAYLOAD = {
    "id": 1,
    "name": "linux-runner-starvation-advisory",
    "path": ".github/workflows/linux-runner-starvation-advisory.yml",
    "state": "disabled_manually",
    "updated_at": "2026-10-24T11:46:51Z",
}
ACTIVE_PAYLOAD = {"state": "active", "updated_at": "2026-10-20T08:00:00Z"}


def test_disabled_workflow_reads_disabled_not_dead():
    """Controle POSITIF : un workflow desactive rend DISABLED, pas DEAD."""
    r = sl.evaluate(STARVATION, times_ago(4324, 4384, 4444), NOW)
    assert r.verdict == "DEAD"  # ce que l'organe rendait avant le fix
    sl.apply_workflow_state(r, DISABLED_PAYLOAD, "")
    assert r.verdict == "DISABLED"
    assert r.workflow_state == "disabled_manually"
    # La date du geste de l'operateur est portee par la ligne de verdict.
    assert r.state_updated_at == "2026-10-24T11:46:51Z"
    assert "DESACTIVE" in r.detail and "2026-10-24T11:46:51Z" in r.detail


def test_disabled_inactivity_is_also_disabled():
    # Desactivation automatique par GitHub (60 j d'inactivite) : meme effet sur
    # les declencheurs, donc meme verdict.
    r = sl.evaluate(STARVATION, times_ago(4324, 4384), NOW)
    sl.apply_workflow_state(r, {"state": "disabled_inactivity", "updated_at": "x"}, "")
    assert r.verdict == "DISABLED"


def test_active_workflow_with_stale_cron_stays_dead():
    """Controle NEGATIF 1 : un workflow actif dont le cron ne livre plus reste DEAD."""
    r = sl.evaluate(STARVATION, times_ago(4324, 4384, 4444), NOW)
    sl.apply_workflow_state(r, ACTIVE_PAYLOAD, "")
    assert r.verdict == "DEAD"
    assert r.workflow_state == "active"


def test_unreadable_state_forges_neither_disabled_nor_dead():
    """Controle NEGATIF 2 : une lecture d'etat en echec ne fabrique rien.

    Cas mesure : 403/404/timeout sur l'endpoint d'etat. Le verdict d'age est
    conserve tel quel et l'echec est nomme -- ni `DISABLED` (faux positif), ni
    `DEAD` (faux positif sur un organe sain), ni blocage de l'organe.
    """
    healthy = sl.evaluate(STARVATION, times_ago(10, 40, 70), NOW)
    assert healthy.verdict == "OK"
    sl.apply_workflow_state(healthy, None, "gh rc=1: HTTP 403: Resource not accessible")
    assert healthy.verdict == "OK"
    assert healthy.workflow_state == ""  # pas d'etat lu != etat actif
    assert any("illisible" in w and "403" in w for w in healthy.warnings)

    dead = sl.evaluate(STARVATION, times_ago(4324, 4384), NOW)
    sl.apply_workflow_state(dead, None, "gh rc=1: HTTP 404: Not Found")
    assert dead.verdict == "DEAD"  # verdict d'age conserve, pas de faux DISABLED
    assert any("illisible" in w for w in dead.warnings)


def test_unknown_state_name_does_not_rewrite_the_verdict():
    # Un etat qu'on ne connait pas (valeur future de l'API) n'est ni actif ni
    # desactive : le verdict d'age est conserve et l'etat est nomme.
    r = sl.evaluate(STARVATION, times_ago(4324, 4384), NOW)
    sl.apply_workflow_state(r, {"state": "something_new", "updated_at": "x"}, "")
    assert r.verdict == "DEAD"
    assert any("inhabituel" in w and "something_new" in w for w in r.warnings)


def test_disabled_with_fresh_run_is_named_before_it_ages():
    # Workflow desactive dont le dernier run est encore frais : il n'y a pas
    # encore de DEAD a requalifier, mais le fait doit etre dit (il ne livrera
    # plus jamais).
    r = sl.evaluate(STARVATION, times_ago(10, 40), NOW)
    assert r.verdict == "OK"
    sl.apply_workflow_state(r, DISABLED_PAYLOAD, "")
    assert r.verdict == "OK"
    assert any("DESACTIVE" in w for w in r.warnings)


def test_workflow_state_probe_parses_the_api_payload(monkeypatch):
    class R:
        returncode = 0
        stdout = '{"state": "disabled_manually", "updated_at": "2026-10-24T11:46:51Z"}'
        stderr = ""
    monkeypatch.setattr(sl.subprocess, "run", lambda *a, **k: R())
    payload, error = sl.probe_workflow_state("jsboige/CoursIA", STARVATION.workflow)
    assert payload is not None and payload["state"] == "disabled_manually"
    assert error == ""


def test_workflow_state_probe_403_is_named_not_raised(monkeypatch):
    class R:
        returncode = 1
        stdout = ""
        stderr = "gh: Resource not accessible by integration (HTTP 403)"
    monkeypatch.setattr(sl.subprocess, "run", lambda *a, **k: R())
    payload, error = sl.probe_workflow_state("jsboige/CoursIA", STARVATION.workflow)
    assert payload is None and "403" in error


def test_workflow_state_probe_missing_state_field_is_unreadable(monkeypatch):
    class R:
        returncode = 0
        stdout = '{"id": 1}'
        stderr = ""
    monkeypatch.setattr(sl.subprocess, "run", lambda *a, **k: R())
    payload, error = sl.probe_workflow_state("jsboige/CoursIA", STARVATION.workflow)
    assert payload is None and "'state' absent" in error


def test_workflow_state_probe_timeout_is_named(monkeypatch):
    import subprocess as sp

    def boom(*a, **k):
        raise sp.TimeoutExpired(cmd="gh", timeout=60)

    monkeypatch.setattr(sl.subprocess, "run", boom)
    payload, error = sl.probe_workflow_state("jsboige/CoursIA", STARVATION.workflow)
    assert payload is None and "TimeoutExpired" in error


def _disabled_hourly_fleet(monkeypatch):
    """Six organs, l'hourly sweep DEAD par l'age -- et desactive a la source."""
    mapping = {o.workflow: (fresh(), "") for o in sl.REGISTRY}
    mapping[HOURLY.workflow] = (fresh(10), "")
    _stub_probe(mapping, monkeypatch)
    _stub_state({HOURLY.workflow: DISABLED_PAYLOAD}, monkeypatch)


def test_cli_disabled_is_red_and_names_the_operator_date(monkeypatch, capsys):
    _disabled_hourly_fleet(monkeypatch)
    assert sl.main(["--repo", "x/y"]) == 1
    err = capsys.readouterr().err
    assert "::error::[scheduler-liveness] pr-gate-stale-sweep.yml" in err
    assert "DESACTIVE" in err
    assert "2026-10-24T11:46:51Z" in err


def test_cli_disabled_follows_the_dead_severity_switch(monkeypatch, capsys):
    # Meme severite que DEAD : sur la jambe `push`, un etat chronique est nomme
    # en avertissement, pour la meme raison qu'au #18292 (un rouge sur presque
    # chaque commit masque les vrais rouges).
    _disabled_hourly_fleet(monkeypatch)
    assert sl.main(["--repo", "x/y", "--dead-exit", "warning"]) == 0
    err = capsys.readouterr().err
    assert "::warning::[scheduler-liveness] pr-gate-stale-sweep.yml" in err
    assert "1 DISABLED" in err


def test_cli_state_read_failure_is_green_and_named(monkeypatch, capsys):
    # Flotte saine mais lecture d'etat en 403 partout : l'organe ne doit ni
    # rougir ni forger un DISABLED/DEAD, et doit le dire.
    _stub_probe({o.workflow: (fresh(), "") for o in sl.REGISTRY}, monkeypatch)
    _stub_state({o.workflow: (None, "gh rc=1: HTTP 403") for o in sl.REGISTRY}, monkeypatch)
    assert sl.main(["--repo", "x/y"]) == 0
    captured = capsys.readouterr()
    assert "DISABLED" not in captured.out
    assert "::error::" not in captured.err
    assert "illisible" in captured.out


def test_cli_json_exposes_disabled_and_the_state(monkeypatch, capsys):
    _disabled_hourly_fleet(monkeypatch)
    import json

    assert sl.main(["--repo", "x/y", "--json"]) == 1
    payload = json.loads(capsys.readouterr().out)
    assert payload["disabled"] == 1 and payload["dead"] == 0
    row = next(o for o in payload["organs"] if o["workflow"] == HOURLY.workflow)
    assert row["verdict"] == "DISABLED"
    assert row["workflow_state"] == "disabled_manually"
    assert row["state_updated_at"] == "2026-10-24T11:46:51Z"


def test_disabled_does_not_move_a_threshold():
    # Le litmus anti-gaming : le nouveau verdict n'ajuste aucun seuil d'age.
    assert sl.DEAD_FACTOR == 4 and sl.DEAD_FLOOR_MIN == 90.0
    assert sl.LATE_FACTOR == 2


def test_waiter_starvation_advisory_is_registered():
    # Arbitrage (d) du coordinateur (c.6441695482) : la seconde des deux
    # advisories desactivees le 24/10 est desormais surveillee par l'organe,
    # avec la cadence reelle lue dans son fichier ('11,41 * * * *').
    entry = next(
        (o for o in sl.REGISTRY if o.workflow == "coursia-waiter-starvation-advisory.yml"),
        None,
    )
    assert entry is not None
    assert entry.declared_min == 30.0
    assert "11,41" in entry.note


def test_ci_overflow_controller_is_registered():
    """#22946, point 3 de la review ai-01 du 2026-10-27.

    Le controleur de debordement declarait '23,53' -- exactement le cron de
    linux-runner-version-pin-advisory.yml, que ce dernier avait choisi pour ne
    pas collisionner. Sa cadence devient horaire, minute 31 (hors :00/:30), et
    il entre dans le registre : son extinction se mesure au lieu de se
    supposer. La cadence declaree ici est celle du fichier -- les deux
    divergent silencieusement sinon, c'est la raison d'etre du registre.
    """
    entry = next(
        (o for o in sl.REGISTRY if o.workflow == "ci-overflow-controller.yml"),
        None,
    )
    assert entry is not None
    assert entry.declared_min == 60.0
    assert "31 * * * *" in entry.note


def test_dwell_du_controleur_depasse_la_cadence_du_cron():
    """Point Hermes du 2026-10-27 (12:53Z) : le dwell doit depasser la cadence.

    Le dwell n'est opposable que s'il depasse l'ecart entre deux passages. Le
    cron du controleur est horaire (60 min) : un dwell de 30 min ne pouvait
    JAMAIS bloquer une bascule -- deux passages consecutifs sont toujours a
    plus de 30 min -- et l'anti-oscillation etait un decor, pas une
    protection. La coherence se mesure : dwell > cadence.
    """
    import ci_overflow_controller as ctl

    entry = next(
        (o for o in sl.REGISTRY if o.workflow == "ci-overflow-controller.yml"),
        None,
    )
    assert entry is not None
    assert ctl.DEFAULT_DWELL_MINUTES > entry.declared_min
