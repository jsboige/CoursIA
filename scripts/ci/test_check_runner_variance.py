#!/usr/bin/env python3
"""Tests offline de la garde de variance runners (#15574 item 4).

L'analyse est pure (dictionnaires -> verdicts) : chaque predicat du mandat
d'arbitrage (c.5916600342) a son controle, plus les gardes anti-faux-positif
(pool petit / mediane trop basse / raza 24 h).
"""

from __future__ import annotations

import json
import sys
from datetime import datetime, timedelta, timezone
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from check_runner_variance import (  # noqa: E402
    evaluate_signals,
    find_slow_instances,
    merge_log,
    parse_log_body,
    render_log_body,
)

NOW = datetime(2026, 9, 30, 18, 0, 0, tzinfo=timezone.utc)
BASE = datetime(2026, 9, 30, 17, 0, 0, tzinfo=timezone.utc)


def _job(name: str, runner: str | None, minutes: float, conclusion: str = "success") -> dict:
    started = BASE
    return {
        "name": name,
        "status": "completed",
        "conclusion": conclusion,
        "started_at": started.strftime("%Y-%m-%dT%H:%M:%SZ"),
        "completed_at": (started + timedelta(minutes=minutes)).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "runner_name": runner,
    }


def _run(jobs: list[dict]) -> dict:
    return {"name": "CI", "jobs": jobs}


def test_signal_deux_instances_sur_24h():
    """Le critere exact du mandat : >= 2 fois sur 24 h -> signal."""
    fenetre1 = _run([_job("tests", f"runner-A-{i}", 7.0 if i == 1 else 2.0) for i in range(4)])
    slow1 = find_slow_instances([fenetre1])
    assert "runner-A-1" in slow1

    log = merge_log([], slow1, NOW - timedelta(hours=2))
    # fenetre suivante, meme runner a nouveau 3x la mediane
    fenetre2 = _run([_job("tests", f"runner-A-{i}", 7.5 if i == 1 else 2.0) for i in range(4)])
    slow2 = find_slow_instances([fenetre2])
    log = merge_log(log, slow2, NOW)
    signals = evaluate_signals(log)
    assert len(signals) == 1
    assert signals[0]["runner"] == "runner-A-1"
    assert signals[0]["hit_count"] == 2


def test_une_seule_instance_ne_signal_pas():
    fenetre = _run([_job("tests", f"runner-B-{i}", 9.0 if i == 3 else 2.0) for i in range(4)])
    log = merge_log([], find_slow_instances([fenetre]), NOW)
    assert evaluate_signals(log) == []


def test_pool_trop_petit_exclu():
    """3 instances = sous min_pool=4 : pas de mediane, pas de signal."""
    fenetre = _run([_job("tests", f"runner-C-{i}", 30.0 if i == 0 else 2.0) for i in range(3)])
    assert find_slow_instances([fenetre]) == {}


def test_mediane_trop_basse_exclue():
    """Tripler 8 secondes de bruit n'est pas un signal."""
    fenetre = _run([_job("lint", f"runner-D-{i}", 0.4 if i == 2 else 0.1) for i in range(4)])
    assert find_slow_instances([fenetre]) == {}


def test_job_timeout_compte_comme_instance_lente():
    """Le job tue par timeout-minutes est l'instance lente canonique (#15574)."""
    fenetre = _run([_job("tests", f"runner-E-{i}", 15.0 if i == 0 else 3.0,
                         conclusion="failure") if i == 0
                    else _job("tests", f"runner-E-{i}", 3.0) for i in range(4)])
    slow = find_slow_instances([fenetre])
    assert "runner-E-0" in slow
    assert slow["runner-E-0"][0]["conclusion"] == "failure"


def test_log_raza_24h():
    """Une entree de 25 h sort du log : son hit ne compte plus."""
    lent = _run([_job("tests", f"runner-F-{i}", 7.0 if i == 1 else 2.0) for i in range(4)])
    log = merge_log([], find_slow_instances([lent]), NOW - timedelta(hours=25))
    log = merge_log(log, {}, NOW)
    assert evaluate_signals(log) == []


def test_corps_issue_roundtrip():
    """Le log survit au passage par le corps de l'issue."""
    fenetre = _run([_job("tests", f"runner-G-{i}", 7.0 if i == 2 else 2.0) for i in range(4)])
    log = merge_log([], find_slow_instances([fenetre]), NOW)
    body = "Garde de variance -- le bloc suivant est l'etat.\n\n" + render_log_body(log)
    relu = parse_log_body(body)
    assert relu == log
    assert evaluate_signals(relu) == []  # 1 hit seulement
    # le body sans bloc rend un log vide, pas une erreur
    assert parse_log_body("rien ici") == []


def test_deux_runners_distincts_deux_hotes():
    """Le signalement nomme le runner ET son hote (host_of du sibling)."""
    jobs = [_job("tests", f"hostX-docker-{i}", 7.0 if i == 9 else 2.0) for i in range(10)]
    log = merge_log([], find_slow_instances([_run(jobs)]), NOW)
    log = merge_log(log, find_slow_instances([_run(jobs)]), NOW + timedelta(minutes=5))
    signals = evaluate_signals(log)
    assert len(signals) == 1
    assert signals[0]["runner"] == "hostX-docker-9"
    assert signals[0]["host"] == "hostX-docker"  # host_of: prefixe avant le suffixe de slot


if __name__ == "__main__":
    for name, fn in sorted(globals().items()):
        if name.startswith("test_") and callable(fn):
            fn()
            print(f"PASS {name}")
    print("ALL_TESTS_PASSED")
