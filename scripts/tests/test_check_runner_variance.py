#!/usr/bin/env python3
"""Tests offline de la garde de variance runners (#15574 item 4).

L'analyse est pure (dictionnaires -> verdicts) : chaque predicat du mandat
d'arbitrage (c.5916600342) a son controle, plus les gardes anti-faux-positif
(pool petit / mediane trop basse / raza 24 h).
"""

from __future__ import annotations

import json
import shutil
import subprocess
import sys
import tempfile
from datetime import datetime, timedelta, timezone
from pathlib import Path

import pytest

# Le module vit dans scripts/ci (convention scripts/tests : cf
# test_check_absorbed_check_run_identity.py ; scripts-tests.yml collecte
# scripts/tests, pas scripts/ci -- relecture ai-01 e04d4e3f3b).
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "ci"))

from check_runner_variance import (  # noqa: E402
    evaluate_signals,
    find_slow_instances,
    merge_log,
    next_signaled,
    parse_log_body,
    render_log_body,
    select_new_signals,
)

REPO_ROOT = Path(__file__).resolve().parents[2]
WORKFLOW = REPO_ROOT / ".github" / "workflows" / "runner-variance-guard.yml"
JQ_PROGRAM = REPO_ROOT / "scripts" / "ci" / "runner_variance_signal.jq"

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
    """Le log ET l'etat de signalement survivent au passage par le corps."""
    fenetre = _run([_job("tests", f"runner-G-{i}", 7.0 if i == 2 else 2.0) for i in range(4)])
    log = merge_log([], find_slow_instances([fenetre]), NOW)
    body = "Garde de variance -- le bloc suivant est l'etat.\n\n" \
        + render_log_body(log, {"runner-G-2": 1})
    entries, signaled = parse_log_body(body)
    assert entries == log
    assert signaled == {"runner-G-2": 1}
    assert evaluate_signals(entries) == []  # 1 hit seulement
    # le body sans bloc rend un log vide, pas une erreur
    assert parse_log_body("rien ici") == ([], {})
    # ancien format (sans cle signaled) : etat vide, entrees lisibles
    old_format = "```" + "variance-guard-log\n" \
        + json.dumps({"entries": log}) + "\n```"
    entries_old, signaled_old = parse_log_body(old_format)
    assert entries_old == log and signaled_old == {}


def test_deux_runners_distincts_deux_hotes():
    """Le signalement nomme le runner ET son hote (host_of du sibling)."""
    jobs = [_job("tests", f"hostX-docker-{i}", 7.0 if i == 9 else 2.0) for i in range(10)]
    log = merge_log([], find_slow_instances([_run(jobs)]), NOW)
    log = merge_log(log, find_slow_instances([_run(jobs)]), NOW + timedelta(minutes=5))
    signals = evaluate_signals(log)
    assert len(signals) == 1
    assert signals[0]["runner"] == "hostX-docker-9"
    assert signals[0]["host"] == "hostX-docker"  # host_of: prefixe avant le suffixe de slot


def test_resignal_seulement_si_compte_croit():
    """Un runner deja signale n'est re-poste que si son compte AUGMENTE.

    Sans ce delta, le garde posterait le meme commentaire toutes les 2 h
    tant que les instances restent dans la fenetre 24 h (relecture ai-01
    e04d4e3f3b).
    """
    jobs = [_job("tests", f"runner-H-{i}", 7.0 if i == 1 else 2.0) for i in range(4)]
    log = merge_log([], find_slow_instances([_run(jobs)]), NOW - timedelta(hours=2))
    log = merge_log(log, find_slow_instances([_run(jobs)]), NOW)
    signals = evaluate_signals(log)
    assert [s["hit_count"] for s in signals] == [2]
    # premier passage : tout signal nouveau
    assert len(select_new_signals(signals, {})) == 1
    # passages suivants a compte constant : rien de nouveau
    state = next_signaled(signals)
    assert select_new_signals(signals, state) == []
    # une TROISIEME instance arrive : le compte croit, on re-signal
    log = merge_log(log, find_slow_instances([_run(jobs)]), NOW + timedelta(minutes=30))
    grown = evaluate_signals(log)
    assert [s["hit_count"] for s in grown] == [3]
    fresh = select_new_signals(grown, state)
    assert len(fresh) == 1 and fresh[0]["hit_count"] == 3


def test_chute_sous_seuil_reset_l_etat():
    """Le runner qui retombe sous min_hits perd son etat : re-accumuler le re-signal."""
    jobs = [_job("tests", f"runner-K-{i}", 7.0 if i == 1 else 2.0) for i in range(4)]
    log = merge_log([], find_slow_instances([_run(jobs)]), NOW - timedelta(hours=2))
    log = merge_log(log, find_slow_instances([_run(jobs)]), NOW)
    state = next_signaled(evaluate_signals(log))
    # 25 h plus tard, les instances ont expire : le log est vide
    log = merge_log(log, {}, NOW + timedelta(hours=25, minutes=1))
    assert evaluate_signals(log) == []
    assert next_signaled([]) == {}  # l'etat ne garde pas un runner sorti
    # re-accumulation complete : signal a nouveau NOUVEAU
    log = merge_log(log, find_slow_instances([_run(jobs)]), NOW + timedelta(hours=26))
    log = merge_log(log, find_slow_instances([_run(jobs)]), NOW + timedelta(hours=26, minutes=30))
    signals = evaluate_signals(log)
    assert len(select_new_signals(signals, {})) == 1


def test_workflow_steps_passent_bash_n():
    """Regression du rouge e04d4e3f3b : chaque run: du workflow doit etre
    analysable par bash. Le step fautif declarait un programme jq entre
    apostrophes contenant l\\'hote : bash -n rendait unexpected EOF, et le
    workflow ne rougissait qu'au PREMIER vrai signalement."""
    import yaml
    wf = yaml.safe_load(WORKFLOW.read_text(encoding="utf-8"))
    steps = wf["jobs"]["measure-and-signal"]["steps"]
    tmp = tempfile.mkdtemp()
    try:
        for step in steps:
            if "run" not in step:
                continue
            script = Path(tmp) / "step.sh"
            script.write_text(step["run"], encoding="utf-8", newline="\n")
            # nom RELATIF + cwd : le bash MSYS local ne voit pas les chemins
            # absolus de %TEMP% (C:/... inclus) -- la forme relative passe
            # partout, local comme runner CI.
            proc = subprocess.run(["bash", "-n", "step.sh"],
                                  capture_output=True, text=True,
                                  encoding="utf-8", errors="replace", cwd=tmp)
            assert proc.returncode == 0, (
                f"bash -n ECHOUE sur le step {step.get('name')!r} : "
                f"{proc.stderr.strip()[:200]}")
    finally:
        # ignore_errors : sous pytest/Windows, un verrou transitoire
        # (WinError 32) peut survivre un instant a la mort du bash dont
        # c'etait le cwd -- le contenu est jetable, pas la peine d'echouer la
        # garde pour un menage refuse.
        shutil.rmtree(tmp, ignore_errors=True)


def test_programme_jq_en_tete_puis_liste():
    """Le rendu jq : un en-tete PAR SIGNAL, puis la liste des instances
    join(\\n) -- l'ancienne forme repetait l'en-tete complet par instance."""
    if not shutil.which("jq"):
        pytest.skip("jq absent de la machine de test")
    verdict = {
        "signals": [{
            "runner": "hostX-docker-9", "host": "hostX-docker", "hit_count": 2,
            "hits": [
                {"ts": "t1", "job": "CI :: tests", "duration_minutes": 7.0,
                 "pool_median_minutes": 2.0, "ratio": 3.5, "conclusion": "success"},
                {"ts": "t2", "job": "CI :: tests", "duration_minutes": 8.0,
                 "pool_median_minutes": 2.0, "ratio": 4.0, "conclusion": "failure"},
            ],
        }],
    }
    proc = subprocess.run(
        ["jq", "-r", "-f", str(JQ_PROGRAM)],
        input=json.dumps(verdict), capture_output=True, text=True,
        encoding="utf-8", errors="replace")
    assert proc.returncode == 0, proc.stderr
    out = proc.stdout
    assert out.count("## SIGNAL") == 1  # en-tete UNE fois
    assert out.count("- t1 --") == 1 and out.count("- t2 --") == 1  # liste join
    assert "hote hostX-docker" in out


if __name__ == "__main__":
    for name, fn in sorted(globals().items()):
        if name.startswith("test_") and callable(fn):
            try:
                fn()
            except pytest.skip.Exception:
                print(f"SKIP {name}")
                continue
            print(f"PASS {name}")
    print("ALL_TESTS_PASSED")
