#!/usr/bin/env python3
"""test_release_parked_runs.py — contrôles positifs du déblocage des runs garés.

Couvre scripts/ci/release_parked_runs.py (issue #17668, port du sondage borné
de #17634 partagé entre catalog-cron.yml et qc-research-monitor.yml) :
  - la course au release : les runs du head n'existent pas à la 1re sonde ->
    la boucle re-sonde et casse au compte stable non nul (2e/3e sonde)
  - filtrage : seuls les runs `action_required` du head courant comptent
  - staggering + plafond RELEASE_CEILING : le run au-delà est différé SANS
    tentative d'approbation
  - approbation refusée -> warning, comptée, jamais de rouge (exit 0)
  - aucune approbation quand la fenêtre de sonde reste vide

Usage :
    pytest tests/test_release_parked_runs.py -v
"""

from __future__ import annotations

import importlib.util
import json
import sys
import types
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / "scripts" / "ci" / "release_parked_runs.py"
HEAD = "abc123def"


def _load(monkeypatch, rows_by_probe, approve_ok=None):
    spec = importlib.util.spec_from_file_location("rpr", SCRIPT)
    rpr = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(rpr)

    state = {"list": 0, "approves": [], "settle_sleeps": 0, "stagger_sleeps": 0}

    def fake_run(cmd, capture_output=True, text=True, **kw):
        if cmd[0] == "git":
            assert cmd[:2] == ["git", "rev-parse"]
            return types.SimpleNamespace(returncode=0, stdout=HEAD + "\n", stderr="")
        if cmd[:2] == ["gh", "run"]:
            state["list"] += 1
            rows = rows_by_probe(state["list"])
            return types.SimpleNamespace(returncode=0, stdout=json.dumps(rows), stderr="")
        if cmd[:2] == ["gh", "api"]:
            assert cmd[2:4] == ["-X", "POST"]
            state["approves"].append(cmd[-1])
            ok = approve_ok(cmd[-1]) if approve_ok else True
            return types.SimpleNamespace(returncode=0 if ok else 1, stdout="{}", stderr="")
        raise AssertionError(f"commande inattendue : {cmd}")

    # stubs injectes sur l'instance du module UNIQUEMENT : `rpr.subprocess` et
    # `rpr.time` sont les singletons globaux -- les muter directement pollue
    # tout le processus pytest (84 tests voisins touches au 1er passage, les
    # fakes interceptant leurs appels git).
    rpr.subprocess = types.SimpleNamespace(run=fake_run)

    def fake_sleep(seconds):
        # les sleeps de sonde sont >= 1 s, le stagger entre approbations vaut
        # la valeur configuree (0 dans ces tests)
        if seconds >= 1:
            state["settle_sleeps"] += 1
        else:
            state["stagger_sleeps"] += 1

    rpr.time = types.SimpleNamespace(sleep=fake_sleep)

    monkeypatch.setenv("GITHUB_REPOSITORY", "jsboige/CoursIA")
    monkeypatch.setenv("BRANCH", "chore/test-pending")
    monkeypatch.setenv("RELEASE_SETTLE_POLLS", "8")
    monkeypatch.setenv("RELEASE_SETTLE_SECONDS", "1")
    monkeypatch.setenv("RELEASE_STAGGER_SECONDS", "0")
    monkeypatch.setenv("RELEASE_CEILING", "40")
    monkeypatch.setenv("GH_TOKEN", "fake")

    return rpr, state


def _run_main(rpr, capsys, monkeypatch):
    monkeypatch.setattr(sys, "argv", ["release_parked_runs.py", "--tag", "T"])
    rc = rpr.main()
    return rc, capsys.readouterr().out


def _rows(*ids):
    return [
        {"databaseId": i, "headSha": HEAD, "conclusion": "action_required",
         "workflowName": f"w{i}"}
        for i in ids
    ]


def test_course_au_release_sondage_borne(monkeypatch, capsys):
    """Runs apparaissant à la 2e sonde : casse au compte stable, puis release."""
    rows_by_probe = lambda n: [] if n == 1 else _rows(101, 102) + [
        {"databaseId": 999, "headSha": "autre-tete", "conclusion": "action_required",
         "workflowName": "bruit-autre-branche"},
        {"databaseId": 101, "headSha": HEAD, "conclusion": "success",
         "workflowName": "deja-execute"},
    ]
    rpr, state = _load(monkeypatch, rows_by_probe)
    rc, out = _run_main(rpr, capsys, monkeypatch)

    assert rc == 0
    # 1re sonde vide, 2e sonde 2 runs, 3e sonde stable -> break
    assert state["list"] == 3
    # seuls les 2 runs action_required du head sont approuves
    assert state["approves"] == [
        "repos/jsboige/CoursIA/actions/runs/101/approve",
        "repos/jsboige/CoursIA/actions/runs/102/approve",
    ]
    assert "released 2 run(s), refused 0, deferred 0" in out
    assert "::warning" not in out


def test_plafond_differe_sans_tenter_lapprobation(monkeypatch, capsys):
    """RELEASE_CEILING=2 sur 3 runs : le 3e est différé, pas d'appel API pour lui."""
    rows_by_probe = lambda n: [] if n == 1 else _rows(201, 202, 203)
    rpr, state = _load(monkeypatch, rows_by_probe)
    monkeypatch.setenv("RELEASE_CEILING", "2")
    rc, out = _run_main(rpr, capsys, monkeypatch)

    assert rc == 0
    assert state["approves"] == [
        "repos/jsboige/CoursIA/actions/runs/201/approve",
        "repos/jsboige/CoursIA/actions/runs/202/approve",
    ]
    assert "released 2 run(s), refused 0, deferred 1" in out
    assert "left parked by the ceiling of 2" in out


def test_approbation_refusee_warning_pas_rouge(monkeypatch, capsys):
    """Un approve refusé est compté + warning, le script reste exit 0."""
    rows_by_probe = lambda n: [] if n == 1 else _rows(301)
    rpr, state = _load(
        monkeypatch, rows_by_probe,
        approve_ok=lambda url: url.endswith("/runs/301/approve") is False,
    )
    rc, out = _run_main(rpr, capsys, monkeypatch)

    assert rc == 0
    assert state["approves"], "l'approbation doit être tentée"
    assert "released 0 run(s), refused 1, deferred 0" in out
    assert "could not approve run 301" in out
    assert "delivery PR will stay BLOCKED" in out


def test_fenetre_vide_aucune_approbation(monkeypatch, capsys):
    """Aucun run garé après toutes les sondes : notice + exit 0, zéro appel."""
    rpr, state = _load(monkeypatch, lambda n: [])
    monkeypatch.setenv("RELEASE_SETTLE_POLLS", "3")
    rc, out = _run_main(rpr, capsys, monkeypatch)

    assert rc == 0
    assert state["list"] == 3
    assert state["approves"] == []
    assert "no parked run at this head" in out
