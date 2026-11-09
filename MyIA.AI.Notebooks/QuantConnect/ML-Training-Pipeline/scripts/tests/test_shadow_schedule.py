"""Tests for shadow_schedule.py -- cadence des passages mensuels du suivi en ombre (#18923).

Etape 3 : le plan ne decide que du QUAND. Les tests epinglent la date de premiere seance,
l'ordre de la marche (locales gratuites, puis QC espacees), le determinisme, la due-mensuelle
deja portee par ``shadow_replay.due``, le caractere lecture-seule du planificateur, et les
deux refus (etat invalide, espacement hors budget MCP).
"""

from __future__ import annotations

import datetime as dt
import json
from pathlib import Path
from zoneinfo import ZoneInfo

import pytest

import shadow_schedule as ss
from shadow_replay import append_row, freeze, load_registry, save_registry

START = dt.datetime(2026, 11, 2, 9, 17, tzinfo=ZoneInfo("Europe/Paris"))


def _registry(tmp_path: Path, specs: list[tuple[str, str, str]]) -> Path:
    """Registre valide : specs = (id, kind, frozen_on), SHA factice stable."""
    path = tmp_path / "registry.json"
    candidates = []
    for cid, kind, frozen_on in specs:
        entry = freeze(candidates, id=cid, kind=kind, sha="a" * 40, frozen_on=frozen_on,
                       entrypoint="mod.py:run" if kind == "local" else "proj/qc:12345",
                       params={}, fee_model="5bps notional")
        assert entry
    save_registry(path, candidates)
    return path


def _csv(tmp_path: Path) -> Path:
    return tmp_path / "passes.csv"


def test_first_session_of_month_skips_weekend():
    # 2026-11-01 est un dimanche, 2027-05-01 un samedi ; 2027-01-01 un vendredi, 2028-02-01 un mardi.
    assert ss.first_session_of_month(2026, 11) == dt.date(2026, 11, 2)
    assert ss.first_session_of_month(2027, 1) == dt.date(2027, 1, 1)
    assert ss.first_session_of_month(2027, 5) == dt.date(2027, 5, 3)
    assert ss.first_session_of_month(2028, 2) == dt.date(2028, 2, 1)


def test_pass_date_for_moves_to_today_once_the_session_passed():
    # Le 2026-11-01 (dimanche), la seance est le lendemain ; le 15, elle est passee.
    assert ss.pass_date_for(dt.date(2026, 11, 1)) == dt.date(2026, 11, 2)
    assert ss.pass_date_for(dt.date(2026, 11, 15)) == dt.date(2026, 11, 15)


def test_qc_rate_spreads_calls_over_the_interval():
    assert ss.qc_rate(10) == pytest.approx(0.5)
    assert ss.qc_rate(0) == float("inf")


def test_plan_orders_locals_then_qc_and_spaces_passages(tmp_path):
    reg = _registry(tmp_path, [("qcB", "qc", "2026-10-05"),
                               ("loc", "local", "2026-10-06"),
                               ("qcA", "qc", "2026-10-04")])
    plan = ss.plan_pass(reg, _csv(tmp_path), "2026-11-02", START, min_interval_min=10)
    assert plan["n_due"] == 3 and plan["n_local"] == 1 and plan["n_qc"] == 2
    assert [s["kind"] for s in plan["steps"]] == [
        "replay-local", "plan-qc", "qc-passage", "ingest-qc", "qc-passage", "ingest-qc"]
    # qcA gelee avant qcB : ordre frozen_on puis id.
    passages = [s for s in plan["steps"] if s["kind"] == "qc-passage"]
    assert [s["candidate"] for s in passages] == ["qcA", "qcB"]
    # Deux passages QC espaces d'au moins l'intervalle, ingestion juste apres chacun.
    slots = [dt.datetime.fromisoformat(s["slot"]) for s in plan["steps"]]
    assert slots == [START,
                     START + dt.timedelta(minutes=1),
                     START + dt.timedelta(minutes=2),
                     START + dt.timedelta(minutes=12),
                     START + dt.timedelta(minutes=13),
                     START + dt.timedelta(minutes=23)]
    assert passages[0]["qc_calls"] == ss.QC_CALLS_PER_PASS
    assert passages[0]["qc_project"] == 12345
    assert plan["qc_calls_total"] == 2 * ss.QC_CALLS_PER_PASS


def test_plan_is_deterministic(tmp_path):
    reg = _registry(tmp_path, [("qcA", "qc", "2026-10-05"), ("loc", "local", "2026-10-06")])
    a = ss.plan_pass(reg, _csv(tmp_path), "2026-11-02", START)
    b = ss.plan_pass(reg, _csv(tmp_path), "2026-11-02", START)
    assert json.dumps(a, sort_keys=True) == json.dumps(b, sort_keys=True)


def test_plan_skips_the_already_replayed_and_the_just_frozen(tmp_path):
    reg = _registry(tmp_path, [("done", "qc", "2026-10-01"),
                               ("todo", "qc", "2026-10-02"),
                               ("jeune", "qc", "2026-11-02")])
    csv = _csv(tmp_path)
    c = {e["id"]: e for e in load_registry(reg)}
    append_row(csv, {"candidate": "done", "sha": c["done"]["sha"],
                     "frozen_on": "2026-10-01", "pass_date": "2026-11-02",
                     "period_end": "2026-11-02", "n_days": "30",
                     "sharpe_net": "0.1", "cagr": "0.02", "max_drawdown": "-0.05",
                     "turnover": "0.5", "fees": "0.001", "fee_model": "5bps notional"})
    plan = ss.plan_pass(reg, csv, "2026-11-02", START)
    ids = [s["candidate"] for s in plan["steps"] if s["kind"] == "qc-passage"]
    # "done" a deja sa ligne de novembre ; "jeune" est gelee le jour du passage (strict avant).
    assert ids == ["todo"]


def test_plan_writes_neither_registry_nor_csv(tmp_path):
    reg = _registry(tmp_path, [("qcA", "qc", "2026-10-05")])
    csv = _csv(tmp_path)
    before_reg = reg.read_text(encoding="utf-8")
    ss.plan_pass(reg, csv, "2026-11-02", START)
    assert reg.read_text(encoding="utf-8") == before_reg
    assert not csv.exists()


def test_plan_refuses_an_invalid_state(tmp_path):
    reg = _registry(tmp_path, [("qcA", "qc", "2026-10-05")])
    tampered = json.loads(reg.read_text(encoding="utf-8"))
    tampered["candidates"][0]["fee_model"] = "changed after freezing"
    reg.write_text(json.dumps(tampered), encoding="utf-8")
    with pytest.raises(ValueError, match="invalide"):
        ss.plan_pass(reg, _csv(tmp_path), "2026-11-02", START)


def test_plan_refuses_a_spacing_over_budget(tmp_path):
    reg = _registry(tmp_path, [("qcA", "qc", "2026-10-05")])
    with pytest.raises(ValueError, match="budget"):
        ss.plan_pass(reg, _csv(tmp_path), "2026-11-02", START, min_interval_min=0)


def test_main_end_to_end_json(tmp_path, capsys):
    reg = _registry(tmp_path, [("qcA", "qc", "2026-10-05"), ("loc", "local", "2026-10-06")])
    rc = ss.main(["--registry", str(reg), "--csv", str(_csv(tmp_path)),
                  "plan", "--on", "2026-11-02", "--json"])
    assert rc == 0
    plan = json.loads(capsys.readouterr().out)
    assert plan["pass_date"] == "2026-11-02"
    assert plan["n_due"] == 2 and plan["n_local"] == 1 and plan["n_qc"] == 1
    assert plan["steps"][0]["command"][0:2] == ["python", "scripts/shadow_replay.py"]
