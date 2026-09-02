from __future__ import annotations

import sys
from datetime import datetime, timedelta, timezone
from pathlib import Path

CI_DIR = Path(__file__).resolve().parents[1] / "ci"
sys.path.insert(0, str(CI_DIR))

import check_runner_starvation as rs  # noqa: E402


def inventory(online: list[str], offline: list[str] | None = None) -> rs.RunnerInventory:
    return rs.RunnerInventory(online=online, offline=offline or [])


def job(age_min: float, workflow: str = "Guard A", number: int = 1) -> rs.JobRow:
    return rs.JobRow(workflow=workflow, run_number=number, run_id=1000 + number,
                     job_name="guard", status="queued", age_min=age_min)


def progress(workflow: str = "Guard B", number: int = 2) -> rs.JobRow:
    return rs.JobRow(workflow=workflow, run_number=number, run_id=2000 + number,
                     job_name="guard", status="in_progress", age_min=1.0)


# --- EXTINCTION (predicat direct, via inventaire) ---------------------------

def test_extinction_zero_online_runner_is_error():
    # Controle positif de l'incident 2026-09-02 : superviseur mort -> tous les
    # slots offline -> la signature exacte vue ce matin-la (4 slots .offline).
    inv = inventory([], ["myia-po-2024-linux-docker-1", "myia-po-2024-linux-docker-2",
                         "myia-po-2024-linux-docker-3", "myia-po-2024-linux-docker-4"])
    v = rs.evaluate(inv, rs.Starvation(), warn_floor=2)
    assert v.status == "ERROR"
    assert any("EXTINCTION" in e for e in v.errors)
    assert any("myia-po-2024-linux-docker-1" in e for e in v.errors)


def test_healthy_inventory_is_ok():
    inv = inventory(["r1", "r2", "r3", "r4"])
    v = rs.evaluate(inv, rs.Starvation(in_progress=[progress()]), warn_floor=2)
    assert v.status == "OK" and not v.errors and not v.warnings


def test_partial_loss_warns_but_does_not_error():
    inv = inventory(["r1"], ["r2", "r3"])
    v = rs.evaluate(inv, rs.Starvation(), warn_floor=2)
    assert v.status == "OK"
    assert len(v.warnings) == 1 and "perte partielle" in v.warnings[0]


# --- STARVATION (predicat symptome, sans secret) -----------------------------

def test_starved_queue_with_no_progress_is_error():
    st = rs.Starvation(starved=[job(35), job(22, workflow="Guard C", number=3)])
    v = rs.evaluate(inventory(["r1", "r2"]), st, warn_floor=2)
    assert v.status == "ERROR"
    assert any("STARVATION" in e for e in v.errors)
    assert any("35 min" in e for e in v.errors)


def test_deep_queue_draining_is_ok():
    # Le garde anti-faux-positif du design : une file PROFONDE qui drainne
    # (slots busy) est un manque de capacite, pas une extinction. Rendre ce
    # cas rouge ferait un advisory rouge permanent = un organe eteint.
    st = rs.Starvation(starved=[job(40), job(28), job(19)], in_progress=[progress(), progress()])
    v = rs.evaluate(inventory(["r1", "r2"]), st, warn_floor=2)
    assert v.status == "OK" and not v.errors


def test_starved_below_threshold_is_ignored():
    st = rs.Starvation(starved=[], in_progress=[])
    v = rs.evaluate(inventory(["r1", "r2"]), st, warn_floor=2)
    assert v.status == "OK"


# --- DEGRADATION sans PAT ----------------------------------------------------

def test_inventory_unavailable_degrades_to_symptom_only():
    inv = rs.InventoryUnavailable(reason="pas de PAT")
    v = rs.evaluate(inv, rs.Starvation(in_progress=[progress()]), warn_floor=2)
    assert v.status == "OK"
    assert any("inventaire non lisible" in n for n in v.notes)


def test_inventory_unavailable_plus_starvation_still_errors():
    inv = rs.InventoryUnavailable(reason="pas de PAT")
    v = rs.evaluate(inv, rs.Starvation(starved=[job(30)]), warn_floor=2)
    assert v.status == "ERROR"
    assert any("STARVATION" in e for e in v.errors)


# --- Parsing ISO et filtres de fetch -----------------------------------------

def test_parse_iso_handles_none_and_garbage():
    assert rs._parse_iso(None) is None
    assert rs._parse_iso("") is None
    assert rs._parse_iso("not-a-date") is None
    parsed = rs._parse_iso("2026-09-02T08:00:00Z")
    assert parsed is not None and parsed.tzinfo is not None


def _runs_payload(status: str, created: datetime) -> dict:
    return {"workflow_runs": [
        {"id": 555, "name": "Guard A", "run_number": 9, "created_at": created.isoformat()}
    ]}


def test_fetch_starvation_filters_by_label_and_status(monkeypatch):
    now = datetime(2026, 9, 2, 12, 0, tzinfo=timezone.utc)
    created = now - timedelta(minutes=40)
    calls: list[str] = []

    def fake_gh(args: list[str], token: str | None = None):
        calls.append(args[0])
        if args[0].startswith("repos/jsboige/CoursIA/actions/runs?status=queued"):
            return _runs_payload("queued", created)
        if args[0].startswith("repos/jsboige/CoursIA/actions/runs?status=in_progress"):
            return {"workflow_runs": []}
        if "/jobs" in args[0]:
            # Deux jobs : un sur le label (affame), un hors label (ignore).
            return {"jobs": [
                {"name": "guard-on-label", "status": "queued",
                 "labels": ["self-hosted", "coursia-linux"]},
                {"name": "guard-ubuntu", "status": "queued",
                 "labels": ["ubuntu-latest"]},
            ]}
        return None

    monkeypatch.setattr(rs, "_gh_json", fake_gh)
    st = rs.fetch_starvation("jsboige/CoursIA", "coursia-linux", 15.0, 30, now=now)
    assert len(st.starved) == 1
    assert st.starved[0].job_name == "guard-on-label"
    assert st.starved[0].age_min is not None and st.starved[0].age_min > 39


def test_fetch_inventory_sorts_online_offline(monkeypatch):
    def fake_gh(args: list[str], token: str | None = None):
        return {"runners": [
            {"name": "r-live", "status": "online",
             "labels": [{"name": "coursia-linux"}]},
            {"name": "r-dead", "status": "offline",
             "labels": [{"name": "coursia-linux"}]},
            {"name": "r-other", "status": "online",
             "labels": [{"name": "windows"}]},
        ]}

    monkeypatch.setattr(rs, "_gh_json", fake_gh)
    inv = rs.fetch_inventory("jsboige/CoursIA", "coursia-linux", token="pat")
    assert inv.available
    assert inv.online == ["r-live"] and inv.offline == ["r-dead"]


def test_fetch_inventory_auth_failure_returns_unavailable(monkeypatch):
    monkeypatch.setattr(rs, "_gh_json", lambda args, token=None: None)
    inv = rs.fetch_inventory("jsboige/CoursIA", "coursia-linux", token=None)
    assert not inv.available
