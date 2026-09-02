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
    st = rs.fetch_starvation("jsboige/CoursIA", "coursia-linux", 15.0, now=now)
    assert len(st.starved) == 1
    assert st.starved[0].job_name == "guard-on-label"
    assert st.starved[0].age_min is not None and st.starved[0].age_min > 39


# --- FENETRE D'EXAMEN (correctif fail-open, signalement po-2025 2026-09-02) --

def _run_row(rid: int, age_min: float, now: datetime, name: str = "Guard X"):
    return {"id": rid, "name": name, "run_number": rid,
            "created_at": (now - timedelta(minutes=age_min)).isoformat()}


def test_starvation_beyond_first_page_is_seen(monkeypatch):
    """Le test de falsification du fail-open : l'affame vit en page 2, la
    page 1 n'a que des runs trop jeunes pour starver. L'ancien cap=30 lisait
    exactement la page 1 -> 0 affame, mesure du jour : 34 runs >15 min en
    pages 6-7, tous invisibles."""
    now = datetime(2026, 9, 2, 12, 0, tzinfo=timezone.utc)

    def fake_gh(args: list[str], token: str | None = None):
        url = args[0]
        if "status=queued" in url:
            # Pas de substring match : "page=1" est un prefixe de
            # "per_page=100" -- parser le numero de page reellement demande.
            page = int(url.rsplit("page=", 1)[1])
            if page == 1:
                # Une vraie page 1 porte RUNS_PAGE_SIZE runs, tous trop
                # jeunes pour starver -- c'est le piege du fail-open.
                return {"total_count": 102, "workflow_runs": [
                    _run_row(rid, 0.1 * (rid % 100), now) for rid in range(rs.RUNS_PAGE_SIZE)
                ]}
            return {"total_count": 102, "workflow_runs": [
                _run_row(160, 20.0, now), _run_row(161, 21.0, now)
            ]}
        if "status=in_progress" in url:
            return {"total_count": 0, "workflow_runs": []}
        if "/jobs" in url:
            return {"jobs": [
                {"name": "guard", "status": "queued",
                 "labels": ["self-hosted", "coursia-linux"]},
            ]}
        return None

    monkeypatch.setattr(rs, "_gh_json", fake_gh)
    st = rs.fetch_starvation("jsboige/CoursIA", "coursia-linux", 15.0, now=now)
    # Page 2 examinee : les deux affames (20 et 21 min) sont VUS.
    assert len(st.starved) == 2
    assert all(r.age_min is not None and r.age_min >= 20 for r in st.starved)
    assert st.unexamined == {}


def test_pagination_stops_when_page_older_than_window(monkeypatch):
    """Le plus recent de la page 1 depasse deja la fenetre : aucun run
    examine, aucune deuxieme page demandee, le reliquat est compte comme
    classe ABANDONNEE (information, pas rouge)."""
    now = datetime(2026, 9, 2, 12, 0, tzinfo=timezone.utc)
    pages_fetched: list[int] = []

    def fake_gh(args: list[str], token: str | None = None):
        url = args[0]
        if "status=queued" in url:
            pages_fetched.append(1 if "page=1" in url else 2)
            # total_count annonce 20576 min d'abandonnes (mesure du jour).
            return {"total_count": 188, "workflow_runs": [
                _run_row(70, 20576.0, now), _run_row(71, 20600.0, now),
            ]}
        if "status=in_progress" in url:
            return {"total_count": 0, "workflow_runs": []}
        raise AssertionError("aucune requete /jobs attendue (rien in-window)")

    monkeypatch.setattr(rs, "_gh_json", fake_gh)
    st = rs.fetch_starvation("jsboige/CoursIA", "coursia-linux", 15.0, now=now)
    assert st.starved == []
    assert st.unexamined.get("queued") == 188
    assert pages_fetched == [1]  # pas de page 2 : arret premature borne


def test_job_created_at_anchors_age_over_run_created_at(monkeypatch):
    """Un job debloque tard (needs:) n'a attendu que 2 min meme si le run a
    40 min : l'age run serait un faux positif, sens inverse du fail-open."""
    now = datetime(2026, 9, 2, 12, 0, tzinfo=timezone.utc)

    def fake_gh(args: list[str], token: str | None = None):
        url = args[0]
        if "status=queued" in url:
            return {"total_count": 1, "workflow_runs": [_run_row(80, 40.0, now)]}
        if "status=in_progress" in url:
            return {"total_count": 0, "workflow_runs": []}
        if "/jobs" in url:
            return {"jobs": [
                {"name": "guard", "status": "queued",
                 "labels": ["self-hosted", "coursia-linux"],
                 "created_at": (now - timedelta(minutes=2)).isoformat()},
            ]}
        return None

    monkeypatch.setattr(rs, "_gh_json", fake_gh)
    st = rs.fetch_starvation("jsboige/CoursIA", "coursia-linux", 15.0, now=now)
    assert st.starved == []
    assert st.in_progress == []


def test_queued_job_inside_in_progress_run_is_seen(monkeypatch):
    """Falsification du faux negatif mixte (po-2025, 2026-09-02) : un run
    in_progress dont le job coursia-linux est reste queued. L'ancien filtre
    classait le job par le statut du RUN -> invisible aux deux passes, verdict
    OK possible sous extinction ciblee de la jambe Linux."""
    now = datetime(2026, 9, 2, 12, 0, tzinfo=timezone.utc)

    def fake_gh(args: list[str], token: str | None = None):
        url = args[0]
        if "status=queued" in url:
            return {"total_count": 0, "workflow_runs": []}
        if "status=in_progress" in url:
            # Run in_progress (40 min) -- l'autre job (ubuntu) draine, le
            # job du label attend depuis 30 min : extinction ciblee.
            return {"total_count": 1, "workflow_runs": [_run_row(90, 40.0, now)]}
        if "/jobs" in url:
            return {"jobs": [
                {"name": "guard-ubuntu", "status": "in_progress",
                 "labels": ["ubuntu-latest"]},
                {"name": "guard-linux", "status": "queued",
                 "labels": ["self-hosted", "coursia-linux"],
                 "created_at": (now - timedelta(minutes=30)).isoformat()},
            ]}
        return None

    monkeypatch.setattr(rs, "_gh_json", fake_gh)
    st = rs.fetch_starvation("jsboige/CoursIA", "coursia-linux", 15.0, now=now)
    assert len(st.starved) == 1
    assert st.starved[0].job_name == "guard-linux"
    assert st.starved[0].age_min is not None and st.starved[0].age_min > 29
    assert st.in_progress == []  # le job ubuntu est hors label


def test_run_transition_between_passes_replaces_classification(monkeypatch):
    """Un run qui transite queued -> in_progress entre les deux passes API
    revient dans les deux listes. Le second passage est le plus frais : son
    observation REMPLACE la premiere -- un job compte affame puis passe
    in_progress doit quitter la liste des affames (faux positif sinon), et un
    job reste queued n'est compte qu'une fois (faux double sinon)."""
    now = datetime(2026, 9, 2, 12, 0, tzinfo=timezone.utc)
    # Pass 1 (queued) : le job du label attend depuis 30 min.
    # Pass 2 (in_progress, plus frais) : le job a demarre.
    state = {"pass": 0}

    def fake_gh(args: list[str], token: str | None = None):
        url = args[0]
        if "status=queued" in url or "status=in_progress" in url:
            state["pass"] += 1
            return {"total_count": 1, "workflow_runs": [_run_row(90, 40.0, now)]}
        if "/jobs" in url:
            job_status = "queued" if state["pass"] == 1 else "in_progress"
            return {"jobs": [
                {"name": "guard", "status": job_status,
                 "labels": ["self-hosted", "coursia-linux"]},
            ]}
        return None

    monkeypatch.setattr(rs, "_gh_json", fake_gh)
    st = rs.fetch_starvation("jsboige/CoursIA", "coursia-linux", 15.0, now=now)
    assert st.starved == []
    assert len(st.in_progress) == 1
    assert st.in_progress[0].job_name == "guard"


def test_job_seen_in_both_passes_is_counted_once(monkeypatch):
    """Run encore queued au second passage (pas de transition) : le meme job
    affame ne doit pas etre compte deux fois."""
    now = datetime(2026, 9, 2, 12, 0, tzinfo=timezone.utc)

    def fake_gh(args: list[str], token: str | None = None):
        url = args[0]
        if "status=queued" in url:
            return {"total_count": 1, "workflow_runs": [_run_row(90, 40.0, now)]}
        if "status=in_progress" in url:
            # Transition run-level vue par l'API : le run reparait en
            # in_progress alors que son job est TOUJOURS queued (attente
            # runner, besoin needs: long).
            return {"total_count": 1, "workflow_runs": [_run_row(90, 40.0, now)]}
        if "/jobs" in url:
            return {"jobs": [
                {"name": "guard", "status": "queued",
                 "labels": ["self-hosted", "coursia-linux"]},
            ]}
        return None

    monkeypatch.setattr(rs, "_gh_json", fake_gh)
    st = rs.fetch_starvation("jsboige/CoursIA", "coursia-linux", 15.0, now=now)
    assert len(st.starved) == 1


def test_job_queued_then_completed_leaves_starved(monkeypatch):
    """Falsification du residu adjoint (po-2025, 2026-09-02 11:23Z) : un job
    observe queued au premier passage puis completed au second (un autre job
    du run a demarre, le run est passe in_progress) doit QUITTER la liste
    des affames -- l'ancien filtre terminal continuait avant le retrait de
    l'ancienne classification, et le job restait artificiellement starved
    apres drain (faux positif rouge)."""
    now = datetime(2026, 9, 2, 12, 0, tzinfo=timezone.utc)
    state = {"pass": 0}

    def fake_gh(args: list[str], token: str | None = None):
        url = args[0]
        if "status=queued" in url or "status=in_progress" in url:
            state["pass"] += 1
            return {"total_count": 1, "workflow_runs": [_run_row(90, 40.0, now)]}
        if "/jobs" in url:
            job_status = "queued" if state["pass"] == 1 else "completed"
            jobs = [
                {"id": 9001, "name": "guard-ubuntu", "status": "in_progress",
                 "labels": ["ubuntu-latest"]},
            ]
            if state["pass"] == 2:
                # Le job du label a termine pile entre les deux passes : le
                # run est in_progress (l'autre job tourne encore).
                jobs.append({"id": 9002, "name": "guard-linux", "status": "completed",
                             "labels": ["self-hosted", "coursia-linux"]})
            else:
                jobs.append({"id": 9002, "name": "guard-linux", "status": "queued",
                             "labels": ["self-hosted", "coursia-linux"],
                             "created_at": (now - timedelta(minutes=40)).isoformat()})
            return {"jobs": jobs}
        return None

    monkeypatch.setattr(rs, "_gh_json", fake_gh)
    st = rs.fetch_starvation("jsboige/CoursIA", "coursia-linux", 15.0, now=now)
    assert st.starved == []
    assert st.in_progress == []


def test_job_queued_then_cancelled_leaves_starved(monkeypatch):
    """Meme transition vers cancelled : la classification anterieure doit
    etre retiree des que le job est revu, sans reinsertion terminale."""
    now = datetime(2026, 9, 2, 12, 0, tzinfo=timezone.utc)
    state = {"pass": 0}

    def fake_gh(args: list[str], token: str | None = None):
        url = args[0]
        if "status=queued" in url or "status=in_progress" in url:
            state["pass"] += 1
            return {"total_count": 1, "workflow_runs": [_run_row(90, 40.0, now)]}
        if "/jobs" in url:
            jobs = [
                {"id": 9003, "name": "guard-ubuntu", "status": "in_progress",
                 "labels": ["ubuntu-latest"]},
            ]
            if state["pass"] == 2:
                jobs.append({"id": 9004, "name": "guard-linux", "status": "cancelled",
                             "labels": ["self-hosted", "coursia-linux"]})
            else:
                jobs.append({"id": 9004, "name": "guard-linux", "status": "queued",
                             "labels": ["self-hosted", "coursia-linux"],
                             "created_at": (now - timedelta(minutes=40)).isoformat()})
            return {"jobs": jobs}
        return None

    monkeypatch.setattr(rs, "_gh_json", fake_gh)
    st = rs.fetch_starvation("jsboige/CoursIA", "coursia-linux", 15.0, now=now)
    assert st.starved == []
    assert st.in_progress == []


def test_unexamined_old_runs_are_noted_not_red():
    """Le reliquat abandonne ne rend JAMAIS l'organe rouge -- sinon rouge
    permanent sur les runs a 14 jours, le mode d'echec que la garde anti-FP
    du body interdit."""
    st = rs.Starvation(unexamined={"queued": 34})
    v = rs.evaluate(inventory(["a", "b", "c", "d"]), st, 2)
    assert v.status == "OK"
    assert any("34" in n and "ABANDONNEE" in n for n in v.notes)
    assert v.errors == []


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
