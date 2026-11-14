from __future__ import annotations

import json
import os
import re
import sys
import time
from datetime import datetime, timedelta, timezone
from pathlib import Path
from urllib.parse import urlsplit

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
    inv = inventory(["r-1"], ["r-2", "r-3"])
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

    def fake_gh(args: list[str], token: str | None = None, stats=None):
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

    def fake_gh(args: list[str], token: str | None = None, stats=None):
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

    def fake_gh(args: list[str], token: str | None = None, stats=None):
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

    def fake_gh(args: list[str], token: str | None = None, stats=None):
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

    def fake_gh(args: list[str], token: str | None = None, stats=None):
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

    def fake_gh(args: list[str], token: str | None = None, stats=None):
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

    def fake_gh(args: list[str], token: str | None = None, stats=None):
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

    def fake_gh(args: list[str], token: str | None = None, stats=None):
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

    def fake_gh(args: list[str], token: str | None = None, stats=None):
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
    def fake_gh(args: list[str], token: str | None = None, stats=None):
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
    monkeypatch.setattr(rs, "_gh_json", lambda args, token=None, stats=None: None)
    inv = rs.fetch_inventory("jsboige/CoursIA", "coursia-linux", token=None)
    assert not inv.available


def test_inventaire_busy_nest_pas_dans_les_slots_libres(monkeypatch):
    # Un runner en ligne mais OCCUPE ne peut pas absorber un debordement :
    # le confondre avec un slot libre ferait annoncer une capacite locale
    # qui n'existe pas.
    def fake_gh(args: list[str], token: str | None = None, stats=None):
        return {"runners": [
            {"name": "r-busy", "status": "online", "busy": True,
             "labels": [{"name": "coursia-linux"}]},
            {"name": "r-idle", "status": "online", "busy": False,
             "labels": [{"name": "coursia-linux"}]},
        ]}

    monkeypatch.setattr(rs, "_gh_json", fake_gh)
    inv = rs.fetch_inventory("jsboige/CoursIA", "coursia-linux", token="pat")
    assert inv.busy == ["r-busy"]
    assert inv.idle == ["r-idle"]
    assert inv.unknown == []
    assert inv.free == 1


def test_inventaire_champ_busy_absent_ne_passe_pas_pour_un_slot_libre(monkeypatch):
    # Un runner en ligne dont l'occupation est INCONNUE (champ `busy` absent
    # de la reponse) n'est PAS comptabilise comme libre : fail-CLOSED vers
    # « capacite disponible ». Le traitement du cas muet est explicite, et
    # le runner est nomme pour que le rapport dise ce qu'il ignore.
    def fake_gh(args: list[str], token: str | None = None, stats=None):
        return {"runners": [
            {"name": "r-muet", "status": "online",
             "labels": [{"name": "coursia-linux"}]},
        ]}

    monkeypatch.setattr(rs, "_gh_json", fake_gh)
    inv = rs.fetch_inventory("jsboige/CoursIA", "coursia-linux", token="pat")
    assert inv.unknown == ["r-muet"]
    assert inv.idle == []
    assert inv.busy == []
    assert inv.free == 0


def test_budget_de_lecture_atteint_une_lecture_tronquee_pas_une_lecture_echouee():
    # Deux proprietes, deux faits : `complete` dit si la lecture a SUCCEEDE
    # (aucun listing en echec), `truncated` dit si elle a vu TOUT. Un run non
    # lu est un run vieux : il peut porter des jobs affames. La consequence
    # directionnelle est traitee par le controleur (#22946).
    st = rs.Starvation()
    assert st.complete is True and st.truncated is False
    st.budget_unread.append(("wf", 42, 17.5))
    assert st.truncated is True
    # La lecture n'a pas ECHOUE : elle a ete arretee par le budget.
    assert st.complete is True


def test_job_queued_then_run_disappears_terminal_is_purged(monkeypatch):
    """Falsification du residu adjoint (po-2025:CoursIA-2, 2026-09-02 14:24Z) :
    le run ENTIER devient terminal entre les deux listing queries -- il
    disparait du snapshot 2 (ni queued ni in_progress), le job du label n'est
    jamais re-observe et l'entree starved du pass 1 survivait
    (`starved=[('guard-linux','queued',40.0)]`). La requete directe au run
    (status=completed) doit purger l'entree -- le snapshot 1 seul n'est plus
    la derniere observation du job."""
    now = datetime(2026, 9, 2, 12, 0, tzinfo=timezone.utc)

    def fake_gh(args: list[str], token: str | None = None, stats=None):
        url = args[0]
        if "status=queued" in url:
            return {"total_count": 1, "workflow_runs": [_run_row(90, 40.0, now)]}
        if "status=in_progress" in url:
            # Snapshot 2 : le run 90 a disparu (devenu terminal entre les
            # deux queries) -- plus ni queued ni in_progress dans ses codes.
            return {"total_count": 0, "workflow_runs": []}
        if "/jobs" in url:
            return {"jobs": [
                {"id": 9010, "name": "guard-linux", "status": "queued",
                 "labels": ["self-hosted", "coursia-linux"],
                 "created_at": (now - timedelta(minutes=40)).isoformat()},
            ]}
        if url.endswith("/actions/runs/90"):
            return {"id": 90, "status": "completed"}
        return None

    monkeypatch.setattr(rs, "_gh_json", fake_gh)
    st = rs.fetch_starvation("jsboige/CoursIA", "coursia-linux", 15.0, now=now)
    assert st.starved == []
    assert st.in_progress == []


def test_job_queued_run_still_queued_direct_preserved(monkeypatch):
    """Contre-test anti-faux-negatif : la re-verification directe tranche. Un
    run queued stable (encore queued a la requete directe) GARDE son entree
    starved -- purger les entrees dont le run n'a pas ete revu au snapshot 2
    SANS re-verifier rendrait l'organe muet sous vraie file profonde (le run
    queued stable n'apparait jamais dans le listing in_progress)."""
    now = datetime(2026, 9, 2, 12, 0, tzinfo=timezone.utc)

    def fake_gh(args: list[str], token: str | None = None, stats=None):
        url = args[0]
        if "status=queued" in url:
            return {"total_count": 1, "workflow_runs": [_run_row(90, 40.0, now)]}
        if "status=in_progress" in url:
            return {"total_count": 0, "workflow_runs": []}
        if "/jobs" in url:
            return {"jobs": [
                {"id": 9011, "name": "guard-linux", "status": "queued",
                 "labels": ["self-hosted", "coursia-linux"],
                 "created_at": (now - timedelta(minutes=40)).isoformat()},
            ]}
        if url.endswith("/actions/runs/90"):
            return {"id": 90, "status": "queued"}
        return None

    monkeypatch.setattr(rs, "_gh_json", fake_gh)
    st = rs.fetch_starvation("jsboige/CoursIA", "coursia-linux", 15.0, now=now)
    assert len(st.starved) == 1
    assert st.starved[0].job_name == "guard-linux"


def test_missing_run_after_failed_listing_is_preserved(monkeypatch):
    """Fail-open : si UN listing a echoue, aucun purgement. Un run invisible
    par panne d'API n'est pas un run terminal prouve -- seule une re-verite
    directe reussie le dit. La requete directe doit donc ne JAMAIS etre
    appelee (le pipeline s'arrete avant)."""
    now = datetime(2026, 9, 2, 12, 0, tzinfo=timezone.utc)

    def fake_gh(args: list[str], token: str | None = None, stats=None):
        url = args[0]
        if "status=queued" in url:
            return {"total_count": 1, "workflow_runs": [_run_row(90, 40.0, now)]}
        if "status=in_progress" in url:
            return None  # listing echoue : aucune conclusion d'absence
        if "/jobs" in url:
            return {"jobs": [
                {"id": 9012, "name": "guard-linux", "status": "queued",
                 "labels": ["self-hosted", "coursia-linux"],
                 "created_at": (now - timedelta(minutes=40)).isoformat()},
            ]}
        raise AssertionError("requete directe interdite quand un listing a echoue")

    monkeypatch.setattr(rs, "_gh_json", fake_gh)
    st = rs.fetch_starvation("jsboige/CoursIA", "coursia-linux", 15.0, now=now)
    assert len(st.starved) == 1


# --- POOL LOSS PAR HOTE (#20697 point 4) ------------------------------------
#
# Le predicat global EXTINCTION ne rougit que si TOUS les online tombent
# (les slots etaient OFFLINE cote GitHub pendant ~2 jours, mais d'autres hotes
# du label restaient online ; l'extinction globale n'a jamais tire). La
# detection par hote comble ce trou en alertant quand UN hote a online==0 et
# offline>0, signe de la disjonction superviseur mort / conteneurs vivants
# sur ce seul hote.

def test_host_of_strips_numeric_suffix():
    """Le format canonique est `<host>-<slot>` (suffixe '-N' jete)."""
    assert rs._host_of("myia-ai-01-wsl-1") == "myia-ai-01-wsl"
    assert rs._host_of("myia-po-2024-linux-docker-3") == "myia-po-2024-linux-docker"
    assert rs._host_of("myia-po-2024-linux-docker-10") == "myia-po-2024-linux-docker"


def test_host_of_keeps_unsuffixed_name_unchanged():
    """Les noms qui ne portent pas le suffixe numerique (futur format) restent
    tels quels -- la detection par hote est best-effort, le predicat EXTINCTION
    global reste la borne dure."""
    assert rs._host_of("myia-ai-01-wsl") == "myia-ai-01-wsl"
    assert rs._host_of("po-2024-docker") == "po-2024-docker"
    assert rs._host_of("") == ""


def test_host_of_handles_single_digit_and_multi_digit():
    """Tous les chiffres au-dela de 1 doivent etre jetes (re-#2 du test_1
    quand le pool grandit) -- le suffixe est le DERNIER token numerique, pas
    seulement 1 chiffre."""
    assert rs._host_of("host-a-1") == "host-a"
    assert rs._host_of("host-a-42") == "host-a"
    assert rs._host_of("host-a-999") == "host-a"


def test_evaluate_host_loss_founder_case():
    """Cas fondateur (#20697, 12:45Z) : tous les slots d'UN hote offline,
    AUCUN en ligne -> une alerte nommant cet hote, la seule."""
    inv = inventory(
        online=["myia-po-2024-linux-docker-1", "myia-po-2024-linux-docker-2"],
        offline=[
            "myia-ai-01-wsl-1", "myia-ai-01-wsl-2", "myia-ai-01-wsl-3",
            "myia-ai-01-wsl-4", "myia-ai-01-wsl-5",
        ],
    )
    warnings = rs.evaluate_host_loss(inv)
    assert len(warnings) == 1
    assert "myia-ai-01-wsl" in warnings[0]
    assert "0 runner online" in warnings[0]
    assert "5 offline" in warnings[0]
    # L'hote en ligne ne doit PAS apparaitre dans les alertes.
    assert "myia-po-2024-linux-docker" not in warnings[0]


def test_evaluate_host_loss_partial_online_no_alert():
    """Garde anti-FP : un hote avec online>0 ET offline>0 n'est PAS une perte
    de pool -- certains slots sont en cours de redemarrage et le pool rend
    des jobs. Mesure du jour : 1 online + 1 offline sur le meme hote -> 0
    alerte."""
    inv = inventory(
        online=["myia-po-2024-linux-docker-1"],
        offline=["myia-po-2024-linux-docker-3"],
    )
    warnings = rs.evaluate_host_loss(inv)
    assert warnings == []


def test_evaluate_host_loss_inventory_unavailable_returns_empty():
    """Pas d'inventaire (pas de PAT) -> pas d'alerte de perte par hote. Le
    predicat est strictement unaire sur l'inventaire, comme EXTINCTION."""
    inv = rs.InventoryUnavailable(reason="pas de PAT")
    warnings = rs.evaluate_host_loss(inv)
    assert warnings == []


def test_evaluate_host_loss_one_lost_host_among_healthy():
    """Deux hotes, un seul perdu : l'alerte ne nomme QUE le perdu, pas
    l'autre. Mesure : myia-ai-01-wsl 4 offline / 0 online, myia-po-2024
    2 online / 0 offline -> 1 alerte ciblant le wsl."""
    inv = inventory(
        online=["myia-po-2024-linux-docker-1", "myia-po-2024-linux-docker-2"],
        offline=[
            "myia-ai-01-wsl-1", "myia-ai-01-wsl-2",
            "myia-ai-01-wsl-3", "myia-ai-01-wsl-4",
        ],
    )
    warnings = rs.evaluate_host_loss(inv)
    assert len(warnings) == 1
    assert "myia-ai-01-wsl" in warnings[0]
    # L'hote sain NE doit PAS apparaitre dans l'alerte du perdu.
    assert "myia-po-2024-linux-docker" not in warnings[0]


def test_evaluate_host_loss_multiple_lost_hosts_each_named():
    """Deux hotes perdus simultanement : 2 alertes distinctes, chacune nomme
    son hote."""
    inv = inventory(
        online=[],
        offline=[
            "myia-ai-01-wsl-1", "myia-ai-01-wsl-2",
            "myia-po-2024-linux-docker-1", "myia-po-2024-linux-docker-2",
        ],
    )
    warnings = rs.evaluate_host_loss(inv)
    assert len(warnings) == 2
    hosts_named = {w.split("host ")[1].split(" ")[0] for w in warnings}
    assert hosts_named == {"myia-ai-01-wsl", "myia-po-2024-linux-docker"}


def test_evaluate_wires_host_loss_warnings():
    """L'integration evaluate() doit etendre v.warnings avec les alertes de
    pool loss, sans les faire passer en erreur -- un hote perdu reste un
    WARN, pas un ERROR (le pool global n'est pas mort)."""
    inv = inventory(
        online=["po-2024-1"],
        offline=["ai-01-wsl-1", "ai-01-wsl-2"],
    )
    v = rs.evaluate(inv, rs.Starvation(), warn_floor=2)
    assert v.status == "OK"
    assert any("POOL LOSS" in w and "ai-01-wsl" in w for w in v.warnings)


# --- RESOLUTION DU CONFLIT (main <- PR #23148) --------------------------
# Les deux sides sont ADDITIFS : le side PR porte le « FILTRE DE CHEMIN
# (#22937 phase A) », le side main porte la « PORTE DE MESURE (#22937) ».
# Aucun nom de niveau module en collision (LOCAL_PATH / HOSTED_PATH /
# _path_run d'un cote, 8 tests de l'autre) -> l'union conservee, rien
# masque.
# --- FILTRE DE CHEMIN (#22937 phase A) ------------------------------------
#
# La lecture locale du controleur de debordement ne doit pas consommer son
# budget de lectures sur des runs qui ne peuvent pas porter un job du label
# : sous saturation de l'offre hebergee, ce sont justement les runs anciens
# de la file, tous en attente d'`ubuntu-latest` (mesure du coordinateur,
# 2026-10-28 16:55Z : 67 run(s) non lu(s), budget 120 atteint).

LOCAL_PATH = ".github/workflows/guard-local.yml"
HOSTED_PATH = ".github/workflows/guard-heberge.yml"


def _path_run(rid: int, path: str | None, created: datetime) -> dict:
    row = {"id": rid, "name": "Guard", "run_number": rid,
           "created_at": created.isoformat()}
    if path is not None:
        row["path"] = path
    return row


def test_les_runs_hors_perimetre_ne_consomment_pas_le_budget(monkeypatch):
    now = datetime(2026, 10, 28, 16, 55, tzinfo=timezone.utc)
    created = now - timedelta(minutes=63)
    job_reads: list[str] = []

    def fake_gh(args: list[str], token: str | None = None, stats=None):
        if "status=queued" in args[0]:
            # Une seule page : au-dela, la liste est vide (le listing est
            # pagine, le fake ne doit pas repeter la meme page 20 fois).
            if args[0].endswith("page=1"):
                return {"workflow_runs": [
                    _path_run(2000 + i, HOSTED_PATH, created) for i in range(250)]}
            return {"workflow_runs": []}
        if "status=in_progress" in args[0]:
            return {"workflow_runs": []}
        if "/jobs" in args[0]:
            job_reads.append(args[0])
            return {"jobs": []}
        return None

    monkeypatch.setattr(rs, "_gh_json", fake_gh)
    st = rs.fetch_starvation("jsboige/CoursIA", "coursia-linux", 15.0, now=now,
                             job_read_budget=120, local_paths={LOCAL_PATH})
    assert st.job_reads == 0
    assert st.truncated is False
    assert st.skipped_other_workflow == 250
    assert job_reads == []


def test_un_run_sans_path_est_lu_malgre_le_filtre(monkeypatch):
    """Un `path` absent ne doit JAMAIS pouvoir cacher une affamescence : le
    run est lu et compte a part."""
    now = datetime(2026, 10, 28, 16, 55, tzinfo=timezone.utc)
    created = now - timedelta(minutes=63)

    def fake_gh(args: list[str], token: str | None = None, stats=None):
        if "status=queued" in args[0]:
            return {"workflow_runs": [_path_run(3001, None, created)]}
        if "status=in_progress" in args[0]:
            return {"workflow_runs": []}
        if "/jobs" in args[0]:
            return {"jobs": [
                {"name": "guard-on-label", "status": "queued",
                 "labels": ["self-hosted", "coursia-linux"],
                 "created_at": created.isoformat()}]}
        return None

    monkeypatch.setattr(rs, "_gh_json", fake_gh)
    st = rs.fetch_starvation("jsboige/CoursIA", "coursia-linux", 15.0, now=now,
                             job_read_budget=120, local_paths={LOCAL_PATH})
    assert st.job_reads == 1
    assert st.unknown_path_reads == 1
    assert len(st.starved) == 1


def test_le_filtre_laisse_passer_le_job_local_du_perimetre(monkeypatch):
    now = datetime(2026, 10, 28, 16, 55, tzinfo=timezone.utc)
    created = now - timedelta(minutes=63)

    def fake_gh(args: list[str], token: str | None = None, stats=None):
        if "status=queued" in args[0]:
            return {"workflow_runs": [_path_run(3002, LOCAL_PATH, created)]}
        if "status=in_progress" in args[0]:
            return {"workflow_runs": []}
        if "/jobs" in args[0]:
            return {"jobs": [
                {"name": "guard-on-label", "status": "queued",
                 "labels": ["self-hosted", "coursia-linux"],
                 "created_at": created.isoformat()}]}
        return None

    monkeypatch.setattr(rs, "_gh_json", fake_gh)
    st = rs.fetch_starvation("jsboige/CoursIA", "coursia-linux", 15.0, now=now,
                             job_read_budget=120, local_paths={LOCAL_PATH})
    assert st.skipped_other_workflow == 0
    assert len(st.starved) == 1
    assert st.starved[0].run_path == LOCAL_PATH
# --- PORTE DE MESURE (#22937) ----------------------------------------------
# Le heartbeat workflow_run declenche sur CHAQUE fin d'ancre (721 fins/24 h
# mesurees -> 60 runs/h pour la paire d'advisories -> ~480 appels API/h sur
# le jeton de depot, sature le 2026-10-28 22:04Z). La porte borne la
# MESURE, pas le RUN : l'observateur survit et son rapport de cadence servie
# (#15332) est emis a chaque passage.

def test_gate_is_inactive_by_default():
    measure, reason = rs.gate_measurement(every_n=0, run_number=7,
                                          event_name="workflow_run")
    assert measure is True
    assert "inactive" in reason


def test_gate_every_n_one_is_inactive():
    measure, _ = rs.gate_measurement(every_n=1, run_number=7,
                                     event_name="workflow_run")
    assert measure is True


def test_gate_never_gates_the_schedule_leg():
    # La jambe schedule est la cadence de REFERENCE de l'advisory : la
    # gater, ce serait supprimer la reference qu'on veut conserver.
    measure, reason = rs.gate_measurement(every_n=4, run_number=3,
                                          event_name="schedule")
    assert measure is True
    assert "schedule" in reason


def test_gate_never_gates_a_manual_dispatch():
    measure, _ = rs.gate_measurement(every_n=4, run_number=3,
                                     event_name="workflow_dispatch")
    assert measure is True


def test_gate_measures_one_workflow_run_in_n():
    measured, _ = rs.gate_measurement(every_n=4, run_number=8,
                                      event_name="workflow_run")
    assert measured is True
    for run_number in (9, 10, 11):
        measured, _ = rs.gate_measurement(every_n=4, run_number=run_number,
                                          event_name="workflow_run")
        assert measured is False


def test_gate_measures_when_the_run_number_is_unknown():
    # Hors Actions (GITHUB_RUN_NUMBER absent) : une lecture qui ne sait pas
    # ou elle est ne doit pas s'arreter.
    measure, reason = rs.gate_measurement(every_n=4, run_number=None,
                                          event_name="workflow_run")
    assert measure is True
    assert "inconnu" in reason


def test_gate_reason_names_the_run_it_refuses_to_measure():
    _, reason = rs.gate_measurement(every_n=4, run_number=17,
                                    event_name="workflow_run")
    assert "17" in reason
    assert "CADENCE SEULE" in reason


def test_env_int_reads_and_refuses_garbage(monkeypatch):
    monkeypatch.setenv("RS_TEST_INT", " 42 ")
    assert rs._env_int("RS_TEST_INT") == 42
    monkeypatch.setenv("RS_TEST_INT", "pas-un-entier")
    assert rs._env_int("RS_TEST_INT") is None
    monkeypatch.delenv("RS_TEST_INT", raising=False)
    assert rs._env_int("RS_TEST_INT") is None


def test_main_cadence_only_pass_still_reports_the_scheduler_silence(
        monkeypatch, capsys):
    # Le devoir #15332 ne doit SURVIVRE a la porte : un passage econome
    # reste un passage, et il dit toujours si le scheduler se tait.
    seen = {"inventory": 0, "starvation": 0}

    def fake_scheduled(repo, workflow, limit=3, stats=None):
        # La vraie lecture compte 1 appel dans le compteur du passage.
        if stats is not None:
            stats.calls += 1
        return []

    def fake_inventory(repo, label, token):
        seen["inventory"] += 1
        return rs.RunnerInventory()

    def fake_starvation(*args, **kwargs):
        seen["starvation"] += 1
        return rs.Starvation()

    monkeypatch.setattr(rs, "fetch_scheduled_runs", fake_scheduled)
    monkeypatch.setattr(rs, "fetch_inventory", fake_inventory)
    monkeypatch.setattr(rs, "fetch_starvation", fake_starvation)
    monkeypatch.setattr(sys, "argv", [
        "check_runner_starvation.py", "--json",
        "--self-workflow", "advisory.yml",
        "--measure-every-n-runs", "4",
    ])
    monkeypatch.setenv("GITHUB_EVENT_NAME", "workflow_run")
    monkeypatch.setenv("GITHUB_RUN_NUMBER", "17")

    assert rs.main() == 0
    out = capsys.readouterr().out
    payload = json.loads(out)
    assert payload["measurement"] == "cadence-only"
    assert payload["gh_calls"] == 1
    assert seen == {"inventory": 0, "starvation": 0}
    assert any("SCHEDULER MUET" in w for w in payload["warnings"])


# --- MIROIR D'OBJETS (#26453) ----------------------------------------------
# L'alerte `[WARN][mirror]` du superviseur ne vaut que si elle REMONTE sur une
# surface qu'une lane lit. Ces tests mesurent ce branchement -- et ses
# limites : hors de l'hote qui porte le miroir, l'etat est illisible, et
# l'organe doit le dire sans rougir (un rouge sur une absence de preuve
# apprendrait a etre ignore).

def _mirror_fixture(tmp_path, fails=None, warn=False, age_s=0.0):
    """Ecrit l'etat du miroir comme le superviseur l'ecrit (#26459).

    Le compteur `.objects-mirror.fails` et l'horodatage `.objects-mirror.ok`
    vivent dans le PARENT du miroir (le volume toolcache) ; le journal
    `objects-mirror.log` vit dans le repertoire d'etat du superviseur.
    """
    state_dir = tmp_path / "state"
    volume = tmp_path / "toolcache"
    state_dir.mkdir(parents=True, exist_ok=True)
    volume.mkdir(parents=True, exist_ok=True)
    mirror = volume / "coursia-mirror.git"
    if fails is not None:
        path = volume / ".objects-mirror.fails"
        path.write_text(str(fails), encoding="utf-8")
        if age_s:
            old = time.time() - age_s
            os.utime(path, (old, old))
    if warn:
        (state_dir / "objects-mirror.log").write_text(
            "miroir: rafraichi (2026-11-14T01:02:35+00:00)\n"
            "[WARN][mirror] refresh en echec 3 fois de suite (~15 min) "
            "-- cause : le fetch a echoue (voir la sortie du fetch ci-dessus)\n",
            encoding="utf-8")
    return str(state_dir), str(mirror)


def test_mirror_absent_is_a_note_and_never_an_error(tmp_path):
    # Hors de l'hote du miroir (runner GitHub-hosted), aucun fichier n'existe.
    # L'organe ne peut rien conclure sur le miroir : c'est une NOTE.
    state = rs.read_mirror_state(str(tmp_path / "nope"), str(tmp_path / "no-mirror"))
    assert state.available is False
    errors, warnings, notes = rs.mirror_verdict(state)
    assert errors == []
    assert warnings == []
    assert any("ne conclut rien" in n for n in notes)


def test_mirror_counter_below_threshold_is_not_an_error(tmp_path):
    state_dir, mirror = _mirror_fixture(tmp_path, fails=1)
    state = rs.read_mirror_state(state_dir, mirror)
    assert state.available is True
    assert state.fails == 1
    errors, _warnings, notes = rs.mirror_verdict(state)
    assert errors == []
    assert any("aucun gel" in n for n in notes)


def test_mirror_fresh_counter_at_threshold_is_an_error_with_the_verbatim_line(
        tmp_path):
    # Le cas fondateur : la boucle tourne et le miroir echoue. C'est un
    # ROUGE, et la ligne `[WARN][mirror]` du superviseur est reprise VERBATIM
    # (c'est elle qui nomme la cause).
    state_dir, mirror = _mirror_fixture(tmp_path, fails=3, warn=True)
    state = rs.read_mirror_state(state_dir, mirror)
    errors, _warnings, _notes = rs.mirror_verdict(state)
    assert len(errors) == 1
    assert "MIROIR FIGE" in errors[0]
    assert "[WARN][mirror] refresh en echec 3 fois de suite" in errors[0]
    assert "le fetch a echoue" in errors[0]


def test_mirror_stale_counter_is_a_note_not_a_permanent_red(tmp_path):
    # Un compteur VIEUX ne prouve pas que le miroir echoue : il prouve que la
    # boucle de rafraichissement est arretee (service desactive, hote eteint).
    # Confondre les deux produirait un rouge permanent sur un etat fige depuis
    # des semaines -- et un rouge permanent s'apprend a etre ignore.
    state_dir, mirror = _mirror_fixture(tmp_path, fails=3, warn=True, age_s=7200.0)
    state = rs.read_mirror_state(state_dir, mirror)
    errors, _warnings, notes = rs.mirror_verdict(state)
    assert errors == []
    assert any("n'est plus reecrit" in n for n in notes)


def test_mirror_warn_line_is_read_from_the_tail_of_the_log(tmp_path):
    state_dir, mirror = _mirror_fixture(tmp_path, fails=3, warn=True)
    state = rs.read_mirror_state(state_dir, mirror)
    assert state.warn_line.startswith("[WARN][mirror]")
    assert state.counter_age_s is not None
    assert state.counter_age_s < 60.0


def test_main_surfaces_the_mirror_alert_in_its_payload(monkeypatch, capsys,
                                                         tmp_path):
    # La branche qui compte : l'alerte du miroir doit changer le VERDICT de
    # l'organe (rc 1) et apparaitre dans le payload JSON -- c'est ce que lit
    # une machine, pas seulement un oeil.
    state_dir, mirror = _mirror_fixture(tmp_path, fails=3, warn=True)

    monkeypatch.setattr(rs, "fetch_scheduled_runs", lambda *a, **k: [])
    monkeypatch.setattr(rs, "fetch_inventory", lambda *a, **k: rs.RunnerInventory())
    monkeypatch.setattr(rs, "fetch_starvation", lambda *a, **k: rs.Starvation())
    monkeypatch.setattr(sys, "argv", [
        "check_runner_starvation.py", "--json",
        "--mirror-state-dir", state_dir,
        "--mirror-path", mirror,
    ])

    assert rs.main() == 1
    payload = json.loads(capsys.readouterr().out)
    assert payload["status"] == "ERROR"
    assert payload["mirror"]["available"] is True
    assert payload["mirror"]["fails"] == 3
    assert payload["mirror"]["threshold"] == 3
    assert "[WARN][mirror]" in payload["mirror"]["warn_line"]
    assert any("MIROIR FIGE" in e for e in payload["errors"])


def test_main_leaves_the_mirror_quiet_when_it_is_healthy(monkeypatch, capsys,
                                                          tmp_path):
    state_dir, mirror = _mirror_fixture(tmp_path, fails=0)
    monkeypatch.setattr(rs, "fetch_scheduled_runs", lambda *a, **k: [])
    monkeypatch.setattr(rs, "fetch_inventory", lambda *a, **k: rs.RunnerInventory())
    monkeypatch.setattr(rs, "fetch_starvation", lambda *a, **k: rs.Starvation())
    monkeypatch.setattr(sys, "argv", [
        "check_runner_starvation.py", "--json",
        "--mirror-state-dir", state_dir,
        "--mirror-path", mirror,
    ])

    assert rs.main() == 0
    payload = json.loads(capsys.readouterr().out)
    assert payload["status"] == "OK"
    assert payload["mirror"]["fails"] == 0
    assert not any("MIROIR" in e for e in payload["errors"])


# --- MODE MIROIR SEUL + SURFACE PR (#26465) --------------------------------
# L'etat du miroir est LOCAL a l'hote qui le porte. Les trois advisories de
# starvation le lisaient depuis `ubuntu-latest`, ou il n'existe pas : l'alerte
# n'atteignait donc AUCUNE surface (revue ai-01 du 14/11, reserve 1). Le mode
# `--mirror-only` est le mode du job de PR : il tourne sur le slot
# auto-heberge qui porte le miroir, ne paie AUCUN appel API, et sa
# conclusion tombe sur la PR.

def test_mirror_only_mode_is_red_on_a_frozen_mirror(monkeypatch, capsys,
                                                     tmp_path):
    state_dir, mirror = _mirror_fixture(tmp_path, fails=3, warn=True)

    def _interdit(*a, **k):
        raise AssertionError("le mode miroir seul ne doit appeler aucune API")

    monkeypatch.setattr(rs, "fetch_scheduled_runs", _interdit)
    monkeypatch.setattr(rs, "fetch_inventory", _interdit)
    monkeypatch.setattr(rs, "fetch_starvation", _interdit)
    monkeypatch.setattr(sys, "argv", [
        "check_runner_starvation.py", "--mirror-only", "--json",
        "--mirror-state-dir", state_dir,
        "--mirror-path", mirror,
    ])

    assert rs.main() == 1
    payload = json.loads(capsys.readouterr().out)
    assert payload["measurement"] == "mirror-only"
    assert payload["gh_calls"] == 0
    assert payload["status"] == "ERROR"
    assert any("MIROIR FIGE" in e for e in payload["errors"])
    assert "[WARN][mirror]" in payload["mirror"]["warn_line"]


def test_mirror_only_mode_is_a_note_when_the_state_is_unreadable(monkeypatch,
                                                                  capsys,
                                                                  tmp_path):
    # Hors de l'hote du miroir, l'absence d'etat ne prouve rien : note,
    # jamais rouge (anti-FP).
    monkeypatch.setattr(sys, "argv", [
        "check_runner_starvation.py", "--mirror-only", "--json",
        "--mirror-state-dir", str(tmp_path / "absent"),
        "--mirror-path", str(tmp_path / "absent" / "coursia-mirror.git"),
    ])

    assert rs.main() == 0
    payload = json.loads(capsys.readouterr().out)
    assert payload["status"] == "OK"
    assert not payload["errors"]
    assert any("ne conclut rien" in n for n in payload["notes"])


def test_le_rouge_du_miroir_atteint_la_pr():
    """TEMOIN : le rouge doit avoir une surface, et cette surface est la PR.

    Ce test ne mesure pas le verdict -- les tests du dessus le font. Il
    **pince le cablage**. Sans lui, on pourrait faire tourner le job sur
    `ubuntu-latest` (ou l'enlever) : l'etat du miroir redeviendrait illisible
    sur la seule surface ou l'alerte atterrissait, et le rouge mourrait en
    silence -- exactement comme le 26/10.
    """
    workflow = CI_DIR.parents[1] / ".github/workflows/mirror-state-pr-advisory.yml"
    assert workflow.exists(), "le job de PR du miroir doit exister"
    texte = workflow.read_text(encoding="utf-8")

    # 1. La surface : le job est declenche par une PR.
    assert "pull_request:" in texte
    # 2. Il tourne sur le slot qui PORTE le miroir (le volume y est monte).
    assert "self-hosted" in texte and "coursia-linux" in texte
    # 3. Il appelle l'organe en mode miroir seul -- le mode qui ne paie
    #    aucun appel API.
    assert "--mirror-only" in texte
    # 4. Il ne consomme pas de quota : aucun appel `gh` dans le job.
    assert "gh api" not in texte and "gh issue" not in texte

    # 5. Structure : le job existe bien, avec le runner auto-heberge.
    try:
        import yaml  # type: ignore
    except ImportError:  # pragma: no cover
        return
    data = yaml.safe_load(texte)
    # YAML 1.1 : la cle `on:` se parse en booleen True.
    triggers = data.get("on", data.get(True))
    assert "pull_request" in triggers
    job = data["jobs"]["mirror"]
    runs_on = job["runs-on"]
    assert isinstance(runs_on, list)
    assert "self-hosted" in runs_on and "coursia-linux" in runs_on
    etapes = "\n".join(str(s.get("run", "")) for s in job["steps"])
    assert "--mirror-only" in etapes

    # 6. Le job ne fait PAS de checkout. Mesure du 14/11 : sur la tete
    #    `13a27f53ced7a`, le checkout a consomme les 5 minutes du job
    #    (`git fetch --depth=1 origin +<sha>:refs/remotes/pull/26465/merge`
    #    de 05:51:19 a 05:56:16, puis `##[error]The operation was canceled.`)
    #    et le job a ete tue SANS produire de verdict. C'est structurel : le
    #    checkout est precisement ce qui se degrade quand le miroir est fige
    #    (A/B #26468 : 296,5 s mediane par la voie paresseuse, 132,1 s en
    #    fetch bulk, 12,1 s par les alternates). Un observateur qui meurt de
    #    la panne qu'il observe n'alerte personne.
    assert not any("actions/checkout" in str(s.get("uses", ""))
                   for s in job["steps"]), (
        "le job du miroir ne doit PAS faire de checkout : c'est la panne "
        "qu'il observe qui le tuerait (mesure du 14/11, job annule a 5 min)"
    )
    # 7. L'organe est recupere par URL brute, epinglee sur la tete de la PR :
    #    c'est le contenu du checkout (le code de la PR a sa tete), sans le
    #    fetch. Un organe deplace est un ROUGE nomme, pas une disparition
    #    silencieuse -- c'est l'incident du 26/10 qu'on ne rejoue pas.
    #    Le controle passe par le **netloc** PARSE : comparer une
    #    sous-chaine a une URL est le patron que CodeQL signale comme
    #    assainissement incomplet (`Incomplete URL substring
    #    sanitization`), et le signalement tombait sur le *test* lui-meme
    #    (annotation CodeQL du 14/11 sur cette ligne). On compare donc le
    #    host PARSE, puis le chemin -- l'URL complete etant epinglee sur la
    #    tete de la PR.
    urls = [urlsplit(m) for m in re.findall(r"https://[^'\"\n]+", texte)]
    miroirs = [u for u in urls if u.netloc == "raw.githubusercontent.com"]
    assert miroirs, (
        "l'organe du miroir doit etre recupere par URL brute, epinglee sur "
        "la tete de la PR"
    )
    assert any(
        u.path.endswith("/scripts/ci/check_runner_starvation.py")
        and "github.event.pull_request.head.sha" in u.path
        for u in miroirs
    ), (
        "l'URL de l'organe doit pointer sur scripts/ci/"
        "check_runner_starvation.py, a la tete epinglee de la PR"
    )
    assert "::error::" in etapes
