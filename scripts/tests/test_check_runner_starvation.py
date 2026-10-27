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
