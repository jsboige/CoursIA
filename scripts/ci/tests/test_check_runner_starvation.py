"""Tests du cout et de l'honnetete d'un passage de la sonde de starvation.

#22215 : le passage lisait les jobs de chaque run de la fenetre (~380 appels
a 15:20Z le 2026-10-23) et `_gh_json` avalait les echecs -- un appel `jobs`
en panne ne laissait aucune trace, et le passages concluait « AUCUN job
in_progress », c'est-a-dire STARVATION, sur une lecture trouee.

Ce fichier verrouille les trois proprietes qui repondent a ce constat :
  - chaque echec d'appel est compte, nomme (endpoint, code, message), et un
    passage troue ne conclut NI `OK` NI `STARVATION` ;
  - le cout est borne : aucun appel jobs sur un run queued trop jeune pour
    porter un job affame, budget sur les runs queued, echantillon sur les
    runs in_progress -- et le non-lu est DIT ;
  - la restriction `--workflow` change bien l'endpoint de listing.
"""

from __future__ import annotations

import importlib.util
import json
import subprocess
import sys
from datetime import datetime, timedelta, timezone
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / "check_runner_starvation.py"
_spec = importlib.util.spec_from_file_location("check_runner_starvation", SCRIPT)
mod = importlib.util.module_from_spec(_spec)
# `@dataclass` resout ses annotations via sys.modules[cls.__module__] : le
# module doit etre enregistre AVANT exec_module (sinon AttributeError sur
# None.__dict__).
sys.modules[_spec.name] = mod
_spec.loader.exec_module(mod)

NOW = datetime(2026, 10, 23, 15, 0, tzinfo=timezone.utc)
LABEL = "coursia-linux"


def _iso(minutes_ago: float) -> str:
    return (NOW - timedelta(minutes=minutes_ago)).isoformat().replace("+00:00", "Z")


def _run(rid: int, minutes_ago: float, name: str = "wf") -> dict:
    return {"id": rid, "name": name, "run_number": rid,
            "created_at": _iso(minutes_ago)}


def _job(jid: int, status: str, minutes_ago: float,
         label: str = LABEL, name: str = "job") -> dict:
    return {"id": jid, "name": name, "labels": [label],
            "status": status, "created_at": _iso(minutes_ago)}


class FakeApi:
    """Routeur d'API : rend les listings, les jobs et les runs directs."""

    def __init__(self, queued=(), in_progress=(), jobs=None,
                 direct=None, fail_on=(), malformed=()):
        self.queued = list(queued)
        self.in_progress = list(in_progress)
        self.jobs = jobs or {}          # run_id -> list[job]
        self.direct = direct or {}      # run_id -> status
        self.fail_on = set(fail_on)     # "queued" | "in_progress" | "jobs"
        # Statuts dont le listing revient en TABLEAU (JSON valide, non-dict) :
        # `_gh_json` ne le compte PAS comme echec -- seul listing_failed le
        # trace (temoin #22234).
        self.malformed = set(malformed)
        self.calls: list[str] = []
        self.job_reads: list[int] = []

    def __call__(self, args, token=None, stats=None):
        url = args[0]
        self.calls.append(url)
        if stats is not None:
            stats.calls += 1

        def fail(why: str):
            if stats is not None:
                stats.record(url, 1, why)
            return None

        if "/jobs?filter=latest" in url:
            rid = int(url.rsplit("/", 2)[-2])
            self.job_reads.append(rid)
            if "jobs" in self.fail_on:
                return fail("API rate limit exceeded")
            return {"jobs": self.jobs.get(rid, [])}
        if "status=queued" in url:
            if "queued" in self.fail_on:
                return fail("503 Service Unavailable")
            if "queued" in self.malformed:
                return [{"id": 1, "created_at": _iso(40)}]
            page = 1 if "page=1" in url else 2
            runs = self.queued if page == 1 else []
            return {"total_count": len(self.queued), "workflow_runs": runs}
        if "status=in_progress" in url:
            if "in_progress" in self.fail_on:
                return fail("502 Bad Gateway")
            if "in_progress" in self.malformed:
                return [{"id": 2, "created_at": _iso(5)}]
            page = 1 if "page=1" in url else 2
            runs = self.in_progress if page == 1 else []
            return {"total_count": len(self.in_progress), "workflow_runs": runs}
        if "/actions/runs/" in url:
            rid = int(url.rsplit("/", 1)[-1])
            return {"id": rid, "status": self.direct.get(rid, "queued")}
        raise AssertionError(f"endpoint inattendu : {url}")


def _patch(monkeypatch, api):
    monkeypatch.setattr(mod, "_gh_json", api)
    return api


def _fetch(api, **kwargs):
    kwargs.setdefault("window_max_minutes", 360.0)
    return mod.fetch_starvation("o/r", LABEL, 15.0, now=NOW, **kwargs)


# --- 1. Comptage et nommage des echecs -------------------------------------

def test_gh_json_compte_et_nomme_un_echec(monkeypatch):
    def fake_run(cmd, **kwargs):
        return subprocess.CompletedProcess(
            cmd, 1, stdout="", stderr="API rate limit exceeded for installation\n")

    monkeypatch.setattr(mod.subprocess, "run", fake_run)
    stats = mod.CallStats()
    assert mod._gh_json(["repos/o/r/actions/runs?status=queued"], stats=stats) is None
    assert stats.calls == 1
    assert stats.failed == 1
    endpoint, code, message = stats.failures[0]
    assert "actions/runs" in endpoint
    assert code == 1
    assert "rate limit" in message
    assert "rate limit" in stats.examples()


def test_gh_json_compte_aussi_une_sortie_vide_ou_non_json(monkeypatch):
    def vide(cmd, **kwargs):
        return subprocess.CompletedProcess(cmd, 0, stdout="  ", stderr="")

    monkeypatch.setattr(mod.subprocess, "run", vide)
    stats = mod.CallStats()
    assert mod._gh_json(["x"], stats=stats) is None
    assert stats.failures[0][2] == "stdout vide"

    def tronque(cmd, **kwargs):
        return subprocess.CompletedProcess(cmd, 0, stdout="{pas du json", stderr="")

    monkeypatch.setattr(mod.subprocess, "run", tronque)
    stats = mod.CallStats()
    assert mod._gh_json(["x"], stats=stats) is None
    assert stats.failures[0][2] == "stdout non-JSON"


def test_un_passage_troue_ne_conclut_pas_starvation(monkeypatch):
    """Le defaut fondateur : « AUCUN job in_progress » sur une lecture trouee."""
    api = _patch(monkeypatch, FakeApi(
        queued=[_run(1, 40), _run(2, 50)],
        in_progress=[],
        jobs={1: [_job(11, "queued", 39)], 2: [_job(21, "queued", 49)]},
        fail_on={"jobs"},
    ))
    st = _fetch(api)
    assert st.stats.failed > 0
    # Les deux runs ont ete lus, les duex appels ont echoue : rien d'observe.
    assert st.starved == []
    assert st.complete is False

    v = mod.evaluate(mod.RunnerInventory(online=["a", "b"]), st, 2)
    assert v.status == "ERROR"
    assert any(e.startswith("LECTURE API INCOMPLETE") for e in v.errors), v.errors
    assert not any(e.startswith("STARVATION") for e in v.errors), v.errors


def test_absence_non_prouvee_d_in_progress_est_un_warning_pas_un_rouge(
    monkeypatch,
):
    """Queued affame observe, mais la passe in_progress a echoue."""
    api = _patch(monkeypatch, FakeApi(
        queued=[_run(1, 40)], in_progress=[],
        jobs={1: [_job(11, "queued", 39)]},
        fail_on={"in_progress"},
    ))
    st = _fetch(api)
    assert len(st.starved) == 1
    assert st.listing_failed == {"in_progress"}

    v = mod.evaluate(mod.RunnerInventory(online=["a", "b"]), st, 2)
    assert any(e.startswith("LECTURE API INCOMPLETE") for e in v.errors)
    assert any("NON CONCLU" in w for w in v.warnings), v.warnings
    assert not any(e.startswith("STARVATION") for e in v.errors)


def test_un_passage_complet_conclut_starvation(monkeypatch):
    api = _patch(monkeypatch, FakeApi(
        queued=[_run(1, 40)], in_progress=[],
        jobs={1: [_job(11, "queued", 39)]},
    ))
    st = _fetch(api)
    assert st.complete is True
    v = mod.evaluate(mod.RunnerInventory(online=["a", "b"]), st, 2)
    assert v.status == "ERROR"
    assert any(e.startswith("STARVATION") for e in v.errors)


# --- 2. Bornes de cout -----------------------------------------------------

def test_les_runs_queued_trop_jeunes_ne_coutent_aucun_appel_jobs(monkeypatch):
    """Un job ne peut pas etre plus vieux que son run : sous le seuil, rien a lire."""
    api = _patch(monkeypatch, FakeApi(
        queued=[_run(i, 5) for i in range(1, 6)],
        jobs={i: [_job(100 + i, "queued", 4)] for i in range(1, 6)},
    ))
    st = _fetch(api)
    assert st.skipped_young == 5
    assert st.job_reads == 0
    assert api.job_reads == []
    assert st.starved == []


def test_le_budget_borne_les_lectures_et_les_prend_du_plus_vieux(monkeypatch):
    # run_id 1 = le plus vieux (120 min), 10 = le plus recent (30 min).
    queued = [_run(i, 130 - 10 * i) for i in range(1, 11)]
    api = _patch(monkeypatch, FakeApi(
        queued=queued,
        jobs={i: [_job(100 + i, "queued", 130 - 10 * i)] for i in range(1, 11)},
    ))
    st = _fetch(api, job_read_budget=3)
    assert st.job_reads == 3
    assert sorted(api.job_reads) == [1, 2, 3], api.job_reads
    assert len(st.budget_unread) == 7
    v = mod.evaluate(mod.RunnerInventory(online=["a", "b"]), st, 2)
    assert any(w.startswith("BUDGET DE LECTURE") for w in v.warnings), v.warnings


def test_l_echantillon_in_progress_borne_les_lectures(monkeypatch):
    api = _patch(monkeypatch, FakeApi(
        in_progress=[_run(1000 + i, 1 + i) for i in range(40)],
        jobs={1000 + i: [_job(9000 + i, "in_progress", 1)] for i in range(40)},
    ))
    st = _fetch(api, in_progress_sample=5)
    assert len(api.job_reads) == 5
    assert st.in_progress_unread == 35
    assert len(st.in_progress) == 5


def test_le_budget_global_couvre_aussi_l_echantillon_in_progress(monkeypatch):
    """Les deux passes partagent le meme budget : pas de depassement en cumul."""
    api = _patch(monkeypatch, FakeApi(
        queued=[_run(1, 40)],
        in_progress=[_run(1000 + i, 1) for i in range(10)],
        jobs={1: [_job(11, "queued", 39)],
              1000: [_job(9000, "in_progress", 1)]},
    ))
    st = _fetch(api, job_read_budget=2, in_progress_sample=20)
    assert st.job_reads == 2
    assert len(api.job_reads) == 2


# --- 2bis. Budget epuise / listing illisible : jamais de conclusion
#            fabriquee sur un angle mort (#22234) ---------------------------

def test_budget_epuise_par_la_file_queued_ne_fabrique_pas_un_starvation(
    monkeypatch,
):
    """Temoin du dossier #22234 : 3 affames lus (budget 3 entierement consomme
    par la passe queued), 2 runs in_progress sains JAMAIS regardes (sample=0).
    L'ancien evaluate lisait ce silence comme « AUCUN job in_progress » et
    rendait ERROR STARVATION sur une file en train de drainer."""
    api = _patch(monkeypatch, FakeApi(
        queued=[_run(i, 40 + i) for i in range(1, 4)],
        in_progress=[_run(1000 + i, 5) for i in range(2)],
        jobs={**{i: [_job(100 + i, "queued", 39 + i)] for i in range(1, 4)},
              **{1000 + i: [_job(9000 + i, "in_progress", 4)] for i in range(2)}},
    ))
    st = _fetch(api, job_read_budget=3, in_progress_sample=20)
    assert len(st.starved) == 3
    assert st.in_progress == []           # sample=0 : jamais lus...
    assert st.in_progress_unread == 2     # ...mais traces comme tels

    v = mod.evaluate(mod.RunnerInventory(online=["a", "b"]), st, 2)
    assert not any(e.startswith("STARVATION") for e in v.errors), v.errors
    assert any("NON CONCLU" in w and "hors echantillon" in w
               for w in v.warnings), v.warnings
    assert v.status == "OK"


def test_budget_epuise_sans_run_in_progress_conclut_starvation(monkeypatch):
    """Controle negatif : le NON CONCLU ne protege que l'absence NON LUE.
    Listing in_progress lu et VIDE (aucun run dans la fenetre) -> l'absence
    est etablie, le vrai positif reste un rouge."""
    api = _patch(monkeypatch, FakeApi(
        queued=[_run(i, 40 + i) for i in range(1, 4)],
        in_progress=[],
        jobs={i: [_job(100 + i, "queued", 39 + i)] for i in range(1, 4)},
    ))
    st = _fetch(api, job_read_budget=3)
    assert len(st.starved) == 3
    assert st.in_progress_unread == 0
    assert st.complete is True

    v = mod.evaluate(mod.RunnerInventory(online=["a", "b"]), st, 2)
    assert v.status == "ERROR"
    assert any(e.startswith("STARVATION") for e in v.errors), v.errors


def test_listing_rendu_en_tableau_ne_rend_pas_ok(monkeypatch):
    """Temoin #22234 : le listing queued revient en TABLEAU -- JSON valide,
    donc aucun echec d'appel compte (`stats.failed == 0`), seul
    `listing_failed` le trace. L'ancien evaluate rendait OK sur une file
    jamais lue (fail-open)."""
    api = _patch(monkeypatch, FakeApi(
        queued=[_run(1, 40)],
        in_progress=[],
        jobs={1: [_job(11, "queued", 39)]},
        malformed={"queued"},
    ))
    st = _fetch(api)
    assert st.listing_failed == {"queued"}
    assert st.stats.failed == 0
    assert st.complete is False
    assert st.starved == []

    v = mod.evaluate(mod.RunnerInventory(online=["a", "b"]), st, 2)
    assert any(e.startswith("LISTING INCOMPLET") for e in v.errors), v.errors
    assert v.status == "ERROR"


def test_listing_in_progress_illisible_ne_fabrique_pas_un_starvation(
    monkeypatch,
):
    """Meme famille, sens STARVATION : des affames lus + le listing
    in_progress illisible (tableau) -- l'absence de job en cours n'est pas
    etablie, le rouge STARVATION ne doit pas partir sur cet angle mort."""
    api = _patch(monkeypatch, FakeApi(
        queued=[_run(1, 40)],
        in_progress=[_run(1000, 5)],
        jobs={1: [_job(11, "queued", 39)],
              1000: [_job(9000, "in_progress", 4)]},
        malformed={"in_progress"},
    ))
    st = _fetch(api)
    assert len(st.starved) == 1
    assert st.in_progress == []
    assert st.listing_failed == {"in_progress"}
    assert st.stats.failed == 0

    v = mod.evaluate(mod.RunnerInventory(online=["a", "b"]), st, 2)
    assert not any(e.startswith("STARVATION") for e in v.errors), v.errors
    assert any("NON CONCLU" in w and "illisible" in w
               for w in v.warnings), v.warnings
    assert any(e.startswith("LISTING INCOMPLET") for e in v.errors), v.errors


# --- 3. Restriction a un workflow -----------------------------------------

def test_workflow_restreint_le_listing_a_son_endpoint(monkeypatch):
    api = _patch(monkeypatch, FakeApi(queued=[], in_progress=[]))
    _fetch(api, workflow="pr-gate.yml")
    assert api.calls, "aucun appel"
    assert all("/actions/workflows/pr-gate.yml/runs" in c for c in api.calls), \
        api.calls


def test_sans_workflow_le_listing_reste_depot_entier(monkeypatch):
    api = _patch(monkeypatch, FakeApi(queued=[], in_progress=[]))
    _fetch(api)
    assert all("/actions/runs?status=" in c for c in api.calls), api.calls


# --- 4. Regression : la semantique « observation recente gagne » ----------

def test_un_run_devenu_terminal_purge_ses_entrees(monkeypatch):
    api = _patch(monkeypatch, FakeApi(
        queued=[_run(1, 40)], in_progress=[],
        jobs={1: [_job(11, "queued", 39)]},
        direct={1: "completed"},
    ))
    st = _fetch(api)
    assert st.starved == []


def test_le_payload_json_expose_les_compteurs(monkeypatch, capsys):
    api = _patch(monkeypatch, FakeApi(queued=[_run(1, 5)]))
    st = _fetch(api)
    v = mod.evaluate(mod.RunnerInventory(online=["a", "b"]), st, 2)
    assert "appels gh" in " ".join(v.notes)
    assert st.stats.calls > 0
    assert st.skipped_young == 1


# --- 5. Label inconnu != extinction (#22215, mesure du 2026-10-23) ---------

def test_un_label_absent_de_tout_runner_est_un_warning_pas_une_extinction(
    monkeypatch,
):
    """`coursia-lean` a rougi « superviseur(s) mort(s) ? » pendant 24 h.

    Mesure du 2026-10-23 : 40 runners online, aucun ne porte `coursia-lean`,
    et plus aucun workflow de main ne route vers ce label. Le pool a ete
    migre, la sonde est restee -- le rouge permanent que la garde anti-FP
    du predicat STARVATION interdit ailleurs.
    """
    api = _patch(monkeypatch, FakeApi(queued=[], in_progress=[]))
    st = _fetch(api)
    v = mod.evaluate(mod.RunnerInventory(), st, 1, label="coursia-lean")
    assert v.errors == [], v.errors
    assert any(w.startswith("LABEL INCONNU") for w in v.warnings), v.warnings
    assert v.status == "OK"


def test_un_label_dont_les_runners_sont_tous_offline_reste_une_extinction():
    v = mod.evaluate(mod.RunnerInventory(offline=["host-1", "host-2"]),
                     mod.Starvation(), 1, label="coursia-linux")
    assert any(e.startswith("EXTINCTION") for e in v.errors), v.errors
    assert not any(w.startswith("LABEL INCONNU") for w in v.warnings)
    assert v.status == "ERROR"


# --- 6. Predicat EXTINCTION/STARVATION sur les etats mesures -----------------
#
# Ces cinq cas viennent de PR #22200 (#22183), qui les portait dans son propre
# exemplaire de ce fichier. Deux PR ouvertes de la meme lane sur le meme
# nouveau fichier se seraient affrontees au merge : le fichier appartient a la
# PR qui modifie l'organe, et #22200 en garde la sonde (le workflow).

_WAITER = "coursia-waiter"
_HOST = "myia-ai-01-wsl"


def _online(n: int) -> list[str]:
    return [f"{_HOST}-{i}" for i in range(1, n + 1)]


def _pr_gate_job(run_id: int, age_min: float, status: str = "queued") -> mod.JobRow:
    return mod.JobRow(
        workflow="PR gate",
        run_number=run_id,
        run_id=run_id,
        job_name="gate",
        status=status,
        age_min=age_min,
    )


def test_cas_2026_10_23_extinction_et_starvation():
    """0 online + 126 jobs PR gate queued > 2 h + 0 in_progress -> 2 erreurs."""
    inv = mod.RunnerInventory(online=[], offline=_online(16))
    st = mod.Starvation(
        starved=[_pr_gate_job(90000 + i, 130.0 + (i % 400)) for i in range(126)],
        in_progress=[],
    )
    v = mod.evaluate(inv, st, warn_floor=2, label=_WAITER)
    assert v.status == "ERROR"
    assert any("EXTINCTION" in e for e in v.errors)
    starv = [e for e in v.errors if "STARVATION" in e]
    assert starv, "STARVATION doit tirer : file qui ne draine pas"
    assert "126" in starv[0] and "PR gate" in starv[0]


def test_pool_vivant_file_profonde_ok():
    """16 slots online, queue > seuil MAIS des jobs in_progress -> OK."""
    inv = mod.RunnerInventory(online=_online(16), offline=[])
    st = mod.Starvation(
        starved=[_pr_gate_job(90000 + i, 200.0) for i in range(126)],
        in_progress=[_pr_gate_job(90126, 10.0, status="in_progress")],
    )
    v = mod.evaluate(inv, st, warn_floor=2, label=_WAITER)
    assert v.status == "OK"
    assert not v.errors, f"une file qui draine ne rougit pas : {v.errors}"


def test_pool_vivant_queue_vide_ok():
    inv = mod.RunnerInventory(online=_online(16), offline=[])
    v = mod.evaluate(inv, mod.Starvation(), warn_floor=2, label=_WAITER)
    assert v.status == "OK"
    assert not v.errors


def test_perte_partielle_warning_pas_erreur():
    """15 des 16 slots online avec un floor au-dessus -> warning, pas d'erreur.

    (Le floor est une borne : 15 online passe sans avertissement au floor 2 --
    c'est le cas nominal du pool de 16 avec un slot en redemarrage.)
    """
    inv = mod.RunnerInventory(online=_online(15), offline=[f"{_HOST}-16"])
    v = mod.evaluate(inv, mod.Starvation(), warn_floor=16, label=_WAITER)
    assert v.status == "OK"
    assert any("perte partielle" in w for w in v.warnings)


def test_sans_pat_pas_extinction_mais_starvation_gardee():
    """Inventaire non lisible : pas d'EXTINCTION (on ne sait pas), mais le
    symptome STARVATION tire quand meme -- degradation propre du docstring."""
    inv = mod.InventoryUnavailable(reason="RUNNERS_READ_PAT absent (test)")
    st = mod.Starvation(starved=[_pr_gate_job(90000, 300.0)], in_progress=[])
    v = mod.evaluate(inv, st, warn_floor=2, label=_WAITER)
    assert v.status == "ERROR"
    assert not any("EXTINCTION" in e for e in v.errors)
    assert any("STARVATION" in e for e in v.errors)
