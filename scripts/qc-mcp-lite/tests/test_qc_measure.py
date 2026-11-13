"""Tests de qc_measure.py — plan, reprise idempotente, lecture, cadenceur.

Aucun reseau : la passerelle est un faux cloud QC en memoire dont la
semantique est calquee sur l'API v2 telle qu'observee dans server.py et les
scripts de mesure (rejet des doublons de nom, compilation asynchrone,
backtest asynchrone, completed=true a la fin). L'horloge et le sleep du
cadenceur sont fictifs : le temps avance par les attentes elles-memes.
"""

import hashlib
import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).parent.parent))

from qc_measure import (
    DEFAULT_MAX_CALLS_PER_MIN,
    MIN_POLL_INTERVAL,
    PlanError,
    Scheduler,
    ThrottledGateway,
    build_parser,
    load_plan,
    normaliser_statistiques,
    read_measure,
    render_table,
    run_measure,
    save_state,
    statistiques_vides,
    status_measure,
    write_plan,
)

RATE_WINDOW = 60.0


# ─── Faux cloud QC en memoire ──────────────────────────────────────────


def stats_defaut() -> dict:
    """Statistiques realistes (modelees sur une reponse /backtests/read)."""
    return {
        "Total Orders": "318",
        "Average Win": "0.56%",
        "Average Loss": "-0.41%",
        "Compounding Annual Return": "8.413%",
        "Drawdown": "14.900%",
        "Expectancy": "0.074",
        "Net Profit": "76.088%",
        "Sharpe Ratio": "0.35",
        "Sortino Ratio": "0.48",
        "Probabilistic Sharpe Ratio": "1.719%",
        "Loss Rate": "45%",
        "Win Rate": "55%",
        "Profit-Loss Ratio": "1.36",
        "Alpha": "0.021",
        "Beta": "0.62",
        "Annual Standard Deviation": "0.119",
        "Information Ratio": "0.31",
    }


class FakeCloud:
    """Cloud QC en memoire : projets, fichiers, compilations, backtests.

    - creation de projet/fichier/backtest deja nomme -> RuntimeError (comme
      la garde success:false du serveur) ;
    - compilation : BuildSuccess apres 2 lectures ;
    - backtest : completed=True et statistiques apres 3 lectures.
    """

    def __init__(self, stats_factory=stats_defaut, lectures_pour_fin=3):
        self.projects: dict[int, dict] = {}
        self.compiles: dict[str, dict] = {}
        self.backtests: dict[str, dict] = {}
        self.stats_factory = stats_factory
        self.lectures_pour_fin = lectures_pour_fin
        self.appels = {
            "create_project": 0,
            "create_file": 0,
            "update_file_contents": 0,
            "create_compile": 0,
            "create_backtest": 0,
        }
        self.journal: list[tuple[str, str]] = []

    def seed_project(self, pid, name, files=None, language="Py", org=""):
        self.projects[pid] = {
            "projectId": pid,
            "name": name,
            "language": language,
            "organizationId": org,
            "files": dict(files or {}),
        }

    def seed_backtest(self, pid, name, bid, completed=False, stats=None,
                      error=None):
        self.backtests[bid] = {
            "projectId": pid,
            "name": name,
            "backtestId": bid,
            "status": "Completed." if completed else "Running",
            "progress": 1.0 if completed else 0.0,
            "completed": completed,
            "statistics": stats if stats is not None else (
                self.stats_factory() if completed else {}
            ),
            "runtimeStatistics": {},
            "error": error,
            "lectures": 0,
        }

    def gateway(self):
        return FakeGateway(self)


class FakeGateway:
    """Passerelle vers le faux cloud : meme interface que ServerGateway."""

    def __init__(self, cloud: FakeCloud):
        self._cloud = cloud

    def list_projects(self, name_contains: str = "") -> dict:
        filtre = (name_contains or "").lower()
        projets = [
            {
                "projectId": p["projectId"],
                "name": p["name"],
                "organizationId": p["organizationId"],
            }
            for p in self._cloud.projects.values()
            if filtre in p["name"].lower()
        ]
        return {"count": len(projets), "total": len(projets), "projects": projets}

    def create_project(self, name, language="Py", organization_id=None) -> dict:
        self._cloud.appels["create_project"] += 1
        self._cloud.journal.append(("create_project", name))
        if any(p["name"] == name for p in self._cloud.projects.values()):
            raise RuntimeError("QC API rejected the request: Project name already exists")
        pid = 1000 + self._cloud.appels["create_project"]
        self._cloud.seed_project(pid, name, language=language,
                                 org=organization_id or "")
        return {"projectId": pid, "name": name, "organizationId": organization_id or ""}

    def read_project(self, project_id: int) -> dict:
        projet = self._cloud.projects[project_id]
        return {
            "projectId": project_id,
            "name": projet["name"],
            "organizationId": projet["organizationId"],
            "files": [
                {"name": nom, "size": len(contenu)}
                for nom, contenu in projet["files"].items()
            ],
        }

    def read_file(self, project_id: int, name: str) -> dict:
        projet = self._cloud.projects[project_id]
        return {"name": name, "content": projet["files"].get(name, "")}

    def create_file(self, project_id: int, name: str, content: str) -> dict:
        self._cloud.appels["create_file"] += 1
        self._cloud.journal.append(("create_file", name))
        projet = self._cloud.projects[project_id]
        if name in projet["files"]:
            raise RuntimeError("QC API rejected the request: file exists")
        projet["files"][name] = content
        return {"success": True, "name": name}

    def update_file_contents(self, project_id: int, name: str, content: str) -> dict:
        self._cloud.appels["update_file_contents"] += 1
        self._cloud.journal.append(("update_file_contents", name))
        self._cloud.projects[project_id]["files"][name] = content
        return {"success": True, "name": name}

    def create_compile(self, project_id: int) -> dict:
        self._cloud.appels["create_compile"] += 1
        self._cloud.journal.append(("create_compile", ""))
        cid = f"c{self._cloud.appels['create_compile']}"
        self._cloud.compiles[cid] = {"projectId": project_id, "lectures": 0}
        return {"compileId": cid, "state": "InQueue"}

    def read_compile(self, project_id: int, compile_id: str) -> dict:
        compile_ = self._cloud.compiles[compile_id]
        compile_["lectures"] += 1
        etat = "BuildSuccess" if compile_["lectures"] >= 2 else "InQueue"
        return {"compileId": compile_id, "state": etat, "errors": []}

    def create_backtest(self, project_id, compile_id, backtest_name,
                        parameters=None) -> dict:
        self._cloud.appels["create_backtest"] += 1
        self._cloud.journal.append(("create_backtest", backtest_name))
        if any(
            b["projectId"] == project_id and b["name"] == backtest_name
            for b in self._cloud.backtests.values()
        ):
            raise RuntimeError(
                "QC API rejected the request: Backtest name already exists"
            )
        bid = f"bt{100 + self._cloud.appels['create_backtest']}"
        self._cloud.seed_backtest(project_id, backtest_name, bid)
        return {"backtestId": bid, "projectId": project_id, "status": "In Queue"}

    def list_backtests(self, project_id: int) -> dict:
        backtests = [
            {
                "backtestId": b["backtestId"],
                "name": b["name"],
                "status": b["status"],
            }
            for b in self._cloud.backtests.values()
            if b["projectId"] == project_id
        ]
        return {"count": len(backtests), "backtests": backtests}

    def read_backtest(self, project_id: int, backtest_id: str) -> dict:
        bt = self._cloud.backtests[backtest_id]
        self._cloud.journal.append(("read_backtest", backtest_id))
        bt["lectures"] += 1
        if not bt["completed"]:
            if bt["lectures"] >= self._cloud.lectures_pour_fin:
                if bt.get("error"):
                    bt["status"] = "Runtime Error"
                else:
                    bt["completed"] = True
                    bt["status"] = "Completed."
                    bt["progress"] = 1.0
                    if not bt["statistics"]:
                        bt["statistics"] = self._cloud.stats_factory()
            else:
                bt["progress"] = min(0.99, 0.33 * bt["lectures"])
        return {
            cle: valeur
            for cle, valeur in bt.items()
            if cle not in ("lectures", "projectId", "name")
        }


class SessionCoupee(BaseException):
    """Simulation d'une coupure de session : echappe aux except Exception."""


class CoupeApres:
    """Passerelle qui leve SessionCoupee au-dela de limite appels reussis."""

    def __init__(self, inner, limite: int):
        self._inner = inner
        self._limite = limite
        self._compteur = 0

    def __getattr__(self, name):
        attr = getattr(self._inner, name)
        if not callable(attr):
            return attr

        def appel(*args, **kwargs):
            self._compteur += 1
            if self._compteur > self._limite:
                raise SessionCoupee(f"session coupee avant l'appel {self._compteur}")
            return attr(*args, **kwargs)

        return appel


class HorlogeFictive:
    def __init__(self):
        self.t = 1000.0

    def __call__(self) -> float:
        return self.t


class SommeilFictif:
    """Sleep qui avance l'horloge : les attentes durent, le test non."""

    def __init__(self, horloge: HorlogeFictive):
        self.horloge = horloge
        self.durees: list[float] = []

    def __call__(self, duree: float) -> None:
        self.durees.append(duree)
        self.horloge.t += duree


def scheduler_fictif(horloge, sommeil, max_calls=DEFAULT_MAX_CALLS_PER_MIN):
    return Scheduler(max_calls=max_calls, window=RATE_WINDOW,
                     clock=horloge, sleep=sommeil)


def duo_horloge():
    """Horloge fictive + sleep fictif couple (les attentes font avancer
    l'horloge : aucun temps effectif ne s'ecoule dans les tests)."""
    horloge = HorlogeFictive()
    return horloge, SommeilFictif(horloge)


def ecrire_plan_mesure(tmp_path: Path, passes=None) -> Path:
    """Plan de mesure a deux fichiers dans tmp_path (deux passes par defaut)."""
    if passes is None:
        passes = [("base", {}), ("rapide", {"lookback": 10})]
    sources = tmp_path / "src"
    sources.mkdir(exist_ok=True)
    (sources / "main.py").write_text("# strategie\n", encoding="utf-8")
    (sources / "indicateurs.py").write_text("# indicateurs\n", encoding="utf-8")
    return write_plan(
        tmp_path / "mesures",
        label="vol",
        project_name="Mesure-Vol",
        files=[sources / "main.py", sources / "indicateurs.py"],
        passes=passes,
    )


# ─── plan : ecriture et validation ─────────────────────────────────────


class TestPlanEcriture:
    def test_ecrit_le_squelette_avec_empreintes(self, tmp_path):
        rundir = ecrire_plan_mesure(tmp_path)
        plan = load_plan(rundir)
        assert plan["project_name"] == "Mesure-Vol"
        assert plan["language"] == "Py"
        assert [f["name"] for f in plan["files"]] == [
            "main.py", "indicateurs.py"
        ]
        for entree in plan["files"]:
            assert len(entree["sha256"]) == 64
        assert [(p["name"], p["parameters"]) for p in plan["passes"]] == [
            ("base", {}), ("rapide", {"lookback": 10})
        ]
        # backtest_name par defaut = nom de la passe
        assert all(
            p["backtest_name"] == p["name"] for p in plan["passes"]
        )

    def test_refuse_d_ecraser_sans_force(self, tmp_path):
        rundir = ecrire_plan_mesure(tmp_path)
        with pytest.raises(PlanError, match="deja present"):
            write_plan(
                tmp_path / "mesures", label="vol", project_name="Autre",
                files=[tmp_path / "src" / "main.py"], passes=[("base", {})],
            )
        write_plan(
            tmp_path / "mesures", label="vol", project_name="Autre",
            files=[tmp_path / "src" / "main.py"], passes=[("base", {})],
            force=True,
        )
        assert load_plan(rundir)["project_name"] == "Autre"

    def test_refuse_un_fichier_absent(self, tmp_path):
        with pytest.raises(PlanError, match="introuvable"):
            write_plan(
                tmp_path, label="x", project_name="P",
                files=[tmp_path / "absent.py"], passes=[("base", {})],
            )


class TestPlanValidation:
    def _ecrire(self, tmp_path, plan: dict) -> Path:
        rundir = tmp_path / "r"
        rundir.mkdir()
        (rundir / "plan.json").write_text(
            json.dumps(plan, ensure_ascii=False), encoding="utf-8"
        )
        return rundir

    def _plan_valide(self, **surcharges) -> dict:
        plan = {
            "project_name": "P",
            "language": "Py",
            "organization_id": None,
            "files": [{"name": "main.py", "path": "main.py", "sha256": "a" * 64}],
            "passes": [{"name": "base", "backtest_name": "base",
                        "parameters": {}}],
        }
        plan.update(surcharges)
        return plan

    def test_refuse_sans_project_name(self, tmp_path):
        rundir = self._ecrire(tmp_path, self._plan_valide(project_name=""))
        with pytest.raises(PlanError, match="project_name"):
            load_plan(rundir)

    def test_refuse_langage_inconnu(self, tmp_path):
        rundir = self._ecrire(tmp_path, self._plan_valide(language="Rust"))
        with pytest.raises(PlanError, match="language"):
            load_plan(rundir)

    def test_refuse_sans_passe(self, tmp_path):
        rundir = self._ecrire(tmp_path, self._plan_valide(passes=[]))
        with pytest.raises(PlanError, match="passes"):
            load_plan(rundir)

    def test_refuse_passe_dupliquee(self, tmp_path):
        plan = self._plan_valide()
        plan["passes"].append(dict(plan["passes"][0]))
        rundir = self._ecrire(tmp_path, plan)
        with pytest.raises(PlanError, match="dupliquee"):
            load_plan(rundir)

    def test_refuse_parametres_non_dict(self, tmp_path):
        plan = self._plan_valide(
            passes=[{"name": "b", "parameters": [1, 2]}]
        )
        rundir = self._ecrire(tmp_path, plan)
        with pytest.raises(PlanError, match="dictionnaire"):
            load_plan(rundir)

    def test_refuse_fichier_sans_path(self, tmp_path):
        plan = self._plan_valide(
            files=[{"name": "main.py", "path": ""}]
        )
        rundir = self._ecrire(tmp_path, plan)
        with pytest.raises(PlanError, match="path"):
            load_plan(rundir)

    def test_refuse_plan_illisible(self, tmp_path):
        rundir = tmp_path / "r"
        rundir.mkdir()
        (rundir / "plan.json").write_text("{pas du json", encoding="utf-8")
        with pytest.raises(PlanError, match="illisible"):
            load_plan(rundir)

    def test_refuse_plan_absent(self, tmp_path):
        with pytest.raises(PlanError, match="introuvable"):
            load_plan(tmp_path / "nulle_part")


# ─── cadenceur ─────────────────────────────────────────────────────────


class TestScheduler:
    def test_jamais_plus_de_n_appels_par_fenetre(self):
        horloge, sommeil = duo_horloge()
        scheduler = scheduler_fictif(horloge, sommeil, max_calls=6)
        for _ in range(40):
            scheduler.acquire()
        historique = scheduler.history
        assert len(historique) == 40
        for debut in historique:
            fenetre = [t for t in historique if debut <= t < debut + RATE_WINDOW]
            assert len(fenetre) <= 6

    def test_le_cadenceur_attend_via_le_sleep_injectable(self):
        horloge, sommeil = duo_horloge()
        scheduler = scheduler_fictif(horloge, sommeil, max_calls=6)
        for _ in range(6):
            scheduler.acquire()
        assert sommeil.durees == []
        scheduler.acquire()  # 7e appel : la fenetre est saturee
        assert sommeil.durees and sommeil.durees[0] > 0
        assert len([t for t in scheduler.history
                    if scheduler.history[-1] - t < RATE_WINDOW]) <= 6


# ─── normalisation des statistiques ────────────────────────────────────


class TestNormalisation:
    def test_forme_brute_statistics(self):
        bt = {
            "statistics": stats_defaut(),
            "runtimeStatistics": {"Net Profit": "$59,745.60"},
        }
        stats = normaliser_statistiques(bt)
        assert stats["sharpe"] == "0.35"
        assert stats["cagr"] == "8.413%"
        assert stats["max_drawdown"] == "14.900%"
        assert stats["psr"] == "1.719%"
        assert stats["beta"] == "0.62"
        assert stats["win_rate"] == "55%"
        assert stats["orders"] == "318"

    def test_fallback_runtime_statistics(self):
        """statistics peut etre vide : runtimeStatistics porte des variantes
        ("CAGR" et non "Compounding Annual Return")."""
        bt = {
            "statistics": {},
            "runtimeStatistics": {
                "Sharpe Ratio": "1.1",
                "CAGR": "12.3%",
                "Beta": "0.4",
                "Win Rate": "60%",
            },
        }
        stats = normaliser_statistiques(bt)
        assert stats["sharpe"] == "1.1"
        assert stats["cagr"] == "12.3%"
        assert stats["beta"] == "0.4"
        assert stats["win_rate"] == "60%"

    def test_forme_camelcase_extraite(self):
        """Forme normalisee par _extract_stats du serveur (read_backtest)."""
        bt = {
            "statistics": {
                "sharpeRatio": "1.5",
                "compoundingAnnualReturn": "15%",
                "drawdown": "10%",
                "probabilisticSharpeRatio": "0.9",
            },
            "totalOrders": 42,
        }
        stats = normaliser_statistiques(bt)
        assert stats["sharpe"] == "1.5"
        assert stats["cagr"] == "15%"
        assert stats["max_drawdown"] == "10%"
        assert stats["psr"] == "0.9"
        assert stats["orders"] == "42"

    def test_ordres_total_orders_haut_niveau_en_repli(self):
        """Regression du serveur : totalOrders vaut null sur un backtest
        termine, statistics['Total Orders'] fait foi ; le champ de haut
        niveau n'est qu'un repli."""
        bt = {
            "totalOrders": None,
            "statistics": {"Total Orders": "318"},
        }
        assert normaliser_statistiques(bt)["orders"] == "318"
        bt_sans_stats = {"totalOrders": 7, "statistics": {}}
        assert normaliser_statistiques(bt_sans_stats)["orders"] == "7"

    def test_statistiques_vides_detectees(self):
        assert statistiques_vides(normaliser_statistiques({}))
        assert statistiques_vides(
            normaliser_statistiques({"statistics": {"Sharpe Ratio": "-"}})
        )
        # Un run termine sans ordre garde des valeurs honnetes : pas vide.
        assert not statistiques_vides(
            normaliser_statistiques(
                {"statistics": {"Total Orders": "0", "Net Profit": "0.000%"}}
            )
        )


# ─── run : execution complete, reprise, adoption ───────────────────────


class TestRun:
    def test_premiere_execution_complete(self, tmp_path, capsys):
        cloud = FakeCloud()
        rundir = ecrire_plan_mesure(tmp_path)
        horloge, sommeil = duo_horloge()
        scheduler = scheduler_fictif(horloge, sommeil)
        rc = run_measure(
            ThrottledGateway(cloud.gateway(), scheduler), scheduler, rundir,
            poll_interval=20.0, max_wait=3600.0,
        )
        assert rc == 0
        etat = json.loads((rundir / "state.json").read_text(encoding="utf-8"))
        assert etat["project_id"] == 1001
        assert etat["compile_state"] == "BuildSuccess"
        for passe in ("base", "rapide"):
            assert etat["passes"][passe]["statut"] == "terminee"
            assert etat["passes"][passe]["backtest_id"]
        # Les parametres de chaque passe ont bien transite vers l'API.
        assert cloud.backtests[
            etat["passes"]["rapide"]["backtest_id"]
        ]["name"] == "rapide"
        assert "terminee" in capsys.readouterr().out

    def test_reprise_apres_coupe_a_chaque_etape(self, tmp_path):
        """Pour CHAQUE budget d'appels avant coupure (1, 2, 3, ...), une
        session complete ensuite la mesure sans jamais recree un projet, un
        fichier ni un backtest deja note."""
        cloud = FakeCloud()
        rundir = ecrire_plan_mesure(tmp_path)
        horloge, sommeil = duo_horloge()
        budget, termine = 1, False
        for _ in range(150):
            scheduler = scheduler_fictif(horloge, sommeil)
            passerelle = ThrottledGateway(
                CoupeApres(cloud.gateway(), budget), scheduler
            )
            try:
                rc = run_measure(
                    passerelle, scheduler, rundir,
                    poll_interval=20.0, max_wait=3600.0,
                )
            except SessionCoupee:
                budget += 1
                continue
            if rc == 0:
                termine = True
                break
        assert termine, "la boucle de reprise n'a jamais termine la mesure"
        # Jamais de double : un projet, deux fichiers, deux backtests.
        assert cloud.appels["create_project"] == 1
        assert cloud.appels["create_file"] == 2
        assert cloud.appels["create_backtest"] == 2
        etat = json.loads((rundir / "state.json").read_text(encoding="utf-8"))
        assert all(p["statut"] == "terminee" for p in etat["passes"].values())

    def test_adoption_projet_et_backtest_par_nom(self, tmp_path, capsys):
        """Une session perdue a deja cree le projet et un backtest du bon
        nom : run les adopte au lieu de recree (anti-doublon)."""
        cloud = FakeCloud()
        cloud.seed_project(777, "Mesure-Vol",
                           files={"main.py": "# strategie\n"})
        cloud.seed_backtest(777, "base", "bt-existant-1")
        rundir = ecrire_plan_mesure(tmp_path)
        horloge, sommeil = duo_horloge()
        scheduler = scheduler_fictif(horloge, sommeil)
        rc = run_measure(
            ThrottledGateway(cloud.gateway(), scheduler), scheduler, rundir,
            poll_interval=20.0, max_wait=3600.0,
        )
        assert rc == 0
        assert cloud.appels["create_project"] == 0
        # base adopte ; rapide (nom absent) lance seul
        assert cloud.appels["create_backtest"] == 1
        etat = json.loads((rundir / "state.json").read_text(encoding="utf-8"))
        assert etat["project_id"] == 777
        assert etat["passes"]["base"]["backtest_id"] == "bt-existant-1"
        assert "adopte" in capsys.readouterr().out

    def test_fichier_modifie_avec_backtests_notes_refuse(self, tmp_path):
        cloud = FakeCloud()
        rundir = ecrire_plan_mesure(tmp_path)
        horloge, sommeil = duo_horloge()
        scheduler = scheduler_fictif(horloge, sommeil)
        run_measure(
            ThrottledGateway(cloud.gateway(), scheduler), scheduler, rundir,
            poll_interval=20.0, max_wait=3600.0,
        )
        # Le fichier local change apres la mesure.
        chemin = _resoudre_premier_fichier(rundir)
        chemin.write_text("# strategie modifiee\n", encoding="utf-8")
        with pytest.raises(Exception, match="nouveau label"):
            run_measure(
                ThrottledGateway(cloud.gateway(), scheduler), scheduler,
                rundir, poll_interval=20.0, max_wait=3600.0,
            )

    def test_fichier_modifie_avant_backtests_recompile(self, tmp_path):
        """Aucun backtest note : le changement de fichier est accepte et
        force une nouvelle compilation."""
        cloud = FakeCloud()
        rundir = ecrire_plan_mesure(tmp_path)
        chemin = _resoudre_premier_fichier(rundir)

        def sha(texte):
            return hashlib.sha256(texte.encode("utf-8")).hexdigest()

        # Etat main la main : projet note, fichiers envoyes, compile reussie,
        # aucune passe lancee.
        contenu = chemin.read_text(encoding="utf-8")
        cloud.seed_project(555, "Mesure-Vol",
                           files={"main.py": contenu,
                                  "indicateurs.py": "# indicateurs\n"})
        save_state(rundir, {
            "version": 1,
            "project_id": 555,
            "files": {"main.py": sha(contenu),
                      "indicateurs.py": sha("# indicateurs\n")},
            "compile_id": "ancien",
            "compile_state": "BuildSuccess",
            "passes": {
                "base": {"backtest_name": "base", "backtest_id": None,
                         "statut": "a_lancer", "erreur": None},
                "rapide": {"backtest_name": "rapide", "backtest_id": None,
                           "statut": "a_lancer", "erreur": None},
            },
        })
        cloud.compiles["ancien"] = {"projectId": 555, "lectures": 99}
        chemin.write_text("# strategie modifiee\n", encoding="utf-8")
        horloge, sommeil = duo_horloge()
        scheduler = scheduler_fictif(horloge, sommeil)
        rc = run_measure(
            ThrottledGateway(cloud.gateway(), scheduler), scheduler, rundir,
            poll_interval=20.0, max_wait=3600.0,
        )
        assert rc == 0
        assert cloud.appels["create_compile"] >= 1
        assert cloud.appels["update_file_contents"] == 1
        etat = json.loads((rundir / "state.json").read_text(encoding="utf-8"))
        assert etat["compile_id"] != "ancien"

    def test_parallel_deux_en_vol(self, tmp_path):
        """--parallel 2 : les deux backtests sont crees avant la premiere
        lecture de backtest (deux noeuds occupes simultanement)."""
        cloud = FakeCloud()
        rundir = ecrire_plan_mesure(tmp_path)
        horloge, sommeil = duo_horloge()
        scheduler = scheduler_fictif(horloge, sommeil)
        rc = run_measure(
            ThrottledGateway(cloud.gateway(), scheduler), scheduler, rundir,
            parallel=2, poll_interval=20.0, max_wait=3600.0,
        )
        assert rc == 0
        creates = [
            i for i, (type_, _) in enumerate(cloud.journal)
            if type_ == "create_backtest"
        ]
        premiere_lecture = next(
            i for i, (type_, _) in enumerate(cloud.journal)
            if type_ == "read_backtest"
        )
        assert len(creates) == 2
        assert max(creates) < premiere_lecture


def _resoudre_premier_fichier(rundir: Path) -> Path:
    plan = load_plan(rundir)
    return Path(plan["files"][0]["path"])


# ─── status ────────────────────────────────────────────────────────────


class TestStatus:
    def _apres_run(self, tmp_path):
        cloud = FakeCloud()
        rundir = ecrire_plan_mesure(tmp_path)
        horloge, sommeil = duo_horloge()
        scheduler = scheduler_fictif(horloge, sommeil)
        run_measure(
            ThrottledGateway(cloud.gateway(), scheduler), scheduler, rundir,
            poll_interval=20.0, max_wait=3600.0,
        )
        return cloud, rundir

    def test_status_local_sans_api(self, tmp_path, capsys):
        _, rundir = self._apres_run(tmp_path)
        assert status_measure(None, None, rundir) == 0
        sortie = capsys.readouterr().out
        assert "passe base : terminee" in sortie
        assert "passe rapide : terminee" in sortie
        assert "projet : 1001" in sortie

    def test_status_refresh_actualise_une_passe_lancee(self, tmp_path, capsys):
        cloud, rundir = self._apres_run(tmp_path)
        # Une nouvelle passe lancee mais non attendie : etat lance.
        etat = json.loads((rundir / "state.json").read_text(encoding="utf-8"))
        etat["passes"]["base"]["statut"] = "lancee"
        save_state(rundir, etat)
        horloge, sommeil = duo_horloge()
        scheduler = scheduler_fictif(horloge, sommeil)
        rc = status_measure(
            ThrottledGateway(cloud.gateway(), scheduler), scheduler, rundir,
            refresh=True,
        )
        assert rc == 0
        etat = json.loads((rundir / "state.json").read_text(encoding="utf-8"))
        assert etat["passes"]["base"]["statut"] == "terminee"
        assert "passe base : terminee" in capsys.readouterr().out


# ─── read ──────────────────────────────────────────────────────────────


class TestRead:
    def _mesure_prete(self, tmp_path, **kwargs_cloud):
        """Plan a une passe + etat complet ; les backtests du cloud sont
        pilotes par le test (completed/stats fixes, sans progression)."""
        cloud = FakeCloud(**kwargs_cloud)
        rundir = ecrire_plan_mesure(tmp_path, passes=[("base", {})])
        cloud.seed_project(888, "Mesure-Vol")
        save_state(rundir, {
            "version": 1,
            "project_id": 888,
            "files": {},
            "compile_id": "c1",
            "compile_state": "BuildSuccess",
            "passes": {
                "base": {"backtest_name": "base", "backtest_id": "bt-base",
                         "statut": "lancee", "erreur": None},
            },
        })
        return cloud, rundir

    def test_refuse_un_backtest_non_termine(self, tmp_path, capsys):
        cloud, rundir = self._mesure_prete(tmp_path, lectures_pour_fin=10**6)
        cloud.seed_backtest(888, "base", "bt-base")
        horloge, sommeil = duo_horloge()
        scheduler = scheduler_fictif(horloge, sommeil)
        rc = read_measure(
            ThrottledGateway(cloud.gateway(), scheduler), scheduler, rundir,
            poll_interval=20.0, max_wait=100.0,
        )
        assert rc == 1
        sortie = capsys.readouterr().out
        assert "pas termine" in sortie
        # Aucune statistique rendue : pas de tableau.
        assert "Sharpe" not in sortie

    def test_termine_avec_statistiques_vides_le_dit(self, tmp_path, capsys):
        def stats_vides():
            return {}

        cloud, rundir = self._mesure_prete(tmp_path, stats_factory=stats_vides)
        cloud.seed_backtest(888, "base", "bt-base", completed=True, stats={})
        horloge, sommeil = duo_horloge()
        scheduler = scheduler_fictif(horloge, sommeil)
        rc = read_measure(
            ThrottledGateway(cloud.gateway(), scheduler), scheduler, rundir,
            poll_interval=20.0, max_wait=100.0, retries=2,
        )
        assert rc == 1
        sortie = capsys.readouterr().out
        assert "statistiques vides" in sortie
        assert "2 relectures" in sortie
        # Le message tient lieu de valeur : pas de tableau a tirets.
        assert "|---" not in sortie

    def test_tableau_markdown_sur_reponse_realiste(self, tmp_path, capsys):
        cloud, rundir = self._mesure_prete(tmp_path)
        cloud.seed_backtest(888, "base", "bt-base", completed=True)
        horloge, sommeil = duo_horloge()
        scheduler = scheduler_fictif(horloge, sommeil)
        rc = read_measure(
            ThrottledGateway(cloud.gateway(), scheduler), scheduler, rundir,
            poll_interval=20.0, max_wait=100.0,
        )
        assert rc == 0
        sortie = capsys.readouterr().out
        for attendu in (
            "| Passe | Sharpe | CAGR | MaxDD | PSR | Beta | Ordres | Reussite"
            " | Backtest | Projet |",
            "| base | 0.35 | 8.413% | 14.900% | 1.719% | 0.62 | 318 | 55%"
            " | bt-base | 888 |",
        ):
            assert attendu in sortie

    def test_sortie_json(self, tmp_path, capsys):
        cloud, rundir = self._mesure_prete(tmp_path)
        cloud.seed_backtest(888, "base", "bt-base", completed=True)
        horloge, sommeil = duo_horloge()
        scheduler = scheduler_fictif(horloge, sommeil)
        rc = read_measure(
            ThrottledGateway(cloud.gateway(), scheduler), scheduler, rundir,
            as_json=True, poll_interval=20.0, max_wait=100.0,
        )
        assert rc == 0
        charge = json.loads(capsys.readouterr().out)
        assert charge["project_id"] == 888
        passe = charge["passes"][0]
        assert passe["passe"] == "base"
        assert passe["statistics"]["sharpe"] == "0.35"
        assert passe["statistics"]["orders"] == "318"

    def test_passe_sans_backtest_note(self, tmp_path, capsys):
        cloud, rundir = self._mesure_prete(tmp_path)
        etat = json.loads((rundir / "state.json").read_text(encoding="utf-8"))
        etat["passes"]["base"]["backtest_id"] = None
        save_state(rundir, etat)
        horloge, sommeil = duo_horloge()
        scheduler = scheduler_fictif(horloge, sommeil)
        rc = read_measure(
            ThrottledGateway(cloud.gateway(), scheduler), scheduler, rundir,
            poll_interval=20.0, max_wait=100.0,
        )
        assert rc == 1
        assert "pas de backtest note" in capsys.readouterr().out

    def test_backtest_en_erreur_rapporte(self, tmp_path, capsys):
        cloud, rundir = self._mesure_prete(tmp_path)
        cloud.seed_backtest(
            888, "base", "bt-base", completed=True,
            stats={}, error="Unsupported security type: Crypto",
        )
        horloge, sommeil = duo_horloge()
        scheduler = scheduler_fictif(horloge, sommeil)
        rc = read_measure(
            ThrottledGateway(cloud.gateway(), scheduler), scheduler, rundir,
            poll_interval=20.0, max_wait=100.0,
        )
        assert rc == 1
        assert "en erreur" in capsys.readouterr().out


# ─── tableau ───────────────────────────────────────────────────────────


class TestRenderTable:
    def test_colonnes_et_valeurs(self):
        tableau = render_table([
            {
                "passe": "base",
                "backtest_id": "bt1",
                "project_id": 42,
                "statistics": {
                    "sharpe": "1.2", "cagr": "10%", "max_drawdown": "5%",
                    "psr": "0.9", "beta": "0.5", "orders": "30",
                    "win_rate": "52%",
                },
            }
        ])
        lignes = tableau.splitlines()
        assert lignes[0].startswith("| Passe | Sharpe |")
        assert "| base | 1.2 | 10% | 5% | 0.9 | 0.5 | 30 | 52% | bt1 | 42 |" \
            in lignes[2]


# ─── CLI ───────────────────────────────────────────────────────────────


class TestCli:
    def test_intervalle_de_sondage_trop_bas_refuse(self):
        with pytest.raises(SystemExit):
            build_parser().parse_args(
                ["read", "x", "--poll-interval", str(MIN_POLL_INTERVAL - 1)]
            )

    def test_max_calls_hors_bornes_refuse(self):
        with pytest.raises(SystemExit):
            build_parser().parse_args(
                ["run", "x", "--max-calls-per-min", "11"]
            )
        with pytest.raises(SystemExit):
            build_parser().parse_args(
                ["run", "x", "--max-calls-per-min", "0"]
            )

    def test_parallel_hors_bornes_refuse(self):
        with pytest.raises(SystemExit):
            build_parser().parse_args(["run", "x", "--parallel", "0"])
