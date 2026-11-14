"""Outil generique de mesure de strategies QuantConnect sur QC Cloud.

Mesurer une strategie (la comparer a des temoins sur plusieurs jeux de
parametres) recommence chaque fois la meme plomberie : creer le projet,
envoyer les fichiers, compiler, lancer un backtest par passe, attendre la
fin, lire les statistiques, dresser le tableau. Les memes erreurs reviennent :
statistiques lues avant la fin du backtest, cles cherchees sous le mauvais
nom, backtests relances en double apres une coupure de session, limite de
debit depassee.

Cet outil factorise cette plomberie en une CLI a quatre sous-commandes :

- ``plan``   ecrit le squelette ``<workdir>/<label>/plan.json`` ;
- ``run``    declenche tout ce qui manque (projet, fichiers, compilation,
  backtests des passes non lancees) et note chaque etape faite dans
  ``state.json`` : une relance apres coupure ne recree ni projet ni backtest
  deja note ;
- ``status`` etat de chaque passe ;
- ``read``  lit chaque backtest, refuse les statistiques tant que l'API ne
  marque pas le backtest termine, normalise les cles et sort un tableau
  Markdown (ou ``--json``).

Le client REST et la lecture des identifiants viennent du serveur MCP du
dossier (``server.py``), par import : pas de second client HTTP, pas d'autre
facon de lire le jeton, et le jeton n'est jamais affiche.

Debit : la limite flotte est de 10 appels/min sur l'API QC, partagée par
tous les agents. L'outil passe par un cadenceur commun a tous ses appels,
6 appels/min au plus par defaut, et sonde au minimum toutes les 20 s.
"""

import argparse
import hashlib
import json
import os
import sys
import time
from collections import deque
from pathlib import Path
from typing import Callable, Optional

# Bornes de debit : la limite flotte (10 appels/min) est un plafond dur ;
# l'outil reste en dessous par defaut.
DEFAULT_MAX_CALLS_PER_MIN = 6
MIN_MAX_CALLS_PER_MIN = 1
MAX_MAX_CALLS_PER_MIN = 10
RATE_WINDOW = 60.0

# Un backtest tourne longtemps : on ne sonde pas plus vite que toutes les 20 s
# pour ne pas consommer la fenetre de debit des autres appels.
DEFAULT_POLL_INTERVAL = 30.0
MIN_POLL_INTERVAL = 20.0
DEFAULT_MAX_WAIT = 3600.0

# Un backtest termine peut avoir ses statistiques non encore remplies : on
# relit un nombre borne de fois avant de declarer les statistiques vides.
EMPTY_STATS_RETRIES = 3

LANGUAGES = ("Py", "C#")

STATUT_A_LANCER = "a_lancer"
STATUT_LANCEE = "lancee"
STATUT_TERMINEE = "terminee"
STATUT_ERREUR = "erreur"


class PlanError(ValueError):
    """plan.json absent, illisible ou invalide."""


class MeasureError(RuntimeError):
    """Blocage de la mesure (compilation echouee, incoherence etat/plan...)."""


# ─── Cadenceur ─────────────────────────────────────────────────────────


class Scheduler:
    """Cadenceur commun : au plus ``max_calls`` appels par fenetre glissante.

    Horloge et sleep injectables : les tests fournissent une horloge fictive
    avancee par le sleep fictif, si bien qu'aucune attente effective n'a lieu
    et que le respect de la fenetre se verifie sur l'historique des appels.
    """

    def __init__(
        self,
        max_calls: int = DEFAULT_MAX_CALLS_PER_MIN,
        window: float = RATE_WINDOW,
        clock: Callable[[], float] = time.monotonic,
        sleep: Callable[[float], None] = time.sleep,
    ) -> None:
        self.max_calls = int(max_calls)
        self.window = float(window)
        self._clock = clock
        self._sleep = sleep
        self._stamps: deque[float] = deque()
        # Historique complet (jamais elague) : preuve mesurable du respect
        # de la fenetre, consultable par les tests.
        self.history: list[float] = []

    def now(self) -> float:
        """Heure courante selon l'horloge injectee."""
        return self._clock()

    def acquire(self) -> float:
        """Reserve un creneau d'appel ; attend si la fenetre est saturee."""
        self._prune(self.now())
        while len(self._stamps) >= self.max_calls:
            attente = self._stamps[0] + self.window - self.now()
            if attente > 0:
                self._sleep(attente)
            self._prune(self.now())
        stamp = self.now()
        self._stamps.append(stamp)
        self.history.append(stamp)
        return stamp

    def wait(self, seconds: float) -> None:
        """Attente de sondage : passe par le sleep injectable."""
        self._sleep(max(0.0, float(seconds)))

    def _prune(self, now: float) -> None:
        horizon = now - self.window
        while self._stamps and self._stamps[0] <= horizon:
            self._stamps.popleft()


# ─── Passerelles vers l'API ────────────────────────────────────────────


class ServerGateway:
    """Passerelle par defaut : delegue au serveur MCP du dossier (server.py).

    Reutilise son client HTTP, son authentification (variables
    ``QC_API_USER_ID`` / ``QC_API_ACCESS_TOKEN``) et sa garde d'erreur
    (``success: false`` du corps releve en RuntimeError) : aucun second
    client, aucune relecture du jeton, jeton jamais affiche.
    """

    def __init__(self) -> None:
        import server  # import tardif : le module exige requests + mcp

        self._server = server

    def list_projects(self, name_contains: str = "") -> dict:
        return self._server.list_projects(name_contains)

    def create_project(
        self,
        name: str,
        language: str = "Py",
        organization_id: Optional[str] = None,
    ) -> dict:
        return self._server.create_project(name, language, organization_id)

    def read_project(self, project_id: int) -> dict:
        return self._server.read_project(project_id)

    def read_file(self, project_id: int, name: str) -> dict:
        return self._server.read_file(project_id, name)

    def create_file(self, project_id: int, name: str, content: str) -> dict:
        return self._server.create_file(project_id, name, content)

    def update_file_contents(
        self, project_id: int, name: str, content: str
    ) -> dict:
        return self._server.update_file_contents(project_id, name, content)

    def create_compile(self, project_id: int) -> dict:
        return self._server.create_compile(project_id)

    def read_compile(self, project_id: int, compile_id: str) -> dict:
        return self._server.read_compile(project_id, compile_id)

    def create_backtest(
        self,
        project_id: int,
        compile_id: str,
        backtest_name: str,
        parameters: Optional[dict] = None,
    ) -> dict:
        return self._server.create_backtest(
            project_id, compile_id, backtest_name, parameters
        )

    def list_backtests(self, project_id: int) -> dict:
        return self._server.list_backtests(project_id)

    def read_backtest(self, project_id: int, backtest_id: str) -> dict:
        """Lecture brute du backtest (dictionnaire ``backtest`` complet).

        ``read_backtest`` du serveur tronque les statistiques a six cles
        (Beta et Win Rate n'y figurent pas) : la lecture brute garde le
        dictionnaire ``statistics`` complet. C'est le meme client HTTP, la
        meme authentification et la meme garde d'erreur, pas un second
        client.
        """
        data = self._server._api_post(
            "/backtests/read",
            {"projectId": project_id, "backtestId": backtest_id},
        )
        return data.get("backtest", data)


class ThrottledGateway:
    """Enveloppe qui passe chaque appel de la passerelle par le cadenceur.

    Le cadenceur est commun a TOUS les appels (projets, fichiers,
    compilations, backtests) : aucun contournement possible en oubliant de
    throttler un appel quelque part.
    """

    def __init__(self, inner: object, scheduler: Scheduler) -> None:
        self._inner = inner
        self._scheduler = scheduler

    def __getattr__(self, name: str):
        attr = getattr(self._inner, name)
        if not callable(attr):
            return attr

        def appel(*args, **kwargs):
            self._scheduler.acquire()
            return attr(*args, **kwargs)

        return appel


# ─── Plan ──────────────────────────────────────────────────────────────


def _sha256(texte: str) -> str:
    return hashlib.sha256(texte.encode("utf-8")).hexdigest()


def write_plan(
    workdir: Path,
    *,
    label: str,
    project_name: str,
    files: list[Path],
    passes: list[tuple[str, dict]],
    language: str = "Py",
    organization_id: Optional[str] = None,
    force: bool = False,
) -> Path:
    """Ecrit le squelette ``<workdir>/<label>/plan.json``.

    Les empreintes sha256 des fichiers sont mesurees a l'ecriture du plan :
    elles documentent le code gele au moment de la mesure.
    """
    if not label or not isinstance(label, str):
        raise PlanError("le label doit etre une chaine non vide")
    rundir = workdir / label
    plan_path = rundir / "plan.json"
    if plan_path.exists() and not force:
        raise PlanError(
            f"plan deja present : {plan_path} — utilisez --force pour l'ecraser"
        )
    entrees = []
    for chemin in files:
        chemin = Path(chemin)
        if not chemin.is_file():
            raise PlanError(f"fichier a envoyer introuvable : {chemin}")
        contenu = chemin.read_text(encoding="utf-8")
        entrees.append(
            {
                "name": chemin.name,
                "path": str(chemin),
                "sha256": _sha256(contenu),
            }
        )
    plan = {
        "version": 1,
        "project_name": project_name,
        "language": language,
        "organization_id": organization_id,
        "files": entrees,
        "passes": [
            {"name": nom, "backtest_name": nom, "parameters": params}
            for nom, params in passes
        ],
    }
    # Valider ce qu'on vient d'ecrire : le squelette doit passer le meme
    # controle qu'un plan ecrit a la main.
    _valider_plan(plan)
    rundir.mkdir(parents=True, exist_ok=True)
    plan_path.write_text(
        json.dumps(plan, ensure_ascii=False, indent=2) + "\n", encoding="utf-8"
    )
    return rundir


def load_plan(rundir: Path) -> dict:
    """Charge et valide ``<rundir>/plan.json`` (message d'erreur explicite)."""
    path = rundir / "plan.json"
    try:
        brut = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError:
        raise PlanError(
            f"plan introuvable : {path} — creez-le avec la sous-commande plan"
        )
    except json.JSONDecodeError as exc:
        raise PlanError(f"plan.json illisible (JSON invalide) : {exc}")
    _valider_plan(brut)
    return brut


def _valider_plan(plan: object) -> None:
    if not isinstance(plan, dict):
        raise PlanError("plan.json doit etre un objet JSON")
    problemes: list[str] = []
    nom_projet = plan.get("project_name")
    if not isinstance(nom_projet, str) or not nom_projet.strip():
        problemes.append("project_name manquant ou vide (nom du projet QC)")
    if plan.get("language", "Py") not in LANGUAGES:
        problemes.append(
            f"language invalide {plan.get('language')!r} : attendu parmi {LANGUAGES}"
        )
    if plan.get("organization_id") is not None and not isinstance(
        plan.get("organization_id"), str
    ):
        problemes.append("organization_id doit etre une chaine ou absent")
    fichiers = plan.get("files")
    if not isinstance(fichiers, list) or not fichiers:
        problemes.append("files doit etre une liste non vide de fichiers a envoyer")
    else:
        vus = set()
        for entree in fichiers:
            if not isinstance(entree, dict):
                problemes.append("chaque entree de files doit etre un objet")
                continue
            nom = entree.get("name")
            if not isinstance(nom, str) or not nom.strip():
                problemes.append(f"entree de files sans name valide : {entree!r}")
            elif nom in vus:
                problemes.append(f"fichier duplique dans files : {nom}")
            else:
                vus.add(nom)
            if not isinstance(entree.get("path"), str) or not entree["path"].strip():
                problemes.append(f"entree de files sans path valide : {nom!r}")
    passes = plan.get("passes")
    if not isinstance(passes, list) or not passes:
        problemes.append("passes doit etre une liste non vide (au moins une passe)")
    else:
        noms, noms_bt = set(), set()
        for passe in passes:
            if not isinstance(passe, dict):
                problemes.append("chaque passe doit etre un objet")
                continue
            nom = passe.get("name")
            if not isinstance(nom, str) or not nom.strip():
                problemes.append(f"passe sans name valide : {passe!r}")
                continue
            if nom in noms:
                problemes.append(f"passe dupliquee : {nom}")
            noms.add(nom)
            nom_bt = passe.get("backtest_name", nom)
            if not isinstance(nom_bt, str) or not nom_bt.strip():
                problemes.append(f"backtest_name invalide pour la passe {nom!r}")
            elif nom_bt in noms_bt:
                problemes.append(
                    f"backtest_name duplique ({nom_bt!r}) : les noms de backtest "
                    "sont uniques par projet sur QC"
                )
            else:
                noms_bt.add(nom_bt)
            params = passe.get("parameters", {})
            if not isinstance(params, dict):
                problemes.append(
                    f"parameters de la passe {nom!r} doit etre un dictionnaire"
                )
    if problemes:
        raise PlanError("plan.json invalide : " + " ; ".join(problemes))


# ─── Etat ──────────────────────────────────────────────────────────────


def _etat_vierge() -> dict:
    return {
        "version": 1,
        "project_id": None,
        "files": {},
        "compile_id": None,
        "compile_state": None,
        "passes": {},
    }


def load_state(rundir: Path) -> dict:
    """Charge state.json ; un etat vierge si absent."""
    path = rundir / "state.json"
    if not path.exists():
        return _etat_vierge()
    try:
        charge = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        # Ecriture interrompue malgre le remplacement atomique : on prefere
        # repartir de rien (l'adoption par nom evite les doublons cote QC)
        # plutot que de bloquer la reprise.
        return _etat_vierge()
    etat = _etat_vierge()
    if isinstance(charge, dict):
        etat.update(charge)
    return etat


def save_state(rundir: Path, etat: dict) -> None:
    """Ecrit state.json atomiquement (fichier temporaire + remplacement).

    Une coupure pendant l'ecriture ne laisse jamais un JSON tronque : la
    reprise lit l'etat d'avant, pas un etat illisible.
    """
    rundir.mkdir(parents=True, exist_ok=True)
    tmp = rundir / "state.json.tmp"
    tmp.write_text(
        json.dumps(etat, ensure_ascii=False, indent=2) + "\n", encoding="utf-8"
    )
    os.replace(tmp, rundir / "state.json")


def _sync_passes(plan: dict, etat: dict) -> None:
    """Reporte les passes du plan dans l'etat (sans ecraser l'avancement)."""
    for passe in plan["passes"]:
        nom = passe["name"]
        if nom not in etat["passes"]:
            etat["passes"][nom] = {
                "backtest_name": passe.get("backtest_name", nom),
                "backtest_id": None,
                "statut": STATUT_A_LANCER,
                "erreur": None,
            }


# ─── Normalisation des statistiques ────────────────────────────────────

# Cles canoniques de sortie et les formes sous lesquelles l'API range chaque
# statistique : dictionnaire ``statistics`` (cles avec espaces, forme
# principale), ``runtimeStatistics`` (variantes typees runtime, ex. "CAGR"),
# et forme camelCase deja normalisee par ``_extract_stats`` du serveur.
CHAMPS_CANONIQUES: list[tuple[str, tuple[str, ...]]] = [
    ("sharpe", ("Sharpe Ratio", "sharpeRatio")),
    ("cagr", ("Compounding Annual Return", "CAGR", "compoundingAnnualReturn")),
    ("max_drawdown", ("Drawdown", "drawdown")),
    ("psr", ("Probabilistic Sharpe Ratio", "probabilisticSharpeRatio")),
    ("beta", ("Beta", "beta")),
    ("win_rate", ("Win Rate", "winRate")),
]


def _premiere_valeur(sources: list[dict], cles: tuple[str, ...]) -> Optional[str]:
    for source in sources:
        for cle in cles:
            valeur = source.get(cle)
            if valeur not in (None, ""):
                return str(valeur)
    return None


def normaliser_statistiques(bt: dict) -> dict:
    """Normalise les statistiques d'un backtest vers les cles canoniques.

    Les valeurs restent les chaines d'affichage de QC ("1.234", "8.413%") :
    l'outil ne re-formate jamais une valeur mesuree. Le nombre d'ordres
    suit le canon du serveur : ``statistics["Total Orders"]`` fait foi, le
    champ de haut niveau ``totalOrders`` n'est qu'un repli (il vaut null sur
    un backtest termine).
    """
    sources = [
        bt.get("statistics") or {},
        bt.get("runtimeStatistics") or {},
        bt,  # forme camelCase extraite : clefs au niveau du dictionnaire
    ]
    stats = {
        canon: _premiere_valeur(sources, cles) for canon, cles in
        CHAMPS_CANONIQUES
    }
    ordres = (bt.get("statistics") or {}).get("Total Orders")
    if ordres in (None, "", "-"):
        ordres = bt.get("totalOrders")
    stats["orders"] = None if ordres in (None, "") else str(ordres)
    return stats


def statistiques_vides(stats: dict) -> bool:
    """Vrai quand aucune cle canonique ne porte de valeur exploitable.

    Un backtest termine mais sans ordre garde des valeurs honnetes
    (orders="0") : il n'est pas « vide ». Ne sont vides que les reponses ou
    toute cle vaut None, "" ou le marqueur d'inapplicabilite "-" de QC.
    """
    return all(valeur in (None, "", "-") for valeur in stats.values())


def backtest_termine(bt: dict) -> bool:
    """Fin du backtest selon l'API.

    Le temoin direct est le booleen ``completed`` du dictionnaire backtest
    (c'est lui que le code de mesure existant teste) ; le statut
    "Completed." (avec point final) et progress a 1 completent le tableau.
    """
    if bt.get("completed") is True:
        return True
    return str(bt.get("status", "")).startswith("Completed")


def backtest_en_erreur(bt: dict) -> bool:
    """Erreur du backtest : champ error/stacktrace ou statut portant Error."""
    if bt.get("error") or bt.get("stacktrace"):
        return True
    return "Error" in str(bt.get("status", ""))


# ─── run ───────────────────────────────────────────────────────────────


def _resoudre_chemin(rundir: Path, chemin: str) -> Path:
    """Resout un chemin de fichier du plan : dossier du plan, puis CWD."""
    candidat = Path(chemin)
    if candidat.is_absolute():
        return candidat
    relatif_au_plan = rundir / candidat
    if relatif_au_plan.is_file():
        return relatif_au_plan
    return candidat


def _assurer_projet(
    gateway, plan: dict, etat: dict, rundir: Path
) -> None:
    """Note le projet dans l'etat ; le retrouve par nom s'il existe deja.

    Une coupure entre la creation du projet et l'ecriture de l'etat ne doit
    pas doubler le projet : on cherche d'abord un projet du meme nom.
    """
    if etat.get("project_id"):
        return
    trouve = None
    reponse = gateway.list_projects(plan["project_name"])
    for projet in reponse.get("projects", []):
        if projet.get("name") == plan["project_name"]:
            trouve = projet.get("projectId")
            print(f"projet retrouve par nom : {trouve} ({plan['project_name']})")
            break
    if trouve is None:
        cree = gateway.create_project(
            plan["project_name"],
            plan.get("language", "Py"),
            plan.get("organization_id"),
        )
        trouve = cree.get("projectId")
        if not trouve:
            raise MeasureError(
                "create_project n'a pas rendu d'identifiant de projet"
            )
        print(f"projet cree : {trouve} ({plan['project_name']})")
    etat["project_id"] = trouve
    save_state(rundir, etat)


def _envoyer_fichiers(
    gateway, plan: dict, etat: dict, rundir: Path
) -> None:
    """Envoie les fichiers du plan non encore notes, avec relecture de controle.

    Un fichier deja note avec la meme empreinte n'est pas renvoye. Si un
    contenu change alors que des backtests sont deja notes, la mesure est
    refusee : re-mesurer exige un nouveau label (les noms de backtest sont
    uniques par projet sur QC, un backtest note correspond a un code gele).
    """
    pid = etat["project_id"]
    a_envoyer = []
    for entree in plan["files"]:
        chemin = _resoudre_chemin(rundir, entree["path"])
        try:
            contenu = chemin.read_text(encoding="utf-8")
        except OSError as exc:
            raise MeasureError(
                f"fichier du plan illisible : {chemin} ({exc}) ; "
                "chemins resolus depuis le dossier du plan puis le repertoire courant"
            )
        empreinte = _sha256(contenu)
        if entree.get("sha256") and entree["sha256"] != empreinte:
            print(
                f"avertissement : {entree['name']} differe de l'empreinte "
                "notee dans plan.json (fichier modifie depuis l'ecriture du plan)"
            )
        if etat["files"].get(entree["name"]) != empreinte:
            a_envoyer.append((entree["name"], contenu, empreinte))
    if a_envoyer and any(p.get("backtest_id") for p in etat["passes"].values()):
        # Refuser AVANT d'envoyer : les mesures deja lancees correspondent au
        # code precedent ; re-mesurer exige un nouveau label (les noms de
        # backtest sont uniques par projet sur QC, un backtest note correspond
        # a un code gele).
        raise MeasureError(
            "fichiers modifies alors que des backtests sont deja notes : "
            "repartez sur un nouveau label pour re-mesurer"
        )
    noms_presents: Optional[set] = None
    for nom, contenu, empreinte in a_envoyer:
        if noms_presents is None:
            noms_presents = {
                f.get("name")
                for f in gateway.read_project(pid).get("files", [])
            }
        if nom in noms_presents:
            gateway.update_file_contents(pid, nom, contenu)
        else:
            gateway.create_file(pid, nom, contenu)
        relu = (gateway.read_file(pid, nom) or {}).get("content", "")
        if _sha256(relu) != empreinte:
            raise MeasureError(
                f"contenu sur QC different du contenu local pour {nom}"
            )
        print(f"fichier envoye : {nom} (empreinte verifiee)")
        etat["files"][nom] = empreinte
        save_state(rundir, etat)
    if a_envoyer:
        # Le code a change : une compilation deja reussie ne correspond plus
        # aux fichiers envoyes.
        etat["compile_id"] = None
        etat["compile_state"] = None
        save_state(rundir, etat)


def _assurer_compilation(
    gateway, scheduler, etat: dict, rundir: Path, *, poll_interval: float,
    max_wait: float,
) -> str:
    """Compile (une fois) et attend BuildSuccess ; rend le compileId."""
    pid = etat["project_id"]
    if etat.get("compile_state") == "BuildSuccess" and etat.get("compile_id"):
        return etat["compile_id"]
    if etat.get("compile_state") == "BuildError":
        # Nouvelle tentative : le code a pu etre corrige depuis.
        etat["compile_id"] = None
        etat["compile_state"] = None
    if not etat.get("compile_id"):
        compile_id = gateway.create_compile(pid).get("compileId")
        if not compile_id:
            raise MeasureError("create_compile n'a pas rendu de compileId")
        etat["compile_id"] = compile_id
        save_state(rundir, etat)
        print(f"compilation lancee : {compile_id}")
    compile_id = etat["compile_id"]
    debut = scheduler.now()
    while True:
        lecture = gateway.read_compile(pid, compile_id)
        etat_compile = lecture.get("state", "")
        if etat_compile in ("BuildSuccess", "BuildError"):
            etat["compile_state"] = etat_compile
            save_state(rundir, etat)
            if etat_compile == "BuildError":
                erreurs = "; ".join(str(e) for e in lecture.get("errors", []))
                raise MeasureError(
                    f"compilation en echec ({compile_id}) : {erreurs[:800]}"
                )
            print(f"compilation reussie : {compile_id}")
            return compile_id
        if scheduler.now() - debut >= max_wait:
            raise MeasureError(
                f"compilation {compile_id} sans issue apres {max_wait:.0f} s "
                f"(etat {etat_compile!r})"
            )
        scheduler.wait(poll_interval)


def _lancer_et_attendre(
    gateway, scheduler, plan: dict, etat: dict, rundir: Path, *,
    parallel: int, poll_interval: float, max_wait: float,
) -> int:
    """Lance les passes non lancees, adopte les backtests existants, attend.

    Adoption par nom : une coupure entre create_backtest et l'ecriture de
    l'etat ne doit pas relancer le backtest en double — on relit la liste
    des backtests du projet et on adopte celui qui porte le nom attendu.
    """
    pid = etat["project_id"]
    compile_id = etat["compile_id"]

    a_adopter = [
        nom for nom, p in etat["passes"].items() if not p.get("backtest_id")
    ]
    if a_adopter:
        existants = {
            b.get("name"): b.get("backtestId")
            for b in gateway.list_backtests(pid).get("backtests", [])
        }
        for nom in a_adopter:
            bid = existants.get(etat["passes"][nom]["backtest_name"])
            if bid:
                etat["passes"][nom]["backtest_id"] = bid
                etat["passes"][nom]["statut"] = STATUT_LANCEE
                print(f"passe {nom} : backtest existant adopte ({bid})")
        save_state(rundir, etat)

    en_attente = [
        nom for nom, p in etat["passes"].items() if not p.get("backtest_id")
    ]
    en_vol: dict[str, float] = {
        nom: scheduler.now()
        for nom, p in etat["passes"].items()
        if p.get("backtest_id") and p.get("statut") == STATUT_LANCEE
    }
    code_retour = 0
    while en_attente or en_vol:
        while en_attente and len(en_vol) < parallel:
            nom = en_attente.pop(0)
            passe = etat["passes"][nom]
            cree = gateway.create_backtest(
                pid, compile_id, passe["backtest_name"],
                plan_parametres(plan, nom),
            )
            bid = cree.get("backtestId")
            if not bid:
                raise MeasureError(
                    f"create_backtest n'a pas rendu d'identifiant pour {nom}"
                )
            passe["backtest_id"] = bid
            passe["statut"] = STATUT_LANCEE
            save_state(rundir, etat)
            print(f"passe {nom} : backtest lance ({bid})")
            en_vol[nom] = scheduler.now()
        if not en_vol:
            break
        progres = False
        for nom in list(en_vol):
            passe = etat["passes"][nom]
            if scheduler.now() - en_vol[nom] >= max_wait:
                # On n'abandonne pas le backtest : au prochain run, l'attente
                # reprend (le backtest reste note lance).
                print(
                    f"passe {nom} : delai depasse ({max_wait:.0f} s) ; "
                    "relancez run pour reprendre l'attente"
                )
                del en_vol[nom]
                code_retour = 1
                progres = True
                continue
            bt = gateway.read_backtest(pid, passe["backtest_id"])
            if backtest_en_erreur(bt):
                passe["statut"] = STATUT_ERREUR
                passe["erreur"] = str(
                    bt.get("error") or bt.get("status") or "erreur inconnue"
                )[:300]
                save_state(rundir, etat)
                print(f"passe {nom} : ERREUR — {passe['erreur']}")
                del en_vol[nom]
                code_retour = 1
                progres = True
            elif backtest_termine(bt):
                passe["statut"] = STATUT_TERMINEE
                save_state(rundir, etat)
                print(f"passe {nom} : terminee ({passe['backtest_id']})")
                del en_vol[nom]
                progres = True
        if en_vol and not progres:
            scheduler.wait(poll_interval)
    if any(p.get("statut") != STATUT_TERMINEE for p in etat["passes"].values()):
        code_retour = 1
    return code_retour


def plan_parametres(plan: dict, nom_passe: str) -> dict:
    """Parametres de la passe nommee dans le plan."""
    for passe in plan["passes"]:
        if passe["name"] == nom_passe:
            return passe.get("parameters", {})
    raise PlanError(f"passe absente du plan : {nom_passe}")


def run_measure(
    gateway, scheduler, rundir: Path, *,
    parallel: int = 1,
    poll_interval: float = DEFAULT_POLL_INTERVAL,
    max_wait: float = DEFAULT_MAX_WAIT,
) -> int:
    """Execute tout ce qui manque, en notant chaque etape dans state.json.

    Renvoie 0 si toutes les passes sont terminees, 1 sinon. Les blocages
    (plan invalide, compilation en echec, fichiers modifies) levent
    MeasureError/PlanError : l'appelant les traduit en code 2.
    """
    plan = load_plan(rundir)
    etat = load_state(rundir)
    _sync_passes(plan, etat)
    _assurer_projet(gateway, plan, etat, rundir)
    _envoyer_fichiers(gateway, plan, etat, rundir)
    etat["compile_id"] = _assurer_compilation(
        gateway, scheduler, etat, rundir,
        poll_interval=poll_interval, max_wait=max_wait,
    )
    save_state(rundir, etat)
    return _lancer_et_attendre(
        gateway, scheduler, plan, etat, rundir,
        parallel=parallel, poll_interval=poll_interval, max_wait=max_wait,
    )


# ─── status ────────────────────────────────────────────────────────────


def status_measure(
    gateway, scheduler, rundir: Path, *, refresh: bool = False
) -> int:
    """Etat de chaque passe ; --refresh interroge l'API pour les lancees."""
    plan = load_plan(rundir)
    etat = load_state(rundir)
    _sync_passes(plan, etat)
    pid = etat.get("project_id")
    if refresh and gateway is not None and pid:
        for nom, passe in etat["passes"].items():
            if not passe.get("backtest_id"):
                continue
            if passe.get("statut") == STATUT_TERMINEE:
                continue
            bt = gateway.read_backtest(pid, passe["backtest_id"])
            if backtest_en_erreur(bt):
                passe["statut"] = STATUT_ERREUR
                passe["erreur"] = str(
                    bt.get("error") or bt.get("status") or "erreur inconnue"
                )[:300]
            elif backtest_termine(bt):
                passe["statut"] = STATUT_TERMINEE
        save_state(rundir, etat)
    print(
        f"projet : {pid} ({plan['project_name']}) ; "
        f"compilation : {etat.get('compile_state')}"
    )
    for passe in plan["passes"]:
        nom = passe["name"]
        p = etat["passes"].get(nom, {})
        ligne = f"passe {nom} : {p.get('statut', STATUT_A_LANCER)}"
        if p.get("backtest_id"):
            ligne += f" (backtest {p['backtest_id']})"
        if p.get("erreur"):
            ligne += f" — {p['erreur']}"
        print(ligne)
    return 0


# ─── read ──────────────────────────────────────────────────────────────

COLONNES_TABLEAU: list[tuple[str, str]] = [
    ("Passe", "passe"),
    ("Sharpe", "sharpe"),
    ("CAGR", "cagr"),
    ("MaxDD", "max_drawdown"),
    ("PSR", "psr"),
    ("Beta", "beta"),
    ("Ordres", "orders"),
    ("Reussite", "win_rate"),
    ("Backtest", "backtest_id"),
    ("Projet", "project_id"),
]


def _attendre_fin(
    gateway, scheduler, pid: int, bid: str, *,
    poll_interval: float, max_wait: float,
) -> dict:
    """Sonde le backtest jusqu'a sa fin (ou l'expiration du delai).

    Les statistiques ne sont jamais lues comme des resultats avant la fin :
    un backtest en cours affiche totalOrders=0 et des statistiques a "-",
    etat indiscernable d'un run termine sans aucun ordre (garde #14142).
    """
    debut = scheduler.now()
    while True:
        bt = gateway.read_backtest(pid, bid)
        if backtest_termine(bt) or backtest_en_erreur(bt):
            return bt
        if scheduler.now() - debut >= max_wait:
            return bt
        scheduler.wait(poll_interval)


def read_measure(
    gateway, scheduler, rundir: Path, *,
    as_json: bool = False,
    poll_interval: float = DEFAULT_POLL_INTERVAL,
    max_wait: float = DEFAULT_MAX_WAIT,
    retries: int = EMPTY_STATS_RETRIES,
) -> int:
    """Lit chaque backtest termine et rend le tableau des statistiques.

    Renvoie 0 si chaque passe est terminee avec statistiques, 1 sinon
    (non lancee, non termine a temps, en erreur, statistiques vides).
    """
    plan = load_plan(rundir)
    etat = load_state(rundir)
    _sync_passes(plan, etat)
    pid = etat.get("project_id")
    if not pid:
        raise PlanError(
            "aucun projet note dans state.json — lancez la sous-commande run d'abord"
        )
    lignes: list[str] = []
    lignes_json: list[dict] = []
    tout_ok = True
    for passe in plan["passes"]:
        nom = passe["name"]
        p = etat["passes"].get(nom, {})
        resultat = {
            "passe": nom,
            "statut": p.get("statut", STATUT_A_LANCER),
            "backtest_id": p.get("backtest_id"),
            "project_id": pid,
            "statistics": None,
        }
        if not p.get("backtest_id"):
            lignes.append(f"passe {nom} : pas de backtest note (lancez run)")
            lignes_json.append(resultat)
            tout_ok = False
            continue
        bt = _attendre_fin(
            gateway, scheduler, pid, p["backtest_id"],
            poll_interval=poll_interval, max_wait=max_wait,
        )
        if backtest_en_erreur(bt):
            message = str(bt.get("error") or bt.get("status"))[:300]
            p["statut"] = STATUT_ERREUR
            p["erreur"] = message
            lignes.append(f"passe {nom} : backtest en erreur — {message}")
            lignes_json.append(resultat)
            tout_ok = False
            continue
        if not backtest_termine(bt):
            lignes.append(
                f"passe {nom} : backtest pas termine apres {max_wait:.0f} s "
                f"(statut {bt.get('status')!r}) — statistiques refusees"
            )
            lignes_json.append(resultat)
            tout_ok = False
            continue
        p["statut"] = STATUT_TERMINEE
        stats = normaliser_statistiques(bt)
        if statistiques_vides(stats):
            # Termine mais sans chiffres : les statistiques peuvent suivre la
            # fin de quelques secondes ; relire un nombre borne de fois avant
            # de le dire, plutot que d'afficher des tirets.
            for _ in range(retries):
                scheduler.wait(poll_interval)
                stats = normaliser_statistiques(
                    gateway.read_backtest(pid, p["backtest_id"])
                )
                if not statistiques_vides(stats):
                    break
        if statistiques_vides(stats):
            lignes.append(
                f"passe {nom} : backtest termine mais statistiques vides "
                f"apres {retries} relectures — aucune valeur rendue"
            )
            lignes_json.append(resultat)
            tout_ok = False
            continue
        resultat["statistics"] = stats
        lignes_json.append(resultat)
    save_state(rundir, etat)
    for ligne in lignes:
        print(ligne)
    if any(r["statistics"] for r in lignes_json):
        lignes_tab = [r for r in lignes_json if r["statistics"]]
        if as_json:
            print(
                json.dumps(
                    {"project_id": pid, "passes": lignes_json},
                    ensure_ascii=False,
                    indent=2,
                )
            )
        else:
            print(render_table(lignes_tab))
    elif as_json:
        print(
            json.dumps(
                {"project_id": pid, "passes": lignes_json},
                ensure_ascii=False,
                indent=2,
            )
        )
    return 0 if tout_ok else 1


def render_table(resultats: list[dict]) -> str:
    """Tableau Markdown : passe, statistiques normalisees, identifiants."""
    entetes = [titre for titre, _ in COLONNES_TABLEAU]
    lignes = [
        "| " + " | ".join(entetes) + " |",
        "|" + "|".join(["---"] * len(entetes)) + "|",
    ]
    for resultat in resultats:
        stats = resultat.get("statistics") or {}
        cellules = []
        for _, cle in COLONNES_TABLEAU:
            if cle == "passe":
                cellules.append(str(resultat["passe"]))
            elif cle in stats:
                cellules.append(stats.get(cle) or "")
            elif cle == "backtest_id":
                cellules.append(resultat.get("backtest_id") or "")
            elif cle == "project_id":
                cellules.append(str(resultat.get("project_id") or ""))
        lignes.append("| " + " | ".join(cellules) + " |")
    return "\n".join(lignes)


# ─── CLI ───────────────────────────────────────────────────────────────


def _entier_borne(mini: int, maxi: int):
    def convertir(texte: str) -> int:
        try:
            valeur = int(texte)
        except ValueError:
            raise argparse.ArgumentTypeError(f"{texte!r} n'est pas un entier")
        if not mini <= valeur <= maxi:
            raise argparse.ArgumentTypeError(
                f"valeur {valeur} hors bornes [{mini}, {maxi}]"
            )
        return valeur

    return convertir


def _intervalle_sondage(texte: str) -> float:
    try:
        valeur = float(texte)
    except ValueError:
        raise argparse.ArgumentTypeError(f"{texte!r} n'est pas un nombre")
    if valeur < MIN_POLL_INTERVAL:
        raise argparse.ArgumentTypeError(
            f"l'intervalle de sondage doit etre d'au moins "
            f"{MIN_POLL_INTERVAL:.0f} s (limite de debit flotte de l'API QC)"
        )
    return valeur


def _parse_passe_cli(valeur: str) -> tuple[str, dict]:
    """Parse une passe de la CLI : NOM ou 'NOM:{"param": valeur}'."""
    nom, separateur, params = valeur.partition(":")
    if not separateur:
        return nom, {}
    try:
        parametres = json.loads(params)
    except json.JSONDecodeError as exc:
        raise PlanError(
            f"parametres invalides pour la passe {nom!r} : {exc}"
        )
    if not isinstance(parametres, dict):
        raise PlanError(
            f"les parametres de la passe {nom!r} doivent etre un dictionnaire JSON"
        )
    return nom, parametres


def build_parser() -> argparse.ArgumentParser:
    """Parseur de la CLI (aide et messages en francais)."""
    parser = argparse.ArgumentParser(
        prog="qc_measure.py",
        description=(
            "Mesure generique de strategies QuantConnect sur QC Cloud : "
            "plan (squelette de mesure), run (execution idempotente et "
            "reprenable), status (etat des passes), read (statistiques "
            "normalisees des backtests termines)."
        ),
    )
    sous = parser.add_subparsers(dest="commande", required=True)

    p_plan = sous.add_parser(
        "plan", help="ecrit le squelette <workdir>/<label>/plan.json"
    )
    p_plan.add_argument("workdir", help="dossier racine des mesures")
    p_plan.add_argument("--label", required=True, help="nom de la mesure")
    p_plan.add_argument(
        "--project-name", required=True, help="nom du projet QC a creer"
    )
    p_plan.add_argument(
        "--language", default="Py", choices=list(LANGUAGES),
        help="langage du projet QC (defaut : Py)",
    )
    p_plan.add_argument(
        "--file", dest="files", action="append", default=[],
        metavar="CHEMIN", help="fichier a envoyer (repeter pour chaque fichier)",
    )
    p_plan.add_argument(
        "--passe", dest="passes", action="append", default=[],
        metavar="NOM[:PARAMS_JSON]",
        help="passe nommee et ses parametres, ex. 'rapide:{\"lookback\": 10}'",
    )
    p_plan.add_argument(
        "--organization-id", default=None,
        help="organisation QC cible (defaut : celle du compte)",
    )
    p_plan.add_argument(
        "--force", action="store_true", help="ecrase un plan deja present"
    )

    p_run = sous.add_parser(
        "run", help="execute tout ce qui manque (idempotent et reprenable)"
    )
    _options_run_read(p_run, avec_parallel=True)

    p_status = sous.add_parser(
        "status", help="etat de chaque passe dans state.json"
    )
    p_status.add_argument("rundir", help="dossier de la mesure (contient plan.json)")
    p_status.add_argument(
        "--refresh", action="store_true",
        help="interroge l'API pour actualiser les passes lancees",
    )

    p_read = sous.add_parser(
        "read", help="statistiques des backtests termines (tableau Markdown)"
    )
    _options_run_read(p_read, avec_parallel=False)
    p_read.add_argument(
        "--json", action="store_true", help="sortie JSON au lieu du tableau"
    )
    return parser


def _options_run_read(parser: argparse.ArgumentParser, *, avec_parallel: bool) -> None:
    parser.add_argument("rundir", help="dossier de la mesure (contient plan.json)")
    if avec_parallel:
        parser.add_argument(
            "--parallel", type=_entier_borne(1, 16), default=1,
            help="nombre de backtests simultanes (defaut : 1)",
        )
    parser.add_argument(
        "--poll-interval", type=_intervalle_sondage,
        default=DEFAULT_POLL_INTERVAL,
        help=f"intervalle de sondage en secondes (>={MIN_POLL_INTERVAL:.0f})",
    )
    parser.add_argument(
        "--max-wait", type=float, default=DEFAULT_MAX_WAIT,
        help="delai maximal d'attente par etape, en secondes",
    )
    parser.add_argument(
        "--max-calls-per-min", type=_entier_borne(
            MIN_MAX_CALLS_PER_MIN, MAX_MAX_CALLS_PER_MIN
        ),
        default=DEFAULT_MAX_CALLS_PER_MIN,
        help=f"appels API par minute au plus (1 a {MAX_MAX_CALLS_PER_MIN})",
    )


def main(argv: Optional[list[str]] = None) -> int:
    """Point d'entree CLI ; renvoie le code de sortie.

    0 : succes ; 1 : au moins une passe sans statistiques exploitables ;
    2 : blocage (plan invalide, compilation en echec, identifiants absents).
    """
    args = build_parser().parse_args(argv)
    try:
        if args.commande == "plan":
            passes = [_parse_passe_cli(v) for v in args.passes]
            rundir = write_plan(
                Path(args.workdir),
                label=args.label,
                project_name=args.project_name,
                files=[Path(f) for f in args.files],
                passes=passes,
                language=args.language,
                organization_id=args.organization_id,
                force=args.force,
            )
            print(f"plan ecrit : {rundir / 'plan.json'}")
            return 0
        rundir = Path(args.rundir)
        if args.commande == "run":
            scheduler = Scheduler(max_calls=args.max_calls_per_min)
            gateway = ThrottledGateway(ServerGateway(), scheduler)
            return run_measure(
                gateway, scheduler, rundir,
                parallel=args.parallel,
                poll_interval=args.poll_interval,
                max_wait=args.max_wait,
            )
        if args.commande == "read":
            scheduler = Scheduler(max_calls=args.max_calls_per_min)
            gateway = ThrottledGateway(ServerGateway(), scheduler)
            return read_measure(
                gateway, scheduler, rundir,
                as_json=args.json,
                poll_interval=args.poll_interval,
                max_wait=args.max_wait,
            )
        if args.commande == "status" and args.refresh:
            scheduler = Scheduler()
            gateway = ThrottledGateway(ServerGateway(), scheduler)
            return status_measure(gateway, scheduler, rundir, refresh=True)
        return status_measure(None, None, rundir)
    except (PlanError, MeasureError) as exc:
        print(f"erreur : {exc}", file=sys.stderr)
        return 2
    except RuntimeError as exc:
        # Rejet de l'API QC (garde success:false du serveur) : message
        # propre plutot qu'une traceback.
        print(f"erreur : appel QC rejete — {exc}", file=sys.stderr)
        return 2
    except ValueError as exc:
        # Identifiants absents cote serveur (message du serveur, jeton
        # jamais affiche).
        print(
            f"erreur : identifiants QC absents ou invalides ({exc}) ; "
            "definissez QC_API_USER_ID et QC_API_ACCESS_TOKEN",
            file=sys.stderr,
        )
        return 2


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
