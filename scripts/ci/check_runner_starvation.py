#!/usr/bin/env python3
"""Organe d'extinction des runners Linux self-hosted (#13378).

POURQUOI CE SCRIPT EXISTE
-------------------------
Le 2026-09-02 entre ~07:00 et 10:25 UTC, le superviseur de conteneurs runner
de myia-po-2024 est mort silencieusement : ses deux slots ont rendu l'ame apres
une generation manglee (bug MSYS), sans qu'aucun signal ne le dise. Sur les 12
workflows routes sur le label `coursia-linux` (#14148), 11 sont bloquants --
un superviseur mort ne degrade pas le CI, il arrete la flotte (3 PRs de
contenu restees rouges ~35 h sur ce seul fait, cf DM ai-01 2026-09-02T07:53Z).

La lecon n'est pas « surveiller le superviseur » (un proxy de proxy), mais de
mesurer le SYMPTOME : des jobs restent-ils non servis ? Deux predicats, dans
l'ordre de fiabilite :

  - EXTINCTION (direct, PAT Administration:read) : plus AUCUN runner online ne
    porte le label. Tant qu'un superviseur vit, ses slots restent enregistres
    online 24/7 -- zero online = extinction, queue vide ou non.
  - STARVATION (symptome, GITHUB_TOKEN seul) : au moins un job libelle queued
    depuis > STARVE_MINUTES minutes, ET aucun job libelle in_progress. Une file
    profonde qui DRAINE (slots busy) est un manque de capacite, pas une
    extinction -- le garde ne rougit pas sur le backlog sain, sinon il serait
    rouge permanent et apprendrait a etre ignore.

FENETRE D'EXAMEN (correctif fail-open, signe par po-2025 / relais CoursIA-2,
2026-09-02) : l'API rend les runs du plus recent au plus ancien. Une lecture
cappee aux N premiers rend exactement ceux qui n'ont pas eu le temps de
starver -- mesure du jour : 34 runs queued > 15 min, tous en pages 6-7,
tous invisibles au cap=30 (dont des runs abandonnes a ~14 jours). La
collecte pagine donc jusqu'a WINDOW_MAX_MINUTES (les runs plus vieux sont
la classe ABANDONNEE, notee sans jamais rougir : rougir dessus serait le
rouge permanent que la garde anti-FP interdit). L'age d'un job s'ancre sur
jobs[].created_at (un job debloque tard par needs: a attendu moins que le
run n'est vieux), avec repli sur run.created_at. Chaque job est classe par
SON PROPRE statut sur l'union dedupliquee des runs queued/in_progress : un
run in_progress peut porter un job du label reste queued (extinction ciblee
de la jambe Linux pendant que les autres jobs du run progressent) -- le
classer par le statut du run le rendait invisible aux deux passes.

Le predicat STARVATION ne demande aucun secret ; le predicat EXTINCTION lit
`/actions/runners` via RUNNERS_READ_PAT (pose 2026-09-02T08:26Z, deliberement
read-only : incapable de minter un registration-token). Sans PAT, l'organe
degrade proprement sur le seul symptome.

COUT ET HONNETETE DE LA LECTURE (#22215, mesure du 2026-10-23 a 15:35Z)
-----------------------------------------------------------------------
Le passage lisait les jobs de CHAQUE run de la fenetre -- ~380 appels a
15:20Z, et le heartbeat `workflow_run` a fait tourner la sonde 104 fois en
3 h. Deux corrections, dans le meme geste parce que la seconde depend de la
premiere :

  - les jobs d'un run ne peuvent pas etre plus vieux que le run : un run de
    moins de `starve_minutes` ne peut pas porter un job affame et ne vaut
    aucun appel ; les autres sont lus du PLUS VIEUX au plus recent dans la
    limite de `--job-read-budget` ; cote in_progress, un echantillon suffit
    (le predicat ne demande que l'existence d'un slot qui sert) ;
  - chaque echec d'appel est compte et NOMME (endpoint, code, message). Un
    passage troue ne conclut ni `OK` ni `STARVATION` : il rend
    `LECTURE API INCOMPLETE`. Avant, `_gh_json` rendait `None` et l'appelant
    faisait `continue` -- le run 39976669812 (15:20Z) a annonce « 311 job(s)
    queued ... et AUCUN job in_progress » alors que 34 runs l'etaient.

Sortie : exit 1 + annotation ::error:: sur EXTINCTION ou STARVATION ;
::warning:: sur perte partielle (online < WARN_FLOOR) sans extinction, ou sur
CADENCE SERVIE (le scheduler GitHub ne livre plus l'evenement schedule, #15332).
Advisory par construction du workflow appelant (schedule/workflow_dispatch +
heartbeat workflow_run, jamais pull_request/push -- il ne peut jamais bloquer
une PR).
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import time
from collections import defaultdict
from dataclasses import dataclass, field
from datetime import datetime, timezone

DEFAULT_REPO = "jsboige/CoursIA"
DEFAULT_LABEL = "coursia-linux"
DEFAULT_STARVE_MINUTES = 15.0
DEFAULT_WARN_FLOOR = 2
DEFAULT_WINDOW_MAX_MINUTES = 360.0
# Seuil SCHEDULER MUET : au-dessus de la queue de la bande servie NOMINALE
# (intervalles planifiés de 30 min servis à 168-323 min mesurés, #15332 ;
# un seuil dans la bande fabrique des fausses alertes en service normal --
# revue ai-01 du 2026-09-16 sur #16388).
DEFAULT_CADENCE_WARN_MINUTES = 360.0
# #22215 : bornes de lecture. Un passage coutait un appel `jobs` par run de la
# fenetre -- ~380 appels a 15:20Z le 2026-10-23, et 104 passages en 3 h.
# Le budget couvre les runs queued les plus vieux (les seuls qui peuvent
# affamer) ; l'echantillon in_progress ne sert qu'a prouver qu'un slot sert.
DEFAULT_JOB_READ_BUDGET = 120
DEFAULT_IN_PROGRESS_SAMPLE = 20
RUNS_PAGE_SIZE = 100


@dataclass
class CallStats:
    """Compteur des appels `gh` d'un passage, echecs compris (#22215).

    Avant ce compteur, `_gh_json` rendait `None` sur tout code retour non nul
    et l'appelant faisait `continue` : un appel `jobs` en echec (quota, 5xx)
    ne laissait AUCUNE trace, et le passage concluait « AUCUN job in_progress »
    -- c'est-a-dire STARVATION -- sur une lecture trouee (run 39976669812 du
    2026-10-23 a 15:20Z : 311 jobs queued annonces alors que 34 runs etaient
    in_progress).
    """

    calls: int = 0
    failures: list[tuple[str, int, str]] = field(default_factory=list)

    @property
    def failed(self) -> int:
        return len(self.failures)

    def record(self, endpoint: str, code: int, message: str) -> None:
        self.failures.append((endpoint, code, message.strip()[:200]))

    def summary(self) -> str:
        return f"appels gh: {self.calls}, echecs: {self.failed}"

    def examples(self, limit: int = 3) -> str:
        return "; ".join(
            f"{ep} rc={code} ({msg or 'sans message'})"
            for ep, code, msg in self.failures[:limit]
        )


# Reserve NanoClaw #22234 : un 5xx/429 isole ne doit pas aveugler le passage
# au rythme du heartbeat -- reprise bornee a UNE tentative de plus avant de
# declarer la lecture impossible. Les indices transitoires sont lus dans le
# message de gh (le code retour seul ne distingue pas 503 de 404).
TRANSIENT_HINTS = (
    "rate limit", "service unavailable", "bad gateway",
    "server error", "try again", "timed out",
)
GH_RETRY_ATTEMPTS = 2


def _is_transient(message: str) -> bool:
    low = message.lower()
    return any(h in low for h in TRANSIENT_HINTS)


def _gh_json(
    args: list[str],
    token: str | None = None,
    stats: CallStats | None = None,
) -> object | None:
    """Run `gh api ...` and parse stdout as JSON. None on failure.

    Chaque echec est enregistre dans `stats` quand le passage en fournit un :
    le motif de l'echec (endpoint, code retour, message de `gh`) est la donnee
    qui distingue une file vide d'une lecture impossible (#22215). Sans
    `stats`, l'appel reste silencieux -- reserve aux lectures dont l'echec est
    deja modelise ailleurs (inventaire des runners sans droit admin).

    Un echec TRANSITOIRE (5xx, rate limit) est rejoue une fois avant d'etre
    declare : chaque tentative compte dans `stats.calls`, seul le resultat
    FINAL est enregistre -- une reussite apres reprise n'est pas un echec.
    """
    env = dict(os.environ)
    if token:
        env["GH_TOKEN"] = token
    endpoint = args[0] if args else "?"
    for attempt in range(GH_RETRY_ATTEMPTS):
        proc = subprocess.run(
            ["gh", "api", *args], capture_output=True, text=True,
            check=False, encoding="utf-8", errors="replace", env=env,
        )
        if stats is not None:
            stats.calls += 1
        if proc.returncode != 0:
            message = proc.stderr or proc.stdout or ""
            if (_is_transient(message)
                    and attempt + 1 < GH_RETRY_ATTEMPTS):
                time.sleep(1.0)
                continue
            if stats is not None:
                stats.record(endpoint, proc.returncode, message)
            return None
        if not proc.stdout.strip():
            if stats is not None:
                stats.record(endpoint, 0, "stdout vide")
            return None
        try:
            return json.loads(proc.stdout)
        except json.JSONDecodeError:
            if stats is not None:
                stats.record(endpoint, 0, "stdout non-JSON")
            return None
    return None


def _parse_iso(value: str | None) -> datetime | None:
    if not value:
        return None
    try:
        return datetime.fromisoformat(value.replace("Z", "+00:00"))
    except ValueError:
        return None


@dataclass
class RunnerInventory:
    online: list[str] = field(default_factory=list)
    offline: list[str] = field(default_factory=list)
    # #22937 phase B : l'inventaire distingue le slot EN LIGNE du slot
    # LIBRE. Un runner en ligne mais occupe ne peut pas absorber un
    # debordement : confondre les deux ferait annoncer une capacite locale
    # qui n'existe pas. `busy`/`idle` sont additifs (les appelants
    # existants ne les lisent pas).
    busy: list[str] = field(default_factory=list)
    idle: list[str] = field(default_factory=list)
    # Runner en ligne dont le champ `busy` est ABSENT de la reponse : son
    # occupation est INCONNUE. Il n'est donc pas comptabilise comme libre
    # (fail-CLOSED vers « capacite disponible »), mais il est nomme pour que
    # le rapport dise ce qu'il ne sait pas.
    unknown: list[str] = field(default_factory=list)

    @property
    def available(self) -> bool:
        """False = l'inventaire n'a pas pu etre lu (pas de droit admin/PAT)."""
        return True

    @property
    def free(self) -> int:
        """Nombre de slots en ligne ET libres pour le label demande."""
        return len(self.idle)


@dataclass
class InventoryUnavailable(RunnerInventory):
    reason: str = ""

    @property
    def available(self) -> bool:
        return False


@dataclass
class JobRow:
    workflow: str
    run_number: int
    run_id: int
    job_name: str
    status: str
    age_min: float | None


@dataclass
class Starvation:
    starved: list[JobRow] = field(default_factory=list)
    in_progress: list[JobRow] = field(default_factory=list)
    # runs non examines car plus vieux que la fenetre (classe abandonnee) :
    # comptes d'information, jamais un rouge -- cf docstring.
    unexamined: dict[str, int] = field(default_factory=dict)
    # #22215 : traces de la lecture. `stats` porte les echecs ; les compteurs
    # suivants portent ce qui a ete DELIBEREMENT non lu.
    stats: CallStats = field(default_factory=CallStats)
    job_reads: int = 0
    skipped_young: int = 0
    budget_unread: list[tuple[str, int, float]] = field(default_factory=list)
    in_progress_unread: int = 0
    listing_failed: set[str] = field(default_factory=set)

    @property
    def complete(self) -> bool:
        """False = la lecture n'a pas vu tout ce qu'elle devait voir."""
        return not self.listing_failed and self.stats.failed == 0

    @property
    def truncated(self) -> bool:
        """True = la lecture a ete arretee par le budget : les comptes sont
        des BORNES INFERIEURES.

        Distinct de `complete` : `complete` dit si la lecture a SUCCEEDE
        (aucun listing en echec), `truncated` dit si elle a vu TOUT. Un run
        non lu est un run vieux (les runs ages de moins que le seuil sont
        ecartes sans cout) : il peut donc porter des jobs affames. La
        consequence directionnelle : une lecture tronquee CONFIRME une
        affirmation positive (« au moins N jobs affames ») mais n'etablit
        aucune affirmation negative (« aucun job affame », « file videe »).
        """
        return bool(self.budget_unread)


def fetch_inventory(repo: str, label: str, token: str | None) -> RunnerInventory:
    # Echec attendu sans droit admin : les echecs d'appel ne comptent PAS
    # dans le stats du passage (ce n'est pas la file qu'on accuse), mais le
    # motif se rend dans la raison au lieu de mourir dans un compteur que
    # personne ne lit (reserve NanoClaw #22234 : stats jetable illisible).
    inv_stats = CallStats()
    data = _gh_json([f"repos/{repo}/actions/runners?per_page=100"], token=token,
                    stats=inv_stats)
    if not isinstance(data, dict) or "runners" not in data:
        motif = inv_stats.examples() if inv_stats.failed else "reponse inattendue"
        return InventoryUnavailable(
            reason=f"gh api actions/runners a echoue (droit admin ou "
                   f"RUNNERS_READ_PAT absent) -- {motif}")
    inv = RunnerInventory()
    for r in data.get("runners", []):
        names = [l.get("name") for l in r.get("labels", [])]
        if label not in names:
            continue
        name = r.get("name", "?")
        if r.get("status") != "online":
            inv.offline.append(name)
            continue
        inv.online.append(name)
        # #22937 phase B : `busy` porte l'occupation reelle du slot.
        # Le champ ABSENT laisse l'occupation INCONNUE : le runner n'est donc
        # pas comptabilise comme libre (fail-CLOSED -- un `r.get("busy")`
        # falsy placerait un runner muet dans `idle`, donc dans `free`, et
        # annoncerait une capacite qui n'est pas etablie). Il est nomme
        # dans `unknown` pour que le rapport dise ce qu'il ignore.
        if "busy" not in r:
            inv.unknown.append(name)
        elif r.get("busy"):
            inv.busy.append(name)
        else:
            inv.idle.append(name)
    return inv


def _runs_endpoint(repo: str, workflow: str | None) -> str:
    """Listing des runs, restreint a un workflow quand il est nomme.

    #22215 : sur `coursia-waiter`, la sonde n'a besoin que des runs de
    `pr-gate.yml` -- interroger le depot entier lui fait payer les ~340 runs
    de la fenetre pour un label de 16 slots.
    """
    if workflow:
        return f"repos/{repo}/actions/workflows/{workflow}/runs"
    return f"repos/{repo}/actions/runs"


def _collect_window(
    repo: str,
    status: str,
    window_max_minutes: float,
    now: datetime,
    workflow: str | None,
    result: Starvation,
    seen_runs: set[int],
) -> list[dict]:
    """Runs du statut donne DANS la fenetre, du plus recent au plus ancien.

    Ne lit aucun job : c'est la partie bon marche (100 runs par page). Le tri
    et le budget de lecture des jobs vivent chez l'appelant, qui peut alors
    choisir LESQUELS valent un appel (#22215).
    """
    out: list[dict] = []
    endpoint = _runs_endpoint(repo, workflow)
    page = 1
    total: int | None = None
    examined = 0
    while True:
        # Query params inline : `-f` forcerait un POST sur un endpoint GET.
        runs = _gh_json(
            [f"{endpoint}?status={status}"
             f"&per_page={RUNS_PAGE_SIZE}&page={page}"],
            stats=result.stats,
        )
        if not isinstance(runs, dict):
            result.listing_failed.add(status)
            break
        if total is None:
            raw_total = runs.get("total_count")
            if isinstance(raw_total, int):
                total = raw_total
        workflow_runs = runs.get("workflow_runs", [])
        if not workflow_runs:
            break
        # Pages triees du plus recent au plus ancien : des que le PLUS RECENT
        # de la page depasse la fenetre, toutes les suivantes sont plus
        # vieilles -- arret premature, le cout reste borne par la fenetre et
        # non par la profondeur de la file.
        newest = _parse_iso(workflow_runs[0].get("created_at"))
        if newest is not None and (now - newest).total_seconds() / 60.0 > window_max_minutes:
            break
        last_page = len(workflow_runs) < RUNS_PAGE_SIZE
        for run in workflow_runs:
            created = _parse_iso(run.get("created_at"))
            if created is None:
                continue
            if (now - created).total_seconds() / 60.0 > window_max_minutes:
                # Classe ABANDONNEE, pas affamee : hors predicat (rouge
                # permanent sinon, cf docstring). Comptee, jamais examinee.
                continue
            rid = run.get("id")
            if rid not in seen_runs:
                seen_runs.add(rid)
                examined += 1
            out.append(run)
        if last_page:
            break
        page += 1
        # Garde cout : au-dela de 20 pages (2000 runs) dans la fenetre,
        # la file est un incident de profondeur, pas de pagination.
        if page > 20:
            result.unexamined[status] = max((total or examined) - examined, 0)
            break
    if isinstance(total, int) and total > examined and status not in result.unexamined:
        result.unexamined[status] = total - examined
    return out


def fetch_starvation(
    repo: str,
    label: str,
    starve_minutes: float,
    window_max_minutes: float = DEFAULT_WINDOW_MAX_MINUTES,
    now: datetime | None = None,
    workflow: str | None = None,
    job_read_budget: int = DEFAULT_JOB_READ_BUDGET,
    in_progress_sample: int = DEFAULT_IN_PROGRESS_SAMPLE,
) -> Starvation:
    """Classe les jobs du label : affames (queued > seuil) et en cours.

    Deux passes, comme avant #22215 -- mais dont la lecture est desormais
    bornee et tracee.

    Union dedupliquee des runs queued + in_progress, chaque JOB classe par SON
    PROPRE statut (faux negatif reproduit par po-2025, 2026-09-02 : un run
    in_progress peut porter un job coursia-linux reste queued -- extinction
    ciblee de la jambe Linux pendant que les jobs GitHub-hosted du meme run
    progressent ; le classer par le statut du RUN le rendait invisible aux deux
    passes). Un run peut transiter queued -> in_progress ENTRE les deux passes :
    il faut donc re-examiner ses jobs au second passage -- la dedup vit au
    niveau JOB (cle run_id+job.id, repli nom), l'observation la plus recente
    REMPLACE TOUTE observation anterieure, y compris vers un etat terminal : un
    job vu queued puis completed au second passage quitte la liste des affames
    (sinon faux positif apres drain, repro adjoint 2026-09-02 11:23Z) ; seuls
    queued/in_progress sont reinseres.
    """
    now = now or datetime.now(timezone.utc)
    result = Starvation()
    seen_runs: set[int] = set()
    seen_jobs: dict[tuple[int, str], JobRow] = {}
    # Tracage des listings pour la re-verification du residuel adjoint
    # (2026-09-02 14:24Z) : un run observe au tour queued mais absent des deux
    # listings du tour in_progress a pu devenir terminal ENTRE les deux
    # queries -- sa re-verification directe tranche (voir plus bas).
    listing_seen: dict[int, set[str]] = {}

    def absorb(run: dict, status: str, created: datetime) -> None:
        """Classe les jobs DU LABEL de ce run ; l'observation recente gagne."""
        result.job_reads += 1
        rid = run.get("id")
        listing_seen.setdefault(rid, set()).add(status)
        jobs = _gh_json([f"repos/{repo}/actions/runs/{rid}/jobs?filter=latest"],
                        stats=result.stats)
        if not isinstance(jobs, dict):
            return
        for job in jobs.get("jobs", []):
            if label not in job.get("labels", []):
                continue
            # Retrait AVANT filtration terminale : toute observation d'un job
            # du label retire sa classification anterieure. Sans ce retrait un
            # job vu queued au 1er passage puis completed/cancelled au 2eme
            # resterait artificiellement starved apres drain (repro adjoint
            # po-2025, 11:23Z). Cle stable : job.id, repli sur job.name.
            key = (rid or 0, job.get("id") if job.get("id") is not None else job.get("name") or "?")
            old = seen_jobs.pop(key, None)
            if old is not None:
                if old in result.starved:
                    result.starved.remove(old)
                if old in result.in_progress:
                    result.in_progress.remove(old)
            job_status = job.get("status")
            if job_status not in ("queued", "in_progress"):
                continue
            # Ancrage par JOB : un job debloque tard (needs:, matrice
            # differree) a attendu moins que le run n'est vieux -- l'age run
            # serait un faux positif, sens inverse du fail-open de la fenetre.
            anchor = _parse_iso(job.get("created_at")) or created
            age_min = (now - anchor).total_seconds() / 60.0
            row = JobRow(
                workflow=run.get("name", "?"),
                run_number=run.get("run_number", 0),
                run_id=rid or 0,
                job_name=job.get("name", "?"),
                status=job_status,
                age_min=age_min,
            )
            seen_jobs[key] = row
            if job_status == "queued":
                if age_min > starve_minutes:
                    result.starved.append(row)
            else:
                result.in_progress.append(row)

    # --- Passe 1 : queued. Les jobs d'un run ne peuvent pas etre plus vieux
    # que le run : un run de moins de `starve_minutes` ne peut pas porter un
    # job affame, donc il ne vaut aucun appel `jobs`. Les autres sont lus du
    # PLUS VIEUX au plus recent, dans la limite du budget -- ce sont eux qui
    # peuvent affamer (#22215).
    queued_runs = _collect_window(repo, "queued", window_max_minutes, now,
                                  workflow, result, seen_runs)
    queued_runs.sort(key=lambda r: r.get("created_at") or "")
    for run in queued_runs:
        created = _parse_iso(run.get("created_at"))
        if created is None:
            continue
        age = (now - created).total_seconds() / 60.0
        if age <= starve_minutes:
            result.skipped_young += 1
            continue
        if result.job_reads >= job_read_budget:
            result.budget_unread.append(
                (run.get("name", "?"), run.get("run_number", 0), age))
            continue
        absorb(run, "queued", created)

    # --- Passe 2 : in_progress. Le predicat n'a besoin que de l'EXISTENCE d'un
    # job en cours (garde anti-faux-positif) : les runs les plus recents en
    # sont la meilleure preuve, et le listing est deja trie du plus recent au
    # plus ancien. Au-dela de l'echantillon, on ne lit plus (#22215).
    in_progress_runs = _collect_window(repo, "in_progress", window_max_minutes,
                                       now, workflow, result, seen_runs)
    sample = min(max(in_progress_sample, 0),
                 max(job_read_budget - result.job_reads, 0))
    for idx, run in enumerate(in_progress_runs):
        created = _parse_iso(run.get("created_at"))
        if created is None:
            continue
        if idx >= sample:
            result.in_progress_unread += 1
            continue
        absorb(run, "in_progress", created)

    # Residuel adjoint (po-2025:CoursIA-2, 2026-09-02 14:24Z) : un run observe
    # au tour queued qui transite vers un etat terminal ENTRE les deux listing
    # queries disparait du snapshot 2 -- son job n'est jamais re-observe et
    # l'entree starved du pass 1 survivait (`starved=[('guard-linux','queued',
    # 40.0)]`). Re-verification bornee : chaque run vu SEULEMENT au tour queued
    # et porteur d'une entree vivante est re-interroge directement (une query
    # run, pas ses jobs) ; `status == completed` purge ses entrees -- semantique
    # "l'observation la plus recente gagne" -- tout autre statut les conserve.
    # Fail-open : si UN listing a echoue, aucun purgement (un run invisible par
    # panne d'API n'est pas un run terminal prouve) ; idem si la query directe
    # echoue. Un run queued stable, re-verifie puis encore queued, garde son
    # entree : purger sans re-verifier rendrait l'organe muet sous vraie file
    # profonde.
    if not result.listing_failed:
        for row in [*result.starved, *result.in_progress]:
            if listing_seen.get(row.run_id) != {"queued"}:
                continue
            run = _gh_json([f"repos/{repo}/actions/runs/{row.run_id}"],
                           stats=result.stats)
            if isinstance(run, dict) and run.get("status") == "completed":
                if row in result.starved:
                    result.starved.remove(row)
                if row in result.in_progress:
                    result.in_progress.remove(row)
    return result


def fetch_scheduled_runs(repo: str, self_workflow: str, limit: int = 3) -> list[datetime]:
    """Dates de creation (UTC, ordre descroissant) des derniers runs
    ``event=schedule`` du workflow lui-meme.

    #15332 : la cadence SERVIE se mesure sur les seuls runs planifies -- les
    runs workflow_run/workflow_dispatch (heartbeats) ne prouvent rien du
    scheduler et ne doivent pas fausser la mesure.
    """
    data = _gh_json(
        [f"repos/{repo}/actions/workflows/{self_workflow}/runs"
         f"?event=schedule&per_page={limit}"]
    )
    if not isinstance(data, dict):
        return []
    out: list[datetime] = []
    for run in data.get("workflow_runs", []):
        d = _parse_iso(run.get("created_at"))
        if d is not None:
            out.append(d)
    return out


def evaluate_cadence(
    scheduled: list[datetime],
    now: datetime,
    declared_minutes: float,
    warn_minutes: float,
) -> Verdict:
    """Mesure l'ecart entre cadence cron DECLAREE et cadence SERVIE (#15332).

    Le 2026-09-09, le scheduler GitHub a cesse de livrer ``schedule`` (4 h
    sans declenchement, depot entier) : un organe porte par schedule seul
    mourait avec la panne. Deux signaux, calibres pour eviter le rouge
    permanent :

      - une NOTE systantique : minutes depuis le dernier run planifie +
        intervalle servi precedent -- la mesure demande par #15332 point 2 ;
      - un WARNING seulement au-dela de ``warn_minutes`` sans run planifie :
        l'echelle de l'arret total (>= 4 h), pas le retard chronique de
        GitHub sur un depot a 159 workflows (intervalles servis de ~2,5-5 h
        deja observes a l'etat nominal -- rougir dessus apprendrait a etre
        ignore, cf garde anti-FP de STARVATION).
    """
    v = Verdict()
    if not scheduled:
        v.warnings.append(
            "SCHEDULER MUET: aucun run event=schedule lisible -- l'API ou le "
            "scheduler est en panne (#15332)"
        )
        return v
    since_last = (now - scheduled[0]).total_seconds() / 60.0
    if len(scheduled) >= 2:
        gap = (scheduled[0] - scheduled[1]).total_seconds() / 60.0
        gap_txt = f"intervalle servi precedent: {gap:.0f} min"
    else:
        gap_txt = "un seul run schedule visible"
    v.notes.append(
        f"cadence servie: {since_last:.0f} min depuis le dernier run planifie "
        f"({gap_txt} ; declare {declared_minutes:.0f} min)"
    )
    if since_last > warn_minutes:
        v.warnings.append(
            f"SCHEDULER MUET: {since_last:.0f} min sans run planifie "
            f"(seuil {warn_minutes:.0f} min, declare {declared_minutes:.0f} min) "
            f"-- l'evenement schedule n'est plus livre (#15332)"
        )
    return v


@dataclass
class Verdict:
    status: str = "OK"  # OK | ERROR -- fixe par evaluate()
    errors: list[str] = field(default_factory=list)
    warnings: list[str] = field(default_factory=list)
    notes: list[str] = field(default_factory=list)


def evaluate(inv: RunnerInventory, st: Starvation, warn_floor: int,
             label: str = DEFAULT_LABEL) -> Verdict:
    v = Verdict()

    if inv.available:
        if not inv.online and not inv.offline:
            # Aucun runner enregistre ne porte le label : c'est un LABEL
            # INCONNU, pas une extinction. Mesure du 2026-10-23 : la sonde
            # `coursia-lean` rougissait « superviseur(s) mort(s) ? (offline:
            # aucun) » a chaque passage depuis la veille alors que 40 runners
            # etaient online et qu'aucun workflow de `main` ne routait plus
            # vers ce label -- le pool a ete migre, la sonde est restee. Le
            # rouge permanent est exactement ce que la garde anti-FP du
            # predicat STARVATION interdit ailleurs : il apprend a etre
            # ignore. Le symptome reste mesure independamment (jobs queued
            # sans in_progress) : si un workflow route encore vers ce label,
            # STARVATION rougira pour la bonne raison.
            v.warnings.append(
                f"LABEL INCONNU: aucun runner enregistre ne porte le label "
                f"« {label} » -- label retire de la flotte, ou sonde obsolete ? "
                f"Si un workflow route encore vers lui, ses jobs ne demarreront "
                f"jamais ; sinon retirer cette sonde."
            )
        elif not inv.online:
            v.errors.append(
                f"EXTINCTION: aucun runner online ne porte le label -- superviseur(s) mort(s) ? "
                f"(offline: {', '.join(inv.offline) or 'aucun'})"
            )
        elif len(inv.online) < warn_floor:
            v.warnings.append(
                f"perte partielle de capacite: {len(inv.online)} runner(s) online "
                f"(< {warn_floor}) : {', '.join(inv.online)} ; offline: {', '.join(inv.offline) or 'aucun'}"
            )
        else:
            v.notes.append(f"{len(inv.online)} runner(s) online: {', '.join(inv.online)}")
    else:
        v.notes.append(f"inventaire non lisible ({getattr(inv, 'reason', '')}) -- garde sur le seul symptome")

    unq = st.unexamined.get("queued", 0)
    if unq:
        v.notes.append(
            f"{unq} run(s) queued plus vieux que la fenetre d'examen -- classe "
            f"ABANDONNEE (hygiene de file), pas extinction : hors predicat, "
            f"jamais un rouge. Cf pr-gate-stale-sweep / cancel-organs."
        )

    # #22215 : ce que la lecture a coute, et ce qu'elle n'a pas pu lire. Un
    # passage ou des appels ont echoue ne conclut NI `OK` NI `STARVATION` sur
    # le silence -- c'est exactement ainsi que le run 39976669812 a annonce
    # « AUCUN job in_progress » alors que 34 runs l'etaient.
    v.notes.append(
        f"lecture: {st.stats.summary()} ; {st.job_reads} run(s) inspecte(s), "
        f"{st.skipped_young} run(s) queued trop jeune(s) pour affamer "
        f"(aucun appel jobs)."
    )
    if st.in_progress_unread:
        v.notes.append(
            f"{st.in_progress_unread} run(s) in_progress hors echantillon -- "
            f"non lus : le predicat ne demande que l'existence d'un job en cours."
        )
    if st.budget_unread:
        oldest_unread = max(a for _, _, a in st.budget_unread)
        v.warnings.append(
            f"BUDGET DE LECTURE: {len(st.budget_unread)} run(s) queued > seuil "
            f"non inspecte(s) au-dela du budget (plus vieux: "
            f"{oldest_unread:.0f} min). Un affame peut s'y cacher : "
            f"augmenter --job-read-budget si la file est durablement profonde."
        )
    if st.stats.failed:
        v.errors.append(
            f"LECTURE API INCOMPLETE: {st.stats.failed} appel(s) gh en echec "
            f"sur {st.stats.calls} -- le passage ne prouve ni file saine ni "
            f"famine. Exemples: {st.stats.examples()}"
        )
    if st.listing_failed:
        # #22234 (dossier adjoint c.6378853422) : un listing qui revient en
        # TABLEAU est du JSON valide -- `_gh_json` ne le compte pas comme un
        # echec d'appel, seul `listing_failed` le trace. Sans cette jambe, le
        # passage rendait OK sur une file jamais lue (fail-open).
        v.errors.append(
            f"LISTING INCOMPLET: listing(s) {sorted(st.listing_failed)} "
            f"illisible(s) (reponse non-dict) -- le passage ne prouve ni "
            f"file saine ni famine."
        )

    if st.starved and not st.in_progress:
        oldest = max(r.age_min or 0 for r in st.starved)
        message = (
            f"STARVATION: {len(st.starved)} job(s) libelle queued > seuil (plus vieux: {oldest:.0f} min) "
            f"et AUCUN job in_progress -- la file ne drainne pas. Exemples: "
            + "; ".join(f"{r.workflow} #{r.run_number} ({r.job_name}, {r.age_min:.0f} min)" for r in st.starved[:5])
        )
        # L'absence d'in_progress n'est PROUVEE que par une lecture complete.
        # Trois angles morts la rendent NON ETABLIE : des appels en echec (run
        # 39976669812 : « AUCUN job in_progress » annonce sur 34 runs en
        # cours), des runs in_progress DELIBEREMENT non lus -- budget epuise
        # par la passe queued, dossier #22234 : 3 affames lus, 2 en cours
        # jamais regardes, evaluate lisait ce silence comme une absence -- et
        # un listing illisible. Un STARVATION en plus accuserait la file sur
        # un angle mort ; les erreurs LECTURE API INCOMPLETE / LISTING
        # INCOMPLET portent deja le constat de lecture.
        reasons = []
        if st.stats.failed:
            reasons.append("des appels ont echoue")
        if st.in_progress_unread:
            reasons.append(
                f"{st.in_progress_unread} run(s) in_progress hors echantillon, "
                f"non lus")
        if st.listing_failed:
            reasons.append(
                f"listing(s) {sorted(st.listing_failed)} illisible(s)")
        if reasons:
            v.warnings.append(
                f"{message} -- NON CONCLU : l'absence de job in_progress "
                f"n'est pas etablie ({' ; '.join(reasons)})."
            )
        else:
            v.errors.append(message)
    elif st.starved:
        v.notes.append(
            f"file profonde mais saine: {len(st.starved)} job(s) queued > seuil, "
            f"{len(st.in_progress)} job(s) in_progress -- capacite en train de drainer"
        )
    elif st.in_progress:
        v.notes.append(f"{len(st.in_progress)} job(s) in_progress, rien d'affame -- OK")
    else:
        v.notes.append("ni queue affamee ni job en cours -- OK")

    # Alertes de perte de pool par hote (#20697 point 4) -- disjointes de
    # EXTINCTION globale : un hote peut perdre tous ses online pendant que le
    # pool global reste vert (les autres hotes du label tournent). Cas
    # fondateur : myia-ai-01-wsl 0 online / 10 offline pendant ~2 jours,
    # EXTINCTION muette car d'autres hotes du label restaient online.
    if inv.available:
        v.warnings.extend(evaluate_host_loss(inv))

    v.status = "ERROR" if v.errors else "OK"
    return v


_HOST_SUFFIX = re.compile(r"-\d+$")


def _host_of(runner_name: str) -> str:
    """Nom de l'hote extrait du nom de slot (suffixe '-N' jete).

    Le format canonique sur la flotte est `<host>-<slot>` (ex :
    `myia-ai-01-wsl-1` -> host `myia-ai-01-wsl` ; `myia-po-2024-linux-docker-3`
    -> host `myia-po-2024-linux-docker`). Les noms qui ne portent pas ce
    suffixe (futur format) restent tels quels -- la detection par hote est
    best-effort, le predicat EXTINCTION global reste la borne dure.
    """
    return _HOST_SUFFIX.sub("", runner_name)


def evaluate_host_loss(inv: RunnerInventory) -> list[str]:
    """Warnings de perte de pool par hote (#20697 point 4).

    Constat fondateur (12:45Z) : le pool `myia-ai-01-wsl` est reste 0 online
    pendant ~2 jours alors que les 10 conteneurs tournaient (visible cote
    superviseur, invisible cote GitHub). Aucun signal n'a nomme cette
    disjonction -- l'organe EXTINCTION global ne rougit que si TOUS les
    online tombent (les 10 slots etaient OFFLINE cote GitHub, mais d'autres
    hotes du label restaient online ; l'extinction globale n'a jamais tire).

    Le predicat par hote : `online == 0` ET `offline > 0` -- les conteneurs
    existent (slots listes, ne serait-ce qu'en OFFLINE) mais aucun n'a pu
    s'inscrire. C'est la disjonction superviseur mort / conteneurs vivants
    sur UN hote, pas la famine globale.

    Un hote avec `online > 0` et `offline > 0` n'est PAS une perte de pool :
    certains slots sont en cours de redemarrage et le pool rend des jobs.
    C'est la garde anti-FP, mesure du jour : `myia-po-2024-linux-docker-3`
    est OFFLINE pendant que `myia-po-2024-linux-docker-1` est ONLINE, et
    l'inventaire rend `online=1, offline=1` -- on NE DOIT PAS alerter.
    """
    if not inv.available:
        return []
    online = set(inv.online)
    offline = set(inv.offline)
    by_host: dict[str, dict[str, int]] = defaultdict(lambda: {"online": 0, "offline": 0})
    for name in online | offline:
        host = _host_of(name)
        bucket = by_host[host]
        if name in online:
            bucket["online"] += 1
        else:
            bucket["offline"] += 1
    out: list[str] = []
    for host, counts in sorted(by_host.items()):
        if counts["online"] == 0 and counts["offline"] > 0:
            out.append(
                f"POOL LOSS: host {host} a 0 runner online et {counts['offline']} offline -- "
                f"conteneurs listes mais aucun ne s'inscrit (superviseur mort ? #20697)"
            )
    return out


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--repo", default=os.environ.get("REPO", DEFAULT_REPO))
    ap.add_argument("--label", default=os.environ.get("LABEL", DEFAULT_LABEL))
    ap.add_argument("--starve-minutes", type=float,
                    default=float(os.environ.get("STARVE_MINUTES", DEFAULT_STARVE_MINUTES)))
    ap.add_argument("--warn-floor", type=int, default=DEFAULT_WARN_FLOOR)
    ap.add_argument("--window-max-minutes", type=float,
                    default=float(os.environ.get("WINDOW_MAX_MINUTES", DEFAULT_WINDOW_MAX_MINUTES)),
                    help="fenetre d'examen ; les runs queued plus vieux sont "
                         "la classe ABANDONNEE, notes sans rouge")
    ap.add_argument("--self-workflow", default=os.environ.get("SELF_WORKFLOW", ""),
                    help="fichier du workflow appelant -- mesure la cadence "
                         "servie de SES runs event=schedule (#15332) ; vide = desactive")
    ap.add_argument("--declared-cadence-minutes", type=float,
                    default=float(os.environ.get("DECLARED_CADENCE_MINUTES", 30.0)),
                    help="cadence cron declaree, pour la note de cadence servie")
    ap.add_argument("--cadence-warn-minutes", type=float,
                    default=float(os.environ.get("CADENCE_WARN_MINUTES", DEFAULT_CADENCE_WARN_MINUTES)),
                    help="minutes sans run planifie avant le warning "
                         "SCHEDULER MUET (echelle de l'arret total, pas du retard chronique)")
    ap.add_argument("--workflow", default=os.environ.get("PROBE_WORKFLOW", ""),
                    help="restreint le listing des runs a CE fichier de workflow "
                         "(#22215 : une sonde de pool n'a pas besoin de payer "
                         "tous les runs du depot) ; vide = depot entier")
    ap.add_argument("--job-read-budget", type=int,
                    default=int(os.environ.get("JOB_READ_BUDGET", DEFAULT_JOB_READ_BUDGET)),
                    help="nombre maximal de runs dont les jobs sont lus sur un "
                         "passage, du plus vieux au plus recent")
    ap.add_argument("--in-progress-sample", type=int,
                    default=int(os.environ.get("IN_PROGRESS_SAMPLE", DEFAULT_IN_PROGRESS_SAMPLE)),
                    help="nombre de runs in_progress inspectes (preuve qu'un "
                         "slot sert) -- les plus recents d'abord")
    ap.add_argument("--json", action="store_true", help="sortie JSON du verdict")
    args = ap.parse_args()

    token = os.environ.get("RUNNERS_READ_PAT") or None
    inv = fetch_inventory(args.repo, args.label, token)
    st = fetch_starvation(
        args.repo, args.label, args.starve_minutes,
        window_max_minutes=args.window_max_minutes,
        workflow=args.workflow or None,
        job_read_budget=args.job_read_budget,
        in_progress_sample=args.in_progress_sample,
    )
    v = evaluate(inv, st, args.warn_floor, label=args.label)
    if args.self_workflow:
        cad = evaluate_cadence(
            fetch_scheduled_runs(args.repo, args.self_workflow),
            datetime.now(timezone.utc),
            args.declared_cadence_minutes,
            args.cadence_warn_minutes,
        )
        v.notes.extend(cad.notes)
        v.warnings.extend(cad.warnings)
        v.errors.extend(cad.errors)
        v.status = "ERROR" if v.errors else "OK"

    payload = {
        "status": v.status,
        "errors": v.errors,
        "warnings": v.warnings,
        "notes": v.notes,
        "online_runners": inv.online if inv.available else None,
        "offline_runners": inv.offline if inv.available else None,
        "starved_jobs": [r.__dict__ for r in st.starved],
        "in_progress_jobs": len(st.in_progress),
        "unexamined_runs": st.unexamined,
        "gh_calls": st.stats.calls,
        "gh_failures": [
            {"endpoint": ep, "returncode": code, "message": msg}
            for ep, code, msg in st.stats.failures
        ],
        "job_reads": st.job_reads,
        "skipped_young_runs": st.skipped_young,
        "budget_unread_runs": len(st.budget_unread),
        "in_progress_unread_runs": st.in_progress_unread,
        "listing_failed": sorted(st.listing_failed),
    }
    if args.json:
        print(json.dumps(payload, ensure_ascii=False, indent=2))
    else:
        for n in v.notes:
            print(f"[runner-starvation] {n}")
        for w in v.warnings:
            print(f"::warning::[runner-starvation] {w}")
        for e in v.errors:
            print(f"::error::[runner-starvation] {e}")

    return 1 if v.errors else 0


if __name__ == "__main__":
    sys.exit(main())
