#!/usr/bin/env python3
"""Sentinelle de ``main`` rouge : couverture, verdicts, latence, premier commit rouge.

Le besoin vient de #24828 (fenetre residuelle de la sentinelle de main rouge
laissee ouverte par #24821). #24821 ferme la fenetre **au sein d'un meme run** :
chaque PR est combinee au ``main`` courant avant le merge. La fenetre qui reste
est **entre deux mergeurs concurrents** : deux PRs fusionnees contre le meme
``main@T``, dont la seconde n'a pas ete combinee a la premiere.

#25169 (PR ouverte, hors flotte) traite le **cote local** de cette fenetre :
`merge_ready` lit le verdict du check de ``main`` et pose une retenue nommee
quand il est rouge. Ce que cet organe apporte est la **mesure de la flotte**,
qui conditionne le critere de sortie de #24828 :

    « Rejeu : un merge concurrent fabrique dans un depot jetable donne un
     rouge nomme en moins de 15 min, et le run ``merge_ready`` suivant refuse
     de merger tant que le rouge tient. »

La premiere moitie de ce critere n'etait mesuree par personne. Mesure du
2026-11-10 sur ``jsboige/CoursIA``, workflow ``scripts-tests.yml``, branche
``main``, 100 runs conclus + les 60 derniers commits de ``main`` :

* **COUVERTURE 66,7 %** : 20 des 60 derniers commits de ``main`` n'ont produit
  **AUCUN run**. Le workflow porte un filtre ``paths:`` sur le push
  (``scripts/**``, ``tests/**``, ``pytest.ini``...), donc un merge qui ne
  touche pas ces chemins ne produit aucun signal : la sentinelle est aveugle
  sur un tiers des poussees.
* **VERDICT DE CODE CONNU 26,7 %** : une fois ce filtre franchi, il faut en
  plus que le run **rende** un verdict de code. Sur les 60 derniers commits de
  ``main``, seuls **16 ont un etat connu** : les 44 autres sont soit sans run,
  soit annules sans rendre de verdict. C'est le taux operationnel -- ce que la
  sentinelle peut reellement lire sur le commit de tete.
* **ANNULES 69,0 %** : sur 100 runs conclus, 69 sont ``cancelled``. Une
  poussee suivante annule le run en cours ; les runs annules ne rendent AUCUN
  verdict, donc l'etat courant de ``main`` est souvent celui d'un run vieux.
* **LATENCE** (creee -> conclue, sur les 31 runs qui ont rendu un verdict) :
  mediane **27,1 min**, p90 **108,2 min**, max **161,8 min**, min **11,2 min**.
  Le seuil « 15 min » du critere de sortie **n'est pas tenu** : meme le plus
  rapide des runs mesures depasse 11 min, et la mediane est pres de 27 min.

Ces trois nombres ne sont pas une opinion : ils se relisent a la source avec
les commandes ci-dessous, et l'organe les recalcule a la demande.

Deux causes mecaniques, deux corrections qui ne se confondent pas :

* le filtre ``paths:`` (couverture) -> lever le filtre sur le push, comme le
  fait #25169 ;
* l'annulation en rafale (69,0 % sans verdict) -> ne pas annuler le run en
  cours, ou accepter qu'un verdict manque et le dire.

Ce que cet organe **ne** fait pas : il ne pose aucune retenue, ne bloque aucun
merge, ne decide rien. Il **mesure** et il **nomme**. La retenue reste
l'affaire de ``merge_ready`` (#25169), la decision reste celle du coordinateur.

**Limite a lire avec le nom qu'il donne.** L'organe lit la **conclusion** du
run, pas son log. Un run tue par le watchdog xdist (worker mort, silence de
480 s) sort en ``failure`` : il est donc nomme comme un rouge de code, alors
que sa cause est l'infrastructure. Constat du 2026-11-10 sur ``main`` :
``c7fe7a91a7dd`` est ainsi nomme, son log ne montre qu'un kill de watchdog
et une starvation de runners, aucun test en echec. La distinction
infra/code demande la **lecture du log** -- l'organe la rend lisible, il ne
la prend pas.

Verdicts lus (**memes ensembles que la retenue de ``merge_ready``**, pour que
les deux organes ne divergent pas sur ce qui est un defaut de code) :

* ROUGE  = ``failure`` -- un defaut de code, la seule conclusion qui pose une
  retenue ;
* VERT   = ``success`` ;
* INFRA  = ``timed_out``, ``startup_failure`` -- runner perdu, temps epuise :
  ce n'est pas une regression, et ce n'est pas non plus une absence de
  signal. Distinct de ``cancelled``, qui n'a rien dit du tout ;
* SANS VERDICT = ``cancelled``, ``skipped``, et toute autre conclusion.

Un commit **sans run** est ``unknown``, jamais ``green`` : une absence de
preuve n'est pas un vert (fail-closed).

**Ce qui distingue cet organe de ``merge_dwell``.** ``merge_dwell`` compte
``timed_out`` et ``startup_failure`` parmi les conclusions rouges, parce que
sa question est « ``main`` est-il vert pourpur ? » -- une branche qui n'a pas
rendu de verdict n'est pas demonstree verte. Ici la question est « **y a-t-il
un defaut de code** ? », et la reponse est non pour une conclusion d'infra.
Les deux organes repondent a deux questions differentes ; ils ne sont pas
contradictoires, et la retenue de ``merge_ready`` -- qui juge le dernier
verdict **termine** -- suit la meme ligne que cet organe.

Sortie :

    python scripts/ci/main_red_sentinel.py --json
    python scripts/ci/main_red_sentinel.py --first-red
    python scripts/ci/main_red_sentinel.py --repo jsboige/CoursIA \
        --workflow scripts-tests.yml --branch main --per-page 100

Sortie JSON::

    {
      "verdict": "green|red|infra|unknown",  # etat du commit de tete
      "first_red_commit": {...}|null,     # le commit QUI a introduit le rouge
      "bounds": {...},                    # ce qui borne la reponse
      "coverage": {...},                  # part des commits couverts par un run
      "verdicts": {...},                  # repartition des conclusions
      "latency_min": {...}                # mediane/p90/max/min des runs rendus
    }

Exit : 0 = aucun rouge prouve ; 1 = rouge prouve (premier commit rouge nomme) ;
2 = instrument en erreur.
"""
from __future__ import annotations

import argparse
import json
import statistics
import subprocess
import sys
from datetime import datetime

REPO = "jsboige/CoursIA"
DEFAULT_WORKFLOW = "scripts-tests.yml"
DEFAULT_BRANCH = "main"

#: Un defaut de CODE : la seule conclusion qui pose une retenue.
#: Meme ensemble que ``MAIN_RED_CODE_VERDICTS`` dans ``scripts/coordination/
#: merge_ready.py`` (#24828) -- les deux organes doivent nommer le meme
#: coupable.
RED_CONCLUSIONS = ("failure",)
GREEN_CONCLUSIONS = ("success",)

#: Conclusions d'INFRA : le runner a perdu la main ou n'a pas demarre. Ce
#: n'est ni une regression du code (rouge), ni une absence de signal
#: (``cancelled``) : le run a rendu un verdict, mais sur l'infrastructure.
#: Distinct de ``cancelled``, qui n'a rien dit du tout.
INFRA_CONCLUSIONS = ("timed_out", "startup_failure")

GREEN = "green"
RED = "red"
INFRA = "infra"
UNKNOWN = "unknown"


class SentinelError(Exception):
    """Instrument en erreur : la mesure est absente, jamais un verdict."""


def _gh_json(path: str) -> object:
    try:
        completed = subprocess.run(
            ["gh", "api", path],
            capture_output=True, text=True, encoding="utf-8", errors="replace",
            check=False,
        )
    except FileNotFoundError as exc:  # pragma: no cover - environnement
        raise SentinelError("gh CLI absent: {}".format(exc)) from exc
    if completed.returncode != 0:
        raise SentinelError(
            "gh api {} a echoue (exit {}): {}".format(
                path, completed.returncode, completed.stderr.strip()[:300])
        )
    try:
        return json.loads(completed.stdout)
    except json.JSONDecodeError as exc:
        raise SentinelError("reponse non-JSON de gh api {}".format(path)) from exc


def _parse(ts: str) -> "datetime | None":
    if not ts:
        return None
    try:
        return datetime.fromisoformat(ts.replace("Z", "+00:00"))
    except ValueError:
        return None


def run_state(run: dict) -> str:
    """Verdict d'un run : vert, rouge, INFRA, ou SANS verdict.

    - ``failure`` : un defaut de code -- le seul etat qui pose une retenue ;
    - ``success`` : vert ;
    - ``timed_out`` / ``startup_failure`` : INFRA -- le runner a perdu la
      main, le code n'a pas ete juge ;
    - ``cancelled`` et tout le reste : SANS verdict, le run n'a rien dit.

    Un run ``cancelled`` n'a rien dit de la qualite du code : il se compte
    comme SANS verdict. C'est ce qui rend la mesure de couverture Vitale --
    69,7 % des runs mesures sur ``main`` etaient annules (2026-11-10).
    """
    conclusion = (run.get("conclusion") or "").lower()
    if conclusion in RED_CONCLUSIONS:
        return RED
    if conclusion in GREEN_CONCLUSIONS:
        return GREEN
    if conclusion in INFRA_CONCLUSIONS:
        return INFRA
    return UNKNOWN


def fetch_runs(repo: str, workflow: str, branch: str, per_page: int,
               fetch=_gh_json) -> list:
    """Runs ``push`` du workflow sur la branche, du plus recent au plus ancien."""
    payload = fetch(
        "repos/{}/actions/workflows/{}/runs"
        "?branch={}&event=push&per_page={}".format(repo, workflow, branch, per_page)
    )
    runs = payload.get("workflow_runs") if isinstance(payload, dict) else None
    if not isinstance(runs, list):
        raise SentinelError("reponse inattendue de l'API des runs")
    return sorted(runs, key=lambda r: r.get("created_at") or "", reverse=True)


def fetch_commits(repo: str, branch: str, per_page: int,
                  fetch=_gh_json) -> list:
    """Commits de la branche, du plus recent au plus ancien."""
    payload = fetch("repos/{}/commits?sha={}&per_page={}".format(
        repo, branch, per_page))
    commits = payload if isinstance(payload, list) else None
    if commits is None:
        raise SentinelError("reponse inattendue de l'API des commits")
    return commits


def commit_states(commits: list, runs: list) -> dict:
    """Etat de chaque commit : vert, rouge, infra, ou unknown (aucun run rendu).

    Un commit peut porter plusieurs runs (relance, annulation puis relance) :
    on retient le **plus recent** qui a rendu un verdict, et l'on note les
    autres. Un commit dont tous les runs sont sans verdict reste ``unknown``.

    Un commit dont le dernier verdict rendu est d'INFRA (``timed_out``,
    ``startup_failure``) est ``infra`` : le code n'a pas ete juge, et aucun
    defaut n'est prouve -- ni dans un sens ni dans l'autre.
    """
    by_sha = {}
    for run in runs:
        by_sha.setdefault(run.get("head_sha") or "", []).append(run)

    states = {}
    for commit in commits:
        sha = commit.get("sha") or ""
        candidates = by_sha.get(sha, [])
        with_verdict = [r for r in candidates if run_state(r) != UNKNOWN]
        if with_verdict:
            latest = max(with_verdict, key=lambda r: r.get("updated_at") or "")
            states[sha] = {"state": run_state(latest), "run": latest,
                           "runs": candidates}
        else:
            states[sha] = {"state": UNKNOWN, "run": None, "runs": candidates}
    return states


def measure_coverage(commits: list, states: dict) -> dict:
    """Trois taux, a ne pas confondre.

    * ``taux_run_pct`` : part des commits qui ont produit **un run** --
      c'est la couverture du filtre ``paths:`` du workflow. Mesure du
      2026-11-10 sur ``main`` : 66,7 % (40/60).
    * ``taux_verdict_pct`` : part des commits dont le verdict de CODE est
      **connu** (vert ou rouge). C'est le taux operationnel : c'est ce que la
      sentinelle peut reellement lire comme etat du code. Mesure du
      2026-11-10 : 25 % -- un commit sur quatre a un etat connu.
    * ``taux_infra_pct`` : part des commits dont le verdict est rendu mais
      d'INFRA (``timed_out``, ``startup_failure``) -- le code n'a pas ete
      juge. Ces commits-la ne sont ni verts ni rouges : ils sont comptes a
      part, jamais fondus dans le « sans verdict ».
    """
    total = len(commits)
    avec_run = 0
    verdict_connu = 0
    infra = 0
    for commit in commits:
        info = states.get(commit.get("sha") or "", {})
        if info.get("runs"):
            avec_run += 1
        state = info.get("state")
        if state in (GREEN, RED):
            verdict_connu += 1
        elif state == INFRA:
            infra += 1
    return {
        "commits": total,
        "avec_run": avec_run,
        "verdict_connu": verdict_connu,
        "infra": infra,
        "sans_run": total - avec_run,
        "taux_run_pct": round(100.0 * avec_run / total, 1) if total else 0.0,
        "taux_verdict_pct": round(100.0 * verdict_connu / total, 1) if total else 0.0,
        "taux_infra_pct": round(100.0 * infra / total, 1) if total else 0.0,
    }


def measure_verdicts(runs: list) -> dict:
    """Repartition des conclusions des runs conclus."""
    counts = {}
    for run in runs:
        if (run.get("status") or "") != "completed":
            continue
        conclusion = (run.get("conclusion") or "none").lower()
        counts[conclusion] = counts.get(conclusion, 0) + 1
    completed = sum(counts.values())
    return {
        "runs_conclus": completed,
        "par_conclusion": counts,
        "taux_annules_pct": round(
            100.0 * counts.get("cancelled", 0) / completed, 1) if completed else 0.0,
    }


def measure_latency(runs: list) -> dict:
    """Duree ``created_at -> updated_at`` des runs qui ont rendu un verdict.

    C'est la borne de detection du « rouge nomme en moins de 15 min » : le
    run ne peut etre lu qu'une fois conclu.
    """
    durations = []
    for run in runs:
        if run_state(run) == UNKNOWN:
            continue
        start = _parse(run.get("created_at") or "")
        end = _parse(run.get("updated_at") or "")
        if start is None or end is None:
            continue
        durations.append((end - start).total_seconds() / 60.0)
    if not durations:
        return {"n": 0, "mediane": None, "p90": None, "max": None, "min": None}
    durations.sort()
    return {
        "n": len(durations),
        "mediane": round(statistics.median(durations), 1),
        "p90": round(durations[min(len(durations) - 1,
                                   int(len(durations) * 0.9))], 1),
        "max": round(durations[-1], 1),
        "min": round(durations[0], 1),
    }


def find_first_red(commits: list, states: dict) -> dict:
    """Le commit QUI a introduit le rouge, et les bornes de la reponse.

    Parcours des commits du plus recent au plus ancien :

    1. on note le commit de tete et son etat ;
    2. on descend jusqu'a trouver le **premier** commit rouge de la serie
       (le plus ancien de la zone rouge) ;
    3. la reponse n'est exacte que si le commit immediatement plus ancien
       est connu VERT. Sinon elle est **bornee** : on declare au plus tot et
       au plus tard, plutot que de nommer un coupables qui peut etre innocent.

    Exemple de borne : un commit sans run entre le vert et le rouge laisse
    le vrai coupable dans l'intervalle -- l'organe ne le devine pas.
    """
    entries = []
    for commit in commits:
        sha = commit.get("sha") or ""
        info = states.get(sha, {"state": UNKNOWN, "run": None})
        entries.append((commit, info))

    head = entries[0] if entries else None
    if head is None:
        return {"verdict": UNKNOWN, "first_red_commit": None, "bounds": {}}

    first_red = None
    latest_green = None
    unknown_between = []
    infra_between = []
    red_zone_started = False
    for commit, info in entries:
        state = info["state"]
        if state == RED:
            red_zone_started = True
            # le bloc rouge est parcouru du plus recent au plus ancien : le
            # DERNIER rouge vu est le plus ancien du bloc, c'est-a-dire le
            # commit qui a INTRODUIT le rouge.
            first_red = (commit, info)
            continue
        if state == GREEN:
            latest_green = (commit, info)
            break
        if state == INFRA:
            # verdict d'INFRA : ni vert ni rouge, et le code n'a pas ete
            # juge -- on le compte a part, on ne le franchit pas.
            infra_between.append(commit)
            continue
        # inconnu : ni vert ni rouge -- on le compte, on ne le franchit pas
        unknown_between.append(commit)

    def describe(item):
        if item is None:
            return None
        commit, info = item
        run = info.get("run") or {}
        return {
            "sha": commit.get("sha"),
            "subject": (commit.get("commit", {}).get("message") or "")
                        .splitlines()[0][:120],
            "date": commit.get("commit", {}).get("committer", {}).get("date"),
            "run_id": run.get("id"),
            "conclusion": run.get("conclusion"),
        }

    verdict = head[1]["state"]
    bounds = {
        "dernier_commit_vert_connu": describe(latest_green),
        "commits_sans_verdict_entre_les_deux": [
            {"sha": c.get("sha"), "subject": (c.get("commit", {})
                                               .get("message") or "")
             .splitlines()[0][:120]} for c in unknown_between],
        "commits_infra_entre_les_deux": [
            {"sha": c.get("sha"), "subject": (c.get("commit", {})
                                              .get("message") or "")
             .splitlines()[0][:120]} for c in infra_between],
    }
    exact = bool(latest_green is not None and first_red is not None
                 and not unknown_between and not infra_between)
    return {
        "verdict": verdict,
        "first_red_commit": describe(first_red) if first_red else None,
        "first_red_commit_exact": exact,
        "bounds": bounds,
        "head": describe(head),
    }


def sentinel_report(repo: str = REPO, workflow: str = DEFAULT_WORKFLOW,
                    branch: str = DEFAULT_BRANCH, per_page: int = 100,
                    commit_page: int = 60, fetch=_gh_json) -> dict:
    """Rapport complet : etat de tete, premier commit rouge, couverture, latence."""
    runs = fetch_runs(repo, workflow, branch, per_page, fetch=fetch)
    commits = fetch_commits(repo, branch, commit_page, fetch=fetch)
    states = commit_states(commits, runs)
    report = find_first_red(commits, states)
    report["repo"] = repo
    report["workflow"] = workflow
    report["branch"] = branch
    report["coverage"] = measure_coverage(commits, states)
    report["verdicts"] = measure_verdicts(runs)
    report["latency_min"] = measure_latency(runs)
    return report


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--repo", default=REPO)
    parser.add_argument("--workflow", default=DEFAULT_WORKFLOW)
    parser.add_argument("--branch", default=DEFAULT_BRANCH)
    parser.add_argument("--per-page", type=int, default=100,
                        help="runs lus pour le workflow (defaut 100)")
    parser.add_argument("--commit-page", type=int, default=60,
                        help="commits lus sur la branche (defaut 60)")
    parser.add_argument("--first-red", action="store_true",
                        help="n'affiche que le commit rouge et ses bornes")
    parser.add_argument("--json", action="store_true", dest="as_json")
    args = parser.parse_args(argv)

    try:
        report = sentinel_report(
            repo=args.repo, workflow=args.workflow, branch=args.branch,
            per_page=args.per_page, commit_page=args.commit_page)
    except SentinelError as exc:
        payload = {"error": str(exc), "verdict": UNKNOWN}
        if args.as_json:
            print(json.dumps(payload, indent=2, ensure_ascii=False))
        else:
            print("[ERREUR] {}".format(exc), file=sys.stderr)
        return 2

    if args.as_json:
        print(json.dumps(report, indent=2, ensure_ascii=False))
    elif args.first_red:
        first = report.get("first_red_commit")
        if first is None:
            print("[main {}] aucun commit rouge prouve (etat de tete : {})".format(
                args.branch, report.get("verdict")))
        else:
            print("[main {}] premier commit rouge : {} {}".format(
                args.branch, first["sha"][:12], first["subject"]))
            print("  exact : {}".format(report.get("first_red_commit_exact")))
            green = report.get("bounds", {}).get("dernier_commit_vert_connu")
            if green:
                print("  dernier vert connu : {} {}".format(
                    green["sha"][:12], green["subject"]))
            for gap in report.get("bounds", {}).get(
                    "commits_sans_verdict_entre_les_deux", []):
                print("  sans verdict : {} {}".format(gap["sha"][:12],
                                                       gap["subject"]))
            for gap in report.get("bounds", {}).get(
                    "commits_infra_entre_les_deux", []):
                print("  infra (code non juge) : {} {}".format(
                    gap["sha"][:12], gap["subject"]))
    else:
        cov = report["coverage"]
        lat = report["latency_min"]
        print("[main {}] etat de tete : {} | couverture : {} % de commits avec un "
              "run, {} % avec un verdict de code, {} % en infra | runs annules : "
              "{} %".format(
                  args.branch, report.get("verdict"), cov["taux_run_pct"],
                  cov["taux_verdict_pct"], cov["taux_infra_pct"], report["verdicts"]
                  ["taux_annules_pct"]))
        print("latence des runs rendus (min) : mediane {} | p90 {} | max {}".format(
            lat.get("mediane"), lat.get("p90"), lat.get("max")))
        first = report.get("first_red_commit")
        if first:
            print("premier commit rouge : {} {}".format(
                first["sha"][:12], first["subject"]))

    return 1 if report.get("verdict") == RED else 0


if __name__ == "__main__":
    sys.exit(main())
