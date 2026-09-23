#!/usr/bin/env python3
"""Etat reel des checks d'une PR, lu a la source (#16765).

Defaut mesure (ai-01, 18/09, fondateurs #16232/#16499/#16579) : le champ
`statusCheckRollup` est une LISTE PLATE qui contient TOUTES les jambes du head,
y compris celles supersedees par une tentative plus recente. Le rollup de
#16232 rend bien les trois jambes `Always-on guards` (CANCELLED 02:12:41Z,
FAILURE 02:12:44Z, SUCCESS 02:19:13Z) -- dans un ordre NON chronologique.
Tout lecteur qui scanne la liste et retient la premiere jambe rouge par nom
refuse une PR verte : les six rouges du rollup de #16232 etaient tous
supersedes sur le meme head.

La lecture juste est le fold canonique de `scripts/pr_gate.py::dedupe_latest`
(#11808/#11869) : derniere jambe par nom, clee (started_at, id). Ce helper en
est l'exposition read-side -- les organes et les lots de dossier appellent
`fold_latest()` au lieu de lire le rollup brut. Le contrat du dossier adjoint
(`checks: latest-wins-green`, check_adjoint_prevalidation.py) se prouve avec
cet instrument.

DEUX VUES, NE PAS LES CONFONDRE :

1. `latest` (fold) : le verdict le plus recent par nom. C'est la reponse a
   « que dit CE check maintenant ? » et le remede au refus sur rouge perime.
   #16232 est MERGE avec une jambe rouge residuelle encore presente sur son
   head : pour un meme nom d'un meme app, le gate retient la plus recente.

2. `residual_reds` : les jambes rouges ANCIENNES encore presentes sous un vert
   recent. Elles ne disparaissent PAS de la liste plate. Contre-preuve mesuree
   (#11532, CodeQL default setup) : une jambe rouge d'une suite distincte a
   BLOQUE la PR malgre un vert homonyme plus recent -- GitHub fait un AND
   inter-suites dans ce cas, pas un latest-wins. Un `latest` vert n'est donc
   JAMAIS une preuve de mergeabilite, et ce helper ne l'affirme pas : il rend
   les deux faits, le lecteur tranche (mergeStateStatus / rerun de la jambe).

Asymetrie des verdicts (meme contrat que check_stale_guard_reds.py / le sweep
PR gate) : RED = verdict RENDU d'echec ({failure, timed_out}) ; GREEN =
{success, neutral, skipped} ; cancelled/stale/action_required = sans verdict,
montres pour lecture mais jamais comptes rouges (un cancel-storm n'est pas un
echec de garde, cf #13156).

Premisse du fold par nom : le nom identifie le job. Gardee par
scripts/ci/check_unique_check_run_names.py (#11869) -- ne pas dedupliquer par
(workflow, name) en remplacement d'un fix de collision.

Sortie :
    python scripts/check_run_state.py --pr 16232
    python scripts/check_run_state.py --sha <head_sha> --json
Exit : 0 = vue latest toute verte ; 1 = au moins un rouge dans la vue latest ;
2 = erreur d'instrument.
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys

RED = {"failure", "timed_out"}
GREEN = {"success", "neutral", "skipped"}
REPO = "jsboige/CoursIA"


def normalize_leg(entry: dict) -> dict:
    """Une jambe, des deux formes possibles : check-run REST (snake_case,
    conclusions minuscules) ou entree de rollup GraphQL (camelCase,
    conclusions MAJUSCULES). Champs rendus : name, conclusion (minuscule),
    started_at, id, details_url. TOUJOURS appliquer -- un pass-through cru
    casse la clee started_at sur la forme camelCase et laisse les
    conclusions majuscules hors des ensembles RED/GREEN."""
    return {
        "name": entry.get("name") or entry.get("context") or "?",
        "conclusion": (entry.get("conclusion") or entry.get("state") or "").lower(),
        "started_at": entry.get("started_at") or entry.get("startedAt") or "",
        "id": entry.get("id") or 0,
        "details_url": entry.get("details_url") or entry.get("detailsUrl") or "",
    }


def fold_latest(legs: list[dict]) -> dict[str, dict]:
    """Derniere jambe par nom, semantique dedupe_latest (clee started_at puis
    id, monotones au niveau check-run -- #11416 : un rerun cree une entree
    fraiche d'id ET de started_at plus grands)."""
    best: dict[str, tuple[tuple, dict]] = {}
    for index, raw in enumerate(legs):
        leg = normalize_leg(raw)
        key = (leg.get("started_at") or "", leg.get("id") or 0, index)
        current = best.get(leg["name"])
        if current is None or key >= current[0]:
            best[leg["name"]] = (key, leg)
    return {name: leg for name, (_, leg) in best.items()}


def residual_reds(legs: list[dict]) -> list[dict]:
    """Jambes rouges anciennes sous un vert recent du meme nom (classe #16765
    pour la lecture, #11532 pour la contre-preuve de blocage)."""
    grouped: dict[str, list[dict]] = {}
    for raw in legs:
        leg = normalize_leg(raw)
        grouped.setdefault(leg["name"], []).append(leg)
    out = []
    for name, group in grouped.items():
        group.sort(key=lambda c: (c.get("started_at") or "", c.get("id") or 0))
        if group[-1].get("conclusion") not in GREEN:
            continue
        for leg in group[:-1]:
            if leg.get("conclusion") in RED:
                out.append({"name": name, **{k: leg[k] for k in
                                             ("conclusion", "started_at", "id")}})
    return out


def _run_gh(args: list[str]) -> str:
    proc = subprocess.run(["gh", *args], capture_output=True, text=True)
    if proc.returncode != 0:
        raise RuntimeError(f"gh {' '.join(args[:4])}... -> {proc.returncode}: "
                           f"{proc.stderr[:200]}")
    return proc.stdout


def _head_sha(pr: int) -> str:
    return json.loads(_run_gh(["pr", "view", str(pr), "--repo", REPO,
                               "--json", "headRefOid"]))["headRefOid"]


def collect(pr: int | None = None, sha: str | None = None) -> tuple[str, list[dict]]:
    """(head_sha, jambes) lus a la source REST -- l'issue #16765 la nomme la
    source fiable : commits/<head>/check-runs, tri par started_at, dernier par
    nom fait foi."""
    sha = sha or _head_sha(pr)
    rows = _run_gh(["api", f"repos/{REPO}/commits/{sha}/check-runs?per_page=100",
                    "--jq", ".check_runs[] | {name, conclusion, started_at, id, "
                    "details_url} | tojson"])
    legs = [json.loads(line) for line in rows.splitlines() if line.strip()]
    return sha, legs


def render(sha: str, legs: list[dict]) -> dict:
    latest = fold_latest(legs)
    reds = sorted(name for name, leg in latest.items()
                  if leg.get("conclusion") in RED)
    residuals = residual_reds(legs)
    counts: dict[str, int] = {}
    for leg in legs:
        counts[leg.get("name") or leg.get("context") or "?"] = \
            counts.get(leg.get("name") or leg.get("context") or "?", 0) + 1
    return {
        "head": sha,
        "n_legs": len(legs),
        "n_names": len(latest),
        "latest": {name: {"conclusion": leg.get("conclusion"),
                          "started_at": leg.get("started_at")}
                   for name, leg in sorted(latest.items())},
        "legs_per_name": counts,
        "latest_reds": reds,
        "residual_reds": residuals,
    }


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--pr", type=int)
    g.add_argument("--sha")
    ap.add_argument("--json", action="store_true", dest="as_json")
    args = ap.parse_args(argv)
    try:
        sha, legs = collect(pr=args.pr, sha=args.sha)
    except RuntimeError as exc:
        print(f"instrument error: {exc}", file=sys.stderr)
        return 2
    state = render(sha, legs)
    if args.as_json:
        print(json.dumps(state, ensure_ascii=False, indent=1))
    else:
        print(f"head {sha} -- {state['n_legs']} jambes / {state['n_names']} noms "
              f"(source: commits/<head>/check-runs)")
        multi = {n: c for n, c in state["legs_per_name"].items() if c > 1}
        for name, leg in sorted(state["latest"].items()):
            mark = "RED" if leg["conclusion"] in RED else \
                   "..." if leg["conclusion"] not in GREEN else "OK"
            extra = f" x{multi[name]} jambes" if name in multi else ""
            print(f"  [{mark}] {name}: {leg['conclusion']} @{leg['started_at']}{extra}")
        if state["residual_reds"]:
            print(f"residual_reds ({len(state['residual_reds'])}) -- rouges "
                  f"supersedes encore presents sous un vert recent ; ne "
                  f"presagent PAS l'etat merge (#11532 CodeQL a bloque ainsi, "
                  f"#16232 a merge malgre) :")
            for r in state["residual_reds"]:
                print(f"    {r['name']}: {r['conclusion']} @{r['started_at']}")
    return 1 if state["latest_reds"] else 0


if __name__ == "__main__":
    sys.exit(main())
