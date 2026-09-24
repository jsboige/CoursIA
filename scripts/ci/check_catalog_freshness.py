#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Garde de la publication quotidienne du catalogue.

Le defaut
---------
`catalog-cron.yml` regenere le catalogue **tous les jours**, et il reussit :
huit runs `success` d'affilee au 2026-09-21. Mais il ne pousse pas sur `main`
-- il livre dans une PR longue duree (`chore/catalog-refresh-pending`), et
c'est cette PR qui porte le catalogue jusqu'a `main`. Quand elle n'est pas
mergee, le cron continue de reussir pendant que `main` gele.

Mesure du 2026-09-21, PR de livraison ouverte depuis 8 jours :

    entrees du catalogue sur main     1137
    ... dont chemins FANTOMES           83  (7,3 % -- le fichier n'existe pas)
    notebooks du disque ABSENTS        316  (couverture reelle 77 %)

et sur la branche de livraison, le meme jour : **0 fantome, 1240 entrees**. La
regeneration etait correcte depuis le debut ; c'est la livraison qui manquait.

Aucun organe ne le voyait, et c'est le point : un cron qui reussit est
silencieux, une PR ouverte est silencieuse, et un catalogue perime se lit
exactement comme un catalogue a jour. La promesse « eventual consistency,
<24h » vivait dans un commentaire de workflow -- pas dans une mesure.

Ce que cet organe mesure
------------------------
Deux choses independantes, parce qu'elles cassent separement :

1. **La divergence** entre le catalogue et l'arbre qu'il pretend decrire
   (chemins fantomes + notebooks absents). Hors-ligne, sans reseau.
2. **La livraison** : age de la PR de livraison et nombre de runs CI
   **gares en `action_required`** sur sa branche. Un run gare n'est ni vert
   ni rouge : il n'a jamais tourne, et le check requis qu'il porte n'existe
   donc pas -- ce qui laisse la PR en `BLOCKED` indefiniment.

Le point 2 corrige un diagnostic inscrit dans `catalog-cron.yml` (l.186-191,
issue #11202) : « a push with GITHUB_TOKEN never emits [a pull_request event]
(GitHub anti-recursion guard) ». La mesure le refute -- les runs **sont**
emis, `gh run list --branch chore/catalog-refresh-pending` en rend 40, event
`pull_request`, tous `action_required`. Ils ne sont pas absents, ils sont non
approuves. Le remede n'est donc pas le « empty-commit wake-up » manuel que ce
commentaire designe comme canonique, mais l'approbation des runs -- qui
s'automatise.

Usage :

    # divergence seule (hors-ligne, rapide)
    python scripts/ci/check_catalog_freshness.py

    # + etat de la livraison (necessite gh authentifie)
    python scripts/ci/check_catalog_freshness.py --delivery

    python scripts/ci/check_catalog_freshness.py --delivery --json

Code de sortie : 0 si la publication tient sa promesse, 1 si elle est rompue
(divergence au-dela de la tolerance, ou livraison plus vieille que le seuil,
ou runs gares), **2 si l'etat n'a pas pu etre mesure** -- un refus de mesure
n'est pas un vert.
"""
from __future__ import annotations

import argparse
import datetime as _dt
import json
import os
import subprocess
import sys

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
CATALOG = os.path.join(REPO_ROOT, "COURSE_CATALOG.generated.json")
NOTEBOOK_ROOT = os.path.join(REPO_ROOT, "MyIA.AI.Notebooks")
DELIVERY_BRANCH = "chore/catalog-refresh-pending"

# Repertoires qui ne font pas partie du corpus catalogue.
SKIP = (".claude/worktrees", "_output", "/.ipynb_checkpoints", "/_archive",
        "/node_modules", "/.git/")


def notebooks_on_disk(root: str = NOTEBOOK_ROOT) -> set[str]:
    """Chemins relatifs des notebooks du corpus, tels que le catalogue les cle."""
    found = set()
    for dirpath, dirnames, filenames in os.walk(root):
        if any(s in dirpath.replace("\\", "/") for s in SKIP):
            dirnames[:] = []
            continue
        for name in filenames:
            if name.endswith(".ipynb") and not name.endswith("_output.ipynb"):
                rel = os.path.relpath(os.path.join(dirpath, name), root)
                found.add(rel.replace("\\", "/"))
    return found


def divergence(catalog: list[dict], on_disk: set[str], root: str = NOTEBOOK_ROOT) -> dict:
    """Ecart entre le catalogue et l'arbre qu'il decrit.

    `phantom` : une entree dont le fichier n'existe pas -- le catalogue promet
    un notebook que le lecteur ne trouvera pas.
    `missing`  : un notebook reel qu'aucune entree ne decrit -- il est invisible
    a tout ce qui consomme le catalogue.
    """
    catalogued = {e["path"] for e in catalog}
    phantom = sorted(p for p in catalogued if not os.path.exists(os.path.join(root, p)))
    missing = sorted(on_disk - catalogued)
    return {
        "entries": len(catalog),
        "on_disk": len(on_disk),
        "phantom": phantom,
        "missing": missing,
        "phantom_count": len(phantom),
        "missing_count": len(missing),
        "coverage_pct": round(100.0 * len(catalogued & on_disk) / len(on_disk), 1) if on_disk else 100.0,
    }


def _gh(args: list[str]) -> str:
    proc = subprocess.run(["gh"] + args, capture_output=True, text=True,
                          encoding="utf-8", errors="replace")
    if proc.returncode != 0:
        raise RuntimeError((proc.stderr or "").strip()[:200])
    return proc.stdout


def delivery_state(repo: str, branch: str = DELIVERY_BRANCH, now: _dt.datetime | None = None) -> dict:
    """Age de la PR de livraison et runs CI gares sur sa branche.

    Un run `action_required` n'a jamais tourne : le check requis qu'il porte
    n'existe pas au head, donc la PR reste `BLOCKED` sans qu'aucun rouge ne
    l'explique.
    """
    prs = json.loads(_gh(["pr", "list", "-R", repo, "--state", "open", "--head", branch,
                          "--json", "number,createdAt,updatedAt,mergeStateStatus,headRefOid"]))
    if not prs:
        return {"pr": None, "parked_runs": 0, "age_days": None}
    pr = prs[0]
    head = pr["headRefOid"]
    runs = json.loads(_gh(["run", "list", "-R", repo, "--branch", branch, "--limit", "100",
                           "--json", "databaseId,conclusion,headSha,workflowName"]))
    # Seuls les runs gares AU HEAD COURANT bloquent : un run gare sur un head
    # abandonne ne porte aucun check requis de la PR telle qu'elle est. Les
    # compter tous ferait un organe qui ne peut plus verdir -- indiscernable
    # d'un organe debranche, et qu'on finirait par ignorer.
    parked = [r for r in runs
              if r.get("conclusion") == "action_required" and r.get("headSha") == head]
    stale = sum(1 for r in runs
                if r.get("conclusion") == "action_required" and r.get("headSha") != head)
    now = now or _dt.datetime.now(_dt.timezone.utc)
    created = _dt.datetime.fromisoformat(pr["createdAt"].replace("Z", "+00:00"))
    return {
        "pr": pr["number"],
        "merge_state": pr["mergeStateStatus"],
        "created_at": pr["createdAt"],
        "head": head,
        "age_days": round((now - created).total_seconds() / 86400, 1),
        "parked_runs": len(parked),
        "parked_workflows": sorted({r["workflowName"] for r in parked}),
        "parked_stale_heads": stale,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--delivery", action="store_true",
                        help="mesure aussi l'etat de la PR de livraison (necessite gh)")
    parser.add_argument("--repo", default="jsboige/CoursIA")
    parser.add_argument("--tolerance", type=int, default=0,
                        help="nombre de notebooks divergents tolere (defaut 0)")
    parser.add_argument("--max-age-days", type=float, default=2.0,
                        help="age maximal de la PR de livraison (defaut 2)")
    parser.add_argument("--json", action="store_true", dest="as_json")
    args = parser.parse_args(argv)

    try:
        with open(CATALOG, encoding="utf-8") as handle:
            catalog = json.load(handle)
    except (OSError, ValueError) as exc:
        print("?? catalogue illisible : %s" % str(exc)[:160])
        print("   L'etat est INCONNU, pas sain.")
        return 2

    div = divergence(catalog, notebooks_on_disk())
    report: dict = {"divergence": div}
    unmeasured = []

    if args.delivery:
        try:
            report["delivery"] = delivery_state(args.repo)
        except (RuntimeError, ValueError, KeyError) as exc:
            unmeasured.append("livraison : %s" % str(exc)[:120])
            report["delivery"] = None

    diverged = div["phantom_count"] + div["missing_count"]
    broken = diverged > args.tolerance
    reasons = []
    if broken:
        reasons.append("%d notebook(s) divergents (tolerance %d)" % (diverged, args.tolerance))

    deliv = report.get("delivery")
    if deliv and deliv.get("pr"):
        if deliv["age_days"] is not None and deliv["age_days"] > args.max_age_days:
            broken = True
            reasons.append("PR de livraison #%s ouverte depuis %s j (seuil %s)"
                           % (deliv["pr"], deliv["age_days"], args.max_age_days))
        if deliv["parked_runs"]:
            broken = True
            reasons.append("%d run(s) CI gares en action_required sur %s"
                           % (deliv["parked_runs"], DELIVERY_BRANCH))

    if args.as_json:
        print(json.dumps({"ok": not broken and not unmeasured,
                          "reasons": reasons, "unmeasured": unmeasured,
                          **report}, ensure_ascii=False, indent=2))
        return 2 if unmeasured else (1 if broken else 0)

    print("Catalogue : %d entrees pour %d notebooks sur disque -- couverture %.1f %%"
          % (div["entries"], div["on_disk"], div["coverage_pct"]))
    print("   chemins fantomes (entree sans fichier) : %d" % div["phantom_count"])
    print("   notebooks absents du catalogue         : %d" % div["missing_count"])
    for path in div["phantom"][:5]:
        print("      fantome : %s" % path)
    for path in div["missing"][:5]:
        print("      absent  : %s" % path)

    if deliv and deliv.get("pr"):
        print("\nLivraison : PR #%s (%s), ouverte depuis %s jour(s)"
              % (deliv["pr"], deliv["merge_state"], deliv["age_days"]))
        if deliv["parked_runs"]:
            print("   %d run(s) GARES en action_required -- ils n'ont jamais tourne,"
                  % deliv["parked_runs"])
            print("   donc le check requis qu'ils portent n'existe pas au head et la")
            print("   PR reste BLOCKED sans qu'aucun rouge ne l'explique.")
            for name in deliv["parked_workflows"][:6]:
                print("      gare : %s" % name)
        if deliv.get("parked_stale_heads"):
            print("   (%d run(s) gares sur des heads perimes -- sans effet, non imputes)"
                  % deliv["parked_stale_heads"])
    elif args.delivery and deliv is not None:
        print("\nLivraison : aucune PR ouverte sur %s (le cron n'a pas detecte de derive)"
              % DELIVERY_BRANCH)

    for note in unmeasured:
        print("\n?? non mesure -- %s" % note)

    if unmeasured:
        print("   L'etat est INCONNU, pas sain.")
        return 2
    if broken:
        print("\nLa publication quotidienne ne tient pas sa promesse :")
        for reason in reasons:
            print("   - %s" % reason)
        return 1

    print("\nOK : le catalogue de main decrit l'arbre de main.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
