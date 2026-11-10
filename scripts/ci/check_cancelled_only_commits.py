#!/usr/bin/env python3
"""Replay #22088's exit criterion at the colour a human actually reads.

## Why this exists

`statusCheckRollup.state` collapses every leg of a commit into one colour. A leg
in `CANCELLED` is not a failure -- no test, no guard, no assertion disagreed with
the commit -- yet GitHub paints it the same red cross as a real failure. Measured
consequence (#22088): `main` read `FAILURE` on 22 of its last 40 commits, and on
19 of those the only legs in cause were cancellations. The organs that read
main's colour (`MAIN_RED_WORKFLOWS` of `merge_dwell.py`, #22085) had to strip
`cancelled` by hand, per workflow, for ever.

`check_concurrency_conj.py` is the STATIC half of the answer: it refuses the
workflow conjunction that produces the cancellation. This script is the RUNTIME
half: it reads the rollup and names the commits whose only non-green legs are
cancellations, whatever workflow emitted them.

## Why the criterion has to name the class, not one workflow

#22088 was written against `Build Quarto site` / `Deploy to GitHub Pages`, and
that instance IS fixed. Measured on the 20 commits that follow #22099 with the
very instrument the issue names (GraphQL `statusCheckRollup`): no commit carries
a Quarto leg at all once superseded, because a run cancelled while PENDING emits
no check-run -- 38 of the 38 cancelled runs of 2026-11-01 have zero jobs.

But those same 20 commits still contain two whose red cross has no cause other
than a cancellation, emitted by `Scripts Tests (CPU)` and `probeAddresses banner
guard`. A criterion naming one workflow would have declared victory over the
class while two instances of it were still on screen.

## Verdicts

  OK              the rollup is not FAILURE, or the failure is earned
                  (at least one non-green leg really failed)
  CANCELLED_ONLY  FAILURE, and every non-green leg is a cancellation  <- offender
  PENDING         the rollup has not settled
  UNKNOWN         FAILURE with no readable leg, or a truncated leg list

Truncation is fail-closed on the accusation: a commit whose leg list hit the
100-context page limit is NEVER reported as an offender, because a real failure
could be sitting just past the page. Silence from truncation is not a clean bill
either -- UNKNOWN is counted and printed.

Run: python scripts/ci/check_cancelled_only_commits.py --commits 20
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys

EXIT_CLEAN, EXIT_OFFENDERS, EXIT_BROKEN = 0, 1, 2

# Conclusions that do not make a commit red on their own. `SKIPPED` is the
# normal state of a leg gated by `if:`; `NEUTRAL` is an advisory that declined
# to vote. Both are legitimately `None` on a commit whose run never started.
NON_GREEN_IGNORED = {"SUCCESS", "SKIPPED", "NEUTRAL", None, "None", ""}
CANCELLED = {"CANCELLED", "cancelled"}

DEFAULT_REPO = "jsboige/CoursIA"
DEFAULT_REF = "refs/heads/main"

HISTORY_FIELDS = """
          history(first: $n) {
            nodes {
              oid
              committedDate
              messageHeadline
              statusCheckRollup {
                state
                contexts(first: 100) {
                  pageInfo { hasNextPage }
                  nodes {
                    __typename
                    ... on CheckRun { name conclusion }
                    ... on StatusContext { context state }
                  }
                }
              }
            }
          }"""

# Deux racines pour la meme fenetre : la tete d'une ref (usage courant), ou un
# commit donne (`--until`) -- le critere de sortie d'une PR se definit sur les
# commits qui SUIVENT son merge, donc il faut pouvoir s'y ancrer.
QUERY_REF = (
    "query($owner:String!, $name:String!, $ref:String!, $n:Int!) {"
    " repository(owner: $owner, name: $name) {"
    "  ref(qualifiedName: $ref) { target { ... on Commit {" + HISTORY_FIELDS + " } } } } }"
)
HISTORY_ONE = """
              oid
              committedDate
              messageHeadline
              statusCheckRollup {
                state
                contexts(first: 100) {
                  pageInfo { hasNextPage }
                  nodes {
                    __typename
                    ... on CheckRun { name conclusion }
                    ... on StatusContext { context state }
                  }
                }
              }"""

QUERY_ONE = (
    "query($owner:String!, $name:String!, $oid:GitObjectID!) {"
    " repository(owner: $owner, name: $name) {"
    "  object(oid: $oid) { ... on Commit {" + HISTORY_ONE + " } } } }"
)


def leg_name(node):
    """A check-run carries `name`, a legacy status context carries `context`."""
    return node.get("name") or node.get("context") or "(sans nom)"


def leg_conclusion(node):
    """Same duality: check-runs conclude, status contexts have a state."""
    return node.get("conclusion") or node.get("state")


def classify(rollup_state, legs, truncated=False):
    """Verdict for one commit. `legs` is an iterable of (name, conclusion).

    A red cross is EARNED when at least one non-green leg really failed; it is
    BORROWED when every non-green leg is a cancellation. That distinction is the
    whole point of the issue: the two are pixel-identical in the UI.
    """
    if rollup_state in (None, "", "SUCCESS"):
        return "OK"
    if rollup_state == "PENDING":
        return "PENDING"
    if rollup_state != "FAILURE":
        return "UNKNOWN"

    non_green = [(n, c) for n, c in legs if c not in NON_GREEN_IGNORED]
    if not non_green:
        # FAILURE with nothing readable: a conclusion we do not model, not a
        # clean commit. Never accused, never blessed.
        return "UNKNOWN"
    if all(c in CANCELLED for _, c in non_green):
        # The accusation is the only claim truncation can corrupt: a real
        # failure could be sitting past the page. An earned failure that is
        # already visible stays earned whatever the rest of the list holds.
        return "UNKNOWN" if truncated else "CANCELLED_ONLY"
    return "OK"


def analyse(commit):
    """One row of the report, from a GraphQL history node."""
    rollup = commit.get("statusCheckRollup") or {}
    contexts = rollup.get("contexts") or {}
    nodes = contexts.get("nodes") or []
    truncated = bool((contexts.get("pageInfo") or {}).get("hasNextPage"))
    legs = [(leg_name(n), leg_conclusion(n)) for n in nodes]
    verdict = classify(rollup.get("state"), legs, truncated=truncated)
    return {
        "oid": commit.get("oid", ""),
        "date": commit.get("committedDate", ""),
        "headline": commit.get("messageHeadline", ""),
        "rollup": rollup.get("state"),
        "verdict": verdict,
        "truncated": truncated,
        "non_green": [f"{n}={c}" for n, c in legs if c not in NON_GREEN_IGNORED],
    }


def resolve(rev):
    """Un GitObjectID GraphQL exige l'OID complet : une abreviation se resout ici."""
    if len(rev) == 40:
        return rev
    proc = subprocess.run(
        ["git", "rev-parse", rev], capture_output=True, text=True,
        encoding="utf-8", errors="replace",
    )
    oid = (proc.stdout or "").strip()
    if proc.returncode != 0 or len(oid) != 40:
        raise RuntimeError(f"revision introuvable : {rev}")
    return oid


def _graphql(args):
    proc = subprocess.run(
        ["gh", "api", "graphql", *args],
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
    )
    if proc.returncode != 0:
        raise RuntimeError((proc.stderr or proc.stdout or "").strip()[:800])
    return json.loads(proc.stdout)


def fetch(repo, ref, count):
    """Fenetre = les `count` commits les plus recents de `ref`, en un appel."""
    owner, name = repo.split("/", 1)
    payload = _graphql([
        "-f", "query=" + QUERY_REF,
        "-f", f"owner={owner}",
        "-f", f"name={name}",
        "-f", f"ref={ref}",
        "-F", f"n={int(count)}",
    ])
    history = (
        payload.get("data", {}).get("repository", {}).get("ref", {})
        .get("target", {}).get("history") or {}
    )
    nodes = history.get("nodes")
    if nodes is None:
        raise RuntimeError("history introuvable dans la reponse GraphQL")
    return nodes


def fetch_after(repo, sha, count, ref):
    """Fenetre = les `count` commits immediatement APRES `sha` (critere d'une PR).

    GraphQL ne remonte le temps que vers le passe : la position de l'ancre se lit
    donc dans l'historique local, puis les commits de la fenetre sont interroges
    un par un. Sans checkout git, cet ancrage est indisponible -- la fenetre de
    tete reste utilisable, et l'echec est explicite plutot que silencieux.
    """
    anchor = resolve(sha)
    proc = subprocess.run(
        ["git", "log", "--first-parent", "--format=%H", ref],
        capture_output=True, text=True, encoding="utf-8", errors="replace",
    )
    if proc.returncode != 0:
        raise RuntimeError(
            "--after exige un checkout git (historique local introuvable) : "
            + (proc.stderr or "").strip()[:200]
        )
    order = (proc.stdout or "").split()
    if anchor not in order:
        raise RuntimeError(f"{sha} n'appartient pas a l'historique de {ref}")
    i = order.index(anchor)
    window = order[max(0, i - count):i]
    if not window:
        raise RuntimeError(f"aucun commit apres {sha} dans {ref}")
    owner, name = repo.split("/", 1)
    nodes = []
    for oid in window:
        payload = _graphql([
            "-f", "query=" + QUERY_ONE,
            "-f", f"owner={owner}",
            "-f", f"name={name}",
            "-f", f"oid={oid}",
        ])
        node = payload.get("data", {}).get("repository", {}).get("object")
        if not node:
            raise RuntimeError(f"commit illisible : {oid}")
        nodes.append(node)
    return nodes


def main(argv=None):
    parser = argparse.ArgumentParser(
        description="Rejoue le critere de sortie #22088 sur les N derniers commits."
    )
    parser.add_argument("--repo", default=DEFAULT_REPO, help="owner/name")
    parser.add_argument("--ref", default=DEFAULT_REF, help="ref complete")
    parser.add_argument("--commits", type=int, default=20, help="taille de la fenetre")
    parser.add_argument(
        "--after",
        default=None,
        help="fenetre = les commits qui SUIVENT ce SHA, au lieu de la tete de --ref -- "
             "c'est la lecture du critere de sortie d'une PR, qui se mesure sur les "
             "commits posterieurs a son merge (exige un checkout git)",
    )
    parser.add_argument("--json", action="store_true", help="sortie machine")
    args = parser.parse_args(argv)

    if not 1 <= args.commits <= 100:
        print("--commits doit etre entre 1 et 100 (limite de page GitHub)", file=sys.stderr)
        return EXIT_BROKEN

    try:
        if args.after:
            nodes = fetch_after(args.repo, args.after, args.commits, args.ref)
        else:
            nodes = fetch(args.repo, args.ref, args.commits)
    except Exception as exc:  # noqa: BLE001 -- instrument joignable ou pas
        print(f"[cancelled-only] instrument injoignable : {exc}", file=sys.stderr)
        return EXIT_BROKEN

    rows = [analyse(n) for n in nodes]
    offenders = [r for r in rows if r["verdict"] == "CANCELLED_ONLY"]
    unknown = [r for r in rows if r["verdict"] == "UNKNOWN"]
    earned = [r for r in rows if r["verdict"] == "OK" and r["rollup"] == "FAILURE"]

    if args.json:
        print(json.dumps({
            "repo": args.repo,
            "ref": args.ref,
            "after": args.after,
            "window": len(rows),
            "offenders": [r["oid"] for r in offenders],
            "unknown": [r["oid"] for r in unknown],
            "earned_failure": [r["oid"] for r in earned],
            "commits": rows,
        }, indent=2, ensure_ascii=False))
    else:
        print(f"{args.repo} {args.ref} -- fenetre de {len(rows)} commits\n")
        print(f"{'date':20s} {'sha':11s} {'rollup':8s} {'verdict':15s} jambes non vertes")
        for r in rows:
            print(
                f"{r['date'][:19]:20s} {r['oid'][:10]:11s} "
                f"{str(r['rollup']):8s} {r['verdict']:15s} "
                f"{', '.join(r['non_green'][:3]) or '-'}"
            )
        print()
        print(f"rouges MERITES (une jambe a vraiment echoue) : {len(earned)}")
        print(f"rouges EMPRUNTES (annulation seule)          : {len(offenders)}")
        print(f"indetermines (troncature/illisible)          : {len(unknown)}")
        for r in offenders:
            print(f"  EMPRUNTE {r['oid'][:10]}  {r['headline'][:60]}")
            print(f"            {', '.join(r['non_green'][:5])}")

    return EXIT_OFFENDERS if offenders else EXIT_CLEAN


if __name__ == "__main__":
    sys.exit(main())
