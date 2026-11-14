#!/usr/bin/env python3
"""Nomme les PRs ouvertes dont la TETE n'a aucun run `pull_request`.

Classe mesuree le 14/11 sur #26455 : `update-branch` a produit une tete dont
aucun workflow `pull_request` n'a tourne -- un seul check, declenche par la
review. La chaine de merge a attendu le gate plus de deux heures, avec
`gate=` vide : rien n'a rien signale.

La source est l'API GraphQL : `statusCheckRollup` donne, pour chaque check,
l'evenement du workflow qui l'a produit (`checkSuite.workflowRun.event`). Une
PR est donc nommee quand AUCUN de ses checks ne vient d'un evenement
`pull_request` / `pull_request_target` -- un workflow elague par `paths:` reste
visible (son check porte `skipped`), donc il n'est pas un faux positif.

Sont ecartees :
- les PRs dont la tete est plus recente que `--min-age-min` (la CI n'a pas
  encore eu le temps de tourner) ;
- les PRs qui portent un check EN VOL (`EXPECTED` / `PENDING`) : leur CI est
  dans la file, elle n'est pas absente.

Une PR sans aucun check du tout est nommee : c'est exactement la forme
mesuree sur #26455.

Le verdict est un ETAT, pas une sanction : l'organe nomme, il ne ferme rien.
Le geste de reparation (fermer puis rouvrir la PR, qui relance la CI sans
changer la tete) reste un geste humain ou de lane.

Usage :
    python scripts/ci/detect_heads_without_ci.py --repo owner/name
    python scripts/ci/detect_heads_without_ci.py --repo owner/name --json
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
from datetime import datetime, timezone

DEFAULT_MIN_AGE_MIN = 15.0
#: Evenements de workflow qui produisent les checks d'une PR.
PULL_REQUEST_EVENTS = frozenset({"pull_request", "pull_request_target"})
#: Etats d'un check qui_signalent une CI en vol (et non absente).
IN_FLIGHT_STATES = frozenset({"EXPECTED", "PENDING"})

QUERY = """
query($owner: String!, $repo: String!, $cursor: String) {
  repository(owner: $owner, name: $repo) {
    pullRequests(states: OPEN, first: 25, after: $cursor) {
      pageInfo { hasNextPage endCursor }
      nodes {
        number
        title
        headRefOid
        updatedAt
        commits(last: 1) { nodes { commit { committedDate } } }
        statusCheckRollup {
          contexts(first: 50) {
            nodes {
              ... on CheckRun {
                status
                checkSuite { workflowRun { event } }
              }
              ... on StatusContext { state }
            }
          }
        }
      }
    }
  }
}
"""


def parse_iso(value: str) -> datetime:
    """Parse an ISO-8601 timestamp into an aware datetime."""
    text = (value or "").strip()
    if text.endswith("Z"):
        text = text[:-1] + "+00:00"
    stamp = datetime.fromisoformat(text)
    if stamp.tzinfo is None:
        stamp = stamp.replace(tzinfo=timezone.utc)
    return stamp.astimezone(timezone.utc)


def rollup_contexts(pr: dict) -> list[dict]:
    """The check contexts of a PR (check runs and legacy commit statuses).

    `StatusCheckRollup.contexts` is a connection: the nodes are a union of
    `CheckRun` and `StatusContext`.
    """
    rollup = pr.get("statusCheckRollup") or {}
    contexts = rollup.get("contexts")
    if isinstance(contexts, dict):
        contexts = contexts.get("nodes")
    if contexts is None:
        contexts = rollup.get("nodes") or []
    return list(contexts)


def rollup_events(pr: dict) -> set[str]:
    """The workflow events that produced the PR's checks (empty if none)."""
    events: set[str] = set()
    for context in rollup_contexts(pr):
        event = (((context.get("checkSuite") or {}).get("workflowRun") or {}).get("event"))
        if event:
            events.add(str(event))
    return events


def has_check_in_flight(pr: dict) -> bool:
    """True when a check is queued or pending: the CI is running, not absent."""
    for context in rollup_contexts(pr):
        state = context.get("state") or context.get("status") or ""
        if str(state).upper() in IN_FLIGHT_STATES:
            return True
    return False


def head_date(pr: dict) -> str:
    """The date of the head commit, falling back on the PR's last update."""
    commits = (pr.get("commits") or {}).get("nodes") or []
    if commits:
        committed = (commits[0].get("commit") or {}).get("committedDate")
        if committed:
            return str(committed)
    return str(pr.get("updatedAt") or "")


def head_age_min(pr: dict, now: datetime) -> float | None:
    """Age of the head commit, in minutes -- None when it cannot be read.

    An unreadable date is not evidence of an old head: the organ stays silent
    rather than name a PR whose age it cannot establish.
    """
    raw = head_date(pr)
    if not raw:
        return None
    try:
        return (now - parse_iso(raw)).total_seconds() / 60.0
    except ValueError:
        return None


def heads_without_ci(
    prs: list[dict], now: datetime, min_age_min: float = DEFAULT_MIN_AGE_MIN
) -> list[dict]:
    """The open PRs whose head carries no `pull_request` run, and is old enough.

    A PR is named when none of its checks comes from a `pull_request` event
    and its head is older than `min_age_min`. A CI in flight is not an absent
    CI: those PRs are left alone.
    """
    named: list[dict] = []
    for pr in prs:
        if rollup_events(pr) & PULL_REQUEST_EVENTS:
            continue
        if has_check_in_flight(pr):
            continue
        age = head_age_min(pr, now)
        if age is None or age < min_age_min:
            continue
        named.append(
            {
                "number": pr.get("number"),
                "title": pr.get("title"),
                "head": pr.get("headRefOid"),
                "age_min": round(age, 1),
                "checks": len(rollup_contexts(pr)),
            }
        )
    return named


def fetch_open_prs(repo: str) -> list[dict]:
    """The open PRs of a repository, with their check rollup (GraphQL).

    One paginated query for the whole repository -- the REST list of runs is
    NOT affordable at fleet scale (measured: 100 runs published in 2 min 27 s).
    """
    owner, _, name = repo.partition("/")
    if not owner or not name:
        raise ValueError("repo must be owner/name, got: {}".format(repo))
    prs: list[dict] = []
    cursor = None
    while True:
        args = [
            "gh", "api", "graphql", "-f", "query=" + QUERY,
            "-f", "owner=" + owner, "-f", "repo=" + name,
        ]
        if cursor:
            args += ["-f", "cursor=" + cursor]
        out = subprocess.run(args, capture_output=True, text=True, encoding="utf-8")
        if out.returncode != 0:
            raise RuntimeError("gh api graphql failed: " + out.stderr.strip()[:300])
        payload = json.loads(out.stdout)
        if payload.get("errors"):
            raise RuntimeError("graphql errors: " + json.dumps(payload["errors"])[:300])
        block = (payload.get("data") or {}).get("repository", {}).get("pullRequests", {})
        prs.extend(node for node in (block.get("nodes") or []) if node)
        info = block.get("pageInfo") or {}
        if not info.get("hasNextPage"):
            break
        cursor = info.get("endCursor")
        if not cursor:
            break
    return prs


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--repo", required=True, help="owner/repository")
    parser.add_argument("--min-age-min", type=float, default=DEFAULT_MIN_AGE_MIN)
    parser.add_argument("--now", help="reference instant (ISO 8601), default: now")
    parser.add_argument("--json", action="store_true", help="JSON output")
    args = parser.parse_args(argv)

    now = parse_iso(args.now) if args.now else datetime.now(timezone.utc)
    prs = fetch_open_prs(args.repo)
    named = heads_without_ci(prs, now, args.min_age_min)

    if args.json:
        print(json.dumps({"now": now.isoformat(), "named": named}, indent=2))
    else:
        if not named:
            print("[heads-sans-ci] aucune PR ouverte sans run `pull_request` ({0} PRs lues)".format(len(prs)))
        for entry in named:
            print(
                "[heads-sans-ci] PR #{0} -- tete {1} ({2} min), {3} check(s), "
                "aucun run `pull_request` -- reparer en fermant puis rouvrant "
                "la PR (relance la CI sans changer la tete)".format(
                    entry["number"], (entry["head"] or "")[:8], entry["age_min"],
                    entry["checks"],
                )
            )
    return 0


if __name__ == "__main__":
    sys.exit(main())
