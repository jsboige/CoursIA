#!/usr/bin/env python3
"""PRs approuvees a la tete, vertes, sans dossier valide -- organe de lecture seule (#22089).

## Le trou que cet organe mesure

Une PR peut porter la **disposition de merge** (une review `APPROVED` de
`myia-ai-01` a la tete exacte) et l'**etat de merge** (rollup vert, B.0 clair,
`mergeStateStatus: CLEAN`) sans qu'aucun organe ne la voie :

- `merge_ready.py` ne merge que sur dossier `[ADJOINT PREFLIGHT]` valide ;
- la file du coordinateur part des dossiers recus ;
- une chaine lancee a la main expire au bout de 4 h.

Mesure du 2026-10-22 22:30Z : sur 293 PRs ouvertes non brouillon, 28 portent
une approbation `myia-ai-01` a la tete courante, 14 sont vertes, et 5 d'entre
elles n'avaient **aucune voie de merge** (`no [ADJOINT PREFLIGHT] dossier
comment found`). Sept autres avaient un dossier `STALE`.

## Ce que l'organe rend

Pour chaque PR ouverte non brouillon dont la **derniere review de
`myia-ai-01`** est `APPROVED` **a la tete courante** et qui **n'a pas** de
dossier valide a cette tete :

- `CHAINABLE` -- tout est vert (B.0, checks latest-wins, `mergeStateStatus`,
  DWELL) : a mettre en chaine, ou a faire dossierser ;
- `WAITING <cause>` -- ce qui manque, nomme.

Une PR dont l'approbation porte sur une tete depassee est **absente** : elle
n'est pas approuvee la ou elle en est. Une PR avec un dossier valide est
**absente** aussi : elle est deja dans la voie normale.

## Contrat

- **Lecture seule.** Aucun etat persistant, aucun commentaire, aucun label.
- **Pagination bornee** : `pullRequests(first: 40, after: cursor)`, et
  `latestReviews(first: 20)` plutot que le champ lourd `reviews` complet.
- Les jugements par PR sont **delegues** aux organes qui font foi
  (`check_adjoint_prevalidation.py`, `check_unaddressed_nits.py`,
  `check_run_state.py`, `ci/merge_dwell.py`) : cet organe ne reimplemente
  aucun de leurs verdicts.

Usage :
  python scripts/coordination/approved_without_dossier.py [--json]
                                                          [--limit N]
                                                          [--login LOGIN]
                                                          [--no-dwell]
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parents[1]
REPO_ROOT = SCRIPTS.parent

DEFAULT_REPO = "jsboige/CoursIA"
DEFAULT_APPROVER = "myia-ai-01"
PAGE_SIZE = 40

EXIT_OK = 0
EXIT_ERROR = 2

_PR_QUERY = """
query($owner: String!, $name: String!, $cursor: String) {
  repository(owner: $owner, name: $name) {
    pullRequests(states: OPEN, first: %d, after: $cursor) {
      pageInfo { hasNextPage endCursor }
      nodes {
        number
        title
        isDraft
        headRefOid
        mergeStateStatus
        latestReviews(first: 20) {
          nodes {
            author { login }
            state
            submittedAt
            commit { oid }
          }
        }
      }
    }
  }
}
""" % PAGE_SIZE


# ---------------------------------------------------------------------------
# Lecture des faits (pure : tout ce qui decide est testable sans reseau)
# ---------------------------------------------------------------------------


def parse_pages(pages: list[dict]) -> list[dict]:
    """Aplatit les pages GraphQL en une liste de PR (brouillon exclues)."""
    prs: list[dict] = []
    for page in pages:
        repo = (page.get("data") or {}).get("repository") or {}
        nodes = ((repo.get("pullRequests") or {}).get("nodes")) or []
        for node in nodes:
            if not isinstance(node, dict) or node.get("isDraft"):
                continue
            reviews = ((node.get("latestReviews") or {}).get("nodes")) or []
            prs.append({
                "number": node.get("number"),
                "title": node.get("title") or "",
                "head": node.get("headRefOid") or "",
                "merge_state": node.get("mergeStateStatus") or "UNKNOWN",
                "reviews": [r for r in reviews if isinstance(r, dict)],
            })
    return prs


def page_cursor(pages: list[dict]) -> "str | None":
    """Curseur de la derniere page lue, ou None quand il n'y a plus de page."""
    if not pages:
        return None
    repo = (pages[-1].get("data") or {}).get("repository") or {}
    info = (repo.get("pullRequests") or {}).get("pageInfo") or {}
    if not info.get("hasNextPage"):
        return None
    return info.get("endCursor")


def approval_verdict(pr: dict, approver: str = DEFAULT_APPROVER) -> str:
    """`at_head` / `stale` / `none` pour la derniere review de `approver`.

    « Derniere » se mesure par `submittedAt`, pas par la position dans la
    liste : `latestReviews` rend la derniere review de CHAQUE auteur, sans
    garantie d'ordre entre auteurs, et un auteur peut avoir plusieurs lignes
    si l'API en rend plusieurs.
    """
    rows = [
        r for r in pr.get("reviews") or []
        if ((r.get("author") or {}).get("login") or "") == approver
    ]
    if not rows:
        return "none"
    last = max(rows, key=lambda r: r.get("submittedAt") or "")
    if (last.get("state") or "").upper() != "APPROVED":
        return "none"
    oid = ((last.get("commit") or {}).get("oid")) or ""
    if not oid:
        return "stale"
    return "at_head" if oid == pr.get("head") else "stale"


def candidates(prs: list[dict], approver: str = DEFAULT_APPROVER) -> list[dict]:
    """PRs approuvees a la tete courante (les autres ne sont pas du sujet)."""
    return [p for p in prs if approval_verdict(p, approver) == "at_head"]


def classify(pr: dict, probes: dict) -> tuple[str, list[str]]:
    """`(statut, causes)` -- `CHAINABLE` si tout est vert, sinon `WAITING`.

    `probes` porte les verdicts des organes qui font foi :
      dossier   : {"ready": bool, "verdict": str}
      b0        : {"blocked": bool, "blocking": [...]}
      checks    : {"green": bool, "reds": [...]}
      dwell     : {"ok": bool, "message": str}
      merge_state: str (deja dans `pr["merge_state"]`)
    """
    dossier = probes.get("dossier") or {}
    if dossier.get("ready"):
        # Deja dans la voie normale : pas du sujet de cet organe.
        return "EXCLUDED", ["dossier-valide"]

    causes: list[str] = []
    merge_state = pr.get("merge_state") or "UNKNOWN"
    if merge_state != "CLEAN":
        causes.append("mergeStateStatus:{}".format(merge_state))

    b0 = probes.get("b0") or {}
    if b0.get("blocked"):
        causes.append("b0:{}".format(len(b0.get("blocking") or [])))

    checks = probes.get("checks") or {}
    if not checks.get("green"):
        reds = checks.get("reds") or []
        causes.append("checks:{}".format(",".join(reds[:3]) or "not-green"))

    dwell = probes.get("dwell") or {}
    if dwell.get("ok") is False:
        causes.append("dwell")

    return ("WAITING", causes) if causes else ("CHAINABLE", [])


# ---------------------------------------------------------------------------
# Probes reseau (deleguees aux organes qui font foi)
# ---------------------------------------------------------------------------


def _run_json(args: list[str]) -> "dict | None":
    """Execute un organe en `--json` et rend son objet, ou None si illisible."""
    try:
        proc = subprocess.run(
            [sys.executable, *args],
            cwd=str(REPO_ROOT), capture_output=True, text=True,
            encoding="utf-8", errors="replace", timeout=300,
        )
    except (OSError, subprocess.SubprocessError):
        return None
    text = (proc.stdout or "").strip()
    if not text:
        return None
    # Certains organes prependent une ligne d'usage API : on prend la
    # derniere ligne qui parse comme objet JSON.
    for line in reversed(text.splitlines()):
        line = line.strip()
        if not line.startswith("{"):
            continue
        try:
            parsed = json.loads(line)
        except json.JSONDecodeError:
            continue
        if isinstance(parsed, dict):
            return parsed
    return None


def probe_dossier(pr: int) -> dict:
    data = _run_json(["scripts/check_adjoint_prevalidation.py", str(pr),
                      "--json"])
    if data is None:
        # Fail-closed sur l'organe, pas sur la PR : un dossier illisible se
        # lit comme absent, et le statut dira `WAITING`.
        return {"ready": False, "verdict": "UNREADABLE"}
    return {"ready": bool(data.get("ready")),
            "verdict": data.get("verdict") or "?"}


def probe_b0(pr: int) -> dict:
    data = _run_json(["scripts/check_unaddressed_nits.py", str(pr), "--json"])
    if data is None:
        return {"blocked": True, "blocking": ["unreadable"]}
    return {"blocked": bool(data.get("blocked")),
            "blocking": data.get("blocking") or []}


def probe_checks(pr: int, head: str) -> dict:
    data = _run_json(["scripts/check_run_state.py", "--pr", str(pr), "--json"])
    if data is None or data.get("head") != head:
        # Un etat de checks lu a une autre tete ne dit rien de celle-ci.
        return {"green": False, "reds": ["not-readable-at-head"]}
    latest = data.get("latest") or {}
    reds = sorted(
        name for name, leg in latest.items()
        if (leg or {}).get("conclusion") != "success"
    )
    residual = data.get("residual_reds") or []
    reds += sorted(
        r.get("name") or "?" for r in residual if isinstance(r, dict)
    )
    return {"green": not reds, "reds": reds}


def probe_dwell(pr: int, head: str, repo: str) -> dict:
    sys.path.insert(0, str(SCRIPTS / "ci"))
    try:
        import merge_dwell  # noqa: PLC0415 -- import tardif, module de CI
    except ImportError:
        return {"ok": None, "message": "merge_dwell illisible"}
    try:
        ok, message = merge_dwell.check(repo, head, pr)
    except Exception as exc:  # noqa: BLE001 -- un organe muet ne deroge pas
        return {"ok": None, "message": "merge_dwell: {}".format(exc)}
    return {"ok": ok, "message": message}


def gh_graphql(query: str, variables: dict) -> dict:
    cmd = ["gh", "api", "graphql", "-f", "query=" + query]
    for key, value in variables.items():
        if value is None:
            continue
        cmd += ["-f", "{}={}".format(key, value)]
    proc = subprocess.run(cmd, capture_output=True, text=True,
                          encoding="utf-8", errors="replace")
    if proc.returncode != 0:
        raise RuntimeError((proc.stderr or "").strip()[:400])
    return json.loads(proc.stdout or "{}")


def fetch_prs(repo: str, limit: "int | None" = None) -> list[dict]:
    owner, name = repo.split("/", 1)
    pages: list[dict] = []
    cursor = None
    while True:
        page = gh_graphql(_PR_QUERY, {"owner": owner, "name": name,
                                      "cursor": cursor})
        pages.append(page)
        cursor = page_cursor([page])
        prs = parse_pages(pages)
        if cursor is None or (limit is not None and len(prs) >= limit):
            break
    prs = parse_pages(pages)
    return prs[:limit] if limit is not None else prs


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def render(repo: str, rows: list[dict], approver: str) -> str:
    if not rows:
        return ("aucune PR approuvee a la tete sans dossier valide "
                "({}, approbateur {})".format(repo, approver))
    lines = []
    chain = sum(1 for r in rows if r["status"] == "CHAINABLE")
    lines.append("#{} PR(s) approuvee(s) a la tete sans dossier valide "
                 "-- {} CHAINABLE".format(len(rows), chain))
    for row in rows:
        cause = ", ".join(row["causes"]) or "-"
        lines.append("  {} {} -- {}".format(
            "#{}".format(row["pr"]), row["status"], cause))
    return "\n".join(lines)


def main(argv: "list[str] | None" = None) -> int:
    parser = argparse.ArgumentParser(
        description="PRs approuvees a la tete, vertes, sans dossier valide "
                    "(lecture seule, #22089).")
    parser.add_argument("--repo", default=DEFAULT_REPO)
    parser.add_argument("--login", default=DEFAULT_APPROVER,
                        help="approbateur dont la review fait foi")
    parser.add_argument("--limit", type=int, default=None,
                        help="borne le nombre de PRs lues (diagnostic)")
    parser.add_argument("--no-dwell", action="store_true",
                        help="saute la probe DWELL (plus rapide, moins sur)")
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)

    try:
        prs = fetch_prs(args.repo, args.limit)
    except (RuntimeError, json.JSONDecodeError) as exc:
        print("ERROR: lecture des PRs impossible: {}".format(exc),
              file=sys.stderr)
        return EXIT_ERROR

    rows: list[dict] = []
    for pr in candidates(prs, args.login):
        probes = {
            "dossier": probe_dossier(pr["number"]),
        }
        status, causes = classify(pr, probes)
        if status == "EXCLUDED":
            continue
        probes["b0"] = probe_b0(pr["number"])
        probes["checks"] = probe_checks(pr["number"], pr["head"])
        probes["dwell"] = ({"ok": None, "message": "saute"}
                           if args.no_dwell
                           else probe_dwell(pr["number"], pr["head"],
                                            args.repo))
        status, causes = classify(pr, probes)
        rows.append({
            "pr": pr["number"],
            "title": pr["title"],
            "head": pr["head"],
            "merge_state": pr["merge_state"],
            "dossier": probes["dossier"]["verdict"],
            "status": status,
            "causes": causes,
        })

    rows.sort(key=lambda r: (r["status"] != "CHAINABLE", r["pr"]))
    if args.json:
        print(json.dumps({"repo": args.repo, "approver": args.login,
                          "scanned": len(prs), "rows": rows},
                         ensure_ascii=False, indent=1))
    else:
        print(render(args.repo, rows, args.login))
    return EXIT_OK


if __name__ == "__main__":
    sys.exit(main())
