#!/usr/bin/env python3
"""Vue de triage du pool : le verdict se lit dans les CORPS, pas dans reviewDecision.

Pourquoi cet organe existe (#16926)
-----------------------------------
Le champ ``reviewDecision`` d'une PR de ce depot vaut ``null`` sur ~82 % du
pool ouvert (174/213, mesure 2026-09-19) et y restera **a perpetuite** : le
jeton de review du cluster ne peut poster que des ``COMMENT`` (contrainte
ecrite par le bot lui-meme -- « **[Hermes]** — VERDICT: CONCERNS (contrainte
token CoursIA : COMMENT only, #15511) »). Trier le pool sur ce champ declare
« sans review » une PR qui porte un ``VERDICT: LGTM`` argumente, et le
coordonnateur a publie ce faux compte deux fois avant de le corriger lui-meme.

Le verdict reel vit dans ``reviews[].body`` (prefixe ``VERDICT:``) et dans
les commentaires de persona -- la lecon a deux surfaces de
``scripts/review_coverage.py`` (#16133/#16145 : une persona contrainte en
jeton emet son verdict en COMMENTAIRE d'issue). Le marqueur de persona est
celui du canon ``check_unaddressed_nits`` (en-tete gras admis #14503,
citation backtick exclue #13030) -- importe, jamais copie.

Ce que rend l'organe, par PR :

  - ``DECISION``   : la valeur brute ``reviewDecision`` (structuralement
                     ``null`` sous token COMMENT-only -- affichee pour la
                     distinction, jamais lue comme un verdict) ;
  - ``VERDICT``    : le dernier verdict typé des corps (``LGTM``,
                     ``CONCERNS``, ``CHANGES_REQUESTED``, ``APPROVED``), ou
                     ``VOIX-SANS-VERDICT`` (une voix de persona existe mais
                     n'emet pas de verdict typé), ou ``SANS-REVIEW`` (aucune
                     voix ni sur ``reviews[]`` ni en commentaire de persona).

La distinction demandee par l'acceptance : « sans review » (SANS-REVIEW) n'est
pas « sans decision de review » (tout le reste sous token COMMENT-only).

Bornes de la lecture, dites plutot que cachees
----------------------------------------------
Le balayage GraphQL demande ``reviews(last:5)`` et ``comments(last:10)`` par
PR -- un payload non borne fait 504 sur ce depot (mesure du stale-sweep).
Un verdict plus ancien que cette fenetre lit ``SANS-REVIEW`` a tort ; le
compromis est assume (latest-wins est la semantique du triage : la voix la
plus recente est celle qui gouverne, cf la regle « latest ruling wins ») et
releve de ``--window-reviews``/``--window-comments`` si le besoin apparait.

Gradient d'age (#16926, acceptance 3)
-------------------------------------
``--gradient`` ajoute la repartition LGTM/CONCERNS/sans-voix par quartile
d'age du pool. La mesure fondatrice (80 PRs CLEAN a decision null, 4 lots de
20) : 15/2 LGTM/CONCERNS chez les plus recentes contre 6/8 chez les plus
anciennes -- une PR vieillit parce qu'elle porte une reserve vivante, pas
parce qu'elle attend une review. Re-mesurer apres les cycles de relance de
reserves pour verifier que le gradient s'aplatit.

Usage ::
    python scripts/ci/pool_review_verdicts.py                    # TSV + comptes
    python scripts/ci/pool_review_verdicts.py --gradient         # + gradient d'age
    python scripts/ci/pool_review_verdicts.py --json             # sortie machine

Advisory par construction : exit 0 (un instrument de mesure ne rougit pas --
un echec d'appel rend exit 2 et le dit, jamais un compte muet).
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any

# Le marqueur de persona vient du canon, durci par incidents -- importe,
# jamais copie (une copie locale divergerait en silence).
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import check_unaddressed_nits as nits  # noqa: E402

DEFAULT_REPO = "jsboige/CoursIA"
DEFAULT_WINDOW_REVIEWS = 5
DEFAULT_WINDOW_COMMENTS = 10

#: Le verdict type se lit en DEBUT DE LIGNE (le canon d'emission du cluster :
#: ``**[Hermes]** — VERDICT: CONCERNS (...)`` ou ``VERDICT: LGTM`` nu). Un
#: token cite en milieu de phrase est une MENTION, pas une emission -- la
#: meme discipline que le backtick-exclusion du canon (#13030).
VERDICT_RE = re.compile(
    r"^\s*(?:\*{0,2}\[[^\]]+\]\*{0,2}\s*[—–-]{1,2}\s*)?VERDICT:\s*(LGTM|CONCERNS)\b",
    re.MULTILINE,
)

#: Etats de review REELS de l'API : rares ici (token COMMENT-only) mais
#: authentiques quand un humain review -- ils gouvernent alors.
REAL_STATES = {"APPROVED": "APPROVED", "CHANGES_REQUESTED": "CHANGES_REQUESTED"}

#: Taille de page mesuree : 100 PRs x (reviews + comments) fait 504, et
#: meme 50 PRs x comments(last:10) essuie des 502/504 transitoires (mesures
#: 2026-09-20, premieres executions) -- la page est bornee a 50 et chaque
#: page est retentee une fois devant un 5xx avant d'echouer.
PAGE_SIZE = 50

QUERY = """
query($endCursor: String) {
  repository(owner: "%s", name: "%s") {
    pullRequests(first: %d, states: OPEN, after: $endCursor,
                 orderBy: {field: CREATED_AT, direction: DESC}) {
      pageInfo { hasNextPage endCursor }
      nodes {
        number
        title
        createdAt
        mergeStateStatus
        reviewDecision
        reviews(last: %d) {
          nodes {
            author { login }
            state
            body
            submittedAt
          }
        }
        comments(last: %d) {
          nodes {
            author { login }
            body
            createdAt
          }
        }
      }
    }
  }
}
"""


def run_gh(args: list[str], stdin: str | None = None) -> str:
    """Execute ``gh``. Couture unique : les tests remplacent ce nom."""
    import subprocess

    proc = subprocess.run(
        ["gh", *args],
        input=stdin,
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
    )
    if proc.returncode != 0:
        raise RuntimeError(
            (proc.stderr or proc.stdout or "").strip()[:400]
            or f"gh {' '.join(args[:3])} exited {proc.returncode}"
        )
    return proc.stdout


def _fetch_page(owner: str, name: str, window_reviews: int, window_comments: int,
                cursor: str | None) -> str:
    """Une page GraphQL, retentee une fois devant un 5xx transitoire."""
    import time

    query = QUERY % (owner, name, PAGE_SIZE, window_reviews, window_comments)
    args = ["api", "graphql", "-f", "query=" + query]
    if cursor:
        args += ["-f", "endCursor=" + cursor]
    try:
        return run_gh(args)
    except RuntimeError as exc:
        if "502" not in str(exc) and "504" not in str(exc) and "5xx" not in str(exc):
            raise
        time.sleep(2)
        return run_gh(args)


def fetch_pool(repo: str, window_reviews: int, window_comments: int) -> list[dict[str, Any]]:
    """Balaye les PRs ouvertes en GraphQL pagine (5 pages pour ~213 PRs)."""
    owner, name = repo.split("/", 1)
    nodes: list[dict[str, Any]] = []
    cursor: str | None = None
    for _ in range(40):  # garde pathologique : 40 pages de 50 = 2000 PRs
        raw = _fetch_page(owner, name, window_reviews, window_comments, cursor)
        data = json.loads(raw)
        pulls = ((data.get("data") or {}).get("repository") or {}).get("pullRequests") or {}
        batch = pulls.get("nodes") or []
        if not isinstance(batch, list):
            raise RuntimeError("payload GraphQL inattendu (nodes absent)")
        nodes.extend(n for n in batch if isinstance(n, dict))
        page_info = pulls.get("pageInfo") or {}
        if not page_info.get("hasNextPage"):
            return nodes
        cursor = page_info.get("endCursor")
        if not cursor:
            return nodes
    return nodes


def _voice(body: str | None) -> dict[str, Any] | None:
    """La premiere emission de verdict d'un corps, ou None.

    Un corps peut emettre un VERDICT type (gouverne) ou n'etre qu'une voix
    de persona sans verdict (compte comme voix, verdict inconnu). Un corps
    sans marker de persona ET sans VERDICT n'est pas une voix de review :
    les commentaires de lane et de CI ne sont pas des reviews.
    """
    text = body or ""
    match = VERDICT_RE.search(text)
    if match:
        return {"verdict": match.group(1), "persona": bool(nits._PERSONA_MARKERS_RE.search(text))}
    if nits._PERSONA_MARKERS_RE.search(text):
        return {"verdict": None, "persona": True}
    return None


def classify_pr(node: dict[str, Any]) -> dict[str, Any]:
    """Dernier verdict des deux surfaces, latest-wins. Fonction pure."""
    voices: list[tuple[str, str, dict[str, Any]]] = []  # (iso_ts, surface, voice)
    for review in ((node.get("reviews") or {}).get("nodes") or []):
        state = review.get("state") or ""
        if state in REAL_STATES:
            # Un etat REEL gouverne : c'est le seul canal qui existe sans
            # contrainte de jeton, et il est pose par un humain.
            voices.append(
                (review.get("submittedAt") or "", "review-state", {"verdict": REAL_STATES[state], "persona": False})
            )
            continue
        found = _voice(review.get("body"))
        if found:
            voices.append((review.get("submittedAt") or "", "review-body", found))
    for comment in ((node.get("comments") or {}).get("nodes") or []):
        found = _voice(comment.get("body"))
        if found:
            voices.append((comment.get("createdAt") or "", "comment", found))

    voices.sort(key=lambda v: v[0], reverse=True)
    if not voices:
        verdict = "SANS-REVIEW"
    elif voices[0][2]["verdict"]:
        verdict = voices[0][2]["verdict"]
    else:
        verdict = "VOIX-SANS-VERDICT"
    return {
        "number": node.get("number"),
        "title": node.get("title") or "",
        "createdAt": node.get("createdAt") or "",
        "mergeStateStatus": node.get("mergeStateStatus") or "",
        "decision": node.get("reviewDecision"),
        "verdict": verdict,
        "verdict_surface": voices[0][1] if voices else None,
    }


def gradient(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    """Repartition des verdicts par quartile d'age (recent -> ancien)."""
    ordered = sorted(rows, key=lambda r: r["createdAt"], reverse=True)
    quart = max(1, (len(ordered) + 3) // 4)
    out = []
    for i in range(0, len(ordered), quart):
        chunk = ordered[i : i + quart]
        counts: dict[str, int] = {}
        for r in chunk:
            counts[r["verdict"]] = counts.get(r["verdict"], 0) + 1
        out.append(
            {
                "rank": len(out),
                "n": len(chunk),
                "counts": dict(sorted(counts.items(), key=lambda kv: -kv[1])),
            }
        )
    return out


def parse_args(argv: list[str] | None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    parser.add_argument("--repo", default=DEFAULT_REPO, help="depot cible")
    parser.add_argument("--gradient", action="store_true", help="ajouter le gradient d'age par quartile")
    parser.add_argument("--json", action="store_true", help="sortie JSON machine")
    parser.add_argument(
        "--window-reviews", type=int, default=DEFAULT_WINDOW_REVIEWS,
        help=f"fenetre reviews(last:N) par PR (defaut {DEFAULT_WINDOW_REVIEWS})",
    )
    parser.add_argument(
        "--window-comments", type=int, default=DEFAULT_WINDOW_COMMENTS,
        help=f"fenetre comments(last:N) par PR (defaut {DEFAULT_WINDOW_COMMENTS})",
    )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)
    try:
        nodes = fetch_pool(args.repo, args.window_reviews, args.window_comments)
    except (RuntimeError, ValueError) as exc:
        print(json.dumps({"error": f"balayage illisible : {exc}"}, ensure_ascii=False))
        return 2

    rows = [classify_pr(n) for n in nodes]
    counts: dict[str, int] = {}
    for r in rows:
        counts[r["verdict"]] = counts.get(r["verdict"], 0) + 1
    no_decision = sum(1 for r in rows if r["decision"] is None)

    if args.json:
        payload: dict[str, Any] = {
            "repo": args.repo,
            "pool": len(rows),
            "decision_null": no_decision,
            "verdicts": counts,
            "results": rows,
        }
        if args.gradient:
            payload["gradient"] = gradient(rows)
        print(json.dumps(payload, indent=2, ensure_ascii=False))
        return 0

    print(f"# pool={len(rows)}  decision_null={no_decision}  verdicts={json.dumps(counts, ensure_ascii=False)}")
    for r in sorted(rows, key=lambda r: r["createdAt"]):
        decision = r["decision"] or "-"
        print(
            f"{r['createdAt'][0:10]}\t#{r['number']}\t{r['mergeStateStatus']}\t"
            f"DECISION={decision}\tVERDICT={r['verdict']}\t{r['title'][:70]}"
        )
    if args.gradient:
        print("# gradient d'age (0 = plus recent) :")
        for g in gradient(rows):
            print(f"#   quartile {g['rank']} (n={g['n']}): {json.dumps(g['counts'], ensure_ascii=False)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
