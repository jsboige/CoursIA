#!/usr/bin/env python3
"""PRs approuvees, vertes, chainables -- organe de lecture seule (#22089).

## Le trou que cet organe mesure

Une PR peut porter la **disposition de merge** (une approbation de
`myia-ai-01` qui couvre la tete courante) et l'**etat de merge** (checks
verts, B.0 clair, `mergeStateStatus` acceptable) sans qu'aucun organe ne la
voie :

- `merge_ready.py` ne merge que sur la review du coordinateur, et rien ne
  liste les PRs qui la portent deja ;
- la file du coordinateur part de ce qu'il a lu, pas de ce qui est pret ;
- une chaine lancee a la main expire au bout de 4 h.

## Ce que l'organe rend

Pour chaque PR ouverte non brouillon dont la **derniere voix de
`myia-ai-01`** est `APPROVED` et **couvre la tete courante** :

- `CHAINABLE` -- tout est vert (B.0, checks latest-wins, `mergeStateStatus`,
  DWELL) : a mettre en chaine ;
- `WAITING <cause>` -- ce qui manque, nomme.

## Deux changements du 2026-11-14 (arbitrage ai-01)

1. **L'approbation couvrante compte** (Q131, CLAUDE.md section A). Une
   approbation posee sur une tete anterieure couvre encore la tete courante
   quand les deux ne different que par des rafraichissements de base prouves
   content-free. Le predicat qui fait foi est
   `merge_ready.coordinator_approval_reason` : il est **importe**, jamais
   recopie (organ-first), pour que la question « la lecture du coordinateur
   couvre-t-elle cette tete ? » ne puisse pas recevoir deux reponses, celle
   de l'organe de merge et celle-ci.
2. **La sonde de dossier a disparu.** Depuis le 2026-11-05 `merge_ready`
   n'exige plus de dossier `[ADJOINT PREFLIGHT]` : une sonde de dossier
   n'aurait plus mesure qu'un vestige, et aurait exclu des PRs qui sont
   precisement le sujet.

`unstable` est traite par le predicat importe `unstable_state_reason`
(#25059) : un etat « unstable » accepte par l'organe de merge ne doit pas
sortir `WAITING` ici. Sans runner (mesure impossible) il reste fail-closed.

## Contrat

- **Lecture seule.** Aucun etat persistant, aucun commentaire, aucun label.
- **Deux modes de lecture.** Par defaut GraphQL pagine
  (`pullRequests`, `latestReviews`, 3 appels pour ~200 PRs). `--rest`
  enumere en REST seul (`pulls?state=open`) puis relit les reviews de chaque
  PR par la surface typee de `merge_ready` : plus couteux en points `core`,
  mais il ne touche pas la porte GraphQL partagee quand la flotte l'a videe.
  Il est reserve au depot de `merge_ready` (la relecture typee y est epinglee).
- Les jugements par PR sont **delegues** aux organes qui font foi
  (`check_unaddressed_nits.py`, `check_run_state.py`, `ci/merge_dwell.py`,
  `merge_ready.coordinator_approval_reason`,
  `merge_ready.unstable_state_reason`) : cet organe ne reimplemente aucun de
  leurs verdicts.

Usage :
  python scripts/coordination/approved_without_dossier.py [--json]
                                                          [--rest]
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

# `merge_ready` vit dans le meme repertoire et importe ses dependances depuis
# `scripts/` et `scripts/ci` : il pose ses propres chemins a l'import. On pose
# seulement les deux notres, avant lui.
for _dir in (SCRIPTS, SCRIPTS / "coordination"):
    if str(_dir) not in sys.path:
        sys.path.insert(0, str(_dir))

# Organe de decision : importe, jamais recopie (organ-first).
import merge_ready  # noqa: E402

DEFAULT_REPO = "jsboige/CoursIA"
DEFAULT_APPROVER = merge_ready.COORDINATOR_USER
PAGE_SIZE = 40
REST_PAGE_SIZE = 100

EXIT_OK = 0
EXIT_ERROR = 2

# Les deux verdicts qui disent « la lecture du coordinateur porte sur cette
# tete ». `at_head` est le geste explicite ; `covering` est la couverture Q131
# a travers des rafraichissements de base sans conflit.
ACCEPTED_APPROVALS = ("at_head", "covering")

# Conclusions de check-run classees ROUGES, miroir des trois organes canoniques
# (check_run_state.py, check_adjoint_prevalidation.py, check_stale_guard_reds.py).
# `skipped` et `neutral` sont des VERTES : le predicate precedent (`!= "success"`)
# les comptait comme rouges et fabriquait des rouges fantomes sur des jambes
# desactivees (ex. Build Quarto / Deploy Pages sur une PR de docs).
RED_CONCLUSIONS = {"failure", "timed_out"}

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
        baseRefOid
        mergeStateStatus
        latestReviews(first: 20) {
          nodes {
            author { login __typename }
            state
            body
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
                "base_oid": node.get("baseRefOid") or "",
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


def parse_rest(items: list[dict]) -> list[dict]:
    """Aplatit une page REST `pulls?state=open` en PR (brouillon exclues).

    La liste REST ne porte pas les reviews : elles sont relues par la surface
    typee de `merge_ready` au moment du verdict, une PR a la fois. Elle porte
    `mergeable_state`, souvent `unknown` sur cette route (GitHub ne calcule
    l'etat que sur la lecture unitaire) : la valeur est donc rafraichie pour
    les seules PRs candidates.
    """
    prs: list[dict] = []
    for item in items:
        if not isinstance(item, dict) or item.get("draft"):
            continue
        prs.append({
            "number": item.get("number"),
            "title": item.get("title") or "",
            "head": ((item.get("head") or {}).get("sha")) or "",
            "base_oid": ((item.get("base") or {}).get("sha")) or "",
            "merge_state": str(
                item.get("mergeable_state") or "unknown"
            ).upper(),
            "reviews": [],
        })
    return prs


def _approval_view(pr: dict) -> dict:
    """La vue que `merge_ready` attend pour lire la voix du coordinateur."""
    return {
        "number": pr.get("number"),
        "reviews": pr.get("reviews") or [],
        "baseRefOid": pr.get("base_oid") or "",
    }


def _generic_verdict(pr: dict, approver: str) -> str:
    """`at_head` / `stale` / `none` pour un approbateur NON coordinateur.

    Hors `myia-ai-01`, il n'existe pas de regle de couverture Q131 : seule la
    tete exacte est reconnue. « Derniere » se mesure par `submittedAt`, pas
    par la position dans la liste.
    """
    rows = [
        r for r in pr.get("reviews") or []
        if ((r.get("author") or {}).get("login") or "") == approver
    ]
    if not rows:
        return "none"
    last = max(rows, key=lambda r: r.get("submittedAt")
               or r.get("submitted_at") or "")
    if (last.get("state") or "").upper() != "APPROVED":
        return "none"
    oid = ((last.get("commit") or {}).get("oid")) or ""
    if not oid:
        return "stale"
    return "at_head" if oid == pr.get("head") else "stale"


def approval_verdict(pr: dict, approver: str = DEFAULT_APPROVER,
                     runner=None, gh_env=None) -> str:
    """`covering` / `at_head` / `stale` / `none` pour la voix de `approver`.

    `covering` (Q131) : l'approbation porte sur une tete anterieure et n'en
    differe que par des rafraichissements de base prouves content-free.

    Le verdict est rendu par l'organe de merge lui-meme
    (`coordinator_approval_oid`, puis `coordinator_approval_reason` pour la
    couverture), jamais par une copie locale du predicat.

    Sans `runner`, la couverture n'est pas mesurable : une approbation sur une
    tete anterieure reste `stale`. C'est fail-closed, jamais permissif.
    """
    if approver != DEFAULT_APPROVER:
        return _generic_verdict(pr, approver)

    view = _approval_view(pr)
    head = pr.get("head") or ""

    # GraphQL : les lignes portent leur `__typename`, la lecture pure suffit
    # et ne coute rien. REST : la liste n'apporte aucune review, c'est la
    # relecture typee par le runner qui fait foi (un appel par PR).
    oid = merge_ready.coordinator_approval_oid(view)
    if oid is None and runner is not None and not view["reviews"]:
        oid = merge_ready.coordinator_approval_oid(view, runner, gh_env)
    if oid is None:
        return "none"
    if oid == head:
        return "at_head"
    if runner is None:
        return "stale"
    reason = merge_ready.coordinator_approval_reason(view, head, runner, gh_env)
    return "covering" if reason is None else "stale"


def candidates(prs: list[dict], approver: str = DEFAULT_APPROVER,
               runner=None, gh_env=None) -> list[dict]:
    """PRs dont la voix de `approver` couvre la tete courante."""
    return [
        p for p in prs
        if approval_verdict(p, approver, runner, gh_env) in ACCEPTED_APPROVALS
    ]


def screen(prs: list[dict], approver: str = DEFAULT_APPROVER,
           runner=None, gh_env=None) -> list[dict]:
    """Trie les PRs par disposition du coordinateur, sans reseau supplementaire.

    Une ligne par PR dont la voix de `approver` existe :

      {"pr": <dict>, "approval": "at_head"|"covering"|"stale",
       "status": None | "WAITING", "causes": [...]}

    `status is None` = a classer sur les probes. `WAITING` = deja tranche :
    une approbation que le rafraichissement a perimee n'est pas chainable, et
    le geste attendu est nomme (`approval:stale`, relecture du coordinateur).
    Mesurer ses checks ne changerait pas le verdict et couterait trois
    organes pour rien.

    Une PR sans aucune voix du coordinateur (`none`) n'est pas du sujet : la
    liste des PRs vertes non approuvees est un autre livrable.
    """
    out: list[dict] = []
    for pr in prs:
        verdict = approval_verdict(pr, approver, runner, gh_env)
        if verdict == "none":
            continue
        if verdict == "stale":
            out.append({"pr": pr, "approval": verdict,
                        "status": "WAITING", "causes": ["approval:stale"]})
        else:
            out.append({"pr": pr, "approval": verdict,
                        "status": None, "causes": []})
    return out


def classify(pr: dict, probes: dict, runner=None, gh_env=None) -> tuple[str, list[str]]:
    """`(statut, causes)` -- `CHAINABLE` si tout est vert, sinon `WAITING`.

    `probes` porte les verdicts des organes qui font foi :
      b0        : {"blocked": bool, "blocking": [...]}
      checks    : {"green": bool, "reds": [...]}
      dwell     : {"ok": bool | None, "message": str}
      merge_state: str (deja dans `pr["merge_state"]`)

    `unstable` n'est pas un refus automatique (#25059) : la decision est
    demandee a `merge_ready.unstable_state_reason`, sur les jambes, au pli du
    gate. Sans runner, la mesure n'existe pas et l'etat est traite comme un
    refus -- un `WAITING` nomme, jamais un `CHAINABLE` suppose.
    """
    causes: list[str] = []

    merge_state = str(pr.get("merge_state") or "UNKNOWN").upper()
    if merge_state == "UNSTABLE":
        reason: "str | None" = None
        if runner is not None and isinstance(pr.get("number"), int):
            reason, _detail = merge_ready.unstable_state_reason(
                runner, pr["number"], pr.get("head") or "", gh_env)
        else:
            reason = "unstable-not-measured"
        if reason is not None:
            causes.append("mergeStateStatus:UNSTABLE:{}".format(reason))
    elif merge_state != "CLEAN":
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
    # Les organes delegues sortent soit un JSON sur une ligne, soit un
    # bloc indent unique (check_unaddressed_nits et check_run_state
    # impriment indent=1, multi-lignes par construction) : on tente le
    # texte entier d'abord, sinon ces blocs ne sont jamais lus.
    try:
        whole = json.loads(text)
        if isinstance(whole, dict):
            return whole
    except json.JSONDecodeError:
        pass
    # Repli : certains organes prependent une ligne d'usage API ; on prend
    # la derniere ligne qui parse comme objet JSON.
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


def _gh_json(path: str):
    """`gh api <path>` -> objet ou liste, ou None si illisible."""
    try:
        proc = subprocess.run(
            ["gh", "api", path], cwd=str(REPO_ROOT), capture_output=True,
            text=True, encoding="utf-8", errors="replace", timeout=120,
        )
    except (OSError, subprocess.SubprocessError):
        return None
    if proc.returncode != 0:
        return None
    try:
        return json.loads(proc.stdout or "")
    except json.JSONDecodeError:
        return None


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
        if (leg or {}).get("conclusion") in RED_CONCLUSIONS
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


def probe_merge_state_rest(repo: str, pr: int) -> "str | None":
    """Etat de merge autoritatif d'une PR candidate, en REST unitaire.

    La liste `pulls?state=open` rend souvent `unknown` : GitHub ne calcule
    l'etat que sur la lecture unitaire. Rend None si illisible -- l'appelant
    laisse alors `UNKNOWN`, qui sort en `WAITING` nomme.
    """
    data = _gh_json("repos/{}/pulls/{}".format(repo, pr))
    if not isinstance(data, dict):
        return None
    state = str(data.get("mergeable_state") or "").upper()
    return state or None


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
    """Enumeration GraphQL : 3 appels pour ~200 PRs, reviews comprises."""
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


def fetch_prs_rest(repo: str, limit: "int | None" = None) -> list[dict]:
    """Enumeration REST seule (`pulls?state=open`), sans reviews.

    Les reviews ne sont pas dans la liste : elles sont relues une PR a la
    fois par la surface typee de `merge_ready`, au moment du verdict. Cout :
    ~1 point `core` par PR ouverte. Ce mode existe pour les fenetres ou la
    porte GraphQL partagee est videe -- pas pour remplacer le mode nominal.
    """
    prs: list[dict] = []
    page = 1
    while True:
        batch = _gh_json("repos/{}/pulls?state=open&per_page={}&page={}".format(
            repo, REST_PAGE_SIZE, page))
        if not isinstance(batch, list):
            raise RuntimeError(
                "pulls?state=open page {} illisible".format(page))
        prs.extend(parse_rest(batch))
        if len(batch) < REST_PAGE_SIZE:
            break
        if limit is not None and len(prs) >= limit:
            break
        page += 1
    return prs[:limit] if limit is not None else prs


def _runner_for(repo: str):
    """Runner reel seulement sur le depot de `merge_ready`.

    `_typed_reviews` epingle `merge_ready.REPO` : sur un autre depot, la
    relecture typee lirait le mauvais corpus. Mieux vaut ne pas mesurer que
    mesurer ailleurs.
    """
    if repo != merge_ready.REPO:
        return None
    return merge_ready.SubprocessRunner()


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def render(repo: str, rows: list[dict], approver: str) -> str:
    if not rows:
        return ("aucune PR dont la voix de {} couvre la tete et qui soit "
                "chainable ({})".format(approver, repo))
    lines = []
    chain = sum(1 for r in rows if r["status"] == "CHAINABLE")
    lines.append("#{} PR(s) approuvee(s) a la tete ou couvrante "
                 "-- {} CHAINABLE".format(len(rows), chain))
    for row in rows:
        cause = ", ".join(row["causes"]) or "-"
        lines.append("  {} {} [{}] -- {}".format(
            "#{}".format(row["pr"]), row["status"], row["approval"], cause))
    return "\n".join(lines)


def main(argv: "list[str] | None" = None) -> int:
    parser = argparse.ArgumentParser(
        description="PRs approuvees (tete ou couvrante), vertes, chainables "
                    "(lecture seule, #22089).")
    parser.add_argument("--repo", default=DEFAULT_REPO)
    parser.add_argument("--login", default=DEFAULT_APPROVER,
                        help="approbateur dont la review fait foi")
    parser.add_argument("--limit", type=int, default=None,
                        help="borne le nombre de PRs lues (diagnostic)")
    parser.add_argument("--rest", action="store_true",
                        help="enumere en REST seul (porte GraphQL videe)")
    parser.add_argument("--no-dwell", action="store_true",
                        help="saute la probe DWELL (plus rapide, moins sur)")
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)

    runner = _runner_for(args.repo)
    if args.rest and runner is None:
        print("ERROR: --rest relit les reviews par {} : reserve a {}".format(
            "merge_ready", merge_ready.REPO), file=sys.stderr)
        return EXIT_ERROR
    gh_env = None

    try:
        if args.rest:
            prs = fetch_prs_rest(args.repo, args.limit)
        else:
            prs = fetch_prs(args.repo, args.limit)
    except (RuntimeError, json.JSONDecodeError) as exc:
        print("ERROR: lecture des PRs impossible: {}".format(exc),
              file=sys.stderr)
        return EXIT_ERROR

    rows: list[dict] = []
    for item in screen(prs, args.login, runner, gh_env):
        pr = item["pr"]
        status, causes = item["status"], item["causes"]
        if status is None:
            if args.rest:
                # La liste REST rend `unknown` : la lecture unitaire est la
                # seule qui dise l'etat de merge, et elle ne se paie que sur
                # les PRs candidates.
                state = probe_merge_state_rest(args.repo, pr["number"])
                if state:
                    pr["merge_state"] = state
            probes = {
                "b0": probe_b0(pr["number"]),
                "checks": probe_checks(pr["number"], pr["head"]),
                "dwell": ({"ok": None, "message": "saute"}
                          if args.no_dwell
                          else probe_dwell(pr["number"], pr["head"],
                                           args.repo)),
            }
            status, causes = classify(pr, probes, runner, gh_env)
        rows.append({
            "pr": pr["number"],
            "title": pr["title"],
            "head": pr["head"],
            "merge_state": pr["merge_state"],
            "approval": item["approval"],
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