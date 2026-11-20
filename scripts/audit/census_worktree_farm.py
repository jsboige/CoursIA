#!/usr/bin/env python3
"""Census d'une ferme de worktrees : qui occupe quoi, et ce qui est recyclable.

Le geste de recyclage d'une ferme de worktrees (post-merge) demande deux
mesures qu'aucun organe ne fournissait :

1. **La taille reelle** de chaque worktree (le volume du disque n'est pas la
   somme des tailles de fichiers de l'arbre de travail : `.lake`, `node_modules`,
   caches et `.git` weighed differently) ;
2. **Le titulaire** de chaque worktree — sans quoi la ferme n'est pas
   attribuable et la demande « hygiene des 114+ worktrees » reste une
   injonction sans adresse.

L'attribution est lue sur le **tag `Grain:` du body de la PR de tete de
branche** (`Grain: <TIER>/<GENRE> — lane <machine:workspace> — prev: ...`),
qui est la seule trace d'identite de lane portee par une PR. En repli, le
fichier `.lane-owner` a la racine du worktree (`machine:workspace`) est lu.
Un worktree sans PR, ou dont le body ne porte pas de tag, reste
`unattributed` : l'inventaire ne devine pas.

L'organe ne retire rien. Il produit une mesure ; le retrait reste un geste
distinct, avec sa preuve de preservation (cf. `prune_merged_worktrees.py`
pour les criteres de retrait).

Usage :

    python scripts/audit/census_worktree_farm.py --farm D:/CoursIA-2-wt
    python scripts/audit/census_worktree_farm.py --farm D:/CoursIA-2-wt --json
    python scripts/audit/census_worktree_farm.py --farm D:/CoursIA-2-wt --lane myia-ai-01:CoursIA-2

Sorties : rc 0 = census produit ; rc 1 = ferme introuvable ou liste illisible ;
rc 2 = `--gh` impose et `gh` indisponible (degrade assume, aucun verdict
forge).
"""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from typing import Any

#: Le tag de lane d'une PR : `Grain: ... — lane <machine:workspace> — prev: ...`
LANE_TAG = re.compile(r"lane\s+([A-Za-z0-9_.-]+:[A-Za-z0-9_.-]+)")

#: Les etats de PR qui rendent un worktree candidat au retrait post-merge.
RECYCLABLE_STATES = ("MERGED", "CLOSED")


def lane_from_body(body: str) -> str | None:
    """La lane declaree par le tag `Grain:` d'un body de PR, ou None.

    Le tag est la premiere ligne du body : la lecture est **ancree** sur cette
    premiere ligne non vide. Une mention de lane plus bas dans le corps (une
    citation, un historique, un renvoi) ne peut donc pas detourner
    l'attribution.
    """
    if not body:
        return None
    for line in body.splitlines():
        if not line.strip():
            continue
        m = LANE_TAG.search(line)
        return m.group(1) if m else None
    return None


def parse_worktree_list(text: str) -> list[dict[str, Any]]:
    """Parse la sortie de `git worktree list --porcelain`.

    Chaque bloc porte un `worktree <chemin>`, puis eventuellement un
    `branch refs/heads/<nom>` ou `detached`.
    """
    entries: list[dict[str, Any]] = []
    current: dict[str, Any] | None = None
    for line in text.splitlines():
        if line.startswith("worktree "):
            if current:
                entries.append(current)
            current = {"path": line[len("worktree "):].strip()}
        elif line.startswith("branch ") and current is not None:
            current["branch"] = line[len("branch "):].strip().replace(
                "refs/heads/", "")
        elif line.startswith("detached") and current is not None:
            current["detached"] = True
    if current:
        entries.append(current)
    return entries


def read_lane_owner(path: str) -> str | None:
    """Le fichier `.lane-owner` a la racine d'un worktree, s'il existe."""
    p = os.path.join(path, ".lane-owner")
    try:
        with open(p, encoding="utf-8") as f:
            value = f.read().strip()
    except OSError:
        return None
    return value or None


def dir_size(path: str) -> int:
    """Taille cumulee d'un repertoire, en octets (les erreurs sont ignorees :
    un fichier ouvert par un autre processus ne doit pas faire echouer le
    census)."""
    total = 0
    for root, _dirs, files in os.walk(path, onerror=lambda e: None):
        for name in files:
            try:
                total += os.lstat(os.path.join(root, name)).st_size
            except OSError:
                pass
    return total


def git(path: str, *args: str) -> tuple[int, str]:
    r = subprocess.run(["git", "-C", path, *args], capture_output=True,
                       text=True, encoding="utf-8", errors="replace")
    return r.returncode, (r.stdout or "").strip()


def gh_slug(repo: str) -> str | None:
    """Le slug GitHub du depot local (`jsboige/CoursIA`), lu sur le remote."""
    rc, url = git(repo, "remote", "get-url", "origin")
    if rc != 0 or not url:
        return None
    url = url.strip().removesuffix(".git")
    if url.startswith("git@") and ":" in url:
        host, _, path = url.partition(":")
        return path.strip("/")
    for marker in ("github.com/", "github.com:"):
        if marker in url:
            return url.split(marker, 1)[1].strip("/")
    return None


def fetch_prs(repo: str, limit: int = 600) -> tuple[dict[str, list[dict[str, Any]]], str | None]:
    """Les PRs du depot, indexees par branche de tete.

    Retourne `(index, erreur)`. L'index est vide et l'erreur non nulle si `gh`
    est indisponible : l'inventaire degrade alors en « sans attribution »,
    ce qui est un etat honnete, pas un echec de mesure.

    `limit` borne le nombre de PRs interrogees (`gh pr list --limit`). Le
    defaut de 600 couvre les PRs merger recemment ; au-dela, une PR ancienne
    sort de l'index et son worktree est lu « sans PR ». Le plafond est
    expose (`--pr-limit`) pour qu'une ferme large puisse l'elever.
    """
    try:
        raw = subprocess.run(
            ["gh", "pr", "list", "--repo", repo, "--state", "all",
             "--limit", str(limit), "--json",
             "number,headRefName,body,title,state,mergedAt"],
            capture_output=True, text=True, encoding="utf-8", errors="replace")
    except OSError as exc:
        return {}, "gh indisponible : %s" % exc
    if raw.returncode != 0:
        return {}, "gh a echoue (rc=%d) : %s" % (
            raw.returncode, (raw.stderr or "").strip()[:200])
    try:
        prs = json.loads(raw.stdout or "[]")
    except json.JSONDecodeError as exc:
        return {}, "sortie de gh illisible : %s" % exc
    index: dict[str, list[dict[str, Any]]] = {}
    for pr in prs:
        index.setdefault(pr.get("headRefName") or "", []).append({
            "number": pr.get("number"),
            "state": pr.get("state"),
            "merged_at": pr.get("mergedAt"),
            "title": (pr.get("title") or "")[:120],
            "lane": lane_from_body(pr.get("body") or ""),
        })
    return index, None


def worktree_state(path: str, branch: str | None) -> dict[str, Any]:
    """Etat de salete et d'ecart d'un worktree."""
    rc, status = git(path, "status", "--porcelain")
    lines = [l for l in status.splitlines() if l.strip()] if rc == 0 else []
    untracked = [l for l in lines if l.startswith("??")]
    modified = [l for l in lines if not l.startswith("??")]
    ahead = behind = None
    if branch:
        rc, out = git(path, "rev-list", "--left-right", "--count",
                      "origin/%s...HEAD" % branch)
        if rc == 0 and out:
            parts = out.split()
            if len(parts) == 2:
                behind, ahead = int(parts[0]), int(parts[1])
    return {"modified": len(modified), "untracked": len(untracked),
            "ahead": ahead, "behind": behind}


def census(farm: str, repo: str, use_gh: bool = True,
           gh_repo: str | None = None, pr_limit: int = 600) -> dict[str, Any]:
    """L'inventaire complet de la ferme."""
    rc, listing = git(repo, "worktree", "list", "--porcelain")
    if rc != 0:
        raise RuntimeError("git worktree list illisible (rc=%d)" % rc)
    pr_index, gh_error = ({}, None)
    if use_gh:
        slug = gh_repo or gh_slug(repo)
        if not slug:
            gh_error = "slug GitHub introuvable sur le remote origin"
        else:
            pr_index, gh_error = fetch_prs(slug, limit=pr_limit)
    rows: list[dict[str, Any]] = []
    farm_norm = os.path.normcase(os.path.abspath(farm))
    rc_top, toplevel = git(repo, "rev-parse", "--show-toplevel")
    principal = os.path.normcase(os.path.abspath(toplevel)) if rc_top == 0 else None
    for entry in parse_worktree_list(listing):
        path = entry["path"]
        norm = os.path.normcase(os.path.abspath(path))
        # La ferme n'est pas le clone principal : on l'exclut, comme la racine
        # de la ferme elle-meme.
        if norm == farm_norm or (principal is not None and norm == principal):
            continue
        branch = entry.get("branch")
        prs = pr_index.get(branch or "", [])
        pr = sorted(prs, key=lambda p: p.get("number") or 0)[-1] if prs else None
        lane = (pr or {}).get("lane") or read_lane_owner(path)
        size = dir_size(path)
        state = worktree_state(path, branch)
        rows.append({
            "name": os.path.basename(path.rstrip("\\/")),
            "path": path,
            "branch": branch,
            "detached": bool(entry.get("detached")),
            "gib": round(size / (1024 ** 3), 3),
            "lane": lane,
            "pr": pr,
            "pr_state": (pr or {}).get("state"),
            "recyclable": (pr or {}).get("state") in RECYCLABLE_STATES,
            **state,
        })
    rows.sort(key=lambda r: -r["gib"])
    by_lane: dict[str, dict[str, Any]] = {}
    for row in rows:
        key = row["lane"] or "(unattributed)"
        bucket = by_lane.setdefault(key, {"n": 0, "gib": 0.0, "recyclable": 0})
        bucket["n"] += 1
        bucket["gib"] += row["gib"]
        if row["recyclable"]:
            bucket["recyclable"] += 1
    return {
        "farm": farm,
        "repo": repo,
        "gh_error": gh_error,
        "total_gib": round(sum(r["gib"] for r in rows), 2),
        "count": len(rows),
        "by_lane": by_lane,
        "rows": rows,
    }


def render(report: dict[str, Any]) -> str:
    out = []
    out.append("Ferme : %s" % report["farm"])
    out.append("Worktrees (hors clone principal) : %d, total %.2f Gio"
               % (report["count"], report["total_gib"]))
    if report["gh_error"]:
        out.append("Attribution indisponible : %s (les worktrees restent "
                   "'unattributed')" % report["gh_error"])
    out.append("")
    out.append("%-34s %5s %9s %-8s %-9s %s"
               % ("lane", "n", "Gio", "PR", "etat", "recyclable"))
    for lane, b in sorted(report["by_lane"].items(),
                          key=lambda kv: -kv[1]["gib"]):
        out.append("%-34s %5d %9.2f %-8s %-9s %d"
                   % (lane[:34], b["n"], b["gib"], "", "",
                      b["recyclable"]))
    out.append("")
    out.append("%-26s %-38s %-7s %-8s %8s %6s %6s"
               % ("worktree", "branche", "PR", "etat", "Gio", "mod", "untr"))
    for row in report["rows"]:
        pr = row["pr"] or {}
        out.append("%-26s %-38s %-7s %-8s %8.3f %6d %6d"
                   % (row["name"][:26], (row["branch"] or "-")[:38],
                      pr.get("number") or "-", pr.get("state") or "-",
                      row["gib"], row["modified"], row["untracked"]))
    return "\n".join(out)


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--farm", required=True,
                    help="racine de la ferme de worktrees a inventorier")
    ap.add_argument("--repo", default=".",
                    help="clone local dont les worktrees sont inventories")
    ap.add_argument("--gh-repo", default=None,
                    help="slug GitHub du depot (par defaut : lu sur le remote)")
    ap.add_argument("--json", action="store_true", dest="as_json",
                    help="sortie structuree")
    ap.add_argument("--no-gh", action="store_true",
                    help="sans GitHub : aucune attribution par tag de PR")
    ap.add_argument("--pr-limit", type=int, default=600,
                    help="nombre maximal de PRs interrogees (defaut : 600)")
    args = ap.parse_args(argv)
    if not os.path.isdir(args.farm):
        sys.stderr.write("ferme introuvable : %s\n" % args.farm)
        return 1
    try:
        report = census(args.farm, args.repo, use_gh=not args.no_gh,
                        gh_repo=args.gh_repo, pr_limit=args.pr_limit)
    except RuntimeError as exc:
        sys.stderr.write("%s\n" % exc)
        return 1
    if args.as_json:
        print(json.dumps(report, ensure_ascii=False, indent=1))
    else:
        print(render(report))
    return 0


if __name__ == "__main__":
    sys.exit(main())
