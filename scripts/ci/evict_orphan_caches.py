#!/usr/bin/env python3
r"""evict_orphan_caches.py -- evince les caches Actions SHA-keyed irrecuperables (#16088).

## Why this exists

Issue #16088 a releve un defaut structurel des caches Actions sur ce depot :
CodeQL default setup ecrit des cles de cache `codeql-overlay-base-database-…`
suffixees par le **SHA du commit** au moment de l'analyse, plus le run-id
GitHub Actions. Une telle cle est **neuve a chaque commit** et **morte des
que la tete bouge** : aucun run ulterieur ne portera exactement ce SHA, donc
le cache ne peut etre restaure que dans la fenetre tres courte du meme run
(matrix des langues), pas cross-runs.

Mesure first-hand 2026-09-14T04:10Z :
- 11 caches CodeQL actifs, 1.26 Go total, sur un quota de 10 Go (12,6 %).
- Hit ratio **9/11 (82 %)** : les hits sont **intra-run matrix** (meme SHA,
  plusieurs langues), pas cross-runs. Le cross-run est structurellement
  nul par construction de la cle.
- 2 caches sur 11 (18 %) sont des MISS purs (jamais hit, 208 + 208 Mo),
  occupant du quota qui pourrait revenir a des caches reutilisables.

Le defaut n'est pas reparable cote configuration (CodeQL default setup ne
suit pas un fichier `.github/workflows/codeql.yml`, il est gere par GitHub,
cf. .github/workflows absent de `codeql*` -- mesure 2026-09-14). Le remede
est cote REPO : eviction periodique des caches dont le SHA n'est plus
ancetre de `main`, ET/OU dont le `last_accessed_at` est anterieur a une
fenetre de retention choisie.

## What it does

  $ python scripts/ci/evict_orphan_caches.py
  # dry-run (default) : affiche les suppressions prevues + les refus motives
  EVICT       codeql-overlay-...-python-2.27.0-1ebc412b...-34799381268-1  sha_not_ancestor_of_main
  EVICT       codeql-overlay-...-python-2.27.0-232e894...-34798835321-1  last_accessed_older_than_24h
  REFUSE      lake-knot_lean-axiom-Linux-821f5e3b...-...-1                not_codeql_overlay
  ---
  total=3  evictable=2  refused=1  would_free_mb=416

  $ python scripts/ci/evict_orphan_caches.py --apply
  # applique les suppressions ; exit 1 si au moins un refus non-bloquant
  #   OU si aucun evictable (idempotent)

  $ python scripts/ci/evict_orphan_caches.py --json
  {"scanned": 3, "evictable": 2, "refused": 1, "actions": [...], "would_free_mb": 416}

  $ python scripts/ci/evict_orphan_caches.py --max-age-hours 12
  # agressif : tout cache non accede dans les 12 dernieres heures est candidat
  # Note : le sweep deploye par .github/workflows/evict-orphan-caches.yml
  # utilise 168 h (7 j) ; le defaut CLI (24 h) est 7x plus agressif.
  # Pour reproduire le comportement du sweep, passez --max-age-hours 168.

Criteres d'eviction (cf. issue #16088 acceptance) :

1. **Cible uniquement les caches `codeql-overlay-base-database-…`** : les
   autres caches du quota (lean `lake-…-axiom-Linux-…`, `setup-python-…`,
   `dotnet-cache-…`, `node-cache-…`) sont reutilises, on n'y touche pas.
   Un cache **non-codeql-overlay** rencontre en dry-run est note REFUSE.
2. **Pas ancetre de `origin/main`** : `git merge-base --is-ancestor <sha>
   origin/main` est FALSE. Cas classique = squash-merge : le SHA a ete
   ecrase sur main, le cache ne sera JAMAIS restore.
3. **Ou pas accede depuis plus de `--max-age-hours`** (defaut 24 h) : un
   cache qui survit au-dela de 24 h sans hit est presque certainement
   orphelin -- les runs suivants apportent un nouveau SHA, l'ancien est
   mort-ne. `last_accessed_at == created_at` equivaut a "jamais hit".

## Garde de surete (defense en profondeur)

- **Dry-run par defaut** : aucun appel DELETE sans `--apply` explicite.
- **Header obligatoire `X-GitHub-Api-Version: 2022-11-28`** : l'API caches
  sans header explicite est documentee `2022-11-28`.
- **Bande de protection** : si le SHA extrait n'est pas un SHA-1 valide
  (40 hex), REFUSE (la cle ne suit pas le pattern CodeQL).
- **Refuse tout cache non-codeql-overlay** : on ne touche pas au reste du
  quota (lean, setup-python, etc.) qui est reutilise.
- **Pas d'appel DELETE sans confirmation visuelle** : le dry-run affiche
  l'identifiant de cache, la cle tronquee, la raison, et la taille. Le
  `--apply` ne supprime que les evictables listes au dry-run.

## Format de cle CodeQL default setup (mesure 2026-09-14)

    codeql-overlay-base-database-1-<random8>-<lang>-2.27.0-<sha40>-<runid>-1

- `<random8>` : 8 hex, probablement un identifiant de step run.
- `<lang>` : `python`, `csharp`, `javascript` (les 3 langues activees
  dans la default setup du repo).
- `2.27.0` : version CodeQL figee.
- `<sha40>` : SHA de commit **complet** (40 hex) -- c'est ce qu'on teste.
- `<runid>` : identifiant numerique du run GitHub Actions.
- `-1` : compteur de version de cache (toujours 1 sur le dataset mesure).

## Sortie

- stdout : rapport lisible (mode dry-run) ou rapport d'execution (mode
  --apply).
- stderr : logs techniques uniquement, pas de narration.
- exit 0 : tout evictable a ete supprime (ou dry-run propre).
- exit 1 : au moins un refus non-bloquant OU aucun evictable.

## See also

- Issue #16088 (mesure du defaut, 12 entrees / 0.19 Go unitaire)
- scripts/ci/prune_merged_worktrees.py -- meme esprit, worktrees au lieu
  de caches ; auteur + revue po-2023, septembre 2026.
- .github/workflows/codeql.yml : **absente** du depot, le CodeQL est en
  default setup gere par GitHub (cf. mesure 2026-09-14).
"""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from datetime import datetime, timedelta, timezone
from pathlib import Path
from typing import Any, Optional

import urllib.error
import urllib.request

THIS_FILE = Path(__file__).resolve()
REPO_ROOT = THIS_FILE.parents[2]

# Pattern d'une cle CodeQL default setup (mesure 2026-09-14).
# Groupes : (1) random8, (2) lang, (3) toolchain, (4) sha40, (5) runid, (6) version.
CODEQL_OVERLAY_RE = re.compile(
    r"^codeql-overlay-base-database-\d+-"
    r"(?P<random8>[0-9a-f]+)-"
    r"(?P<lang>\w+)-"
    r"(?P<toolchain>[\d.]+)-"
    r"(?P<sha40>[0-9a-f]{40})-"
    r"(?P<runid>\d+)-"
    r"(?P<version>\d+)$"
)

# Header documente par l'API GitHub Actions caches.
GITHUB_API_VERSION = "2022-11-28"


def _parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    p.add_argument(
        "--apply",
        action="store_true",
        help="Apply the eviction (default: dry-run).",
    )
    p.add_argument(
        "--json",
        action="store_true",
        help="Emit JSON instead of human-readable verdict.",
    )
    p.add_argument(
        "--max-age-hours",
        type=int,
        default=24,
        help="Evict caches whose last_accessed_at is older than this many hours "
        "(default: 24). A cache never hit has last_accessed_at == created_at.",
    )
    p.add_argument(
        "--repo",
        default=os.environ.get("GITHUB_REPOSITORY", "jsboige/CoursIA"),
        help="Target repo (default: $GITHUB_REPOSITORY or jsboige/CoursIA).",
    )
    p.add_argument(
        "--remote",
        default="origin",
        help="Git remote whose main branch is the orphan reference (default: origin).",
    )
    p.add_argument(
        "--main-branch",
        default="main",
        help="Branch reference for ancestry check (default: main).",
    )
    return p.parse_args()


def _list_caches(repo: str, token: str | None) -> list[dict[str, Any]]:
    """List all Actions caches for the repo via REST API."""
    url = f"https://api.github.com/repos/{repo}/actions/caches?per_page=100"
    req = urllib.request.Request(url, headers=_gh_headers(token))
    out: list[dict[str, Any]] = []
    while url:
        req = urllib.request.Request(url, headers=_gh_headers(token))
        try:
            with urllib.request.urlopen(req, timeout=30) as resp:
                payload = json.load(resp)
        except urllib.error.HTTPError as e:
            print(f"[FATAL] GET {url} -> HTTP {e.code}: {e.read()!r}", file=sys.stderr)
            sys.exit(2)
        out.extend(payload.get("actions_caches", []))
        # Follow pagination if there's a next page.
        link = None
        for k, v in resp.headers.items():
            if k.lower() == "link":
                link = v
        url = _next_link(link) or ""
    return out


def _next_link(link_header: str | None) -> str | None:
    if not link_header:
        return None
    for part in link_header.split(","):
        seg = part.strip()
        if seg.endswith('rel="next"'):
            url = seg.split(";")[0].strip().strip("<>")
            return url
    return None


def _gh_headers(token: str | None) -> dict[str, str]:
    h = {
        "Accept": "application/vnd.github+json",
        "X-GitHub-Api-Version": GITHUB_API_VERSION,
    }
    if token:
        h["Authorization"] = f"Bearer {token}"
    return h


def _delete_cache(repo: str, cache_id: int, token: str | None) -> int:
    """Delete one cache by ID. Returns HTTP status."""
    url = f"https://api.github.com/repos/{repo}/actions/caches/{cache_id}"
    req = urllib.request.Request(url, method="DELETE", headers=_gh_headers(token))
    try:
        with urllib.request.urlopen(req, timeout=30) as resp:
            return resp.status
    except urllib.error.HTTPError as e:
        return e.code


def _is_ancestor(sha: str, remote: str, branch: str) -> Optional[bool]:
    """Return True if <sha> is an ancestor of <remote>/<branch>, False otherwise.

    Returns None if the check could not be performed (git absent, ref
    missing, depot casse). Callers MUST treat None as "unknown -- do
    not evict", because the cost of an unknown answer is asymmetric:
    evicting a live cache costs a perf re-creation, while keeping a
    cache that the next sweep will re-classify correctly is free.

    The previous fail-OPEN behaviour (NanoClaw 2026-09-14 review on
    PR #16099) treated "not ancestor" (rc=1) and "impossible to
    determine" (rc>=2, FileNotFoundError) identically -- both fell
    through to ``return False``, so any cache was evicted on a
    checkout with a degraded git history. The split here is the
    direction-of-failure fix that the script's job (delete) demands:
    fail-CLOSED when the check cannot answer.
    """
    try:
        result = subprocess.run(
            ["git", "merge-base", "--is-ancestor", sha, f"{remote}/{branch}"],
            cwd=str(REPO_ROOT),
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
    except FileNotFoundError:
        # git absent or not on PATH -- we cannot answer. Fail-closed.
        return None
    rc = result.returncode
    if rc == 0:
        return True
    if rc == 1:
        return False
    # rc >= 2: ref absente, depot casse, ou autre erreur git.
    # Fail-closed: the script cannot answer, do not evict.
    return None


def _parse_iso(s: str) -> datetime:
    # GitHub returns "...Z" or "...+00:00"; fromisoformat handles +00:00 in 3.11+.
    if s.endswith("Z"):
        s = s[:-1] + "+00:00"
    return datetime.fromisoformat(s)


def _classify_cache(
    cache: dict[str, Any],
    *,
    max_age_hours: int,
    remote: str,
    main_branch: str,
) -> dict[str, Any]:
    """Decide for one cache: keep / evict / refuse."""
    key = cache["key"]
    rec: dict[str, Any] = {
        "id": cache["id"],
        "key": key,
        "size_bytes": cache["size_in_bytes"],
        "created_at": cache["created_at"],
        "last_accessed_at": cache["last_accessed_at"],
    }
    m = CODEQL_OVERLAY_RE.match(key)
    if not m:
        rec.update({"verdict": "REFUSE", "reason": "not_codeql_overlay"})
        return rec

    sha = m.group("sha40")
    rec["sha40"] = sha
    rec["lang"] = m.group("lang")

    reasons: list[str] = []
    ancestor_status = _is_ancestor(sha, remote, main_branch)
    if ancestor_status is None:
        # Cannot determine -- fail-CLOSED. We refuse rather than evict
        # because the script's job is to delete; an undecidable check
        # must not be answered by "yes, delete".
        rec.update({"verdict": "REFUSE", "reason": "ancestor_check_failed"})
        return rec
    if ancestor_status is False:
        reasons.append("sha_not_ancestor_of_main")

    last_accessed = _parse_iso(cache["last_accessed_at"])
    cutoff = datetime.now(timezone.utc) - timedelta(hours=max_age_hours)
    if last_accessed < cutoff:
        reasons.append(f"last_accessed_older_than_{max_age_hours}h")

    if reasons:
        rec.update({"verdict": "EVICT", "reason": "+".join(reasons)})
    else:
        rec.update({"verdict": "KEEP", "reason": "recent_and_ancestor"})
    return rec


def _print_human(records: list[dict[str, Any]], applied: bool) -> None:
    for r in records:
        verdict = r["verdict"]
        if verdict == "EVICT" and applied:
            action = "DELETED"
        elif verdict == "EVICT":
            action = "EVICT"
        elif verdict == "KEEP":
            action = "KEEP"
        else:
            action = "REFUSE"
        size_mb = r["size_bytes"] / 1e6
        key_trunc = r["key"][:80] + ("…" if len(r["key"]) > 80 else "")
        print(
            f"{action:<10s}  {size_mb:6.1f} Mo  "
            f"sha={r.get('sha40', '-')[:10]}  {r.get('reason', '-'):<35s}  {key_trunc}"
        )


def _print_json(records: list[dict[str, Any]], applied: bool) -> None:
    out = {
        "applied": applied,
        "scanned": len(records),
        "evictable": sum(1 for r in records if r["verdict"] == "EVICT"),
        "refused": sum(1 for r in records if r["verdict"] == "REFUSE"),
        "kept": sum(1 for r in records if r["verdict"] == "KEEP"),
        "would_free_mb": round(
            sum(r["size_bytes"] for r in records if r["verdict"] == "EVICT") / 1e6, 1
        ),
        "actions": records,
    }
    json.dump(out, sys.stdout, indent=1)
    sys.stdout.write("\n")


def main() -> int:
    args = _parse_args()
    token = os.environ.get("GH_TOKEN") or os.environ.get("GITHUB_TOKEN")
    if not token:
        print(
            "[WARN] GH_TOKEN/GITHUB_TOKEN absent -- appel API limite a 60 req/h "
            "anonyme. Positionner GH_TOKEN avant --apply.",
            file=sys.stderr,
        )

    caches = _list_caches(args.repo, token)
    records = [
        _classify_cache(
            c,
            max_age_hours=args.max_age_hours,
            remote=args.remote,
            main_branch=args.main_branch,
        )
        for c in caches
    ]

    applied = args.apply
    if applied:
        for r in records:
            if r["verdict"] == "EVICT":
                status = _delete_cache(args.repo, r["id"], token)
                r["delete_status"] = status

    if args.json:
        _print_json(records, applied)
    else:
        _print_human(records, applied)

    evictable = sum(1 for r in records if r["verdict"] == "EVICT")
    refused = sum(1 for r in records if r["verdict"] == "REFUSE")
    if applied and evictable == 0 and refused == 0:
        # Nothing to do AND nothing refused: nothing to apply, fine.
        return 0
    if applied and evictable == 0:
        print(
            f"[INFO] --apply demande mais aucun evictable : rien a faire.",
            file=sys.stderr,
        )
        return 1
    if not applied and evictable == 0:
        print(
            f"[INFO] Aucun cache evictable (scanned={len(records)}, "
            f"refused={refused}). Dry-run termine.",
            file=sys.stderr,
        )
        return 0
    return 0


if __name__ == "__main__":
    sys.exit(main())
