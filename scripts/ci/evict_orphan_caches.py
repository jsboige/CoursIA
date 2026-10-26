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
  # applique les suppressions ; exit 1 seulement si --apply ne trouve AUCUN
  #   evictable alors que des caches ont ete refuses (idempotence : un second
  #   passage rend 1). Des refus seuls, avec des evictables presents, rendent 0.

  $ python scripts/ci/evict_orphan_caches.py --json
  {"scanned": 3, "evictable": 2, "refused": 1, "actions": [...], "would_free_mb": 416}

  $ python scripts/ci/evict_orphan_caches.py --max-age-hours 12
  # agressif : tout cache non accede dans les 12 dernieres heures est candidat
  # Note : le sweep deploye par .github/workflows/evict-orphan-caches.yml
  # utilise 168 h (7 j) ; le defaut CLI (24 h) est 7x plus agressif.
  # Pour reproduire le comportement du sweep, passez --max-age-hours 168.

Criteres d'eviction (cf. issue #16088 acceptance) :

1. **Cible uniquement les caches `codeql-overlay-base-database-…`** : les
   autres caches du quota (lean `lake-…-axiom-Linux-…`, `dotnet-cache-…`,
   `node-cache-…`) sont reutilises, on n'y touche pas.
   Un cache **non-codeql-overlay** rencontre en dry-run est note REFUSE.
   **Seule exception (#19658)** : les familles de `DEDUPE_KEY_PREFIXES`
   (`setup-python-…`), dont la cle est un hash de contenu. Leurs **copies
   de la meme cle** sont evincees -- voir critere 4.
2. **Pas ancetre de `origin/main`** : `git merge-base --is-ancestor <sha>
   origin/main` est FALSE. Cas classique = squash-merge : le SHA a ete
   ecrase sur main, le cache ne sera JAMAIS restore.
3. **Ou pas accede depuis plus de `--max-age-hours`** (defaut 24 h) : un
   cache qui survit au-dela de 24 h sans hit est presque certainement
   orphelin -- les runs suivants apportent un nouveau SHA, l'ancien est
   mort-ne. `last_accessed_at == created_at` equivaut a "jamais hit".
4. **Ou copie redondante d'une cle content-addressee** (#19658) : pour une
   cle de `DEDUPE_KEY_PREFIXES`, GitHub en stocke une entree par scope de
   branche mais n'en sert qu'une. On garde la plus recente -- une branche
   vivante (`refs/heads/*`) primant sur une ref de PR (`refs/pull/*/merge`) --
   ET celle de `--main-branch` (le repli des branches sans copie propre), on
   evince les autres. Mesure du 2026-10-25 : 76 entrees `setup-python-*` pour
   5 cles distinctes, 4,85 Go du quota de 10 Go, dont 4,48 Go de doublons.
5. **Ou cle que plus aucun workflow de `main` ne demande** (#19658,
   decision A du coordinateur, 2026-10-26) : une cle
   `setup-python-<...>-python-<version>-<pm>-<hash>` n'est relisible que par un
   run dont le workflow **de `main`** pose le meme `cache:` ET resout la meme
   version. Le couple `(cache, version)` demande est derive **a la lecture des
   workflows** (jamais d'une liste figee dans le script) ; quand aucun
   workflow de `main` ne demande plus ce couple, la cle est prouvee orpheline
   et evincee, **meme sur une PR ouverte** : la regle fail-closed « copie de
   PR ouverte » ne protege que les cles encore demandees.

   Ce que la mesure dit du plafond de ce critere : la resolution de la version
   depend du **runner**, pas du YAML (`3.12` se resout en `3.12.14` sur l'image
   du pool). Le critere compare donc la version **resolue** de la cle a la
   version **declaree** dans les workflows -- une spec de minor (`3.12`)
   couvre toutes les patchs de cette minor. Une cle dont la version n'est
   couverte par aucune spec de `main` est donc evincee ; une cle encore
   couverte est conservee, quelle que soit sa PR.

## Garde de surete (defense en profondeur)

- **Dry-run par defaut** : aucun appel DELETE sans `--apply` explicite.
- **Header obligatoire `X-GitHub-Api-Version: 2022-11-28`** : l'API caches
  sans header explicite est documentee `2022-11-28`.
- **Bande de protection** : si le SHA extrait n'est pas un SHA-1 valide
  (40 hex), REFUSE (la cle ne suit pas le pattern CodeQL).
- **Refuse tout cache non-codeql-overlay** : on ne touche pas au reste du
  quota (lean, dotnet, node) qui est reutilise. La seule famille ouverte est
  `DEDUPE_KEY_PREFIXES`, et seulement pour ses **doublons de cle** : la
  nouvelle entree et celle de la branche par defaut survivent toujours.
- **Le critere « non demandee par main » est fail-CLOSED** : si les workflows
  de `main` ne sont pas lisibles (checkout incomplet, repertoire absent), la
  demande est **inconnue** et aucune cle `setup-python` n'est evincee -- la
  passe le dit dans sa raison (`unrequested_check_failed`) au lieu de
  presumer une absence. Une spec de version illisible (`${{ matrix.x }}`)
  couvre toutes les versions : une demande qu'on ne sait pas lire ne peut
  pas etre niee.
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
- exit 0 : tout evictable a ete supprime (ou dry-run propre), y compris
  lorsqu'un REFUSE coexiste avec des evictables traites.
- exit 1 : `--apply` n'a trouve AUCUN evictable alors qu'au moins un cache a
  ete refuse -- c'est-a-dire `evictable == 0 and refused > 0`, le cas
  d'idempotence d'un second passage.
- exit 2 : l'API caches est injoignable ou rend une erreur HTTP.

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

# #19658 : familles de cles content-addressees dont la duplication entre
# scopes de branche est de la redondance pure. Mesure du 2026-10-25 : 76
# entrees `setup-python-*` pour 5 cles distinctes -- 73 copies de
# `...python-3.12.14-pip-f601c5c89e...` (toutes sur `refs/pull/<n>/merge`,
# aucune sur `main`) et 2 de la 3.12.15, ~293 Mo chacune, 4,85 Go du quota de
# 10 Go. La cle etant un hash du contenu (version python + pip + hash de
# dependances), deux entrees de meme cle sont interchangeables.
#
# Ce que « redondant » veut dire exactement (review ai-01, 2026-10-25, tete
# 647f417530) : une copie scellee sur `refs/pull/<n>/merge` n'est lisible que
# par les runs de CETTE PR. Tant que la PR est ouverte, ses runs suivants la
# lisent -- l'evincer les renvoie a un `pip install` a froid, qu'ils repayent
# par un re-save de ~293 Mo. Le gain de quota serait donc paye en calcul et en
# upload sur toute la file, au moment ou c'est le calcul qui manque (#22461).
# Ne sont donc evincees que les copies dont la PR est **fermee ou mergee** ;
# la liste des PRs ouvertes est lue avant le balayage, et son absence
# (reseau, 403) rend la passe inoperante plutot que devinante.
DEDUPE_KEY_PREFIXES = ("setup-python-",)

# `refs/pull/<n>/merge` et `refs/pull/<n>/head` : deux formes pour la meme PR.
PR_REF_RE = re.compile(r"^refs/pull/(\d+)/(?:merge|head)$")

# #19658 (decision A du coordinateur, 2026-10-26) : format de cle
# `actions/setup-python`, mesure sur les logs de run (job « Golden-set
# execution (H.7 P3) », run 40270198774, 2026-10-26T04:41Z) :
#
#   setup-python-Linux-x64-24.04-Ubuntu-python-3.12.14-pip-<fileHash 64 hex>
#
# - `<OS>-<arch>-<image>` : le triplet du runner (le prefixe `24.04-Ubuntu`
#   est l'image du runner, pas une partie de la version python) ;
# - `python-<version>` : la version **resolue** par le runner, pas la version
#   demandee dans le YAML (`3.12` se resout en `3.12.14` sur l'image du pool) ;
# - `<pm>` : le gestionnaire de paquets (`pip`) ;
# - `<fileHash>` : le hash des fichiers de `cache-dependency-path`, **independant
#   de la version** -- c'est pourquoi une meme empreinte apparait sous deux
#   versions (3.12.14 et 3.12.15 pour le meme job).
SETUP_PYTHON_RE = re.compile(
    r"^setup-python-[^-]+-[^-]+-.+-python-"
    r"(?P<version>\d+\.\d+\.\d+)-"
    r"(?P<pm>[a-z]+)-"
    r"(?P<filehash>[0-9a-f]{64})$"
)


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
        "--keep-latest",
        type=int,
        default=3,
        help="Per overlay family (config hash + lang + toolchain), keep only the "
        "N most recent caches still classified KEEP and evict the older ones "
        "(default: 3; 0 disables). Reopening of #16088: every overlay of main "
        "is an ancestor of main, so the two other criteria never catch them.",
    )
    p.add_argument(
        "--no-dedupe",
        action="store_true",
        help="Disable the duplicate-key pass (#19658). By default, entries of a "
        "content-addressed key (%s) beyond the newest one are evicted, except "
        "the entry on --main-branch, which stays as every other branch's "
        "fallback." % ", ".join(DEDUPE_KEY_PREFIXES),
    )
    p.add_argument(
        "--no-unrequested",
        action="store_true",
        help="Disable the unrequested-key pass (#19658, decision A). By default, a "
        "setup-python cache key whose (package manager, python version) pair is "
        "no longer declared by any workflow of main is evicted, even on an open "
        "PR.",
    )
    p.add_argument(
        "--workflows-dir",
        default=str(REPO_ROOT / ".github" / "workflows"),
        help="Directory holding the workflows the demand is derived from "
        "(default: <repo>/.github/workflows).",
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


def _pr_number_from_ref(ref: str) -> int | None:
    """Numero de PR porte par une ref de scope, ou None.

    `refs/pull/<n>/merge` est le scope ou GitHub scelle le cache d'une PR ;
    `refs/pull/<n>/head` existe aussi selon l'evenement qui a sauve. Une ref
    de branche (`refs/heads/*`) ne nomme aucune PR : None.
    """
    m = PR_REF_RE.match(str(ref or ""))
    return int(m.group(1)) if m else None


def _list_open_pr_numbers(repo: str, token: str | None) -> set[int] | None:
    """Numeros des PRs ouvertes du depot, ou None si la lecture echoue.

    None n'est pas « aucune PR ouverte » : c'est « je ne sais pas », et
    l'appelant doit alors s'abstenir d'evincer les copies de PR (cf.
    `_mark_duplicate_keys`). Le cout des deux erreurs est asymetrique --
    garder une copie morte coute du quota jusqu'au balayage suivant,
    evincer la copie d'une PR ouverte fait repayer un `pip install` a froid
    a chaque run de cette PR, puis un re-save de ~293 Mo.
    """
    url = f"https://api.github.com/repos/{repo}/pulls?state=open&per_page=100"
    out: set[int] = set()
    while url:
        req = urllib.request.Request(url, headers=_gh_headers(token))
        try:
            with urllib.request.urlopen(req, timeout=30) as resp:
                payload = json.load(resp)
                link = None
                for k, v in resp.headers.items():
                    if k.lower() == "link":
                        link = v
        except urllib.error.HTTPError as e:
            print(
                f"[WARN] GET {url} -> HTTP {e.code} : liste des PRs ouvertes "
                f"inconnue, les copies de PR ne seront pas evincees.",
                file=sys.stderr,
            )
            return None
        except (urllib.error.URLError, OSError) as e:
            print(
                f"[WARN] GET {url} -> {e!r} : liste des PRs ouvertes inconnue, "
                f"les copies de PR ne seront pas evincees.",
                file=sys.stderr,
            )
            return None
        for pr in payload:
            num = pr.get("number")
            if isinstance(num, int):
                out.add(num)
        url = _next_link(link) or ""
    return out


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
        "ref": cache.get("ref", ""),
        "size_bytes": cache["size_in_bytes"],
        "created_at": cache["created_at"],
        "last_accessed_at": cache["last_accessed_at"],
    }
    m = CODEQL_OVERLAY_RE.match(key)
    if not m:
        # #19658 : une cle content-addressee (`setup-python-...-<hash>`) peut
        # exister en plusieurs exemplaires, un par scope de branche. GitHub
        # ne sert qu'UNE entree par cle : les copies sont de la redondance
        # pure. On les marque KEEP avec `dedupe_key` -- `_mark_duplicate_keys`
        # tranche ensuite, et une famille hors prefixes reste REFUSE.
        if key.startswith(DEDUPE_KEY_PREFIXES):
            rec.update({"verdict": "KEEP", "reason": "dedupe_candidate"})
            rec["dedupe_key"] = key
            return rec
        rec.update({"verdict": "REFUSE", "reason": "not_codeql_overlay"})
        return rec

    sha = m.group("sha40")
    rec["sha40"] = sha
    rec["lang"] = m.group("lang")
    rec["family"] = f"{m.group('random8')}-{m.group('lang')}-{m.group('toolchain')}"

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


def _mark_superseded(records: list[dict[str, Any]], keep_latest: int) -> None:
    """Evict the overlays of a family beyond its `keep_latest` most recent ones.

    Only records still classified KEEP are counted and touched : an overlay
    already evicted for another reason does not take one of the kept slots,
    and a REFUSE (undecidable ancestry) is never turned into a deletion.
    Order is `created_at` descending ; `keep_latest <= 0` disables the rule.

    Why (reopening of #16088, 2026-09-28) : each overlay of `main` carries a
    SHA of `main`, hence an ancestor, and the quota fills in a few hours while
    the age window is 7 days. Measured : 33 overlays kept, 3.96 GB, quota at
    10.14 / 10 GB, and the knot_lean `.lake` cache evicted within 10 h of its
    save -- every Lean build of that lake then ran cold.
    """
    if keep_latest <= 0:
        return
    families: dict[str, list[dict[str, Any]]] = {}
    for r in records:
        if r["verdict"] == "KEEP" and "family" in r:
            families.setdefault(r["family"], []).append(r)
    for members in families.values():
        members.sort(key=lambda r: _parse_iso(r["created_at"]), reverse=True)
        for r in members[keep_latest:]:
            r.update(
                {"verdict": "EVICT", "reason": f"superseded_beyond_latest_{keep_latest}"}
            )


def _mark_duplicate_keys(
    records: list[dict[str, Any]],
    main_branch: str,
    open_prs: set[int] | None = None,
) -> None:
    """Evict the redundant copies of a content-addressed key (#19658).

    GitHub keys the cache store by `(key, ref)` : the SAME key can be saved
    once per branch scope, and a lookup serves exactly one entry. For a
    content-addressed key (`setup-python-...-<hash>`) the copies are therefore
    interchangeable, and every dead copy is quota spent for no cache-hit.

    Safe by construction, which is why this pass may evict on a criterion the
    other three never use :

    * every entry on the **default branch** is kept -- that is the entry a
      branch without its own copy falls back to, so no branch loses the hit ;
    * a copy on a **live branch** (`refs/heads/*`) outranks a PR merge ref
      (`refs/pull/*/merge`), so the branch copy is kept even when older ;
    * a copy whose **PR is still open** is kept (review ai-01, 2026-10-25,
      head `647f417530`) : `refs/pull/<n>/merge` is readable by the runs of
      that PR, so evicting it makes every later run of an open PR pay a cold
      `pip install`, then re-save ~293 MB -- quota returned to `lake-*`, paid
      back as compute and upload on the whole queue while compute is the
      scarce resource (#22461). Only copies of **closed or merged** PRs are
      evicted ;
    * `open_prs is None` means the open-PR list could not be read. No PR copy
      is evicted then (fail-CLOSED, same principle as `_is_ancestor`) : the
      dry-run reports them `open_prs_unknown` rather than guessing ;
    * only KEEP records carrying `dedupe_key` are touched : a REFUSE (family
      outside `DEDUPE_KEY_PREFIXES`) is never turned into a deletion.

    Why it matters (measured 2026-10-25) : 75 `setup-python-*` entries for 5
    distinct keys, 4.85 GB of a 10 GB quota, and the `lake-*` cache evicted
    within hours of its save -- every Lean build of that lake ran cold.
    """
    groups: dict[str, list[dict[str, Any]]] = {}
    for r in records:
        if r["verdict"] == "KEEP" and "dedupe_key" in r:
            groups.setdefault(r["dedupe_key"], []).append(r)

    default_ref = f"refs/heads/{main_branch}"

    def rank(r: dict[str, Any]) -> tuple[int, datetime]:
        # Une branche vivante avant une ref de PR, puis la plus recente.
        live = 1 if str(r.get("ref", "")).startswith("refs/heads/") else 0
        return (live, _parse_iso(r["created_at"]))

    for members in groups.values():
        if len(members) < 2:
            continue
        members.sort(key=rank, reverse=True)
        for r in members[1:]:
            if r.get("ref") == default_ref:
                # L'entree de la branche par defaut est le repli de toute
                # branche sans copie propre : la retirer ferait perdre le hit.
                r["dedupe_kept"] = "default_branch"
                continue
            pr = _pr_number_from_ref(r.get("ref", ""))
            if pr is not None:
                if open_prs is None:
                    # Liste inconnue : ne pas deviner. `KEEP` explicite, avec
                    # la raison publiee par le dry-run.
                    r["dedupe_kept"] = "open_prs_unknown"
                    continue
                if pr in open_prs:
                    # La PR tourne encore : ses runs relisent cette copie.
                    r["dedupe_kept"] = "pr_open"
                    continue
            r.update({"verdict": "EVICT", "reason": "duplicate_key_superseded"})


def _strip_quotes(value: str) -> str:
    v = (value or "").strip()
    if len(v) >= 2 and v[0] == v[-1] and v[0] in ("'", '"'):
        v = v[1:-1]
    return v.strip()


def _spec_covers(spec: str, version: str) -> bool:
    """Une spec de version YAML couvre-t-elle une version resolue ?

    `3.12` couvre `3.12.14` ; `3.x` couvre `3.12.14` ; `3.12.14` ne couvre
    que lui-meme. Une spec **illisible** (vide, expression `${{ ... }}`) couvre
    tout : une demande qu'on ne sait pas lire ne peut pas etre niee.
    """
    s = (spec or "").strip()
    if not s or "${{" in s:
        return True
    if s == version:
        return True
    parts = s.split(".")
    vparts = version.split(".")
    if len(parts) > len(vparts):
        return False
    for a, b in zip(parts, vparts):
        if a in ("x", "X", "*"):
            return True
        if a != b:
            return False
    return True


def _parse_step(rest: str, block: list[str]) -> dict[str, str]:
    """Extrait les cles d'un step (dont `uses` et le contenu de `with:`)."""
    out: dict[str, str] = {}

    def add(key: str, value: str) -> None:
        out.setdefault(key, value)

    m = re.match(r"^(?P<k>[\w.-]+)\s*:\s*(?P<v>.*)$", rest.strip())
    if m:
        add(m.group("k"), m.group("v"))

    indents = [len(ln) - len(ln.lstrip()) for ln in block if ln.strip()]
    if not indents:
        return out
    child_indent = min(indents)

    with_indent: Optional[int] = None
    with_entries: list[tuple[int, str]] = []
    for ln in block:
        if not ln.strip():
            continue
        ind = len(ln) - len(ln.lstrip())
        s = ln.strip()
        if with_indent is not None:
            if ind <= with_indent:
                with_indent = None
            else:
                with_entries.append((ind, s))
                continue
        if ind != child_indent:
            continue
        mm = re.match(r"^(?P<k>[\w.-]+)\s*:\s*(?P<v>.*)$", s)
        if not mm:
            continue
        key, value = mm.group("k"), mm.group("v")
        if key == "with" and not value.strip():
            with_indent = ind
            continue
        add(key, value)

    if with_entries:
        entry_indent = min(i for i, _ in with_entries)
        for ind, s in with_entries:
            if ind != entry_indent:
                continue
            mm = re.match(r"^(?P<k>[\w.-]+)\s*:\s*(?P<v>.*)$", s)
            if mm:
                add(mm.group("k"), mm.group("v"))
    return out


def _demand_from_workflow_text(text: str) -> list[dict[str, str]]:
    """Couples (package manager, version) demandes par les steps setup-python.

    Seul un step `actions/setup-python` **avec** une entree `cache:` compte :
    c'est lui qui écrit une cle de cache Actions. Le couple produit est
    `(cache, python-version)`.
    """
    lines = text.splitlines()
    out: list[dict[str, str]] = []
    i = 0
    while i < len(lines):
        m = re.match(r"^(?P<indent>\s*)-\s+(?P<rest>.*)$", lines[i])
        if not m:
            i += 1
            continue
        step_indent = len(m.group("indent"))
        j = i + 1
        block: list[str] = []
        while j < len(lines):
            ln = lines[j]
            if not ln.strip():
                block.append(ln)
                j += 1
                continue
            ind = len(ln) - len(ln.lstrip())
            if ind <= step_indent:
                break
            block.append(ln)
            j += 1
        step = _parse_step(m.group("rest"), block)
        if "actions/setup-python" in str(step.get("uses", "")):
            cache = _strip_quotes(str(step.get("cache", "")))
            if cache:
                out.append(
                    {
                        "pm": cache,
                        "version": _strip_quotes(str(step.get("python-version", ""))),
                    }
                )
        i = j
    return out


def _declared_demand(workflows_dir: Path) -> Optional[list[dict[str, str]]]:
    """Couples (cache, version) declares par les workflows de `main`, a la lecture.

    Retourne `None` quand la lecture est impossible ( repertoire absent,
    fichier illisible) : c'est le signal fail-CLOSED -- rien n'est evince.
    La liste est **derivee des workflows**, jamais figee dans le script : le
    critere suit les workflows au lieu de les deviner.
    """
    try:
        files = sorted(
            p for p in Path(workflows_dir).iterdir() if p.suffix in (".yml", ".yaml")
        )
    except OSError:
        return None
    if not files:
        return None
    demand: list[dict[str, str]] = []
    for f in files:
        try:
            text = f.read_text(encoding="utf-8")
        except OSError:
            return None
        demand.extend(_demand_from_workflow_text(text))
    return demand


def _mark_unrequested_keys(
    records: list[dict[str, Any]], demand: Optional[list[dict[str, str]]]
) -> None:
    """Evince les cles `setup-python` que plus aucun workflow de `main` ne demande.

    Decision A du coordinateur (2026-10-26, #19658) : une cle de cache
    `setup-python-<...>-python-<version>-<pm>-<hash>` n'est relisible que par un
    run dont le workflow **de `main`** pose le meme `cache:` ET resout la meme
    version. Quand aucun workflow de `main` ne demande plus ce couple
    `(cache, version)`, la cle est **prouvee orpheline** : elle ne peut plus
    etre relue ni reecrite, et sa copie sur une PR ouverte n'a plus de valeur
    (la regle fail-closed « copie de PR ouverte » ne protege que les cles
    **encore demandees**).

    La regle fail-closed « copie de PR ouverte » reste intacte pour toute cle
    encore demandee : cette passe ne contourne le garde des PRs ouvertes que
    pour une cle dont l'orphelinage est etabli.

    `demand is None` (workflows illisibles) : rien n'est evince, chaque cle
    `setup-python` est conservee avec la raison `unrequested_check_failed`.
    """
    for r in records:
        if r.get("verdict") != "KEEP":
            continue
        m = SETUP_PYTHON_RE.match(str(r.get("key", "")))
        if not m:
            continue
        pm = m.group("pm")
        version = m.group("version")
        r["setup_python_pm"] = pm
        r["setup_python_version"] = version
        r["setup_python_filehash"] = m.group("filehash")
        if demand is None:
            # Fail-CLOSED : la demande est inconnue, donc rien n'est affirme.
            r["reason"] = "unrequested_check_failed"
            continue
        covering = [
            d
            for d in demand
            if d.get("pm") == pm and _spec_covers(d.get("version", ""), version)
        ]
        if covering:
            r["reason"] = "requested_by_main"
            r["declared_by"] = covering[0].get("version", "")
            continue
        r.update({"verdict": "EVICT", "reason": "unrequested_by_main_workflows"})


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
        # `dedupe_kept` porte la raison d'une copie CONSERVEE par la passe de
        # deduplication (`pr_open`, `open_prs_unknown`, `default_branch`) :
        # sans lui le dry-run afficherait « dedupe_candidate » et laisserait
        # croire que rien n'a ete decide.
        reason = r.get("dedupe_kept") or r.get("reason", "-")
        print(
            f"{action:<10s}  {size_mb:6.1f} Mo  "
            f"sha={r.get('sha40', '-')[:10]}  {reason:<35s}  {key_trunc}"
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
    _mark_superseded(records, args.keep_latest)
    if not args.no_dedupe:
        # La liste des PRs ouvertes n'est lue que si la passe en a besoin :
        # un `--no-dedupe` ne doit pas dependre du reseau. Son absence rend
        # la passe conservatrice (aucune copie de PR evincee), jamais
        # devinante.
        open_prs = _list_open_pr_numbers(args.repo, token)
        if open_prs is None:
            print(
                "[WARN] PRs ouvertes illisibles : la passe de deduplication "
                "ne touchera a aucune copie de PR (fail-CLOSED).",
                file=sys.stderr,
            )
        else:
            print(
                f"[INFO] {len(open_prs)} PR(s) ouverte(s) : leurs copies de "
                f"cache sont conservees.",
                file=sys.stderr,
            )
        _mark_duplicate_keys(records, args.main_branch, open_prs)

    if not args.no_unrequested:
        # La demande est derivee des workflows de `main` lus sur le checkout du
        # sweep (sur le push vers `main`, ce checkout EST `main`). Une lecture
        # impossible rend la demande INCONNUE : fail-CLOSED, aucune cle
        # `setup-python` n'est evincee.
        demand = _declared_demand(Path(args.workflows_dir))
        if demand is None:
            print(
                "[WARN] Workflows de main illisibles : la demande est inconnue, "
                "aucune cle setup-python n'est evincee (fail-CLOSED).",
                file=sys.stderr,
            )
        else:
            pairs = sorted({(d.get("pm", ""), d.get("version", "")) for d in demand})
            print(
                f"[INFO] Demande derivee de {args.workflows_dir} : "
                f"{len(pairs)} couple(s) (cache, version) : "
                + ", ".join(f"{pm}/{ver}" for pm, ver in pairs),
                file=sys.stderr,
            )
        _mark_unrequested_keys(records, demand)

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
