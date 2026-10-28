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

Le defaut n'est pas reparable cote configuration. Etat mesure le 2026-09-14 :
CodeQL tournait en default setup, qui ne suit aucun fichier
`.github/workflows/codeql.yml` (gere par GitHub, absent de `codeql*`). Depuis
#22548 (2026-10-25) le depot porte un workflow advanced setup : **le format de
cle peut avoir change** et le pattern ci-dessous, mesure sur le default setup,
n'a pas encore ete revalide sur une analyse advanced. Un balayage en dry-run
apres la bascule est la mesure a faire ; tout cache non reconnu sort en REFUSE
(`not_codeql_overlay`), jamais en silence. Le remede reste cote REPO :
eviction periodique des caches dont le SHA n'est plus ancetre de `main`, ET/OU
dont le `last_accessed_at` est anterieur a une fenetre de retention choisie.

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
5. **Ou cache TRAP CodeQL supersede** (#22937) : les cles
   `codeql-trap-<ver>-<toolchain>-<lang>-<sha40>` ne sont adressables que
   par restore-key, qui rend la plus RECENTE entree du prefixe -- jamais
   une autre. On garde les `--keep-latest-traps` plus recentes par
   famille sur la branche par defaut (defaut 1), on evince le reste.
   Mesure du 2026-10-27 : 77 entrees / 2 222 Mo, toutes sur `main`, dont
   22 jamais lues ; cf. section « Format de cle TRAP CodeQL ».

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
- **Pas d'appel DELETE sans confirmation visuelle** : le dry-run affiche
  l'identifiant de cache, la cle tronquee, la raison, et la taille. Le
  `--apply` ne supprime que les evictables listes au dry-run.

## Format de cle TRAP CodeQL (mesure 2026-10-26/27, #22937)

    codeql-trap-1-2.27.3-javascript-<sha40>

- `1` : version du format de cache TRAP cote codeql-action.
- `2.27.3` : version du bundle CodeQL.
- `javascript` : langage de l'extracteur CodeQL (pas le nom de matrice
  `javascript-typescript` de la CI).
- `<sha40>` : SHA du commit analyse. Une cle par commit : chaque push sur
  `main` ecrit une entree neuve (~28,9 Mo) et rend la precedente
  inadressable.

Le lecteur est unique et partiel, mesure dans les journaux du 2026-10-27 :

- **La branche par defaut ne restaure jamais** : « Analyzing default
  branch. Skipping downloading of TRAP caches. » (run 40512896186, job
  Analyze (javascript-typescript)). `main` ne fait qu'ECRIRE.
- **Les analyses de PR restaurent par restore-key uniquement** : la cle
  exacte demandee est `codeql-trap-1-2.27.3-javascript-unknown` (job
  122140111550) -- jamais un SHA -- et la restore-key prefixee rend la
  plus recente entree visible. Aucune requete ne peut donc adresser une
  entree autre que la plus recente de sa famille : garder 1 entree par
  famille preserve exactement 100 % des restaurations possibles.
- **Le gain de la restauration est mesure** : extraction + import TRAP
  12,1 s avec cache restaure (job 122140111550, 2 955 fichiers) contre
  19,1 s sans restauration (job 122254109719, 2 967 fichiers), soit
  ~7 s par analyse. La desactivation du trap-caching ne serait donc pas
  justifiee par un gain nul -- la voie retenue est l'eviction, pas
  `trap-caching: false`.
- **55 des 75 entrees ecrites sous default setup ont ete relues** (de
  10 s a 2 h apres creation, par les analyses de PR de l'epoque ou toute
  PR etait analysee). Les 2 entrees ecrites sous advanced setup (#22553,
  2026-10-27 13:25Z) ne l'ont pas encore ete : la fenetre ne portait
  aucune PR touchant du JS/TS, ce qui n'est PAS une preuve d'inutilite
  -- une PR JS/TS derive une analyse javascript (matrice de codeql.yml)
  qui restaurerait l'entree la plus recente.
- **Nettoyage interne absent** : `codeql.yml` declare `permissions:
  contents: read` au workflow et `actions: read` au job analyze -- sans
  le droit d'ecriture sur les caches, l'action ne peut pas retirer ses
  anciens TRAP elle-meme.

## Format de cle CodeQL default setup (mesure 2026-09-14)

    codeql-overlay-base-database-1-<random8>-<lang>-2.27.0-<sha40>-<runid>-1

**Non revalide depuis la bascule advanced setup (#22548, 2026-10-25)** : ce
format est celui du default setup. Le premier dry-run qui suit la bascule est
la mesure a faire ; un `-1-<random8>` qui disparait ferait tomber la famille
entiere en REFUSE `not_codeql_overlay` — visible dans le rapport, jamais
silencieux.

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
- .github/workflows/codeql.yml : absente du depot jusqu'a #22548 (2026-10-25),
  qui fait passer CodeQL en advanced setup. Le workflow existe desormais, donc
  le declencheur `workflow_run: [CodeQL]` de evict-orphan-caches.yml resout un
  workflow reel (question ouverte #18309). Le format de cle CodeQL, lui, reste
  a revalider sur une analyse advanced : cf. section « Format de cle ».
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

# Pattern d'une cle TRAP CodeQL (mesure 2026-10-26/27, #22937). Une cle par
# commit analyse : `codeql-trap-<cachever>-<toolchain>-<lang>-<sha40>`.
# Adressage par restore-key uniquement (la plus recente de la famille) --
# cf. la section « Format de cle TRAP CodeQL » du module pour les journaux
# qui fondent ce lecteur unique et partiel.
CODEQL_TRAP_RE = re.compile(
    r"^codeql-trap-"
    r"(?P<cachever>\d+)-"
    r"(?P<toolchain>[\d.]+)-"
    r"(?P<lang>\w+)-"
    r"(?P<sha40>[0-9a-f]{40})$"
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
        "--keep-latest-traps",
        type=int,
        default=1,
        help="Per TRAP family (cache version + toolchain + language), keep "
        "only the N most recent caches on the default branch and evict the "
        "older ones (default: 1; 0 disables). #22937: PR analyses restore "
        "TRAP caches by restore-key, which only ever serves the newest "
        "entry of the family, so a single kept entry preserves every "
        "possible restore.",
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
        # #22937 : cache TRAP CodeQL. Pas de test d'ancestry ni d'age ici :
        # l'adressage d'un cache TRAP ne depend NI du SHA de sa cle (la cle
        # exacte demandee par les analyses est `...-<lang>-unknown`), NI de
        # sa date (la restore-key rend la plus recente de la famille). La
        # seule question est "est-ce la plus recente de ma famille sur la
        # branche par defaut", et c'est `_mark_superseded_traps` qui y
        # repond -- le dry-run affiche donc un KEEP provisoire
        # `trap_candidate`, tranche par la passe.
        mt = CODEQL_TRAP_RE.match(key)
        if mt:
            rec.update({"verdict": "KEEP", "reason": "trap_candidate"})
            rec["trap_family"] = (
                f"{mt.group('cachever')}-{mt.group('toolchain')}-{mt.group('lang')}"
            )
            return rec
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


def _mark_superseded_traps(
    records: list[dict[str, Any]],
    main_branch: str,
    keep: int = 1,
) -> None:
    """#22937 : evincer les caches TRAP au-dela de la plus recente par famille.

    Un cache TRAP `codeql-trap-<ver>-<toolchain>-<lang>-<sha>` n'a qu'un
    lecteur possible et partiel (journaux du 2026-10-27, cf. la section
    « Format de cle TRAP CodeQL » du module) :

    * la branche par defaut ne restaure JAMAIS (« Analyzing default branch.
      Skipping downloading of TRAP caches. », run 40512896186) -- `main`
      ne fait qu'ecrire ;
    * les analyses de PR demandent la cle exacte `...-<lang>-unknown` (job
      122140111550) et restaurent par restore-key, qui rend la plus
      RECENTE entree du prefixe. Aucune requete ne peut adresser une
      entree autre que la plus recente de sa famille.

    Garder `keep` entrees par famille preserve donc exactement 100 % des
    restaurations possibles ; evincer le reste est sans perte. Mesure du
    2026-10-27 : 77 entrees `codeql-trap-*` (2 222 Mo), toutes sur
    `refs/heads/main`, dont 22 jamais lues -- chaque push sur `main` en
    ecrit une neuve (~28,9 Mo) et rend la precedente inadressable.

    Seules les entrees scellees sur la branche par defaut sont traitees :
    une entree sur `refs/pull/<n>/merge` reste visible des runs de sa PR
    (scope GitHub), on ne la touche pas -- elle est affichee
    `not_default_branch` au dry-run, jamais silencieuse.
    """
    if keep <= 0:
        return
    default_ref = f"refs/heads/{main_branch}"
    families: dict[str, list[dict[str, Any]]] = {}
    for r in records:
        if r.get("verdict") == "KEEP" and "trap_family" in r:
            if str(r.get("ref", "")) != default_ref:
                r["trap_kept"] = "not_default_branch"
                continue
            families.setdefault(r["trap_family"], []).append(r)
    for members in families.values():
        members.sort(key=lambda r: _parse_iso(r["created_at"]), reverse=True)
        for r in members[keep:]:
            r.update({"verdict": "EVICT", "reason": "trap_superseded_by_newer"})


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
        # croire que rien n'a ete decide. `trap_kept` joue le meme role pour
        # un cache TRAP hors branche par defaut (`not_default_branch`).
        reason = (
            r.get("dedupe_kept") or r.get("trap_kept") or r.get("reason", "-")
        )
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
    _mark_superseded_traps(records, args.main_branch, args.keep_latest_traps)
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
