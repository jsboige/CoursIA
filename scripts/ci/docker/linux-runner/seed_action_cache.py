#!/usr/bin/env python3
"""Embarque le cache d'archives d'actions dans l'image runner (#14853, A1).

Pourquoi ce fichier existe
--------------------------
Codeload sert les archives d'actions a un debit qui oscille (mesure #14853 du
2026-09-06 : 1 936 a 39 530 o/s). Sous ~16 Ko/s, l'archive de
`actions/setup-python` (1,5 Mo annonces) demande plus de 100 s, le runner
abandonne trois fois, et le job meurt sur `Set up job` -- AVANT le moindre
checkout, donc avant toute ligne du depot. Toutes les PRs ouvertes portent
alors un rouge requis que rien dans le depot n'explique.

Ces archives sont, par construction, identiques a chaque run. Le runner sait
les lire depuis un repertoire de cache : on les embarque donc dans l'image.

La cle de cache, lue dans le source du runner (pas devinee)
-----------------------------------------------------------
`src/Runner.Worker/ActionManager.cs`, `PrepareRepositoryAsync`, verifie au pin
`v2.337.0` (celui du `RUNNER_VERSION` du Dockerfile) ET sur `main` :

    var cacheArchiveFile = Path.Combine(
        actionArchiveCacheDir,
        downloadInfo.ResolvedNameWithOwner.Replace('/', '_'),
        $"{downloadInfo.ResolvedSha}.tar.gz");   # .zip sous Windows

Soit, sur Linux :

    $ACTIONS_RUNNER_ACTION_ARCHIVE_CACHE/<owner>_<repo>/<sha_resolu>.tar.gz

Deux consequences qui font echouer un cache ecrit « au feeling » :

- le `/` de `owner/repo` devient `_`, et le nom s'arrete au **depot** : une
  action de sous-chemin (`github/codeql-action/init@v4`) se cache sous
  `github_codeql-action/`, pas sous `github_codeql-action_init/` ;
- la cle est le **SHA resolu**, jamais le tag. `actions/setup-python@v5` ne se
  cache pas sous `v5.tar.gz`.

On resout donc tag -> SHA **ici, au build**, avec le meme mecanisme que le
runner (`git ls-remote`, deref `^{}` des tags annotes), pour que la cle ecrite
au build soit exactement celle que le runner cherchera au run.

Ce que ce script ne fait pas
----------------------------
Il n'active pas `ACTIONS_RUNNER_SYMLINK_CACHED_ACTIONS` (forme « dossier
deploye » du meme cache). Cette forme exige d'extraire chaque archive selon une
disposition stricte et le runner retombe silencieusement sur le telechargement
en cas d'ecart ; c'est un second levier, pas A1. L'archive est la forme que A1
demande.
"""

from __future__ import annotations

import argparse
import os
import subprocess
import sys
import tarfile
import time
import urllib.error
import urllib.request
import zlib

GITHUB = "https://github.com"
CODELOAD = "https://codeload.github.com"

# Actions distantes que les workflows du depot utilisent REELLEMENT.
#
# Cette liste se MESURE, elle ne se devine pas (#14853, A1). Les DEUX formes
# YAML d'une etape comptent -- `uses:` aligne sous un `name:`, et la forme en
# ligne de liste `- uses:` (133 occurrences dans le corpus au 2026-09-13). Un
# motif qui n'en couvre qu'une rate silencieusement toute action ecrite dans
# l'autre :
#
#   grep -rhoE '^[[:space:]]*(-[[:space:]]+)?uses:[[:space:]]*[^ #]+' \
#       .github/workflows/*.yml \
#     | sed 's/.*uses:[[:space:]]*//' | grep -v '^\./' | grep -v '^docker://' \
#     | grep -v '^jsboige/CoursIA/' | sort -u
#
# `scripts/tests/test_action_cache_seed_guard.py` rejoue cette mesure (en
# Python, sur les deux formes) et rougit si cette liste et les workflows
# divergent : une action ajoutee dans un workflow sans entree ici est un trou
# de cache silencieux. C'est ce test qui fait foi, pas la recette ci-dessus.
#
# Exclus volontairement par le filtre : les actions composites LOCALES de ce
# depot (`./.github/actions/lean-build`, `./.github/actions/lean-axiom` --
# meme depot, servies directement), les actions `docker://` (le runner ne les
# telecharge pas comme archives), et les workflows reutilisables de CE depot
# (`jsboige/CoursIA/.github/workflows/*@main`).
ACTIONS = (
    "actions/cache@v4",
    "actions/checkout@v4",
    "actions/deploy-pages@v4",
    "actions/github-script@v7",
    "actions/setup-dotnet@v4",
    "actions/setup-node@v4",
    "actions/setup-python@v5",
    "actions/upload-artifact@v4",
    "actions/upload-pages-artifact@v3",
    "github/codeql-action/init@v4",
    "github/codeql-action/autobuild@v4",
    "github/codeql-action/analyze@v4",
    "marocchino/sticky-pull-request-comment@v2",
)

ATTEMPTS = 3
TIMEOUT_S = 120


class SeedError(RuntimeError):
    """Echec de resolution ou de telechargement, apres epuisement des essais."""


def parse_uses(uses: str) -> tuple[str, str]:
    """`github/codeql-action/init@v4` -> (`github/codeql-action`, `v4`).

    Le depot s'arrete aux deux premiers segments : c'est ce que le runner
    appelle `ResolvedNameWithOwner`.
    """
    if "@" not in uses:
        raise SeedError(f"{uses!r} ne porte pas de ref (`owner/repo@ref`)")
    path, _, ref = uses.rpartition("@")
    segments = path.split("/")
    if len(segments) < 2 or not all(segments):
        raise SeedError(f"{uses!r} n'est pas `owner/repo[/subpath]@ref`")
    return "/".join(segments[:2]), ref


def cache_dir_name(repo: str) -> str:
    """`github/codeql-action` -> `github_codeql-action` (convention du runner)."""
    return repo.replace("/", "_")


def cache_archive_path(cache_root: str, repo: str, sha: str) -> str:
    """Chemin exact que le runner calculera au run (Linux : `.tar.gz`)."""
    return os.path.join(cache_root, cache_dir_name(repo), f"{sha}.tar.gz")


def _ls_remote(repo: str, pattern: str) -> list[tuple[str, str]]:
    """`git ls-remote` -> [(sha, ref), ...]. Vide si le motif ne matche rien."""
    try:
        out = subprocess.run(
            ["git", "ls-remote", f"{GITHUB}/{repo}.git", pattern],
            capture_output=True, text=True, encoding="utf-8", timeout=TIMEOUT_S,
        )
    except (OSError, subprocess.SubprocessError):
        return []
    if out.returncode != 0:
        return []
    pairs = []
    for line in out.stdout.splitlines():
        parts = line.split("\t")
        if len(parts) == 2 and parts[0]:
            pairs.append((parts[0], parts[1]))
    return pairs


def resolve_sha(repo: str, ref: str) -> str:
    """Resout `ref` en SHA de commit, comme le fait le runner.

    L'ordre compte : un tag **annote** rend d'abord le SHA de l'objet tag, et
    seul le deref `^{}` donne le commit -- c'est le commit que le runner inscrit
    dans sa cle de cache. Un tag leger (`actions/checkout@v4`) n'a pas de `^{}`
    et rend directement le commit.
    """
    for pattern in (f"refs/tags/{ref}^{{}}", f"refs/heads/{ref}", f"refs/tags/{ref}", ref):
        for sha, _ in _ls_remote(repo, pattern):
            if len(sha) == 40:
                return sha
    raise SeedError(
        f"ref {ref!r} introuvable sur {GITHUB}/{repo}.git "
        f"(essaie : tag annote, branche, tag leger)"
    )


def _fetch(url: str) -> bytes:
    req = urllib.request.Request(url, headers={"User-Agent": "coursia-runner-image"})
    with urllib.request.urlopen(req, timeout=TIMEOUT_S) as resp:  # noqa: S310
        return resp.read()


def verify_archive(path: str, repo: str) -> None:
    """Refuse une archive illisible ou sans racine unique.

    Le runner extrait l'archive et attend **exactement un** dossier racine (il
    leve `InvalidOperationException` sinon). Une archive tronquee par un debit
    degrade passerait sinon le build et echouerait au run -- c'est-a-dire
    exactement le mode d'echec que ce cache existe pour supprimer.
    """
    try:
        with tarfile.open(path, "r:gz") as tf:
            roots = {name.split("/")[0] for name in tf.getnames() if name.strip("/")}
    except (tarfile.TarError, OSError, EOFError, zlib.error) as exc:
        raise SeedError(f"archive illisible pour {repo} : {exc}") from exc
    if len(roots) != 1:
        raise SeedError(
            f"archive {repo} porte {len(roots)} racines ({sorted(roots)[:4]}) ; "
            f"le runner en exige exactement 1"
        )


def download_archive(repo: str, sha: str, dest: str) -> None:
    url = f"{CODELOAD}/{repo}/tar.gz/{sha}"
    last: Exception | None = None
    for attempt in range(1, ATTEMPTS + 1):
        try:
            blob = _fetch(url)
            with open(dest, "wb") as fh:
                fh.write(blob)
            verify_archive(dest, repo)
            return
        except (urllib.error.URLError, OSError, SeedError, ValueError) as exc:
            last = exc
            if os.path.exists(dest):
                os.remove(dest)
            if attempt < ATTEMPTS:
                print(f"  essai {attempt}/{ATTEMPTS} rate ({exc}), reprise...", flush=True)
                time.sleep(2 * attempt)
    raise SeedError(f"telechargement de {url} echoue apres {ATTEMPTS} essais : {last}")


def find_ref_conflicts(actions=ACTIONS) -> tuple[set[str], list[str]]:
    """Depots demandes sous deux refs : une seule cle de cache serait lue.

    Rend `(depots en conflit, messages)`. Pur et sans reseau -- c'est la partie
    que le test unitaire exerce.
    """
    seen: dict[str, str] = {}
    conflicted: set[str] = set()
    messages: list[str] = []
    for uses in actions:
        repo, ref = parse_uses(uses)
        previous = seen.setdefault(repo, ref)
        if previous != ref:
            conflicted.add(repo)
            messages.append(
                f"{uses} : le depot {repo} est deja demande en {previous!r} ; "
                f"deux refs pour un meme depot produiraient deux cles de cache "
                f"dont une seule sera lue"
            )
    return conflicted, messages


def seed(cache_root: str, actions=ACTIONS, dry_run: bool = False,
         allow_partial: bool = False) -> list[str]:
    """Remplit le cache. Rend la liste des chemins d'archives ecrits."""
    written: list[str] = []
    conflicted, failures = find_ref_conflicts(actions)

    for uses in actions:
        repo, ref = parse_uses(uses)
        if repo in conflicted:
            continue

        sha = resolve_sha(repo, ref)
        dest = cache_archive_path(cache_root, repo, sha)
        rel = os.path.relpath(dest, cache_root)
        if os.path.exists(dest):
            print(f"  deja en cache  {rel}")
            written.append(dest)
            continue
        if dry_run:
            print(f"  a telecharger  {rel}  ({repo}@{ref})")
            written.append(dest)
            continue
        os.makedirs(os.path.dirname(dest), exist_ok=True)
        print(f"  telecharge     {rel}  ({repo}@{ref})", flush=True)
        try:
            download_archive(repo, sha, dest)
        except SeedError as exc:
            failures.append(f"{uses} : {exc}")
            continue
        written.append(dest)

    if failures:
        message = "\n".join(f"  - {f}" for f in failures)
        if allow_partial:
            print(f"\nAVERTISSEMENT -- cache PARTIEL, {len(failures)} action(s) "
                  f"absente(s) :\n{message}", file=sys.stderr)
        else:
            raise SeedError(
                f"cache INCOMPLET, {len(failures)} action(s) absente(s) :\n{message}\n"
                f"Un cache partiel est un fix qui a l'air fait et ne l'est pas : "
                f"relancer le build, ou assumer explicitement avec --allow-partial."
            )
    return written


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--cache-dir", required=True,
                    help="repertoire cible (= ACTIONS_RUNNER_ACTION_ARCHIVE_CACHE)")
    ap.add_argument("--dry-run", action="store_true",
                    help="resout et liste sans telecharger")
    ap.add_argument("--allow-partial", action="store_true",
                    help="avertir au lieu d'echouer si une action manque")
    args = ap.parse_args(argv)

    print(f"cache d'archives d'actions -> {args.cache_dir} "
          f"({len(ACTIONS)} actions, {len({parse_uses(a)[0] for a in ACTIONS})} depots)")
    try:
        written = seed(args.cache_dir, dry_run=args.dry_run,
                       allow_partial=args.allow_partial)
    except SeedError as exc:
        print(f"\nECHEC : {exc}", file=sys.stderr)
        return 1
    print(f"\nOK -- {len(written)} archive(s) en cache")
    return 0


if __name__ == "__main__":
    sys.exit(main())
