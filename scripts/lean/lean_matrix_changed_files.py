#!/usr/bin/env python3
"""Liste des fichiers modifies d'un evenement, pour le job `changes` de
``.github/workflows/lean-ci-matrix.yml`` (#22065).

Le job doit choisir les lakes a batir : il lit la liste des fichiers
modifies dans l'API REST (pull_request : fichiers de la PR ; push :
compare avant..apres) puis la passe au dispatcher.

Avant ce correctif, la lecture etait faite dans le shell avec un repli
silencieux (``|| echo -n "" > "$out"``) : un 403 de quota transformait la
liste des fichiers modifies en liste VIDE, donc ``any=false``, donc le
build Lean etait ``skipped`` -- et ``skipped`` se replie en vert. Un
build Lean qui n'a pas eu lieu s'affichait comme fait (instance #21999,
run 39814286963 : ``gh: API rate limit exceeded ... (HTTP 403)`` suivi
d'une liste vide, et pourtant le job de build au vert).

Ici l'echec est BRUYANT : une nouvelle tentative (le 403 de quota
d'installation est transitoire -- le rejeu a reussi sur l'instance
mesuree), puis sortie non nulle. Le fichier de sortie n'est ecrit
qu'a la reussite : un ``any=false`` ne peut pas naitre d'une lecture en
echec.
"""

from __future__ import annotations

import argparse
import subprocess
import sys
import time
from pathlib import Path

# Self-cover : un evenement manuel est une intention explicite de tout
# lancer (le dispatcher y arrive par le self-cover du gate).
SELF_COVER = ".github/workflows/lean-ci-matrix.yml"


class ApiError(RuntimeError):
    """La lecture de l'API GitHub a echoue."""


def _gh_api(args: list[str]) -> str:
    proc = subprocess.run(
        ["gh", "api", *args],
        capture_output=True,
        text=True,
        encoding="utf-8",
    )
    if proc.returncode != 0:
        detail = (proc.stderr or proc.stdout or "").strip()
        raise ApiError(
            f"gh api {' '.join(args)} a echoue (rc={proc.returncode}) : {detail}"
        )
    return proc.stdout


def _lines(text: str) -> list[str]:
    return [line.strip() for line in text.splitlines() if line.strip()]


def changed_files_pull_request(repo: str, pr: int) -> list[str]:
    out = _gh_api([
        "--paginate",
        f"repos/{repo}/pulls/{pr}/files",
        "--jq", ".[].filename",
    ])
    return _lines(out)


def changed_files_push(repo: str, before: str, sha: str) -> list[str]:
    if before.startswith("0000000"):
        # Nouvelle histoire de branche : on ne peut pas differencer -> tout.
        return [SELF_COVER]
    out = _gh_api([
        f"repos/{repo}/compare/{before}...{sha}",
        "--jq", ".files[].filename",
    ])
    return _lines(out)


def collect(
    event: str,
    repo: str,
    pr: str | None = None,
    before: str | None = None,
    sha: str | None = None,
) -> list[str]:
    if event == "pull_request":
        if not pr:
            raise ValueError("evenement pull_request sans numero de PR")
        return changed_files_pull_request(repo, int(pr))
    if event == "push":
        if not before or not sha:
            raise ValueError("evenement push sans before/sha")
        return changed_files_push(repo, before, sha)
    if event == "workflow_dispatch":
        return [SELF_COVER]
    raise ValueError(f"evenement non gere : {event}")


def collect_with_retry(
    event: str,
    repo: str,
    pr: str | None = None,
    before: str | None = None,
    sha: str | None = None,
    retries: int = 1,
    sleep_s: float = 5.0,
) -> list[str]:
    """Une nouvelle tentative sur echec de l'API, puis l'echec remonte.

    Le 403 de quota d'installation est transitoire (instance #21999 : le
    rejeu du job a dispatche le build normalement). Au-dela, l'echec
    remonte : mieux vaut un job rouge qu'un build qui n'a pas eu lieu.
    """
    last: Exception | None = None
    for attempt in range(retries + 1):
        try:
            return collect(event, repo, pr=pr, before=before, sha=sha)
        except ApiError as exc:
            last = exc
            if attempt < retries:
                print(
                    f"lecture API en echec ({exc}) -- nouvelle tentative "
                    f"dans {sleep_s}s",
                    file=sys.stderr,
                )
                time.sleep(sleep_s)
    assert last is not None
    raise last


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--event", required=True,
                    help="pull_request | push | workflow_dispatch")
    ap.add_argument("--repo", required=True, help="owner/name")
    ap.add_argument("--pr", default=None, help="numero de PR (pull_request)")
    ap.add_argument("--before", default=None, help="sha avant (push)")
    ap.add_argument("--sha", default=None, help="sha courant (push)")
    ap.add_argument("--out", required=True, type=Path,
                    help="fichier de sortie (une ligne par chemin)")
    ap.add_argument("--retries", type=int, default=1,
                    help="nouvelles tentatives sur echec de l'API")
    ap.add_argument("--sleep", type=float, default=5.0,
                    help="attente entre deux tentatives (secondes)")
    args = ap.parse_args(argv)

    try:
        files = collect_with_retry(
            args.event, args.repo,
            pr=args.pr, before=args.before, sha=args.sha,
            retries=args.retries, sleep_s=args.sleep,
        )
    except (ApiError, ValueError) as exc:
        # BRUYANT : aucun fichier de sortie n'est ecrit, le job echoue.
        print(f"LEAN-MATRIX CHANGED-FILES: {exc}", file=sys.stderr)
        return 1

    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(
        "".join(f"{name}\n" for name in files), encoding="utf-8"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
