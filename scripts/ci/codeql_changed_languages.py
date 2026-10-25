#!/usr/bin/env python3
"""Derive the CodeQL language matrix of a pull request (#22548).

Advanced setup (decision mainteneur Q142 = c, issue #22548, audit CI #22461)
remplace le default setup de GitHub par `.github/workflows/codeql.yml`. Le
workflow est filtre par `paths` sur le code reellement analyse, mais une PR qui
touche du Python n'a aucune raison de payer trois analyses de plus : la matrice
est donc **derivee des langages dont un fichier a change**, au lieu d'etre
toujours x4.

## Pourquoi l'API et pas `git diff`

`git diff base...head` demanderait un clone complet (`fetch-depth: 0`). Le
depot pese 2,1 Go et 46 workflows le clonent deja ainsi : c'est une depense
que #22461 cherche a reduire, pas a etendre. Le job `changes` fait donc un
checkout superficiel et lit la liste des fichiers via
`GET /repos/{repo}/pulls/{n}/files`. Le chemin `git` reste disponible pour un
usage local, hors CI.

## Pourquoi ici et pas dans le YAML

1. c'est testable — `scripts/ci/tests/test_codeql_changed_languages.py` ;
2. `scripts/ci/detect_python_nu_jobs.py` lit les blocs `run:` des workflows et
   signale tout `python` nu : les identifiants de langage CodeQL (`"python"`)
   d'un heredoc y ressemblent a une invocation d'interpreteur. Le detecteur
   n'est pas elargi ; c'est le code qui change de place.

## Contrat : FAIL-OPEN

Toute incertitude rend la **matrice complete** — API injoignable, reponse
illisible, liste tronquee (plafond de 3 000 fichiers de GitHub), diff
impossible, ensemble vide. Se tromper dans ce sens coute du calcul ; se
tromper dans l'autre laisse du code non analyse. La raison choisie est
toujours imprimee et sort en JSON pour l'audit.

Deux mesures faites sur le premier passage en CI (PR #22553, job
`CodeQL changed languages`) : la matrice est retombee complete avec la seule
raison « diff illisible (HTTPError) », qui ne distingue pas un 403 (permissions
ou quota secondaire) d'un 404 (URL) — deux causes, deux remedes. La raison
nomme donc desormais le **statut et le debut du corps** de la reponse, et un
403/429/5xx transitoire est retente une fois (l'IP d'un runner heberge est
partagee, le « secondary rate limit » y est courant) avant de faillir ouvert.

## Sortie

- `--github-output <path>` (ou `$GITHUB_OUTPUT`) recoit `languages=<json>`,
   la matrice du job ;
- stdout : la matrice et sa raison, en clair.

## Codes de sortie

- 0 : matrice produite (fail-open compris) ;
- 1 : instrument casse — `GITHUB_OUTPUT` illisible ou non inscriptible. Un 0
   silencieux laisserait `fromJSON('')` echouer plus loin sur un message qui
   ne nomme pas la cause.

Usage (CI) :
    python scripts/ci/codeql_changed_languages.py \
        --event pull_request --repo jsboige/CoursIA --pr 12345
Usage (local, sans jeton) :
    python scripts/ci/codeql_changed_languages.py --event pull_request --base-ref main
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
import time
import urllib.error
import urllib.request
from collections.abc import Callable, Iterable
from pathlib import Path

EXIT_OK = 0
EXIT_BROKEN = 1

# Plafond dur de l'API GitHub sur la liste des fichiers d'une PR.
API_FILE_CAP = 3000
API_PER_PAGE = 100

# Ordre stable : il fixe l'ordre des jobs `Analyze (...)` rendus par la matrice.
# `csharp` porte `build_mode: none` — aucun build (voir l'en-tete de
# `.github/workflows/codeql.yml` : le default setup, lui, construisait le C#,
# ~6 min 34 s sur #14746 ; c'est un arbitrage de cout assume, reversible en une
# ligne de matrice).
LANGUAGES: list[dict] = [
    {"language": "actions"},
    {"language": "csharp", "build_mode": "none"},
    {"language": "javascript-typescript"},
    {"language": "python"},
]

# Surfaces analysees. Un fichier peut n'appartenir a aucune (carnet, markdown,
# Lean, donnees) : c'est le cas nominal, pas une erreur.
LANGUAGE_BY_EXT: dict[str, str] = {
    ".py": "python",
    ".cs": "csharp",
    ".csproj": "csharp",
    ".sln": "csharp",
    ".cshtml": "csharp",
    ".razor": "csharp",
    ".js": "javascript-typescript",
    ".mjs": "javascript-typescript",
    ".cjs": "javascript-typescript",
    ".jsx": "javascript-typescript",
    ".ts": "javascript-typescript",
    ".tsx": "javascript-typescript",
    ".mts": "javascript-typescript",
    ".cts": "javascript-typescript",
}

# Repertoires dont tous les fichiers appartiennent au langage `actions`.
ACTIONS_PREFIXES = (".github/workflows/", ".github/actions/")


def full_matrix() -> list[dict]:
    """La matrice complete, copiee : les appelants ne partagent pas l'etat."""
    return [dict(item) for item in LANGUAGES]


def entry_for(language: str) -> dict:
    """L'entree de matrice d'un langage, avec ses options (`build_mode`)."""
    for item in LANGUAGES:
        if item["language"] == language:
            return dict(item)
    return {"language": language}


def languages_for(paths: Iterable[str]) -> set[str]:
    """Langages CodeQL touches par une liste de chemins (relatifs au depot)."""
    found: set[str] = set()
    for raw in paths:
        path = str(raw).strip()
        if not path:
            continue
        if path.startswith(ACTIONS_PREFIXES):
            found.add("actions")
            continue
        for ext, language in LANGUAGE_BY_EXT.items():
            if path.endswith(ext):
                found.add(language)
                break
    return found


def matrix_for(found: Iterable[str]) -> list[dict]:
    """Matrice ordonnee pour un ensemble de langages ; vide = matrice complete."""
    wanted = set(found)
    if not wanted:
        return full_matrix()
    return [entry_for(item["language"]) for item in LANGUAGES
            if item["language"] in wanted]


def _fetch_with_retry(fetch, request, attempts: int = 2, pause_s: float = 1.0):
    """`fetch(request, timeout=20)` avec une seconde chance sur 403/429/5xx.

    Motif mesure : un runner heberge partage son IP avec le reste du cluster,
    et GitHub repond alors 403 « secondary rate limit ». Une seule tentative
    ferait retomber la matrice sur 4 langages pour une cause passagere — du
    calcul paye en silence. Un vrai refus de permission (403 stable) ne coute
    que `pause_s` de plus.
    """
    last: Exception | None = None
    for attempt in range(attempts):
        try:
            return fetch(request, timeout=20)
        except urllib.error.HTTPError as exc:
            if exc.code not in (403, 429, 500, 502, 503, 504) or attempt == attempts - 1:
                raise
            last = exc
            time.sleep(pause_s)
    raise last  # pragma: no cover - la boucle leve avant


def _api_pr_paths(
    repo: str,
    number: int,
    token: str | None,
    opener: Callable[..., object] | None = None,
    per_page: int = API_PER_PAGE,
) -> list[str]:
    """Chemins modifies d'une PR via l'API ; leve si la liste est tronquee."""
    fetch = opener or urllib.request.urlopen
    paths: list[str] = []
    page = 1
    while True:
        url = (
            f"https://api.github.com/repos/{repo}/pulls/{number}/files"
            f"?per_page={per_page}&page={page}"
        )
        headers = {"Accept": "application/vnd.github+json",
                   "User-Agent": "coursia-codeql-changed-languages"}
        if token:
            headers["Authorization"] = "Bearer " + token
        request = urllib.request.Request(url, headers=headers)
        with _fetch_with_retry(fetch, request) as response:
            payload = json.loads(response.read().decode("utf-8"))
        if not isinstance(payload, list):
            raise TypeError("reponse inattendue de l'API")
        paths.extend(str(item.get("filename", "")) for item in payload
                     if isinstance(item, dict))
        if len(payload) < per_page:
            return paths
        page += 1
        if len(paths) >= API_FILE_CAP:
            raise ValueError(f"liste tronquee au plafond de {API_FILE_CAP} fichiers")


def _git_diff_paths(base_ref: str) -> list[str]:
    """Chemins modifies entre la base et la tete (usage local ; leve en cas d'echec)."""
    subprocess.run(
        ["git", "fetch", "--no-tags", "origin", base_ref],
        check=True,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )
    diff = subprocess.run(
        ["git", "diff", "--name-only", "FETCH_HEAD...HEAD"],
        check=True,
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
    )
    return [line.strip() for line in diff.stdout.splitlines() if line.strip()]


def _describe(exc: BaseException) -> str:
    """Nomme la cause d'un fail-open : un type seul est un angle mort.

    Premiere mesure en CI (PR #22553, job `CodeQL changed languages`) : la
    matrice est retombee complete avec la raison « diff illisible
    (HTTPError) ». Un `HTTPError` ne dit ni 403 (permissions / quota
    secondaire) ni 404 (URL), et ces deux causes n'ont pas le meme remede.
    Le statut et le debut du corps de la reponse sont donc repris ici.
    """
    name = type(exc).__name__
    if isinstance(exc, urllib.error.HTTPError):
        detail = f"HTTP {exc.code}"
        try:
            body = exc.read().decode("utf-8", "replace")[:200].strip()
        except Exception:  # noqa: BLE001 - un corps illisible ne masque pas le code
            body = ""
        if body:
            detail += " " + " ".join(body.split())
        return f"{name}: {detail}"
    text = str(exc).strip()
    return f"{name}: {text}" if text else name


def derive(
    event: str,
    base_ref: str = "main",
    diff_paths: Callable[[str], list[str]] | None = None,
) -> tuple[list[dict], str]:
    """Rend (matrice, raison). Fail-open : la raison dit toujours pourquoi."""
    if event != "pull_request":
        return full_matrix(), f"evenement {event or '?'} : matrice complete"

    reader = diff_paths or _git_diff_paths
    try:
        paths = reader(base_ref)
    except Exception as exc:  # noqa: BLE001 - fail-open documente en tete
        return full_matrix(), (
            "diff illisible (" + _describe(exc) + ") : matrice complete"
        )

    found = languages_for(paths)
    if not found:
        return full_matrix(), "aucun langage reconnu dans le diff : matrice complete"
    return matrix_for(found), "langages touches : " + ", ".join(sorted(found))


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--event", default=os.environ.get("EVENT_NAME", ""),
                        help="github.event_name")
    parser.add_argument("--base-ref", default=os.environ.get("BASE_REF", "main"),
                        help="github.base_ref (branche cible de la PR)")
    parser.add_argument("--repo", default=os.environ.get("GITHUB_REPOSITORY"),
                        help="owner/name (defaut : $GITHUB_REPOSITORY)")
    parser.add_argument("--pr", type=int,
                        default=int(os.environ.get("PR_NUMBER") or 0),
                        help="numero de la PR (defaut : $PR_NUMBER)")
    parser.add_argument("--github-output", default=None,
                        help="fichier de sortie (defaut : $GITHUB_OUTPUT)")
    parser.add_argument("--json", action="store_true",
                        help="emettre un document JSON au lieu du texte")
    args = parser.parse_args(argv)

    token = os.environ.get("GITHUB_TOKEN") or os.environ.get("GH_TOKEN")
    if args.pr and args.repo:
        def reader(_base_ref: str) -> list[str]:
            return _api_pr_paths(args.repo, args.pr, token)

        matrix, reason = derive(args.event, args.base_ref, diff_paths=reader)
    else:
        matrix, reason = derive(args.event, args.base_ref)

    payload = {"languages": matrix, "reason": reason}
    if args.json:
        print(json.dumps(payload, ensure_ascii=False))
    else:
        print("matrix: " + json.dumps(matrix))
        print("reason: " + reason)

    output = args.github_output or os.environ.get("GITHUB_OUTPUT")
    if output:
        try:
            with Path(output).open("a", encoding="utf-8") as handle:
                handle.write("languages=" + json.dumps(matrix) + "\n")
        except OSError as exc:
            print(f"ECHEC : GITHUB_OUTPUT illisible ({exc})", file=sys.stderr)
            return EXIT_BROKEN
    return EXIT_OK


if __name__ == "__main__":
    raise SystemExit(main())
