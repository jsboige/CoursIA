#!/usr/bin/env python3
"""Ecriture GitHub **REST**, avec la garde post-POST du depot (#26973, ligne 1).

Pourquoi cet organe existe
--------------------------
Le compte partage `jsboige` a un **seau GraphQL** (5000 req/h) divise par le
nombre de lanes : cinq lanes sur sept citent l'echec GraphQL dans leur tour
de table des freins du 16/11/2026. Les endpoints **REST** passent par un seau
`core` separe. Le detour est donc ecrit une fois, ici, au lieu d'etre
refait a la main a chaque cycle (~12 min de ceremonie mesures par cycle,
pour quatre ecritures).

Ce que fait l'organe
--------------------
Quatre gestes, tous par **`--input`** (un payload JSON construit par
`json.dumps`) :

| verbe | methode | endpoint |
|---|---|---|
| `comment` | POST | `/repos/<repo>/issues/<n>/comments` |
| `pr-comment` | POST | `/repos/<repo>/issues/<pr>/comments` |
| `pr-create` | POST | `/repos/<repo>/pulls` |
| `edit-body` | PATCH | `/repos/<repo>/issues/<n>` |
| `edit-pr-body` | PATCH | `/repos/<repo>/pulls/<pr>` |

La garde post-POST (`gh-posting-hygiene`, regle 2) est **faite par
l'organe**, pas laissee a la memoire de l'appelant. L'organe tient le
corps **envoye** : il compare le corps **publie** (celui que l'API
renvoie) a celui qu'il a pose, et verifie trois predicats :

1. **divergence** (predicat principal) -- le corps publie n'est pas celui
   qui a ete envoye : le piege `-f body=@fichier` a tire (echec
   silencieux de 100 %) ou l'API a tronque ;
2. **longueur** -- un corps publie de moins de 100 caracteres, signalee
   **seulement** si les deux diffèrent : un corps court publie a
   l'identique est un corps **legitime** (un `[CLAIMED]` de 60 caracteres
   n'a rien d'anormal) ;
3. **structure** -- le corps publie ne doit pas parser en objet JSON portant
   une cle `body` : c'est le payload complet passe comme corps, le vrai
   corps echappe a l'interieur d'une chaine (#17326).

Quand une garde echoue, l'organe **rend quand meme l'id et l'URL** (le
correctif est un PATCH sur cet id) et sort avec `rc=3` : le POST a eu lieu,
la publication est douteuse. `rc=2` est reserve a l'erreur d'usage (verbe
inconnu, corps illisible ou vide, jeton absent) : rien n'a ete publie.

Le jeton
--------
`--token-source` :

- `user` (defaut) : `resolve_write_token()` de `post_dossier.py` — **importe**,
  jamais reecrit (le jeton d'ecriture `jsboige` est epingle par commande) ;
- `env` : le `GH_TOKEN` de l'environnement — c'est la voie du jeton **App**
  de la lane, exporte en amont par `scripts/secrets/github_app_token.py` ;
- `app` : le jeton App forge a la demande (`--app-id`, `--app-key-path`) ;
  le jeton **n'est jamais affiche**.

Usage
-----
    python scripts/coordination/gh_rest_post.py comment \
        --repo jsboige/CoursIA --number 26966 --body-file corps.md
    python scripts/coordination/gh_rest_post.py pr-comment \
        --repo jsboige/CoursIA --number 26704 --body-file corps.md
    python scripts/coordination/gh_rest_post.py pr-create \
        --repo jsboige/CoursIA --base main --head fix/x --title "..." \
        --body-file corps.md
    python scripts/coordination/gh_rest_post.py edit-pr-body \
        --repo jsboige/CoursIA --number 26976 --body-file corps.md

Sortie : une ligne JSON `{"id": ..., "url": ..., "length": ..., "guards": [...]}`.
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path

SCRIPTS_DIR = Path(__file__).resolve().parent.parent
if str(SCRIPTS_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPTS_DIR))

from coordination import post_dossier  # noqa: E402

#: Longueur minimale d'un corps publie. En dessous, le piege `-f body=@` a
#: tire : un corps de 30 a 50 caracteres atterrit sans erreur et sans corps.
MIN_PUBLISHED_LEN = 100

#: Verbes et leur methode / gabarit d'endpoint.
ENDPOINTS = {
    "comment": ("POST", "/repos/{repo}/issues/{number}/comments"),
    "pr-comment": ("POST", "/repos/{repo}/issues/{number}/comments"),
    "pr-create": ("POST", "/repos/{repo}/pulls"),
    "edit-body": ("PATCH", "/repos/{repo}/issues/{number}"),
    "edit-pr-body": ("PATCH", "/repos/{repo}/pulls/{number}"),
}

#: Codes de sortie.
EXIT_OK = 0
EXIT_USAGE = 2
EXIT_GUARD = 3


def resolve_token(source: str, app_id: str = "", app_key_path: str = "") -> str:
    """Le jeton d'ecriture, selon la source demandee.

    `user` : `resolve_write_token()` de `post_dossier.py` — le jeton
    `jsboige` epingle par commande (importe, jamais reecrit).
    `env` : le `GH_TOKEN` de l'environnement (jeton App exporte en amont).
    `app` : le jeton App forge a la demande ; il n'est jamais affiche.
    """
    if source == "user":
        return post_dossier.resolve_write_token()
    if source == "env":
        token = os.environ.get("GH_TOKEN", "").strip()
        if not token:
            raise RuntimeError(
                "--token-source env : GH_TOKEN est absent de l'environnement"
            )
        return token
    if source == "app":
        if not app_id or not app_key_path:
            raise RuntimeError(
                "--token-source app : --app-id et --app-key-path sont requis"
            )
        proc = subprocess.run(
            [
                sys.executable,
                str(SCRIPTS_DIR / "secrets" / "github_app_token.py"),
                "--app-id",
                app_id,
                "--key",
                app_key_path,
                "--quiet",
            ],
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
        )
        if proc.returncode != 0 or not proc.stdout.strip():
            raise RuntimeError(
                "cannot forge the App token: {}".format(
                    (proc.stderr or proc.stdout).strip()[:200]
                )
            )
        return proc.stdout.strip()
    raise RuntimeError("source de jeton inconnue : {}".format(source))


def build_payload(args: argparse.Namespace, body: str) -> dict:
    """Le payload JSON du POST, construit par `json.dumps` (jamais en ligne).

    Le corps vient **toujours** d'un fichier : l'organe n'a pas d'option
    qui accepte un corps en ligne, donc aucune forme du piege `-f body=@`
    n'est saisissable depuis la ligne de commande.
    """
    payload: dict = {}
    if args.verb == "pr-create":
        payload["title"] = args.title
        payload["head"] = args.head
        payload["base"] = args.base
        if args.draft:
            payload["draft"] = True
    payload["body"] = body
    return payload


def endpoint_for(verb: str, repo: str, number: int | None) -> tuple[str, str]:
    """La methode et le chemin de l'endpoint pour un verbe."""
    if verb not in ENDPOINTS:
        raise ValueError("verbe inconnu : {}".format(verb))
    method, template = ENDPOINTS[verb]
    if "{number}" in template:
        if number is None:
            raise ValueError("le verbe {} exige un numero".format(verb))
        path = template.format(repo=repo, number=number)
    else:
        path = template.format(repo=repo)
    return method, path


def check_published_body(published: str, sent: str = "") -> list[str]:
    """Les predicats de la garde post-POST, sur le corps **publie**.

    1. divergence (predicat principal) : le corps publie differe du corps
       **envoye** (`sent`) -- le piege `-f body=@fichier` a tire, ou l'API
       a tronque ;
    2. longueur : un corps publie de moins de `MIN_PUBLISHED_LEN`
       caracteres, signalee **seulement** quand les deux diffèrent : un
       corps court publie a l'identique est un corps legitime ;
    3. structure : le corps parse en objet JSON portant une cle `body`
       (le payload complet passe comme corps, #17326).

    `sent` vide = le corps envoye n'est pas connu (appel direct) : la
    divergence est alors invérifiable et seule la longueur peut l'etre.
    """
    failures: list[str] = []
    texte = published or ""
    attendu = sent or ""
    identique = bool(attendu) and texte.strip() == attendu.strip()
    if attendu and not identique:
        failures.append(
            "divergence : le corps publie ({} caracteres) differe du corps "
            "envoye ({} caracteres) -- le piege `-f body=@fichier` a "
            "probablement tire".format(len(texte), len(attendu))
        )
    if not identique and len(texte) < MIN_PUBLISHED_LEN:
        failures.append(
            "longueur : corps publie de {} caracteres (< {}) -- le piege "
            "`-f body=@fichier` a probablement tire".format(
                len(texte), MIN_PUBLISHED_LEN
            )
        )
    try:
        payload = json.loads(texte)
    except (json.JSONDecodeError, ValueError):
        payload = None
    if isinstance(payload, dict) and isinstance(payload.get("body"), str):
        failures.append(
            "structure : le corps publie est un objet JSON portant une cle "
            "`body` -- le payload complet a ete passe comme corps (PAYLOAD-TRAP)"
        )
    return failures


def _gh_api(method: str, path: str, payload: dict, token: str) -> dict:
    """L'appel REST, avec le payload dans un fichier `--input`."""
    with tempfile.NamedTemporaryFile(
        "w", suffix=".json", encoding="utf-8", delete=False
    ) as handle:
        json.dump(payload, handle, ensure_ascii=False)
        payload_path = handle.name
    try:
        env = post_dossier.write_env(token)
        proc = subprocess.run(
            ["gh", "api", path, "--method", method, "--input", payload_path],
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            env=env,
        )
    finally:
        try:
            os.unlink(payload_path)
        except OSError:
            pass
    if proc.returncode != 0:
        raise RuntimeError(proc.stderr.strip() or "gh api a echoue")
    try:
        data = json.loads(proc.stdout or "{}")
    except json.JSONDecodeError:
        data = {}
    return data if isinstance(data, dict) else {}


def run(args: argparse.Namespace) -> tuple[int, dict]:
    """Execute le geste et rend (code de sortie, rapport)."""
    body_path = Path(args.body_file)
    try:
        body = body_path.read_text(encoding="utf-8")
    except OSError as exc:
        return EXIT_USAGE, {"error": "corps illisible : {}".format(exc)}
    if not body.strip():
        return EXIT_USAGE, {"error": "corps vide : {}".format(body_path)}

    method, path = endpoint_for(args.verb, args.repo, args.number)
    payload = build_payload(args, body)
    token = resolve_token(args.token_source, args.app_id, args.app_key_path)

    data = _gh_api(method, path, payload, token)
    published = data.get("body")
    if not isinstance(published, str):
        # Une creation de PR ou une edition renvoie l'objet ; le corps
        # publie est alors son champ `body`.
        published = body
    failures = check_published_body(published, body)
    report = {
        "id": data.get("id"),
        "url": data.get("html_url") or data.get("url") or "",
        "length": len(published),
        "endpoint": "{} {}".format(method, path),
        "guards": failures,
    }
    return (EXIT_GUARD if failures else EXIT_OK), report


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Ecriture GitHub REST avec la garde post-POST du depot."
    )
    parser.add_argument(
        "verb",
        choices=sorted(ENDPOINTS),
        help="le geste a poser",
    )
    parser.add_argument("--repo", required=True, help="repo `owner/name`")
    parser.add_argument("--number", type=int, help="issue ou PR visee")
    parser.add_argument(
        "--body-file",
        required=True,
        help="fichier du corps ; il est lu puis passe par `--input`",
    )
    parser.add_argument("--title", default="", help="titre (pr-create)")
    parser.add_argument("--head", default="", help="branche (pr-create)")
    parser.add_argument("--base", default="", help="base (pr-create)")
    parser.add_argument(
        "--draft", action="store_true", help="PR en brouillon (pr-create)"
    )
    parser.add_argument(
        "--token-source",
        choices=("user", "env", "app"),
        default="user",
        help="origine du jeton : `user` (jsboige), `env` (jeton App exporte), "
        "`app` (forge a la demande)",
    )
    parser.add_argument("--app-id", default="", help="identifiant de l'App")
    parser.add_argument(
        "--app-key-path", default="", help="chemin de la cle privee de l'App"
    )
    return parser


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    try:
        code, report = run(args)
    except (RuntimeError, ValueError) as exc:
        print(json.dumps({"error": str(exc)}, ensure_ascii=False))
        return EXIT_USAGE
    print(json.dumps(report, ensure_ascii=False))
    return code


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
