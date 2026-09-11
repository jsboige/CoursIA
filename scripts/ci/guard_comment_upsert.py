#!/usr/bin/env python3
r"""Upsert du commentaire d'un garde : PATCH en place, jamais de mur (#15372).

Un garde qui poste un commentaire bloquant a chaque run rouge sans jamais
retirer produit un mur de verdicts perimes : 19 commentaires « bloquant »
mesures sur 4 PRs le 2026-09-09, tous faux a l'instant de la mesure (la
cible ``prev:`` avait merge apres le tir, et seul un nouvel evenement
``pull_request`` reevalue -- il n'y en a plus quand la PR attend).

Ce module remplace le ``gh pr comment`` create-only par un upsert :

* **recherche** du commentaire porte par le marqueur **ET** ecrit par le
  bot du depot (login ``github-actions`` / ``github-actions[bot]``). Le
  filtre d'auteur n'est pas decoratif : sur #15146, 4 commentaires
  HUMAINS portent le marqueur ``<!-- vtr-prev-close-keyword -->``
  verbatim, cites dans des comptes rendus -- une recherche marqueur-seul
  editerait un commentaire humain ;
* **PATCH** en place (``repos/{repo}/issues/comments/{id}``) au lieu
  d'en creer un nouveau ;
* **levee sur run vert** : si un commentaire bloquant existe, il est
  reecrit en etat leve, horodate, nommant les ``prev:`` desormais
  acceptes. Le marqueur reste porte par le corps releve pour que le
  prochain upsert le retrouve.

Jamais de suppression : pas d'effacement d'historique (#15372
acceptance 4).

Les appels ``gh`` passent par un ``runner`` injectable (pattern
``variation_prev_guard.resolve_prev_targets``) pour que les tests
rejouent le corpus reel sans reseau.
"""
from __future__ import annotations

import argparse
import json
import sys
from datetime import datetime, timezone
from typing import Callable, Optional

# Les commentaires postes avec GITHUB_TOKEN ont pour auteur
# ``github-actions[bot]`` ; les runs legacy ``github-actions``. Ce sont les
# DEUX SEULS logins editables -- appartenance exacte, pas un prefix : sur un
# depot public un tiers peut porter ``github-actions-xyz`` (review ai-01
# #15374) et un autre bot (dependabot, etc.) ne doit jamais l'etre non plus.
GUARD_BOT_LOGINS = frozenset({"github-actions", "github-actions[bot]"})

DEFAULT_TIMEOUT = 15


def _default_runner(cmd, **kwargs):  # pragma: no cover - trivial default
    import subprocess
    return subprocess.run(cmd, **kwargs)


def find_guard_comment_id(
    comments: Optional[list],
    marker: str,
) -> Optional[int]:
    r"""Dernier commentaire DU BOT portant ``marker`` dans son corps.

    Le dernier (id REST max) gagne : c'est l'etat courant affiche du
    garde. Retourne ``None`` quand aucun commentaire bot ne porte le
    marqueur -- y compris si des commentaires humains le portent (corpus
    #15146 : 3 ``jsboige`` + 1 ``myia-ai-01`` citaient le verdict
    verbatim ; ils ne doivent jamais etre edites).
    """
    best: Optional[int] = None
    for c in comments or []:
        body = c.get("body") or ""
        login = ((c.get("user") or {}).get("login") or "")
        if marker in body and login in GUARD_BOT_LOGINS:
            cid = c.get("id")
            if isinstance(cid, int) and (best is None or cid > best):
                best = cid
    return best


def list_comments(
    pr: int,
    repo: str,
    runner: Optional[Callable] = None,
    timeout: int = DEFAULT_TIMEOUT,
) -> list:
    r"""Commentaires de la PR via l'API REST (id NUMERIQUE).

    L'``id`` de ``gh pr view --json comments`` est le node id GraphQL
    (``IC_...``), inutilisable par le PATCH REST -- mesure sur #15373 :
    ``IC_kwDO...`` cote GraphQL, ``5600457600`` cote REST. On va donc a
    la source. ``--paginate --slurp`` rend un tableau de pages (un
    element par page) : on aplatit.
    """
    if runner is None:  # pragma: no cover - trivial default
        runner = _default_runner
    proc = runner(
        ["gh", "api", "--paginate", "--slurp",
         f"repos/{repo}/issues/{pr}/comments"],
        capture_output=True, text=True, timeout=timeout,
    )
    if getattr(proc, "returncode", 1) != 0:
        raise RuntimeError(f"gh api comments failed: {proc.stderr.strip()}")
    data = json.loads(proc.stdout)
    if not isinstance(data, list):
        raise RuntimeError(
            f"gh api comments: forme inattendue ({type(data).__name__})")
    return [row for page in data for row in page]


def _patch_comment(
    comment_id: int,
    body: str,
    repo: str,
    runner: Callable,
    timeout: int,
) -> dict:
    proc = runner(
        ["gh", "api", "--method", "PATCH",
         f"repos/{repo}/issues/comments/{comment_id}",
         "-f", f"body={body}"],
        capture_output=True, text=True, timeout=timeout,
    )
    if getattr(proc, "returncode", 1) != 0:
        raise RuntimeError(
            f"gh api PATCH comment {comment_id} failed: {proc.stderr.strip()}")
    return {"action": "patched", "comment_id": comment_id}


def _create_comment(
    pr: int,
    body: str,
    repo: str,
    runner: Callable,
    timeout: int,
) -> dict:
    proc = runner(
        ["gh", "api", "--method", "POST",
         f"repos/{repo}/issues/{pr}/comments",
         "-f", f"body={body}"],
        capture_output=True, text=True, timeout=timeout,
    )
    if getattr(proc, "returncode", 1) != 0:
        raise RuntimeError(f"gh api POST comment failed: {proc.stderr.strip()}")
    try:
        cid = json.loads(proc.stdout).get("id")
    except (json.JSONDecodeError, AttributeError):
        cid = None
    return {"action": "created", "comment_id": cid}


def upsert_comment(
    pr: int,
    marker: str,
    body: str,
    repo: str,
    runner: Optional[Callable] = None,
    timeout: int = DEFAULT_TIMEOUT,
) -> dict:
    r"""Edite le commentaire bot existant, sinon en cree un premier."""
    if runner is None:  # pragma: no cover - trivial default
        runner = _default_runner
    existing = find_guard_comment_id(list_comments(pr, repo, runner, timeout),
                                     marker)
    if existing is not None:
        return _patch_comment(existing, body, repo, runner, timeout)
    return _create_comment(pr, body, repo, runner, timeout)


def build_lifted_body(marker: str, title: str, note: str,
                      ts: Optional[str] = None) -> str:
    r"""Corps releve : marqueur CONSERVE pour le prochain upsert."""
    if ts is None:
        ts = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    return (
        f"{marker}\n"
        f"**{title} — LEVÉ ({ts}).**\n\n"
        f"{note}\n\n"
        "Run vert du garde : ce commentaire bloquant est obsolète. Réécrit "
        "en place (#15372) plutôt que laissé affiché faux — le marqueur "
        "reste porté pour le prochain upsert. Historique : runs "
        "`Always-on guards` de la PR."
    )


def lift_comment(
    pr: int,
    marker: str,
    note: str,
    repo: str,
    title: str = "`prev:` genre mot-clé fermant (#10093)",
    runner: Optional[Callable] = None,
    timeout: int = DEFAULT_TIMEOUT,
) -> dict:
    r"""Run vert : releve le commentaire bloquant precedent s'il existe.

    No-op silencieux quand aucun commentaire bot ne porte le marqueur --
    un run vert sur une PR jamais bloquee ne doit pas fabriquer du bruit.
    """
    if runner is None:  # pragma: no cover - trivial default
        runner = _default_runner
    existing = find_guard_comment_id(list_comments(pr, repo, runner, timeout),
                                     marker)
    if existing is None:
        return {"action": "noop", "comment_id": None}
    body = build_lifted_body(marker, title, note)
    return _patch_comment(existing, body, repo, runner, timeout)


def _resolve_repo(explicit: Optional[str]) -> str:
    import os
    if explicit:
        return explicit
    env = os.environ.get("GITHUB_REPOSITORY")
    if env:
        return env
    proc = _default_runner(
        ["gh", "repo", "view", "--json", "nameWithOwner",
         "--jq", ".nameWithOwner"],
        capture_output=True, text=True, timeout=DEFAULT_TIMEOUT,
    )
    if getattr(proc, "returncode", 1) != 0:
        raise RuntimeError(
            "repo introuvable : --repo absent, GITHUB_REPOSITORY absent, "
            f"gh repo view a échoué: {proc.stderr.strip()}")
    return proc.stdout.strip()


def main(argv: Optional[list] = None,
         runner: Optional[Callable] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--pr", type=int, required=True,
                        help="Numéro de la PR porteuse du commentaire.")
    parser.add_argument("--marker", required=True,
                        help="Marqueur HTML identifiant le commentaire.")
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--body-file",
                      help="Mode bloquant : corps complet du commentaire.")
    mode.add_argument("--lift", action="store_true",
                      help="Mode levée : réécrire le bloquant en LEVÉ.")
    parser.add_argument("--note", default="",
                        help="Mode levée : note horodatée (prev acceptés...).")
    parser.add_argument("--repo", default=None,
                        help="owner/name. Défaut : GITHUB_REPOSITORY.")
    args = parser.parse_args(argv)

    repo = _resolve_repo(args.repo)
    if args.lift:
        result = lift_comment(args.pr, args.marker, args.note, repo,
                              runner=runner)
    else:
        with open(args.body_file, encoding="utf-8") as fh:
            body = fh.read()
        result = upsert_comment(args.pr, args.marker, body, repo,
                                runner=runner)
    print(json.dumps(result))
    return 0


if __name__ == "__main__":
    sys.exit(main())
