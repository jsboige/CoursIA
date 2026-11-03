#!/usr/bin/env python3
r"""UN SEUL commentaire collant par PR pour les avertissements consultatifs (#15511).

Le 2026-11-03, le bot ``github-actions`` ecrivait ~5,5 commentaires par PR et
~60 % d'entre eux ne portaient qu'un succes deja dit par le check-run
(« Notebook PR Validation: PASS », « No organ-duplication », « Golden-Set
Execution ✅ ... »). Chaque relecteur les relit a chaque tour : un signal que
le check-run porte deja ne doit pas avoir de **canal** propre.

Ce module remplace le create-only par un **upsert de section** :

* **un** commentaire par PR, identifie par le marqueur HTML
  ``<!-- coursia:advisory-sticky -->`` ;
* **une section par organe**, encadree par ``<!-- organ:<nom> -->`` ...
  ``<!-- /organ:<nom> -->`` ;
* **le succes ne parle pas** : l'organe qui redevient vert **retire sa
  section** ; si aucun avertissement ne reste, le commentaire est **edite en
  place** en un etat « plus aucun avertissement consultatif » — il n'est
  jamais supprime (l'historique reste, #15372) ;
* **jamais de signal bloquant ne change de canal** : ce module ne porte que
  des advisories. Un organe bloquant garde son check-run rouge et son propre
  commentaire ; voir le garde-fou de test
  ``scripts/ci/tests/test_advisory_sticky.py``.

Les appels ``gh`` passent par un ``runner`` injectable (pattern
``guard_comment_upsert``) pour que les tests rejouent le corpus reel sans
reseau.
"""
from __future__ import annotations

import argparse
import json
import os
import re
import sys
from datetime import datetime, timezone
from typing import Callable, Optional

# Meme contrainte que ``guard_comment_upsert.GUARD_BOT_LOGINS`` : les seuls
# logins editables sont ceux du bot du depot. Un tiers peut porter un login
# qui COMMENCE par ``github-actions`` (review ai-01 #15374) : appartenance
# exacte, pas prefixe.
GUARD_BOT_LOGINS = frozenset({"github-actions", "github-actions[bot]"})

# Le marqueur du commentaire unique. Un PR porte au plus UN commentaire qui
# le contient : c'est ce qui rend le regroupement verifiable de l'exterieur.
MARKER = "<!-- coursia:advisory-sticky -->"

# Encadrement d'une section d'organe.
_SECTION_RE = re.compile(
    r"[ \t]*<!--[ \t]*organ:(?P<name>[A-Za-z0-9._-]+)[ \t]*-->"
    r"(?P<body>.*?)"
    r"[ \t]*<!--[ \t]*/[ \t]*organ:(?P=name)[ \t]*-->[ \t]*\n?",
    re.S,
)

TITLE = "Avertissements consultatifs"
EMPTY_NOTE = (
    "*Aucun avertissement consultatif en cours sur cette PR.* "
    "Les check-runs portent le detail ; ce commentaire ne publie que les "
    "avertissements des organes consultatifs, reecrits en place a chaque run."
)

DEFAULT_TIMEOUT = 15
DEFAULT_REPO = "jsboige/CoursIA"


def _default_runner(cmd, **kwargs):  # pragma: no cover - trivial default
    import subprocess
    return subprocess.run(cmd, **kwargs)


# --------------------------------------------------------------------------
# Corps du commentaire
# --------------------------------------------------------------------------

def render(sections: dict) -> str:
    r"""Compose le corps du commentaire collant a partir des sections.

    Le corps est **deterministe** : meme etat -> meme corps, donc un run
    repete ne rechauffe pas le commentaire (pas de bruit d'edition).
    """
    parts = [MARKER, f"## {TITLE}", ""]
    if not sections:
        parts.append(EMPTY_NOTE)
        parts.append("")
        return "\n".join(parts)
    for name in sorted(sections):
        body = (sections[name] or "").strip()
        if not body:
            continue
        parts.append(f"<!-- organ:{name} -->")
        parts.append(body)
        parts.append(f"<!-- /organ:{name} -->")
        parts.append("")
    parts.append(
        "_Une section par organe ; ce commentaire est reecrit en place, il "
        "n'est pas empile._"
    )
    parts.append("")
    return "\n".join(parts)


def parse_sections(body: str) -> dict:
    r"""Sections organe -> corps, dans un corps de commentaire donne."""
    out = {}
    for m in _SECTION_RE.finditer(body or ""):
        out[m.group("name")] = m.group("body").strip("\n").strip()
    return out


def strip_sections(body: str) -> str:
    r"""Corps sans aucune section (en-tete conserve)."""
    return _SECTION_RE.sub("", body or "")


# --------------------------------------------------------------------------
# API GitHub
# --------------------------------------------------------------------------

def list_comments(pr: int, repo: str, runner: Optional[Callable] = None,
                   timeout: int = DEFAULT_TIMEOUT) -> list:
    r"""Commentaires de la PR via l'API REST (id NUMERIQUE).

    L'``id`` de ``gh pr view --json comments`` est le node id GraphQL, qui
    n'est pas utilisable par le PATCH REST : on va a la source.
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


def find_sticky_id(comments: list, marker: str = MARKER) -> Optional[int]:
    r"""Dernier commentaire DU BOT portant le marqueur (id max).

    Le filtre d'auteur n'est pas decoratif : un commentaire humain peut
    citer le marqueur verbatim ; l'editer serait falsifier une prise de
    parole.
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


def _patch_comment(comment_id: int, body: str, repo: str, runner: Callable,
                    timeout: int) -> dict:
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


def _create_comment(pr: int, body: str, repo: str, runner: Callable,
                    timeout: int) -> dict:
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
    if cid is None:
        # #22758 transpose : un succes ne se rend pas sur l'absence
        # d'erreur, il se rend sur la constatation de l'ecriture. Sans
        # identifiant, l'ecriture n'est ni adressable ni verifiable.
        raise RuntimeError(
            "gh api POST comment: reponse sans identifiant de commentaire "
            f"({(proc.stdout or '').strip()[:200] or '<vide>'}) -- ecriture "
            "non constatee, succes refuse")
    return {"action": "created", "comment_id": cid}


def upsert_section(organ: str, body: str, pr: int, repo: str = DEFAULT_REPO,
                   runner: Optional[Callable] = None,
                   timeout: int = DEFAULT_TIMEOUT) -> dict:
    r"""Ecrit (ou reecrit) la section d'un organe dans le commentaire unique."""
    _validate_organ(organ)
    if runner is None:  # pragma: no cover - trivial default
        runner = _default_runner
    comments = list_comments(pr, repo, runner, timeout)
    cid = find_sticky_id(comments)
    existing_body = ""
    for c in comments:
        if c.get("id") == cid:
            existing_body = c.get("body") or ""
            break
    sections = parse_sections(existing_body)
    sections[organ] = (body or "").strip()
    new_body = render(sections)
    if cid is not None:
        if new_body == existing_body:
            return {"action": "unchanged", "comment_id": cid}
        return _patch_comment(cid, new_body, repo, runner, timeout)
    return _create_comment(pr, new_body, repo, runner, timeout)


def clear_section(organ: str, pr: int, repo: str = DEFAULT_REPO,
                  runner: Optional[Callable] = None,
                  timeout: int = DEFAULT_TIMEOUT) -> dict:
    r"""Retire la section d'un organe qui redevient vert.

    Le commentaire n'est **jamais supprime** : il est reecrit en place avec
    l'etat « plus aucun avertissement consultatif » (#15372 : pas
    d'effacement d'historique).
    """
    _validate_organ(organ)
    if runner is None:  # pragma: no cover - trivial default
        runner = _default_runner
    comments = list_comments(pr, repo, runner, timeout)
    cid = find_sticky_id(comments)
    if cid is None:
        # Rien a retirer : l'organe n'a jamais eu d'avertissement -> le
        # succes ne parle pas. Aucun commentaire n'est cree.
        return {"action": "silent", "comment_id": None}
    existing_body = ""
    for c in comments:
        if c.get("id") == cid:
            existing_body = c.get("body") or ""
            break
    sections = parse_sections(existing_body)
    if organ not in sections:
        return {"action": "unchanged", "comment_id": cid}
    del sections[organ]
    new_body = render(sections)
    return _patch_comment(cid, new_body, repo, runner, timeout)


def _validate_organ(organ: str) -> None:
    if not organ or not re.fullmatch(r"[A-Za-z0-9._-]+", organ or ""):
        raise ValueError(
            f"nom d'organe invalide: {organ!r} (attendu: [A-Za-z0-9._-]+)")


# --------------------------------------------------------------------------
# CLI
# --------------------------------------------------------------------------

def main(argv: Optional[list] = None) -> int:
    parser = argparse.ArgumentParser(
        description="Un seul commentaire collant par PR pour les advisories.")
    parser.add_argument("--pr", type=int, required=True,
                        help="numero de la Pull Request")
    parser.add_argument("--organ", required=True,
                        help="nom de l'organe (section)")
    parser.add_argument("--body-file",
                        help="fichier portant le corps de la section")
    parser.add_argument("--clear", action="store_true",
                        help="retire la section (organe redevenu vert)")
    parser.add_argument("--repo", default=os.environ.get(
        "GITHUB_REPOSITORY", DEFAULT_REPO))
    args = parser.parse_args(argv)

    if args.clear and args.body_file:
        parser.error("--clear et --body-file sont exclusifs")
    if not args.clear and not args.body_file:
        parser.error("--body-file ou --clear est obligatoire")

    try:
        if args.clear:
            out = clear_section(args.organ, args.pr, args.repo)
        else:
            with open(args.body_file, "r", encoding="utf-8") as fh:
                body = fh.read()
            out = upsert_section(args.organ, body, args.pr, args.repo)
    except Exception as exc:  # noqa: BLE001 - l'echec est remonte tel quel
        print(f"advisory_sticky: {exc}", file=sys.stderr)
        return 1
    print(json.dumps(out, ensure_ascii=False))
    return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
