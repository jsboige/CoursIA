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

**Ecritures concurrentes** (reserve ai-01, review 5752268155, 2026-11-03) : les
six workflows ont chacun leur propre groupe ``concurrency``, donc ils tournent
**en parallele** sur un meme ``synchronize``. Une lecture-modification-ecriture
sans verrou produit deux defauts :

1. deux runs lisent l'absence de commentaire et font chacun un POST -> deux
   commentaires collants, dont un garde une section perimee ;
2. deux runs lisent le meme corps et font chacun un PATCH -> le dernier ecrit,
   et la section de l'autre **disparait** jusqu'au run suivant de cet organe —
   un avertissement qui n'est pas un succes pourrait ne jamais s'afficher.

Le contrat tient donc par trois mecaniques, sans verrou externe :

* **verifier apres ecriture** : relire et controler que l'etat attendu est
  constate ; sinon **reessayer** (au plus ``MAX_ATTEMPTS`` fois, avec un
  delai aleatoire), puis echouer franchement (``::warning::``) ;
* **reparer les doublons** : si plusieurs commentaires du bot portent le
  marqueur, les sections sont fusionnees dans l'**id max** et les autres sont
  reecrits en une ligne de **renvoi** (rien n'est supprime) ;
* le **succes** d'un organe ne parle toujours pas : le retrait de section suit
  la meme lecture-modification-ecriture verifiee.

Les appels ``gh`` passent par un ``runner`` injectable (pattern
``guard_comment_upsert``) pour que les tests rejouent le corpus reel sans
reseau.
"""
from __future__ import annotations

import argparse
import json
import os
import random
import re
import sys
from typing import Callable, Optional

# Meme contrainte que ``guard_comment_upsert.GUARD_BOT_LOGINS`` : les seuls
# logins editables sont ceux du bot du depot. Un tiers peut porter un login
# qui COMMENCE par ``github-actions`` (review ai-01 #15374) : appartenance
# exacte, pas prefixe.
GUARD_BOT_LOGINS = frozenset({"github-actions", "github-actions[bot]"})

# Le marqueur du commentaire unique. Un PR porte au plus UN commentaire qui
# le contient : c'est ce qui rend le regroupement verifiable de l'exterieur.
MARKER = "<!-- coursia:advisory-sticky -->"

#: Marqueur du commentaire **renvoi** : un doublon fusionne qui ne porte plus
#: de section et ne se presente plus comme collant (le marqueur principal lui
#: est retire), mais qui n'est **pas supprime** — son contenu a ete porte par
#: le commentaire canonique.
FORWARD_MARKER = "<!-- coursia:advisory-sticky:forwarded -->"

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

#: Nombre maximal de tours lecture-modification-ecriture-verification.
MAX_ATTEMPTS = 3

#: Fourchette du delai aleatoire entre deux tentatives (secondes). Le jitter
#: est ce qui evite que deux workflows qui se sont percutes rejouent en phase.
RETRY_JITTER = (0.4, 1.6)


def _default_runner(cmd, **kwargs):  # pragma: no cover - trivial default
    import subprocess
    return subprocess.run(cmd, **kwargs)


def _sleep(seconds):  # pragma: no cover - trivial default
    import time
    time.sleep(seconds)


def _jitter_delay() -> float:
    return random.uniform(*RETRY_JITTER)


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


def forward_body(canonical_id: int) -> str:
    r"""Corps de renvoi d'un doublon fusionne.

    Le marqueur principal est **retire** : ce commentaire ne se presente plus
    comme un collant (le PR n'en porte plus qu'un), mais il **n'est pas
    supprime** et son contenu a ete porte par le commentaire canonique.
    """
    return (
        f"{FORWARD_MARKER}\n\n"
        f"*Ce commentaire a ete fusionne dans le commentaire collant "
        f"canonique (id {canonical_id}) : ses sections y sont integrees. "
        f"Rien n'est efface.*\n"
    )


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


def _is_bot(row: dict) -> bool:
    login = ((row.get("user") or {}).get("login") or "")
    return login in GUARD_BOT_LOGINS


def sticky_comments(comments: list) -> list:
    r"""Commentaires DU BOT portant le marqueur collant, tries par id."""
    out = []
    for row in comments or []:
        body = row.get("body") or ""
        cid = row.get("id")
        if MARKER in body and _is_bot(row) and isinstance(cid, int):
            out.append(row)
    return sorted(out, key=lambda r: r["id"])


def find_sticky_id(comments: list, marker: str = MARKER) -> Optional[int]:
    r"""Dernier commentaire DU BOT portant le marqueur (id max).

    Le filtre d'auteur n'est pas decoratif : un commentaire humain peut
    citer le marqueur verbatim ; l'editer serait falsifier une prise de
    parole.
    """
    best: Optional[int] = None
    for c in comments or []:
        body = c.get("body") or ""
        if marker in body and _is_bot(c):
            cid = c.get("id")
            if isinstance(cid, int) and (best is None or cid > best):
                best = cid
    return best


def _body_of(comments: list, cid: Optional[int]) -> str:
    for c in comments or []:
        if c.get("id") == cid:
            return c.get("body") or ""
    return ""


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


# --------------------------------------------------------------------------
# Concurrence : reparation des doublons, verification apres ecriture
# --------------------------------------------------------------------------

def merge_duplicates(pr: int, repo: str = DEFAULT_REPO,
                     runner: Optional[Callable] = None,
                     timeout: int = DEFAULT_TIMEOUT) -> dict:
    r"""Fusionne les commentaires collants en doublon dans l'**id max**.

    Deux workflows en parallele peuvent chacun creer un commentaire : le PR
    en porte alors deux, dont un garde une section perimee. Ici, toutes les
    sections sont reunies dans le commentaire d'**id max** (canonique), et les
    autres sont reecrits en une ligne de **renvoi** — **rien n'est supprime**,
    et le PR n'en porte plus qu'un collant.
    """
    if runner is None:  # pragma: no cover - trivial default
        runner = _default_runner
    comments = list_comments(pr, repo, runner, timeout)
    stickies = sticky_comments(comments)
    if len(stickies) <= 1:
        return {"action": "noop",
                "comment_id": stickies[0]["id"] if stickies else None,
                "merged": []}
    canonical = stickies[-1]
    merged = parse_sections(canonical.get("body") or "")
    for row in stickies:
        if row["id"] == canonical["id"]:
            continue
        for name, text in parse_sections(row.get("body") or "").items():
            # Le canonique gagne en cas de conflit : son contenu est le plus
            # recent ; le doublon n'apporte que ce qui manque.
            merged.setdefault(name, text)
    _patch_comment(canonical["id"], render(merged), repo, runner, timeout)
    others = []
    for row in stickies:
        if row["id"] == canonical["id"]:
            continue
        _patch_comment(row["id"], forward_body(canonical["id"]), repo, runner,
                       timeout)
        others.append(row["id"])
    return {"action": "merged", "comment_id": canonical["id"], "merged": others}


def _verify_upsert(organ: str, body: str, pr: int, repo: str,
                    runner: Callable, timeout: int) -> bool:
    r"""L'ecriture est-elle **constatee** dans l'etat attendu ?

    On relit le commentaire canonique : la section doit y porter exactement
    le corps ecrit. Une section **absente** apres un POST concurrent est un
    echec d'ecriture, pas un succes.
    """
    want = (body or "").strip()
    comments = list_comments(pr, repo, runner, timeout)
    cid = find_sticky_id(comments)
    if cid is None:
        return False
    sections = parse_sections(_body_of(comments, cid))
    if not want:
        return organ not in sections
    return sections.get(organ, "") == want


def _verify_clear(organ: str, pr: int, repo: str, runner: Callable,
                  timeout: int) -> bool:
    r"""Le retrait est-il constate (la section a disparu partout) ?"""
    comments = list_comments(pr, repo, runner, timeout)
    for row in sticky_comments(comments):
        if organ in parse_sections(row.get("body") or ""):
            return False
    return True


# --------------------------------------------------------------------------
# Operations
# --------------------------------------------------------------------------

def _upsert_attempt(organ: str, body: str, pr: int, repo: str, runner: Callable,
                    timeout: int) -> dict:
    comments = list_comments(pr, repo, runner, timeout)
    cid = find_sticky_id(comments)
    existing_body = _body_of(comments, cid)
    sections = parse_sections(existing_body)
    sections[organ] = (body or "").strip()
    new_body = render(sections)
    if cid is not None:
        if new_body == existing_body:
            return {"action": "unchanged", "comment_id": cid}
        return _patch_comment(cid, new_body, repo, runner, timeout)
    return _create_comment(pr, new_body, repo, runner, timeout)


def _clear_attempt(organ: str, pr: int, repo: str, runner: Callable,
                   timeout: int) -> dict:
    comments = list_comments(pr, repo, runner, timeout)
    cid = find_sticky_id(comments)
    if cid is None:
        # Rien a retirer : l'organe n'a jamais eu d'avertissement -> le
        # succes ne parle pas. Aucun commentaire n'est cree.
        return {"action": "silent", "comment_id": None}
    existing_body = _body_of(comments, cid)
    sections = parse_sections(existing_body)
    if organ not in sections:
        return {"action": "unchanged", "comment_id": cid}
    del sections[organ]
    return _patch_comment(cid, render(sections), repo, runner, timeout)


def upsert_section(organ: str, body: str, pr: int, repo: str = DEFAULT_REPO,
                   runner: Optional[Callable] = None,
                   timeout: int = DEFAULT_TIMEOUT,
                   attempts: int = MAX_ATTEMPTS,
                   sleep: Optional[Callable] = None) -> dict:
    r"""Ecrit (ou reecrit) la section d'un organe dans le commentaire unique.

    L'ecriture est **verifiee** : apres chaque tour, l'etat est relu ; s'il
    n'est pas celui attendu (section ecrasee par un ecrivain concurrent,
    doublon cree en parallele), on **retente** avec un delai aleatoire, au
    plus ``attempts`` fois. A defaut de verification, l'echec est remonte :
    un succes ne se rend pas sur une ecriture non constatee.
    """
    _validate_organ(organ)
    if runner is None:  # pragma: no cover - trivial default
        runner = _default_runner
    if sleep is None:
        sleep = _sleep
    for attempt in range(1, max(1, attempts) + 1):
        out = _upsert_attempt(organ, body, pr, repo, runner, timeout)
        merged = merge_duplicates(pr, repo, runner, timeout)
        if merged.get("action") == "merged":
            out = dict(out)
            out["merged"] = merged.get("merged", [])
        if _verify_upsert(organ, body, pr, repo, runner, timeout):
            out["verified"] = True
            return out
        if attempt < attempts:
            sleep(_jitter_delay())
    raise RuntimeError(
        f"section {organ!r} non constatee apres {attempts} tentative(s) "
        f"(ecriture concurrente ?) -- succes refuse")


def clear_section(organ: str, pr: int, repo: str = DEFAULT_REPO,
                  runner: Optional[Callable] = None,
                  timeout: int = DEFAULT_TIMEOUT,
                  attempts: int = MAX_ATTEMPTS,
                  sleep: Optional[Callable] = None) -> dict:
    r"""Retire la section d'un organe qui redevient vert.

    Le commentaire n'est **jamais supprime** : il est reecrit en place avec
    l'etat « plus aucun avertissement consultatif » (#15372 : pas
    d'effacement d'historique). Comme l'ecriture, le retrait est **verifie**
    (la section doit avoir disparu) et rejoue en cas de conflit concurrent.
    """
    _validate_organ(organ)
    if runner is None:  # pragma: no cover - trivial default
        runner = _default_runner
    if sleep is None:
        sleep = _sleep
    for attempt in range(1, max(1, attempts) + 1):
        out = _clear_attempt(organ, pr, repo, runner, timeout)
        merged = merge_duplicates(pr, repo, runner, timeout)
        if merged.get("action") == "merged":
            out = dict(out)
            out["merged"] = merged.get("merged", [])
        if _verify_clear(organ, pr, repo, runner, timeout):
            out["verified"] = True
            return out
        if attempt < attempts:
            sleep(_jitter_delay())
    raise RuntimeError(
        f"retrait de la section {organ!r} non constate apres {attempts} "
        f"tentative(s) (ecriture concurrente ?) -- succes refuse")


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
