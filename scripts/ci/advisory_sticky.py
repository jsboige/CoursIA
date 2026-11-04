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

Le contrat tient donc par quatre mecaniques :

* **un verrou d'ecriture** : l'ecriture se fait sous un verrou pose dans le
  corps du commentaire collant (une ligne HTML, invisible au rendu). Un
  ecrivain concurrent trouve le verrou, il **attend** au lieu d'ecraser ; le
  verrou a une duree de vie, donc un ecrivain mort ne bloque pas les autres
  indefiniment ;
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
import time
import uuid
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
#: est ce qui evite que deux workflows qui se sont percoutes rejouent en phase.
RETRY_JITTER = (0.4, 1.6)

# --------------------------------------------------------------------------
# Verrou d'ecriture -- une ETIQUETTE du PR
# --------------------------------------------------------------------------
# Le verrou porte par le **corps** du commentaire ne fermait pas la
# fenetre. L'adjoint (`myia-po-2025:CoursIA-2`, contre-exemple du
# 2026-11-04) a montre que lire -> PATCH du corps entier -> relire son
# proprietaire n'est pas une acquisition **atomique** : un ecrivain dont la
# lecture precede la prise de l'autre peut ecraser une section deja
# verifiee, et les deux se croient verifies. Une relecture supplementaire ne
# ferme pas cette classe de course : l'API refuse l'ecriture conditionnelle
# (mesure du 2026-11-04 : `If-Match` -> HTTP 400 **sur le commentaire et sur
#: l'issue**, `If-Unmodified-Since` -> HTTP 400), et l'API des reactions est
#: **idempotente** (mesure du 2026-11-04 : un second POST renvoie la
#: reaction existante en 200, pas 422) -- elle ne peut donc pas servir de
#: test-and-set. Aucun primitive de comparaison-et-echange n'existe sur ce
#: PR : le verrou doit etre une **serialisation reelle**.
#:
#: Le verrou est desormais **une etiquette du PR** :
#:
#: * l'ajout d'une etiquette est un **ajout a un ensemble**, atomique cote
#:   serveur, la ou un PATCH de corps ne l'est pas ; l'ensemble ne
#:   s'ecrase pas -- deux ecrivains y ajoutent chacun la leur ;
#: * l'arbitrage se lit dans l'ensemble et se fait sur l'**identifiant
#:   serveur** de l'etiquette : cet identifiant est attribue par creation
#:   (mesure du 2026-11-04 : cinq creations successives ont rendu cinq
#:   identifiants strictement croissants), donc les deux concurrents lisent
#:   le meme identifiant et elisent **le meme** gagnant -- l'horloge du
#:   client n'entre pas dans l'arbitrage, et deux machines dont les
#:   horloges different ne peuvent pas elire deux gagnants differents ;
#: * la peremption se mesure sur une **duree d'observation locale**
#:   (horloge monotone de la machine qui observe), jamais par comparaison
#:   de deux horloges : une etiquette vue vivante pendant
#:   :data:`LOCK_TTL_SECONDS` consecutivement est presumee perimee ;
#: * la liberation et le nettoyage passent par
#:   `DELETE /repos/{owner}/{repo}/labels/{nom}` : cet appel **detache**
#:   l'etiquette du PR **et supprime la definition** au niveau du depot
#:   (mesure du 2026-11-04 : HTTP 204, definition absente de la liste du
#:   depot, etiquette absente des etiquettes du PR). Deposer le seul lien
#:   (`DELETE /issues/{n}/labels/{nom}`) laisserait la definition deriver
#:   au depot -- c'etait la fuite de la premiere version.
#:
#: **Ce que ce verrou ne garantit pas.** Il serialise les ecrivains qui
#: *respectent* le protocole : la garantie porte sur les ecrivains de ce
#: module, pas sur un ecrivain tiers qui PATCHerait le corps sans passer
#: par le verrou. Et la peremption est un **bail** : un ecrivain vivant
#: mais lent au-dela du TTL peut voir son verrou vole. Le TTL (45 s) est
#: tres superieur a la duree de la section critique (lecture, PATCH,
#: verification : quelques secondes).
#:
#: **Effet de bord mesure.** Poser une etiquette declenche l'evenement
#: `labeled` : `notebook-exec-sequence-ratchet.yml` est le **seul**
#: workflow du depot qui **declare** ce declencheur (mesure du
#: 2026-11-04, scan des blocs `on:` de tous les workflows) ; son filtre
#: `paths: **.ipynb` le restreint aux PR de carnets, et sur les evenements
#: d'etiquette dates (des PRs `.ipynb`) **aucun run n'a suivi** (mesure
#: Hermes, 2026-11-04T06:43Z) -- le filtre `paths` parait neutraliser
#: l'evenement en pratique. La formulation « aucun workflow ne se declenche
#: sur `labeled` » est donc **fausse** et retiree : un workflow declare
#: ce declencheur. Le ratchet ne publie ni collant ni etiquette : **aucune
#: boucle** n'est possible meme s'il partait. Aucun workflow ne declare
#: `unlabeled`.
#:
#: Les workflows qui publient ont deja `issues: write` : c'est ce droit qui
#: autorise la suppression de la definition au niveau du depot. Aucun droit
#: nouveau, aucune surface d'ecriture elargie.
#:
#: Un ecrivain mort laisse son etiquette : au-dela du TTL elle est
#: **perimee**, le suivant la retire (nettoyage) et prend la main.
LOCK_LABEL_PREFIX = "coursia-advisory-lock-"

#: Duree de vie d'un verrou (secondes). Au-dela, le verrou est considere
#: perime : l'ecrivain qui le detient est presume mort.
LOCK_TTL_SECONDS = 45.0

#: Duree maximale d'attente d'un verrou (secondes). Au-dela, l'ecriture
#: est **refusee** : on ne certifie pas une ecriture sous contention.
LOCK_WAIT_SECONDS = 60.0


def _default_runner(cmd, **kwargs):  # pragma: no cover - trivial default
    import subprocess
    return subprocess.run(cmd, **kwargs)


def _sleep(seconds):  # pragma: no cover - trivial default
    import time
    time.sleep(seconds)


def _jitter_delay() -> float:
    return random.uniform(*RETRY_JITTER)


#: Delai de stabilisation : le temps laisse a un ecrivain concurrent pour
#: ecrire **entre** notre ecriture et notre relecture de controle. See
#: `upsert_section` pour ce que cette fenetre ferme, et ce qu'elle ne ferme
#: pas.
SETTLE_DELAY = (0.5, 1.5)


def _settle_delay() -> float:
    return random.uniform(*SETTLE_DELAY)


# --------------------------------------------------------------------------
# Verrou d'ecriture -- helpers d'etiquettes
# --------------------------------------------------------------------------

def _lock_label(owner: str) -> str:
    r"""Nom de l'etiquette de verrou.

    Le nom ne porte **plus d'horodatage** : l'ordre d'arbitrage est donne
    par l'identifiant **serveur** de l'etiquette (attribue par creation),
    pas par une horloge de client -- deux machines dont les horloges
    different eligent donc le meme gagnant.
    """
    return f"{LOCK_LABEL_PREFIX}{owner}"


def _is_lock_label(name: str) -> bool:
    r"""`True` si le nom porte le prefixe des verrous d'ecriture."""
    return bool(name) and name.startswith(LOCK_LABEL_PREFIX)


def _sort_key(label_id, name: str):
    r"""Cle d'ordre des verrous : l'identifiant serveur (attribue par
    creation, mesure du 2026-11-04).

    A defaut d'identifiant (reponse degradee), on retombe sur le nom :
    le tri reste alors **deterministe**, donc encore agree par les deux
    concurrents.
    """
    return (label_id if isinstance(label_id, int) else -1, name)


def _rows_from_payload(data) -> list:
    r"""Aplatit la charge utile de `gh api --paginate --slurp`.

    `--slurp` rend une liste de pages ; chaque page est une liste
    d'objets. Un testes qui renvoie directement la liste des objets est
    accepte aussi (la meme fonction sert pour la reponse d'un POST,
    qui n'est pas paginee).
    """
    rows = []
    if not isinstance(data, list):
        return rows
    for page in data:
        if isinstance(page, list):
            rows.extend(page)
        elif isinstance(page, dict):
            rows.append(page)
    return rows


def _labels_state(pr: int, repo: str, runner: Callable, timeout: int) -> dict:
    r"""Etat des etiquettes du PR : ``{nom: identifiant serveur}``.

    Une PR est une issue pour l'API. Les identifiants sont attribues par
    creation : ils fournissent un ordre **serveur**, independant de
    l'horloge des machines.
    """
    proc = runner(
        ["gh", "api", "--paginate", "--slurp",
         f"repos/{repo}/issues/{pr}/labels"],
        capture_output=True, text=True, timeout=timeout,
    )
    if getattr(proc, "returncode", 1) != 0:
        raise RuntimeError(f"gh api labels failed: {proc.stderr.strip()}")
    data = json.loads(proc.stdout)
    if not isinstance(data, list):
        raise RuntimeError(
            f"gh api labels: forme inattendue ({type(data).__name__})")
    state = {}
    for row in _rows_from_payload(data):
        if isinstance(row, dict) and row.get("name"):
            state[row["name"]] = row.get("id")
        elif isinstance(row, str):
            state.setdefault(row, None)
    return state


def _add_label(pr: int, repo: str, runner: Callable, timeout: int,
               name: str) -> dict:
    r"""Ajoute une etiquette au PR -- **ajout a un ensemble**, atomique.

    Renvoie l'etat des etiquettes du PR **apres** l'ajout : la reponse du
    serveur porte la liste complete (mesure du 2026-11-04), ce qui evite
    une lecture supplementaire.
    """
    proc = runner(
        ["gh", "api", "--method", "POST",
         f"repos/{repo}/issues/{pr}/labels",
         "-f", f"labels[]={name}"],
        capture_output=True, text=True, timeout=timeout,
    )
    if getattr(proc, "returncode", 1) != 0:
        raise RuntimeError(
            f"gh api POST label {name!r} failed: {proc.stderr.strip()}")
    try:
        data = json.loads(proc.stdout or "[]")
    except ValueError:
        data = []
    state = {}
    for row in _rows_from_payload(data):
        if isinstance(row, dict) and row.get("name"):
            state[row["name"]] = row.get("id")
        elif isinstance(row, str):
            state.setdefault(row, None)
    return state


def _delete_label(repo: str, runner: Callable, timeout: int,
                  name: str) -> None:
    r"""Supprime l'etiquette **au niveau du depot**.

    `DELETE /repos/{owner}/{repo}/labels/{nom}` **detache** l'etiquette du
    PR **et supprime la definition** au depot (mesure du 2026-11-04 :
    HTTP 204, definition absente de la liste du depot, etiquette absente
    des etiquettes du PR). Deposer le seul lien
    (`DELETE /issues/{n}/labels/{nom}`) ne supprimerait pas la definition :
    elle deriverait au depot, une par prise de verrou.

    Une etiquette deja absente (404) n'est pas une erreur : c'est l'etat
    vise.
    """
    proc = runner(
        ["gh", "api", "--method", "DELETE",
         f"repos/{repo}/labels/{name}"],
        capture_output=True, text=True, timeout=timeout,
    )
    if getattr(proc, "returncode", 1) != 0:
        err = getattr(proc, "stderr", "") or ""
        if "Not Found" in err:
            return
        raise RuntimeError(
            f"gh api DELETE label {name!r} failed: {err.strip()}")


def _owner_id() -> str:
    r"""Identite d'un ecrivain : unique par processus et par tentative."""
    return f"{uuid.uuid4().hex[:8]}{os.getpid() % 1000}"


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

def _acquire_lock(pr: int, repo: str, runner: Callable, timeout: int,
                  owner: str, sleep: Callable,
                  monotonic: Callable = time.monotonic):
    r"""Prend le verrou d'ecriture -- **une etiquette du PR**.

    Le verrou est un **ajout a un ensemble** (les etiquettes du PR) : la
    prise est atomique cote serveur, la ou un PATCH de corps ne l'est pas.
    Un PATCH de corps n'est jamais conditionnel (mesure du 2026-11-04 :
    `If-Match` -> HTTP 400 sur le commentaire et sur l'issue) ; l'etiquette,
    elle, s'ajoute.

    L'arbitrage se lit dans l'ensemble et se fait sur l'**identifiant
    serveur** de l'etiquette, attribue par creation : les deux concurrents
    lisent le meme identifiant et elisent donc le **meme** gagnant. Aucune
    horloge de client n'entre dans l'arbitrage -- deux machines dont les
    horloges different ne peuvent pas elire deux gagnants differents.

    Un ecrivain mort laisse son etiquette : la peremption se mesure sur une
    **duree d'observation locale** (horloge monotone de la machine qui
    observe -- jamais une comparaison de deux horloges), et au-dela de
    :data:`LOCK_TTL_SECONDS` d'observation continue l'etiquette est
    presumee perimee : elle est supprimee (nettoyage) et le suivant prend
    la main.

    Renvoie le **jeton** du verrou (le nom de l'etiquette), ou ``None`` si
    le PR ne porte encore aucun commentaire collant : le premier ecrivain
    le cree, il n'y a alors rien a verrouiller (et le cas des deux
    commentaires collants naissants est traite par
    :func:`merge_duplicates`).
    """
    deadline = monotonic() + LOCK_WAIT_SECONDS
    mine = _lock_label(owner)
    first_seen: dict = {}   # (nom, identifiant) -> horloge de 1re observation
    while True:
        comments = list_comments(pr, repo, runner, timeout)
        cid = find_sticky_id(comments)
        if cid is None:
            return None
        state = _labels_state(pr, repo, runner, timeout)
        now = monotonic()
        # --- purge des verrous perimes -----------------------------------
        # La peremption se mesure sur une **duree d'observation locale** :
        # une etiquette de verrou vue vivante sans interruption pendant
        # LOCK_TTL_SECONDS est presumee perimee (ecrivain mort). Aucune
        # horloge d'une autre machine n'entre dans la comparaison -- deux
        # machines dont les horloges different ne peuvent pas se voler
        # mutuellement le verrou. La fenetre est indexee sur le couple
        # (nom, identifiant) : un **re-enregistrement** (donc un nouvel
        # identifiant) rouvre une fenetre neuve.
        purged = False
        for name in list(state):
            if name == mine or not _is_lock_label(name):
                continue
            key = (name, state[name])
            seen = first_seen.setdefault(key, now)
            if now - seen >= LOCK_TTL_SECONDS:
                # ecrivain presume mort : on supprime le verrou perime
                first_seen.pop(key, None)
                _delete_label(repo, runner, timeout, name)
                purged = True
        if purged:
            continue    # on relit l'etat apres nettoyage
        # --- election : le plus ancien identifiant serveur gagne --------
        # Tout verrou observe ici a ete enregistre **avant** notre propre
        # enregistrement : il porte donc un identifiant plus petit que le
        # notre. On attend.
        others = sorted((_sort_key(state[n], n), n)
                        for n in state if n != mine and _is_lock_label(n))
        if others:
            # un ecrivain tient le verrou : on attend, on n'ecrit pas
            if monotonic() > deadline:
                raise RuntimeError(
                    f"verrou du commentaire collant {pr} tenu par "
                    f"{others[0][1]!r} -- ecriture refusee (pas de succes "
                    f"sur une ecriture non exclusive)")
            sleep(_jitter_delay())
            continue
        # --- tentative : on s'enregistre (ajout atomique) ---------------
        state = _add_label(pr, repo, runner, timeout, mine)
        if mine not in state:
            state = _labels_state(pr, repo, runner, timeout)
            if mine not in state:
                raise RuntimeError(
                    f"verrou du commentaire collant {pr} : l'etiquette de "
                    f"verrou {mine!r} n'apparait pas apres son ajout")
        my_key = _sort_key(state.get(mine), mine)
        others = sorted((_sort_key(state[n], n), n)
                        for n in state if n != mine and _is_lock_label(n))
        if others and others[0][0] < my_key:
            # un ecrivain plus ancien s'est enregistre entre-temps : on
            # attend (notre etiquette reste posee -- elle porte notre rang)
            if monotonic() > deadline:
                raise RuntimeError(
                    f"verrou du commentaire collant {pr} pris par un autre "
                    f"ecrivain -- ecriture refusee")
            sleep(_jitter_delay())
            continue
        # --- confirmation -----------------------------------------------
        # Une lecture peut avoir ete servie **avant** la commit d'un
        # concurrent : elle ne le montre pas. On relit donc l'etat de
        # verrou apres un delai de stabilisation, et c'est cette lecture
        # etablie qui tranche. Ce n'est pas une relecture de plus du
        # *corps* (elle ne fermerait pas la classe de course) : c'est la
        # relecture de l'etat de verrou, ou l'ordre serveur est connu.
        sleep(_settle_delay())
        state = _labels_state(pr, repo, runner, timeout)
        if mine not in state:
            # notre etiquette a disparu (volee entre-temps) : on recommence
            continue
        my_key = _sort_key(state.get(mine), mine)
        others = sorted((_sort_key(state[n], n), n)
                        for n in state if n != mine and _is_lock_label(n))
        if others and others[0][0] < my_key:
            if monotonic() > deadline:
                raise RuntimeError(
                    f"verrou du commentaire collant {pr} pris par un autre "
                    f"ecrivain -- ecriture refusee")
            sleep(_jitter_delay())
            continue
        return mine


def _release_lock(pr: int, repo: str, runner: Callable, timeout: int,
                  token: Optional[str]) -> bool:
    r"""Relache le verrou -- en supprimant **notre** etiquette.

    La suppression passe par `DELETE /repos/{owner}/{repo}/labels/{nom}` :
    elle detache l'etiquette du PR **et** supprime la definition, de sorte
    qu'aucune trace ne reste au depot apres chaque ecriture (mesure du
    2026-11-04).

    Un verrou vole (perime puis repris par un autre) n'est pas relache :
    ce n'est pas le notre. L'echec de la suppression n'est pas fatal :
    l'etiquette perimee sera retiree par l'ecrivain suivant.
    """
    if not token:
        return False
    try:
        _delete_label(repo, runner, timeout, token)
    except RuntimeError:
        return False
    return True


def merge_duplicates(pr: int, repo: str = DEFAULT_REPO,
                     runner: Optional[Callable] = None,
                     timeout: int = DEFAULT_TIMEOUT,
                     token: Optional[str] = None,
                     sleep: Optional[Callable] = None) -> dict:
    r"""Fusionne les commentaires collants en doublon dans l'**id max**.

    Deux workflows en parallele peuvent chacun creer un commentaire : le PR
    en porte alors deux, dont un garde une section perimee. Ici, toutes les
    sections sont reunies dans le commentaire d'**id max** (canonique), et les
    autres sont reecrits en une ligne de **renvoi** — **rien n'est supprime**,
    et le PR n'en porte plus qu'un collant.

    La fusion **ecrit** : elle se fait donc sous le meme verrou que
    l'ecriture. Un jeton deja acquis (l'appelant tient deja le verrou) est
    reutilise ; sinon la fusion prend le verrou elle-meme -- sans quoi deux
    fusions concurrentes s'ecraseraient.
    """
    if runner is None:  # pragma: no cover - trivial default
        runner = _default_runner
    if sleep is None:
        sleep = _sleep
    comments = list_comments(pr, repo, runner, timeout)
    stickies = sticky_comments(comments)
    if len(stickies) <= 1:
        return {"action": "noop",
                "comment_id": stickies[0]["id"] if stickies else None,
                "merged": []}
    held = token
    if held is None:
        held = _acquire_lock(pr, repo, runner, timeout, _owner_id(), sleep)
    try:
        # Relecture sous verrou : l'etat a pu bouger entre la detection du
        # doublon et la prise du verrou.
        comments = list_comments(pr, repo, runner, timeout)
        stickies = sticky_comments(comments)
        if len(stickies) <= 1:
            return {"action": "noop",
                    "comment_id": stickies[0]["id"] if stickies else None,
                    "merged": []}
        canonical = stickies[-1]
        canonical_body = canonical.get("body") or ""
        merged = parse_sections(canonical_body)
        for row in stickies:
            if row["id"] == canonical["id"]:
                continue
            for name, text in parse_sections(row.get("body") or "").items():
                # Le canonique gagne en cas de conflit : son contenu est le
                # plus recent ; le doublon n'apporte que ce qui manque.
                merged.setdefault(name, text)
        new_body = render(merged)
        _patch_comment(canonical["id"], new_body, repo, runner, timeout)
        others = []
        for row in stickies:
            if row["id"] == canonical["id"]:
                continue
            _patch_comment(row["id"], forward_body(canonical["id"]), repo, runner,
                           timeout)
            others.append(row["id"])
        return {"action": "merged", "comment_id": canonical["id"],
                "merged": others}
    finally:
        if token is None and held is not None:
            _release_lock(pr, repo, runner, timeout, held)


def _verify_upsert(organ: str, body: str, pr: int, repo: str,
                    runner: Callable, timeout: int) -> bool:
    r"""L'ecriture de **notre** section est-elle **constatee** ?

    On relit le commentaire canonique : **notre** section doit y porter
    exactement le corps ecrit. Une section **absente** apres un POST
    concurrent est un echec d'ecriture, pas un succes.

    **Portee : une seule section.** La verification porte sur l'organe
    ecrivain -- elle ne certifie **pas** que les sections des autres
    ecrivains sont intactes. Une section ecrasée entre-temps par un
    tiers n'est pas detectable d'ici (l'ecrivain concurrent l'a vue, lui ;
    c'est lui qui peut la restaurer). L'annonce doit le dire tel quel :
    certifier « toutes les sections » serait une affirmation que le code ne
    fait pas.
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


def _settled_state(organ: str, body: str, pr: int, repo: str,
                   runner: Callable, timeout: int):
    r"""L'etat voulu est-il **deja** celui du commentaire collant ?

    Lecture **seule** : aucun verrou pris, aucun corps reecrit. Un run qui
    n'a rien a dire ne touche donc pas au commentaire -- pas de bruit
    d'edition, et pas de fenetre ouverte pour un ecrivain concurrent.

    Renvoie ``(etat_atteint, id_du_commentaire_collant)``.
    """
    comments = list_comments(pr, repo, runner, timeout)
    cid = find_sticky_id(comments)
    if cid is None:
        return False, None
    sections = parse_sections(_body_of(comments, cid))
    want = (body or "").strip()
    if not want:
        return organ not in sections, cid
    return sections.get(organ, "") == want, cid


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
    if cid is not None and new_body == existing_body:
        return {"action": "unchanged", "comment_id": cid}
    # --- relecture juste avant l'ecriture --------------------------------
    # Fenetre de perte d'ecriture : entre notre lecture et notre PATCH, un
    # autre ecrivain peut avoir ajoute SA section. Ecrire le corps derive
    # de la lecture perimee EFFACE sa section -- et notre verification, qui
    # ne regarde que notre organe, ne le verrait pas : le succes serait
    # rendu sur un etat ou l'autre avertissement a disparu.
    # On relit donc juste avant d'ecrire, et si le corps a bouge, on
    # reapplique notre section sur le corps COURANT.
    comments = list_comments(pr, repo, runner, timeout)
    fresh_cid = find_sticky_id(comments)
    fresh_body = _body_of(comments, fresh_cid)
    if fresh_cid != cid or fresh_body != existing_body:
        cid = fresh_cid
        existing_body = fresh_body
        sections = parse_sections(existing_body)
        sections[organ] = (body or "").strip()
        new_body = render(sections)
        if cid is not None and new_body == existing_body:
            return {"action": "unchanged", "comment_id": cid}
    if cid is not None:
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
    new_body = render(sections)
    # Meme fenetre que pour l'upsert : on relit avant d'ecrire, et on
    # reapplique le retrait sur le corps courant plutot que d'effacer la
    # section qu'un autre ecrivain y aurait ajoutee entre-temps.
    comments = list_comments(pr, repo, runner, timeout)
    fresh_cid = find_sticky_id(comments)
    fresh_body = _body_of(comments, fresh_cid)
    if fresh_cid != cid or fresh_body != existing_body:
        cid = fresh_cid
        existing_body = fresh_body
        sections = parse_sections(existing_body)
        if organ not in sections:
            return {"action": "unchanged", "comment_id": cid}
        del sections[organ]
        new_body = render(sections)
    if cid is None:
        return {"action": "silent", "comment_id": None}
    return _patch_comment(cid, new_body, repo, runner, timeout)


def upsert_section(organ: str, body: str, pr: int, repo: str = DEFAULT_REPO,
                   runner: Optional[Callable] = None,
                   timeout: int = DEFAULT_TIMEOUT,
                   attempts: int = MAX_ATTEMPTS,
                   sleep: Optional[Callable] = None,
                   owner: Optional[str] = None) -> dict:
    r"""Ecrit (ou reecrit) la section d'un organe dans le commentaire unique.

    L'ecriture est **verifiee** : apres chaque tour, l'etat est relu ; s'il
    n'est pas celui attendu (section ecrasee par un ecrivain concurrent,
    doublon cree en parallele), on **retente** avec un delai aleatoire, au
    plus ``attempts`` fois. A defaut de verification, l'echec est remonte :
    un succes ne se rend pas sur une ecriture non constatee.

    **Fenetre de stabilisation.** La relecture certifie l'etat **a l'instant
    de la relecture**. Un ecrivain concurrent peut ecrire juste apres, et
    ecraser notre section -- sans pouvoir la restaurer (il ne l'a jamais
    vue). L'ecriture conditionnelle, qui fermerait la fenetre, n'est pas
    disponible : l'API des commentaires la refuse (mesure du 2026-11-04,
    `PATCH .../issues/comments/<id>` avec `If-Match` -> HTTP 400
    « Conditional request headers are not allowed in unsafe requests unless
    supported by the endpoint »).

    On relit donc **une seconde fois, apres un delai de stabilisation** : si
    notre section a disparu entre-temps, c'est qu'un ecrivain concurrent
    nous a ecrase -- on ne certifie pas, on rejoue (et le rejeu remerge sur
    le corps courant, donc les deux sections se retrouvent).

    Ce que la fenetre ne ferme pas : une ecriture concurrente qui tombe
    **apres** la derniere relecture. La portee de la certification est donc
    explicitement **notre section**, a l'instant de la derniere relecture --
    pas « toutes les sections », et pas « pour toujours ».

    **Verrou d'ecriture.** La fenetre residuelle est fermee par une
    **exclusion mutuelle reelle** : l'ecriture se fait sous un verrou
    **externe au commentaire** -- une etiquette du PR (:func:`_acquire_lock`),
    dont l'ajout est atomique cote serveur, la ou un PATCH de corps ne
    l'est pas. Un ecrivain concurrent qui trouve le verrou **attend** au
    lieu d'ecraser ; il reprend au tour suivant sur un corps frais, une
    fois le verrou libere. Le verrou a une duree de vie : un ecrivain mort
    laisse une etiquette, que le suivant retire (verrou perime) et
    remplace.
    """
    _validate_organ(organ)
    if runner is None:  # pragma: no cover - trivial default
        runner = _default_runner
    if sleep is None:
        sleep = _sleep
    # --- etat deja voulu ? (lecture seule) --------------------------------
    # Rien a ecrire -> pas de verrou, pas de reecriture : le commentaire
    # n'est pas touche (le corps reste byte-identique, pas de bruit
    # d'edition).
    settled, cid = _settled_state(organ, body, pr, repo, runner, timeout)
    if settled:
        out = {"action": "unchanged", "comment_id": cid}
        merged = merge_duplicates(pr, repo, runner, timeout)
        if merged.get("action") == "merged":
            out = dict(out)
            out["merged"] = merged.get("merged", [])
        if _verify_upsert(organ, body, pr, repo, runner, timeout):
            out["verified"] = True
            return out
        # l'etat a bouge entre-temps : on passe par le chemin verrouille
    if owner is None:
        owner = _owner_id()
    lock_token = _acquire_lock(pr, repo, runner, timeout, owner, sleep)
    try:
        for attempt in range(1, max(1, attempts) + 1):
            out = _upsert_attempt(organ, body, pr, repo, runner, timeout)
            merged = merge_duplicates(pr, repo, runner, timeout, token=lock_token)
            if merged.get("action") == "merged":
                out = dict(out)
                out["merged"] = merged.get("merged", [])
            if _verify_upsert(organ, body, pr, repo, runner, timeout):
                # --- relecture de stabilisation ------------------------------
                # On relit une fois de plus apres un court delai : une ecriture
                # concurrencee tombee DANS la fenetre est detectee ici, et le
                # rejeu la remerge sur le corps courant.
                sleep(_settle_delay())
                if _verify_upsert(organ, body, pr, repo, runner, timeout):
                    out["verified"] = True
                    return out
                if attempt < attempts:
                    sleep(_jitter_delay())
                continue
            if attempt < attempts:
                sleep(_jitter_delay())
        raise RuntimeError(
            f"section {organ!r} non constatee apres {attempts} tentative(s) "
            f"(ecriture concurrente ?) -- succes refuse")
    finally:
        if lock_token is not None:
            _release_lock(pr, repo, runner, timeout, lock_token)


def clear_section(organ: str, pr: int, repo: str = DEFAULT_REPO,
                  runner: Optional[Callable] = None,
                  timeout: int = DEFAULT_TIMEOUT,
                  attempts: int = MAX_ATTEMPTS,
                  sleep: Optional[Callable] = None,
                  owner: Optional[str] = None) -> dict:
    r"""Retire la section d'un organe qui redevient vert.

    Le commentaire n'est **jamais supprime** : il est reecrit en place avec
    l'etat « plus aucun avertissement consultatif » (#15372 : pas
    d'effacement d'historique). Comme l'ecriture, le retrait est **verifie**
    (la section doit avoir disparu) et rejoue en cas de conflit concurrent.

    Le retrait se fait **sous verrou** comme l'ecriture : sans exclusion
    mutuelle, deux retraits concurrents peuvent se masquer l'un l'autre.
    """
    _validate_organ(organ)
    if runner is None:  # pragma: no cover - trivial default
        runner = _default_runner
    if sleep is None:
        sleep = _sleep
    # Rien a retirer -> pas de verrou, pas de reecriture.
    settled, cid = _settled_state(organ, "", pr, repo, runner, timeout)
    if settled and cid is not None:
        out = {"action": "unchanged", "comment_id": cid}
        merged = merge_duplicates(pr, repo, runner, timeout)
        if merged.get("action") == "merged":
            out = dict(out)
            out["merged"] = merged.get("merged", [])
        if _verify_clear(organ, pr, repo, runner, timeout):
            out["verified"] = True
            return out
    if owner is None:
        owner = _owner_id()
    lock_token = _acquire_lock(pr, repo, runner, timeout, owner, sleep)
    try:
        for attempt in range(1, max(1, attempts) + 1):
            out = _clear_attempt(organ, pr, repo, runner, timeout)
            merged = merge_duplicates(pr, repo, runner, timeout, token=lock_token)
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
    finally:
        if lock_token is not None:
            _release_lock(pr, repo, runner, timeout, lock_token)


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
