#!/usr/bin/env python3
"""Filet des remarques user sans reponse sur les issues (#20183, campagne #20185).

Le depot a un filet pour les remarques du user sur les PRs (B.0,
``scripts/check_unaddressed_nits.py``, exit 1 au merge). Il n'avait rien pour les
remarques du user sur les **issues** : un commentaire « Concern: ... » du
mainteneur pouvait rester sans reponse indefiniment — le merge-gate ne le voit pas
(ce n'est pas une PR), le tapis sert l'issue selon ses propres criteres (le grain,
pas le fil), et la condensation du dashboard emporte le signalement.

La premiere livraison couvrait la classe ``user-concern``, la deuxieme la
classe ``user-remark`` : **tout autre commentaire du mainteneur** (question,
consigne, arbitrage, constat) en attente de reponse. La troisieme a ajoute la
classe ``reviewer-reserve`` : une **reserve de relecteur** (Hermes, NanoClaw,
clusterManager-Myia, lane tierce) posee sur une **issue** avec un marqueur de
verdict, et jamais levee. Cette tranche ajoute la classe
``external-unanswered`` : un **commentaire d'un auteur hors flotte** (etudiant,
contributeur public) reste sans triage de la flotte (campagne #20185 ; les
deux classes restantes viendront chacune par sa propre PR). Seule la flotte
trie : un second auteur externe ni un bot ne sont candidats de reponse, et la
reponse attendue **cite le commentaire oublie** (machinerie de citation forte,
comme une remarque).

Le probleme propre a cette classe est le **login partage** : la flotte ecrit sous
le compte du mainteneur, et l'auteur ne distingue donc plus un post de lane d'une
remarque du user. C'est la FORME du corps qui tranche — six signatures mesurees
(``lane`` + siege, jeton de siege ``myia-x:y``, tag ``Grain:``, en-tete ``Lane``,
filigrane de cycle ``c.NNN``, tag de tete entre crochets). Mesure canonique du
2026-10-20 (465 issues ouvertes depuis le 2026-09-25, predicats de ce fichier) :
1627 commentaires bruts du compte partage, **1071 ecartes** par les signatures
(deux tiers), 556 candidats — dont 268 en ``MANUAL_REVIEW`` et 52 en
``NON REPONDU`` a l'etat du jour.

Ce qui reste apres les signatures n'est PAS un verdict : l'intention declaree
(``question`` | ``directive`` | ``statement``) est **enregistree, pas
filtrante** — les marqueurs de vocabulaire sont cites par les lanes elles-memes
(« décision user », « le user a tranché »), s'en servir comme filtre ecarterait
de vraies remarques. Le plancher ``MANUAL_REVIEW`` s'applique tel quel : la liste
est complete, quitte a sur-signaler ; l'arbitrage fin revient a la lecture
(phase 1 de la campagne).

Deux pieges mesures, et la raison pour laquelle ce n'est pas un ``grep`` :

* **FP classe 1 — l'accuse de reception d'une lane.** Sous le login partage, une
  lane repond « Concern pris en compte » : un ``^Concern`` naif le compte comme un
  Concern user neuf (#17889, #16757). Le sous-pattern ``^Concern (pris|note|...)``
  se classe ACK et sort du recensement.
* **La reponse n'est pas garantie de citer le mot.** #18601 : la reponse existe et
  ne dit jamais « Concern » — elle cite l'horodatage du Concern. Exiger le mot
  fabriquerait un faux « sans reponse ».

Un geste de lane pose apres le Concern (claim, verification, livraison, dossier de
cloture) n'est **pas** une reponse : il laisse le Concern ouvert et leve le drapeau
aggravant ``gesture-after`` (#19898 : deux gestes entre les deux Concerns).

Deux regles bornent ce qui **referme** un Concern (#20186) :

* **Le compte ne decide pas.** Les lanes ecrivent sous plusieurs logins
  (``jsboige``, les sieges ``myia-*``, le bot reviewer) ; un accuse de reception se
  juge par sa **forme**, sous n'importe lequel. Router sur le seul compte du
  mainteneur laissait les posts des autres comptes tomber dans le seau **sans
  plancher de substance**, ou un « Concern pris » nu refermait le fil.
* **Le mot seul ne referme pas.** Une citation **forte** — l'horodatage du Concern,
  ou un extrait de son texte — referme ; le mot « Concern » seul ne referme que
  porte par un acquittement de lane qui franchit ``ACK_SUBSTANCE_MIN``.

Plancher ``MANUAL_REVIEW``, fail-closed : un Concern dont le traitement n'est pas
prouve reste dans la liste, quitte a sur-signaler. L'arbitrage fin est humain.

Usage::

    python scripts/ci/check_issue_concerns.py                  # issues ouvertes
    python scripts/ci/check_issue_concerns.py --json
    python scripts/ci/check_issue_concerns.py --issues 19898 16757 17889 18601
    python scripts/ci/check_issue_concerns.py --classes user-remark --issues 21092
    python scripts/ci/check_issue_concerns.py --as-of 2026-10-08T23:59:59Z
"""

from __future__ import annotations

import argparse
import concurrent.futures
import json
import re
import subprocess
import sys
from dataclasses import dataclass, field
from datetime import datetime, timezone

REPO = "jsboige/CoursIA"

#: Le mainteneur ecrit sous ce login. Les lanes ecrivent sous le meme compte
#: (login partage) : l'auteur ne suffit donc pas a distinguer une remarque user
#: d'un post de lane — c'est la FORME du corps qui tranche (``lane_signature``,
#: classe ``user-remark``). Pour ``user-concern``, le prefixe reste un signal fort.
CONCERN_AUTHOR = "jsboige"

#: Les comptes sous lesquels une lane de la flotte ecrit : le compte partage du
#: mainteneur, les sieges de worker (``myia-*``), les bots reviewers et les
#: sieges reels mesures. Un post de lane se juge par la meme regle **quel que
#: soit** le compte qui le porte (#20186) : indexer la garde sur le seul
#: ``jsboige`` laissait un accuse de reception nu franchir le plancher de
#: substance des qu'il etait ecrit sous un autre login, alors que la menace
#: nommee par l'organe est precisement le compte partage.
#:
#: Sieges reels (mesure du 2026-11-13, corpus 1000 issues depuis le
#: 2026-09-25) : ``jsboigeEpita`` (siege po-2023 — tous ses commentaires dans
#: la fenetre sont des posts de lane) et ``jsboigeEPF`` (siege po-2025 **et**
#: plume du mainteneur : 4 « Concern: » mesures sur #22844, #23778, #23983 x2,
#: qui echappaient au filet user-concern sans cette extension — et dont les
#: posts de lane auraient inonde la classe ``external-unanswered``). La liste
#: reste FERMEE sur le mesure : un siege neuf (p. ex. ``jsboigeECE``, absent du
#: corpus) s'ajoute par une ligne accompagnee de sa mesure.
LANE_LOGIN = re.compile(
    r"^(?:jsboige|jsboigeEpita|jsboigeEPF|myia-[a-z0-9-]+|clusterManager-Myia)$"
)

#: Les comptes d'integration GitHub (App) : tout login d'app porte le suffixe
#: ``[bot]``. Ils ne sont ni la flotte ni un externe a trier — leur activite
#: (label, stale, resultat de workflow) n'attend pas de reponse de la flotte.
#: Mesure du 2026-11-13 sur le corpus (1000 issues lues depuis le 2026-09-25,
#: tous etats) : le seul bot present est ``github-actions[bot]`` ; la forme
#: par suffixe couvre la famille entiere (dependabot, stale, imgbot...).
BOT_LOGIN = re.compile(r"\[bot\]$")

#: Classe ``external-unanswered`` (#20185) : un commentaire d'un auteur HORS
#: flotte (etudiant, contributeur public — cf. ``public-contribution-triage.md``).
#: La reponse attendue est portee par la flotte seule, « en citant le
#: commentaire oublie » (#20185, phase 2) : la machinerie de citation forte
#: (horodatage, extrait long) s'applique telle quelle. Un second externe ni
#: un bot ne trient a la place de la flotte : seuls les commentaires d'un
#: login de flotte comptent comme candidats de reponse.

#: Forme mesuree du user (#19898, #16757, #17889, #18601).
CONCERN_PREFIX = re.compile(r"^Concern\b", re.IGNORECASE)

#: FP classe 1 : l'accuse de reception d'une lane, poste sous le compte partage.
ACK_PATTERN = re.compile(
    r"^Concern\s+(pris|note|traite|acquitte|ack)", re.IGNORECASE
)

#: Un geste de lane pose apres le Concern — drapeau aggravant ``gesture-after``.
#: Reconnu a son tag de protocole ou a sa signature de lane. Un geste n'est PAS
#: une reponse **en soi** : il ne retire pas le Concern de la liste. Exception :
#: un geste qui **cite fortement** le Concern (son horodatage, un extrait) y
#: repond — voir ``is_response_candidate`` (mesure : #2159).
GESTURE_PATTERN = re.compile(
    r"^\[(?:CLAIMED|CLAIMED-AMEND|VERIFICATION|DELIVERED|RELEASED|INFO|DONE|"
    r"LIVRAISON|COMPLEMENT|ADJOINT PREFLIGHT|CLOSURE PREFLIGHT|OVERRIDE|"
    r"WARN|ERROR|BLOCKED|ASK|REPLY|ACK|PROPOSAL)\]|lane\s+myia-",
    re.IGNORECASE,
)

#: Le tag de geste n'est cherche que dans les premiers caracteres : un tag de
#: protocole situe au-dela d'un long preambule n'est pas vu (donc ni
#: ``gesture-after``, ni exclusion du seau des reponses). La borne est assumee —
#: c'est elle qui empeche un long commentaire de lane de compter comme reponse —
#: et elle est nommee ici pour ne pas etre decouverte par surprise (#20186).
GESTURE_WINDOW = 400

#: Signatures de lane de la classe ``user-remark`` (#20185, classe 2). Sous le
#: login partage, l'auteur ne separe plus un post de lane d'une remarque du
#: mainteneur : c'est la FORME du corps qui tranche. Les formes ci-dessous sont
#: celles que la flotte utilise, mesurees sur le corpus du 2026-10-20 (465 issues
#: ouvertes depuis le 2026-09-25) ; elles sont evaluees dans cet ordre et le nom
#: rendu sert au rapport. Un corps qui en porte une est un post de lane, jamais
#: un candidat — deux tiers des commentaires du compte partage sont ainsi ecartes.
_LANE_SIGNATURES: tuple[tuple[str, re.Pattern[str]], ...] = (
    # Dossier de clôture produit par la session hors flotte : le login GitHub
    # est partagé, mais l'en-tête structuré identifie explicitement sa lane.
    # Ancrer la forme entière en tête évite d'exclure une remarque qui cite
    # simplement un dossier dans sa prose.
    ("astra-closure-preflight", re.compile(
        r"\AHors flotte[^\n]*\n\s*\[CLOSURE PREFLIGHT\]\s*\n"
        r"schema:\s*1\s*\nlane:\s*astra:CoursIA\s*(?:\n|\Z)"
    )),
    ("lane-near-seat", re.compile(r"\blane\b[^\w\n]{0,12}myia-", re.IGNORECASE)),
    ("seat-token", re.compile(r"myia-[a-z0-9-]+:[A-Za-z0-9._-]+")),
    ("grain-tag", re.compile(r"\bGrain\s*:", re.IGNORECASE)),
    ("lane-header", re.compile(r"(?m)^\s*\*{0,2}Lane\s*[:*]")),
    #: Borne haute a quatre chiffres (#21621) : ``\d{3,}`` avalait les ids de
    #: commentaire (``c.6280946388``) et ecartait une remarque du mainteneur qui
    #: les cite. Les numeros de cycle tiennent en 3-4 chiffres (c.278, c.2199) ;
    #: le ``\b`` final interdit deja toute coupure en tete d'un id plus long.
    ("cycle-watermark", re.compile(r"\bc\.\d{3,4}\b")),
)

#: La sixieme signature, evaluee apres neutralisation de la decoration markdown
#: (comme ``classify``) : un tag de protocole entre crochets en tete de corps.
_LANE_HEAD_TAG = re.compile(r"^\[[^\]]{1,80}\]")

#: Intention declaree d'une remarque — **enregistree, pas filtrante** : la mesure
#: du 2026-10-20 a montre que ces marqueurs de vocabulaire sont cites par les
#: lanes elles-memes (« décision user », « le user a tranché ») ; s'en servir comme
#: filtre ecarterait de vraies remarques. Le champ sert a ORDONNER la lecture.
_ACT_DIRECTIVE_RE = re.compile(
    r"\bD[ée]cision\b|\btranche\b|\bIl faut\b|\bmerci de\b|\bpeux-tu\b|"
    r"\bje pr[ée]f[èe]re\b|\bconsigne\b|\bCorrige\b|\bà corriger\b|\bnote pour\b|"
    r"\bj'attends\b",
    re.IGNORECASE,
)
ACT_QUESTION = "question"
ACT_DIRECTIVE = "directive"
ACT_STATEMENT = "statement"
_ACT_ORDER = {ACT_QUESTION: 0, ACT_DIRECTIVE: 1, ACT_STATEMENT: 2}

#: Classe ``reviewer-reserve`` — marqueurs de verdict STRUCTURELS, en position
#: d'EMISSION (premiere ligne du corps, decoration markdown neutralisee, comme
#: ``classify``). La grammaire reprend le sous-ensemble non ambigu de
#: ``CONCERN_MARKERS`` (B.0, ``scripts/check_unaddressed_nits.py``) : les
#: verdicts formels et les deux glyphes de severite. Sont EXCLUS de ce cote
#: issues les marqueurs de prose (« avant merge », « a changer »...) —
#: vocabulaire PR-contextuel dont la prose de lane sur les issues est saturee —
#: et la sous-chaine nue « CONCERNS », citee en permanence par le vocabulaire
#: de la campagne elle-meme (« la liste [CONCERNS] postee par le
#: coordinateur ») : les garder ouvrirait un mur de faux positifs, non mesure
#: ici. Le #13030 s'applique : un marqueur CITE en milieu de corps (mention,
#: citation de verdict passe) n'est pas une reserve POSEE.
_RESERVE_MARKERS = (
    "COMMENT_WITH_CONCERNS",
    "CHANGES_REQUESTED",
    "REQUEST_CHANGES",
    "NEEDS_CHANGES",
    "SUSPECT_",
    "STRUCTURAL_ONLY",
    "SCOPE FLAG",
    "🟡",
    "🔴",
)
_RESERVE_MARKER_RE = re.compile(
    "|".join(re.escape(m) for m in _RESERVE_MARKERS)
)
_RESERVE_POSED_RE = re.compile(
    "^(?:" + "|".join(re.escape(m) for m in _RESERVE_MARKERS) + ")"
)
#: Groupes de tete neutres pour la position d'emission : la persona du
#: reviewer entre crochets (« [Hermes] COMMENT_WITH_CONCERNS ») et le tag de
#: verdict passe au meme format. Ils ne SONT pas le marqueur — ils le
#: precedent.
_RESERVE_HEAD_BRACKETS = re.compile(r"^\[[^\]]{1,80}\]\s*")


def reserve_marker(body: str | None) -> str | None:
    """Le marqueur de verdict POSE en tete de premiere ligne, ou ``None``.

    Position d'emission seulement : la decoration de tete (gras, titre,
    citation) est neutralisee comme dans ``classify``, puis la PREMIERE ligne
    seule est lue ; les groupes de persona entre crochets qui ouvrent la
    ligne (« [Hermes] ») sont ecartes, et le reste doit COMMENCER par le
    marqueur. Un verdict cite apres de la prose — la reponse d'une lane qui
    reprend « ta reserve COMMENT_WITH_CONCERNS », ou la narration « Verdict :
    CHANGES_REQUESTED » — n'est pas une reserve POSEE (#13030 : c'est une
    mention).
    """
    stripped = _DECORATION.sub("", body or "")
    first_line = stripped.splitlines()[0] if stripped.splitlines() else ""
    while True:
        reduced = _RESERVE_HEAD_BRACKETS.sub("", first_line, count=1)
        if reduced == first_line:
            break
        first_line = reduced
    match = _RESERVE_POSED_RE.match(first_line)
    return match.group(0) if match else None

_WS = re.compile(r"\s+")
_DECORATION = re.compile(r"^[\s*_#>`]+")
_LINK = re.compile(r"https?://\S+")
_WORD_CONCERN = re.compile(r"\bConcerns?\b", re.IGNORECASE)

GRAPHQL_SEARCH = """
query($q: String!, $after: String) {
  search(query: $q, type: ISSUE, first: 100, after: $after) {
    pageInfo { hasNextPage endCursor }
    nodes { ... on Issue { number } }
  }
}
"""


# --------------------------------------------------------------------------- #
# Modele
# --------------------------------------------------------------------------- #


@dataclass(frozen=True)
class Comment:
    id: int
    author: str
    created_at: str
    body: str

    @property
    def when(self) -> datetime:
        return datetime.strptime(self.created_at, "%Y-%m-%dT%H:%M:%SZ").replace(
            tzinfo=timezone.utc
        )


@dataclass
class ConcernFinding:
    comment_id: int
    created_at: str
    excerpt: str
    status: str
    proof: int | None
    gesture_after: bool

    #: Etiquette de classe — le rendu et les tests scoping lisent ce champ.
    slug = "user-concern"

    def as_dict(self) -> dict:
        return {
            "comment_id": self.comment_id,
            "created_at": self.created_at,
            "excerpt": self.excerpt,
            "status": self.status,
            "proof": self.proof,
            "gesture_after": self.gesture_after,
        }


@dataclass
class RemarkFinding:
    comment_id: int
    created_at: str
    excerpt: str
    status: str
    proof: int | None
    act: str
    gesture_after: bool

    slug = "user-remark"

    def as_dict(self) -> dict:
        return {
            "comment_id": self.comment_id,
            "created_at": self.created_at,
            "excerpt": self.excerpt,
            "status": self.status,
            "proof": self.proof,
            "act": self.act,
            "gesture_after": self.gesture_after,
        }


@dataclass
class ReserveFinding:
    comment_id: int
    created_at: str
    excerpt: str
    status: str
    proof: int | None
    marker: str
    gesture_after: bool

    slug = "reviewer-reserve"

    def as_dict(self) -> dict:
        return {
            "comment_id": self.comment_id,
            "created_at": self.created_at,
            "excerpt": self.excerpt,
            "status": self.status,
            "proof": self.proof,
            "marker": self.marker,
            "gesture_after": self.gesture_after,
        }


@dataclass
class ExternalFinding:
    comment_id: int
    created_at: str
    excerpt: str
    status: str
    proof: int | None
    author: str
    gesture_after: bool

    slug = "external-unanswered"

    def as_dict(self) -> dict:
        return {
            "comment_id": self.comment_id,
            "created_at": self.created_at,
            "excerpt": self.excerpt,
            "status": self.status,
            "proof": self.proof,
            "author": self.author,
            "gesture_after": self.gesture_after,
        }


@dataclass
class IssueReport:
    number: int
    concerns: list[ConcernFinding]
    remarks: list[RemarkFinding] = field(default_factory=list)
    reserves: list[ReserveFinding] = field(default_factory=list)
    externals: list[ExternalFinding] = field(default_factory=list)
    #: Commentaires ecartes par signature de lane, agreges par nom de signature
    #: (#21621). L'ecart est PUBLIE : un total de candidats ne doit jamais
    #: passer pour un recensement exhaustif du fil.
    excluded: dict[str, int] = field(default_factory=dict)

    @property
    def unresolved(self) -> list:
        return [c for c in self.concerns if c.status != "REPONDU"] + [
            r for r in self.remarks if r.status != "REPONDU"
        ] + [r for r in self.reserves if r.status != "REPONDU"] + [
            e for e in self.externals if e.status != "REPONDU"
        ]

    @property
    def gesture_after(self) -> bool:
        return (
            any(c.gesture_after for c in self.concerns)
            or any(r.gesture_after for r in self.remarks)
            or any(r.gesture_after for r in self.reserves)
            or any(e.gesture_after for e in self.externals)
        )

    def as_dict(self) -> dict:
        return {
            "number": self.number,
            "gesture_after": self.gesture_after,
            "concerns": [c.as_dict() for c in self.concerns],
            "remarks": [r.as_dict() for r in self.remarks],
            "reserves": [r.as_dict() for r in self.reserves],
            "externals": [e.as_dict() for e in self.externals],
            "excluded_by_signature": dict(self.excluded),
        }


# --------------------------------------------------------------------------- #
# Classification (pur, sans reseau — c'est ce que les tests exercent)
# --------------------------------------------------------------------------- #


def normalise(body: str) -> str:
    return _WS.sub(" ", (body or "").strip())


def excerpt(body: str, width: int = 200) -> str:
    return normalise(body)[:width]


def classify(comment: Comment) -> str:
    """Classe un commentaire : ``concern`` | ``ack`` | ``gesture`` | ``other``.

    La decoration markdown de tete est neutralisee avant le match : une reponse
    « **Concern pris (ai-01).** » doit se lire comme un ACK, pas comme un Concern.

    Le routage porte sur **l'ensemble** des logins de lane (``LANE_LOGIN``), pas sur
    le seul compte du mainteneur : router sur un login unique faisait tomber les
    posts des autres comptes dans ``other``, le seul seau **sans plancher de
    substance** — un accuse de reception nu y refermait un Concern (#20186).
    """
    stripped = _DECORATION.sub("", comment.body or "")
    if LANE_LOGIN.match(comment.author or "") and CONCERN_PREFIX.match(stripped):
        return "ack" if ACK_PATTERN.match(stripped) else "concern"
    if GESTURE_PATTERN.search((comment.body or "")[:GESTURE_WINDOW]):
        return "gesture"
    return "other"


def lane_signature(body: str | None) -> str:
    """Signature de lane portee par le corps, ou ``""`` (classe ``user-remark``).

    Sous le login partage, l'auteur ne separe pas un post de lane d'une remarque
    du mainteneur : un corps qui porte l'une des signatures mesurees est un post
    de lane, **jamais** un candidat de la classe 2 (#20185). L'ordre d'evaluation
    est celui de ``_LANE_SIGNATURES`` ; le nom rendu sert au rapport et aux tests.
    La decoupe tete-crochets s'applique apres neutralisation de la decoration
    markdown, comme ``classify``.
    """
    text = body or ""
    for name, pattern in _LANE_SIGNATURES:
        if pattern.search(text):
            return name
    if _LANE_HEAD_TAG.match(_DECORATION.sub("", text)):
        return "head-tag"
    return ""


def remark_act(body: str) -> str:
    """Intention declaree : ``question`` | ``directive`` | ``statement``.

    **Enregistree, pas filtrante** : la mesure du 2026-10-20 a montre que les
    marqueurs de vocabulaire (« Décision », « tranche »...) sont cites par les
    lanes elles-memes (« décision user », « le user a tranché ») — s'en servir
    comme filtre ecarterait de vraies remarques. Le champ sert a ordonner la
    lecture, l'arbitrage reste humain.
    """
    text = normalise(body)
    if "?" in text:
        return ACT_QUESTION
    if _ACT_DIRECTIVE_RE.search(text):
        return ACT_DIRECTIVE
    return ACT_STATEMENT


def hhmm_token(created_at: str) -> str:
    """``2026-10-07T15:30:59Z`` -> ``15:30Z`` (la forme citee par #18601).

    Rend ``""`` sur toute forme non ``Z`` (milliseconde, offset, ``null``) au lieu
    de lever : un seul commentaire mal forme tuait le run sur les 580 issues pour
    une donnee non essentielle (#20186). Un jeton vide **n'est pas** une citation —
    ``cite_strength`` le teste explicitement avant de s'en servir.
    """
    try:
        dt = datetime.strptime(created_at, "%Y-%m-%dT%H:%M:%SZ")
    except (TypeError, ValueError):
        return ""
    return f"{dt.hour:02d}:{dt.minute:02d}Z"


def _shares_quote(source: str, reply: str, width: int = 40, step: int = 20) -> bool:
    """Une fenetre du texte de ``source`` se retrouve-t-elle dans ``reply`` ?

    Les parametres etaient nommes a l'envers (``body``/``text``) alors que le
    premier recoit toujours le **Concern** et le second la **reponse** : le
    comportement etait correct, la lecture ne l'etait pas (#20186).
    """
    src = normalise(_LINK.sub("", source))
    if len(src) < width:
        return False
    for i in range(0, len(src) - width + 1, step):
        window = src[i : i + width]
        if window.count(" ") > width * 0.5:
            continue
        if window in reply:
            return True
    return False


#: Longueur minimale d'un extrait partage pour qu'une citation **par le texte**
#: soit tenue pour une citation. La fenetre courte (40 caracteres) de
#: ``_shares_quote`` est un **filet**, pas une preuve : mesure sur 624 issues,
#: elle attrapait des coincidences de fenetre dans des posts de lane
#: (« 46`, `37642385421`, `37642397358` » — une suite de numeros de PR partages,
#: pas une citation). Pour un **geste**, dont le texte est formule, la citation
#: par le texte n vaut que si elle est longue ; l'horodatage reste la forme
#: forte par excellence (c'est la convention mesuree : « Reponse au Concern du
#: 2026-10-18T22:26Z »).
QUOTE_STRONG_MIN = 80


def cites_concern(concern: Comment, reply: Comment) -> bool:
    """Le commentaire ``reply`` cite-t-il **ce** Concern sans ambiguite ?

    Deux formes, toutes deux explicites :

    * l'**horodatage** du Concern (convention actuelle des lanes : « Reponse au
      Concern du 2026-10-18T22:26Z »). Cette détection est donc couplée à la
      signature des lanes, qui inclut la date et l'heure à la minute en UTC ;
      le test ``test_lane_signature_contract_requires_utc_minute`` surveille
      explicitement ce contrat ;
    * un **extrait long** de son texte (>= ``QUOTE_STRONG_MIN`` caracteres).

    La fenetre courte de ``_shares_quote`` est exclue ici : c'est ce qui
    separait une citation d'une coincidence, mesure a l'appui (#2159 et les
    624 issues lues).
    """
    token = hhmm_token(concern.created_at)
    if token and token in normalise(reply.body):
        return True
    return _shares_quote(
        concern.body, normalise(reply.body), width=QUOTE_STRONG_MIN, step=20
    )


#: Force d'une citation. Les trois formes mesurees ne se valent pas : l'horodatage
#: du Concern et la citation de son texte s'obtiennent en **lisant** le Concern ;
#: le mot seul s'ecrit sans l'avoir lu. La docstring historique de ``cites``
#: concedait deja que « le mot seul ne suffit pas a distinguer un acquittement ».
CITE_STRONG = "strong"
CITE_WEAK = "weak"
CITE_NONE = "none"


def cite_strength(concern: Comment, reply: Comment) -> str:
    """``strong`` (horodatage ou citation) | ``weak`` (le mot seul) | ``none``."""
    text = normalise(reply.body)
    token = hhmm_token(concern.created_at)
    if token and token in text:
        return CITE_STRONG
    if _shares_quote(concern.body, text):
        return CITE_STRONG
    if _WORD_CONCERN.search(text):
        return CITE_WEAK
    return CITE_NONE


def cites(concern: Comment, reply: Comment) -> bool:
    """La reponse traite-t-elle CE Concern, au sens **faible** ?

    Vrai des qu'une des trois formes est presente, le mot compris : c'est le
    predicat de *reference*. Ce qui **referme** un Concern est ``proves``, qui
    separe les formes fortes de la forme faible.
    """
    return cite_strength(concern, reply) != CITE_NONE


def proves(concern: Comment, reply: Comment, kind: str) -> bool:
    """La reponse REFERME-t-elle le Concern ?

    Une citation **forte** referme. La forme **faible** (le mot seul) ne referme
    que portee par un acquittement de lane qui franchit le plancher de substance —
    doctrine de #17889 (« une lane qui prend le Concern ET pose du fond y repond »),
    et ``is_response_candidate`` a deja ecarte les acquittements nus. Hors de la,
    un commentaire qui ne fait que nommer le mot laisse le Concern en
    ``MANUAL_REVIEW`` : ni prouve traite, ni ignore (#20186).
    """
    strength = cite_strength(concern, reply)
    if strength == CITE_STRONG:
        return True
    if strength == CITE_WEAK:
        return kind == "ack"
    return False


#: Un acquittement de lane ne repond pas s'il ne fait qu'accuser reception. Une
#: lane qui prend le Concern ET pose du fond y repond (#17889 : « Concern pris en
#: compte — oui, les transcripts portent plus que la premiere vague… », 2410
#: caracteres). Seuil de substance, volontairement bas : au-dela du seul accuse.
ACK_SUBSTANCE_MIN = 120


def is_response_candidate(
    kind: str, comment: Comment, concern: Comment | None = None
) -> bool:
    """Un commentaire ``comment`` peut-il refermer ``concern`` ?

    ``concern`` est optionnel par compatibilite (les tests d'isolement
    l'appellent sans) : **sans** lui, un geste n'est jamais candidat — c'est le
    comportement historique, conserve.

    Un geste de lane qui **cite fortement** le Concern (son horodatage, un
    extrait de son texte) est en revanche une reponse : sous le login partage,
    toute reponse de lane porte un tag de protocole (``[INFO]``, ``[REPLY]``...)
    ou la signature ``lane myia-``, donc tout tombe dans ``gesture``. Sans cette
    exception, une reponse qui cite le Concern restait invisible et le Concern
    restait classe NON REPONDU — mesure : #2159, faux NON REPONDU sur la
    reponse c6259310809 au Concern c6255920966.
    """
    if kind == "concern":
        return False
    if kind == "gesture":
        return concern is not None and cites_concern(concern, comment)
    if kind == "ack":
        return len(normalise(comment.body)) >= ACK_SUBSTANCE_MIN
    return True


#: Classes livrees par l'organe (la campagne #20185 en compte six ; les deux
#: restantes viendront chacune par sa propre PR). ``analyse_comments`` accepte un
#: sous-ensemble — les tests s'en servent pour scoper une classe a la fois.
CLASSES = (
    "user-concern",
    "user-remark",
    "reviewer-reserve",
    "external-unanswered",
)


def analyse_comments(
    number: int, comments: list[Comment], classes: tuple[str, ...] = CLASSES
) -> IssueReport:
    kinds = [classify(c) for c in comments]
    findings: list[ConcernFinding] = []
    remarks: list[RemarkFinding] = []
    reserves: list[ReserveFinding] = []
    externals: list[ExternalFinding] = []
    excluded: dict[str, int] = {}

    if "user-concern" in classes:
        for i, comment in enumerate(comments):
            if kinds[i] != "concern":
                continue
            later = list(zip(comments[i + 1 :], kinds[i + 1 :]))
            candidates = [
                (other, kind)
                for other, kind in later
                if is_response_candidate(kind, other, comment)
            ]
            proof = None
            for other, kind in candidates:
                if proves(comment, other, kind):
                    proof = other.id
                    break
            if proof is not None:
                status = "REPONDU"
            elif candidates:
                status = "MANUAL_REVIEW"
            else:
                status = "NON REPONDU"
            findings.append(
                ConcernFinding(
                    comment_id=comment.id,
                    created_at=comment.created_at,
                    excerpt=excerpt(comment.body),
                    status=status,
                    proof=proof,
                    # Le geste qui **referme** le Concern n'aggrave rien : le
                    # drapeau vise les gestes poses apres le Concern et qui
                    # n'y repondent pas.
                    gesture_after=any(
                        kind == "gesture" and other.id != proof
                        for other, kind in later
                    ),
                )
            )

    if "reviewer-reserve" in classes:
        for i, comment in enumerate(comments):
            marker = reserve_marker(comment.body)
            if marker is None:
                continue
            later = list(zip(comments[i + 1 :], kinds[i + 1 :]))
            candidates = [
                (other, kind)
                for other, kind in later
                if is_response_candidate(kind, other, comment)
            ]
            # Une reserve se referme comme une remarque : par une citation
            # FORTE (horodatage du commentaire porteur, extrait long de son
            # texte). La convention mesuree des levees — « [OVERRIDE] lane
            # myia-ai-01 ... je leve la reserve d'Hermes du 14:05Z » — porte
            # l'horodatage, donc tombe dans la forme forte. Une levee qui ne
            # cite ni l'heure ni le texte reste en MANUAL_REVIEW : le plancher
            # rend la liste COMPLETE, quitte a sur-signaler.
            proof = None
            for other, kind in candidates:
                if proves(comment, other, kind):
                    proof = other.id
                    break
            if proof is not None:
                status = "REPONDU"
            elif candidates:
                status = "MANUAL_REVIEW"
            else:
                status = "NON REPONDU"
            reserves.append(
                ReserveFinding(
                    comment_id=comment.id,
                    created_at=comment.created_at,
                    excerpt=excerpt(comment.body),
                    status=status,
                    proof=proof,
                    marker=marker,
                    gesture_after=any(
                        kind == "gesture" and other.id != proof
                        for other, kind in later
                    ),
                )
            )

    if "user-remark" in classes:
        for i, comment in enumerate(comments):
            if comment.author != CONCERN_AUTHOR or kinds[i] != "other":
                continue
            signature = lane_signature(comment.body)
            # Le tag de protocole en tete est AMBIGU (#21621) : « [NanoClaw] a
            # raison de… » est une vraie remarque du mainteneur, tandis qu'un
            # « [LIVRAISON] … » est un post de lane. Faute de pouvoir trancher,
            # il est ROUTE vers MANUAL_REVIEW au lieu d'etre ecarte.
            # Un humain peut aussi copier l'en-tête d'un dossier : ne jamais
            # écarter sa remarque sans revue.
            ambiguous = signature in {"head-tag", "astra-closure-preflight"}
            if signature and not ambiguous:
                excluded[signature] = excluded.get(signature, 0) + 1
                continue
            later = list(zip(comments[i + 1 :], kinds[i + 1 :]))
            candidates = [
                (other, kind)
                for other, kind in later
                if is_response_candidate(kind, other, comment)
            ]
            # Une remarque n'est pas un Concern : seule une citation FORTE
            # (horodatage, extrait de texte) la referme. Le mot « Concern » n'est
            # pas une forme de citation d'une remarque — ``proves`` avec
            # ``kind="other"`` n'accepte deja que la force forte.
            proof = None
            for other, _kind in candidates:
                if proves(comment, other, "other"):
                    proof = other.id
                    break
            if proof is not None:
                status = "REPONDU"
            elif candidates or ambiguous:
                status = "MANUAL_REVIEW"
            else:
                status = "NON REPONDU"
            remarks.append(
                RemarkFinding(
                    comment_id=comment.id,
                    created_at=comment.created_at,
                    excerpt=excerpt(comment.body),
                    status=status,
                    proof=proof,
                    act=remark_act(comment.body),
                    gesture_after=any(
                        kind == "gesture" and other.id != proof
                        for other, kind in later
                    ),
                )
            )

    if "external-unanswered" in classes:
        for i, comment in enumerate(comments):
            author = comment.author or ""
            if LANE_LOGIN.match(author) or BOT_LOGIN.search(author):
                continue
            later = list(zip(comments[i + 1 :], kinds[i + 1 :]))
            # Seule la flotte trie un commentaire externe (#20185 : « une
            # seule reponse publique porte le triage », par la flotte) : un
            # second auteur externe ni un bot d'integration ne sont des
            # candidats de reponse. La reponse attendue cite le commentaire
            # oublie — la machinerie forte (horodatage, extrait long) tranche,
            # comme pour une remarque.
            candidates = [
                (other, kind)
                for other, kind in later
                if LANE_LOGIN.match(other.author or "")
                and is_response_candidate(kind, other, comment)
            ]
            proof = None
            for other, kind in candidates:
                if proves(comment, other, kind):
                    proof = other.id
                    break
            if proof is not None:
                status = "REPONDU"
            elif candidates:
                status = "MANUAL_REVIEW"
            else:
                status = "NON REPONDU"
            externals.append(
                ExternalFinding(
                    comment_id=comment.id,
                    created_at=comment.created_at,
                    excerpt=excerpt(comment.body),
                    status=status,
                    proof=proof,
                    author=comment.author,
                    gesture_after=any(
                        kind == "gesture" and other.id != proof
                        for other, kind in later
                        if LANE_LOGIN.match(other.author or "")
                    ),
                )
            )

    return IssueReport(
        number=number,
        concerns=findings,
        remarks=remarks,
        reserves=reserves,
        externals=externals,
        excluded=excluded,
    )


# --------------------------------------------------------------------------- #
# Acces reseau
# --------------------------------------------------------------------------- #


def gh_json(args: list[str]):
    proc = subprocess.run(
        ["gh", *args], capture_output=True, text=True, encoding="utf-8"
    )
    if proc.returncode != 0:
        raise RuntimeError(f"gh {' '.join(args)} -> rc={proc.returncode}: {proc.stderr[:300]}")
    return json.loads(proc.stdout)


def list_issue_numbers(since: str, state: str) -> list[int]:
    query = f"repo:{REPO} is:issue updated:>={since}"
    if state == "open":
        query += " is:open"
    elif state == "closed":
        query += " is:closed"
    numbers: list[int] = []
    after = None
    while True:
        args = ["api", "graphql", "-f", f"query={GRAPHQL_SEARCH}", "-f", f"q={query}"]
        if after:
            args += ["-f", f"after={after}"]
        data = gh_json(args)["data"]["search"]
        numbers.extend(node["number"] for node in data["nodes"])
        page = data["pageInfo"]
        if not page["hasNextPage"]:
            return numbers
        after = page["endCursor"]


def fetch_comments(number: int) -> list[Comment]:
    out: list[Comment] = []
    page = 1
    while True:
        batch = gh_json(
            ["api", f"repos/{REPO}/issues/{number}/comments?per_page=100&page={page}"]
        )
        out.extend(
            Comment(
                id=item["id"],
                author=item["user"]["login"],
                created_at=item["created_at"],
                body=item.get("body") or "",
            )
            for item in batch
        )
        if len(batch) < 100:
            return out
        page += 1


# --------------------------------------------------------------------------- #
# Rendu
# --------------------------------------------------------------------------- #


def excluded_by_signature(reports: list[IssueReport]) -> dict[str, int]:
    """Ecart par signature de lane, agrege sur les rapports (#21621)."""
    totals: dict[str, int] = {}
    for report in reports:
        for name, count in report.excluded.items():
            totals[name] = totals.get(name, 0) + count
    return totals


def render_text(reports: list[IssueReport], since: str, state: str, scanned: int) -> str:
    unresolved = [(r, c) for r in reports for c in r.unresolved]
    total = sum(
        len(r.concerns) + len(r.remarks) + len(r.reserves) + len(r.externals)
        for r in reports
    )
    n_conc = sum(1 for _, c in unresolved if c.slug == "user-concern")
    n_res = sum(1 for _, c in unresolved if c.slug == "reviewer-reserve")
    n_ext = sum(1 for _, c in unresolved if c.slug == "external-unanswered")
    n_rem = len(unresolved) - n_conc - n_res - n_ext
    excluded = excluded_by_signature(reports)
    by_sig = ", ".join(f"{name} {count}" for name, count in sorted(excluded.items()))
    lines = [
        f"=== Remarques user sans reponse (issues {state}, depuis {since}) ===",
        f"{len(unresolved)} non resolu(s) — {n_conc} concern(s), {n_rem} "
        f"remarque(s), {n_res} reserve(s) de relecteur, {n_ext} externe(s) — "
        f"sur {total} recense(s), dans "
        f"{len({r.number for r, _ in unresolved})} issue(s) ; "
        f"{scanned} issue(s) lue(s) ; "
        f"{sum(excluded.values())} commentaire(s) ecarte(s) par signature de "
        f"lane ({by_sig or 'aucune'}).",
    ]
    if not unresolved:
        if sum(excluded.values()):
            lines.append("Aucun non resolu — les commentaires ecartes sont comptes en tete.")
        else:
            lines.append("Aucun — le fil est propre sur la fenetre.")
        return "\n".join(lines)
    grouped: dict[int, IssueReport] = {}
    for report, _ in unresolved:
        grouped.setdefault(report.number, report)
    ordered = sorted(
        grouped.values(),
        key=lambda r: (not r.gesture_after, min(c.created_at for c in r.unresolved)),
    )
    for report in ordered:
        flag = "  [gesture-after]" if report.gesture_after else ""
        open_concerns = [c for c in report.concerns if c.status != "REPONDU"]
        open_remarks = sorted(
            (r for r in report.remarks if r.status != "REPONDU"),
            key=lambda r: (_ACT_ORDER.get(r.act, 9), r.created_at),
        )
        open_reserves = [r for r in report.reserves if r.status != "REPONDU"]
        open_externals = [e for e in report.externals if e.status != "REPONDU"]
        lines.append("")
        lines.append(
            f"#{report.number} — {len(open_concerns)} concern(s), "
            f"{len(open_remarks)} remarque(s), "
            f"{len(open_reserves)} reserve(s), "
            f"{len(open_externals)} externe(s){flag}"
        )
        for finding in open_concerns + open_remarks + open_reserves + open_externals:
            proof = f" (piste c{finding.proof})" if finding.proof else ""
            if finding.slug == "user-concern":
                label = ""
            elif finding.slug == "reviewer-reserve":
                label = f"  [reserve {finding.marker}]"
            elif finding.slug == "external-unanswered":
                label = f"  [ext {finding.author}]"
            else:
                label = f"  [{finding.act}]"
            lines.append(
                f"  - {finding.created_at} c{finding.comment_id}  "
                f"{finding.status}{proof}{label}"
            )
            lines.append(f"      {finding.excerpt}")
    return "\n".join(lines)


def _ensure_utf8_output(stream) -> None:
    # Windows : un flux redirige utilise la page de codes ANSI (cp1252) et un
    # extrait d'emoji y crashe le print (UnicodeEncodeError, mesure 2026-10-30
    # apres lecture de 686 issues). La restitution du coordinateur (#20183)
    # passe par ce rendu a chaque cycle : la ligne [CONCERNS] ne doit pas
    # dependre de la page de codes de la machine qui la produit.
    if hasattr(stream, "reconfigure"):
        stream.reconfigure(encoding="utf-8", errors="replace")


def main(argv: list[str] | None = None) -> int:
    for stream in (sys.stdout, sys.stderr):
        _ensure_utf8_output(stream)
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--since", default="2026-09-25", help="issues mises a jour depuis (AAAA-MM-JJ)")
    parser.add_argument("--state", choices=["open", "closed", "all"], default="open")
    parser.add_argument("--issues", type=int, nargs="*", help="issues explicites (controles)")
    parser.add_argument("--as-of", help="figer le fil a cet instant (ISO, ex 2026-10-08T23:59:59Z)")
    parser.add_argument("--limit", type=int, default=0, help="ne lire que N issues (0 = toutes)")
    parser.add_argument("--jobs", type=int, default=8, help="lectures de fils en parallele")
    parser.add_argument("--json", action="store_true", help="sortie JSON")
    parser.add_argument(
        "--classes",
        default=",".join(CLASSES),
        help="classes a recenser, separees par des virgules (defaut : toutes les classes livrees)",
    )
    parser.add_argument("--fail-on-open", action="store_true", help="exit 1 si un constat reste ouvert")
    args = parser.parse_args(argv)

    requested = tuple(c.strip() for c in args.classes.split(",") if c.strip())
    unknown = [c for c in requested if c not in CLASSES]
    if unknown:
        print(
            f"classe(s) non livree(s) : {', '.join(unknown)} — disponibles : "
            f"{', '.join(CLASSES)} (les autres classes de #20185 viendront "
            f"chacune par sa PR)",
            file=sys.stderr,
        )
        return 2

    if args.issues:
        numbers = list(dict.fromkeys(args.issues))
    else:
        numbers = list_issue_numbers(args.since, args.state)
    if args.limit:
        numbers = numbers[: args.limit]

    cutoff = None
    if args.as_of:
        cutoff = datetime.strptime(args.as_of, "%Y-%m-%dT%H:%M:%SZ").replace(
            tzinfo=timezone.utc
        )

    print(f"lecture de {len(numbers)} issue(s)…", file=sys.stderr)

    def work(number: int) -> IssueReport:
        comments = fetch_comments(number)
        if cutoff is not None:
            comments = [c for c in comments if c.when <= cutoff]
        return analyse_comments(number, comments, requested)

    with concurrent.futures.ThreadPoolExecutor(max_workers=max(1, args.jobs)) as pool:
        reports = list(pool.map(work, numbers))

    # Les rapports qui ne portent QUE des ecarts sont conserves (#21621) : les
    # retirer ferait disparaitre du total publie les commentaires qu'on ecarte.
    reports = [
        r
        for r in reports
        if r.concerns or r.remarks or r.reserves or r.externals or r.excluded
    ]
    unresolved = sum(len(r.unresolved) for r in reports)
    excluded = excluded_by_signature(reports)

    if args.json:
        payload = {
            "since": args.since,
            "state": args.state,
            "as_of": args.as_of,
            "classes": list(requested),
            "issues_scanned": len(numbers),
            "concerns_total": sum(len(r.concerns) for r in reports),
            "concerns_unresolved": sum(
                1 for r in reports for c in r.concerns if c.status != "REPONDU"
            ),
            "remarks_total": sum(len(r.remarks) for r in reports),
            "remarks_unresolved": sum(
                1 for r in reports for c in r.remarks if c.status != "REPONDU"
            ),
            "reserves_total": sum(len(r.reserves) for r in reports),
            "reserves_unresolved": sum(
                1 for r in reports for c in r.reserves if c.status != "REPONDU"
            ),
            "externals_total": sum(len(r.externals) for r in reports),
            "externals_unresolved": sum(
                1 for r in reports for c in r.externals if c.status != "REPONDU"
            ),
            "unresolved": unresolved,
            "excluded_total": sum(excluded.values()),
            "excluded_by_signature": excluded,
            "issues": [
                r.as_dict()
                for r in sorted(
                    reports,
                    key=lambda r: (not r.gesture_after, r.number),
                )
                # Les rapports a ecarts seuls gardent leur entree : le total
                # publie les compte, l'entree montre par quelle signature.
                if r.unresolved or r.excluded
            ],
        }
        print(json.dumps(payload, ensure_ascii=False, indent=2))
    else:
        print(render_text(reports, args.since, args.state, len(numbers)))

    if args.fail_on_open and unresolved:
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
