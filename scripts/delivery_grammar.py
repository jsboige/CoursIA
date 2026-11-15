"""GRAMMAIRE de l'etat de livraison d'une issue -- source UNIQUE (#24461).

Pourquoi ce module existe
-------------------------
Deux organes lisaient la meme grammaire, chacun de son cote :

- le **tapis** (`scripts/pick_idle_grain.py`) : il decidait qu'une issue
  portant un marqueur de livraison etait **ecartee** du tirage des lanes
  workers ;
- le **poseur de label** (`scripts/candidate_delivered.py`) : il decidait
  qu'une issue livree **portait le label** `candidate-delivered`, et c'est
  ce LABEL qui rend le filtre du tapis gratuit.

Les deux grammaires divergeaient, et la divergence etait **structurelle** :
l'attestation d'une lane -- `[INFO] candidate-delivered`, la forme que le
protocole prescrit de poser en rendant la main -- armait l'etat du tapis
mais **n'arme jamais** le label, parce que `classify()` ne CLASSAIT le label
que sur une PR mergee portant `Closes`/`Fixes` (`partial` sinon) et sans
commentaire posterieur au merge. Resultat mesure le 2026-11-03 (#24461) :
**165 issues ouvertes portaient un marqueur vivant, 1 seule portait le
label**. Le tapis, lui, ecarte ces issues par une **sonde par issue**, donc
par un budget de sondes : quand le budget ou le mur de temps est atteint, le
tapis rend `fail-OPEN` et sert l'issue comme un grain neuf -- 37 des 120
grains servis par un tirage worker portaient un marqueur vivant.

Ce module est donc l'unique definition de la grammaire, et les deux organes
l'IMPORTENT. Il ne depend d'aucun module du depot hormis
`released_covers` (extrait de `pick_idle_grain` par #24082, sans dependance)
et `check_closure_dossier` (l'organe canonique du dossier de cloture,
charge paresseusement : son absence ne doit pas faire echouer l'import).

Ce qui est EXPORTE
------------------
- `DELIVERED_MARKER_RE`, `DELIVERED_MARKER_REVOKED_RE`,
  `ATTESTATION_MARKER_RE` / `CONTAINER_DELIVERY_MARKER_RE` : les grammaires
  de marqueurs, a l'identique de celles du tapis (memes regex, meme
  lookahead anti-`-revoked` / `-partial`).
- `delivery_state(bodies, *, lane_marker, dossier)` : l'etat du FIL apres le
  DERNIER evenement de livraison -- `"attested"` / `"revoked"` / `"none"`.
- `delivered_state(bodies)` : le booleen historique du tapis (grammaire
  large).
- `attestation_state(bodies, *, dossier)` : l'etat du fil pour le POSEUR DE
  LABEL (grammaire etroite).

L'ordre des evenements est celui du transport et il est CHRONOLOGIQUE :
l'appelant passe les corps dans l'ordre de l'API. Aucun tri n'est fait ici
-- en ajouter un ferait dependre le sens d'un champ que le transport REST ne
porte pas.
"""

from __future__ import annotations

import re

# --- Les formes de marqueur de livraison --------------------------------------
#
# 1. `[INFO] candidate-delivered`      (canonique, fermante `]`)
# 2. `[INFO candidate-delivered]`      (espace au lieu de `]`)
# 3. `[INFO] lane <machine:workspace> -- <sujet> -- candidate-delivered <suite>`
#                                      (annonce, le mot n'est pas immediatement
#                                      apres `[INFO` mais sur la meme ligne)
#
# La forme etroite : la 3e alternative exige `candidate-delivered` complete sur
# la MEME ligne qu'un `[INFO]` en tete, et un discriminant de classe
# (`lane <m:w>`, `signal`, `livre(e)`, `verification first-hand`) SUR LA MEME
# LIGNE -- sinon une mention discursive du mecanisme serait classee a tort
# comme marqueur de livraison.
#
# Ancrage en debut de ligne (`^\s*` + MULTILINE) : evite les mentions
# incidentes du type "sans [INFO] candidate-delivered". Le prefixe de TITRE
# markdown (`#{1,6}` + espaces optionnels) est tolere : un commentaire
# structure en sections ecrit couramment `## [INFO] candidate-delivered -- ...`.
#
# #20008 : la fermeture est un LOOKAHEAD `(?![-_\w])`, jamais un `\b`. Un `\b`
# pose apres `delivered` ne separe PAS `candidate-delivered` de
# `candidate-delivered-partial` (le tiret est un non-mot).
#
# La forme `[DELIVERED] lane <machine:workspace> -- PR #N` (c.15069) est une
# cloture explicite de LIVRAISON DE GRAIN : elle exige la forme canonique
# (`\s+lane\b`), et l'ancrage debut de ligne tient les citations
# `> [DELIVERED] lane` hors du match.
DELIVERED_MARKER_RE = re.compile(
    r"(?:"
    r"^\s*(?:#{1,6}\s*)?\[DELIVERED\]\s+lane\b"
    r"|"
    r"^\s*(?:#{1,6}\s*)?\[INFO\]\s+candidate-delivered(?![-_\w])"
    r"|"
    r"^\s*(?:#{1,6}\s*)?\[INFO\s+candidate-delivered(?![-_\w])[^\n\]]*\]"
    r"|"
    r"^\s*(?:#{1,6}\s*)?\[INFO\][^\n]*\b(?:lane\s+\S+:\S+|signal|livr[ée]e?|"
    r"verification first-hand)[^\n]*\bcandidate-delivered(?![-_\w])"
    r")",
    re.IGNORECASE | re.MULTILINE,
)

# Retractation du marqueur (mesure du 12/10 : sur 80 issues marquees livrees,
# 20 l'etaient partiellement). Deux formes, l'une et l'autre en TETE de ligne :
# une mention en prose (« ...et non [NOT-DELIVERED] dans ce fil ») ne retracte
# rien. La forme `[INFO] candidate-delivered-revoked` ne se relit PAS comme
# une livraison : le lookahead `(?![-_\w])` ferme `candidate-delivered` devant
# `-revoked`. Le sens est porte par l'ORDRE : une retractation defait les
# marqueurs posterieurs a elle, un marqueur repose apres elle rearme.
DELIVERED_MARKER_REVOKED_RE = re.compile(
    r"(?:"
    r"^\s*(?:#{1,6}\s*)?\[NOT-DELIVERED\]"
    r"|"
    r"^\s*(?:#{1,6}\s*)?\[INFO\]\s+candidate-delivered-revoked"
    r")",
    re.IGNORECASE | re.MULTILINE,
)

# L'ATTESTATION DE LIVRAISON PROPRE : les trois formes
# `[INFO] candidate-delivered`. C'est l'idiome que le protocole prescrit de
# poser en rendant la main -- « les criteres sont couverts, la main est
# rendue », verifie first-hand par la lane.
#
# #24461 residu (11/11) -- la forme `[DELIVERED] lane X -- PR #N` SANS clause
# `paths:` arme desormais AUSSI le label (via `attestation_state`, qui lit la
# meme machine d'etat que le tapis). L'exclusion historique (mesure 03/11 :
# #23778 portait ce marqueur ET une Concern du user) protegeait moins qu'elle
# ne coutait : le TAPIS traite deja cette forme comme une livraison vivante
# (`delivery_state`), donc l'issue sortait quand meme du tirage -- mais par
# une SONDE par issue, et le budget de sondes epuise rend fail-OPEN (mesure
# 11/11 : 76 des 120 grains servis aux workers portaient un marqueur vivant,
# dont ce marqueur). La protection REELLE d'un `[DELIVERED]` pose a tort est
# la REVOCATION partagee (`[NOT-DELIVERED]`, rearmable) -- celle qu'utilise le
# triage du secretariat (temoins #24393/#24461, 11/11). La forme AVEC clause
# `paths:` reste une TRANCHE : elle n'arme ni le tapis ni le label.
#
# C'est aussi, mot pour mot, le marqueur de CONTENEUR du tapis : sur une
# umbrella, `[INFO] candidate-delivered` dit « le CONTENEUR est livre ».
ATTESTATION_MARKER_RE = re.compile(
    r"(?:"
    r"^\s*(?:#{1,6}\s*)?\[INFO\]\s+candidate-delivered(?![-_\w])"
    r"|"
    r"^\s*(?:#{1,6}\s*)?\[INFO\s+candidate-delivered(?![-_\w])[^\n\]]*\]"
    r"|"
    r"^\s*(?:#{1,6}\s*)?\[INFO\][^\n]*\b(?:lane\s+\S+:\S+|signal|livr[ée]e?|"
    r"verification first-hand)[^\n]*\bcandidate-delivered(?![-_\w])"
    r")",
    re.IGNORECASE | re.MULTILINE,
)

# Le marqueur de CONTENEUR du tapis : le meme jeu de formes. Alias, pas copie
# (une seule definition, deux organes).
#
# Note de suivi de la revue Hermes (2026-11-03) : sur une UMBRELLA,
# `[INFO] candidate-delivered` dit « le CONTENEUR est livre », et le labeler
# classe alors par la branche `container` (exclusion ahead, testee) -- les
# deux noms pointeront donc toujours la meme regex, et les scinder
# casseraient la parite verifiee par test. Le comment est la, pour le
# lecteur futur qui aurait l'idee de les separer.
CONTAINER_DELIVERY_MARKER_RE = ATTESTATION_MARKER_RE

# La clause `paths:` d'une livraison de GRAIN (semantique v2 du claim,
# lane-claim-protocol) : `[DELIVERED] lane X -- PR #N -- paths: <glob>`
# livre une **TRANCHE**, pas l'issue ENTIERE (decision #24461 (c), point 3).
# La clause doit etre **SUR LA LIGNE DU MARQUEUR** : posee ailleurs (ligne
# suivante, autre commentaire) elle ne porte pas l'evenement -- c.2816 :
# `paths:` hors de la ligne du marqueur = claim epic-wide.
DELIVERED_LANE_MARKER_RE = re.compile(
    r"^\s*(?:#{1,6}\s*)?\[DELIVERED\]\s+lane\b[^\n]*$",
    re.IGNORECASE | re.MULTILINE,
)

PATHS_CLAUSE_RE = re.compile(r"\bpaths\s*:", re.IGNORECASE)

# Compatibilite du filtre rapide avec les en-tetes sans lane.
_RECENT_DELIVERED_RE = re.compile(
    r"^\s*(?:#{1,6}\s*)?\[DELIVERED\](?=\s|:|$)", re.MULTILINE)
_TRANCHE_DELIVERED_RE = re.compile(
    _RECENT_DELIVERED_RE.pattern, re.MULTILINE | re.IGNORECASE)

# --- Les trois etats d'un fil --------------------------------------------------

ATTESTED = "attested"   # le fil porte une attestation VIVANTE
REVOKED = "revoked"     # le fil porte une attestation RETIRACEE (la derniere)
NONE = "none"           # le fil ne porte aucune attestation


def closure_dossier_verdict(body: str) -> str | None:
    """Le VERDICT d'un dossier `[CLOSURE PREFLIGHT]` : "CLOSE", "KEEP" ou None.

    Deux verdicts portent un sens oppose pour le tapis :

    - **CLOSE** : la cloture est acquise, le dossier est TERMINAL (il
      n'expire pas -- la terminalite est portee par le reducteur, qui rend
      `stamp=None`) ;
    - **KEEP** : la cloture est EN COURS, l'issue n'est pas un grain de
      production (decision #24461 (c), point 2). Le dossier est VIVANT : il
      expire comme un marqueur de livraison (48 h, #22500), pour qu'un
      dossier oublie ne bloque pas l'urne indefiniment.

    L'organe canonique est `scripts/check_closure_dossier.py` : on l'IMPORTE,
    on n'en recopie pas la grammaire. Un dossier qui ne parse pas n'est PAS un
    signal : il est ignore (fail-OPEN), plutot que devine.

    Import paresseux et tolerant : l'organe peut etre absent du checkout
    reduit du cron (le sparse-checkout ne le declare pas) ; son absence ne
    doit pas faire echouer l'import du module.
    """
    if not body or "[CLOSURE PREFLIGHT]" not in body:
        return None
    try:
        from check_closure_dossier import parse_dossier
    except Exception:  # noqa: BLE001 - organe absent -> pas de signal
        return None
    try:
        dossier, errors = parse_dossier(body, 0, "", "")
    except Exception:  # noqa: BLE001 - parseur en faute -> pas de signal
        return None
    if dossier is None or errors:
        return None
    verdict = (dossier.fields.get("verdict") or "").strip().upper()
    return verdict if verdict in ("CLOSE", "KEEP") else None


def closure_dossier_close(body: str) -> bool:
    """Vrai si le corps porte un dossier `[CLOSURE PREFLIGHT]` de verdict CLOSE.

    Raccourci : `closure_dossier_verdict(body) == "CLOSE"`. La grammaire du
    dossier est celle de `closure_dossier_verdict` -- une seule definition.
    """
    return closure_dossier_verdict(body) == "CLOSE"


def delivery_marker_is_epic_wide(body: str) -> bool:
    """Ce corps atteste-t-il la livraison de l'issue ENTIERE ?

    Deux formes, deux sens :

    - `[INFO] candidate-delivered` et ses variantes : l'**ATTESTATION** de
      l'issue -- elle livre l'issue entiere ;
    - `[DELIVERED] lane X -- PR #N` : la livraison du GRAIN de la lane. Elle
      ne livre l'issue que si elle ne porte **pas** de clause `paths:` ; avec
      la clause, elle ne livre qu'une **TRANCHE** et l'issue reste servie
      (semantique v2 du claim, decision #24461 (c) point 3).

    La clause `paths:` doit etre sur la **ligne du marqueur** (c.2816) : une
    clause posee ailleurs ne porte pas l'evenement.

    Une attestation l'emporte sur une tranche : l'une dit « l'issue est
    livree », l'autre « ce grain est livre ».

    PLUSIEURS marqueurs dans UN corps se lisent comme PLUSIEURS
    evenements : le DERNIER ne l'emporte pas. Une livraison epic-wide
    posee avant une tranche n'est pas desarmee par elle -- « une tranche
    ne desarme rien » (#24461 (c), point 3). C'est la meme lecture que
    pour deux corps distincts, ou l'ordre des corps n'y change rien.
    """
    if not body:
        return False
    attested = False
    lane_epic = False
    for line in body.splitlines():
        if DELIVERED_LANE_MARKER_RE.match(line):
            lane_epic = lane_epic or not bool(PATHS_CLAUSE_RE.search(line))
            continue
        if ATTESTATION_MARKER_RE.match(line):
            attested = True
    return attested or lane_epic


def is_tranche_marker(body: str) -> bool:
    """Ce corps ne porte-t-il qu'une livraison de TRANCHE ?

    Une tranche ne livre pas l'issue : elle ne doit ni l'ecarter du tapis,
    ni poser d'heure de cloture. C'est la decision #24461 (c), point 3.

    « Que des tranches » : le corps doit porter **au moins un** marqueur de
    lane, et **tous** ses marqueurs doivent porter la clause `paths:`. Un
    corps qui melange une tranche et une livraison epic-wide n'est PAS une
    tranche -- c'est une livraison de l'issue entiere, plus une tranche.
    Le predicat est ainsi coherent avec `delivery_marker_is_epic_wide`,
    qui lit les memes marqueurs (une grammaire, deux lectures, aucun
    desaccord possible).
    """
    if not body:
        return False
    seen = False
    for line in body.splitlines():
        if _TRANCHE_DELIVERED_RE.match(line):
            seen = True
            if not PATHS_CLAUSE_RE.search(line):
                return False
    return seen


def is_tranche_only(body: str) -> bool:
    """Une tranche sans attestation de livraison de l'issue entière."""
    return is_tranche_marker(body) and not delivery_marker_is_epic_wide(body)


# Le separateur qui porte le motif dans une cause RENDUE. Il est defini
# ici, avec la grammaire, pour qu'aucune surface ne le recompose.
MOTIF_SUFFIX = "-- motif : "


def motif_class(cause: str) -> str | None:
    """La CLASSE du motif d'un ecartement, lue dans une cause rendue.

    Deux classes, les deux que la decision #24461 nomme :

    - ``living_dossier`` : un dossier `[CLOSURE PREFLIGHT]` VIVANT (KEEP) ;
    - ``epic_wide`` : une livraison de l'issue ENTIERE.

    La classe est lue dans le MOTIF lui-meme, jamais par une recherche de
    sous-chaine dans toute la cause : une cause « dossier CLOSE » porte
    aussi la chaine `CLOSURE PREFLIGHT`, et une sous-chaine la classait a
    tort comme « dossier vivant ».

    ``None`` = la cause ne nomme aucun motif (ecartement d'un autre
    genre, ou motif absent).
    """
    text = cause or ""
    if MOTIF_SUFFIX not in text:
        return None
    motif = text.split(MOTIF_SUFFIX, 1)[1]
    if "CLOSURE PREFLIGHT" in motif and "VIVANT" in motif:
        return "living_dossier"
    if "epic-wide" in motif:
        return "epic_wide"
    return None


def delivery_motif(bodies: list[str]) -> str | None:
    """Le MOTIF d'un ecartement de livraison, **nomme** (decision #24461, point 4).

    Ce que le tapis ecarte ne doit pas disparaitre : la cause rendue doit
    nommer le motif, pour que l'urne de l'adjoint (etape 6bis) puisse
    l'instruire sans re-deriver la grammaire. Deux motifs sont nommes :

    - un dossier `[CLOSURE PREFLIGHT]` **VIVANT** (verdict KEEP) : la
      cloture est en cours, l'issue n'est pas un grain de production ;
    - une livraison **epic-wide** : un `[DELIVERED]` sans clause `paths:`
      livre l'issue ENTIERE.

    Le fil est lu **a l'envers** : c'est le DERNIER evenement qui decide, et
    l'ordre du transport est chronologique. ``None`` = aucun motif (l'issue
    n'est pas ecartee pour un motif de livraison).

    Le motif est **coherent avec l'etat** : il ne nomme que ce qui ecarte
    ENCORE l'issue du tapis. Un fil retracte (`[NOT-DELIVERED]`,
    `candidate-delivered-revoked` en dernier evenement) rend l'etat
    ``revoked`` -- l'issue redevient servable -- et ne porte donc AUCUN
    motif de livraison : nommer « livraison epic-wide » sur un fil
    retracte, c'est annoncer une ecarte qui n'a plus lieu.
    """
    bodies = list(bodies or [])
    if delivery_state(bodies) != ATTESTED:
        return None
    for body in reversed(bodies):
        text = body or ""
        if closure_dossier_verdict(text) == "KEEP":
            return ("dossier `[CLOSURE PREFLIGHT]` VIVANT (verdict KEEP) : "
                    "la cloture est en cours, l'issue n'est pas un grain "
                    "de production.")
        if delivery_marker_is_epic_wide(text):
            return ("livraison epic-wide : un `[DELIVERED]` sans clause "
                    "`paths:` livre l'issue ENTIERE.")
    return None


def _released_covers_acceptance(body: str) -> bool:
    """`[RELEASED] ... acceptance deja couverte` -- une livraison au sens du tapis.

    Le predicat est importe de `released_covers` (extrait du picker par
    #24082, module sans dependance) : `[RELEASED]` a DEUX sens -- une lane
    rend la main sur une barriere reelle (rien n'a ete livre, l'item reste
    servable) ou elle signale l'acceptance deja couverte (l'item est livre).
    Reecrire cette distinction ici serait la deriver une deuxieme fois.
    """
    try:
        from released_covers import _released_covers_acceptance as predicate
    except Exception:  # noqa: BLE001 - module absent -> pas de signal
        return False
    return bool(predicate(body or ""))


def delivery_state(bodies: list[str], *, lane_marker: bool = True,
                   dossier: bool = True) -> str:
    """L'etat du FIL apres le DERNIER evenement de livraison.

    Un `any(...)` rendrait le marqueur permanent : une retractation
    posterieure ne pourrait plus remettre une issue partiellement livree sur
    le tapis (mesure du 12/10 : 20 des 80 issues marquees livrees etaient
    partielles). Ici le marqueur est un ETAT, et chaque corps est un
    evenement -- un marqueur de livraison rearme, une forme de retractation
    desarme ; c'est l'etat apres le DERNIER evenement qui est rendu. Un corps
    portant les deux est contradictoire et la retractation l'emporte (c'est
    le geste delibere, et c'est elle que cette machine d'etat doit rendre
    effective).

    Evenements d'arming :
    - `[INFO] candidate-delivered` (et ses variantes de forme) ;
    - `[DELIVERED] lane <machine:workspace> -- PR #N` SANS clause `paths:`
      (livraison epic-wide) -- gate ``lane_marker``, que le labeler ouvre
      aussi depuis le residu #24461 (11/11) ;
    - un dossier `[CLOSURE PREFLIGHT]` de verdict CLOSE (``dossier=True``) ;
    - `[RELEASED] ... acceptance deja couverte`.

    Evenements de desarming : `[NOT-DELIVERED]` et
    `[INFO] candidate-delivered-revoked`.

    Rend `"attested"`, `"revoked"` ou `"none"`.

    Le parametre ``dossier`` existe pour une raison de COHERENCE, pas de
    commodite : l'organe qui parse le dossier (`check_closure_dossier`)
    depend de `check_adjoint_prevalidation`, qui n'est pas dans le
    sparse-checkout du cron `candidate-delivered` (#23762 : le checkout
    reduit ne peut pas hosting l'organe). Si le labeler l'utilisait, le
    balayage local armerait le label d'un dossier CLOSE et le balayage CI
    non -- deux comportements pour le meme depot. Le labeler passe donc
    ``dossier=False`` : le dossier reste le signal de l'adjoint, et le
    tapis -- qui, lui, tourne sur le depot complet -- continue de le lire.
    """
    state = NONE
    for body in bodies or []:
        text = strip_code(body or "")
        if DELIVERED_MARKER_REVOKED_RE.search(text):
            state = REVOKED
        elif DELIVERED_MARKER_RE.search(text):
            # La forme `[DELIVERED] lane ... -- PR #N` : « la lane X a livre
            # SON grain ». #24461 residu (11/11) : elle arme desormais le
            # TAPIS **et** le LABEL quand elle est epic-wide (sans clause
            # `paths:`) -- l'ancienne exclusion protegeait moins qu'elle ne
            # coutait (le tapis ecartait deja l'issue par sonde budgetee ;
            # fail-OPEN servait le grain quand meme, mesure 76/120). La
            # protection d'un marqueur pose a tort est la REVOCATION partagee.
            #
            # Decision #24461 (c), point 3 : une livraison qui porte une
            # clause `paths:` ne livre qu'une TRANCHE -- elle n'arme NI le
            # tapis NI le label, et elle ne DESARME pas non plus une
            # livraison entiere anterieure (une tranche ne desarme rien).
            if (lane_marker or ATTESTATION_MARKER_RE.search(text)) \
                    and delivery_marker_is_epic_wide(text):
                state = ATTESTED
        elif dossier and closure_dossier_verdict(text) in ("CLOSE", "KEEP"):
            # Un dossier VIVANT (KEEP) ecarte l'issue comme un dossier CLOSE,
            # mais il EXPIRE (48 h, #22500) : la cloture est en cours, elle
            # n'est pas acquise.
            state = ATTESTED
        elif _released_covers_acceptance(text):
            state = ATTESTED
    return state


def delivered_state(bodies: list[str], *, dossier: bool = True) -> bool:
    """Le booleen historique du tapis : le fil atteste-t-il une livraison ?

    Raccourci : `delivery_state(bodies, dossier=dossier) == ATTESTED`.
    """
    return delivery_state(bodies, dossier=dossier) == ATTESTED


def attestation_state(bodies: list[str], *, dossier: bool = True) -> str:
    """L'etat du fil pour le POSEUR DE LABEL.

    #24461 residu (11/11) : meme grammaire d'arming que le TAPIS -- la forme
    `[DELIVERED] lane X -- PR #N` SANS clause `paths:` (livraison epic-wide)
    arme le label en plus des attestations `[INFO] candidate-delivered`. La
    forme AVEC clause `paths:` reste une TRANCHE : elle n'arme ni le tapis ni
    le label. Motif de l'elargissement : le tapis ecartait deja ces issues,
    mais par une sonde par issue -- budget epuise, fail-OPEN servait le grain
    quand meme (mesure 11/11 : 76/120). Le label, lui, est lu gratuitement
    dans le payload du pool. La protection d'un `[DELIVERED]` pose a tort est
    la REVOCATION partagee (`[NOT-DELIVERED]`, rearmable -- cf #24393/#24461).

    Deux differences avec `delivery_state` subsistent, toutes deux deliberes :

    - le parametre ``dossier`` : le labeler appelle avec ``dossier=False``
      (l'organe qui parse le dossier n'est pas dans son sparse-checkout,
      #23762) ; le tapis appelle avec ``dossier=True`` ;
    - aucune : sur tout le reste, les deux organes lisent la meme machine.

    Le predicat `released_covers_acceptance` reste inclus : `[RELEASED] ...
    acceptance deja couverte` est un verdict de LIVRAISON (« les criteres
    sont couverts »), la ou `[RELEASED] ... barriere` ne l'est pas.

    Rend `"attested"`, `"revoked"` ou `"none"`.
    """
    return delivery_state(bodies, lane_marker=True, dossier=dossier)


_FENCE_OPEN_RE = re.compile(r"^ {0,3}(`{3,}|~{3,})")
_INLINE_CODE_RE = re.compile(r"`{1,3}[^`\n]+`{1,3}")


def strip_code(text: str) -> str:
    """Retire les blocs de code (fences) et les code-spans inline.

    Le contenu retire est remplace par des lignes vides : la structure de
    lignes est conservee (le debut de ligne reste le debut de ligne), ce
    qui laisse le test des marqueurs **strictement** plus strict, jamais
    plus laxiste.
    """
    if not text:
        return text
    out: list[str] = []
    fence_char: str | None = None
    fence_len = 0
    for line in text.splitlines():
        match = _FENCE_OPEN_RE.match(line)
        if fence_char is None:
            if match:
                marker = match.group(1)
                fence_char = marker[0]
                fence_len = len(marker)
                out.append("")
                continue
            out.append(line)
        else:
            # La fence se ferme sur un marqueur du MEME caractere, au moins
            # aussi long que celui d'ouverture (CommonMark).
            if match and match.group(1)[0] == fence_char and len(match.group(1)) >= fence_len:
                fence_char = None
                fence_len = 0
            out.append("")
    stripped = "\n".join(out)
    return _INLINE_CODE_RE.sub(" ", stripped)


CLOSURE_ANNOUNCEMENT_RE = re.compile(
    r"^\s*(?:#{1,6}\s*)?Fermeture sur dossier\b[^\n]*?\bverdict\s+CLOSE\b",
    re.IGNORECASE | re.MULTILINE)

def recent_delivery_state(bodies: list[str]) -> bool:
    """Etat chronologique du filtre rapide, hors gel traite par le picker."""
    state = False
    for body in bodies or []:
        text = strip_code(body or "")
        if DELIVERED_MARKER_REVOKED_RE.search(text):
            state = False
        elif (delivered_state([text]) or CLOSURE_ANNOUNCEMENT_RE.search(text)
              or (_RECENT_DELIVERED_RE.search(text)
                  and not is_tranche_marker(text))):
            state = True
    return state

def container_delivery_state(bodies: list[str]) -> bool:
    """Etat chronologique des seules attestations de conteneur."""
    state = False
    for body in bodies or []:
        text = strip_code(body or "")
        if DELIVERED_MARKER_REVOKED_RE.search(text):
            state = False
        elif CONTAINER_DELIVERY_MARKER_RE.search(text):
            state = True
    return state
