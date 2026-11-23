#!/usr/bin/env python3
"""Les ITEMS que le tapis rapide ne sert plus : epuise ou sature (#26973).

Le tapis rapide ecarte un item par des barrieres **administratives** :
il est gele, une autre lane le tient, il a ete visite cette semaine. Il ne
savait rien dire de deux barrieres de **FOND**, mesurees sur le fil lui-meme :

1. **EPAISSE** -- le fil DECLARE que la part deleguable de l'item est
   epuisee. Cas #18258 : deux `[RELEASED]` successifs ecrivent « le reste de
   l'issue est expressement reserve au coordinateur, la part deleguable est
   epuisee », puis le tapis ressert l'EPIC a chaque lane (la regle `RELACHEE`
   ne tient que 3 jours). Le fil est ici l'autorite : c'est lui qui dit ce
   qu'il reste a faire dedans. La forme mesuree n'est PAS limitee aux
   conteneurs : #18258 n'en est pas un, et c'est pourtant le cas vise.

2. **SATURE** -- tous les ENFANTS du conteneur sont FERMES : il n'y a plus
   de grain a prendre dedans, le conteneur n'est pas un grain. Cas #11698
   (moissonnage QC) : 10 enfants « Part of #11698 » closes, aucun ouvert --
   et le tapis le sert encore, comme s'il avait une tranche a distribuer.

Les deux ecarteurs sont **fail-OPEN** : une mesure impossible (panne reseau,
lecture incomplette, motif illisible) rend l'ecart AUCUN -- le conteneur
reste servable. Un conteneur qu'on n'a pas su mesurer ne disparait pas du
pool.

Ce module ne lance aucun processus : la mesure des enfants passe par
`coordination.gh_recherche.chercher_enfants`, qui detient le transport.
"""
from __future__ import annotations

import re
import sys
import unicodedata
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from delivery_grammar import container_delivery_state  # noqa: E402

# --- La filiation : l'issue declare le conteneur comme son parent -----------
#
# La convention du depot : l'issue nomme son parent dans son corps
# ("Part of #N", "Sous-grain de #N", "Fille de #N", ...). C'est cette
# DECLARATION qui fait la relation -- un lien transversal ("voir #4208")
# ne fait pas un enfant.
#
# La liste est celle de `scripts/ci/check_umbrella_freshness.py`, completee
# de la forme « sous-grain de », tres employee par les grains QC (mesure :
# « Sous-grain de #11698 (Phase ...) »). L'organe CI garde sa propre liste :
# il ne s'agit pas de le rendre identique, mais de NE PAS reinventer la
# grammaire de filiation.
def motifs_filiation(numero: int) -> list[re.Pattern]:
    """Les formes de declaration de filiation vers `numero`."""
    n = numero
    return [
        re.compile(rf"part\s+of\s+#{n}\b", re.IGNORECASE),
        re.compile(rf"child\s+of\s+#{n}\b", re.IGNORECASE),
        re.compile(rf"issue\s+fille\s+de\s+(?:l['’]\s*)?(?:EPIC\s+)?#{n}\b", re.IGNORECASE),
        re.compile(rf"parent\s*:?\s*#{n}\b", re.IGNORECASE),
        re.compile(rf"(?:sous[-\s]grain|sous[-\s]issue|fille|fils|enfant|petite[-\s]fille"
                   rf"|petit[-\s]fils|anc[eê]tre)\s+de\s+(?:l['’]\s*)?(?:EPIC\s+)?#{n}\b",
                   re.IGNORECASE),
        re.compile(rf"grand[-\s]m[eè]re\s+(?:de\s+)?(?:l['’]\s*)?(?:EPIC\s+)?#{n}\b",
                   re.IGNORECASE),
    ]


def declare_filiation(body: str, numero: int) -> bool:
    """Ce corps declare-t-il `numero` comme son parent ?"""
    return any(pattern.search(body or "") for pattern in motifs_filiation(numero))


def enfants(candidats: list[dict], numero: int) -> list[dict]:
    """Les candidats qui sont des ENFANTS du conteneur (filiation declaree)."""
    return [c for c in candidats
            if not c.get("pr") and declare_filiation(c.get("body") or "", numero)]


def sature(numero: int, candidats: list[dict], complet: bool) -> str | None:
    """Le conteneur dont tous les enfants sont fermes : plus rien a prendre dedans.

    `complet` dit si la mesure a vu TOUS les candidats (pagination) : une
    mesure incomplete ne peut pas conclure -- fail-OPEN.
    """
    if not complet:
        return None
    fills = enfants(candidats, numero)
    if not fills:
        return None  # aucun enfant declare : le conteneur peut garder du travail
    if any(c.get("state") == "open" for c in fills):
        return None
    return (f"tous les enfants sont fermes ({len(fills)} enfant(s) declare(s), "
            f"aucun ouvert) : plus rien a prendre dedans")


# --- L'epuisement declare par le fil ----------------------------------------
#
# L'ATTESTATION canonique (`[INFO] candidate-delivered`) dit « le CONTENEUR
# est livre » : c'est la grammaire unique du depot
# (`delivery_grammar.container_delivery_state`), on l'IMPORTE, on ne la
# reecrit pas.
#
# Le [RELEASED] est plus heterogene : il peut dire « barriere reelle, je
# rends la main » (l'item reste servi) ou « la part deleguable est epuisee »
# (l'item ne doit plus remonter). Le predicat canonique
# (`released_covers`) reconnait la forme « acceptance deja couverte » ; la
# forme mesuree sur #18258 -- « la part deleguable de l'issue est epuisee »
# -- n'en fait pas partie. On l'ajoute ici, avec sa CONTEXTE : un mot
# d'epuisement seul (« le credit de la lane est epuise ») ne parle pas de
# l'item.
_RELEASED_RE = re.compile(r"^\s*(?:#{1,6}\s*)?\[RELEASED\](?=\s|:|$)", re.IGNORECASE)
#: Les marqueurs de fin de tour. On lit le DERNIER d'entre eux -- un
#: `[CLAIMED]` n'en est pas un : c'est une prise, pas une fin. Un `[RELEASED]`
#: suivi d'un `[CLAIMED]` reste donc le dernier mot : c'est precisement le
#: cycle fautif (#18258, reclame le 14/11 alors que l'epuisement etait
#: declare le 10/11).
_MARQUEUR_FIN_RE = re.compile(
    r"^\s*(?:#{1,6}\s*)?\[(RELEASED|DELIVERED)\b", re.IGNORECASE)
_MOTIF_EPUISEMENT_RE = re.compile(
    r"epuise\w*"
    r"|plus\s+rien\s+a\s+faire"
    r"|plus\s+rien\s+(?:restant|a\s+prendre|a\s+servir)"
    r"|aucun\s+grain\s+(?:restant|ouvert)"
    r"|plus\s+aucun\s+grain",
    re.IGNORECASE)
_CONTEXTE_RE = re.compile(
    r"(?:issue|grain|travail|tranche|partie|delegable|deleguable"
    r"|acceptance|conteneur|epic)",
    re.IGNORECASE)
#: La negation est cherchee explicitement (« l'acceptance n'est pas epuisee »).
_NEGATION_RE = re.compile(r"(?:pas|non|jamais)\s+(?:\w+\s+){0,2}epuise\w*", re.IGNORECASE)


def _sans_accents(texte: str) -> str:
    return "".join(c for c in unicodedata.normalize("NFD", texte)
                   if unicodedata.category(c) != "Mn")


def _released_covers(corps: str) -> bool:
    """`[RELEASED] ... acceptance deja couverte` -- le predicat canonique."""
    try:
        from released_covers import _released_covers_acceptance as predicat
    except Exception:  # noqa: BLE001 - module absent -> pas de signal
        return False
    try:
        return bool(predicat(corps))
    except Exception:  # noqa: BLE001 - predicat en faute -> pas de signal
        return False


def _motif_epuise(ligne: str) -> bool:
    """Cette ligne de [RELEASED] dit-elle que la part deleguable est epuisee ?"""
    normalise = _sans_accents(ligne).lower()
    if _NEGATION_RE.search(normalise):
        return False
    if not _MOTIF_EPUISEMENT_RE.search(normalise):
        return False
    return bool(_CONTEXTE_RE.search(normalise))


def _dernier_marqueur(comments: list[dict]) -> tuple[str | None, str, str]:
    """Le DERNIER marqueur de FIN de tour du fil : (marqueur, ligne, corps).

    Les commentaires sont lus a l'envers ; dans chacun, la premiere ligne qui
    porte un marqueur de fin le represente. Un `[CLAIMED]` n'est pas un
    marqueur de fin : une prise ne dit pas ou en est l'item. Un fil sans
    marqueur de fin rend (None, "", "").
    """
    for c in reversed(comments or []):
        corps = c.get("body") or ""
        for ligne in corps.splitlines():
            m = _MARQUEUR_FIN_RE.match(ligne)
            if m:
                return m.group(1).upper(), ligne, corps
    return None, "", ""


def epuise(e, comments: list[dict]) -> str | None:
    """Le fil declare-t-il l'item epuise ?

    Deux formes, mesurees sur le fil :

    * le CONTENEUR atteste sa livraison (`[INFO] candidate-delivered`) --
      c'est la grammaire unique du depot (`delivery_grammar`), on l'IMPORTE ;
    * le DERNIER marqueur de FIN de tour du fil est un `[RELEASED]` qui dit
      soit que l'acceptance est deja couverte (predicat canonique
      `released_covers`), soit que la part deleguable est epuisee (cas
      #18258 : « le reste de l'issue est expressement reserve au
      coordinateur, la part deleguable est epuisee »).

    La regle ne s'applique PAS au label EPIC : #18258 n'est pas un conteneur
    et c'est pourtant lui que la regle vise. Elle s'applique a tout item dont
    le fil se declare epuise -- et SEULEMENT lui : un `[DELIVERED]` posterieur
    dit que l'item a ete livre, il n'est donc plus epuise. Un `[CLAIMED]`
    posterieur ne l'annule pas : c'est lui, la RECLAMEE d'une autre lane, le
    symptome du cycle fautif.
    """
    bodies = [c.get("body") or "" for c in comments or []]
    if getattr(e, "conteneur", False) and container_delivery_state(bodies):
        return "le fil atteste la livraison du conteneur ([INFO] candidate-delivered)"
    marque, ligne, corps = _dernier_marqueur(comments)
    if marque != "RELEASED":
        return None
    if _released_covers(corps):
        return ("le fil rend la main en declarant l'acceptance couverte "
                "([RELEASED] ... acceptance deja couverte)")
    if _motif_epuise(ligne):
        return ("le fil declare la part deleguable epuisee "
                "([RELEASED] ... epuise)")
    return None


#: Les deux barrieres de **fond** : un item ecarte par l'une d'elles ne
#: revient PLUS dans le pool. C'est ce qui distingue un ecart administratif
#: (`GEL`, `RECLAMEE`, `LIVREE` -- l'item revient au tour suivant) d'une
#: **extinction** : l'item eteint n'est plus servi, et personne ne le ferme
#: s'il n'est pas nomme -- c'est ce que le tapis ecartait en silence.
CODES_FOND = ("EPAISSE", "SATURE")


def eteints(ecartees: dict) -> list[dict]:
    """Les items **eteints** par une barriere de fond, pour l'urne de cloture.

    Un ecart administratif se resorbe de lui-meme ; une barriere de fond est
    **definitive**. L'urne de cloture (coordinateur, adjoint) a besoin de la
    liste : un item eteint qui n'est pas nomme reste ouvert pour toujours.

    Chaque entree porte son numero, son CODE et le MOTIF de son extinction.
    """
    return [{"numero": item["numero"], "code": code, "motif": item.get("motif") or ""}
            for code in CODES_FOND
            for item in (ecartees.get(code) or [])]


def lignes_urne(eteints: list[dict]) -> list[str]:
    """Les lignes de la section « items eteints » de la sortie texte.

    La section est ecrite ICI, dans le module qui decide de l'extinction :
    le rendu (tapis_service) ne fait que l'ajouter a ses lignes.
    """
    if not eteints:
        return []
    lignes = [f"\nItems eteints ({len(eteints)}) -- urne de cloture "
              "(coordinateur, adjoint) : un item eteint ne revient pas dans le "
              "pool, il faut le fermer ou lui donner une tranche."]
    lignes += [f"  #{i['numero']}  {i['code']}  {i['motif']}" for i in eteints]
    return lignes


def ecarter_satures(tous: list, file: list, mesure, rebuild, max_passes: int = 3) -> list:
    """Ecarte les conteneurs satures de la file, puis RETIRE le tirage.

    La mesure porte sur les seuls conteneurs de la file (deux au plus) : le
    pool n'est pas sonde, il n'y a pas de budget a epuiser. Si un conteneur
    sature, le tirage est refait pour le remplacer par un grain reel.
    """
    for _ in range(max_passes):
        ecarte = []
        for e in [e for e in file if getattr(e, "conteneur", False)]:
            motif = _mesurer_saturation(e, mesure)
            if motif:
                e.ecart, e.motif = "SATURE", motif
                ecarte.append(e)
        if not ecarte:
            break
        file = rebuild()
    return file


def _mesurer_saturation(e, mesure) -> str | None:
    """Le verdict de saturation d'un conteneur ; fail-OPEN sur toute panne."""
    try:
        candidats, complet = mesure(e.numero)
    except Exception:  # noqa: BLE001 - une mesure qui rate n'ecarte rien
        return None
    try:
        return sature(e.numero, candidats or [], complet)
    except Exception:  # noqa: BLE001 - un predicat en faute n'ecarte rien
        return None
