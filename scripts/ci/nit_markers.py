"""La grammaire des marqueurs de l'organe B.0 (#27881, #26364 T5).

Ce module porte la **grammaire** de `scripts/check_unaddressed_nits.py` : les
familles de marqueurs de reserve (FORMELLE / PROSE), le vocabulaire des
verdicts de l'organe (glyphes de severite, verdicts de blocage, refus
d'approbation) et le predicte qui applique la separation FORMELLE/PROSE aux
commentaires de signalement.

Il est extrait de l'organe pour ne pas le faire grossir : le cliquet de
taille (`scripts/ci/script_size_ceilings.json`) epingle l'organe et son
module, et une baisse de l'un doit abaisser le plafond de l'autre. Une
extraction qui laisse l'organe au-dessus de son plafond ne rembourse rien.

Ce qui vit ici, et pourquoi
---------------------------
Les marqueurs FORMELS sont des **VERDICTS** : « CHANGES_REQUESTED », le glyphe
de severite, le refus d'approbation, la forme etiquetee « Concern: ». Les
marqueurs de PROSE sont des **LOCUTIONS** : « avant merge », « il va faudra »,
« a changer ». La PROSE sur-accuse d'un facteur 5 — c'est le motif meme pour
lequel #14682 a refuse d'ajouter des mots de prose « bloquante » au filet (le
contrat est cote EMISSION).

Pourquoi la separation est necessaire : un commentaire de SIGNALEMENT agent
(`[ACTION]` / `[DIAG]` / `[BASE-INHERITED]`) est, par construction, un
commentaire qui **PORTE** une action ou un constat — pas une reserve. Le
prefixe l'exempte deja de la classification, SAUF s'il « porte une reserve » —
et cette exception ne distinguait pas la PROSE du VERDICT.

Consequence mesuree (PR #27368, 2026-11-20) : le commentaire
`[ACTION] lane myia-ai-01:CoursIA-2` de la lane — qui dit « la PR merite un
regard de taille avant merge » — est classe BOT-CONCERN par le seul marqueur
de prose `avant merge`, et la PR est bloquee par SON PROPRE commentaire
d'action (29 h). C'est le regime absorbant decrit au founding incident
#16381, en miroir : la LIFT absorbait la reserve, ici c'est la PROSE qui
transforme le signalement en reserve — et personne ne peut lever une reserve
que la lane a posee elle-meme (B.0 : une reponse d'auteur ne leve pas une
reserve de tiers).

Le bouclage est donc : dans un commentaire de signalement, seule une reserve
FORMELLE reste un nit ; la PROSE seule ne bloque plus. Un verdict formel
l'emporte toujours (le tag n'est pas un passe-droit).

Usage
-----
    import nit_markers

    FORMAL = nit_markers.formal_concern_markers(CONCERN_MARKERS)
    live = nit_markers.signal_live_concern(
        live, stripped, surface, FORMAL, has_live_marker)

Les predicats de marquage (`has_live_marker`, `has_marker`) restent dans
l'organe : ils possedent les tables de normalisation (casse, citation, mot
borne) ; ce module n'en duplique aucune.
"""
from __future__ import annotations

import re
from typing import Callable, Iterable

# #12143 — Hermes severity glyphes (substance du premier PR #12148 fondateur).
# Extrait en constante separee pour subordonner la levee par LIFT_MARKERS
# (cf `classify` ci-dessous) : un glyphe est une EMISSION, et une emission
# ne se laisse pas eteindre par un mot de levee pose ailleurs dans la meme
# prose. Distribution scan 150 PRs mergees (35 reviews Hermes) :
#   △ (U+25B3) : micro-nit non-bloquant, 23/35 (exclu de CONCERN_MARKERS).
#   🟡 (U+1F7E1) : constat substantiel, 5/35. Promote car 4 leves par la suite,
#     1 NON levee = #12059 fondateur, defaut B.0 = merge avec constat sans
#     reponse, defaut pedagogique en production (hyperparametres GRPO contredits).
#   🔴 (U+1F534) : bloquant strict, 1/35 (vrai bloquant).
# #15951 — contrat de vocabulaire (acceptance 1 de l'issue) : le jeu de
# SEVERITE est FERME = {🟡, 🔴}. Les glyphes de NOUVEAUTE doctrinale des
# lanes (ex. « ★ NEW fondateur », vocabulaire Tell de po-2024:CoursIA-2)
# ne sont PAS des marqueurs de severite et ne le deviendront pas —
# severite et nouveaute restent DISJOINTS. Cote emission, une lane qui
# introduit un nouveau glyphe de severite doit le proposer ici avec une
# mesure corpus ; cote filet, aucun glyphe hors de SEVERITY_GLYPHS n'est
# lu comme alarme. Le defaut reel de #15762 c.1102 n'etait PAS le glyphe
# mais le verdict litteral en narration de dissipation avec attribution
# tell — cf `_MENTION_VERDICT_TELL` (Position K).
# `_unaccent` preserve les glyphes (categorie So, pas Mn), `_is_cited` reste
# symetrique via CITERS ascii. Les positions A-I (regex `_MENTION_VERDICT*`)
# ciblent l'ASCII formel et ignorent les glyphes ; la Position J
# (`_strip_glyphe_mentions`, #14277) les neutralise en position de MENTION
# (méta-nom sur la même ligne), l'émission en tête de ligne restant vive.
SEVERITY_GLYPHS = (
    "🟡",  # constat substantiel (fondateur #12059)
    "🔴",  # bloquant strict
)
# Concatene pour que `live_concern` (has_live_marker sur CONCERN_MARKERS) capture
# aussi les glyphes isoles — sans cette ligne, un body compose uniquement d'un
# glyphe (pas de LIFT, pas de CONCERN_MARKERS textuel) retournerait None a tort.

# #12908 — le verdict de l'organe B.0 lui-même, en ses deux formes d'EMISSION :
# le gras de revalidation (« classe encore cette PR **BLOCKED** », commentaire
# fondateur 2026-08-25T04:45:30Z de #12798) et la sortie pastee de l'organe
# (« BLOCKED  PR #N — ... », double espace). Ce commentaire fondateur
# maintenait explicitement la reserve (« quatre réserves tierces actives »,
# « réserve uniquement B.0/process ») tout en narrant le vocabulaire de levée
# (« une levée explicite sur le head final ») : le LIFT_MARKER « levée » de la
# narration absorbait la reserve vivante — le defaut exact que B.0 existe pour
# traquer. Comme les glyphes : concatene pour que `live_concern` classe le
# maintien BOT-CONCERN, ET subordonne la branche LIFT de `classify` via
# `_formal_concern_precedes_lift` (un BLOCKED emis AVANT la narration de
# levee garde la reserve vivante ; une levée suivie d'un BLOCKED narré au
# passe reste une levée — la position decide, comme pour les verdicts
# formels). Le mot NU « BLOCKED » n'est PAS matche : le tag de protocole
# « [BLOCKED] lane ... » d'une lane et la negation « n'est plus BLOCKED »
# restent hors du filet. Residuels assumes : un BLOCKED d'emission sans gras
# ni paste d'organe ne matche pas ; une paste dans un bloc de code fence est
# une mention (_strip_quoted), comme tout autre verdict backtinque.
BLOCK_VERDICTS = ("**BLOCKED**", "BLOCKED  PR")

# #14553 — le registre du REFUS d'approbation. Fondateur mesure : review
# NanoClaw du 2026-09-03T23:50:16Z sur #14535 — trois demandes numerotees,
# cloture « Donnees exactes, discipline de provenance en defaut — pas de
# LGTM en l'etat » -> AUCUN des marqueurs existants ne vit -> classify None
# -> gate vert. Un refus d'approbation est un verdict a part entiere (CLAUDE.md
# B.0 : « un reviewer qui ecrit "je ne peux pas approuver seul sur ce
# format" bloque ») ; aucun des 21 motifs ne couvrait cette famille. Casse
# RELACHEE (defaut has_live_marker) : « Pas de LGTM » en tete de phrase doit
# vivre. Garde-fou FP double : (1) la fenetre de citation (_is_cited) rend
# morte l'occurrence d'un refus QUOTE dans une levee (« la reserve
# « pas de LGTM » est adressee ») ; (2) « no LGTM » est word-bounded avec
# lookahead anti-« no LGTM needed » (_WORD_BOUNDED_MARKERS). « sous reserve
# de » est EXCLU : sa neutralite depend de la POSITION (verdict final vs
# subordonnee conditionnelle), qu'un motif ne peut pas porter — residuel
# documente sur l'issue.
APPROVAL_REFUSALS = (
    "pas de LGTM", "no LGTM",
    "je ne peux pas approuver", "cannot approve", "not approving",
    "ne pas merger en l'etat", "do not merge as is",
)


# Les LOCUTIONS de prose : une mention de reserve sans VERDICT.
PROSE_CONCERN_MARKERS = (
    "avant merge", "avant de merger", "il va falloir", "a nuancer", "à nuancer",
    "[BEFORE-MERGE]", "before merge", "a changer",
    "concerns about", "concerns remain",
)

# Les trois prefixes de SIGNALEMENT (et non l'ensemble des prefixes de
# protocole) : ce sont ceux que #26364 a ajoutes precisement pour que le
# signalement d'un agent ne bloque pas la PR qu'il documente.
SIGNAL_COMMENT_PREFIXES = ("[ACTION", "[DIAG", "[BASE-INHERITED")

# La forme STRICTE du tag (`[ACTION]` suivi d'un separateur), comme la
# taxonomie COMMENT_TAG_RE : `[ACTIONNEEDED` n'est pas un tag.
SIGNAL_HEAD_RE = re.compile(r"\[(ACTION|DIAG|BASE-INHERITED)\](?=\s|$)")


def formal_concern_markers(concern_markers: Iterable[str]) -> tuple[str, ...]:
    """Les marqueurs de reserve FORMELS : tous ceux qui ne sont pas de la prose.

    La liste de prose est un sous-ensemble du registre des marqueurs vivants
    (`CONCERN_MARKERS`) ; la famille formelle est donc **derivee**, jamais
    recopiee — une recopie deriverait en silence quand le registre bouge.
    """
    prose = set(PROSE_CONCERN_MARKERS)
    return tuple(m for m in concern_markers if m not in prose)


def signal_live_concern(
    live_concern: bool,
    stripped: str,
    concern_surface: str,
    formal_markers: tuple[str, ...],
    has_live_marker: Callable[[str, tuple[str, ...]], bool],
) -> bool:
    """Reserve qui survit dans un commentaire de SIGNALEMENT (#27881).

    `live_concern` est le verdict deja calcule sur TOUS les marqueurs. Dans un
    commentaire de signalement (`[ACTION]` / `[DIAG]` / `[BASE-INHERITED]`, forme
    stricte), la PROSE seule ne fait plus une reserve : le verdict est
    recalcule sur la seule famille FORMELLE. Un VERDICT formel reste un nit :
    le tag n'est pas un passe-droit.

    Le predicat de marquage (`has_live_marker`) est recu en parametre : il vit
    dans l'organe, qui possede les tables de normalisation (casse, citation,
    mot borne) ; ce module n'en duplique aucune.
    """
    if live_concern and SIGNAL_HEAD_RE.match(stripped):
        return has_live_marker(concern_surface, formal_markers)
    return live_concern
