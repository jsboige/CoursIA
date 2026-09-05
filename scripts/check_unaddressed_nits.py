#!/usr/bin/env python3
"""Gate pre-merge : aucun nit de review non leve ne doit survivre a un merge.

Pourquoi cet organe existe
--------------------------
Le champ `reviews[].state` est **structurellement aveugle** aux deux canaux de
review qui comptent le plus sur ce depot :

1. Le **user** poste ses nits comme *issue comments* (pas de review formelle) :
   il n'y a donc AUCUN `state` a lire — ni `CHANGES_REQUESTED`, ni meme une
   entree dans `reviews[]`.
2. **Hermes** (bot reviewer) poste ses reserves avec `state: COMMENTED` et le
   verdict en **prefixe de body** (`[Hermes] COMMENT_WITH_CONCERNS`) : lire
   l'etat renvoie `COMMENTED`, qui ne bloque rien.
3. Les **commentaires inline** de review vivent dans `reviewThreads` (GraphQL),
   une 3e surface absente de `gh pr view --json comments,reviews`.

Incident fondateur : PR #10761, mergee 2026-08-14T04:15Z malgre 2 nits user du
2026-08-13T11:07 (~17 h avant) et une review Hermes COMMENT_WITH_CONCERNS
confirmant les 2 nits + 3 points neufs dont « second reviewer obligatoire non
fourni ». `mergeStateStatus: CLEAN`, `reviews[].state: COMMENTED` : les deux
champs qu'un merge-gate lit d'ordinaire etaient verts.

Usage
-----
    python scripts/check_unaddressed_nits.py <PR>          # gate : exit 1 si bloque
    python scripts/check_unaddressed_nits.py <PR> --json   # sortie machine
    python scripts/check_unaddressed_nits.py --audit --limit 400   # audit retro

Ce qui leve un nit — et ce qui ne le leve PAS
---------------------------------------------
**Ce qui leve une remarque est une phrase, pas un SHA.** Un nit n'est considere
**leve** que si, entre son horodatage et le merge, on trouve au moins un de :
  - une **reponse ecrite** capable de repondre (cf `can_lift` : ni bot de CI,
    ni tag de protocole nu) ;
  - pour un thread inline : `isResolved: true` ou `isOutdated: true` ;
  - **de la bonne personne** (borne d'auteur #11145, durcie #12836) : l'auteur
    de la reserve. L'auteur de la PR ne peut pas lever lui-meme une reserve
    posee par un tiers — sa phrase documente une reponse, mais seule une
    re-review/levee du tiers confirme qu'il la tient pour traitee. Une reponse
    ou une approbation d'un autre tiers n'eteint pas davantage la reserve.
    L'echappement B.0 reste l'arbitrage ECRIT du coordinateur, par la trappe
    nommee `[OVERRIDE] lane <machine:workspace>` + phrase de levee (meme
    convention ecrite que les claims #10223). Pas une ouverture generale :
    la borne tient pour tout autre tiers, et un override POST-merge ne peut
    pas avoir eteint une reserve avant la decision de merge.

Le symetrique — #13083 : un coordinateur qui BLOQUE, direction que #11639 ne
traitait pas. Un blocage (`[BLOCAGE] lane ...` pose en tete de ligne, ou le
verdict `**BLOCAGE ...**` en tete de corps) ne se leve ni par l'auteur de la
PR ni par un compte qui, sous le self-review cap, est a la fois emetteur et
auteur : seuls l'arbitrage ecrit `[OVERRIDE] lane` ou l'emetteur reel (compte
distinct de l'auteur PR) levent. Detection structurelle, jamais une
sous-chaine — un adverbe intercale (« avant TOUT merge ») ne la rate pas.

Ne levent RIEN :
  - **un commit pousse apres le nit** : un push muet est indiscernable d'un push
    qui repond (sur #10761, le « traitement » etait un rebase qui n'adressait
    aucun des deux nits). Il est reporte comme contexte (`code_pushed_after`) ;
  - **un commentaire poste apres le merge** : c'est l'annonce de merge, pas une
    reponse — sans cette borne, le gate ratait son propre incident fondateur ;
  - **un commentaire de bot CI ou un tag de protocole nu** : ils ne repondent a
    rien, et sur ce depot ils sont postes a chaque push (defaut signale par
    Hermes en review de cet organe meme, cf `can_lift`).

Limite honnete de l'heuristique HUMAN
-------------------------------------
Le compte `jsboige` est utilise **a la fois** par le user et par les agents. Le
discriminant retenu est le **CRLF** : un commentaire redige dans l'UI web GitHub
porte `\r\n`, un commentaire poste via `gh` CLI porte `\n`. C'est fiable en
pratique sur ce depot mais ce n'est pas une preuve d'identite : un nit user
poste via `gh` serait manque (faux negatif), un agent collant du CRLF serait
signale a tort (faux positif). Le gate signale, l'humain tranche.

Limite honnete du CONDITIONAL_LIFT (#11201, resserree #12074)
-------------------------------------------------------------
La regex neutralise le marqueur « je merge » quand la construction est
conditionnelle. #12074 a resserre la neutralisation : un marqueur de levee
EXPLICITE par son auteur (« je leve ma reserve », « Levee de mon
CHANGES_REQUESTED ») EN AMONT du match conditionnel preserve le LIFT — « je
leve ma reserve et je merge » est la formulation naturelle d'une levee, le
« et je merge » n'y est que la consequence annoncee (comparaison d'offsets,
cf `_lift_cancelled`). Residuel assume : une annonce NON explicite (« c'est
bon, je merge ») coexistant avec une construction conditionnelle dans le meme
body reste integralement de-levee (faux positif possible) — rescaper « je
merge »/« Merge. » rouvrirait #11201 par la porte de service. La branche
« des » peut aussi matcher « je merge des PRs » (pluriel direct, pas « dès »).
Choix assume : le cout d'un faux positif (un flag a trier) est inferieur au
cout du faux negatif corrige ici (un nit invisible fondu dans sa propre
condition). Toute passe `--audit` lancee avant le 2026-08-16 a sous-compte :
elle est a rejouer.
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import unicodedata
from datetime import datetime, timezone

REPO = "jsboige/CoursIA"

BOT_LOGINS = {"github-actions", "codecov", "dependabot", "copilot-pull-request-reviewer"}

# Prefixes de tags utilises par les agents du cluster (protocole dashboard/PR).
AGENT_PREFIXES = (
    "[PART-OF-EPIC", "[GRAIN", "[CLAIMED", "[DONE", "[INFO", "[DISPATCH",
    "[ACK", "[RELEASED", "[OVERRIDE", "[MERGED", "[WARN", "[ERROR", "[ASK",
    "[REPLY", "[PROPOSAL", "[BLOCKED", "[ESCALATION",
)

# #11639 — l'arbitrage ECRIT du coordinateur. B.0 ne restreint pas l'auteur
# d'une reponse de levée (« une reponse ecrite sur la PR qui nomme la
# remarque »), mais `_lift_eligible` ne creditait que l'auteur du nit ou
# celui de la PR : tout arbitrage coordinateur laissait le gate rouge, et le
# merge se faisait a EXIT=1 en routine (#11479 — mesure : merge 13:06:39Z,
# override ecrit 13:07:40Z). La trappe est NOMMEE, pas generale : elle exige
# le marqueur de lane ecrit (`[OVERRIDE] lane <machine:workspace>`, meme
# convention ecrite que les claims #10223) ET une phrase de levee (LIFT_MARKER,
# deja exige par explicit_lifts) — un OVERRIDE nu ne leve rien. Les bornes
# temporelles restent entieres : un override POST-merge ne peut pas avoir
# eteint une reserve avant la decision de merge (borne #10761).
#
# #13316 — jsboige n'est PAS un compte de levee : c'est l'identite de poussee
# PARTAGEE de toutes les lanes (cf le commentaire #12319 de explicit_lifts :
# Hermes poste sous jsboige, la lane pousse sous jsboige). Crediter jsboige
# comme coordinateur retablit exactement ce que la borne d'auteur #11145
# interdit — n'importe quelle lane pose un `[OVERRIDE]` sous jsboige sur sa
# propre PR et eteint la reserve d'un tiers (#12737 : reserve ai-01 02:37:04Z,
# « overrides » jsboige 02:40/02:41 ; classe #12798, l'auto-levee). L'arbitre
# tiers de B.0 est la lane coordinateur dediee, et elle seule.
LIFT_OVERRIDE_LOGINS = {"myia-ai-01"}
# #13609 -- alias de persona Hermes/NanoClaw cross-login. La persona de
# reviewer Hermes parle sous DEUX logins -- clusterManager-Myia (reviewer
# principal) et jsboige (self-bot). Quand elle pose une reserve sous l'un
# puis leve sous l'autre, sa propre levee n'etait pas creditee par
# `_lift_eligible` (borne d'auteur stricte #11145 / #12836), et la reserve
# restait vivante : aucun geste de la lane ne pouvait la lever hors
# `[OVERRIDE]` coordinateur (coûteux, exige re-verif tierce, ne s'applique
# pas sur PR lane-coordinateur -- cf #13316). La composition des deux
# decisions est juste ; seule leur intersection est un faux negatif.
#
# On declare donc que les deux logins sont la MEME persona au sens de la
# borne d'auteur, mais UNIQUEMENT quand le corps du lifter porte un marqueur
# explicite `[Hermes]` / `[NanoClaw]` / `[Hermes self-bot]`. Sans marqueur,
# `jsboige` reste l'identite de poussee partagee des lanes (#13316) et un
# commentaire sans marqueur ne leve rien. LIFT_OVERRIDE_LOGINS reste
# inchange : un override `[OVERRIDE]` jsboige n'entre pas, alias de persona
# != droit d'override coordinateur.
PERSONA_ALIAS_LOGINS = {"clusterManager-Myia"}
_PERSONA_MARKERS_RE = re.compile(
    # #14503 (2e cause) : l'en-tete reel des personas peut etre en GRAS —
    # `**[NanoClaw]** structural review` (PR #14548). L'alternative `(?:^|\s)`
    # exigeait un debut de ligne ou une espace avant `[` : le `*` du gras
    # suffisait a effacer la review entiere du radar, AVANT meme la question
    # du verdict. `*` (gras/italique markdown) rejoint les debuts admis ;
    # le backtick reste EXCLU : `` `[Hermes]` `` est une citation (#13030).
    r"(?m)(?:^|[\s*])\[(?:Hermes|NanoClaw|Hermes self-bot)(?:\s+[^\]]*)?\]"
)
# #14503 — reserves enoncees en PROSE ordinaire par une persona, sans aucun
# prefixe de verdict (CONCERN_MARKERS muet). Jeu SERRE, mesure sur le corpus
# des 200 dernieres PRs mergees (controle 3 de l'issue) : le fail-CLOSED pur
# sur « persona + post-commit + sans verdict » attraperait 70 reviews dont la
# quasi-totalite sont des APPROBATIONS en prose (« Verdict : solide »,
# « validé », « exemplary fix ») — un mur, pas un durcissement. Les motifs
# ci-dessous attrapent les deux cas fondateurs (#14486 « défauts constatés »,
# #14548 « contredit ») et 0 des 70 approbations. « reproduit » et
# « à corriger » sont EXCLUS : usage positif dominant dans le corpus
# (« chaque chiffre du tableau se reproduit exactement »).
_PROSE_CONCERN_RE = re.compile(
    r"(?i)d[ée]fauts?\s+constat|m[ée]rite\s+une\s+it[ée]ration"
    r"|avant\s+c[âa]blage|contredit"
    r"|faux\s+n[ée]gatifs?|false\s+negatives?"
)
# #13030 -- le marqueur doit etre POSE, pas CITE. L'ancien pattern sans
# ancre matchait n'importe quelle mention dans le corps : le commentaire de
# la lane #12872 qui DOCUMENTAIT l'option « (b) `[OVERRIDE] lane x` par
# ai-01 » a eteint deux reserves BOT-CONCERN jamais levees (regex matchee
# dans le backtick, nom de lane capture avec le backtick parasite), et le
# gate est passe rc=0 sans que rien ne le signale. Un override fantome
# SOUS-bloque : la porte s'ouvre silencieusement -- inverse exact du
# [CLAIMED] fantome qui sur-bloque. Trois proprietes :
#   1. ancrage ^ (re.M) : le marqueur doit ouvrir la ligne (un tiret de
#      liste ou une phrase qui le precede = citation) ;
#   2. rejet de la forme encadree de backticks -- la citation canonique ;
#   3. lane capturee sans backtick parasite ( `\S+` avalait `CoursIA-2`` `).
# Decoration de debut de ligne toleree (même famille que _DECOR de
# check_lane_claim #10906 : `>`, `#`, `-` ne doivent pas voider un vrai
# override) -- mais le backtick AVANT le crochet reste une citation, seul
# le decor ASCII #>*+- l'est.
_OVERRIDE_LANE = re.compile(
    r"(?m)^[#>*+\-\s]*\[\s*OVERRIDE\s*\]\s+lane\s+([^\s`]+)",
)
OVERRIDE_LANE = _OVERRIDE_LANE

# #13083 — le symetrique de #11639 : un coordinateur BLOQUE aussi, et l'organe
# ne le modelisait pas. Même contrainte de pose stricte que le durcissement de
# la citation (#13030) : le marqueur est POSE — ancre debut de ligne (seule
# indentation toleree), hors backticks, hors puces markdown (`* `, `- `), hors
# blockquote (`>`), il n'est jamais POSE par une citation en milieu de phrase.
# La forme verdict-gras (`**BLOCAGE ...**` en tete de corps) est couverte par
# _block_emitted (2e branche), pas par ce pattern. La prose descriptive peut
# suivre sur la meme ligne. Alias anglais `[BLOCK] lane` pour les reviews
# ecrites en anglais. `[HOLD] lane` (#13779) : HOLD est le verbe que
# variation-protocol.md donne au coordinateur (« HOLD sans remplacement =
# echec coordinateur ») — entre crochets et en tete de ligne, il est aussi
# peu ambigu que les deux autres.
BLOCAGE_LANE = re.compile(r"(?m)^\s*\[(?:BLOCAGE|BLOCK|HOLD)\]\s+lane\s+\S+")

# #13779 — la forme VERDICT du HOLD coordinateur : le corps COMMENCE par HOLD,
# modulo l'emphase markdown (`**HOLD ...**`) et le titre (`## HOLD ...`). Deux
# resserrements par rapport a la pose de BLOCAGE (n'importe ou dans les 60
# premiers chars, casse indifferente), parce que « hold » est un mot ordinaire
# la ou « blocage » est deja presque toujours un verdict :
#   - POSITION : tete de corps, pas tete de fenetre — « je ne mets pas de hold
#     sur cette PR » ne pose rien ;
#   - CASSE : HOLD majuscule, la forme dans laquelle le protocole et les posts
#     du coordinateur l'ecrivent — « hold on, je regarde » ne pose rien.
HOLD_HEAD = re.compile(r"^[\s*_#]*HOLD\b")

# Marqueurs de reserve d'un reviewer bot (le verdict est dans le body, pas l'etat).
# #12311 — `REQUEST_CHANGES` (verbe, e.g. « [Hermes] Review — REQUEST_CHANGES »)
# complete `CHANGES_REQUESTED` (nom) : Hermes self-bot est force a state:COMMENTED
# par GitHub (PR sur son propre compte), donc son verdict = texte du body. Verifier
# les 2 formes couvre 9 corpus mesures (cf issue #12311), dont #12267 et #12288
# rendus mergeable a tort par l'absence du verbe. `has_live_marker` filtre les
# sous-chaines citees (CITERS ligne 455+), donc ajouter un verbe n'ouvre pas la
# porte aux faux positifs « 0 REQUEST_CHANGES » (#11916 controle negatif) :
# CITERS inclut deja « zero » et sera etendu de « 0 » (cf ligne ~470).
# #13559 — RESERVE SUR APPROBATION. #11677 a pose que la prose l'emporte sur
# l'etat natif `APPROVED` : « si classify() a deja retourne un kind, c'est
# qu'une reserve VIVANTE survit dans la prose ». L'intention est juste ; la
# mise en oeuvre laissait tout marqueur RESIDUEL renverser l'etat, y compris
# quand il n'est la que parce que la review NOMME la reserve qu'elle leve
# (« depuis mon CHANGES_REQUESTED sur `ae88aefc` », #13496 ; « Conversion de
# la reserve : CHANGES_REQUESTED (`21e0d810`) -> APPROVE », #13027).
#
# Mesure (30/08, 160 PR balayees, `state == "APPROVED"` + marqueur survivant
# a `_strip_mentioned_verdicts`) : **2 occurrences, 0 vraie reserve**. Les
# deux etaient des narrations retrospectives. Sur la fenetre mesuree,
# l'override avait donc un taux de vrais positifs NUL — il ne mesurait plus
# la reserve, il mesurait la mention.
#
# Le remede ne SUPPRIME pas l'override (le cas nomme par #11677, « j'approuve
# mais le point 2 reste ouvert », est reel et doit continuer de bloquer) : il
# lui demande une trace EXPLICITE de reserve. L'etat natif redevient decisif
# par defaut, la prose garde le dernier mot quand elle reserve vraiment.
# Volontairement LARGE : c'est le cote permissif du garde (il MAINTIENT le
# blocage), donc un faux positif ici ne coute qu'une phrase de levee, tandis
# qu'un trou coute un merge non mesure.
_APPROVE_RESERVATION_RE = re.compile(
    r"(?i)("
    r"sous\s+r[ée]serve"
    r"|avec\s+r[ée]serves?\b"
    r"|r[ée]serve\s+(?:maintenue|subsiste|demeure|tient)"
    r"|je\s+maintiens"
    r"|je\s+conserve\s+(?:ma|mon|la)\b"
    r"|(?:mais|toutefois|cependant|neanmoins|n[ée]anmoins)[^.\n]{0,120}?"
    r"\b(?:reste|restent|subsiste|subsistent|demeure|demeurent"
    r"|non\s+trait[ée]|non\s+lev[ée]|ouverte?s?|en\s+suspens)\b"
    r"|\b(?:[àa]\s+corriger|[àa]\s+traiter|[àa]\s+adresser)\s+"
    r"(?:avant|imp[ée]rativement)"
    r"|\bblocage\s+maintenu\b"
    r")"
)

# Sentinelle du marqueur ETIQUETE : une valeur inecrivable en prose, pour que la
# forme « Concern: » soit un marqueur A PART -- relachee en casse et en nombre --
# sans toucher a la sous-chaine « CONCERNS », qui reste case-sensitive.
_CONCERN_LABEL = "\x00concern-label"

CONCERN_MARKERS = (
    "COMMENT_WITH_CONCERNS", "CHANGES_REQUESTED", "REQUEST_CHANGES",
    "NEEDS_CHANGES", "CONCERNS",
    "SUSPECT_", "STRUCTURAL_ONLY", "SCOPE FLAG", "scope mismatch",
    "avant merge", "avant de merger", "il va falloir", "a nuancer", "à nuancer",
    # Miroir anglais de « avant merge » : fenetre 04-23..04-30 (triage po-2023,
    # #11044) — 2 faux negatifs mesures, PRs mergees sans aucune levee :
    # #594 « issues that should be addressed before merge » et #590
    # « CRITICAL — Must fix before merge ». Une seule addition couvre les deux.
    "before merge",
    # Fenetre 2026-08-16 (#11201) : le registre naturel d'un nit redige a la main.
    # Le commentaire 03:22:28Z de #11190 disait « Une seule chose a changer —
    # une ligne » sans AUCUN marqueur ci-dessus : une fois le faux negatif
    # « et je merge » neutralise (CONDITIONAL_LIFT), classify() le rendait
    # encore None. `_unaccent` fait matcher « a changer » et « à changer ».
    # Garde-fou FP : « rien a changer » nie le nit — le citer « rien »
    # (CITERS, ci-dessous) rend l'occurrence citee.
    "a changer",
)

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
CONCERN_MARKERS = CONCERN_MARKERS + SEVERITY_GLYPHS

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
CONCERN_MARKERS = CONCERN_MARKERS + BLOCK_VERDICTS

# La forme ETIQUETEE (« Concern: », « Concerns :», « **Concern 2 :** ») rejoint
# les marqueurs vivants : elle tolere casse et nombre des deux cotes (user comme
# agents) sans rien devoir a la sous-chaine nue, qui reste case-sensitive.
CONCERN_MARKERS = CONCERN_MARKERS + (_CONCERN_LABEL,)

# Un commentaire qui ANNONCE la levee ou le merge n'est pas un nit — il en est

# Un commentaire qui ANNONCE la levee ou le merge n'est pas un nit — il en est
# la resolution. Sans ce filtre, chaque « CHANGES_REQUESTED levée » est compte
# comme une reserve ouverte (faux positif massif, mesure sur 400 PRs).
LIFT_MARKERS = (
    "levée", "levee", "LGTM", "Mergé", "Merged", "je merge", "Merge.",
    "est adressé", "sont adressés", "sont levées", "est levée",
    # #13635 : les formes MASCULINES de la levee passive manquaient. Le depot
    # nomme ce qui se leve au masculin (« le concern », « le point », « le nit »)
    # — la phrase la plus naturelle pour lever un [BOT-CONCERN] (« tes concerns
    # sont levés ») echappait a LIFT_MARKERS, faux negatif. Miroir exact des
    # formes feminines ci-dessus : « sont levés », « est levé ». Ces marqueurs
    # passent par `_lift_is_negated` comme les autres (via `_live_lift_positions`),
    # donc une negation directe (« n'est pas levé ») reste exclue.
    "sont levés", "est levé",
    "Je lève", "Je leve", "Levée de", "Levee de",
    # #11677 : « je lève ma CHANGES_REQUESTED » (#11664 fondateur) — LIFT
    # historique ne captait que « levée » (mot complet), donc « lève ma » ne
    # matchait pas. Les 2 formes idiomatiques « je lève / je leve » ajoutent
    # la levee explicite d'une reserve par son auteur. Casse + accent
    # normalises par `_unaccent` (preserve la casse). CONDITIONAL_LIFT gere
    # l'aval (« corrige X et je leve » → la levee est conditionnelle, pas
    # acquise), comme deja pour « et je merge ».
    "je lève", "je leve",
    # #11542 : forme francaise SANS pronom en tete de phrase, avec un
    # verdict NON backquote — « Leve la CHANGES_REQUESTED de <auteur> ».
    # Le strip des verdicts cites (ci-dessus) couvre deja la variante
    # backquotee ; celle-ci lui echappe, et le marqueur de concern se
    # trouve alors *a l'interieur* de la phrase qui le leve.
    "lève la", "leve la", "Lève la", "Leve la",
    # #12944 : le close-the-loop Hermes (« Mon concern ... est traité et
    # fermé », PR #12941 fondateur, review 5020777166). Forme PASSIVE de
    # levee, verbes de FERMETURE uniquement (clos / fermé / résolu) plus
    # les composes « traité et fermé » qui couvrent le gras markdown
    # separant l'auxiliaire du participe (« est **traité et fermé** »).
    # La suggestion « est traité » nue de l'issue a ete REJETTEE sur
    # contre-exemple mesure : le body pinned #11639 « le point 3 est
    # traité en argument » (override NU qui ne doit rien lever) matcherait
    # — « traité » narratif se promene (« traité dans la section 4 »),
    # les verbes de fermeture s'engagent. Residu assume : une negation
    # INTERNE au compose (« pas encore traité et fermé ») le matcherait
    # (limite NLP documentee dans can_lift, pinne par
    # test_12944_residu_negation_du_compose_documente).
    "est clos", "sont clos", "sont closes",
    "est fermé", "sont fermés", "sont fermées",
    "est résolu", "sont résolus", "sont résolues",
    "traité et fermé", "traitée et fermée",
    "traité et clos", "traitée et close",
)

# Un LIFT en construction CONDITIONNELLE (« corrige X et je merge », « je merge
# quand… ») n'est pas une levee : c'est l'enonce de la condition bloquante
# (#11201). Le marqueur « je merge » couvre en effet deux sens opposes —
# « c'est bon, je merge » (annonce, levant) et « Change la ligne 19 et je
# merge » (condition, bloquant) — et le test LIFT_MARKERS passait AVANT toute
# recherche de reserve : le nit devenait invisible par la clause meme qui le
# rendait bloquant. On ne RETIRE pas le marqueur : sur les 7 occurrences
# conditionnelles mesurees dans les 60 dernieres PRs mergees, 4 etaient de
# vraies annonces (le retrait produirait des faux positifs). On annule son
# effet quand la construction est conditionnelle.
CONDITIONAL_LIFT = re.compile(
    r"(et je merge|puis je merge|ensuite je merge"
    r"|je merge (?:dès|des|une fois|quand|après|apres|si\b)"
    # #12319 — miroir exact des constructions « je merge » pour « je leve » :
    # « corrige X et je leve » est l'enonce de la condition, pas une levee
    # acquise. Le commentaire de LIFT_MARKERS le revendiquait deja ; le regex
    # ne couvrait que « je merge » — mesure par le test de regression
    # test_12319_levee_conditionnelle_ne_leve_pas_nit_commentaire.
    r"|et je l[èe]ve|puis je l[èe]ve|ensuite je l[èe]ve"
    r"|je l[èe]ve (?:dès|des|une fois|quand|après|apres|si\b))", re.I)

# #12074 — marqueurs de levee EXPLICITE par son auteur : quand l'un d'eux
# PRECEDE le match CONDITIONAL_LIFT, la construction n'est pas une condition —
# « je leve ma reserve et je merge » : la levee est acquise, le merge n'en est
# que la consequence annoncee. Distinct des annonces generiques (« je merge »,
# « Merge. ») : les rescaper rouvrirait #11201 (« corrige X et je merge »
# redeviendrait une levee). Miroir des entrees d'auteur de LIFT_MARKERS —
# casse preservee et accents normalises par `_unaccent`, comme pour ces
# derniers.
EXPLICIT_LIFT_MARKERS = (
    "Je lève", "Je leve", "je lève", "je leve",
    "Levée de", "Levee de", "levée de", "levee de",
    "Lève la", "Leve la", "lève la", "leve la",
)

# #11246 — use vs mention : CONDITIONAL_LIFT lisait les exemples CITES du motif
# comme des usages. Une review qui explique « corrige X et je merge » se
# flaggait elle-meme (2/15 findings de l'audit --limit 400 : les 2 seules
# reviews du corpus qui PARLENT du gate), et son annonce de merge reelle
# (« **Mergée.** ») etait annulee. On neutralise les segments cites AVANT la
# recherche de la construction conditionnelle — guillemets typographiques
# (« … »), backticks inline (`…`), blocs de code (``` … ```) — comme pour tout
# parseur qui ne doit pas lire ses propres exemples. La construction
# conditionnelle EMPLOYEE (« corrige la ligne 19 et je merge ») reste bloquante
# (#11201) : elle ne porte aucun de ces delimiteurs.
#
# #12315 — 4ᵉ reformulation de la même classe use-vs-mention, délimiteurs ASCII
# (apostrophe droite `'…'`, guillemet droit `"…"`). Cas fondateur #12266 :
# `c.457 lever le nit Hermes 'COMMENT_WITH_CONCERNS' -- clarification ecrite` —
# le verdict entre apostrophes droites ASCII était relu comme une mention nouvelle
# et le nit restait bloquant. On etend `_QUOTED_RANGES` A CONDITION que la charge
# utile soit VERDICT-SHAPED (`[A-Z][A-Z_]{2,}` minimum, sans whitespace ni
# délimiteur interne) — c'est la forme d'un nom de verdict, jamais celle d'une
# apostrophe d'élision française (`l'analyse`, `qu'il`, `n'est`, `c'est`,
# precedees d'une minuscule et suivies d'une minuscule ou d'un espace). Cette
# restriction discrimine naturellement les deux classes SANS risquer le piège
# de la regex naïve `'[^']*'` (le commentaire pointe : "Une regex naïve
# avalerait tout le texte entre deux apostrophes d'élision — potentiellement des
# paragraphes entiers").
#
# Portée et limite volontaire : on NE COUVRE PAS les chaînes apostrophees en
# minuscules (`'corrige X et je merge'`). La couverture plus large passe par
# piste 2 (généraliser par le verbe de levée plutôt que par le délimiteur, cf
# note de l'issue #12315) — le présent ticket ferme l'incident fondateur
# verbatim par delimiteur, et le test un-par-forme pin chaque cas pour ne pas
# régresser en silence.
_QUOTED_RANGES = re.compile(
    r"```.*?```|«.*?»|`[^`]*`|'[A-Z][A-Z_]{2,}'|\"[A-Z][A-Z_]{2,}\"",
    re.DOTALL,
)


def _strip_quoted(body: str) -> str:
    """Retire les segments cites (guillemets typo, backtick, bloc code)."""
    return _QUOTED_RANGES.sub(" ", body)


def _lift_cancelled(stripped: str) -> bool:
    """#12074 — le CONDITIONAL_LIFT n'annule le LIFT que si AUCUN marqueur de
    levee explicite d'auteur ne precede le match conditionnel.

    « **Je leve mon CHANGES_REQUESTED** et je merge. » s'auto-bloquait : le
    « et je merge » annulait le LIFT au niveau du body entier, le commentaire
    de levee etait re-compte comme un nit de plus, et la reserve qu'il levait
    redevenait vivante. Le discriminateur est la POSITION — ce qui PRECEDE le
    connecteur decide : antecedent imperatif (« corrige X et je merge ») =
    condition bloquante ; antecedent de levee accomplie = consequence
    annoncee. Les offsets sont compares sur la meme chaine passee par
    `_strip_quoted` : une levee CITEE (« ... ») ne rescape rien (use vs
    mention, #11246). `_unaccent` preserve la longueur, donc les offsets de la
    chaine stripee restent ceux de la chaine originale.
    """
    for m in CONDITIONAL_LIFT.finditer(stripped):
        if not has_marker(stripped[: m.start()], EXPLICIT_LIFT_MARKERS):
            return True
    return False

# #11636 — use vs mention, 2e reformulation de la classe #11246 : un rapport
# de correction qui NOMME le verdict qu'il corrige n'emet pas de reserve. Cas
# fondateur #11628 (mesure : le SEUL item bloquant du gate) :
#   « Fix review ai-01 (CHANGES_REQUESTED) — commit 06956bd0a. »
# Le nom du verdict est entre PARENTHESES, pas entre guillemets —
# `_strip_quoted` ne le voyait pas et aucun CITERS ne matche « review ai-01 ( ».
# L'incitation etait inversee : le rapport le PLUS precis etait classe
# BOT-CONCERN pendant qu'un « done » passait. Deux conditions CUMULATIVES,
# pour ne pas transformer une emission parenthesee en mention : (1) un
# verbe/locution de REFERENCE (fix, corrige, suite a, en reponse a, levee...)
# dans les 40 chars qui precedent la parenthese ouvrante — un nom d'agent peut
# s'intercaler, meme mecanique que l'attribution de `_is_cited` ; (2) un nom
# de verdict FORMEL `[A-Z][A-Z_]{3,}` immediatement entre parentheses.
# L'emission reelle reste « MARKER: » nue ou portee par le state de la review —
# les marqueurs naturels (« avant merge », « a changer ») ne sont pas des noms
# de verdict et restent hors de cette voie.
#
# #11744 — extension a 2 positions supplementaires : un verdict peut etre en
# mention (a) en TITRE de section `## ...VERDICT...`, ou (b) en prose INLINE
# apres un mot-cle de mention (« le verdict CHANGES_REQUESTED que je levais »).
# Les deux instances mesurees le 2026-08-19 : #11625 (« ## Remedes au
# CHANGES_REQUESTED » en tete de rapport de remediation, classe BOT-CONCERN
# comme si c'etait la SORTIE d'un verdict neuf) ; #11428 (« mon message
# d'approbation nommant le verdict qu'il levait, au fil du texte » — auto-
# bloquant apres que la levee par re-review APPROVED eut deja fonctionne).
# Compteur cumulatif : les 3 positions sont cumulees, pas OU-exclusives.
_MENTION_VERDICT = re.compile(
    r"(?i)\b(?:fix(?:ed|ée?e?)?|corrig\w+|suite\s+[àa]|en\s+r[ée]ponse\s+[àa]"
    r"|r[ée]ponse\s+[àa]|lev\w+|lift\w*|adress\w+|trait\w+|repondu\s+[àa])"
    # #12871 (cf grain) — Position A+ : tolere une prose INTERNE a la
    # parenthese du verdict (`(COMMENT_WITH_CONCERNS, porte sur...)`) tant
    # qu'elle ne commence pas par un verbe d'emission (`Verdict :`,
    # `Block on`...). Le mot declencheur de mention (fix/reponse a/leve/
    # adresse) porte deja la semantique de mention, et le verdict est
    # encapsule entre parentheses — donc le caractere distinctif (verdict
    # declare) est absent, c'est une mention par construction.
    # `(?-i:)` sur le verdict : sans lui, le `(?i)` global fait que
    # `[A-Z][A-Z_]{3,}` capture aussi un mot minuscule (`commit`) dans la
    # parenthese — et `[^()\n]{0,80}` apres (Position A+) transforme ce
    # faux match en neutralisation de `commit` au lieu du verdict (2 FAIL
    # tests #11809 mesures en CI, 2026-08-28). Même discriminant case-
    # sensitive que la Position D.
    # #13474 — la capture A+ est POSITIONNELLE : le PREMIER token en
    # capitales apres la parenthese ouvrante, pas « le token le plus proche
    # du verbe d'emission ». Consequence fail-loud : si un autre marqueur
    # majuscule precede le verdict dans la parenthese (ex `(BOT_CONCERTATION
    # a propos du BOT_CONCERN)`), c'est BOT_CONCERTATION qui est capture et
    # BOT_CONCERN reste emis — le garde reste bruyant.
    r"[^()\n]{0,40}\(\s*((?-i:[A-Z][A-Z_]{3,}))[^()\n]{0,80}\)")

# #12311 (cf grain) — Position A : titre de section. Le pattern historique
# (`[A-Z]{4,}` puis `[A-Z][A-Z_]{2,}[A-Z]`) neutralisait en sous-chaine les
# VERBES d'emission directe dans les titres, ex. « ## [Hermes] Review —
# REQUEST_CHANGES (...) » capturait `CHANGES` (7 majuscules) au sein de
# `REQUEST_CHANGES`. Hermes self-bot force a state:COMMENTED (#12311) ecrit
# son verdict dans le TITRE — neutraliser systematiquement le titre rend la
# detection aveugle exactement sur le canal qu'elle doit lire.
# Discrimination : un titre **avec prefixe agent reviewer** (`[Hermes]`,
# `[NanoClaw]`, `[Claude]`, `[Review]`, `[Hermes self-bot]`, etc.) est une
# EMISSION (le reviewer declare son verdict dans le titre). Un titre **sans
# prefixe** (ex. `## Remedes au CHANGES_REQUESTED`) est une MENTION (rapport
# de remediation qui evoque un verdict anterieur). On preserve le verdict
# uniquement dans le premier cas. Le tag agent est matche dans les 80 chars
# entre `##` et le verdict (cf limite d'origine).
# #13642 -- le garde d'origine `\[[A-Z][A-Za-z_-]{2,40}\]` n'acceptait que les
# tags UPPERCASE-initial (`[Hermes]`, `[NanoClaw]`, `[Claude]`) : le
# coordinateur, qui se tag `[ai-01]` / `[ai-01 ARBITRAGE]` (et le compte
# self-bot `[jsboige]`), est minuscule-initial et echappait au garde -> sa
# reserve en position de titre etait strippee en MENTION et devenait invisible
# au gate. Le vocabulaire est CLOS (reutilise tel quel, pas de caractere
# generique) : la classe symetrique `## [bug] CHANGES_REQUESTED` (categorie de
# prose, pas un reviewer) doit RESTER une MENTION et rester strippee.
_AGENT_REVIEWER_TAG = (
    r"\[(?i:(?:Hermes(?:\s+self-bot)?|NanoClaw|Claude|Review|"
    r"clusterManager-Myia|ai-01|jsboige|myia-ai-01)\b[^\]]*)\]"
)
_MENTION_VERDICT_HEADING = re.compile(
    r"(?m)^#{1,6}(?![^\n]*" + _AGENT_REVIEWER_TAG + r")[^\n]{0,80}?"
    r"([A-Z][A-Z_]{2,}[A-Z])(?![A-Za-z0-9_])")

# #11744 — Position B : prose inline. Un verdict est en mention quand un mot-
# cle de mention (`verdict`, `nit`, `remark`, `previous`, `previous`, `precedent`,
# `levee`, `levait`, `que je levais`, ...) le precede dans les 60 chars et
# qu'il N'est PAS suivi immediatement de « : » ou « . » qui marquerait une
# fin de phrase d'emission. Borne obligatoire : UNIQUEMENT les noms de
# VERDICT_FORMELS (les marqueurs naturels « avant merge » / « a changer »
# ne sont pas des noms de verdict).
_MENTION_VERDICT_INLINE = re.compile(
    r"(?i)(?:^|[\s,;:(])"  # frontiere de mot
    r"(?:nomm(?:e|ant|ation)|cit(?:e|ant|ation)|"
    r"verdict(?![:.])\s+\w+|d[ée]crivan?t|"
    r"(?:le|la|les|du|mon|ma|ces?\s+)?verdict(?![:.])|"
    r"que\s+je\s+lev\w*|que\s+je\s+lift\w*)"
    r"[^():\n.]{0,60}?(?-i:([A-Z][A-Z_]{3,}))(?![A-Za-z0-9_])")

# #11809 — Position C : verdict DEVANT le marqueur de levee. La forme
# naturelle d'une levee ecrite est « CHANGES_REQUESTED adresse (commit <sha>) »
# ou « SUSPECT_REGRESSION leve (PR #N) » : le verdict precede le verbe de levee,
# qui est suivi d'un identifiant pointant sur ce qui leve. Le marqueur CITERS
# couvre la negation (« No CHANGES_REQUESTED ») mais pas la mention positive :
# les motifs precedents (_MENTION_VERDICT, _MENTION_VERDICT_HEADING,
# _MENTION_VERDICT_INLINE) exigent tous que le marqueur de mention precede le
# verdict. La forme inverse restait comptee comme emission, et bloquait un
# merge sur une phrase qui dit exactement le contraire de ce que le garde en
# comprend.
#
# Le discriminant n'est pas la position du verdict mais **qui parle de quoi** :
# une levee pointe sur ce qu'elle leve (`(commit <sha>)`, `(PR #N)`,
# `(#<n>)`), une emission cree l'obligation. Le pattern exige donc, apres le
# verbe de levee, une **reference pointable** (commit SHA, PR/issue number,
# pull/<n>) entre parentheses immediates. Pas de reference = pas de match =
# le verdict reste emis (meme garde qu'avant, FP neutralise).
#
# Negocie avec les 3 motifs existants : ils utilisent deja `[ée]` pour tolerer
# les accents francais (cluster ecrit massivement sans accents), donc ici
# egalement. Les verbes de levee retenus sont ceux qui disent « j'ai adresse
# ce qui etait dans ce commit/PR » : `adresse(r)`, `traite(r)`, `repondu`,
# `leve(r)`, `lift`. Le `leve` couvre deja la serie `leve / levee / levees /
# lever / levees / leves`. `lift` garde la variante anglaise.
_MENTION_VERDICT_LIFTED = re.compile(
    r"(?<![\w/])([A-Z][A-Z_]{3,})\s+"
    r"(?:adresse|adresser|adressé|adressée|adressés|adressées"
    r"|traite|traiter|traité|traitée|traités|traitées"
    r"|repondu|répondu|repondre|répondre"
    r"|leve|lever|levé|levée|levés|levées|lift)"
    r"\w*"
    # #12871 (cf grain) — Position C+ : reference pointable NUE apres le verbe
    # de levee, dans une fenetre de 40 chars (les formes parenthesees
    # `leve (commit <sha>)` continuent de matcher ; les formes narratives
    # `leve par le commit <sha>` sont ajoutees). Borne courte (40 chars) pour
    # eviter d'avaler une autre phrase ou un commentaire distinct. Le
    # discriminant reste la piste (b) : une REF POINTABLE suit le verbe ;
    # sans pointable (CE2), la neutralisation ne s'applique pas.
    r"(?:\s+\((?:commit\s+[a-f0-9]+|#\d+|PR\s*#?\d+|pull/\d+)\)"
    r"|\s+(?:par|via|dans|en)\s+(?:le\s+|la\s+|les\s+|du\s+|des\s+)?"
    r"(?:commit\s+[a-f0-9]+|PR\s*#?\d+|#\d+|pull/\d+))")


# #11984 — Position D : le nominal `revue` / `review` DEVANT le verdict, avec
# reference pointable APRES. Cinquieme reformulation de la classe use-vs-
# mention (#11246 → #11636 → #11744 → #11809 → celle-ci) : les correctifs
# precedents portaient le nominal `verdict` (avec ses determinants) mais pas
# `revue`/`review`, la facon la plus naturelle d'ecrire la meme mention en
# francais comme en anglais. Instance fondatrice : #11911, commentaire du
# 2026-08-20T14:50:21Z — « La revue CHANGES_REQUESTED (07:32Z, SHA
# `5aa6e035`) pointait 2 defauts » — un rapport de re-review classe
# BOT-CONCERN comme s'il emettait la reserve qu'il rapporte.
#
# ELARGIR une neutralisation ouvre le sens dangereux : le faux negatif (une
# reserve reelle eteinte), failure mode fondateur de B.0 (#10761) — il ne se
# signale pas. Le discriminant n'est donc PAS le nominal seul — le contre-
# exemple de l'issue, « Cette review CHANGES_REQUESTED reste bloquante »,
# porte le nominal devant le verdict ET emet une reserve vivante. On exige
# la piste (a) de l'issue, calquee sur le precedent #11809 : une reference
# POINTABLE entre parentheses dans la suite immediate du verdict — SHA hex
# 7+, numero PR/issue, date ISO ou horodatage. Un rapport de correction
# designe l'evenement passe qu'il rapporte (`(07:32Z, SHA ...)`) ; une
# emission revendique sans pointer. Pas de reference pointable = pas de
# match = le verdict reste emis. Frontiere elargie a `*` : le mot est
# souvent en gras (« La **revue** CHANGES_REQUESTED »).
#
# #12944 — extension de position : la reference pointable HORS parentheses.
# Cas fondateur #12941 (review Hermes close-the-loop 5020777166) : « sur ma
# review REQUEST_CHANGES de #12900 (`ffe18961`) » — le numero de la PR/review
# source suit directement le verdict, sans parenthese. La forme d'origine ne
# voyait que la ref entre parentheses immediates, le verdict restait emis et
# `_formal_concern_precedes_lift` annulait meme la levee passive qui suivait.
# Meme discriminant que #11984 (le ref pointable designe l'evenement passe
# rapporte ; une emission ne pointe pas), position differente seulement.
_MENTION_VERDICT_REVIEW = re.compile(
    r"(?i)(?:^|[\s,;:(*])"  # frontiere (inclut * pour **revue**)
    r"(?:le|la|les|du|mon|ma|ce|cet|cette|ces|the|my)?\s*"
    r"(?:revue|review)(?![:.])"
    r"[^():\n.]{0,60}?(?-i:([A-Z][A-Z_]{3,}))(?![A-Za-z0-9_])"
    r"(?:"
    # Forme d'origine : ref pointable entre parentheses immediates.
    r"[^():\n.]{0,12}?"
    # #12871 (cf grain) — Position D+ : la ref pointable peut etre NUE dans
    # une fenetre bornee apres le verdict (les formes parenthesees
    # `(SHA ...)` continuent de matcher ; les formes narratives
    # `... par le commit <sha>` sont ajoutees). #13474 — la borne REELLE est
    # {0,12} chars de gap verdict->par/via/dans/en (temoin mecanique :
    # gap 12 matche, gap 13 ne matche plus — test_13474_* dans
    # test_check_unaddressed_nits.py) ; le long-format releve de la Position
    # E (fenetre 200). Borne courte volontaire pour ne pas avaler une autre
    # phrase distincte.
    r"(?:"
    r"\([^()\n]{0,80}?"
    r"(?:[a-f0-9]{7,}|#\d+|\d{4}-\d{2}-\d{2}|\d{1,2}:\d{2}(?::\d{2})?Z?)"
    r"[^()\n]{0,40}\)"
    # #12944 : ref pointable inline — « review VERDICT de #N ».
    r"|\s+(?:de\s+|sur\s+|dans\s+)?(?:la\s+|le\s+)?(?:PR\s+)?#\d+"
    r"|"
    r"(?:par|via|dans|en)\s+(?:le\s+|la\s+|les\s+|du\s+|des\s+)?"
    r"(?:commit\s+[a-f0-9]+|PR\s*#?\d+|#\d+|pull/\d+)"
    r"))")

# #12871 (cf grain) — Position E : `La review <VERDICT> ... traitee par le
# commit <sha>` (ou variantes). La Position D stricte echoue sur ce cas parce
# que la ref pointable est trop loin (plus de 12 chars apres le verdict, borne
# D+ ci-dessus, #13474), au-dela d'une frontiere de phrase `.`. Mais la phrase CONTIENT un verbe de levee
# suivi d'une ref pointable — c'est la signature d'une mention, pas d'une
# emission. Discriminant : on exige (a) `La review/ce <VERDICT>` en tete, (b)
# PAS de fin de phrase entre le verdict et le verbe de levee (donc sous la
# meme phrase), (c) verbe de levee + ref pointable a la fin. Borne dure : la
# phrase complete ne doit pas contenir `Verdict :` (emission formelle) ni
# `reste bloquante` (declaration de blocage) — implementee par le lookahead
# #13425 ci-dessous.
_MENTION_VERDICT_REVIEW_NARRATIVE = re.compile(
    r"(?i)(?:^|[\s,;:(*])"
    r"(?:le|la|les|du|mon|ma|ce|cet|cette|ces|the|my)?\s*"
    r"(?:revue|review)(?![:.])"
    r"[^():\n.]{0,60}?(?-i:([A-Z][A-Z_]{3,}))(?![A-Za-z0-9_])"
    # #13425 — la borne dure promise ci-dessus, desormais implementee : si la
    # suite de la phrase (fenetre 200 chars, meme phrase) contient une
    # declaration de blocage vivante (`reste bloquante`) ou une emission
    # formelle (`Verdict :`), la position ne s'applique PAS — le verdict
    # reste emis. Cas hybride fondateur : « Cette review CHANGES_REQUESTED
    # reste bloquante - traitee par le commit a1b2c3d4e » voyait son verdict
    # neutralise alors que la phrase declare le blocage vivant.
    r"(?![^.!?\n]{0,200}(?:reste\s+bloquante|verdict\s*:))"
    # Pas de fin de phrase avant le verbe de levee : `[^.!?\n]{0,200}` est
    # borne a 200 chars pour eviter de manger une phrase distincte (cf
    # discriminateur enonce par l'issue, le verbe de levee doit etre dans
    # la meme phrase).
    r"[^.!?\n]{0,200}?"
    r"(?:adresse|adresser|adressé|adressée|adressés|adressées"
    r"|traite|traiter|traité|traitée|traités|traitées"
    r"|repondu|répondu|repondre|répondre"
    r"|leve|lever|levé|levée|levés|levées|lift)\w*"
    r"(?:\s+(?:par|via|dans|en)\s+(?:le\s+|la\s+|les\s+|du\s+|des\s+)?"
    r"|\s+\()"
    r"(?:commit\s+[a-f0-9]+|PR\s*#?\d+|#\d+|pull/\d+)")


# #13512 (cf grain) — Position G : verbe de mention + verdict NU dans une
# fenetre bornee, SANS parenthese obligatoire ni `revue|review` en tete.
# Cas fondateur (PR #13496) : « @jsboige — reponse au REQUEST_CHANGES Hermes
# du 2026-08-29T17:33Z sur head `ae88aefc`. » — la forme naturelle d'une
# reponse a un verdict de reviewer : verbe de mention (`reponse a`/`fix`/
# `leve`/`corrige`/`traite`/`suite a`/`adresse`), puis le verdict NU (sans
# parentheses), puis contexte (auteur, date, head SHA). Les positions
# existantes (A-F) exigent soit des parentheses (A), un titre `##` (B), une
# prose avec mot-cle inline (C), un verbe de levee + ref pointable (D/E),
# ou `revue|review` en tete (D-F) — aucune ne couvre cette forme qui est
# pourtant la plus naturelle.
#
# Discrimination vs emission formelle :
# (1) Le caractere distinctif est la PRESENCE du verbe de MENTION (`reponse a`,
#     `fix`, `suite a`, `corrige`, `leve`, `adresse`, `traite`, `repondu a`,
#     `lift`) au lieu du verbe d'EMISSION (`Verdict :`, `Block on`, `declare`,
#     `reste bloquante`). Le verbe de mention ANNONCE une reponse, le verbe
#     d'EMISSION pose une reserve : le sens est inverse.
# (2) La fenetre `[^():\n.]{0,40}?` exclut `:` (donc `Fix : CHANGES_REQUESTED`
#     ne matche pas — `:` suit immediatement le verbe) et `.` (donc le verdict
#     doit etre dans la MEME phrase, pas apres une fin de phrase).
# (3) Verdict `(?-i:[A-Z][A-Z_]{3,})` case-sensitive : pas de capture d'un mot
#     natural-langue (`commit`, `commit`...) dans la fenetre.
#
# Mesure discriminatoire c.840 (corpus de validation) :
#   TP (match attendu) :
#     - "@jsboige — reponse au REQUEST_CHANGES Hermes du ..."
#     - "Voici le fix du CHANGES_REQUESTED pose par Hermes en review."
#     - "Suite au COMMENT_WITH_CONCERNS du 2026-08-29, voici le diagnostic."
#     - "Corrige SUSPECT_REGRESSION identifiee sur la branche main."
#     - "A leve le BLOCKED PR apres validation par ai-01."
#     - "Repondu au STRUCTURAL_ONLY via le commit 33ef4d6."
#   FN (ne doit PAS matcher) :
#     - "CHANGES_REQUESTED: edge case non couvert." (verdict nu en tete)
#     - "Verdict : CHANGES_REQUESTED sur ce commit." (verdict precede de "Verdict :")
#     - "Block on CHANGES_REQUESTED jusqu'a validation." (verdict precede de "Block on")
#     - "Fix : CHANGES_REQUESTED sur le ticket 1234." (`:` suit le verbe)
#     - "Je declare CHANGES_REQUESTED sur le diff." (verbe d'emission absent de la liste)
#     - "Le CHANGES_REQUESTED reste bloquante jusqu'a correction." (pas de verbe de mention)
#
# La borne 40 chars est calibree pour absorber #13496 (1 char mesuré entre
# `reponse au` et `REQUEST_CHANGES`) avec une marge de 39 chars. Une borne
# plus large rouvrirait le risque d'attraper une phrase distincte ; une borne
# plus etroite echouerait sur des variantes avec contexte immediat (un mot
# avant le verdict).
# #13512 fondateur — verbes resserres (Hermes demande 2/2, desiderata) :
# `lev\w+` devient `lev(?:e|é|ée|er|ons)\b` (exclut Levenshtein/lvgl/leve
# arabe/...) et `trait\w+` devient `trait(?:e|é|er)\b` (exclut trait-/traits/
# traitment/...). Les autres verbes de mention gardent leur `\w+` (leur
# variabilite naturelle est plus large : `corrige`/`corrigea`/`corrigeant`,
# `fix`/`fixe`/`fixer`, etc.).
#
# #13559 fondateur (PR #13560) — ajout d'un **negative lookahead**
# post-verdict `(?!\s*[—\-]\s+commit\b)` : la phrase « Fix review ai-01
# CHANGES_REQUESTED — commit 06956bd0a » est une **annonce de fix**
# (verdict suivi d'une reference a un commit futur), pas une **reponse**
# a un verdict (qui finit par contexte de reponse : Hermes, date, identifiee,
# via commit **passe**, ...). Le lookahead distingue les deux : apres le
# verdict, un `— commit` (= reference future) bloque le match. Les
# phrases de reponse (les 6 TP c.840 fondateur #13496 + variantes avec
# Hermes/date/identifiee/...) ne sont pas suivies de `— commit`, donc
# matchent toujours. c.845 regression fix.
_MENTION_VERDICT_BARE = re.compile(
    r"(?i)(?:^|[\s,;:(*]|@\S+\s+[—\-]\s+)"
    r"(?:fix(?:ed|ée?e?)?|corrig\w+|suite\s+[àa]|en\s+r[ée]ponse\s+[àa]"
    r"|r[ée]ponse\s+[àa]|lev(?:e|é|ée|er|ons)\b|lift\w*|adress\w+|trait(?:e|é|er)\b|repondu\s+[àa])"
    r"[^():\n.]{0,40}?(?-i:([A-Z][A-Z_]{3,}))(?![A-Za-z0-9_])"
    r"(?!\s*[—\-]\s+commit\b)")


# #14130 (cf grain) — Position H : rapport de verdict ATTRIBUE a un tiers, sans
# ref pointable obligatoire. Instance fondatrice (#14070) : « La review Hermes
# porte un CHANGES_REQUESTED que ma lane ne peut pas lever seule. » — un
# rapport de diagnostic sur l'etat d'une review tierce, pas une emission
# propre. Les positions A-G exigent soit une parenthese (A), un titre (B), une
# ref pointable (C/D/E/F), ou un verbe de mention + verdict (G) ; aucune ne
# couvre le rapport « la review X porte/comporte/contient/mentionne un
# VERDICT » qui est pourtant la formulation la plus naturelle d'un diagnostic.
#
# Discrimination vs emission formelle :
# (1) Attribution explicite a un tiers (Hermes / NanoClaw / ai-01 / jsboige /
#     myia-* / un nom propre) — sans attribution, le verdict est propre
#     (l'auteur l'emet), la position ne s'applique PAS.
# (2) Verbe DESCRIPTIF (`porte`, `comporte`, `contient`, `mentionne`,
#     `indique`, `signale`, `releve`, `contient`, `a emis`, `avait emis`, et
#     ext. #14185 `conclut`, `declare` — conclusifs/declaratifs acceptes
#     UNIQUEMENT sous attribution tierce + article, cf pattern) — un verbe
#     d'EMISSION (`Verdict :`, `Block on`, `reste bloquante`) n'est PAS
#     descriptif, c'est une emission, la position ne s'applique PAS.
# (3) Pas de declaration de blocage dans la suite de la phrase (meme garde
#     dure que Position E, ligne 645 : `reste bloquante` / `Verdict :` / `Block
#     on`) — sinon le verdict reste emis.
#
# Mesure discriminatoire (corpus c.840) :
#   TP (doit matcher, rendre None) :
#     - "La review Hermes porte un CHANGES_REQUESTED que ma lane ne peut pas lever seule."
#     - "La revue ai-01 contient un COMMENT_WITH_CONCERNS sur la sortie 12."
#     - "La review NanoClaw mentionne un SUSPECT_REGRESSION bloque en CI."
#     - "La review jsboige avait emis un STRUCTURAL_ONLY sur la note de parite."
#   FN (ne doit PAS matcher, doit rester BOT-CONCERN) :
#     - "Cette review CHANGES_REQUESTED reste bloquante." (pas d'attribution, pas de verbe desc.)
#     - "CHANGES_REQUESTED: edge case non couvert." (verdict nu en tete)
#     - "Verdict : CHANGES_REQUESTED sur ce commit." (verdict precede de "Verdict :")
#     - "Block on CHANGES_REQUESTED jusqu'a validation." (verdict precede de "Block on")
#     - "Je declare CHANGES_REQUESTED sur le diff." (verbe d'emission, pas descriptif)
#     - "La review CHANGES_REQUESTED reste vive." (verdict sans attribution, bloque)
_MENTION_VERDICT_REPORTED = re.compile(
    r"(?i)(?:^|[\s,;:(*])"
    # (1) determiner optionnel + revue|review
    r"(?:le|la|les|du|mon|ma|ce|cet|cette|ces|the|my)?\s*"
    r"(?:revue|review)(?![:.])"
    # Attribution a un tiers : Hermes / NanoClaw / ai-01 / jsboige / myia-XXX ou
    # un nom propre ([A-Z][a-z]+) precede de `de|du|des|par` ou simplement place
    # apres la review. La forme « la review Hermes porte » (sans preposition) est
    # la plus naturelle, on l'accepte ; « la review de Hermes » aussi.
    r"\s+(?:de\s+|du\s+|des\s+|par\s+)?"
    r"(?:Hermes|NanoClaw|jsboige|ai-?01|myia-[a-z0-9-]+|[A-Z][a-z][A-Za-z0-9_-]{0,30})"
    # (2) verbe DESCRIPTIF (ni METION comme G, ni EMISSION comme Hermes)
    r"\s+(?:porte|portes|portent|comporte|comportes|comportent"
    r"|contient|contiens|contiennent|contienta"
    r"|mentionne|mentionnes|mentionnent"
    r"|indique|indiques|indiquent"
    r"|signale|signales|signalent"
    r"|releve|releves|relevent"
    r"|a\s+emis|avait\s+emis|avaient\s+emis|ont\s+emis"
    # Ext. #14185 : verbes conclusifs/declaratifs sous attribution tierce —
    # « La review NanoClaw conclut un SUSPECT_REGRESSION » est un rapport de
    # verdict de tiers, pas une emission propre. Surs sous ce pattern car
    # l'attribution (1) et l'article (garde ce6) sont exigees en amont :
    # « Je declare CHANGES_REQUESTED » ne peut pas matcher (pas de
    # « review/revue » + tiers avant le verbe).
    r"|conclut|concluent|declare|declarent)"
    r"\s+(?:un|une|le|la|les|des|du)\s+"
    # Verdict case-sensitive (memes bornes que A-G)
    r"(?-i:([A-Z][A-Z_]{3,}))(?![A-Za-z0-9_])"
    # (3) garde dure : pas de declaration de blocage ni d'emission formelle
    # dans la suite de la phrase (200 chars, meme phrase)
    r"(?![^.!?\n]{0,200}(?:reste\s+bloquante|reste\s+vive|verdict\s*:|block\s+on))"
)


# #14199 (cf grain) — Position I : `avant merge` en position de mention (FP).
# Le marqueur `avant merge` est dans CONCERN_MARKERS comme signal d'un nit
# redige a la main, MAIS trois formes mesurees 2026-09-02 le portent en
# mention pure (pas en emission) :
#
#   1. **Qualifieur explicite non-bloquant** : « Concern (non bloquant) :
#      <details> à confirmer avant merge. Ball merge : <delegate>. » — le
#      qualifieur parenthese neutralise le nit, et le `Ball merge :` delegue
#      ailleurs. (PR #13537 fondateur.)
#
#   2. **Narration de verification prealable** : « Verifié de mon côté
#      avant merge : mergeStateStatus CLEAN, 0 check rouge. » — l'auteur
#      DECRIT un check qu'il a fait, pas un nit qu'il pose. (PR #13498
#      fondateur.)
#
#   3. **Formule de la voie B.0** : « levee par **issue de suivi ouverte
#      avant merge** (#N) » / « par la voie B.0 ... avant merge » — la
#      prose NOMME le mecanisme de levee B.0, elle ne pose pas un nit.
#      (PR #13860 fondateur.)
#
# Les Positions A-H utilisent toutes un verdict formel comme discriminant
# (`CHANGES_REQUESTED`, etc.). Position I est differente : la cible n'est
# pas un verdict mais le marqueur temporel `avant merge` lui-meme, qui est
# un CONCERN_MARKER a part entiere (L231). On ne peut donc pas utiliser
# la voie iso-longueur existante des verdicts — on neutralise directement
# le token `avant [le/la/l'] merge` (remplacement par espaces) dans les
# trois contextes mentionnes.
#
# Discrimination vs VP — ce qui doit rester bloquant :
#   - « A relire par ai-01 avant merge » (#13800 VP) : verbe ACTIONNEL
#     (`à relire`) deleguant une intervention — pas une verification
#     passee ni une delegation de merge.
#   - « a verifier avant merge » / « à corriger avant merge » : verbe
#     IMPERATIF a l'infinitif — l'auteur demande une action.
#   - « Concern (bloquant) a confirmer avant merge » : qualifieur
#     `(bloquant)`/`(urgent)` n'est PAS couvert par la liste (a) — il
#     reste un nit vivant.
#
# 7 sous-patterns (un par contexte FP, exactitude isolee ; review NanoClaw
# #14322 minor : compteur corrige) :

_MENTION_AVANT_MERGE_QUALIFIER = re.compile(
    r"(?i)"
    # Qualifieur explicite entre parentheses (200 chars gap)
    r"\((?:non[\s-]+(?:bloquant|bloquante|bloquants|bloquantes|blocker)"
    r"|mineur(?:s)?|optionnel(?:le)?s?|optiona(?:l|ux|les)?"
    r"|advisory|info(?:rmation)?(?:s|nel)?)\)"
    # Gap intra-phrase : point exclu (review NanoClaw #14322 concern 1) --
    # un aparte benin dans une phrase precedente ne neutralise pas un nit
    # VIVANT de la phrase suivante.
    r"[^.!?\n]{0,200}?"
    r"\bavant(?:\s+(?:le|la|l[\\']))?\s+merge\b"
)

_MENTION_AVANT_MERGE_VERIFIED = re.compile(
    r"(?i)"
    # Verbe de verification au passe compose / past participle (FR + EN)
    # suivi de 'de mon cote' / 'côté' optionnel, puis 'avant merge' (60 chars gap)
    r"(?:"
    # FR past p. (avec ou sans accent)
    r"v[éèe]rifi(?:[éèe]s?|e|ée|és|ées|er)?"
    r"|confirm(?:[éèe]s?|e|ée|és|ées|er)?"
    r"|contr[ôo]l(?:[éèe]s?|e|ée|és|ées|er)?"
    r")"
    r"\s+(?:de\s+(?:mon|ma|notre|leur)\s+)?c[ôo]t[éèe]?"
    r"[^.!?\n]{0,20}?"
    r"\bavant(?:\s+(?:le|la|l[\\']))?\s+merge\b"
)

_MENTION_AVANT_MERGE_VERIFIED_EN = re.compile(
    r"(?i)"
    # EN past participle (verified, checked, confirmed) + auteur optionnel
    r"\b(?:verified|check(?:ed|ée?s?)|confirm(?:ed|ée?s?))\b"
    r"(?:\s+(?:par|by|via)\s+\S+)?"
    r"[^.!?\n]{0,40}?"
    r"\bavant(?:\s+(?:le|la|l[\\']))?\s+merge\b"
)

_MENTION_AVANT_MERGE_PAST_PRECEDED = re.compile(
    r"(?i)"
    # Past p. immediatement avant 'avant merge' (3 chars gap max, allow space/punct)
    r"(?:"
    r"v[éèe]rifi(?:é|ée|és|ées)"
    r"|confirm(?:é|ée|és|ées)"
    r"|contr[ôo]l(?:é|ée|és|ées)"
    r"|verified"
    r"|check(?:ed)"
    r"|confirm(?:ed)"
    r")"
    r"[\s,;:.\\-]{0,3}"
    r"\bavant(?:\s+(?:le|la|l[\\']))?\s+merge\b"
)

_MENTION_AVANT_MERGE_PREFLIGHT = re.compile(
    r"(?i)"
    # Preflight / pre-flight check passe
    r"(?:pre[\s-]?flight|preflight)\s+(?:check|verified|passed|ok)"
    r"[^.!?\n]{0,20}?"
    r"\bavant(?:\s+(?:le|la|l[\\']))?\s+merge\b"
)

_MENTION_AVANT_MERGE_B0 = re.compile(
    r"(?i)"
    # Formule B.0 : 'issue de suivi ouverte ... avant merge' / 'voie B.N ... avant merge'
    r"(?:issue\s+de\s+suivi\s+(?:ouverte|ouvert|opened|open)"
    r"|voie\s+B\.\d+)"
    r"[^.!?\n]{0,80}?"
    r"\bavant(?:\s+(?:le|la|l[\\']))?\s+merge\b"
)

_MENTION_AVANT_MERGE_BALL = re.compile(
    r"(?i)"
    # 'avant merge' suivi de '. Ball merge : <delegate>' (delegation pattern)
    r"\bavant(?:\s+(?:le|la|l[\\']))?\s+merge\b"
    r"[^.!?\n]{0,30}?"
    r"\.\s*Ball\s+merge\s*:"
)

_MENTION_AVANT_MERGE_PATTERNS = (
    _MENTION_AVANT_MERGE_QUALIFIER,
    _MENTION_AVANT_MERGE_VERIFIED,
    _MENTION_AVANT_MERGE_VERIFIED_EN,
    _MENTION_AVANT_MERGE_PAST_PRECEDED,
    _MENTION_AVANT_MERGE_PREFLIGHT,
    _MENTION_AVANT_MERGE_B0,
    _MENTION_AVANT_MERGE_BALL,
)


# #13083 instance 3 — Position I' : `avant merge` en TETE de corps (titre),
# sans verbe actionnel ni qualifieur bloquant dans la meme ligne de titre.
# Le commentaire fondateur est du 2026-08-26T08:11:21Z sur #13083 : un
# compte-rendu d'audit ai-01 intitule « **Audit ai-01 avant merge** » etait
# classe BOT-CONCERN par `classify()`, bloquant la PR sur l'absence de
# reserve de l'auteur. Les 7 sous-patterns Position I (#14199) ne matchent
# pas : aucun qualifieur `(non bloquant)`, aucune verification passee
# (verifie/confirme/...), aucune formule B.0 (« issue de suivi ouverte
# avant merge »), aucune delegation Ball merge. Le `avant merge` en tete
# de corps est un **localisateur temporel pur** (« rapport a poser avant
# merge ») — pas un verdict.
#
# Discriminant vs VP : un titre qui contient `avant merge` ET un verbe
# d'action ou un qualifieur bloquant reste un nit (cf VP #13800 « A relire
# par ai-01 avant merge », VP « a verifier avant merge », VP « Concern
# (bloquant) : ... avant merge »). Les VPs ont TOUS un verbe actionnel /
# imperatif / qualifieur `(bloquant)`/`(urgent)` dans la meme ligne.
#
# Mesure : 1 PR FP (#12627 fondateur verbatim, commentaire 5422425135,
# 2026-08-26), 0 PR VP nouveau (les 7 VP Position I ont tous le verbe
# actionnel qui les garde vivants hors tete de corps, et la fenetre
# 2026-08-25..2026-09-02 ne montre aucun titre sans verbe actionnel).
#
# Architecture : sous-pattern (h) AJOUTE a `_MENTION_AVANT_MERGE_PATTERNS`,
# meme strategie de strip iso-longueur que les autres positions. Le
# sous-pattern matche UNIQUEMENT quand la ligne de titre (entre le debut
# du body et la premiere fin de ligne) contient `avant merge` ET NE
# contient PAS de verbe actionnel/imperatif ni de qualifieur bloquant.
_MENTION_AVANT_MERGE_HEAD_NEUTRAL = re.compile(
    r"\A[ \t]*"
    # Debut de body strictement (apres lstrip), pas de mode MULTILINE :
    # l'ancien `(?im)^` faisait matcher `^` au debut de CHAQUE ligne (cf
    # verification ai-01 2026-09-04 sur #14538, DM msg-20260904T011521-9d9p4k).
    # `\A` ancre au debut de la chaine, fermant le trou pour les occurrences
    # en milieu de corps (cf tests `test_13083_instance3_fp_milieu_*`).
    # La ligne peut etre precede de decoration markdown (`**`, `#`, `__`,
    # `### `, etc.) -- on accepte tout prefixe non-alphanumerique. La
    # limite `[^.\n]*?` empeche le saut a une ligne suivante.
    r"[^.\n]*?"
    # Le token `avant [le/la/l'] merge` ou `before merge` EN FIN de ligne de
    # titre (espaces optionnels avant, decoration markdown optionnelle,
    # puis fin de ligne / fin de body). Le lookahead plutot que `$` capture
    # correctement la fin de body sans exiger un `\n` final.
    r"\b(?:avant(?:\s+(?:le|la|l[\\']))?|before)\s+merge\b"
    r"(?=\s*[.*_~`:]*\s*(?:\n|\Z))"
)


def _is_action_verb_heading(heading_line: str) -> bool:
    """Une ligne de titre porte-t-elle un verbe actionnel ou un qualifieur bloquant ?

    Discriminant du sous-pattern (h) : si la ligne contient un marqueur
    d'action imperative ou un qualifieur (bloquant)/(urgent), le `avant
    merge` est un verdict (cf VPs Position I). Sinon, c'est un localisateur
    temporel pur (#13083 instance 3, FP #12627 fondateur).

    Le test se fait sur la ligne TOTALE (apres strip des decorations
    markdown `**`/`#`/`_`), pas seulement sur les mots autour de `avant
    merge` — un qualifieur en debut de titre (« Concern (bloquant) :
    <details> a confirmer avant merge ») doit garder le nit vivant.
    """
    cleaned = re.sub(r"[*_~`#]+", " ", heading_line).lower()
    cleaned = re.sub(r"\s+", " ", cleaned).strip()
    if not cleaned:
        return False
    # (a) Verbes d'action a l'infinitif / imperatif qui PRECEDENT `avant merge`
    # dans le meme titre. Liste bornee : 7 VP mesures (#14199) + EN imperatifs
    # (test #14199 corpus ajoute `must fix before merge` fondateur #590/#594).
    # Ajouter un verbe exige la meme procedure (mesure + sign-off) : aucun
    # elargissement opportuniste.
    if re.search(
        r"(?i)(?:[àa]\s+(?:relire|revoir|v[ée]rifier|corriger|confirmer|"
        r"traiter|adresser|regarder|relancer|confirmer|compl[ée]ter|"
        r"solutionner)|pri[èe]re\s+de\s+bien\s+vouloir|action\s+obligatoire|"
        r"action\s+requise|"
        # EN : `must fix`, `must change`, `must check`, `must address`,
        # `must verify`, `must resolve`. Sans `must` (juste `fix` ou `check`),
        # le mot reste ambigu (un substantif dans un titre -- `Fix check
        # before merge` n'a pas de verbe). Couverture EN miroir de la FR.
        r"must\s+(?:fix|change|check|address|verify|resolve|review|"
        r"rebase|re-execute|revisit|confirm|complete|solve))",
        cleaned,
    ):
        return True
    # (b) Qualifieur bloquant / urgent / non-couvert par Position I (a)
    if re.search(
        r"(?i)\((?:bloquant|bloquante|urgent|critique|important|prioritaire|"
        r"action\s+requise|breaking|major)\)",
        cleaned,
    ):
        return True
    # (c) Headings de pure emission formelle (verdict-prefix) — un titre qui
    # debute par un verdict ne peut pas etre un localisateur temporel pur
    # (meme raisonnement que `_block_emitted` Position I (b)).
    if re.match(
        r"(?i)\s*(?:reserve|r[ée]serve|nit|blocking|hold|bloquant|"
        r"changement?s?\s+requis|attention|warning|caution)",
        cleaned,
    ):
        return True
    return False


def _strip_avant_merge_mention(body: str) -> str:
    """Neutralise `avant merge` en position de mention (Position I, #14199)
    et en position de TETE de corps / titre (Position I', #13083 instance 3).

    Remplace le token `avant [le/la/l'] merge` par des espaces de meme longueur :
    les offsets du reste du body sont preserves, comme les autres strips.

    Cible : `avant merge` est un CONCERN_MARKER (L231) qui peut etre en
    mention (4 formes mesurees : qualifieur explicite non-bloquant, narration
    de verification passee, formule de la voie B.0, delegation Ball merge ;
    review NanoClaw #14322 minor : compteur corrige). Sans cette
    neutralisation, ces mentions sont classee BOT-CONCERN (FP).
    Position I' (#13083 instance 3, 2026-08-26T08:11:21Z sur #12627) : un
    localisateur temporel pur en tete de corps (« **Audit ai-01 avant
    merge** » dans un rapport de gate) etait classe BOT-CONCERN a tort,
    les 7 sous-patterns Position I ne matchant pas (aucun qualifieur /
    verification passee / formule B.0 / Ball merge).

    Anti-regression (acceptance #14199) :
    - 3 PR mesurees en FP doivent etre neutralisees : #13537 / #13498 / #13860
    - 7 VP de la fenetre 2026-08-25..2026-09-01 doivent rester signales :
      #13921, #13800, #13789, #13667, #13542, #13386, #13370.
      En particulier #13800 « A relire par ai-01 avant merge. Aucune action »
      ne matche aucun sous-pattern — verbe actionnel deleguant, pas une
      verification passee ni une delegation Ball merge.

    Anti-regression (acceptance #13083 instance 3, present fix) :
    - 1 PR FP #12627 fondateur (commentaire 5422425135, 2026-08-26T08:11:21Z)
      doit etre neutralisee : « **Audit ai-01 avant merge** » + prose
      descriptive (verdict qui DECRIT un check passe, pas un nit).
    - VP garde-eux : tout titre contenant un verbe actionnel (`a relire`,
      `a verifier`, `a corriger`, `a confirmer`, ...) ou un qualifieur
      `(bloquant)` / `(urgent)` doit RESTER BOT-CONCERN.
    """
    for pat in _MENTION_AVANT_MERGE_PATTERNS:
        # Le token cible est le `avant [le/la/l'] merge` (non capture, neutralise integralement)
        # La longueur du token est variable (`avant merge` = 11, `avant le merge` = 14, etc.)
        body = pat.sub(
            lambda m: re.sub(r"\bavant(?:\s+(?:le|la|l[\\']))?\s+merge\b",
                             lambda mm: " " * (mm.end() - mm.start()),
                             m.group(0)),
            body,
        )
    # Phase Position I' (#13083 instance 3) : `avant [le/la/l'] merge` /
    # `before merge` en TETE de corps, titre sans verbe actionnel ni
    # qualifieur bloquant. Le strip est post-Position I pour beneficier du
    # strip anterieur, mais il est distinct : il neutralise une occurrence
    # de tete qui n'aurait pas ete atteinte par les 7 sous-patterns en
    # milieu de phrase.
    body = _MENTION_AVANT_MERGE_HEAD_NEUTRAL.sub(
        lambda m: (
            # Garde-fou : si la ligne de titre porte un verbe actionnel /
            # qualifieur bloquant, NE PAS neutraliser (VP).
            re.sub(
                r"\b(?:avant(?:\s+(?:le|la|l[\\']))?|before)\s+merge\b",
                lambda mm: " " * (mm.end() - mm.start())
                if not _is_action_verb_heading(m.group(0))
                else mm.group(0),
                m.group(0),
            )
        ),
        body,
    )
    return body


# #14277 — Position J : glyphe de sévérité en position de MENTION. Les
# SEVERITY_GLYPHS (🟡/🔴) sont concaténés dans CONCERN_MARKERS mais restent
# invisibles aux positions A-H (regex `_MENTION_VERDICT*` ciblant l'ASCII
# formel) : un compte-rendu technique qui NOMME le glyphe qu'il décrit est
# classé BOT-CONCERN à tort. 3 FP mesurés (sweep 264 corps / 61 PRs,
# fenêtre 2026-08-23..2026-09-02 ; 0 VP glyph-only sur la même fenêtre) :
#   FP1 (#13951 c.869, issuecomment-5506801880) : « variante glyphe 🟡. »
#   FP2 (#13951 c.872, issuecomment-5507737699) : « 2 cas (prose
#        contradictoire + glyphe 🟡) ajoutes. »
#   FP3 (#13951 c.871) : « les **glyphes de severite** (🟡 constat
#        substantiel #12059, 🔴 bloquant) »
#
# Discriminateurs LIGNE-PORTÉS (le glyphe est une mention si l'un des deux
# tient sur sa ligne) :
#   (A) MÉTA-NOM — un nom nommant le glyphe précède sur la même ligne
#       (« glyphe 🟡 », « glyphes de severite (🟡 ..., 🔴 ...) », FP1-3).
#   (B) ITEM D'ÉNUMÉRATION — le glyphe est immédiatement précédé d'un
#       séparateur `,` ou `+` (modulo espaces) : « (prose, 🟡, 🔴, +
#       controle positif) », cellule de tableau « **CWC + 🟡** » (formes
#       résiduelles de FP3, 5503423343).
# L'émission réelle (mesurée #12059 / #12083 / #12077 — scan 35 reviews
# Hermes de #12143) est un en-tête de verdict en tête de ligne (« **🟡
# FINDING — ... », « LGTM structural / 🟡 ... »), jamais un item de liste :
# ni méta-nom avant, ni séparateur `,`/`+` immédiat — le séparateur `/`
# (VP #12083) est délibérément EXCLU du set d'énumération. Substitution
# iso-longueur (1 char -> 1 espace) : les offsets du reste du body sont
# préservés, comme les autres strips.
_GLYPH_META_NOUN_RE = re.compile(
    r"(?i)\b(?:glyphes?|glyphs?|marqueurs?|markers?|badges?|symboles?|emojis?)\b"
)
_GLYPH_ENUM_PRECEDER_RE = re.compile(r"[,+]\s+$")
_SEVERITY_GLYPH_CLASS_RE = re.compile(f"[{''.join(SEVERITY_GLYPHS)}]")


def _strip_glyphe_mentions(body: str) -> str:
    """Neutralise les glyphes de sévérité en position de mention (Position J, #14277).

    Chaque glyphe (🟡/🔴) dont la ligne porte un méta-nom le nommant (A) ou
    qui est un item d'énumération `,`/`+` (B) est remplacé par une espace :
    c'est une mention, pas une émission. Le glyphe en tête de ligne
    (en-tête de verdict Hermes) reste vivant.
    """
    out = list(body)
    for m in _SEVERITY_GLYPH_CLASS_RE.finditer(body):
        line_start = body.rfind("\n", 0, m.start()) + 1
        prefix = body[line_start:m.start()]
        if (_GLYPH_META_NOUN_RE.search(prefix)
                or _GLYPH_ENUM_PRECEDER_RE.search(prefix)):
            out[m.start()] = " "
    return "".join(out)


def _strip_mentioned_verdicts(body: str) -> str:
    """Neutralise les noms de verdict cites en position de mention (#11636, #11744, #11809).

    Remplace le verdict par des espaces de meme longueur : les offsets du
    reste du body sont preserves (les fenetres de `_is_cited` restent
    calibrees sur la vraie position des occurrences survivantes).

    Position G (#14070) beneficie du garde anti-negation : un match
    Position G dont la fenetre 15 chars avant/apres contient un token
    `_LIFT_NEGATION_TOKENS` (`ne...pas`, `plus`, `jamais`, `non`, `aucun`,
    `sans`, `n'est`, `rien`) est preserve (le verdict reste cite dans
    le body — l'organe `classify()` peut alors le voir comme un nit non
    leve). Voie canonique d'application : `_lift_is_negated(window_before,
    window_after)`, symetrie exacte avec la logique existante sur
    `_LIFT_MARKERS`. Les 6 autres positions restent en `sub` iso-longueur
    direct (elles n'ont pas de garde anti-negation homologue — leur
    discrimination par contexte est suffisante).
    """
    # Phase 1 : sub iso-longueur pour les 6 patterns historiques (pas de
    # negation — leur discrimination par contexte est suffisante).
    for pat in (_MENTION_VERDICT, _MENTION_VERDICT_HEADING, _MENTION_VERDICT_INLINE, _MENTION_VERDICT_LIFTED, _MENTION_VERDICT_REVIEW, _MENTION_VERDICT_REVIEW_NARRATIVE, _MENTION_VERDICT_REPORTED):
        body = pat.sub(
            lambda m: m.group(0).replace(m.group(1), " " * len(m.group(1))), body)
    # Phase 1b : Position I — neutralise `avant [le/la/l'] merge` en position
    # de mention (#14199). Cible differente des autres positions : ce n'est
    # pas un verdict formel mais un token CONCERN_MARKER (`avant merge`)
    # qui peut apparaitre en mention (qualifieur explicite / verification
    # passee / formule B.0 / delegation Ball merge). Voir
    # `_strip_avant_merge_mention` pour la justification des 7 sous-patterns.
    body = _strip_avant_merge_mention(body)
    # Phase 1j : Position J — neutralise les glyphes de sévérité (🟡/🔴) en
    # position de mention (#14277). Cible distincte des positions A-H : pas
    # un verdict ASCII formel mais un glyphe concaténé dans CONCERN_MARKERS,
    # invisible aux regex de mention. Discriminateur ligne-portée : voir
    # `_strip_glyphe_mentions`.
    body = _strip_glyphe_mentions(body)
    # Phase 2 : Position G avec garde anti-negation (Hermes demande 1/2,
    # PR #14070). Approche `finditer` car le verdict-match n'est pas en
    # bord de phrase (la mention `traite le REQUEST_CHANGES` met le
    # verdict a 10-20 chars du verbe de mention). On cherche un token de
    # negation n'importe ou dans la window 15 chars avant/apres, avec
    # strip des separateurs de bord (coherence avec `_lift_is_negated`
    # qui regarde les bords).
    # NOTE : on n'utilise PAS `_lift_is_negated` directement ici — ce
    # helper regarde uniquement les BORDS de la window (le token `pas`
    # doit finir la window avant OU commencer la window apres). Or
    # Position G matche la mention `... pas traite le REQUEST_CHANGES`
    # ou `pas` est AU DEBUT de win_before, pas en bord : helper naturel
    # mais inadapte. Helper dedie ci-dessous.
    negates_spans: list[tuple[int, int]] = []
    for m in _MENTION_VERDICT_BARE.finditer(body):
        verdict_start = m.start(1)
        verdict_end = m.end(1)
        win_before = body[max(0, verdict_start - 15):verdict_start]
        win_after = body[verdict_end:verdict_end + 15]
        if _bare_mention_is_negated(win_before, win_after):
            negates_spans.append((m.start(), m.end()))
    if negates_spans:
        def _bare_sub(m: re.Match[str]) -> str:
            for s, e in negates_spans:
                if m.start() == s and m.end() == e:
                    return m.group(0)  # garde le verdict intact (negated)
            return m.group(0).replace(m.group(1), " " * len(m.group(1)))
        body = _MENTION_VERDICT_BARE.sub(_bare_sub, body)
    else:
        # Aucun negation detectee — fast path iso-longueur comme avant.
        body = _MENTION_VERDICT_BARE.sub(
            lambda m: m.group(0).replace(m.group(1), " " * len(m.group(1))), body)
    return body


# #13083 (2e instance) — mention nominale au generique : « une formule de
# levee conditionnelle », « ses conditions de levee », « une levee reelle »
# (#12896 c.5422312669, verbatim). Un determiner DEVANT le mot (genitif « de »,
# article indefini « une ») en fait un nom : la prose NOMME le concept de
# levee (metalinguistique), elle ne l'emets pas. Distinct des annonces
# « Levée de <x> » (EXPLICIT_LIFT_MARKERS) ou le « de » suit le mot —
# l'annonce reste une emission. La premiere implementation de cette PR
# (regex `_NOMINAL_LIFT_RE` + `_strip_nominal_lifts`, iso-longueur) a ete
# FUSIONNEE au rebase 2026-08-29 dans la fenetre de determinants #12908 de
# main (`LIFT_NARRATION_CITERS` + `_lift_is_narrated`), qui couvre de/une et
# une largeur supérieure de déterminants (la/son/apres/avant/sans/obtenir/
# exige...) — les deux mécanismes faisaient le même travail en double.

# NOTE — proposition ecartee (triage 07-15..07-31, retiree au rebase 2026-08-16).
# Un `NO_CONCERN_TAIL_MARKERS` dechargeant tout body dont les 300 derniers chars
# portent « ne bloque pas » / « Safe to merge » a ete propose puis RETIRE : il
# rouvre le failure mode fondateur de B.0. Sur #10761, Hermes a emis
# COMMENT_WITH_CONCERNS et la PR a ete mergee sans reponse ecrite ; si ce meme
# body s'etait conclu par « ne bloque pas », un tel filtre l'aurait efface — et
# l'organe aurait manque precisement l'incident qui l'a fait naitre. Une reserve
# emise se leve par une PHRASE de reponse, jamais par la conclusion de celui qui
# l'a emise. `POSITIVE_MARKERS` ci-dessous fait le travail voisin, mais lui ne
# decharge QUE s'il ne reste aucune reserve vivante — c'est la difference.

# Verdict structurel POSITIF : l'emporte sur toute prose du body, y compris un
# decompte de CONCERNS passe en revue (« NanoClaw a relevé 2 CONCERNS... Verdict
# : COMMENT_WITHOUT_CONCERNS » #7583). C'est le miroir exact de
# COMMENT_WITH_CONCERNS : quand le verdict formel est rendu, il decide.
VERDICT_POSITIVE = "COMMENT_WITHOUT_CONCERNS"

# Verdicts positifs HUMAINS (#11677) : un reviewer UI qui tape « APPROVE » /
# « APPROVED » / « LGTM » (avec ou sans decoration markdown : **APPROVE**,
# `APPROVE`, # APPROVE) emet un verdict positif, equivalent formel du `state:
# APPROVED` natif. Hermes utilise deja `COMMENT_WITHOUT_CONCERNS` (string
# unique), ces 3 formes ajoutent le vocabulaire humain standard. Insensible
# a la casse (`re.IGNORECASE`).
#
# Ce que le word-bounding fait, et ce qu'il ne fait PAS (mesure, pas
# supposition -- #11753 F2, NanoClaw) : il ecarte bien les mots dont le
# verdict n'est qu'un fragment (`the approver left a note`, `disapprove
# entirely` -> pas de match), mais il ne distingue PAS l'usage narratif
# (`I approve the design` -> MATCH, parce que « approve » y est bel et bien
# un mot entoure d'espaces ; aucune quantite de word-bounding ne separe un
# verbe de son verdict homographe).
#
# Ce n'est pas un trou, parce que cette branche est subordonnee : elle ne
# rend None que si `live_concern` est deja faux. Une phrase narrative ne
# peut donc eteindre qu'une review qui ne portait aucune reserve vivante --
# ou il n'y avait rien a eteindre. Le garde tient par l'ORDRE des branches,
# pas par la finesse du motif.
HUMAN_VERDICT_POSITIVE = ("APPROVE", "APPROVED", "LGTM")
_HUMAN_VERDICT_RE = re.compile(
    r"(?:^|[\s\*_`#>])(" + "|".join(HUMAN_VERDICT_POSITIVE) + r")(?:$|[\s\*_`.,;:!?)])",
    re.IGNORECASE,
)

# Approbations SOUPES : ne rescussitent un commentaire que s'il ne porte AUCUNE
# reserve vivante. Une review mixte (« [COMMENT_WITH_CONCERNS] — 2 concerns...
# Safe to merge » #6849/#6852/#7704, gate vision « [avant merge] » #6698) garde
# ses reserves — le « Safe to merge » y est une conclusion nuancee, pas un
# verdict.
POSITIVE_MARKERS = (
    "SAFE for merge", "Safe to merge",
    "Verdict** : OK", "Verdict : OK",
)

# Mots qui, DEVANT une occurrence de marqueur, la rendent CITEE et non emise :
# negation (« No CHANGES_REQUESTED », « COMMENT_WITHOUT_CONCERNS »), article
# defini narratif (« the CHANGES_REQUESTED reflects a pre-fix state » #6699),
# modal hypothesique (« would `CHANGES_REQUESTED` a probeAddresses strip »
# #7248). L'occurrence fait reference au verdict d'un autre sans l'emettre.
# Fenetre courte (30 chars avant l'occurrence) : une citation a distance
# (autre phrase) ne desactive rien.
CITERS = (
    "no", "not", "pas de", "pas d'", "sans", "without", "aucun", "aucune",
    "zero", "jamais", "the", "would", "could", "might", "aurait",
    # « Previous CHANGES_REQUESTED was incorrect... Revised verdict: APPROVE »
    # (#748, 10 s avant le merge) : le reviewer RETRACTE sa propre reserve.
    # On ne peut pas demander « previous » — le mot ne peut que narrer.
    "previous",
    # Fenetre 05-08..05-14 (triage po-2023, #11044) — trois narrations mesurees :
    # « **COMMENTED** (pas CHANGES_REQUESTED) » (#860) : negation francaise
    # sans « de » — « pas de » ci-dessus ne couvrait pas la forme nue.
    "pas",
    # « rien a changer » (#11201) : negation totale du nit — le marqueur
    # « a changer » y est cite, pas emis.
    "rien",
    # « pending dismissal of stale CHANGES_REQUESTED » (#977) : comme
    # « previous », le mot ne peut que narrer une reserve passee.
    "stale",
    # « **0 REQUEST_CHANGES** : reviewDecision: "" » (#11916 commentaire
    # 5379577822) : le chiffre « 0 » precede REQUEST_CHANGES au sens d'un
    # COMPTE nul (et non d'une negation anglaise comme « no »). Sans cette
    # entree, `_is_cited` ne matche pas (`"0"` absent de CITERS) et le controle
    # negatif du grain #12311 deviendrait un faux positive massif.
    # (Le mot francais equivalent « zero » est deja dans CITERS via la liste
    # initiale ligne 455.)
    "0",
    # « CONFLICTING — needs rebase before merge » (#887, recidive de #729
    # fenetre 05-01..05-07) : demande procedurelle satisfaite par le merge
    # lui-meme — git n'autorise pas le merge d'une branche en conflit.
    "needs rebase",
    # « Si Static validation rouge → CHANGES_REQUESTED + diagnostic » (#1247,
    # fenetre 05-15..05-21) : verdict CONDITIONNEL futur, jamais emis. Une
    # fleche devant le marqueur est une derivation, pas une emission — les
    # verdicts reels s'ecrivent « Verdict : X » ou dans le state de la review.
    # Traite hors CITERS (voir _is_cited) car la fleche n'est pas un mot.
    # Fenetre 05-22..05-28 (triage po-2023, #11044) — la RETRACTION narree :
    # « my earlier CHANGES_REQUESTED was a FALSE POSITIVE (retracted) » puis
    # « Supersedes my earlier false-positive CHANGES_REQUESTED » (#1458), et
    # « supersedes my CHANGES_REQUESTED of 03:21 » (#1442). Comme « previous »,
    # ces mots ne peuvent que narrer un verdict passe ; une emission s'ecrit
    # « CHANGES_REQUESTED: » ou passe par le state de la review. « supersedes
    # my » en deux mots (pas « my » nu : « my CONCERN is... » est une vraie
    # emission).
    "earlier",
    "false-positive",
    "supersedes my",
    # « **Retracting CHANGES_REQUESTED → approving.** » (#1458, meme
    # commentaire) : le gerondif de retraction ne peut qu'annuler sa propre
    # reserve passee.
    "retracting",
    # Fenetre 05-29..06-04 (triage po-2023, #11044) — la REPONSE QUI NOMME.
    # « ## Re: CONCERNS ... **Fixed.** » (#1839) : « Re: » est un en-tete de
    # reponse — le marqueur cite est le SUJET auquel on repond, jamais une
    # nouvelle emission. (Forme nue « re » : le normalisateur retire la
    # ponctuation de fin de fenetre, deux-points compris.)
    "re",
    # « Per ai-01 CHANGES_REQUESTED: ... » (#2363) : « per X » = « selon X »,
    # attribution d'une reserve passee dans un rapport de fix. Idem « du
    # precedent review (CHANGES_REQUESTED ... » (#1958, 2e review APPROVED).
    # Ces deux-la agissent via la regle du mot d'attribution dans _is_cited.
    "per",
    "precedent",
)


def _unaccent(text: str) -> str:
    """« sont adressés » et « sont adresses » disent la meme chose.

    Les agents du cluster ecrivent massivement sans accents (les fichiers de
    regles eux-memes le font) tandis que les marqueurs ci-dessus sont accentues.
    Comparer les formes brutes rend le filtre orthographique — un nit deja leve
    serait re-signale (faux positif) sur la seule foi d'un accent absent. La
    casse, elle, est PRESERVEE : elle porte du sens (« Merge. »), et l'ignorer
    elargirait le filet au point de manquer de vrais nits.
    """
    return "".join(
        c for c in unicodedata.normalize("NFD", text)
        if unicodedata.category(c) != "Mn"
    )


def has_marker(body: str, markers: tuple[str, ...]) -> bool:
    normalised = _unaccent(body)
    return any(_unaccent(m) in normalised for m in markers)


# #13083 (2e instance) — fleche de derivation DEVANT une occurrence de levee.
# « -> je merge » / « X => Merged » : la fleche en fait la
# CONSEQUENCE conditionnelle d'une precondition (« sign-off user tel quel ->
# je merge sans autre reserve », #12896 c.5422307622 verbatim) — une
# derivation n'est pas une annonce, elle ne leve rien tant que la
# precondition n'est pas satisfaite. C'est la regle fleche de `_is_cited`,
# reprise ISO sans le reste de la fenetre de citation : importer cette
# derniere dans l'etage lift cassait des annonces reelles trans-sentence
# (« n'est pas une levee. **Mergée.** » — le « pas » de la phrase
# precedente tuait le Mergé de la suivante, 4 tests du corpus). Au rebase
# 2026-08-29 la garde vit dans `_live_lift_positions` (avec `_lift_is_narrated`
# #12908), plus de fonction `_has_lift_announce` dediee.
_ARROW_DERIVATIONS = ("->", "=>", "→")


def _arrow_precedes(normalised: str, index: int) -> bool:
    j = index
    while j > 0 and normalised[j - 1].isspace():
        j -= 1
    return normalised[:j].endswith(_ARROW_DERIVATIONS)


def _formal_concern_precedes_lift(body: str) -> bool:
    """Un verdict Hermes formel precede-t-il la narration de sa levee ?

    #12798 contient ``COMMENT_WITH_CONCERNS`` en tete de revalidation puis
    raconte plus bas qu'une ancienne reserve avait ete « levee ». Ce mot ne
    retracte pas le verdict vivant qui le precede. A l'inverse, « je leve ma
    CHANGES_REQUESTED » est une levee explicite historique : le marqueur nomme
    vient APRES le verbe et doit rester admissible.
    """
    stripped = _strip_mentioned_verdicts(_strip_quoted(body))
    normalised = _unaccent(stripped)
    concern_positions = [
        normalised.find(_unaccent(marker))
        for marker in ("COMMENT_WITH_CONCERNS", "REQUEST_CHANGES",
                       "NEEDS_CHANGES", "**BLOCKED**", "BLOCKED  PR")
    ]
    concern_positions = [position for position in concern_positions if position >= 0]
    # #12908 : les occurrences NARRÉES de levée (« après la levée annoncée »)
    # ne sont pas des gestes — la garde compare le verdict vivant aux levées
    # VIVES uniquement.
    lift_positions = _live_lift_positions(normalised)
    return (
        bool(concern_positions)
        and bool(lift_positions)
        and min(concern_positions) < min(lift_positions)
    )


# #13938 — quand un reviewer pose `[Hermes] COMMENT_WITH_CONCERNS` (verdict
# de pure emission, sans autorite de blocage, cf #12311) ET que le corps de
# la review declare explicitement que rien n'est bloquant, la review n'est
# PAS une reserve — c'est un commentaire FYI que la convention « reponse
# ecrite / thread inline / issue de suivi » (Tell c.589-L1 ★★★ strict)
# assimile a une APPROVED. Sans cette exemption, l'organe punit la
# precaution : plus l'auteur desambigue (« rien de bloquant (contrainte
# token : COMMENT only) »), plus le verdict formel matche CONCERN_MARKERS,
# plus le preflight rougit. Mesure : PR #13935 (GenAI tranche orphelins,
# substance OK, 63 checks SUCCESS, scope clean) bloquee sur Hermes
# COMMENT_WITH_CONCERNS + corps « Rien de bloquant. » — Tell NEW c.840
# sustained « un detecteur qui matche des phrases doit ignorer les
# occurrences en position de citation ou de refutation ».
#
# Garde STRICTE : l'exemption n'est JAMAIS elargie a CHANGES_REQUESTED /
# REQUEST_CHANGES / NEEDS_CHANGES / BLOCKED. Ces prefixes-la gardent leur
# autorite de blocage — seul COMMENT_WITH_CONCERNS est le verdict «
# comment-only par design » (force a state:COMMENTED par #12311, le seul
# etat que Hermes self-bot peut poster avec ce label).
def _comment_only_prefix(body: str) -> bool:
    """Le verdict formel en tete est-il exclusivement COMMENT_WITH_CONCERNS ?

    On distingue les formes EMISES des formes CITEES (mentionnees dans une
    prose qui les refute) par la seule fenetre de citation de 30 caracteres
    de `_is_cited` — la POSITION dans le corps n'est PAS verifiee, et le nom
    « prefixe » designe l'usage attendu, pas un controle. Le verdict
    ``[Hermes] COMMENT_WITH_CONCERNS — ...`` compte ; le corps ``pas de
    COMMENT_WITH_CONCERNS ici`` ne compte pas.

    Rejette si un verdict de blocage strict est aussi emis (CHANGES_REQUESTED,
    REQUEST_CHANGES, NEEDS_CHANGES, BLOCKED, SUSPECT_*, STRUCTURAL_ONLY).
    """
    if not body:
        return False
    normalised = _unaccent(body)
    # Marqueurs de blocage strict : leur presence simultanee a COMMENT_WITH_CONCERNS
    # annule l'exemption (le reviewer etale les deux = « concerns + change »,
    # pas un simple « comment only »).
    blocking_markers = (
        "CHANGES_REQUESTED", "REQUEST_CHANGES", "NEEDS_CHANGES",
        "**BLOCKED**", "BLOCKED  PR", "SUSPECT_", "STRUCTURAL_ONLY",
    )
    for marker in blocking_markers:
        if _unaccent(marker) in normalised:
            # Verifier que l'occurrence n'est pas CITEe (meme logique que
            # `has_live_marker`, mais inline : on n'a besoin que d'une
            # occurrence vivante).
            start = 0
            while (i := normalised.find(_unaccent(marker), start)) != -1:
                if not _is_cited(normalised[max(0, i - 30):i]):
                    return False
                start = i + 1
    # COMMENT_WITH_CONCERNS doit etre emis (vivant, non cite).
    target = _unaccent("COMMENT_WITH_CONCERNS")
    start = 0
    while (i := normalised.find(target, start)) != -1:
        if not _is_cited(normalised[max(0, i - 30):i]):
            return True
        start = i + 1
    return False


# Formulations explicites de non-blocage, dans le corps nettoye des verdicts
# mentionnes (cf `_strip_mentioned_verdicts` + `_strip_quoted` utilises
# ailleurs dans `classify`). Insensible a la casse et aux accents via
# `_unaccent`. Compile une seule fois au chargement du module.
_NON_BLOCKING_PHRASES = tuple(
    phrase.encode("unicode_escape").decode("ascii").replace(r"\u", r"\u")
    for phrase in (
        r"rien de bloquant",
        r"rien (?:a|à) corriger",
        r"rien (?:a|à) signaler",
        r"rien (?:a|à) traiter",
        r"rien (?:a|à) addresser",
        r"pas (?:de |d')bloquant",
        r"pas (?:de |d')blocage",
        r"aucun bloquant",
        r"aucun blocage",
        r"aucune bloque",
        r"aucune reserve",
        r"non.?bloquant",
        r"comment only",
        r"comment-only",
        r"no blocker",
        r"nothing blocking",
        r"all (?:is |looks )?good",
        r"tout (?:est )?ok",
        r"tout (?:est )?bon",
    )
)
_NON_BLOCKING_RE = re.compile(
    r"(?:" + "|".join(_NON_BLOCKING_PHRASES) + r")",
    re.IGNORECASE,
)


def _review_explicit_non_blocking(body: str) -> bool:
    """Le corps NETTOYE des mentions porte-t-il une formulation non-bloquante ?

    Le nettoyage (``_strip_mentioned_verdicts(_strip_quoted(body))``) aligne
    la surface analysee sur celle utilisee par `has_live_marker` pour
    CONCERN_MARKERS — une formulation de non-blocage posee dans une citation
    ou un bloc de code ne doit pas eteindre une reserve vivante.
    """
    if not body:
        return False
    surface = _strip_mentioned_verdicts(_strip_quoted(body))
    return bool(_NON_BLOCKING_RE.search(_unaccent(surface)))


# #13951 (Concern 1) -- l'exemption ne tient que si le SEUL concern EMIS est le
# prefixe COMMENT_WITH_CONCERNS lui-meme.
#
# `_comment_only_prefix` ne rejette que la famille des verdicts de BLOCAGE
# STRICT (CHANGES_REQUESTED / REQUEST_CHANGES / NEEDS_CHANGES / BLOCKED /
# SUSPECT_ / STRUCTURAL_ONLY). Elle est structurellement AVEUGLE aux deux
# autres familles de `CONCERN_MARKERS` :
#   (a) la famille PROSE     -- « avant merge », « a changer », « il va falloir »
#   (b) les GLYPHES de severite -- 🟡 (constat substantiel), 🔴 (bloquant strict)
#
# Un corps CONTRADICTOIRE passait donc l'exemption :
#
#     [Hermes] COMMENT_WITH_CONCERNS -- relu.
#     🟡 la cellule 12 est a changer avant merge.
#     Rien de bloquant par ailleurs.
#
# La phrase de non-blocage effacait un marqueur vivant emis dans la MEME
# review. On retire donc les occurrences de COMMENT_WITH_CONCERNS de la surface
# nettoyee (sans quoi le marqueur « CONCERNS » qu'il contient se compterait
# lui-meme) et on exige qu'il ne reste AUCUN concern vivant.
def _sole_live_concern_is_comment_prefix(body: str) -> bool:
    """Hors le prefixe CWC, le corps porte-t-il encore un concern VIVANT ?

    Retourne ``True`` quand le prefixe est le seul concern emis (l'exemption
    peut tenir), ``False`` des qu'un marqueur de prose ou un glyphe de
    severite survit au nettoyage (l'exemption tombe).
    """
    if not body:
        return False
    surface = _strip_mentioned_verdicts(_strip_quoted(body))
    residuel = re.sub("COMMENT_WITH_CONCERNS", " ", surface, flags=re.IGNORECASE)
    return not has_live_marker(residuel, CONCERN_MARKERS)


def _excerpt(body: str) -> str:
    """Tete + queue : le verdict d'un reviewer vit en QUEUE de body.

    Les 280 premiers chars seuls coupaient la conclusion (mesure triage
    07-15..07-31 : le verdict final tombait hors excerpt sur les PRs longues,
    et l'audit lisait la position du titre au lieu de la conclusion).

    Note : ceci concerne l'AFFICHAGE de l'audit, pas la classification. Voir
    `classify` — la conclusion en queue n'y decharge rien.
    """
    snippet = " ".join(body.split())
    if len(snippet) <= 400:
        return snippet[:280]
    return snippet[:200] + " [...] " + snippet[-200:]


def _is_cited(window: str) -> bool:
    """La fenetre avant l'occurrence se termine-t-elle sur un mot de citation ?

    Le mot doit etre delimite : le caractere qui le precede est non-alphanumerique
    (espace, newline, ponctuation) ou le debut de la fenetre. Sans frontiere,
    « xxxtechno » matcherait « no ».
    """
    w = window
    # Fleche immediatement devant le marqueur : derivation conditionnelle
    # (« Si X → CHANGES_REQUESTED », #1247), pas une emission de verdict.
    stripped = w.rstrip()
    if stripped.endswith(("→", "->", "=>")):
        return True
    while w and not w[-1].isalnum():
        w = w[:-1]
    w = w.lower()
    for c in CITERS:
        c = c.rstrip("'’")
        # Compteur numerique (« 0 » dans CITERS, grain #12311) — cas reel
        # `**0 REQUEST_CHANGES** » (#11916) : on veut que `**0` (markdown
        # bold) matche, mais pas `v2.0`, `4.0`, `P-0`, `(0)`. La regle est :
        # extraire le DERNIER mot du window, strip typographie markdown
        # (`*`, `_`, backtick) des deux cotes, puis tester que le token
        # resultant est EXACTEMENT ce compteur. Sans le strip de debut,
        # `**0` ne matche pas (le `*` final est deja degage mais le `*`
        # initial ne l'est pas) ; sans l'egalite stricte, `v2.0` matche
        # (endswith « 0 » + caractere precedent non-alphanum `.`). Cf
        # issue #12335 (defaut latent — portee mesuree : 0/120 PR corpus,
        # mais 4 formes ordinaires atteignables).
        if c.isdigit():
            if not w:
                continue
            parts = w.rsplit(None, 1)
            tail = parts[-1]
            token = tail
            while token and token[0] in "*_`":
                token = token[1:]
            while token and token[-1] in "*_`":
                token = token[:-1]
            if token == c:
                return True
            continue
        if w == c or (w.endswith(c) and not w[-len(c) - 1].isalnum()):
            return True
    # Fenetre 05-29..06-04 (#11044) — le mot d'ATTRIBUTION entre le citer et
    # le marqueur : « Per ai-01 CHANGES_REQUESTED » (#2363), « Stale Hermes
    # CHANGES_REQUESTED was purely... » (#2006), « du precedent review
    # (CHANGES_REQUESTED sur commit... » (#1958). Un citer suivi d'UN seul
    # mot reste une narration — le nom d'agent n'y change rien. Une emission
    # ne le traverse jamais : elle s'ecrit « MARKER: » nue ou passe par le
    # state de la review (« [Hermes] — CHANGES_REQUESTED » n'a pas de citer
    # devant l'agent, donc reste live).
    parts = w.rsplit(None, 1)
    head = parts[0] if len(parts) == 2 else ""
    if head:
        for c in CITERS:
            c = c.rstrip("'’")
            if c.isdigit():
                # Pas de propagation au mot d'attribution — un compteur nu
                # comme « 0 » n'a pas de raison d'etre precede d'un nom
                # d'agent. Si le cas se presente, le citer fait foi tel quel.
                continue
            if head == c or (head.endswith(c) and not head[-len(c) - 1].isalnum()):
                return True
    return False


# #12908 — miroir LIFT-side de CITERS : un mot qui fait de l'occurrence
# suivante un NOM de levee, pas sa PERFORMANCE. « obtenir une levée
# explicite » (PREFLIGHT jsboigeEpita 2026-08-25T04:45:30Z sur #12798)
# demande la levee, il ne l'accorde pas ; « la levée annoncée » la narre.
# Le discriminant est le déterminant/quantificateur immédiatement devant :
# une émission performative s'ouvre sur un verbe (« Je lève », « est
# levée », « Levée de ») ou un acronyme nu (LGTM), jamais sur « une ».
LIFT_NARRATION_CITERS = (
    "un", "une", "le", "la", "les", "des", "du", "de",
    "mon", "ma", "ton", "ta", "sa", "son", "ses",
    "leur", "leurs", "notre", "votre",
    "ce", "cet", "cette", "ces", "chaque", "aucun", "aucune",
    "apres", "avant", "sans", "obtenir", "exige", "exiger",
    "the", "a", "an",
)


def _lift_is_narrated(window: str) -> bool:
    """La fenetre avant l'occurrence se termine-t-elle sur un déterminant ?

    Même garde de frontière que `_is_cited` : le caractère précédant le mot
    doit être non-alphanumérique, sinon « aucune » matcherait « une ».
    """
    w = window
    while w and not w[-1].isalnum():
        w = w[:-1]
    w = w.lower()
    for c in LIFT_NARRATION_CITERS:
        if w == c or (w.endswith(c) and not w[-len(c) - 1].isalnum()):
            return True
    return False


# #13622 — negation directe d'un LIFT_MARKER dans la portee locale. La
# negation est l'inverse semantique d'une levee : « ne pas merger tant
# qu'elle n'est pas levee » AFFIRME que la levee n'a pas eu lieu, alors
# que le gate rendait `None` (commentaire non-nitrant). Les tokens sont
# ceux qui precedent ou suivent immediatement le marqueur (15 chars) ;
# au-dela, c'est une autre phrase, un autre commentaire, ou une
# narration sans rapport.
_LIFT_NEGATION_TOKENS = (
    "non", "pas", "plus", "aucun", "aucune", "n'est", "nest", "jamais",
    "rien", "sans",
)


def _lift_is_negated(window_before: str, window_after: str) -> bool:
    """Le LIFT_MARKER est-il dans une negation directe ?

    #13622 fondateur — PR #13563 verbatim :
      "... **ne pas merger tant qu'elle n'est pas levee** ..."
    matchait `LIFT_MARKER=levee` a la fenetre 30 chars etait non-narree
    (pas de determinant CITERS) ET non-conditionnelle (pas de fleche de
    derivation), donc classee `None` (= « pas un nit »). Le predicat
    matchait le TOKEN `lev[ée]` ; il ne modelisait pas la negation.

    Discrimination : tokens de negation (`non`, `pas`, `plus`, `n'est`,
    `jamais`, `aucun`, `aucune`, `rien`, `sans`) dans une fenetre de
    15 chars avant OU apres le marker, avec garde de frontiere
    alphanumerique (mecanique `_is_cited`, symetrie exacte avec
    `_lift_is_narrated`). Les CITERS determinants (`la`, `le`, `aucun`,
    etc.) restent geres par `_lift_is_narrated` — la negation est
    distincte.

    Residuel assume (documente dans l'issue) : une negation NON
    locale (« levee il y a longtemps, reserve non acquise » avec 20+
    chars entre les deux) echappe. C'est la frontiere entre negation
    directe et narration : la derniere appartient a `_lift_is_narrated`
    (CITERS).
    """
    norm_before = _unaccent(window_before).lower()
    norm_after = _unaccent(window_after).lower()
    # Tronque les separateurs de bord (espaces, virgules, points) pour
    # que la negation du dernier token soit testee sans pollution. La
    # negation NON locale (15+ chars de distance) echappe par construction
    # — c'est la frontiere documentee dans l'issue #13622.
    tail = norm_before[-15:].rstrip(" \t\n.,;:!?")
    head = norm_after[:15].lstrip(" \t\n.,;:!?")
    for tok in _LIFT_NEGATION_TOKENS:
        # Token avant : match \btok\b en fin de fenetre (apres strip).
        if tail.endswith(" " + tok) or tail == tok:
            return True
        # Token apres : match \btok\b en tete de fenetre (apres strip).
        if head.startswith(tok + " ") or head == tok:
            return True
    return False


def _bare_mention_is_negated(window_before: str, window_after: str) -> bool:
    """Le verdict Position G est-il dans une negation directe ?

    Variante de `_lift_is_negated` adaptee a Position G (`#14070`) : la
    mention peut mettre le token de negation N'IMPORTE OU dans la window
    (ex. « pas traite le REQUEST_CHANGES » met `pas` au DEBUT de la
    window avant, pas en bord). `_lift_is_negated` regarde les BORDS
    uniquement (helper naturel pour `_LIFT_MARKERS` ou le token de
    negation precede/suit immediatement le marqueur). Helper dedie
    pour Position G : cherche un token `_LIFT_NEGATION_TOKENS` n'importe
    ou dans la window combinee (avant + apres), avec strip des
    separateurs de bord.

    Meme semantique que `_lift_is_negated` (meme ensemble de tokens),
    seule la fenetre de scan change. Symetrie preservee.
    """
    combined = (window_before + " " + window_after).lower()
    combined = _unaccent(combined)
    # Token de negation entoure de non-alphanumerique (`\b` word boundary
    # gere implicitement les separateurs ASCII : espace, virgule, point,
    # point d'interrogation, deux-points, point-virgule, point
    # d'exclamation, apostrophe droite). Coherent avec le
    # `rstrip(".,;:!?")` de `_lift_is_negated` — la ponctuation est une
    # bordure valide de token.
    for tok in _LIFT_NEGATION_TOKENS:
        if re.search(rf"\b{re.escape(tok)}\b", combined):
            return True
    return False


def _live_lift_positions(normalised: str) -> list[int]:
    """Positions des occurrences de LIFT_MARKERS NON narrées ET NON niées.

    `has_marker` traite le body comme un sac de mots ; #12798/#12908 a
    mesuré le coût de ce sac côté LIFT : le PREFLIGHT qui EXIGE « une
    levée explicite » était enregistré comme événement de levée, et
    éteignait les réserves antérieures de son propre auteur (faux OK).
    #13083 (2e instance) y ajoute la flèche de dérivation : « -> je
    merge » conditionne le merge à une précondition non satisfaite, ce
    n'est pas une annonce.
    #13622 (3e instance) y ajoute la negation directe : « ne pas merger
    tant qu'elle n'est pas levee » AFFIRME que la levee n'a pas eu
    lieu, alors que le token `levee` matchait sans prise en compte de
    la negation. Le predicat `_lift_is_negated` regarde 15 chars avant
    ET apres le marker.
    """
    out: list[int] = []
    for marker in LIFT_MARKERS:
        m = _unaccent(marker)
        m_len = len(m)
        start = 0
        while (i := normalised.find(m, start)) != -1:
            window_before = normalised[max(0, i - 30):i]
            window_after = normalised[i + m_len:i + m_len + 15]
            if not _lift_is_narrated(window_before) \
                    and not _arrow_precedes(normalised, i) \
                    and not _lift_is_negated(window_before, window_after):
                out.append(i)
            start = i + 1
    return out


def has_live_lift(body: str) -> bool:
    """LIFT_MARKER présent avec au moins une occurrence NON narrée.

    Miroir exact de `has_live_marker` côté levée : la classe use-vs-mention
    (#11636 → #12944 côté verdicts) s'appliquait aux réserves, pas aux
    levées — la symétrie ferme la dernière porte par laquelle un commentaire
    neutre passait pour un geste de levée.
    """
    return bool(_live_lift_positions(_unaccent(body)))


# Marqueurs reconnus par MOTIF plutot que par sous-chaine. La cle est le marqueur
# du tuple, minuscule et desaccentue (has_live_marker normalise des deux cotes).
#
# « CONCERNS » : la sous-chaine nue ne peut pas devenir insensible a la casse sans
# retourner l'organe contre lui-meme. Mesure sur 588 commentaires (corpus 80 PRs
# ouvertes + 70 mergees, 2026-09-01) : la seule insensibilite a la casse fait
# basculer 6 verdicts None -> BOT-CONCERN, et les 6 sont des narrations de LEVEE
# qui citent le mot en y REPONDANT (« les 2 concerns sont traitees au commit X »,
# « Reponse a la CONCERN empirique »). Les bloquer serait le miroir exact du
# defaut que B.0 traque. On retient donc la forme ETIQUETEE en tete de ligne --
# « Concern: », « concerns :», « **Concern 2 :** », « > CONCERNS : » -- qui est
# une EMISSION et non une mention, tolere la casse et le nombre des deux cotes,
# et laisse muettes les six narrations mesurees.
# Marqueurs dont la casse NE se relache PAS. Deux familles, une raison commune :
# leur variante de casse est plus rare que les mentions qu'elle attraperait.
#   - prose : « AVANT merge » est une emphase sur la chronologie dans une
#     narration de levee Voie 3, pas une reserve (2 cas mesures sur 588).
#   - « CONCERNS » nu : « les 2 concerns sont traitees », « Reponse a la CONCERN
#     empirique » sont des REPONSES a une reserve (6 cas mesures). Le relachement
#     de casse pour ce mot passe par _CONCERN_LABEL ci-dessous, qui exige la
#     forme etiquetee -- donc une emission, pas une mention.
_CASE_SENSITIVE_MARKERS = frozenset({
    "avant merge", "avant de merger", "before merge",
    "il va falloir", "a nuancer", "à nuancer", "a changer",
    "CONCERNS",
})


_WORD_BOUNDED_MARKERS = {
    _CONCERN_LABEL: re.compile(r"(?m)^[\s*_#>\-]*concerns?\s*\d*\s*:"),
}


def has_live_marker(body: str, markers: tuple[str, ...]) -> bool:
    """Marqueur present avec au moins une occurrence NON citee.

    `has_marker` traite le body comme un sac de mots : « No CHANGES_REQUESTED
    from this review » contient « CHANGES_REQUESTED » donc compte comme une
    reserve. C'est la source dominante de faux positifs de l'organe (11/64
    signaux flagges sur la fenetre 07-14..07-20, triage po-2024:CoursIA-2) :
    des reviews d'approbation qui citent le verdict qu'elles n'emettent pas —
    negation (« No », « Pas de », « without »), narration d'une review
    pre-fix (« the CHANGES_REQUESTED reflects a pre-fix state » #6699), ou
    modal hypothesique (« would CHANGES_REQUESTED » #7248). On verifie donc
    chaque occurrence : si un mot de citation touche le debut du marqueur
    (fenetre de 30 caracteres, le « WITHOUT_ » de COMMENT_WITHOUT_CONCERNS
    compris), l'occurrence est morte ; le marqueur ne vit que si au moins une
    occurrence survit.
    """
    raw = _unaccent(body)
    lowered = raw.lower()
    for marker in markers:
        m = _unaccent(marker).lower()
        # La casse ne se relache que sur les JETONS de verdict (identifiants
        # ecrits en capitales par convention, dont les variantes de casse sont
        # des accidents de frappe). Les marqueurs de PROSE gardent leur forme
        # litterale : mesure du 2026-09-01 sur 588 commentaires -- relacher la
        # casse de « avant merge » fait basculer 2 verdicts, et les 2 sont des
        # narrations de levee Voie 3 (« issue #14030 ouverte AVANT merge »), ou
        # la majuscule est une EMPHASE sur la chronologie, pas une reserve.
        if marker in _CASE_SENSITIVE_MARKERS:
            normalised, m = raw, _unaccent(marker)
        else:
            normalised = lowered
        word_re = _WORD_BOUNDED_MARKERS.get(m)
        if word_re is not None:
            for hit in word_re.finditer(normalised):
                i = hit.start()
                if not _is_cited(normalised[max(0, i - 30):i]):
                    return True
            continue
        start = 0
        while (i := normalised.find(m, start)) != -1:
            if not _is_cited(normalised[max(0, i - 30):i]):
                return True
            start = i + 1
    return False


# #13912 -- le chemin `HOLD_HEAD` (#13784) a ete ajoute SANS les deux
# discriminations que son chemin FRERE `_COORDINATOR_INJUNCTION_RE` portait
# deja. Un chemin neuf herite des gardes de son jumeau, sinon il rouvre les
# faux positifs que le jumeau avait fermes -- ce qui est arrive ici deux fois :
#
#   (a) VERDICT NOMME. `**HOLD G-VAR-2 (cap de genre)**` NOMME la garde
#       G-VAR-2, il ne pose rien. Le lookahead
#       `(?![\s-]+(?:G-VAR|BLOCK|BOT|COMMENT|VERDICT|PR))` de la ligne 1237
#       ecarte ces noms depuis #13598 ; `HOLD_HEAD` ne l'avait pas.
#   (b) NEGATION APRES LE LIBELLE. `**HOLD coordinateur** NON.` DENIE un hold.
#       `_lift_participle_after` ne connait que « leve / levee / lifted », qui
#       suivent immediatement ; ici la negation suit le LIBELLE, deux mots plus
#       loin.
#
# Les deux resserrements de (b) sont repris de la raison meme qui fait exiger
# `HOLD` en majuscules dans #13784 -- « hold » est un mot ordinaire :
#   - MAJUSCULES exigees. `pas` est volontairement ABSENT de la liste : « HOLD
#     -- ne pas merger » est un hold REEL, et une negation minuscule le
#     neutraliserait.
#   - FIN DE CLAUSE exigee. « HOLD: NO merge until X » porte « NO » sans etre
#     une denegation ; seul un `NON`/`NO` qui CLOT la clause est le verdict.
_HOLD_NAMED_VERDICT_RE = re.compile(
    r"^[\s-]+(?:G-VAR|BLOCK|BOT|COMMENT|VERDICT|PR\b|PR-)", re.I
)
_HOLD_NEGATED_RE = re.compile(r"^[^.\n]{0,40}?\b(?:NON|NO)\b\s*(?:[.,;!]|$)")


def _hold_head_is_emission(head: str, end: int) -> bool:
    """Le `HOLD` en tete de corps EMET-il un hold, ou en NOMME-t-il un ?

    Miroir de `_is_cited` pour le chemin `HOLD_HEAD` : rend False des que le
    texte qui suit disqualifie l'occurrence -- levee (delegue a
    `_lift_participle_after`), verdict nomme (a), denegation (b).
    """
    if _lift_participle_after(head, end):
        return False
    tail = head[end:]
    if _HOLD_NAMED_VERDICT_RE.match(tail):
        return False
    if _HOLD_NEGATED_RE.match(tail):
        return False
    return True


def _lift_participle_after(head: str, end: int) -> bool:
    """Le mot qui SUIT l'occurrence est-il un participe de levee ?

    Miroir post-fenetre de `_is_cited` : « BLOCAGE leve », « HOLD lifted »
    NOMMENT le blocage pour le clore, ils ne l'emettent pas (mention #11636).
    """
    tail = head[end:end + 10].lstrip(" \t:;,.)('\"-—*")
    word = ""
    for ch in tail:
        if not ch.isalpha():
            break
        word += ch
    return word.lower() in ("leve", "levee", "lifted")


def _block_emitted(body: str) -> bool:
    """Le coordinateur POSE-t-il un blocage (verdict, jamais une citation) ?

    #13083 — le defaut mesure : la prose « il doit etre leve par une phrase
    AVANT TOUT merge » ratait la sous-chaine « avant merge » a cause du mot
    intercale — un marqueur de sous-chaine ne survit pas a un adverbe. Deux
    formes STRUCTURELLES, aucune dependante d'un mot :

      (a) le marqueur de protocole `[BLOCAGE] lane <machine:workspace>` /
          `[BLOCK] lane ...`, pose en tete de ligne — ancre `^` re.M et rejet
          des backticks, meme pose stricte que #13030 pour `[OVERRIDE] lane` :
          citer le marqueur (en liste, en prose, en backticks) ne le POSE pas ;
      (b) le verdict `**BLOCAGE ...**` en TETE du corps (60 premiers chars) —
          la position du verdict, pas une substring de milieu. La narration
          « pas un blocage » (fixture #11190) vit en section ; l'emission
          aussi. Les negations immediates (« pas de blocage ») restent citees
          via `_is_cited` ;
      (c) le verdict `**HOLD ...**` en TETE de corps (#13779). HOLD est le
          verbe que variation-protocol.md §3 donne au coordinateur (« HOLD
          sans remplacement = echec coordinateur ») — un gate de merge qui
          ignore le verbe de l'instrument qui le pilote est aveugle a son
          propre pilote. Pose plus stricte que (b) — debut de corps ET
          majuscule, cf HOLD_HEAD — parce que « hold » est un mot ordinaire.

    La levée d'un blocage passe par les formes canoniques — LIFT_MARKER
    reconnu (donc classify -> None dans la branche levee, cf `classify`) ou
    `[OVERRIDE] lane` (arbitrage #11639 en `analyse`). Un corps qui commence
    par BLOCAGE sans forme de levee reste un signal : sur-blocquer est le bon
    defaut d'un gate de merge, le sous-blocage est la dechirure que #13083
    ferme.

    Reparation preflight ADJOINT (po-2025, 2026-08-26) : un override NATUREL
    qui nomme le blocage qu'il leve (« [OVERRIDE] lane x — Blocage leve par
    override ») etait reclasse BLOCK avant l'etage de levee — mesure : le post
    d'arbitrage devenait lui-meme un signal BLOCK (et etait exclu
    d'explicit_lifts par classify != None), la prose meme qui arbitrait
    re-bloquait le gate. Deux bornes, toutes deux scopees a la forme verdict
    en tete (b) ; le marqueur structurel (a) reste absolu — un arbitre qui
    veut re-bloquer le pose delibereement :

      A. un post d'ARBITRAGE (`[OVERRIDE]` pose en tete du corps) n'emet
         jamais — l'override est l'etage superieur du protocole (#11639) ;
      B. « BLOCAGE leve / levee / lifted ... » : l'occurrence immédiatement
         suivie d'un participe de levée est le COMPLÉMENT d'une levée
         (mention #11636), pas une émission — miroir post-fenêtre de
         `_is_cited`.
    """
    stripped = _strip_quoted(body)
    normalised = _unaccent(stripped)
    if BLOCAGE_LANE.search(normalised):
        return True
    head = normalised[:60]
    uhead = head.upper()
    if head.lstrip(" \t*_").upper().startswith("[OVERRIDE]"):
        return False
    m_hold = HOLD_HEAD.match(head)
    if m_hold and _hold_head_is_emission(head, m_hold.end()):
        return True
    for marker in ("BLOCAGE", "BLOCK"):
        pos = 0
        while (i := uhead.find(marker, pos)) != -1:
            before = head[i - 1] if i > 0 else ""
            after = head[i + len(marker)] if i + len(marker) < len(head) else ""
            if before.isalnum() or before == "_" or before == "[" or after.isalnum() or after == "_":
                pos = i + len(marker)
                continue
            if _lift_participle_after(head, i + len(marker)):
                pos = i + len(marker)
                continue
            if not _is_cited(normalised[max(0, i - 30):i]):
                return True
            pos = i + len(marker)
    return False


# #13598 — EMISSION informelle d'un LIFT_OVERRIDE_LOGINS. Le cas fondateur
# (#13550, 2026-08-30T00:37:09Z, myia-ai-01) : « ## [ai-01 ARBITRAGE] La
# reserve GPU tient. **Ne pas merger sur les verts.** » — coordonne en
# francais courant, sans glyphe formel ni verdict formel, etait rendu None
# par classify(). La classe CONCERN_MARKERS suppose un vocabulaire de revue
# (CHANGES_REQUESTED, BLOCKED, glyphes Hermes) que la plume du coordinateur
# n'utilise pas quand il EMET un hold.
#
# Discrimination ciblee : un seul auteur concerne (LIFT_OVERRIDE_LOGINS,
# 1 entree aujourd'hui), donc le cout du whack-a-mole est borne. La
# detection porte sur des INJONctions structurelles (verbe + assertion),
# pas sur le vocabulaire d'une revue :
#   - verbe d'injonction explicite (« ne pas merger/fusionner », « hold »,
#     « bloque », « attend », « wait », « stop », « arr[êe]t », « tant que »)
#   - PAS un LIFT_MARKER (la phrase EMET, ne leve pas)
#   - PAS une narration nominale de levee (miroir de la borne `_is_cited`)
#   - PAS un ARBITRAGE/OVERRIDE (un override EMET une LEVEE, pas une reserve ;
#     le trappe #11639 reste la voie de levee du coordinateur)
#
# Faux positif a surveiller (acceptance #13598 point 2) : un commentaire
# coordinateur ANODIN post-cutoff (accuse reception, remerciement, « vu »)
# ne porte aucun verbe d'injonction ni assertion substantive, et reste muet.
_COORDINATOR_INJUNCTION_RE = re.compile(
    r"(?i)(?:"
    r"ne\s+(?:pas\s+)?(?:merger|fusionner)|"
    r"\bhold\b(?![\s-]+(?:G-VAR|BLOCK|BOT|COMMENT|VERDICT|PR\b|PR-))|"
    r"\b(?:je\s+)?bloque\b|"
    r"\b(?:j['e]\s+)?attend[s]?\b(?:\s+le|\s+le\s+run|\s+la|\s+les)?|"
    r"\bwait\b(?:\s+for|\s+le|\s+la|\s+les)?|"
    r"\bstop\b|"
    r"\barre?te[rs]?\b|"
    r"\btant\s+que\b|"
    r"sur\s+(?:les?\s+)?verts?|"
    r"sur\s+(?:le\s+)?hold|"
    r"pas\s+sur\s+les\s+(?:verts?|ciels?)"
    r")",
)
_COORDINATOR_INJUNCTION_NEGATED_RE = re.compile(
    r"(?i)\b(?:pas|plus|jamais|aucun)\s+(?:hold|wait|bloque|attend|stop|arr[êe]t)\b",
)
# #13912 -- le mot `hold` en MENTION NOMINALE d'un hold tenu par un tiers n'est
# pas une EMISSION. La voie #13598 n'attrape ce cas qu'a demi : le lookahead
# `(?![\s-]+(?:G-VAR|BLOCK|BOT|COMMENT|VERDICT|PR\b|PR-))` ecarte les NOMS DE
# VERDICT (« HOLD G-VAR-2 », « HOLD PR-1234 »), pas les mentions descriptives
# d'un hold detenu ailleurs (« moteur sous hold user (#10038) », cf review
# ai-01 sur #13706 Le moteur est sous hold user). Le discriminateur est le mot
# qui precede `hold` : un mot de CITATION_NOMINALE (sous, sur, de, par, en, du,
# des, le, la, les, ce, cette, un, une, mon, ton, son, notre, votre, leur,
# « tenir » au passe) introduit une mention ; seul un verbe d'INJONCTION
# explicite a cote du `hold` (« tient le hold », « maintenir le hold ») EMET.
# Meme mechanique que `_is_cited` (L883) pour les marqueurs formels, mais avec
# un CITERS adapte au `hold` en francais courant.
_HOLD_NOMINAL_MENTION_BEFORE_RE = re.compile(
    r"(?i)(?:^|[\s,.;:!?\(\[*_])(?:"
    r"sous|sur(?:plement)?|d['e]|de|du|des|le|la|les|ce|cette|ces|un|une|"
    r"mon|ton|son|notre|votre|leur|leurs|en|par|avec|sans|n['e]|tenant"
    r")\s+hold\b",
)
_HOLD_EMISSION_VERB_BEFORE_RE = re.compile(
    r"(?i)(?:^|[\s,.;:!?\(\[*_])(?:tiens|tenir|maintiens|maintenir|poser?|imposer?)\s+(?:le\s+|la\s+|du\s+|des\s+)?hold\b",
)


def _hold_match_is_emission(body: str) -> bool:
    """#13912 : un `hold` matche par `_COORDINATOR_INJUNCTION_RE` est-il une
    EMISSION du coordinateur, ou une MENTION NOMINALE d'un hold tiers ?

    Renvoie True si le `hold` est en EMISSION (verbe d'injonction explicite
    immediatement voisin, ou contexte « tient/maintenir le hold »), False si
    en MENTION NOMINALE (precede d'un mot de citation descriptive).

    Le defaut documente par ai-01 sur #13706 : « moteur sous hold user »,
    « il est sous hold user », « Et le moteur qui ecraserait est sous hold
    user (#10038) » -- toutes des MENTIONS d'un hold tenu par user via #10038,
    jamais une EMISSION du coordinateur sur cette PR.

    Cas reels :
    - EMISSION  : « **HOLD coordinateur** » -- le mot est en tete, pas de mot
                  avant, donc _HOLD_NOMINAL_MENTION_BEFORE_RE ne matche pas,
                  _HOLD_EMISSION_VERB_BEFORE_RE peut etre absent. Verdict:
                  EMISSION.
    - EMISSION  : « Je tiens le hold jusqu'a resolution » -- verbe explicite.
    - MENTION   : « sous hold user », « sur le hold de #10038 » -- mots de
                  citation avant.
    - MENTION   : « le hold tient » -- ambigu ; ici le coord EMET implicitement
                  qu'il tient le hold, donc EMISSION (verbe « tient » avant).

    Strategie : si AUCUNE mention nominale n'est trouvee, c'est une EMISSION.
    Si UNE mention nominale est trouvee, c'est une MENTION. On ignore les
    emissions qui n'ont pas de verbe explicite (le cas « HOLD coordinateur »
    en tete), parce qu'elles ont toujours le `_COORDINATOR_INJUNCTION_RE`
    matche par leur glyphe « HOLD G-VAR-2 » que le lookahead ecarte deja --
    le cas EMISSION qui nous interesse ici est VERBE + hold.
    """
    if not _COORDINATOR_INJUNCTION_RE.search(body):
        return False
    # Si AUCUNE mention nominale, c'est une emission (verbe d'injonction
    # autre que hold, ou un hold-EMISSION sans mot de citation avant).
    if not _HOLD_NOMINAL_MENTION_BEFORE_RE.search(body):
        return True
    # Sinon, c'est une mention -- sauf si un verbe d'emission explicite
    # precede (`je tiens le hold`, `maintenir le hold`).
    if _HOLD_EMISSION_VERB_BEFORE_RE.search(body):
        return True
    return False


def _coordinator_emission_informal(body: str) -> bool:
    """#13598 : le coordinateur EMET-il un hold en francais courant ?

    Renvoie True si (a) le body porte une injonction structurelle non
    negatee, ET (b) le body n'emet ni une LEVEE (LIFT_MARKER present) ni
    un ARBITRAGE (OVERRIDE pose). Cible : 1 auteur (LIFT_OVERRIDE_LOGINS).
    """
    normalised = _unaccent(body)
    if _COORDINATOR_INJUNCTION_NEGATED_RE.search(normalised):
        return False
    # #13912 -- sur le mot `hold`, demasquer les MENTIONS NOMINALES d'un hold
    # tiers (cf review ai-01 sur #13706 : « moteur sous hold user (#10038) »).
    # Sans cette discrimination, un override qui CITE un hold tenu ailleurs
    # devient lui-meme une emission, et l'instrument de levee est auto-bloquant.
    if _COORDINATOR_INJUNCTION_RE.search(normalised) and not _hold_match_is_emission(normalised):
        return False
    if not _COORDINATOR_INJUNCTION_RE.search(normalised):
        return False
    # Une levee VIVE neutralise l'injonction (la phrase leve la reserve qu'elle
    # nommait). Mirror exact de la branche `_block_emitted` : un override qui
    # nomme l'injonction levee (« BLOCAGE leve ») reste muet.
    if has_live_lift(normalised):
        return False
    # #14089 -- chemin different : l'injonction peut etre ANNONCEE puis LEVEE
    # dans la meme phrase, sans LIFT_MARKER (qui exige la graphie complete
    # « levee »). Cas fondateur : « HOLD leve -- le remplacement est nomme,
    # vous pouvez merger. » -- la voie _block_emitted reconnait le motif via
    # `_lift_participle_after` (leve / levee / lifted post-marker), mais la
    # voie `_coordinator_emission_informal` n'en herite pas : elle conclut a
    # une emission et classifie BOT-CONCERN, donc la PR que le commentaire
    # vient de DEBLOQUER reste BLOQUEE. Meme classe de defaut que celle
    # corrigee dans #13912 : un chemin qui n'a pas herite de la garde de
    # son jumeau. On ajoute ici le MEME test post-marker que porte
    # `_block_emitted` (point B), sur l'INJONCTION structurellement matchee
    # (toutes les positions), pas seulement sur le head. Si TOUTES les
    # injonctions sont suivies d'un participe de levee, c'est une levee.
    if _every_injunction_followed_by_lift(normalised):
        return False
    # Un [OVERRIDE] pose en tete (arbretage tiers de B.0) EMET une levee,
    # jamais une reserve — garde-fou de l'override, deja documente en
    # `_block_emitted` point A.
    head = normalised[:60].lstrip(" \t*_").upper()
    if head.startswith("[OVERRIDE]"):
        return False
    return True


def _every_injunction_followed_by_lift(normalised: str) -> bool:
    """#14089 : toute occurrence d'injonction structurelle est-elle suivie
    d'un participe de levee (`leve` / `levee` / `lifted`) ?

    Renvoie True si le body NE porte aucune injonction (defaut : pas une
    levee) OU si chaque occurrence matchee par `_COORDINATOR_INJUNCTION_RE`
    est immediatement suivie d'un participe de levee (miroir de la borne
    `_lift_participle_after` que porte `_block_emitted` point B).
    """
    matches = list(_COORDINATOR_INJUNCTION_RE.finditer(normalised))
    if not matches:
        return False
    for m in matches:
        end = m.end()
        if not _lift_participle_after(normalised, end):
            return False
    return True


def ts(value: str | None) -> datetime | None:
    if not value:
        return None
    return datetime.fromisoformat(value.replace("Z", "+00:00"))


def gh_json(args: list[str]) -> object:
    out = subprocess.run(
        ["gh", *args], capture_output=True, text=True, encoding="utf-8", check=True
    ).stdout
    return json.loads(out)


# #14218 — la voie 3 de B.0 a besoin de 4 conditions, pas 1. Une seule
# (createdAt avant cutoff) etait verifiee par `gh_issue_created`, ce qui
# ouvrait la trappe a 3 classes silencieuses : issue fermee qui pointe
# encore sur la PR, issue ancienne sans rapport, issue qui ne cite pas la
# PR (le « report » decrit un autre travail). On enrichit le callback
# pour rendre les 4 jugements : OUVERTE, anterieure au cutoff, posterieure
# a la reserve, et citant la PR dans son titre ou son corps.
_ISSUE_INFO_CACHE: dict[int, "IssueInfo | None"] = {}
# Garde compat : l'ancien nom etait deja importe par d'anciens tests
# (cf `gh_issue_created` comme pointeur historique). Le callback ci-dessous
# rend le createdAt isole, comme avant ; la voie 3 utilise desormais
# `gh_issue_info` directement.
_ISSUE_CREATED_CACHE: dict[int, datetime | None] = {}


class IssueInfo:
    """Snapshot minimal d'une issue GitHub resolue par voie 3.

    Champs : `state` ('open'/'closed'), `created_at` (tz-aware UTC, ``None``
    si la cle manque), `title`, `body`. ``None`` est rendu pour un numero
    qui n'est PAS une issue (PR, 404, payload non-dict) — cf #13725.
    """

    __slots__ = ("state", "created_at", "title", "body")

    def __init__(self, d: dict):
        self.state = (d.get("state") or "").lower() or None
        self.created_at = ts(d.get("created_at"))
        self.title = d.get("title") or ""
        self.body = d.get("body") or ""

    @property
    def is_open(self) -> bool:
        return self.state == "open"


def _gh_fetch_issue(n: int) -> dict | None:
    """Fetch brut d'une issue, cachee par numero. Retourne None si PR/404/malformed.

    #13725 — la representation REST `issues/{n}` expose `pull_request` pour
    les PRs (et pas pour les issues), et rend un 404 franc pour un numero
    inexistant. La cle `pull_request` est donc le discriminant canonique.
    """
    if n not in _ISSUE_INFO_CACHE:
        try:
            d = gh_json(["api", "repos/" + REPO + "/issues/" + str(n)])
        except Exception:
            _ISSUE_INFO_CACHE[n] = None
            return None
        if not isinstance(d, dict) or "pull_request" in d:
            _ISSUE_INFO_CACHE[n] = None
        else:
            _ISSUE_INFO_CACHE[n] = IssueInfo(d)
    return _ISSUE_INFO_CACHE[n]


def gh_issue_info(n: int) -> IssueInfo | None:
    """#14218 — snapshot d'une issue, source des 4 conditions voie 3.

    Renvoie ``None`` si ``n`` n'est pas une issue (PR, 404, payload non-dict).
    Mêmes garanties de cache que #13725.
    """
    return _gh_fetch_issue(n)


def gh_issue_created(n: int) -> datetime | None:
    """#13495 — createdAt de l'issue #n, ou None si elle n'existe pas (ou PR).

    Compat historique : ``collect_followup_lifts`` lit aujourd'hui le
    snapshot via ``gh_issue_info``. Ce wrapper reste expose pour les
    anciens tests d'integration et ne change pas de semantique : il rend
    ``IssueInfo.created_at`` pour une issue, ``None`` sinon.

    #13725 — le garde passait par ``gh issue view --json isPullRequest``,
    un champ que ``gh issue view`` N'EXPOSE PAS. Le discriminant correct
    est REST : ``issues/{n}`` porte la cle ``pull_request`` UNIQUEMENT pour
    une PR.
    """
    if n in _ISSUE_CREATED_CACHE:
        return _ISSUE_CREATED_CACHE[n]
    info = gh_issue_info(n)
    _ISSUE_CREATED_CACHE[n] = info.created_at if info is not None else None
    return _ISSUE_CREATED_CACHE[n]


# #13725 -- la voie 3 exige un report DELIBERE, pas une mention.
#
# La spec de B.0 dit « issue de suivi ouverte et nommee AVANT le merge
# (reportee sciemment) » : c'est un GESTE, pas une coincidence lexicale.
# L'implementation d'origine creditait tout `#N` hors citation resolvant en
# issue -- donc « cf. le defaut #13316 », « Tell c.11145 #13649 », un renvoi
# de code vers #12319 : autant de reports valides eteignant n'importe quelle
# reserve anterieure. Le trou etait INVISIBLE tant que `gh_issue_created`
# levait sur tout (meme incident, cf. sa docstring) : reparer le resolveur
# SEUL convertissait un gate qui SUR-bloque en trappe qui s'ouvre en
# silence -- strictement pire, une trappe ne se voit pas.
#
# Mesure au moment du fix, sur les 37 PRs ouvertes : 61 reports auraient ete
# credites par le seul resolveur repare, dont 15 deliberes et **46 par
# mention incidente** (75 %).
#
# Le predicat est lexical et PROCHE : le marqueur de report doit vivre dans
# la meme ligne que la reference, ou dans les 200 caracteres qui la
# precedent -- de sorte qu'un commentaire disant « issue de suivi » a propos
# d'une chose et citant `#N` a propos d'une autre ne credite rien.
_FOLLOWUP_MARK = re.compile(
    "issue\\s+de\\s+suivi|issues?\\s+de\\s+report|follow[-\\s]?up|"
    "report(?:e|\u00e9)e?\\s+sciemment|suivi\\s+ouverte",
    re.I)


def _is_deliberate_followup(stripped: str, pos: int) -> bool:
    """Le marqueur de report vit-il au voisinage immediat de la reference ?"""
    line_start = stripped.rfind("\n", 0, pos) + 1
    line_end = stripped.find("\n", pos)
    line = stripped[line_start:line_end if line_end != -1 else len(stripped)]
    if _FOLLOWUP_MARK.search(line):
        return True
    return bool(_FOLLOWUP_MARK.search(stripped[max(0, pos - 200):pos]))


def _issue_references_pr(issue: "IssueInfo", pr_number: int) -> bool:
    """#14218 condition 4 : l'issue cite le numero de la PR dans son titre OU
    son corps. Pas une regex stricte (les PRs sont referencees de maniere
    heterogene : « #14218 », « PR #14218 », « pull/14218 », « PRs #14218 »)
    mais un test simple : le numero doit apparaitre en mot-borne.

    Garde anti-self : on cherche la reference seulement si ``pr_number``
    est distinct de l'issue (defense en profondeur ; `_FOLLOWUP_MARK`
    pose deja cette borne par `_is_deliberate_followup`).
    """
    needle = r"(?<![A-Za-z0-9_])" + str(pr_number) + r"(?![A-Za-z0-9_])"
    return bool(re.search(needle, issue.title)) or bool(re.search(needle, issue.body))


def collect_followup_lifts(pr_data: dict, cutoff: datetime,
                           issue_info=None) -> list[tuple]:
    """#13495 + #14218 — voie 3 de B.0 : « issue de suivi ouverte et nommée
    AVANT le merge (reportée sciemment) ».

    Conditions verifiees ICI (par collecte, identiques pour toutes les
    reserves de la PR) :

    1. ``#N`` est une **issue** (le payload GitHub distingue issues/PRs via
       ``pull_request``, cf #13725).
    2. ``#N`` est **OUVERTE** au moment du check (la voie 3 perd son sens sur
       une issue fermee : la suite serait ailleurs, pas en suivi).
    3. ``#N`` a ete creee **avant le cutoff** (proxy du « avant le merge »,
       l'invariant ancien).
    4. La reference est **deliberee** (le `_FOLLOWUP_MARK` la distingue d'une
       citation de contexte, cf #13725).

    Conditions verifiees LA-BAS (par reserve, dans `analyse`) :

    5. ``#N`` a ete creee **apres** la reserve qu'elle reporte — sinon une
       issue preexistante sans rapport ferait l'affaire.
    6. ``#N`` **reference la PR** dans son titre ou son corps — sinon le
       lien entre report et reserve n'est pas etabli.

    Une phrase de l'auteur de la PR ne leve pas la reserve d'un tiers
    (voie 1 close pour lui, #11145), mais un report nomme avant merge est
    un geste delibere que B.0 credite — l'auteur de la PR est explicitement
    ouvert comme nommeur (borne #13563).

    `issue_info=None` coupe la voie — `analyse()` reste pur pour les tests
    (aucun appel reseau n'y est tolere). Retourne des tuples
    ``(instant, nommeur, IssueInfo)`` ; `analyse` applique les conditions
    5 et 6 par reserve. La PR-resolving-callback retourne ``IssueInfo`` ou
    ``None`` ; on filtre ``None`` (PR, 404, etc.).
    """
    if issue_info is None:
        return []
    out: list[tuple] = []
    self_ref = pr_data.get("number")
    for c in (pr_data.get("comments") or []):
        if not can_lift(c):
            continue
        t = ts(c.get("createdAt"))
        if t is None or not t < cutoff:
            continue
        stripped = _strip_quoted(c.get("body") or "")
        for m in re.finditer(r"#(\d+)", stripped):
            n = int(m.group(1))
            if n == self_ref:
                continue
            if not _is_deliberate_followup(stripped, m.start()):
                continue
            info = issue_info(n)
            if info is None:
                continue
            if not info.is_open:
                continue  # condition 2
            if info.created_at is None or not info.created_at < cutoff:
                continue  # condition 3
            out.append((t, (c.get("author") or {}).get("login", ""), info))
            break
    return out


# #13639 -- une levee dont la PREUVE citee n'est plus dans la PR. Sur #13557,
# la levee citait le commit 2d6e4c3642 (« corrige dans ce commit ») ; un
# force-push ulterieur avait rembobine ce commit, et le gate restait vert :
# la phrase etait honnete au moment ou elle fut ecrite, mais ce qu'elle
# nommait n'existait plus au merge. Le principe B.0 (« ce qui leve une
# remarque est une phrase ») suppose que la phrase dise VRAI au merge ; une
# levee qui cite une preuve absente ne dit plus vrai.
#
# Refus ETROIT deliberement : (a) le corps de levee cite un SHA, (b) ce SHA
# n'appartient pas aux commits de la PR (match par prefixe), (c) il RESOUD
# cote serveur, (d) son message se RAPPORTE a cette PR (`#N`, N = numero de
# la PR ou issue citee dans le titre/corps). (c)+(d) distinguent le
# rembobinage (#13557) de la citation de CONTEXTE (« comme fixe en abc1234
# sur l'autre PR ») : la seconde reste une levee valide, juste signalee.
# En cas de doute : avertir (A RELIRE), jamais bloquer.
_SHA_CITED = re.compile(r"\b[0-9a-f]{7,40}\b")


def _cited_shas(body: str) -> set[str]:
    """SHAs cites dans un corps : 7-40 hex, avec AU MOINS une lettre.

    Un token 100% numerique de 7+ chiffres (une date 20260830, un run-id)
    est hex-compatible mais n'est quasi jamais un SHA -- l'exiger lettree
    evite de partir resoudre une date cote serveur pour rien.
    """
    out: set[str] = set()
    for m in _SHA_CITED.finditer((body or "").lower()):
        tok = m.group(0)
        if any(ch in "abcdef" for ch in tok):
            out.add(tok)
    return out


# Proximite maximale (caracteres) entre un SHA cite et un marqueur de levee
# VIVANT pour que le SHA compte comme la PREUVE avancee par la phrase.
_LIFT_SHA_PROXIMITY = 150


def _sha_in_lift_claim(lift_body: str, sha: str) -> bool:
    """Le SHA est-il cite DANS la clause de levee (proximal du marqueur) ?

    Mesure au deploiement meme de #13639 (PR #13631) : la levee d'ai-01
    citait `e408b2fce` a ~2000 chars du marqueur, dans un paragraphe
    forensique qui disait explicitement « c'est main qui a avance » --
    une reference de CONTEXTE, pas une preuve. Refuser cette levee (ou
    meme l'avertir) etait un faux positif : la phrase etait valide et sa
    preuve etait inline (la clé Grain citee dans le commentaire meme).
    Seul un SHA PROXIMAL du marqueur vivant est ce que la phrase avance ;
    un SHA distant est une citation annexe et ne doit etre ni refuse ni
    signale. Marqueurs et SHA sont cherches dans le MEME espace de
    coordonnees (le corps unaccente), insensible a toute variation de
    longueur du _unaccent.
    """
    norm = _unaccent(lift_body or "")
    markers = _live_lift_positions(norm)
    if not markers:
        return False
    low = norm.lower()
    start = 0
    while (i := low.find(sha, start)) != -1:
        if min(abs(i - p) for p in markers) <= _LIFT_SHA_PROXIMITY:
            return True
        start = i + 1
    return False


def _message_refs_pr(message: str, pr_refs: set[str]) -> bool:
    """Le message de commit reference-t-il exactement un PR/issue de la liste ?

    Substring check trop generique : `#13639` matchait un message contenant
    `#136390` (ticket adjacent cite par hasard), declenchant un refus au lieu
    d'un simple avertissement (NanoClaw c.702 sur #13641). Le bon test est
    l'extraction/tokenisation exacte des references `#\\d+` : la PR/issue
    doit apparaitre comme un MOT COMPLET du message, pas comme prefixe d'un
    identifiant plus long.

    Retourne True si au moins une ref de `pr_refs` apparait comme token
    isole (apres `#`, jusqu'au prochain non-alphanumerique) dans `message`.
    """
    if not message or not pr_refs:
        return False
    # Tokeniser toutes les references `#\\d+` du message, garder UNIQUEMENT
    # la portion numerique (le `#` est implicite).
    cited = {m.group(1) for m in re.finditer(r"#(\d+)", message)}
    return bool(cited & pr_refs)


def _resolve_absent_sha_messages(data: dict, cap: int = 5) -> dict[str, str]:
    """Resoudre cote serveur les SHAs cites mais absents des commits de la PR.

    S'execute UNIQUEMENT dans le chemin `gate` (reseau) : `analyse` reste
    pur et lit le resultat via `data["_absent_sha_messages"]`. Sans entree
    resolue, `analyse` reste en mode avertissement -- l'audit retro, qui
    n'appelle jamais ceci, ne peut donc pas produire de faux blocage.
    Capped a `cap` appels : plus de 5 SHAs absents cites sur une seule PR
    est extraordinaire, et chaque appel paie un aller-retour API.
    """
    oids = {(c.get("oid") or "").lower() for c in (data.get("commits") or [])}
    oids.discard("")
    if not oids:
        return {}
    cited: set[str] = set()
    for c in (data.get("comments") or []) + (data.get("reviews") or []):
        cited |= _cited_shas(c.get("body") or "")
    absent = sorted(s for s in cited if not any(o.startswith(s) for o in oids))
    messages: dict[str, str] = {}
    for sha in absent[:cap]:
        try:
            commit = gh_json(["api", f"repos/{REPO}/commits/{sha}"])
        except subprocess.CalledProcessError:
            continue  # non resoluble -> analyse restera en mode avertissement
        head = ((commit.get("commit") or {}).get("message") or "").split("\n")[0]
        if head:
            messages[sha] = head
    return messages


def can_lift(comment: dict) -> bool:
    """Ce commentaire est-il capable de LEVER un nit qui le precede ?

    Seule une reponse d'un humain ou d'un agent, qui dit quelque chose, peut
    lever une remarque. Sont exclus :
      - les bots de CI (`github-actions` & co) : ils postent a chaque push et
        n'ont aucun compte a rendre sur une remarque de review ;
      - les tags de protocole nus (`[ACK]`, `[DISPATCH...]`, `[CLAIMED]`) :
        ils ne nomment aucun nit.

    Sans ce filtre, l'organe reproduit exactement le defaut qu'il traque :
    n'importe quel bruit poste entre le nit et le merge eteint le nit. Sur ce
    depot ou les bots commentent a chaque push, ce failure mode est la regle,
    pas l'exception (defaut trouve par Hermes en review de #11045).

    Limite connue et assumee : on ne verifie pas que la reponse *nomme* la
    remarque — cela demanderait du NLP. Un commentaire humain hors-sujet leve
    donc encore un nit (faux negatif residuel). Auteur + protocole eliminent le
    gros du bruit sans pretendre lire le sens.
    """
    login = (comment.get("author") or {}).get("login", "")
    if login in BOT_LOGINS:
        return False
    body = (comment.get("body") or "").lstrip()
    if not body:
        return False
    # #12908 : la phrase exigée est une levée VIVE — un tag de protocole
    # qui narre « une levée explicite » (exigence, pas geste) ne peut
    # toujours pas lever.
    if body.startswith(AGENT_PREFIXES) and not has_live_lift(body):
        return False
    return True


def classify(author: str, body: str) -> str | None:
    """'HUMAN' (nit user, UI web) | 'BOT-CONCERN' (reviewer avec reserves) | None."""
    if author in BOT_LOGINS or not body:
        return None
    stripped = body.lstrip()
    # #12143 — Hermes severity glyphes (subordonne LIFT_MARKERS, fix concomitant
    # du PR #12148 fondateur) : un glyphe est une EMISSION, et une emission
    # ne se laisse pas eteindre par un mot de levee (LGTM, Merged, etc.) pose
    # ailleurs dans la meme prose. Sans cette subordination, 3 des 4 cas reels
    # mesures par ai-01 sur PR #12148 — #12083 (🟡 SPY 6/8 contredit),
    # #12059 (🟡 hyperparametres GRPO contredits), #12077 (🟡 claim img_020
    # contredite) — etaient absorbes par le LGTM en tete avant evaluation de
    # CONCERN_MARKERS. Mesure corpus 80 PRs (2026-08-20T16:27Z →
    # 2026-08-21T12:46Z) : avant = 0 flagged, apres = 3 flagged.
    # Principe borne : un LGTM *scopé* sur une partie du diff (« LGTM
    # structural / 🟡 ... ») ne leve pas la partie non-LGTM. `has_live_marker`
    # preserve l'hygiene `_is_cited`, donc un glyphe cite (« Re 🟡 : leve »)
    # reste muet — la sous-accusation coute un merge, la sur-accusation coute
    # une relecture. Aucun body sans glyphe ne change de classement : la
    # table de distribution d'ai-01 reste exacte.
    # #13083 (2e instance) — SYMETRIE de l'etage lift : le concern est evalue
    # mention-aware (`_strip_mentioned_verdicts`), le lift etait un substring
    # brut sur le body ENTIER. Consequence mesuree (#12896) : « une formule de
    # levee conditionnelle », « une levee reelle », « ses conditions de levee »
    # (mentions nominales — la prose NOMME le concept, elle ne l'emets pas)
    # eteignaient une reserve vivante — nommer une resolution valait la
    # prononcer, alors que nommer une reserve ne vaut pas l'emettre (#11636
    # symetrique). Fusion au rebase 2026-08-29 : le miroir LIFT #12908 deja
    # sur main (cb95b65020, `_lift_is_narrated` + `LIFT_NARRATION_CITERS`)
    # couvre les mentions nominales par sa fenetre de determinants (de/une,
    # la/son, apres/avant/sans, obtenir/exige...) — il est utilise TEL QUEL ;
    # la presente instance y ajoute (a) la SURFACE : l'etage concern lit
    # `_strip_mentioned_verdicts(_strip_quoted(body))` (L. ci-dessous), le
    # lift lit la meme surface stripee — un marqueur de levee DANS une quote
    # ou un verdict mentionne ne peut pas lever ; (b) la regle FLECHE : « ->
    # je merge » est une derivation conditionnelle (si sign-off alors merge,
    # #12896 c.5422307622), syntaxiquement prouvee par la fleche, pliee dans
    # `_live_lift_positions`. Importer `_is_cited` ENTIER casserait des
    # annonces reelles trans-sentence (« n'est pas une levee. **Mergée.** » —
    # le « pas » de la phrase precedente tuerait le Mergé de la suivante,
    # 4 tests du corpus) : seule la fleche est reprise.
    if (has_live_lift(_strip_mentioned_verdicts(_strip_quoted(body)))
            and not _lift_cancelled(_strip_quoted(body))
            and not has_live_marker(_strip_quoted(body), SEVERITY_GLYPHS)
            # #12836 / #12798 : une revalidation COMMENT_WITH_CONCERNS peut
            # narrer la levee anterieure qu'elle REFUTE. Seul un verdict Hermes
            # formel place AVANT le mot de levee garde la reserve vivante ; les
            # #12908 : le verdict B.0 (« **BLOCKED** ») est un verdict de
            # concern a part entiere pour cette comparaison positionnelle.
            # levees explicites historiques (« je leve ma CHANGES_REQUESTED »)
            # restent admissibles parce que leur ordre est inverse.
            and not _formal_concern_precedes_lift(body)):
        return None  # annonce de levee / de merge : resolution, pas reserve
    # (construction conditionnelle « et je merge » : voir _lift_cancelled —
    # l'annonce conditionnee n'est pas une levee, SAUF levee explicite d'auteur
    # en amont (#12074) ; le commentaire continue sinon)
    # #13083 — un BLOCAGE coordinateur, le symetrique non traite de #11639 :
    # l'organe modelisait un coordinateur qui LEVE (trappe [OVERRIDE] lane),
    # pas un coordinateur qui BLOQUE. Traite a part de CONCERN_MARKERS : le
    # blocage ne se leve PAS par les regles des nits ordinaires (cf `analyse`,
    # lieu de la borne stricte) — le mettre dans la liste le downgraderait en
    # reserve levable trop facilement. La detection est structurelle, pas une
    # sous-chaine (cf `_block_emitted`).
    if _block_emitted(body):
        return "BLOCK"
    # #13598 — EMISSION informelle d'un LIFT_OVERRIDE_LOGINS : le
    # coordinateur tient un hold en francais courant (« ne pas merger sur
    # les verts », « j'attends le run GPU », etc.). Avant : None. Apres :
    # BOT-CONCERN. Bornee a 1 auteur (cout whack-a-mole minimal) et a un
    # predicat structurel (verbe d'injonction + pas de levee ni d'override).
    # Les commentaires anodins (« merci », « vu », « ok ») ne portent aucun
    # verbe d'injonction et restent muets (acceptance #13598 point 2).
    if author in LIFT_OVERRIDE_LOGINS and _coordinator_emission_informal(body):
        return "BOT-CONCERN"
    if has_live_marker(body, (VERDICT_POSITIVE,)):
        return None  # verdict structurel positif rendu : il decide, la prose ne compte plus
    # #11636 : la recherche porte le body nettoye de ses verdicts MENTIONNES —
    # un rapport de correction qui nomme le verdict qu'il corrige n'emet pas
    # de reserve. Uniquement pour CONCERN_MARKERS et l'etage lift (symetrie
    # #13083 ci-dessus) : VERDICT_POSITIVE garde le body brut.
    live_concern = has_live_marker(_strip_mentioned_verdicts(_strip_quoted(body)), CONCERN_MARKERS)
    # #13938 — exemption de « comment-only Hermes » : quand un reviewer pose
    # `[Hermes] COMMENT_WITH_CONCERNS` (verdict de pure emission, force a
    # state:COMMENTED par #12311) ET que le corps declare explicitement
    # que rien n'est bloquant, la review n'est PAS une reserve. Convention
    # Tell c.589-L1 ★★★ strict assimile un tel commentaire a une APPROVED
    # pour le merge-gate. Garde stricte : l'exemption ne s'applique PAS
    # aux verdiicts de blocage strict (CHANGES_REQUESTED, REQUEST_CHANGES,
    # NEEDS_CHANGES, BLOCKED, SUSPECT_*, STRUCTURAL_ONLY) — verifie par
    # `_comment_only_prefix`. Fuite classee Tell NEW c.840 ★★★ sustained.
    if (
        live_concern
        and _comment_only_prefix(body)
        and _review_explicit_non_blocking(body)
        # #13951 Concern 1 : la phrase de non-blocage ne peut pas effacer un
        # marqueur de prose (« avant merge ») ni un glyphe (🟡) emis dans la
        # MEME review. L'exemption ne tient que si le prefixe CWC est le SEUL
        # concern vivant du corps.
        and _sole_live_concern_is_comment_prefix(body)
    ):
        return None
    if not live_concern and _HUMAN_VERDICT_RE.search(body):
        return None  # verdict humain positif (APPROVE / APPROVED / LGTM) SANS reserve vivante : equivalent state:APPROVED
    if not live_concern and has_live_marker(body, POSITIVE_MARKERS):
        return None  # approbation sans reserve vivante : la review conclut, ne reserve pas
    if stripped.startswith(AGENT_PREFIXES):
        # Tag de protocole agent : informatif, pas un nit — sauf s'il porte une reserve.
        return "BOT-CONCERN" if live_concern else None
    if "\r\n" in body:
        return "HUMAN"
    if live_concern:
        return "BOT-CONCERN"
    return None


def review_threads(pr: int) -> list[dict]:
    """Threads inline (3e surface, absente de `gh pr view --json`)."""
    query = """
    query($owner:String!,$repo:String!,$n:Int!){
      repository(owner:$owner,name:$repo){
        pullRequest(number:$n){
          reviewThreads(first:100){nodes{
            isResolved isOutdated path line
            comments(first:1){nodes{author{login} body createdAt}}
          }}
        }
      }
    }"""
    owner, name = REPO.split("/")
    data = gh_json([
        "api", "graphql", "-f", f"query={query}",
        "-F", f"owner={owner}", "-F", f"repo={name}", "-F", f"n={pr}",
    ])
    nodes = data["data"]["repository"]["pullRequest"]["reviewThreads"]["nodes"]
    # Pas de pagination : au-dela de 100 threads inline, les suivants seraient
    # invisibles. Plutot que de tronquer en silence — le mode d'echec que ce
    # script existe pour combattre — on le DIT. Theorique sur ce depot ; si le
    # message apparait, paginer devient necessaire, pas optionnel.
    if len(nodes) == 100:
        print(f"  [!] PR #{pr}: 100 threads inline retournes (plafond `first:100`) "
              "— d'eventuels threads supplementaires ne sont PAS analyses.",
              file=sys.stderr)
    out = []
    for t in nodes:
        first = (t.get("comments") or {}).get("nodes") or [{}]
        c = first[0]
        out.append({
            "resolved": bool(t.get("isResolved")),
            "outdated": bool(t.get("isOutdated")),
            "path": t.get("path"),
            "line": t.get("line"),
            "author": (c.get("author") or {}).get("login", "?"),
            "body": c.get("body", ""),
            "createdAt": c.get("createdAt"),
        })
    return out


def improper_dismissals(pr: int) -> set[str]:
    """Auteurs de review dont la reserve a ete dismissee par QUELQU'UN D'AUTRE.

    `gh pr view --json reviews` ne dit ni qui a dismisse ni quand : il ne rend
    que l'etat final `DISMISSED`. L'acteur vit dans la timeline REST
    (`review_dismissed`), l'auteur de la review dans les reviews REST — les deux
    se joignent par l'`id` NUMERIQUE (le champ `id` de `gh pr view` est un
    node-id GraphQL, `PRR_kwDO...`, non comparable au `review_id` entier).

    Retourne des LOGINS d'auteurs de review, pas des ids : la reserve est
    reappariee par auteur dans `analyse`. Sur-approximation assumee quand un
    meme auteur a deux reviews dismissees dont une legitimement — un gate se
    trompe du cote qui bloque, jamais du cote qui laisse passer.

    Non cable sur `audit()` : deux appels API par PR, pour un chemin retrospectif
    ou l'enforcement n'a plus lieu. Le gate pre-merge est le point de controle.
    """
    try:
        reviews = gh_json(["api", f"repos/{REPO}/pulls/{pr}/reviews", "--paginate"])
        events = gh_json(["api", f"repos/{REPO}/issues/{pr}/timeline", "--paginate"])
    except Exception:
        return set()  # timeline illisible : on retombe sur l'ancien comportement
    if not isinstance(reviews, list) or not isinstance(events, list):
        return set()
    author_of = {
        r.get("id"): ((r.get("user") or {}).get("login") or "")
        for r in reviews if isinstance(r, dict)
    }
    improper: set[str] = set()
    for e in events:
        if not isinstance(e, dict) or e.get("event") != "review_dismissed":
            continue
        actor = ((e.get("actor") or {}).get("login") or "")
        rid = (e.get("dismissed_review") or {}).get("review_id")
        emitter = author_of.get(rid)
        if not emitter:
            continue
        if actor == emitter or actor in LIFT_OVERRIDE_LOGINS:
            continue
        improper.add(emitter)
    return improper


def _names_author(body: str, author: str) -> bool:
    """``body`` mentionne-t-il ``author`` comme identite, pas par hasard ?

    #13399 : un reviewer tiers n'approuve la reserve d'une lane que s'il NOMME
    cette lane — sinon un APPROVED generique eteindrait toutes les reserves de
    la PR. La frontiere de mot est posee par non-caractere d'identite (un login
    contient `-` et `.`, donc `\\b` est fragile autour d'eux : `clusterManager-Myia`
    n'a pas de frontiere au tiret). On exige un mot-de-login complet delimitere.
    """
    if not body or not author:
        return False
    return re.search(r"(?<![A-Za-z0-9_.-])" + re.escape(author) + r"(?![A-Za-z0-9_.-])",
                     body) is not None


# #14216 — langage de LEVEE portee a la reserve nommee (affirmatif). La
# nomination seule ne suffit pas : le corps fondateur de #14166 portait
# « la reserve de clusterManager-Myia n'est pas concernee par cette levee »
# — le nom ETAIT present, dans une phrase d'EXCLUSION.
_SCOPE_LIFT_RE = re.compile(r"(?i)\blev\w*\b|\blift\w*\b")
# #14216 — phrase qui nomme la reserve pour l'EXCLURE de la levee. Accents
# neutralises (le depot ecrit les deux), formes FR d'abord.
_SCOPE_NEGATION_RE = re.compile(
    r"(?i)\bn['’]\s*\w+\s+pas\b"
    r"|\bne\s+(?:\w+\s+){0,3}pas\b"
    r"|\bpas\s+(?:concerne\w*|leve\w*|lift\w*|inclus\w*|touch\w*)\b"
    r"|\bhors\s+(?:du\s+|de\s+la\s+)?(?:scope|perimetre|champ)\b"
    r"|\b(?:exclu\w*|non\s+leve\w*|reste\s+ouverte?)\b"
    r"|\b(?:not|isn['’]t)\s+(?:concerned|lifted|in\s+scope)\b"
    r"|\b(?:remains\s+open|out\s+of\s+scope)\b")


def _scope_lifted_sentence(body: str, needle_re) -> bool:
    """Une PHRASE porte-t-elle le nom ET une levee affirmative de la reserve ?

    Phrase = segment entre [.!?\\n]. Pour chaque occurrence du nom (login ou
    persona), la phrase qui la contient doit porter un mot de levee SANS
    negation d'exclusion — « je leve aussi la reserve de <login> » scope,
    « la reserve de <login> n'est pas concernee par cette levee » non.
    """
    for m in needle_re.finditer(body):
        s0 = max(body.rfind(c, 0, m.start()) for c in ".!?\n") + 1
        ends = [j for j in (body.find(c, m.end()) for c in ".!?\n")
                if j != -1]
        s1 = min(ends) if ends else len(body)
        sent = _unaccent(body[s0:s1]).lower()
        if _SCOPE_LIFT_RE.search(sent) and not _SCOPE_NEGATION_RE.search(sent):
            return True
    return False


def _override_scopes_reserve(lift_body: str, nit_author: str) -> bool:
    """#14216 — un OVERRIDE coordinateur nomme-t-il LA reserve qu'il leve ?

    La trappe #11639 agissait par PR, jamais par reserve : un seul
    commentaire portant le marqueur eteignait TOUTES les reserves ouvertes,
    y compris celle d'un tiers que le coordinateur n'a ni legitimite ni
    intention de lever (#14166 : la levee legitime de sa reserve de
    collision a emporte la reserve structurelle Hermes, et la PR serait
    apparue mergeable si l'organe n'avait pas ete relance APRES le post).
    Un override ne leve desormais une reserve d'AUTRUI que s'il la nomme
    dans une phrase de levee AFFIRMATIVE — le corps fondateur portait le
    login dans une phrase d'exclusion (« n'est pas concernee par cette
    levee ») : le nom seul n'est pas un scope.

    Deux formes reconnues, toutes deux presentes dans l'historique reel :

    1. le login de l'auteur de la reserve — frontiere d'identite de
       ``_names_author`` (« Levee des reserves : la mienne et celle de
       clusterManager-Myia aussi ») ;
    2. le nom de persona — « Levée de la réserve Hermes » (#11639, forme
       canonique historique) quand l'auteur de la reserve est la persona
       Hermes/NanoClaw ou le self-bot jsboige qui la porte.

    Les reserves de l'auteur de la levee restent couvertes sans nomination
    (branche self de ``_lift_eligible``). Un nit d'auteur inconnu (compte
    supprime) reste levable : un scope ne peut pas nommer ce qui n'a pas
    de nom.
    """
    if not nit_author:
        return True
    body = lift_body or ""
    author_re = re.compile(r"(?<![A-Za-z0-9_.-])" + re.escape(nit_author)
                           + r"(?![A-Za-z0-9_.-])")
    if _scope_lifted_sentence(body, author_re):
        return True
    if nit_author in PERSONA_ALIAS_LOGINS or nit_author == "jsboige":
        return _scope_lifted_sentence(
            body, re.compile(r"(?i)\b(?:hermes|nanoclaw)\b"))
    return False


def analyse(pr_data: dict, threads: list[dict], cutoff: datetime,
            issue_info=None, dismissed_improperly=None) -> dict:
    """cutoff = mergedAt (audit retro) ou now (gate pre-merge)."""
    commits = [ts(c.get("committedDate")) for c in (pr_data.get("commits") or [])]
    commits = [c for c in commits if c]
    last_commit = max(commits) if commits else None
    pr_author = (pr_data.get("author") or {}).get("login", "")
    pr_number = pr_data.get("number")

    # #11145 — borne d'auteur, durcie par #12836 : seule une levee de l'auteur
    # de la reserve compte. #12798 a montre pourquoi PR_AUTHOR n'est pas une
    # confirmation : l'auteur de la PR avait declare la reserve Hermes levee,
    # l'organe etait vert, mais le livrable committe restait un stub sans sortie
    # vLLM. Une reponse de PR_AUTHOR documente le traitement ; elle ne remplace
    # pas la re-review du tiers. L'arbitrage coordinateur nomme [OVERRIDE]
    # ci-dessous reste le seul echappement tiers.

    # Fenetre 05-29..06-04 (#1958) : la RE-REVIEW APPROVED. Le reviewer qui
    # revient approuver apres sa demande de changements A dit que la reserve
    # est levee — le state GitHub natif porte plus de sens que le body (une
    # re-review Hermes narre l'ancien verdict en le citant, sans mot de
    # levee). Seul APPROVED compte : une re-review COMMENTED qui re-emet une
    # reserve (« NOT FIXED », #2298) ne doit rien eteindre, et l'agent
    # d'exclusion can_lift ne s'applique pas — un state APPROVED n'est pas du
    # bruit de protocole, meme depuis un reviewer bot.
    approved_rereviews = [
        (ts(r.get("submittedAt")), (r.get("author") or {}).get("login", ""),
         r.get("body", ""))
        for r in (pr_data.get("reviews") or [])
        if r.get("state") == "APPROVED"
        and (r.get("author") or {}).get("login", "") not in BOT_LOGINS
    ]
    approved_rereviews = [x for x in approved_rereviews if x[0] is not None]

    def _approved_lifts_reserve(reserve_author: str, reserve_when: datetime,
                                pr_author: str) -> bool:
        """Une re-review APPROVED leve-t-elle la reserve de ``reserve_author`` ?

        #13399 — le defaut constate sur #13299 n'etait pas l'absence de re-review,
        mais le fait que ``approved_rereviews`` ne levait que la reserve dont
        l'auteur de l'APPROVED etait l'auteur (auto-approbation). Un reviewer
        TIERS (ai-01) qui approuve en nommant la reserve d'une lane la leve
        aussi. Le garde-fou #12798 reste : seule l'identite de l'auteur tranche,
        jamais un commit ni un SAR. Deux voies, toutes posterieures a la reserve :

        1. **Re-review de l'auteur** (``auteur_approved == reserve_author``) :
           legitime uniquement si l'auteur de la reserve n'est pas l'auteur de la
           PR. Sous le self-review cap (#12319) l'auteur de la reserve == l'auteur
           de la PR == jsboige, et une APPROVED de ce compte est une
           auto-approbation qui demontre rien — refuse.
        2. **Approbation d'un tiers nommant la reserve** (auteur different de la
           reserve ET de l'auteur de la PR, corps mentionnant le login de la
           reserve) : le coordinateur confirme par ecrit que le point de la lane
           est traite. Un APPROVED completement generique (qui n'identifie pas
           la reserve) ne leve rien — sinon tout approval d'un coordinateur
           eteindrait toutes les reserves de la PR.
        """
        for (t, app_author, app_body) in approved_rereviews:
            if t is None or t <= reserve_when:
                continue
            if app_author == reserve_author:
                if reserve_author != pr_author:
                    return True
                continue  # auto-approbation self-review : refusee, voir ci-dessous
            if app_author != pr_author and _names_author(app_body, reserve_author):
                return True
        return False

    def _lift_eligible(lift_author: str, nit_author: str,
                       lift_body: str = "") -> bool:
        if lift_author == nit_author:
            return True
        # #13609 -- alias de persona Hermes/NanoClaw cross-login. La persona
        # parle sous clusterManager-Myia ET jsboige. Quand elle leve SA
        # propre reserve sous l'autre login, c'est sa levee. Le marqueur
        # `[Hermes]` / `[NanoClaw]` / `[Hermes self-bot]` dans le corps
        # identifie la source ; l'autre cote de l'alias est dans
        # `PERSONA_ALIAS_LOGINS` (= clusterManager-Myia) pour eviter qu'une
        # lane (qui pousse sous jsboige) s'auto-promeuve en collant le
        # marqueur dans un commentaire ordinaire. Les deux conditions sont
        # obligatoires : sans marqueur, jsboige reste l'identite de poussee
        # partagee des lanes (#13316), rien n'est leve.
        if (lift_author == "jsboige"
                and nit_author in PERSONA_ALIAS_LOGINS
                and _PERSONA_MARKERS_RE.search(lift_body or "")):
            return True
        # #13495 — la trappe coordinateur ci-dessous ne s'ouvre pas pour
        # l'auteur de la PR : sinon la voie 3 (report par issue nommee) serait
        # contournable par la porte de service qu'elle vient d'ouvrir — la
        # forme d'auto-levee pour laquelle #13316 a deja retire jsboige des
        # comptes de levee.
        if lift_author == pr_author:
            return False
        # #11639 : l'override NOMME du coordinateur — l'arbitre tiers de B.0.
        # La restriction d'auteur reste la regle pour tout le monde (elle
        # bloque l'auto-levee d'un bystander, #11145) ; seule la trappe ecrite
        # s'ajoute. Un OVERRIDE sans phrase de levee n'entre meme pas ici :
        # can_lift l'a ecarte (tag de protocole nu), et explicit_lifts exige
        # un LIFT_MARKER.
        # #13030 -- search sur le corps ENTIER retire : une citation du
        # marqueur (documentation, dispatch, post-mortem, DM recopie)
        # posait l'override. Seule la forme POSEE en tete de ligne compte.
        # #13316 -- jsboige n'entre plus : identite de poussee partagee des
        # lanes (self-review cap #12319), un override jsboige est
        # indiscernable d'une auto-levee de lane (replay #12737).
        m = OVERRIDE_LANE.search(lift_body or "")
        if not (lift_author in LIFT_OVERRIDE_LOGINS and m is not None):
            return False
        # #14216 — l'override est scope PAR RESERVE, plus par PR : sans
        # nomination de la reserve d'autrui (login ou persona Hermes), il ne
        # leve que les siennes. La trappe reste fermee a l'auteur de la PR
        # (garde ci-dessus) : le scope n'ouvre pas la porte d'auto-levee.
        return _override_scopes_reserve(lift_body or "", nit_author)

    # Fenetre 2026-08-16 (#11222) : les temps plats ne suffisent pas pour un
    # CHANGES_REQUESTED. Une PHRASE explicite de levee (LIFT_MARKER non
    # conditionnel) dans un commentaire qui peut lever reste une levee pour
    # l'etat de review — c'est la reponse ecrite que B.0 exige. On garde
    # l'auteur pour la branche dedicated ci-dessous.
    # #12319 : explicit_lifts est desormais LE regime des nits portes par un
    # COMMENTAIRE ou une review COMMENTED aussi — l'ancienne branche elif
    # consultait lift_events (tout commentaire can_lift), et la borne d'auteur
    # #11145 est vacue sur ce depot : Hermès poste sous jsboige (self-review
    # cap) et la lane pousse sous jsboige, donc nit_author == pr_author ==
    # "jsboige" sur presque chaque PR — n'importe quel commentaire posterieur
    # de la lane eteignait la reserve de son propre reviewer. B.0 : ce qui
    # leve une remarque est une PHRASE, pas un commentaire de protocole.
    explicit_lifts = [
        (ts(c["createdAt"]), (c.get("author") or {}).get("login", ""),
         c.get("body", ""))
        for c in (pr_data.get("comments") or [])
        if can_lift(c)
        # #12908 : levée VIVE exigée — le PREFLIGHT de #12798 qui demandait
        # « une levée explicite » était compté comme levée par le sac de mots.
        and has_live_lift(c.get("body", ""))
        and not _lift_cancelled(_strip_quoted(c.get("body", "")))
        # #12836 / #12798 : une reserve qui narre une ancienne levee reste
        # une reserve, pas un evenement de levee du signal precedent.
        and classify((c.get("author") or {}).get("login", ""),
                     c.get("body", "")) is None
    ] + [
        # #13399 point 2 — symetrie de la levee : une PHRASE de levee portee
        # par le corps d'une review COMMENTED (et pas un commentaire) devait
        # aussi compter. Aujourd'hui la pose acceptait commentaire et review,
        # la levee un seul. Une review APPROVED est deja traitee par
        # approved_rereviews (etat natif) ; une review COMMENTED qui ecrit
        # « je leve ma CHANGES_REQUESTED » est une levee comme un commentaire.
        (ts(r.get("submittedAt")), (r.get("author") or {}).get("login", ""),
         r.get("body", ""))
        for r in (pr_data.get("reviews") or [])
        if r.get("state") == "COMMENTED"
        and can_lift(r)
        and has_live_lift(r.get("body", ""))
        and not _lift_cancelled(_strip_quoted(r.get("body", "")))
        and classify((r.get("author") or {}).get("login", ""),
                     r.get("body", "")) is None
    ]
    explicit_lifts = [x for x in explicit_lifts if x[0] is not None]
    # #13495 + #14218 — voie 3 de B.0 : les commentaires qui NOMMENT une
    # issue de suivi ouverte avant le cutoff sont des leveries a part
    # entiere. Avant : seul `created < cutoff` etait verifie (condition 2
    # sur 4 — issue FERMEe, issue ANTERIEURE a la reserve, ou issue qui
    # ne cite PAS la PR eteignait quand meme des reserves). Apres :
    # `collect_followup_lifts` filtre OUVERTE + deliberee ; les conditions
    # 5 (posterieure a la reserve) et 6 (reference la PR dans titre/corps)
    # sont appliquees par reserve dans les `any(...)` ci-dessous.
    followup_lifts = collect_followup_lifts(pr_data, cutoff, issue_info)

    # #13639 -- passer les levees au crible du SHA rembobine (voir
    # _SHA_CITED ci-dessus pour le pourquoi et l'etroitesse). Inerte sans
    # OIDs connus : le pre-filtre d'audit (sans `commits`) et les fixtures
    # sans `oid` sautent ce passage -- comportement inchange. Limite assumee
    # : ce pre-filtre d'audit ne verra donc jamais cette classe de defaut
    # (il rend son verdict sans commits) ; c'est le gate, en direct sur la
    # PR avant merge, qui est le client visé par #13639.
    commit_oids = [(c.get("oid") or "").lower()
                   for c in (pr_data.get("commits") or []) if c.get("oid")]
    voided_lifts: list[dict] = []
    absent_sha_warnings: list[dict] = []
    if commit_oids:
        pr_refs: set[str] = set()
        if pr_data.get("number") is not None:
            pr_refs.add(str(pr_data["number"]))
        for m in re.finditer(r"#(\d+)", (pr_data.get("title") or "")
                             + "\n" + (pr_data.get("body") or "")):
            pr_refs.add(m.group(1))
        pr_refs.discard("")
        resolved = pr_data.get("_absent_sha_messages") or {}
        kept_lifts = []
        for (t, lifter, lift_body) in explicit_lifts:
            refused = None
            warned = None
            for sha in sorted(_cited_shas(lift_body)):
                if any(oid.startswith(sha) for oid in commit_oids):
                    continue  # present dans la PR : preuve valide
                if not _sha_in_lift_claim(lift_body, sha):
                    continue  # citation de contexte : ni refus, ni signalement
                message = resolved.get(sha)
                if message and _message_refs_pr(message, pr_refs):
                    refused = sha  # rembobine ET rattache : la levee est nue
                    break
                warned = sha  # non resoluble ou sans rapport : avertir
            if refused:
                voided_lifts.append(
                    {"author": lifter, "at": t.isoformat(), "sha": refused})
            else:
                kept_lifts.append((t, lifter, lift_body))
                if warned:
                    absent_sha_warnings.append(
                        {"author": lifter, "at": t.isoformat(), "sha": warned})
        explicit_lifts = kept_lifts

    signals: list[tuple] = []
    for c in pr_data.get("comments") or []:
        login = (c.get("author") or {}).get("login", "")
        kind = classify(login, c.get("body", ""))
        if kind:
            signals.append((ts(c["createdAt"]), kind, login, c.get("body", ""), "comment"))
    for r in pr_data.get("reviews") or []:
        login = (r.get("author") or {}).get("login", "")
        body = r.get("body", "")
        state = r.get("state")
        if state == "DISMISSED":
            # #13685 — la premisse precedente (« une dismissal n'est possible
            # que par l'auteur de la review ou un admin ») est FAUSSE : tout
            # compte disposant du droit d'ecriture peut dismisser la review d'un
            # tiers, l'auteur de la PR compris. Le `continue` inconditionnel
            # faisait donc de `PUT /pulls/N/reviews/ID/dismissals` une trappe :
            # sur #13685, la CHANGES_REQUESTED de clusterManager-Myia (« 1 defect
            # bloquant trouve ») est dismissee a 18:14:56Z, et `check-navlinks`
            # passe FAILURE a 18:16:11Z — 75 secondes plus tard. La reserve etait
            # declaree levee pendant que la propriete qu'elle protege etait encore
            # cassee. C'est #12798 mecanise : se lever soi-meme la reserve d'un
            # tiers ne repond pas a la remarque, ca la declare repondue.
            #
            # Une dismissal n'eteint donc la reserve que si elle vient de son
            # EMETTEUR (retrait volontaire, #11222 levee (b)) ou d'un login
            # d'override nomme. Dismissee par quiconque d'autre, elle SURVIT.
            if login not in (dismissed_improperly or ()):
                continue
            # La reserve survivante reprend son etat D'ORIGINE : la timeline
            # rend `dismissed_review.state == "changes_requested"`. Sans cette
            # ligne le signal existe mais retombe en `review:DISMISSED` — hors
            # de la branche qui force BOT-CONCERN, et hors du durcissement
            # `src == "review:CHANGES_REQUESTED"` en aval. Mesure sur #13685 :
            # `improper_dismissals` rendait bien {clusterManager-Myia} et le
            # gate restait vert. Un signal hors de sa branche ne bloque rien.
            state = "CHANGES_REQUESTED"
        kind = classify(login, body)
        if state == "CHANGES_REQUESTED":
            kind = "BOT-CONCERN" if kind is None else kind
        # #14503 — reserve de persona enoncee en PROSE, invisible au scanner
        # de verdicts. Mesure fondatrice #14486 : review `[Hermes]` COMMENTED
        # posterieure au dernier commit, reserves en prose ordinaire (« 3
        # defauts constates en execution reelle ») SANS prefixe de verdict
        # ni glyphe -> CONCERN_MARKERS muet -> classify None -> rc=0. Une
        # persona sous contrainte de tokens abrege, et le verdict formel est
        # precisement ce qui saute : le mecanisme se degrade exactement dans
        # le sens ou il ne faut pas.
        #
        # Calibrage (controle 3 de l'issue, 200 dernieres PRs mergees) : le
        # fail-CLOSED pur (« persona + post-commit + pas de levee »)
        # attraperait 70 reviews quasi toutes APPROBATIVES (« Verdict :
        # solide ») = un mur. La reserve n'est donc declaree que si la prose
        # PORTE un motif de reserve (_PROSE_CONCERN_RE). Bornes :
        #   * marque persona POSEE dans le body (gras compris, citation
        #     backtick exclue) — un login sans marque reste l'identite de
        #     poussee partagee ;
        #   * motif de reserve en prose — vocabulaire serre MESURE : les 2
        #     cas fondateurs attrapes, 0 des 70 approbations du corpus ;
        #   * POSTERIEURE au dernier commit : une review d'avant le push est
        #     presumee adressee par celui-ci ;
        #   * PAS de levee vivante dans le corps : classify sort aussi None
        #     pour une annonce de LEVEE — c'est une resolution, pas une
        #     reserve, et la transformer en blocage serait l'exact inverse
        #     de ce que le gate doit faire.
        elif (state == "COMMENTED" and kind is None
              and _PERSONA_MARKERS_RE.search(_strip_quoted(body))
              and _PROSE_CONCERN_RE.search(_strip_quoted(body))
              and not has_live_lift(_strip_quoted(body))
              and last_commit is not None
              and ts(r.get("submittedAt")) > last_commit):
            kind = "BOT-CONCERN"
        # #11677 — symetrique APPROVED : l'etat natif GitHub `APPROVED` temoigne
        # qu'aucune reserve n'est posee. Si classify() a deja retourne un kind
        # (HUMAN ou BOT-CONCERN), c'est qu'une reserve VIVANTE survit dans la
        # prose (« j'approuve mais le point 2 reste ouvert ») — on respecte.
        # Sinon (None) : on CONFIRME l'extinction par l'etat, kind reste None
        # et la review APPROVED ne devient jamais un signal bloquant. Sans
        # cette branche, le verdict positif est calcule sur la prose seule,
        # alors que la preuve la plus dure (l'etat natif) est disponible
        # deux lignes plus haut. Meme symetrie que CHANGES_REQUESTED ci-dessus.
        elif state == "APPROVED":
            if kind is None:
                pass  # kind reste None (l'etat natif confirme l'extinction)
            # Le test porte sur le corps DEPOUILLE, jamais sur le brut : une
            # review qui *cite* une formule de reserve (tableau de sondes,
            # explication du garde, fixture entre backticks ou guillemets) la
            # MENTIONNE au lieu de l'EMETTRE. Mesure du 30/08 sur la review
            # Hermes de cette PR meme : 6 matches sur le corps brut, dont 5
            # sont ses propres fixtures -- le garde bloquait la PR sur les
            # chaines que la review citait pour demontrer qu'il fonctionne.
            # Troisieme occurrence de la confusion usage/mention apres #11246
            # (CONDITIONAL_LIFT) et #13261 (marqueur d'override G-VAR-3) : le
            # depouillement `_strip_quoted` existait deja et est applique
            # partout ailleurs (l.803, l.1040) -- cette branche etait la seule
            # a s'en passer.
            elif not _APPROVE_RESERVATION_RE.search(_strip_quoted(body)):
                # #13559 : marqueur residuel SANS langage de reserve — la
                # review NOMME une reserve (le plus souvent celle qu'elle
                # leve) au lieu d'en emettre une. L'etat natif decide.
                kind = None
        if kind:
            signals.append((ts(r.get("submittedAt")), kind, login, body,
                            f"review:{state}"))

    blocking = []
    for (when, kind, login, body, src) in signals:
        if when is None or when >= cutoff:
            continue
        # Un commentaire posté APRÈS le merge ne peut pas avoir levé le nit :
        # c'est l'annonce de merge, pas une réponse. Sans cette borne, le gate
        # rate son propre incident fondateur (#10761, où mon commentaire de
        # merge « éteignait » rétroactivement le nit user posté 17 h plus tôt).
        if src == "review:CHANGES_REQUESTED":
            # Fenetre 2026-08-16 (#11222) : un CHANGES_REQUESTED est un ETAT
            # GitHub natif, pas une remarque en prose — un commentaire
            # posterieur quelconque ne l'eteint pas. Sur #11215, la review de
            # 08:34:39 etait eteinte par le commentaire 08:36:23 de son
            # PROPRE auteur (« Ma remarque de review sur le fond est
            # inchangee ») : le gate rendait EXIT=0. Le principe du state
            # natif (deja applique a la LEVEE par la re-review APPROVED
            # ci-dessus) est honore dans l'autre sens : l'etat ne se retire
            # que par son AUTEUR (re-review APPROVED ; la dismissal est
            # eliminee des la collecte), ou par une PHRASE explicite de levee
            # (B.0 : ce qui leve une remarque est une phrase). Les nits portes
            # par un COMMENTAIRE gardent le regime general ci-dessous — limite
            # NLP documentee dans can_lift.
            lifted = (_approved_lifts_reserve(login, when, pr_author)
                      or any(when < t < cutoff
                             and _lift_eligible(lifter, login, lift_body)
                             for (t, lifter, lift_body) in explicit_lifts)
                      # #14218 conditions 5+6 — voir commentaire `followup_lifts`
                      or any(when < t < cutoff and namer in (login, pr_author)
                             and when < info.created_at
                             and _issue_references_pr(info, pr_number)
                             for (t, namer, info) in followup_lifts))
            if lifted:
                continue
        # #13083 — les bornes strictes du blocage. Un blocage ne se leve ni
        # par l'auteur de la PR, ni par une phrase de levee d'un compte qui est
        # a la fois auteur de la PR et emetteur du blocage : sous le self-review
        # cap (#12319) nit_author == pr_author == "jsboige" rendait la borne
        # d'auteur #11145 vacue — la PR se debloquait elle-meme en repondant
        # une phrase de levee. Seuls ouverts : l'arbitrage ECRIT `[OVERRIDE]
        # lane` d'un coordinateur (mecanique #11639) et la re-review APPROVED
        # de l'emetteur (etat natif), plus l'emetteur reel quand son compte est
        # DISTINCT de l'auteur de la PR.
        elif kind == "BLOCK":
            if (any(
                    when < t < cutoff
                    and _lift_eligible(lift_author, login, lift_body)
                    and (lift_author != pr_author
                         or bool(OVERRIDE_LANE.search(lift_body)))
                    for (t, lift_author, lift_body) in explicit_lifts)
                    or _approved_lifts_reserve(login, when, pr_author)
                    # #13495 — voie 3 : le report par issue nommee leve aussi
                    # un blocage. La garde d'auteur ci-dessus est celle des
                    # PHRASES de levee (#13083) ; la voie 3 porte sa propre
                    # garantie — l'issue existe et fut creee AVANT le cutoff —
                    # et reste ouverte a l'auteur : un report nomme avant
                    # merge est un geste delibere que B.0 credite. Borne
                    # nommeur (c.705) : {auteur du blocage, auteur de la PR}.
                    or any(when < t < cutoff and namer in (login, pr_author)
                           and when < info.created_at
                           and _issue_references_pr(info, pr_number)
                           for (t, namer, info) in followup_lifts)):
                continue
        # #12319 : meme regime pour un nit porte par un commentaire ou une
        # review COMMENTED (dont chaque reserve Hermes, self-review cap).
        # Avant : n'importe quel commentaire posterieur de la lane levait
        # (nit_author == pr_author == "jsboige" flotte-wide rendait la borne
        # #11145 vacue — un [READY-FOR-MERGE SELF attestation] qui ne nomme
        # pas la reserve l'eteignait). Apres : une PHRASE de levee
        # (LIFT_MARKER, borne d'auteur #11145 preservee via _lift_eligible)
        # OU une re-review APPROVED de l'auteur de la reserve (etat natif
        # GitHub, phrase de levee au sens fort).
        elif (any(
                  when < t < cutoff and _lift_eligible(lift_author, login, lift_body)
                  for (t, lift_author, lift_body) in explicit_lifts
              ) or _approved_lifts_reserve(login, when, pr_author)
              or any(when < t < cutoff and namer in (login, pr_author)
                     and when < info.created_at
                     and _issue_references_pr(info, pr_number)
                     for (t, namer, info) in followup_lifts)):
            continue
        # Un commit poussé après le nit ne le lève PAS à lui seul : sur #10761,
        # le « traitement » était un rebase à 19:41 qui n'adressait aucun des
        # deux nits de 11:07. Le push est reporté comme contexte, pas comme levée
        # — seule une réponse écrite (ou un thread résolu) lève une remarque.
        pushed_after = last_commit is not None and last_commit > when
        blocking.append({
            "kind": kind, "author": login, "src": src,
            "channel": "review" if src.startswith("review") else "comment",
            "at": when.isoformat(),
            "gap_hours": round((cutoff - when).total_seconds() / 3600.0, 1),
            "code_pushed_after": pushed_after,
            "excerpt": _excerpt(body),
        })

    for t in threads:
        if t["resolved"] or t["outdated"]:
            continue
        blocking.append({
            "kind": "INLINE-UNRESOLVED", "author": t["author"], "src": "reviewThread",
            "channel": "review",
            "at": t.get("createdAt") or "?",
            "where": f"{t.get('path')}:{t.get('line')}",
            "excerpt": _excerpt(t.get("body") or ""),
        })

    # #13316 — un override ECARTE pour cause d'auteur doit etre NOMME. Avant,
    # un gate rouge « malgre notre override » etait indistinguable d'un bug du
    # detecteur (#13030, #12096) : le commentaire existait, la borne l'avait
    # rejete, personne ne le disait. Ce n'est PAS bloquant (la reserve qui
    # survit reste le signal) — c'est l'explication visible du rouge. Un
    # override de l'auteur de la reserve (self-lift legitime) n'est pas liste.
    nit_authors = {login for (_, _, login, _, _) in signals}
    ignored_overrides = [
        {"author": author, "at": t.isoformat(),
         "why": (f"override ignoré — auteur « {author} » n'est pas un compte "
                 "de levée (#13316 : identité de poussée partagée des lanes)")}
        for (t, author, body) in explicit_lifts
        if t is not None
        and OVERRIDE_LANE.search(body or "") is not None
        and author not in LIFT_OVERRIDE_LOGINS
        and author not in nit_authors
    ] + [
        # #13495 — meme exigence de nomination pour la trappe fermee a
        # l'auteur de la PR : un override coordinateur pose PAR l'auteur ne
        # doit pas disparaitre en silence.
        {"author": author, "at": t.isoformat(),
         "why": (f"override ignoré — auteur « {author} » est l'auteur de la "
                 "PR : la trappe coordinateur ne s'ouvre pas pour lui "
                 "(#13495)")}
        for (t, author, body) in explicit_lifts
        if t is not None
        and OVERRIDE_LANE.search(body or "") is not None
        and author in LIFT_OVERRIDE_LOGINS
        and author == pr_author
    ] + [
        # #14216 — un override legitime qui ne NOMME pas affirmativement la
        # reserve qu'il laisse survivre doit etre explique : sans cette ligne,
        # un gate rouge « malgre notre override » redeviendrait
        # indistinguable d'un bug du detecteur. La levee n'etait pas refusee,
        # elle etait trop large — le rouge le dit maintenant.
        {"author": author, "at": t.isoformat(),
         "why": (f"override ignoré pour la réserve de « {login} » — il ne la "
                 "lève pas nommément (#14216 : une levée coordinatrice est "
                 "scopée par réserve ; la nommer dans une phrase de levée "
                 "affirmative — « je lève aussi la réserve de <login> » — une "
                 "mention d'exclusion ne compte pas)")}
        for (t, author, body) in explicit_lifts
        if t is not None
        and OVERRIDE_LANE.search(body or "") is not None
        and author in LIFT_OVERRIDE_LOGINS
        and author != pr_author
        for login in sorted({b.get("author") for b in blocking
                             if b.get("author") not in ("", author)
                             and not _override_scopes_reserve(
                                 body or "", b.get("author") or "")})
    ]

    # #13512 -- CE QUE L'ORGANE N'A PAS EVALUE.
    #
    # `classify` reconnait un commentaire humain a ses retours CRLF de l'UI
    # web (test sur la sequence CR-LF dans le corps). Un commentaire d'UNE
    # SEULE LIGNE n'en porte aucun : il tombe en `None` et devient invisible.
    # Mesure du 2026-08-29 sur quatre remarques user reelles : les trois
    # one-liners (#13476 tika/qwen, #13397 exercices pre-resolus, #13403
    # prose confuse) rendent `None` ; seule celle de deux lignes (#13472
    # graphviz) rend "HUMAN". #13476 a ete mergee 2 h 13 apres la remarque,
    # sous un `OK -- aucun nit non leve` qui ne l'avait jamais lue.
    #
    # Aucun detecteur ne repare ca : `jsboige` est a la fois le compte user,
    # l'identite de poussee des lanes et le login coordinateur, et l'API ne
    # les distingue par AUCUN champ (author_association, performed_via_github_app,
    # user.type : identiques, verifie firsthand). Un classifieur candidat
    # mesure le meme jour attrapait 3/3 des remarques user mais accusait 3/5
    # des commentaires de lane -- trop bruyant pour bloquer.
    #
    # D'ou le parti : ne pas classer, mais CESSER DE CERTIFIER LE SILENCE.
    # Ce que l'organe n'a pas evalue, il l'imprime. Lancer le gate devient
    # l'acte de relire la queue -- la regle user HARD (« on ne merge pas sans
    # avoir relu tous les commentaires au dernier moment ») cesse de dependre
    # de la vigilance et devient mecanique.
    lift_keys = {(t_, a) for (t_, a, _b) in explicit_lifts if t_}
    unevaluated: list[dict] = []
    for c in pr_data.get("comments") or []:
        login = (c.get("author") or {}).get("login", "")
        if login in BOT_LOGINS:
            continue
        body = (c.get("body") or "").strip()
        when = ts(c.get("createdAt"))
        if not body or when is None or when > cutoff:
            continue
        if classify(login, body) is not None:
            continue  # deja porte par `blocking`, ou explicitement neutralise
        if (when, login) in lift_keys:
            continue  # compte comme levee : deja lu par l'etage lift
        unevaluated.append({
            "author": login,
            "at": c.get("createdAt"),
            "after_last_commit": bool(last_commit and when > last_commit),
            "body": body,
        })
    # Ce qui suit le dernier commit est le plus a risque (rien ne peut
    # pretendre l'avoir traite) ; s'y ajoute la queue -- exactement les
    # `comments[-3:]` que la regle demande de relire avant `gh pr merge`.
    #
    # #13779 -- le repli etait EXCLUSIF (`after_lc or queue`) : des qu'UN
    # commentaire suivait le dernier commit, toute la queue anterieure
    # sortait de l'affichage, et l'en-tete imprimait le compte du
    # SOUS-ENSEMBLE en le presentant comme le total. Mesure sur #13712 :
    # 5 non evalues, 3 affiches -- et parmi les 2 masques, le
    # `[ADJOINT PREFLIGHT]` de 19:30:49Z dont le point non traite motivait
    # le HOLD du coordinateur sur cette PR meme. Masque parce qu'un commit
    # etait passe apres lui, alors que « un commit pousse apres la remarque
    # ne la leve PAS a lui seul » (B.0) : sur la seule PR ou l'echappatoire
    # a servi, elle a cache le commentaire qui justifiait le blocage.
    #
    # Les deux mecanismes COMPOSENT au lieu de s'exclure : tout le
    # post-dernier-commit, PLUS la queue des anterieurs -- que l'existence
    # du premier n'annule plus. Strict sur-ensemble de l'ancien affichage :
    # cette borne ne peut que montrer davantage, jamais moins, et ne touche
    # aucun verdict (`unevaluated` ne participe pas a `blocked`).
    after_lc = [u for u in unevaluated if u["after_last_commit"]]
    before_lc = [u for u in unevaluated if not u["after_last_commit"]]
    to_read = sorted(after_lc + before_lc[-3:], key=lambda u: u["at"] or "")

    return {
        "pr": pr_data.get("number"),
        "title": (pr_data.get("title") or "")[:110],
        "blocking": blocking,
        "blocked": bool(blocking),
        "ignored_overrides": ignored_overrides,
        "voided_lifts": voided_lifts,
        "absent_sha_warnings": absent_sha_warnings,
        "unevaluated": to_read,
        "unevaluated_total": len(unevaluated),
    }


FIELDS = "number,title,body,mergedAt,author,comments,reviews,commits,url,state"

# `commits` porte une connection `authors` par commit : sur un `gh pr list` large,
# GraphQL depasse son plafond de 500 000 noeuds. L'audit retro liste donc SANS
# `commits`, puis ne les recupere que pour les PRs reellement candidates.
# `author` est requis depuis #11145 : la borne d'auteur des levees a besoin de
# l'auteur de la PR, en audit comme en gate.
LIST_FIELDS = "number,title,mergedAt,url,comments,reviews,author"


def _print_unevaluated(result: dict) -> None:
    """Imprimer verbatim ce que l'organe n'a pas evalue (#13512).

    `OK -- aucun nit non leve` repond « aucune phrase de levee ne manque », et
    RIEN D'AUTRE : un commentaire que `classify` n'a pas su lire n'est pas un
    commentaire absent. Le dire est tout l'organe.
    """
    rows = result.get("unevaluated") or []
    if not rows:
        return
    # #13779 : le compte imprime est celui du TOTAL non evalue, pas celui des
    # lignes affichees -- un organe dont tout le propos est de ne pas certifier
    # son propre silence ne peut pas sous-declarer ce qu'il n'a pas lu.
    total = result.get("unevaluated_total") or len(rows)
    omitted = total - len(rows)
    after = sum(1 for r in rows if r["after_last_commit"])
    tail = f", dont {after} posterieur(s) au dernier commit" if after else ""
    cut = f" — {len(rows)} affiche(s), {omitted} plus ancien(s) omis" if omitted > 0 else ""
    print()
    print(f"  --- A RELIRE : {total} commentaire(s) NON EVALUE(S) par cet organe{tail}{cut} ---")
    print("  Le verdict ci-dessus ne porte QUE sur les phrases de levee. Ces")
    print("  commentaires n'ont pas ete classes : les lire avant `gh pr merge`.")
    for r in rows:
        mark = " [APRES LE DERNIER COMMIT]" if r["after_last_commit"] else ""
        print()
        print(f"  * {r['author']} — {r['at']}{mark}")
        lines = r["body"].split("\n")
        for line in lines[:8]:
            print(f"      {line[:160]}")
        if len(lines) > 8:
            print(f"      ... (+{len(lines) - 8} ligne(s))")
    print()


def _print_sha_notes(result: dict) -> None:
    """#13639 : nommer les levees dont la preuve citee manque de la PR."""
    for v in result.get("voided_lifts") or []:
        print(f"  [!] NON LEVE — levee de {v['author']} à {v['at']} : cite "
              f"{v['sha']}, absent des commits de la PR (résolu côté serveur, "
              f"mais rembobiné par un push ultérieur)")
    for w in result.get("absent_sha_warnings") or ():
        print(f"  [i] levee de {w['author']} à {w['at']} cite {w['sha']} "
              f"(absent des commits, non rattaché à cette PR) — non bloquant")


def gate(pr: int, as_json: bool) -> int:
    data = gh_json(["pr", "view", str(pr), "--repo", REPO, "--json", FIELDS])
    # #13639 : resolution serveur des SHAs cites-absents, AVANT analyse
    # (qui reste pure). Sans ceci, la classe #13557 serait invisible.
    data["_absent_sha_messages"] = _resolve_absent_sha_messages(data)
    merged = ts(data.get("mergedAt"))
    cutoff = merged or datetime.now(timezone.utc)
    result = analyse(data, review_threads(pr), cutoff,
                     issue_info=gh_issue_info,
                     dismissed_improperly=improper_dismissals(pr))
    if as_json:
        print(json.dumps(result, indent=1, ensure_ascii=False))
    elif not result["blocked"]:
        print(f"OK  PR #{pr} — aucun nit non leve.")
        _print_sha_notes(result)
        _print_unevaluated(result)
    else:
        print(f"BLOCKED  PR #{pr} — {len(result['blocking'])} nit(s) non leve(s) :\n")
        for b in result["blocking"]:
            where = b.get("where", "")
            gap = f" (+{b['gap_hours']}h avant merge)" if "gap_hours" in b else ""
            print(f"  [{b['kind']}] {b['author']} via {b['src']}{where}{gap}")
            print(f"      {b['excerpt']}\n")
        for o in result.get("ignored_overrides", ()):
            # #13316 : dire POURQUOI l'override visible n'a rien eteint — le
            # silence etait le mode d'echec couteux (#13030, #12096).
            print(f"  [i] {o['why']} (commentaire de {o['author']} à {o['at']})")
        _print_sha_notes(result)
        print("Lever chaque nit (reponse explicite, thread inline resolu, ou issue de suivi nommee)")
        print("avant `gh pr merge`. Cf CLAUDE.md section B.0.")
        _print_unevaluated(result)
    return 1 if result["blocked"] else 0


def audit(limit: int, search: str | None = None) -> int:
    cmd = ["pr", "list", "--repo", REPO, "--state", "merged",
           "--limit", str(limit), "--json", LIST_FIELDS]
    if search:
        # Partitionnement de l'historique entre lanes, ex :
        #   --search "merged:2026-07-01..2026-07-15"
        cmd += ["--search", search]
    prs = gh_json(cmd)
    findings = []
    for p in prs:
        merged = ts(p.get("mergedAt"))
        if not merged:
            continue
        # Pre-filtre sans `commits` : si rien ne ressort deja, inutile de payer
        # un appel de plus (les commits ne peuvent que LEVER un nit, jamais en creer).
        # #13495 : voie 3 active aussi en retro — sinon l'audit flaggerait des
        # PRs dont les nits etaient legitiment reportes par issue nommee. Le
        # cache global de gh_issue_created amortit les lookups croises entre PRs.
        if not analyse(p, [], merged,
                       issue_info=gh_issue_info)["blocked"]:
            continue
        try:
            p["commits"] = gh_json(
                ["pr", "view", str(p["number"]), "--repo", REPO, "--json", "commits"]
            )["commits"]
        except subprocess.CalledProcessError:
            p["commits"] = []
        # Ce 2e passage rend le MEME verdict `blocked` que le pre-filtre — un
        # commit ne leve rien (c'est le principe de B.0). Il n'est pas pour le
        # verdict : il renseigne `code_pushed_after`, dont la Phase 2 de #11044
        # a besoin pour trier (« du code a bouge apres le nit » = aller lire le
        # diff avant de conclure). Information de triage, pas critere.
        # Audit retro : on n'interroge pas les threads inline (1 appel GraphQL/PR).
        res = analyse(p, [], merged, issue_info=gh_issue_info)
        if res["blocked"]:
            res["url"] = p.get("url")
            res["merged_at"] = p["mergedAt"]
            findings.append(res)
    findings.sort(key=lambda f: f["pr"], reverse=True)
    print(json.dumps({
        "scanned": len(prs),
        "search": search,
        "oldest_merged": min((p["mergedAt"] for p in prs if p.get("mergedAt")), default=None),
        "newest_merged": max((p["mergedAt"] for p in prs if p.get("mergedAt")), default=None),
        "flagged": len(findings),
        "findings": findings,
    }, indent=1, ensure_ascii=False))
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("pr", nargs="?", type=int, help="numero de PR (mode gate)")
    ap.add_argument("--audit", action="store_true", help="audit retro des PRs mergees")
    ap.add_argument("--limit", type=int, default=200, help="taille de l'audit retro")
    ap.add_argument("--search", help="filtre gh (ex: 'merged:2026-07-01..2026-07-15')")
    ap.add_argument("--json", action="store_true", help="sortie machine (mode gate)")
    args = ap.parse_args()
    if args.audit:
        return audit(args.limit, args.search)
    if args.pr is None:
        ap.error("fournir un numero de PR, ou --audit")
    return gate(args.pr, args.json)


if __name__ == "__main__":
    sys.exit(main())
