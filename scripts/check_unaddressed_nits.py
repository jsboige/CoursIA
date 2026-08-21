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
  - **de la bonne personne** (borne d'auteur #11145) : l'auteur de la reserve,
    ou l'auteur de la PR qui repond a son reviewer. Une reponse ou une
    approbation d'un tiers (ni l'un ni l'autre) n'eteint pas la reserve —
    c'est la classe #10761 que l'organe existe pour bloquer (mesure #11494 :
    24,3 % des levees etaient BYSTANDER). L'echappement B.0 (issue de suivi
    nommee) reste le chemin quand la reserve exige l'arbitrage d'un tiers —
    et depuis #11639, l'arbitrage ECRIT du coordinateur porte une trappe
    nommee : `[OVERRIDE] lane <machine:workspace>` + phrase de levee (meme
    convention ecrite que les claims #10223). Pas une ouverture generale :
    la borne tient pour tout autre tiers, et un override POST-marge ne peut
    pas avoir eteint une reserve avant la decision de merge.

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
COORDINATOR_LOGINS = {"myia-ai-01", "jsboige"}
OVERRIDE_LANE = re.compile(r"\[OVERRIDE\]\s+lane\s+\S+")

# Marqueurs de reserve d'un reviewer bot (le verdict est dans le body, pas l'etat).
CONCERN_MARKERS = (
    "COMMENT_WITH_CONCERNS", "CHANGES_REQUESTED", "NEEDS_CHANGES", "CONCERNS",
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
    # Glyphes de severite d'Hermes (#12143). Le mot par lequel il NOMME ses
    # constats est « FINDING » — et c'est precisement le mot qu'il ne faut PAS
    # ajouter ici : mesure sur les 150 dernieres PR mergees, 13 reviews sur 35
    # contiennent « finding », dont 9 sans aucune reserve reelle (« 1 finding
    # max par cell » = nom d'une sortie de scanner ; « les 4 findings restants
    # ... cadrage honnete » ; « 2 FINDINGS non-bloquants »). C'est le
    # vocabulaire courant du domaine, pas un marqueur.
    #
    # Le discriminant est le GLYPHE, que la convention Hermes porte de facon
    # stable : sur ces 35 reviews, 23 portent △ (micro-nit explicitement non
    # bloquant, exclu ici), 5 portent 🟡 et 1 porte 🔴. Les 5 🟡 relevent tous
    # d'une seule classe — la claim du body dementie par l'artefact, soit le
    # point 1 des 5 de la revue (« la PR fait ce qu'elle annonce »).
    #
    # Consequence d'ordre, et c'est la vraie reparation : `live_concern`
    # redevient vrai, donc la branche HUMAN_VERDICT_POSITIVE ne peut plus
    # eteindre la review. Le « LGTM structural sur les 3 fixes + 1 FINDING »
    # de #12077 etait scope dans sa propre phrase ; l'organe lisait le LGTM et
    # pas le « + 1 FINDING », et rendait exit 0 sur une reserve vivante. Le
    # garde tient par l'ORDRE des branches (cf. HUMAN_VERDICT_POSITIVE
    # ci-dessous) — ce qui avait cede, c'est la premiere.
    #
    # Cout mesure de la promotion : 6 reviews flaggees sur 35 au lieu de 2 ;
    # sur les 150 PR du scan, une seule (#12059) aurait ete bloquee sans levee
    # ecrite, les 4 autres ayant deja une suite (commits ou commentaires) qui
    # l'aurait levee.
)

# Les deux glyphes seuls, nommes : la branche LIFT_MARKERS de `classify` en a
# besoin, et une reserve EMISE par glyphe ne se laisse pas eteindre par un mot
# de levee situe ailleurs dans le meme body.
SEVERITY_GLYPHS = (
    "\U0001F7E1",  # 🟡 constat substantiel
    "\U0001F534",  # 🔴 bloquant
)
CONCERN_MARKERS = CONCERN_MARKERS + SEVERITY_GLYPHS

# Un commentaire qui ANNONCE la levee ou le merge n'est pas un nit — il en est
# la resolution. Sans ce filtre, chaque « CHANGES_REQUESTED levée » est compte
# comme une reserve ouverte (faux positif massif, mesure sur 400 PRs).
LIFT_MARKERS = (
    "levée", "levee", "LGTM", "Mergé", "Merged", "je merge", "Merge.",
    "est adressé", "sont adressés", "sont levées", "est levée",
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
    r"|je merge (?:dès|des|une fois|quand|après|apres|si\b))", re.I)

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
_QUOTED_RANGES = re.compile(r"```.*?```|«.*?»|`[^`]*`", re.DOTALL)


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
    r"[^()\n]{0,40}\(\s*([A-Z][A-Z_]{3,})\s*\)")

# #11744 — Position A : titre de section `## ...VERDICT...`. La section est en
# mention par construction (un titre ne « declare » jamais un verdict, il
# l'evoque). Limite : 80 chars du `##` au verdict pour eviter les titres tres
# longs qui seraient des resumes sections sans mention explicite. Compteur
# cumulatif : l'eventuelle emission en corps de section est geree separement
# par les CONCERN_MARKERS et `_is_cited` (les emissions reelles passent par
# `MARKER:` nu ou par le state de la review, pas par un nom de verdict
# eparpille dans une prose narrative).
# Critere : nom de verdict = (a) TOUT en majuscules (>=4 chars) OU (b) contient
# un underscore. Un titre ne contient presque jamais un mot de 4+ majuscules
# consecutives SAUF un nom de verdict — c'est exactement la signature qu'on
# cherche. Le pattern `[A-Z][A-Z_]{3,}` (v1) etait trop court (matche aussi
# « Remedes » partiellement). **PAS de `(?i)` ici** : on veut strictement
# `[A-Z]` (majuscule), pas `[a-zA-Z]` (case-insensitive).
_MENTION_VERDICT_HEADING = re.compile(
    r"(?m)^#{1,6}[^\n]{0,80}?([A-Z]{4,})(?![A-Za-z0-9_])")

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
    r"\w*\s+\((?:commit\s+[a-f0-9]+|#\d+|PR\s*#?\d+|pull/\d+)\)")


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
_MENTION_VERDICT_REVIEW = re.compile(
    r"(?i)(?:^|[\s,;:(*])"  # frontiere (inclut * pour **revue**)
    r"(?:le|la|les|du|mon|ma|ce|cet|cette|ces|the|my)?\s*"
    r"(?:revue|review)(?![:.])"
    r"[^():\n.]{0,60}?(?-i:([A-Z][A-Z_]{3,}))(?![A-Za-z0-9_])"
    r"[^():\n.]{0,12}?"
    r"\([^()\n]{0,80}?"
    r"(?:[a-f0-9]{7,}|#\d+|\d{4}-\d{2}-\d{2}|\d{1,2}:\d{2}(?::\d{2})?Z?)"
    r"[^()\n]{0,40}\)")


def _strip_mentioned_verdicts(body: str) -> str:
    """Neutralise les noms de verdict cites en position de mention (#11636, #11744, #11809).

    Remplace le verdict par des espaces de meme longueur : les offsets du
    reste du body sont preserves (les fenetres de `_is_cited` restent
    calibrees sur la vraie position des occurrences survivantes).
    """
    for pat in (_MENTION_VERDICT, _MENTION_VERDICT_HEADING, _MENTION_VERDICT_INLINE, _MENTION_VERDICT_LIFTED, _MENTION_VERDICT_REVIEW):
        body = pat.sub(
            lambda m: m.group(0).replace(m.group(1), " " * len(m.group(1))), body)
    return body

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
            if head == c or (head.endswith(c) and not head[-len(c) - 1].isalnum()):
                return True
    return False


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
    normalised = _unaccent(body)
    for marker in markers:
        m = _unaccent(marker)
        start = 0
        while (i := normalised.find(m, start)) != -1:
            if not _is_cited(normalised[max(0, i - 30):i]):
                return True
            start = i + 1
    return False


def ts(value: str | None) -> datetime | None:
    if not value:
        return None
    return datetime.fromisoformat(value.replace("Z", "+00:00"))


def gh_json(args: list[str]) -> object:
    out = subprocess.run(
        ["gh", *args], capture_output=True, text=True, encoding="utf-8", check=True
    ).stdout
    return json.loads(out)


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
    if body.startswith(AGENT_PREFIXES) and not has_marker(body, LIFT_MARKERS):
        return False
    return True


def classify(author: str, body: str) -> str | None:
    """'HUMAN' (nit user, UI web) | 'BOT-CONCERN' (reviewer avec reserves) | None."""
    if author in BOT_LOGINS or not body:
        return None
    stripped = body.lstrip()
    # #12143 -- correction de mon propre diagnostic. J'avais impute le exit 0
    # de #12077 a la branche HUMAN_VERDICT_POSITIVE plus bas ; elle est bien
    # subordonnee a `live_concern`, comme son commentaire l'affirme, et n'etait
    # donc PAS en cause. Le coupable est CETTE branche-ci : `LIFT_MARKERS`
    # contient « LGTM », elle s'execute AVANT que `live_concern` ne soit
    # calcule, et elle n'est subordonnee a rien. Le « LGTM structural sur les
    # 3 fixes + 1 FINDING » rendait None ici meme, sans que le glyphe de
    # severite qui suivait ait jamais ete lu.
    #
    # Le correctif reste etroit : un glyphe de severite VIVANT annule la levee.
    # C'est le sens de la convention -- le glyphe est une EMISSION, et une
    # emission ne se laisse pas eteindre par un mot de levee pose ailleurs dans
    # la meme prose (« LGTM structural » scopait une partie du diff, pas le
    # constat). Aucun body sans glyphe ne change de classement.
    if (has_marker(body, LIFT_MARKERS)
            and not _lift_cancelled(_strip_quoted(body))
            and not has_live_marker(_strip_quoted(body), SEVERITY_GLYPHS)):
        return None  # annonce de levee / de merge : resolution, pas reserve
    # (construction conditionnelle « et je merge » : voir _lift_cancelled —
    # l'annonce conditionnee n'est pas une levee, SAUF levee explicite d'auteur
    # en amont (#12074) ; le commentaire continue sinon)
    if has_live_marker(body, (VERDICT_POSITIVE,)):
        return None  # verdict structurel positif rendu : il decide, la prose ne compte plus
    # #11636 : la recherche porte le body nettoye de ses verdicts MENTIONNES —
    # un rapport de correction qui nomme le verdict qu'il corrige n'emet pas
    # de reserve. Uniquement pour CONCERN_MARKERS : LIFT_MARKERS et
    # VERDICT_POSITIVE gardent le body brut (surface minimale du fix — le
    # controle positif deux formes vit dans les tests, cote a cote).
    live_concern = has_live_marker(_strip_mentioned_verdicts(_strip_quoted(body)), CONCERN_MARKERS)
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


def analyse(pr_data: dict, threads: list[dict], cutoff: datetime) -> dict:
    """cutoff = mergedAt (audit retro) ou now (gate pre-merge)."""
    commits = [ts(c.get("committedDate")) for c in (pr_data.get("commits") or [])]
    commits = [c for c in commits if c]
    last_commit = max(commits) if commits else None

    # #11145 — borne d'auteur : seules les levees de l'auteur de la reserve OU
    # de l'auteur de la PR comptent. Mesure #11494 (850 PRs) : SELF 22/37
    # (59,5 %) + PR_AUTHOR 6/37 (16,2 %) = flux sain preserve ; BYSTANDER 9/37
    # (24,3 %) = la classe #10761 que l'organe bloque (un tiers — approbation
    # ou reponse — n'eteint pas une reserve posee par un autre).
    pr_author = (pr_data.get("author") or {}).get("login", "")

    # Seuls les commentaires capables de LEVER comptent (cf can_lift) : un
    # commentaire de bot CI ou un tag de protocole nu n'a jamais repondu a rien.
    # On porte l'AUTEUR de chaque evenement de levee : la borne #11145 en a
    # besoin (auteur seul = les temps plats de #11222 ne suffisaient pas).
    # Le body est porte pour la trappe OVERRIDE de `_lift_eligible` (#11639) :
    # elle doit voir le marqueur `[OVERRIDE] lane …` de la levee, pas
    # seulement son auteur.
    lift_events = [
        (ts(c["createdAt"]), (c.get("author") or {}).get("login", ""),
         c.get("body", "") or "")
        for c in (pr_data.get("comments") or []) if can_lift(c)
    ]

    # Fenetre 05-29..06-04 (#1958) : la RE-REVIEW APPROVED. Le reviewer qui
    # revient approuver apres sa demande de changements A dit que la reserve
    # est levee — le state GitHub natif porte plus de sens que le body (une
    # re-review Hermes narre l'ancien verdict en le citant, sans mot de
    # levee). Seul APPROVED compte : une re-review COMMENTED qui re-emet une
    # reserve (« NOT FIXED », #2298) ne doit rien eteindre, et l'agent
    # d'exclusion can_lift ne s'applique pas — un state APPROVED n'est pas du
    # bruit de protocole, meme depuis un reviewer bot.
    approved_rereviews = [
        (ts(r.get("submittedAt")), (r.get("author") or {}).get("login", ""), "")
        for r in (pr_data.get("reviews") or [])
        if r.get("state") == "APPROVED"
        and (r.get("author") or {}).get("login", "") not in BOT_LOGINS
    ]
    approved_rereviews = [x for x in approved_rereviews if x[0] is not None]
    lift_events += approved_rereviews
    lift_events = [x for x in lift_events if x[0] is not None]

    def _lift_eligible(lift_author: str, nit_author: str,
                       lift_body: str = "") -> bool:
        if lift_author in (nit_author, pr_author):
            return True
        # #11639 : l'override NOMME du coordinateur — l'arbitre tiers de B.0.
        # La restriction d'auteur reste la regle pour tout le monde (elle
        # bloque l'auto-levee d'un bystander, #11145) ; seule la trappe ecrite
        # s'ajoute. Un OVERRIDE sans phrase de levee n'entre meme pas ici :
        # can_lift l'a ecarte (tag de protocole nu), et explicit_lifts exige
        # un LIFT_MARKER.
        return (lift_author in COORDINATOR_LOGINS
                and bool(OVERRIDE_LANE.search(lift_body or "")))

    # Fenetre 2026-08-16 (#11222) : les temps plats ne suffisent pas pour un
    # CHANGES_REQUESTED. Une PHRASE explicite de levee (LIFT_MARKER non
    # conditionnel) dans un commentaire qui peut lever reste une levee pour
    # l'etat de review — c'est la reponse ecrite que B.0 exige. On garde
    # l'auteur pour la branche dedicated ci-dessous.
    explicit_lifts = [
        (ts(c["createdAt"]), (c.get("author") or {}).get("login", ""),
         c.get("body", ""))
        for c in (pr_data.get("comments") or [])
        if can_lift(c)
        and has_marker(c.get("body", ""), LIFT_MARKERS)
        and not _lift_cancelled(_strip_quoted(c.get("body", "")))
    ]
    explicit_lifts = [x for x in explicit_lifts if x[0] is not None]

    signals: list[tuple] = []
    for c in pr_data.get("comments") or []:
        login = (c.get("author") or {}).get("login", "")
        kind = classify(login, c.get("body", ""))
        if kind:
            signals.append((ts(c["createdAt"]), kind, login, c.get("body", ""), "comment"))
    for r in pr_data.get("reviews") or []:
        login = (r.get("author") or {}).get("login", "")
        body = r.get("body", "")
        if r.get("state") == "DISMISSED":
            # Une dismissal GitHub n'est possible que par l'auteur de la review
            # (ou un admin) : la reserve est formellement RETIREE par son
            # emetteur — pas un signal (#11222, levée (b)).
            continue
        kind = classify(login, body)
        if r.get("state") == "CHANGES_REQUESTED":
            kind = "BOT-CONCERN" if kind is None else kind
        # #11677 — symetrique APPROVED : l'etat natif GitHub `APPROVED` temoigne
        # qu'aucune reserve n'est posee. Si classify() a deja retourne un kind
        # (HUMAN ou BOT-CONCERN), c'est qu'une reserve VIVANTE survit dans la
        # prose (« j'approuve mais le point 2 reste ouvert ») — on respecte.
        # Sinon (None) : on CONFIRME l'extinction par l'etat, kind reste None
        # et la review APPROVED ne devient jamais un signal bloquant. Sans
        # cette branche, le verdict positif est calcule sur la prose seule,
        # alors que la preuve la plus dure (l'etat natif) est disponible
        # deux lignes plus haut. Meme symetrie que CHANGES_REQUESTED ci-dessus.
        elif r.get("state") == "APPROVED" and kind is None:
            pass  # kind reste None (l'etat natif confirme l'extinction)
        if kind:
            signals.append((ts(r.get("submittedAt")), kind, login, body,
                            f"review:{r.get('state')}"))

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
            lifted = any(
                when < t < cutoff and author == login
                for (t, author, _) in approved_rereviews
            ) or any(
                when < t < cutoff and _lift_eligible(lifter, login, lift_body)
                for (t, lifter, lift_body) in explicit_lifts
            )
            if lifted:
                continue
        elif any(
            when < t < cutoff and _lift_eligible(lift_author, login, lift_body)
            for (t, lift_author, lift_body) in lift_events
        ):
            continue  # reponse de l'auteur du nit ou de l'auteur de la PR
        # Un commit poussé après le nit ne le lève PAS à lui seul : sur #10761,
        # le « traitement » était un rebase à 19:41 qui n'adressait aucun des
        # deux nits de 11:07. Le push est reporté comme contexte, pas comme levée
        # — seule une réponse écrite (ou un thread résolu) lève une remarque.
        pushed_after = last_commit is not None and last_commit > when
        blocking.append({
            "kind": kind, "author": login, "src": src,
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
            "at": t.get("createdAt") or "?",
            "where": f"{t.get('path')}:{t.get('line')}",
            "excerpt": _excerpt(t.get("body") or ""),
        })

    return {
        "pr": pr_data.get("number"),
        "title": (pr_data.get("title") or "")[:110],
        "blocking": blocking,
        "blocked": bool(blocking),
    }


FIELDS = "number,title,mergedAt,author,comments,reviews,commits,url,state"

# `commits` porte une connection `authors` par commit : sur un `gh pr list` large,
# GraphQL depasse son plafond de 500 000 noeuds. L'audit retro liste donc SANS
# `commits`, puis ne les recupere que pour les PRs reellement candidates.
# `author` est requis depuis #11145 : la borne d'auteur des levees a besoin de
# l'auteur de la PR, en audit comme en gate.
LIST_FIELDS = "number,title,mergedAt,url,comments,reviews,author"


def gate(pr: int, as_json: bool) -> int:
    data = gh_json(["pr", "view", str(pr), "--repo", REPO, "--json", FIELDS])
    merged = ts(data.get("mergedAt"))
    cutoff = merged or datetime.now(timezone.utc)
    result = analyse(data, review_threads(pr), cutoff)
    if as_json:
        print(json.dumps(result, indent=1, ensure_ascii=False))
    elif not result["blocked"]:
        print(f"OK  PR #{pr} — aucun nit non leve.")
    else:
        print(f"BLOCKED  PR #{pr} — {len(result['blocking'])} nit(s) non leve(s) :\n")
        for b in result["blocking"]:
            where = b.get("where", "")
            gap = f" (+{b['gap_hours']}h avant merge)" if "gap_hours" in b else ""
            print(f"  [{b['kind']}] {b['author']} via {b['src']}{where}{gap}")
            print(f"      {b['excerpt']}\n")
        print("Lever chaque nit (commit, reponse explicite, ou issue de suivi nommee)")
        print("avant `gh pr merge`. Cf CLAUDE.md section B.0.")
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
        if not analyse(p, [], merged)["blocked"]:
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
        res = analyse(p, [], merged)
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
