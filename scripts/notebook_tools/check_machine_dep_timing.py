#!/usr/bin/env python3
"""Detecteur dedie : temps d'horloge machine-dependants en prose de notebook.

Issu de l'inventaire manquant de l'EPIC #9434 (le quantitatif doit etre tenu
par le CI, pas par la prose manuelle) et de l'organe demande par #10158.

Contrairement a ``check_prose_quantitative_claims.py --class machine`` qui
couvre aussi env/stochastic/artifact/structural et applique une regex unique,
ce detecteur :

  - se limite aux notebooks ``MyIA.AI.Notebooks/**/*.ipynb`` cellules
    **markdown** (sortie structuree TSV/JSON, pas de bruit hors-scope) ;
  - importe ``MACHINE_RE`` du detecteur canonique (single source of truth)
    pour eviter toute divergence de motif ;
  - porte une **semantique de contexte** : un « 15.85 min » dans une cellule
    d'inference bayesienne est un parametre de distribution, pas un temps
    d'horloge -- l'organe distingue wall-clock vs distribution-param par
    trois tests de contexte (``CONTEXT_KEYWORDS``, ``DISTRIBUTION_KEYWORDS``,
    exemption ligne-complete pacing) ;
  - sort un **JSON structure** avec categorisation (wallclock vs ambiguous
    vs distribution_param) pour permettre l'inventaire qui manque a #9434 ;
  - tourne en mode **advisory** (exit 0 meme avec findings), le label/compte
    est le signal.

Usage
-----

    # Inventaire --all (utilise pour poster le compteur sur #9434)
    python check_machine_dep_timing.py --all

    # Inventaire structure (machine-readable)
    python check_machine_dep_timing.py --all --json

    # Filtre par chemin (debug)
    python check_machine_dep_timing.py MyIA.AI.Notebooks/GenAI/Audio

    # CI --check : exit 1 si findings wallclock stricts (futur, post-drain)
    python check_machine_dep_timing.py --check

Acceptance (cf. #10158)
- [x] Script sous ``scripts/notebook_tools/`` (pas a la racine)
- [x] Sortie exploitable (JSON structure par notebook)
- [x] Mode advisory : exit 0 par defaut, --check pour CI bloquant
- [x] Tests qui prouvent le silence sur les 5 familles FP documentees
- [x] Inventaire mesure pour #9434 (commande --all + --json)

Acceptance (cf. CHANGES_REQUESTED #10162, c.1331+59)
- [x] STUDENT_PACING_RE etendu aux deux formes reelles : parenhese "(15 min)"
      et cellule de tableau "| 15 min |".
- [x] Fourchettes et bornes traitees comme soft signals (au meme titre que `~`) :
      `N-M min`, `< N sec`, `<= N sec`, `N+ min` ne sont PAS signalees.
- [x] FP-2 : categorie `domain_quantity` propagee par cellule -- si le notebook
      porte `distribution_param` sur >=1 finding, les findings `wallclock` de
      la meme cellule basculent en `domain_quantity`.
- [x] Tests de silence par classe ci-dessus avec extraits reels.
- [x] Controle positif `Sudoku-13` preserve.
- [x] Inventaire re-mesure : 256 wallclock + 40 distribution_param +
      35 domain_quantity + 0 ambiguous = 331 total (vs 978 avant).

Acceptance (cf. #10169, frontiere residuelle)
- [x] Residu 1 : propagation per-NOTEBOOK ``domain_quantity`` -- si le notebook
      porte >=1 ``distribution_param``, l'unite de temps est son sujet et tous
      les ``wallclock`` residuels basculent (6 findings Infer-2-Gaussian-Mixtures
      dont les moyennes ajustees 15.07 / 26.69 min).
- [x] Residu 2 : ``PROTOCOL_KEYWORDS`` (settle_delay, temps de bloc, finality)
      route les constantes de consensus en ``domain_quantity`` ; tilde detache
      ``~ 2 min`` reconnu comme ordre de grandeur (SC-19, SC-23).
- [x] Residu 3 : ``--all`` resolu depuis la racine git (``git rev-parse
      --show-toplevel``), resultat vide = erreur explicite (exit 1).
- [x] Controle positif `Sudoku-13` preserve (Z3 wall-clock strict reste detecte).

Acceptance (tranche GenAI/Audio #9434, 2026-08-19 -- 04-6/04-11/04-12)
- [x] « de l'ordre de N s » / « de l'ordre de grandeur de N s » reconnus
      comme marqueurs d'ordre de grandeur DETACHES (forme en toutes lettres
      du tilde ; 04-11 c10 : « chaque segment prend de l'ordre de 3 s a
      generer »). Le mandat #9434 sanctionne l'ordre de grandeur -- le
      scanner n'exemptait que la forme tildée.
- [x] Borne inferieure stricte « > N unit » exemptee comme borne superieure
      (symetrique oublie de #10162 ; 04-12 c22 « narration longs (> 10
      secondes) » = seuil d'exercice) -- SAUF le « > » de blockquote en
      debut de ligne (research_m12_har_rv_j_minute c0 « > 25 s... » =
      duree mesuree d'un run, reste wallclock).
- [x] ``PARAM_DURATION_RE`` : parametres de DESIGN d'un pipeline audio
      (silence/fade/crossfade/pause/break SSML/extrait/seuil/rate-limit +
      duree a proximite, fenetre 40 chars sans '.' ni '|') classes
      ``domain_quantity`` -- constante du code, pas une mesure machine.
      ~30 findings wallclock sur les 3 notebooks de la tranche etaient
      exactement cette classe.
- [x] « durée finale » rejoint « durée cible/totale/maximale/optimale » dans
      CONTENT_DURATION_CONSTRAINT_RE (04-12 c12 : duree ffprobe du fichier
      MP3 commite = contenu, pas execution).
- [x] Arithmetique deterministe etendue a la multiplication « N x Mms = K s »
      (04-12 c12/c14/c17 : « 13 x 500ms = 6.5s » = silences d'assemblage).
- [x] Controles positifs preserves : Sudoku-13 (Z3 wall-clock strict),
      Sudoku-18 post-#11512 (0 wallclock attendu, toujours 0), 04-7
      post-#10707 (0 wallclock attendu, toujours 0).

Acceptance (tranche SymbolicAI #9434, 2026-08-19 -- 19 wallclock -> 1)
- [x] ``TIMEOUT_LIMIT_RE`` : timeout/limite de temps POSE sur le pipeline
      (solveur, build, service) = constante de config, classe
      ``domain_quantity``. 5 findings SymbolicAI (Planners-7 c16, Lean-13
      c25, FD-Legacy c3/c14, RDF.Net c69) + 12 findings TN verifies
      firsthand sur d'autres familles (la classe reparait une lacune
      repo-wide : tout timeout de config etait flagge wallclock).
- [x] ``STUDENT_PACING_RE`` etendu au pacing IMPERATIF (« prenez 5 minutes
      pour lire », « (essayez 5 min) ») et a la borne ADVISORY cold-start
      (« peut prendre 30 minutes a plusieurs heures », « Si ca prend plus
      de 15 minutes, interrompez ») -- attente adressee a l'etudiant, pas
      mesure. Le passe mesure « a pris plus de » ne matche pas.
- [x] ``PROTOCOL_KEYWORDS`` etendu aux cadences d'INFRASTRUCTURE
      (cadence/cron/periodicite) -- Lean-20 c7 « 30 min cadence » = periode
      du cron du cluster, constante de config.
- [x] Trois exemptions positionnelles : numero de section DECIMAL dans un
      header (« ### 2.3 MIN (FIN) » = section sur l'axiome MIN de
      Conway-Kochen, Lean-16f c9), conversion d'UNITE parenthetique d'une
      constante primaire (« 500s (8.3 min) », FD-Legacy c9 -- la forme
      entiere etait deja couverte par la parenthese pacing #10162),
      traduction litterale d'un ``sleep()`` du code (« sleep(0.1) ... 100ms
      », Argument_Analysis_UI c22 -- la valeur EST le code).
- [x] Drainage prose reel (le seul) : Z3-Linq2Z3/09 c16 -- 5 epingles
      numeriques dupliquant les sorties committes de la cellule de mesure
      c17 (0,29 s / 8,7 s / 600 s / 0,01-0,03 s / 0,05 s) remplacees par
      des descripteurs + renvoi aux sorties live ; le 600 s devient « la
      borne du protocole de bench » (constante, cf. sortie).
- [x] Controle de non-regression repo-wide : diff base->new sur 1033
      notebooks = 25 findings neutralises (13 cibles + 12 timeouts TN
      verifies ligne par ligne), 0 finding apparu. Sudoku-13-Python etait
      deja a 0 sur la base (draine par une PR anterieure) -- le controle
      positif vit dans les tests unitaires (Z3 25,2 s), tous verts.
- [x] Lean-22 c7 (30 minutes) RESTE wallclock : hors perimetre de cette
      tranche (rework actif po-2024, claim paths Sudoku-18).

Note : `ambiguous=0` est structural (defaut conservateur = wallclock). Aucun
finding ne reste ambigue apres la passe 1 -- le defaut de `_categorize`
classe toute ligne sans mot-cle en wallclock. La categorie `ambiguous`
reste dans la taxonomie pour compatibilite (cf. migrations futures) mais
n'est pas emise en pratique avec l'heuristique courante. Decision #10169 :
on garde la categorie documentee plutot que de la retirer, pour stabilite
du schema ``--json`` consomme par l'inventaire #9434.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

# --------------------------------------------------------------------------- #
#  Single source of truth : la regex canonique vit dans le detecteur generique.
#  On l'importe pour eviter toute divergence de motif (cf. incident ICT-21
#  #9434 angle-mort t2 ou la meme regex avait ete reimplemented et avait
#  diverge de 2 fixes #5101 et 22 verbes reflechis).
# --------------------------------------------------------------------------- #
sys.path.insert(0, str(Path(__file__).resolve().parent))
try:
    from check_prose_quantitative_claims import MACHINE_RE  # noqa: E402
except ImportError:
    # Fallback de survie : replicate inlined pour ne pas casser l'organe si
    # le module parent est absent (rare ; hooks pre-commit par exemple).
    MACHINE_RE = re.compile(
        r"(?<![\w.#])~?\d{1,6}(?:[.,]\d{1,3})?"
        r"(?:"
        r"\s?(?:ms|millisecondes?|sec(?:ondes?)?|min(?:utes?)?)"
        r"|\ss"
        r")"
        r"(?![\w\-’‘'])",  # apostrophes typographiques + ASCII
        re.IGNORECASE,
    )


# --------------------------------------------------------------------------- #
#  Heuristiques de contexte -- distinguent wall-clock d'un parametre de domaine
# --------------------------------------------------------------------------- #
# Mot-cle qui signale un contexte d'execution wall-clock dans la MEME LIGNE
# (ex : "duree d'execution : 2.4 s", "wall-clock time ~50 ms"). Si absent, on
# ne peut pas affirmer que le chiffre est wall-clock -- il reste "ambiguous".
WALLCLOCK_KEYWORDS = re.compile(
    r"\b(?:wall[\s\-]?clock|temps\s+d['’]ex[ée]cution|dur[ée]e\s+d['’]ex[ée]cution|"
    r"r[ée]sol(?:u|ution|vant)|solve|infer(?:red|ence)?|compute[ds]?|"
    r"elapsed|timing|benchmark(?:\w*)?|latency|throughput|"
    r"performance|mesure|mesur[ée]|performa?nce?)\b",
    re.IGNORECASE,
)

# Mot-cle qui signale un contexte parametre de distribution (bayesien,
# statistique) -- le chiffre est une variable continue du domaine, pas une
# duree machine. Exempt.
DISTRIBUTION_KEYWORDS = re.compile(
    r"\b(?:Gaussian|Normal|prior|posterior|posteriori|likelihood|vraisemblance|"
    r"moyenne|mean|std|sigma|sigma[_\s]?2|variance|precision|"
    r"distribution|mu_|sigma_|mixture|Dirichlet|Gamma|Beta|"
    r"intervalle?\s+de\s+confiance|IC\s+\d|probabilit[ée]?|"
    # #10178 Classe 5 (proposée po-2024, c.66 firsthand) : discriminants
    # bayesiens qui signalent qu'une durée (N min / N minutes) est une
    # quantité de domaine (composante de mélange, observation, trajet,
    # écart-type de la postérieure) et NON un wallclock machine. Sans
    # cette liste, les notebooks de Probas qui modélisent des grandeurs
    # temporelles (durée trajet vélo, durée décision) sont flaggés à tort
    # et un drain détruirait des paramètres du modèle (anti-regression §D).
    r"composantes?|observations?|trajets?|ecarts?[\-\s]?types?)\b",
    re.IGNORECASE,
)

# Mot-cle qui signale une CONSTANTE DE PROTOCOLE (consensus blockchain, canal
# de paiement) -- le chiffre est un parametre du domaine modifie, pas une
# duree machine. Exempt en tant que ``domain_quantity`` (cf. residu 2 #10169) :
# un ``settle_delay`` de canal XRP (3600 s) ou un temps de bloc Ethereum
# (12 blocs ~ 2 min) ne derivent pas d'une machine a l'autre -- ils ne derivent
# pas du tout, ce sont des parametres de consensus.
PROTOCOL_KEYWORDS = re.compile(
    r"\b(?:settle[\s\-_]?delay|settlement|temps\s+de\s+bloc|block[\s\-]?time|"
    r"blocs?(?:\s+(?:d['Ee]thereum|ethereum|de\s+bitcoin|bitcoin))?|"
    r"finalit[ée]|epoch|slot|confirmation|consensus|"
    r"canal\s+de\s+paiement|payment\s+channel|"
    # Tranche SymbolicAI #9434 (2026-08-19) : cadence d'INFRASTRUCTURE
    # (« Cluster CoursIA (4 workers, 30 min cadence) » -- Lean-20 c7).
    # La duree est la periode du cron, constante de configuration du
    # cluster, pas une mesure machine.
    r"cadences?|crons?|p[ée]riodicit[ée]|intervalle\s+de\s+r[ée]veil)\b",
    re.IGNORECASE,
)

# Contrainte de duree de CONTENU (longueur cible d'un media produit) : le chiffre
# est une borne du domaine (longueur max d'une video YouTube Shorts, duree cible
# d'un module de cours), pas une duree machine. Exempt en tant que
# ``domain_quantity`` (#10178 Classe 4). Discriminant : un wallclock strict ne
# s'encadre JAMAIS comme « contrainte de duree » / « duree cible » / « YouTube
# Shorts » / « module de cours » -- ce sont des descripteurs de CONTENU, pas
# d'execution. Verifie firsthand : GenAI/Video cell[12] « contraintes de duree
# (ex: moins de 5 minutes pour YouTube Shorts, ou exactement 10 minutes pour un
# module de cours) » = 2 FP wallclock -> domain_quantity ; le controle positif
# GenAI/Texte/10 cell[56] « Temps : 1M / 40 = 25,000 secondes » (vrai throughput
# compute) ne matche AUCUN de ces signaux et reste wallclock.
CONTENT_DURATION_CONSTRAINT_RE = re.compile(
    r"(?:\bcontrainte[s]?\s+(?:de\s+)?dur[ée]e\b"
    r"|\bdur[ée]e\s+(?:cible|totale|maximale|optimale|finale)\b"
    r"|\bdur[ée]e\s+de\s+la\s+vid[ée]o\b"
    r"|\bYouTube\s+Shorts\b"
    r"|\bmodule\s+de\s+cours\b)",
    re.IGNORECASE,
)

# Parametre de DESIGN d'un pipeline audio/mediatique : silence, fade,
# crossfade, pause, break SSML, extrait -- la duree est une CONSTANTE
# choisie par l'auteur du pipeline (visible dans le code), pas une mesure
# d'execution. Elle ne derive ni de la machine ni d'un re-run. Mesure du
# 2026-08-19 sur la tranche GenAI/Audio (#9434) : ~30 findings wallclock
# sur 3 notebooks (04-6/04-11/04-12) sont exactement cette classe
# (« Silence inter-segment: 500ms », « fade in/out de 200ms », « silences
# de 0.5 s generes par anullsrc », « <break time="500ms"/> », « un extrait
# de 30 s », « rate-limit de 0.2 s »). Proximite exigee (fenetre de 40
# chars sans '.' ni '|' : fin de phrase ou changement de cellule de table
# coupent le lien) pour ne pas exempter une duree qui cotoie le mot param
# par hasard.
PARAM_DURATION_RE = re.compile(
    r"\b(?:silences?|fades?|crossfades?|pauses?|breaks?|interludes?"
    r"|extraits?|seuils?|th?resholds?|rate[\s\-]?limits?)\b"
    r"[^.|]{0,40}?"
    r"\d+(?:[.,]\d+)?\s*(?:ms|millisecondes?|sec(?:ondes?)?|min(?:utes?)?|s)\b",
    re.IGNORECASE,
)

# Constante de CONFIG d'execution : timeout / limite de temps POSE sur le
# pipeline (solveur, build, service externe) -- le chiffre est un parametre
# choisi par l'auteur (visible dans le code qui le pose), pas une mesure
# machine. Mesure du 2026-08-19 sur la tranche SymbolicAI (#9434) : 5
# findings wallclock sur 5 notebooks etaient exactement cette classe
# (« Lancons le solveur CP-SAT avec un timeout de 30 secondes », « timeout
# de 15 minutes » via wsl_papermill, « Un timeout de 30 minutes est
# configure », « Le temps total est limite a 30 minutes », « Timeout =
# 30000, // 30 secondes » dans un listing C# en markdown). Proximite 40
# chars sans '.' ni '|' comme PARAM_DURATION_RE. NB : « limite a N » sans
# mot temps/timeout reste volontairement ABSENT de cette classe -- la forme
# « limitee a N requetes » est un quota de domaine, pas notre sujet ici.
TIMEOUT_LIMIT_RE = re.compile(
    r"\b(?:time[\s\-]?outs?|temps\s+total\s+(?:est\s+)?limit[ée]\s+(?:a|à)\b)"
    r"[^.|]{0,40}?"
    r"\d+(?:[.,]\d+)?\s*(?:ms|millisecondes?|sec(?:ondes?)?|min(?:utes?)?|s)\b",
    re.IGNORECASE,
)

# Pacing pedagogique : la cellule H1/H2/H3 documente l'effort demande a
# l'etudiant. Ligne entiere exoneree (cf. arbitrage jsboige 14:05:37Z #9434).
# Le motif "**Notebook** : ... 30-60 min selon niveau" est aussi couvert --
# c'est un format frequent dans la prose de series EPITA/IS (#10158 inventaire).
# CHANGES_REQUESTED #10162 (c.1331+59) : etend aux deux formes reelles observees
# dans l'inventaire 978 findings :
#  - parenhese en fin de titre de section : "## Titre (15 min)" ou "(1-2 min)"
#  - cellule de tableau markdown : "| 15 min |" (sommaire de serie)
STUDENT_PACING_RE = re.compile(
    r"(?:[Dd][uû]r[ée]e\s+(?:estim[ée]e|estim[ée]e|du\s+notebook|approximative)|"
    r"Duree\s*:|Durée\s*:|"
    r"\*\*Notebook\s*:|"
    r"\bDuree\s+du\s+notebook\b|"
    r"\b\d+\s*(?:-\s*\d+)?\s*(?:min(?:utes?)?|h(?:eures?)?)\s+(?:selon|approximativement|approximatif)\b|"
    # Extensions #10162 : parenhese "(15 min)" / "(1-2 min)"
    r"\(\d+\s*(?:-\s*\d+)?\s*(?:min(?:utes?)?|sec(?:ondes?)?|h(?:eures?)?)\)|"
    # Extensions #10162 : cellule de tableau "| 15 min |"
    r"\|\s*\d+\s*(?:-\s*\d+)?\s*(?:min(?:utes?)?|sec(?:ondes?)?|h(?:eures?)?)\s*\|"
    # Frontiere FP (frontier issue) : duree suivi d'un qualificatif d'effort
    # humain entre parentheses -- « 45 min (lecture + execution sequentielle) ».
    # C'est le meme signal que le pacing ci-dessus (effort demande a l'etudiant,
    # arbitrage jsboige 14:05:37Z #9434), mais la duree PRECEDE la parenthese au
    # lieu de s'y trouver (ex ICT-19-EnjeuBattery cell[0], ICT-19b cell[0]).
    # NB : on cible le qualificatif d'effort (lecture/cours/tp) precisement -- la
    # forme « moins de N » / « plus de N » est un signal de borne runtime OU de
    # probabilite de domaine (P(trajet < 18 min)), PAS de pacing, et ne doit PAS
    # etre exemptee (cf. brainstorm G.1 : sur-exemption cassait la propagation
    # per-cell #10162 et flagait des wallclock reels « plus de 4 secondes »).
    r"|\d+\s*(?:min(?:utes?)?|sec(?:ondes?)?|h(?:eures)?)\s*\(\s*(?:lecture|cours|travaux\s+pratiques|tp\b)"
    # Extensions tranche SymbolicAI (#9434, 2026-08-19) : pacing IMPERATIF
    # adresse a l'etudiant (« prenez 5 minutes pour lire », « (essayez 5
    # min) ») et borne ADVISORY de garde cold-start (« peut prendre 30
    # minutes a plusieurs heures », « Si ca prend plus de 15 minutes,
    # interrompez »). L'un et l'autre parlent de l'ATTENTE attendue de
    # l'etudiant, pas d'une mesure d'execution ; la forme passe « a pris
    # plus de N » (mesure) ne matche pas « prend plus de » (present).
    r"|\b(?:essayez|prenez|accordez[\s\-]?vous|consacrez)\b[^.|\n]{0,30}?\d+(?:[.,]\d+)?\s*(?:min(?:utes?)?|sec(?:ondes?)?|s)\b"
    r"|\b(?:peut\s+(?:prendre|durer)|prend\s+plus\s+de|prendre\s+plus\s+de)\b)",
    re.IGNORECASE,
)

# Fourchette / borne : comme `~`, c'est un signal d'ordre de grandeur et NON
# une mesure precise. Conforme au mandat #9434. CHANGES_REQUESTED #10162
# (c.1331+59) : `N-M min`, `< N sec`, `<= N sec`, `N+ min` ne sont PAS des
# wallclock -- ce sont des estimations, donc des soft signals.
def _is_range_bound(line: str, match_start: int, match_end: int) -> bool:
    """Detecte si le match MACHINE_RE est un soft signal (fourchette/borne).

    On regarde une fenetre de 8 chars AVANT match_start + le PREMIER char du
    match (= la borne haute N2 d'une fourchette 'N1-N2 unit'). Renvoie True
    si le match est une fourchette (`N-M`), une borne superieure (`< N`),
    ou une borne inferieure (`N+`).
    """
    # Fenetre de recherche : 8 chars avant match_start + le 1er char du match.
    # NB : on inclut le 1er char du match parce que la fourchette 'N1-N2'
    # a son digit N2 (= debut du match MACHINE_RE) a match_start, et le '-'
    # juste avant. Sans inclure le debut du match, on ne verrait que 'N1-'
    # (et la regex '\d-\d$' ne matche pas, parce qu'on n'a pas N2).
    lo = max(0, match_start - 8)
    hi = min(len(line), match_start + 1)
    window = line[lo:hi]
    # Test 1 : fourchette 'N1-N2 unit' -- '\d-\d' en fin de la fenetre.
    if re.search(r"\d\s*-\s*\d\s*$", window):
        return True
    # Test 2 : borne '< N' ou '<= N' / borne '> N' ou '>= N' -- la borne en
    # fin de fenetre. La borne inferieure stricte est le symetrique oublie
    # de #10162 (04-12-Compilation-Audio c22 : « narration longs (> 10
    # secondes) » = seuil de classification d'exercice, pas une mesure).
    # NB : un '>' en DEBUT de ligne est un BLOCKQUOTE markdown, pas une
    # borne mathematique -- « > 25 s, zero barre minute chargee »
    # (research_m12_har_rv_j_minute c0, duree mesuree d'un run) reste
    # wallclock. On exige donc du contenu non-blanc AVANT la borne.
    m2 = re.search(r"([<>])\s*=?\s*\d\s*$", window)
    if m2:
        bound_pos = line.rfind(m2.group(1), 0, match_start)
        if bound_pos > 0 and line[:bound_pos].strip():
            return True
    # Test 3 : borne inferieure 'N+' -> le match est 'N X' et le caractere
    # APRES le debut du nombre est '+'. Ex : '5+ min' -> match = '5 min',
    # match_start pointe sur '5', line[match_start:match_start+3] = '5+ '.
    if match_end > match_start and re.match(r"\d\s*\+", line[match_start:match_end + 3]):
        return True
    return False


def _is_detached_approximate(line: str, match_start: int) -> bool:
    """Detecte un marqueur d'ordre de grandeur DETACHE : ``~ 2 min`` (espace).

    Le ``MACHINE_RE`` accolé ``~2 min`` est deja gere (le ``~?`` optionnel
    inclus dans le match -> ``snippet.startswith('~')`` -> skip). Ce helper
    couvre la forme avec espace, ou le ``~`` (ou ``≈``) precede le chiffre
    d'une espace -- cas reel SC-23-Cross-Chain : « 12 blocs Ethereum ~ 2 min »
    (residu 2 #10169). Conforme au mandat #9434 : ordre de grandeur, pas
    mesure precise -> on ne signale pas.
    """
    # Fenetre de 3 chars avant le match : le marqueur + eventuelle espace.
    lo = max(0, match_start - 3)
    window = line[lo:match_start]
    if re.search(r"[~≈]\s*$", window):
        return True
    # Forme FRANCAISE du marqueur d'ordre de grandeur : « de l'ordre de N s »,
    # « de l'ordre de grandeur de N s » (04-11-Generation-TTS c10 : « chaque
    # segment prend de l'ordre de 3 s a generer » -- deja le traitement
    # sanctionne par le mandat, mais ecrit en toutes lettres la ou le tilde
    # etait attendu). Fenetre elargie a 25 chars : le marqueur le plus long
    # est « ordre de grandeur de ~ ».
    lo2 = max(0, match_start - 25)
    window2 = line[lo2:match_start]
    return bool(re.search(
        r"(?:l['’]\s*)?ordre(?:\s+de\s+grandeur)?\s+de\s*~?\s*$", window2,
        re.IGNORECASE,
    ))


# --- Exemptions positionnelles tranche SymbolicAI (#9434, 2026-08-19) ----- #
# Trois formes ou le match MACHINE_RE n'est PAS une duree mais un token
# derive d'une constante : numero de section decimal, conversion d'unite
# parenthetique, traduction litterale d'un sleep() du code.


def _is_section_number(line: str, match_start: int, snippet: str) -> bool:
    """Numero de section DECIMAL dans un header markdown.

    « ### 2.3 MIN (FIN) -- l'independance des choix » (Lean-16f cell[9]) :
    le match « 2.3 MIN » est le titre de la section 2.3 portant sur l'axiome
    MIN de Conway-Kochen -- pas « 2,3 minutes ». Discriminant double : le
    snippet COMMENCE par un decimal (une vraie duree s'ecrit « 2,3 min » ou
    « 2 min 30 », jamais en position de titre) et un header markdown
    (#..######) precede immediatement le match.
    """
    if not re.match(r"\d+[.,]\d+", snippet):
        return False
    lo = max(0, match_start - 8)
    return bool(re.search(r"#{2,6}\s*$", line[lo:match_start]))


def _is_unit_conversion(line: str, match_start: int) -> bool:
    """Conversion D'UNITE entre parentheses d'une constante primaire.

    « | Recherche | 500s (8.3 min) | 8000 MB | » (Fast-Downward-Legacy
    cell[9]) : le match « 8.3 min » derive arithmetiquement de la borne de
    config 500s posee par l'auteur de la table -- c'est la meme constante
    convertie, pas une mesure machine. Discriminant : une valeur+unite de
    temps ouvre la parenthese immediatement avant le match. (La forme
    entiere « (5 min) » etait deja exoneree par la parenthese pacing
    #10162 ; seul le decimal lui echappait.)
    """
    lo = max(0, match_start - 16)
    return bool(re.search(
        r"\d+(?:[.,]\d+)?\s*(?:ms|s|sec(?:ondes?)?)\s*\(\s*$", line[lo:match_start],
        re.IGNORECASE,
    ))


def _is_code_constant_translation(line: str, match_start: int) -> bool:
    """Traduction litterale d'une constante sleep() du code, meme ligne.

    « `ui_events().poll(10)` avec `sleep(0.1)` = polling toutes les 100ms »
    (Argument_Analysis_UI cell[22]) : le 100ms est la conversion affichee de
    la constante `sleep(0.1)` visible dans la ligne -- il ne peut pas
    deriver d'une machine a l'autre puisqu'il EST le code. Discriminant :
    un appel sleep(N) apparait AVANT le match dans la meme ligne.
    """
    return bool(re.search(
        r"\bsleep\s*\(\s*\d+(?:[.,]\d+)?\s*\)", line[:match_start],
    ))


# --------------------------------------------------------------------------- #
#  Taxonomie de sortie
# --------------------------------------------------------------------------- #
# On categorise chaque finding en 4 classes :
# - ``wallclock`` : duree machine-dependante reelle (regex + contexte wall-clock
#   present ou absence de mot-cle distribution). Cible du drainage #9434.
# - ``distribution_param`` : la regex matche mais le contexte est distribution
#   bayesienne/stat (parametre de modele, pas une duree machine). TN dur.
# - ``ambiguous`` : aucun mot-cle de contexte. Le reviewer humain arbitre.
# - ``domain_quantity`` : la duree EST la variable modelisee par le notebook
#   (cf. FP-2 #10162). Propagation per-cell : si le notebook porte
#   distribution_param sur >=1 finding, les autres findings de la meme cellule
#   basculent en domain_quantity plutot qu'en wallclock -- l'unite de temps
#   est le sujet du modele, pas une mesure d'execution.

CATEGORY_WALLCLOCK = "wallclock"
CATEGORY_DISTRIBUTION = "distribution_param"
CATEGORY_AMBIGUOUS = "ambiguous"
CATEGORY_DOMAIN_QUANTITY = "domain_quantity"


def _categorize(line: str, snippet: str) -> str:
    """Classifie un finding selon le contexte de la ligne qui le contient.

    Heuristique : on regarde la LIGNE ENTIERE, pas le snippet isole, parce que
    le mot-cle est generalement a proximite du chiffre (« Gaussian(15.33, 1.32)
    -> moyenne 15.33 min, ecart type 1.32 min »). Si la ligne contient un mot
    distribution, on classe en distribution_param. Sinon, si elle contient un
    mot wall-clock ou si le snippet n'a PAS de marqueur `~`, on classe en
    wallclock. Sinon : ambiguous (a arbitrer).
    """
    if DISTRIBUTION_KEYWORDS.search(line):
        return CATEGORY_DISTRIBUTION
    # Constante de protocole (consensus blockchain / canal de paiement) :
    # parametre du domaine, pas une duree machine. Residu 2 #10169.
    if PROTOCOL_KEYWORDS.search(line):
        return CATEGORY_DOMAIN_QUANTITY
    # Contrainte de duree de CONTENU (#10178 Classe 4) : longueur cible d'un
    # media produit (YouTube Shorts, module de cours, duree cible de video).
    # Borne du domaine, pas une duree machine -- les 2 FP GenAI/Video cell[12].
    if CONTENT_DURATION_CONSTRAINT_RE.search(line):
        return CATEGORY_DOMAIN_QUANTITY
    # Parametre de design d'un pipeline audio (silence/fade/pause/extrait...)
    # -- constante du code, pas une duree machine. Cf. PARAM_DURATION_RE.
    if PARAM_DURATION_RE.search(line):
        return CATEGORY_DOMAIN_QUANTITY
    # Constante de CONFIG d'execution (timeout/limite pose sur le pipeline)
    # -- cf. TIMEOUT_LIMIT_RE. Parametre du code, pas une mesure machine.
    if TIMEOUT_LIMIT_RE.search(line):
        return CATEGORY_DOMAIN_QUANTITY
    # Frontiere FP (frontier issue) : cout d'action dans une table de plan.
    # La duree est le RESULTAT d'une arithmetique « N + M = K unit » (ex
    # Planners-8-Temporal cell[37] « 5 + 4 = 9 min » = duree d'une livraison
    # drone). C'est un parametre DETERMINISTE du domaine planifie, pas une
    # duree machine. Le motif est precis (un vrai wallclock ne se rend presque
    # jamais comme une somme explicite `a + b = c unit`) -- Sudoku-13 (controle
    # positif) n'a aucune ligne de cette forme, donc reste detecte.
    # « 13 x 500ms = 6.5s » (04-12 c12/c14/c17, silences d'assemblage) est
    # la meme classe deterministe en multiplication -- l'unite interne du
    # facteur droit (500ms) est acceptee.
    if re.search(
        r"\d+\s*[+×x*]\s*\d+\s*(?:ms|millisecondes?|sec(?:ondes?)?|min(?:utes?)?|s)?\s*=\s*\d+(?:[.,]\d+)?\s*"
        r"(?:min(?:utes?)?|sec(?:ondes?)?|s\b|h(?:eures)?)", line):
        return CATEGORY_DOMAIN_QUANTITY
    if WALLCLOCK_KEYWORDS.search(line):
        return CATEGORY_WALLCLOCK
    # Pas de mot-cle de contexte : on considere que la presence de la regex
    # seule (sans `~`) est un signal wallclock, parce que le drainage #9434
    # assume que les chiffres machine-dep sont ecrits tels quels.
    # L'echec de cette hypothese = FP que le reviewer peut flagger comme
    # TN via une exemption contextuelle.
    return CATEGORY_WALLCLOCK


# --------------------------------------------------------------------------- #
#  Coeur du scan
# --------------------------------------------------------------------------- #
def _iter_markdown_lines(cell: dict) -> list[str]:
    """Yield les lignes d'une cellule markdown."""
    src = cell.get("source", "")
    if isinstance(src, list):
        src = "".join(src)
    return src.splitlines() if src else []


# --------------------------------------------------------------------------- #
#  Provenance d'un finding (#9434) -- opt-in, ne change rien par defaut
# --------------------------------------------------------------------------- #
# Mesure du 2026-09-02 (lane myia-po-2024:CoursIA-2, issuecomment-5505846033) :
# sur les 288 findings `wallclock` du depot, 283 citent un nombre que le
# notebook PORTE deja -- dans ses outputs, dans ses cellules de code, ou dans
# un fichier compagnon qu'il pilote. Le compteur ne le voyait pas parce qu'il
# raisonne ligne a ligne, sur du TEXTE.
#
# La consequence est celle qu'ai-01 a nommee sur ce fil : "une metrique
# d'occurrences se satisfait toujours en supprimant, jamais en corrigeant".
# Un drainage pilote par le compteur brut supprimerait de la prose qui LIT
# correctement une sortie -- exactement ce que le test READS-vs-AFFIRMS protege.
#
# Quatre provenances, dans l'ordre de preference :
#   OUT  -- la valeur est dans une sortie de cellule du notebook
#   DER  -- elle est un RATIO de deux valeurs de sortie (« ~72x », « ~40 »)
#   SRC  -- elle est declaree dans une cellule de code (constante, parametre)
#   COMP -- elle est dans un fichier compagnon que le notebook pilote
#           (`Program.cs`, `.csproj`, config...) : c'est une SPECIFICATION
# Aucune des quatre -> `unbacked` : le seul residu qui merite un regard humain.
#
# LIMITE, a lire avant de se fier au chiffre : la tolerance de 5 % sur six
# echelles peut ABSORBER un vrai defaut par coincidence numerique. Le compte
# `unbacked` est donc un PLANCHER du legitime, pas un plafond du defaut. Il
# reduit un tri de 288 lignes a un tri de 5 ; il ne prouve pas que les 283
# autres soient toutes justes.
PROVENANCE_TOLERANCE = 0.05

# Echelles admises entre le nombre en prose et la valeur portee par le
# notebook. Mesurees sur les cas reels du depot :
#   1.0     identite (« 2,97 » <- 2.9682, arrondi)
#   1000.0  s -> ms (« ~60 ms » <- 0.0587 s)
#   0.001   ms -> s
#   60.0    min -> s   /  1/60  s -> min
#   0.01    fraction -> pourcentage (« 4,1 % » <- 0.0410)
PROVENANCE_SCALES = (1.0, 1000.0, 0.001, 60.0, 1.0 / 60.0, 0.01)

PROVENANCE_ORDER = ("OUT", "DER", "SRC", "COMP")
PROVENANCE_UNBACKED = "unbacked"

# Extensions de fichiers compagnons scannes pour la provenance COMP.
_COMPANION_SUFFIXES = (
    ".cs", ".py", ".fs", ".csproj", ".json", ".yml", ".yaml",
    ".ps1", ".sh", ".lean",
)
_COMPANION_SKIP_DIRS = (
    ".ipynb_checkpoints", "bin", "obj", ".lake", "node_modules", "__pycache__",
)
# Budget de lecture des compagnons (caracteres). Une serie comme QuantConnect
# porte des dumps de donnees ; sans borne, `--all --provenance` deviendrait
# quadratique.
_COMPANION_CHAR_BUDGET = 400_000
# Budget de lecture des outputs d'un notebook. Les blobs base64 d'images sont
# exclus AVANT ce compte (ils n'apportent aucun nombre lisible et saturaient la
# mesure -- FP observe pendant la calibration).
_OUTPUT_CHAR_BUDGET = 2_000_000

_NUMBER_RE = re.compile(r"[0-9][0-9]*(?:[.,][0-9]+)?")

# Cache par repertoire : plusieurs notebooks d'une meme serie partagent leurs
# compagnons. Sans cache, `--all --provenance` relit `Program.cs` a chaque fois.
_COMPANION_CACHE: dict[str, list[float]] = {}


def _parse_numbers(text: str) -> list[float]:
    """Extrait les nombres d'un texte, virgule decimale francaise comprise.

    « 2,97 » et « 2.97 » rendent tous deux 2.97. C'est le point ou une premiere
    version de cet outil s'est trompee : elle normalisait en SUPPRIMANT la
    virgule, ce qui transformait « 0,041 » en 41.
    """
    out: list[float] = []
    for tok in _NUMBER_RE.findall(text):
        try:
            out.append(float(tok.replace(",", ".")))
        except ValueError:
            continue
    return out


def _values_close(prose: float, carried: float) -> bool:
    """Le nombre en prose correspond-il a une valeur portee, a une echelle pres ?

    La comparaison est RELATIVE (5 %) parce que la prose arrondit : « 2,97 »
    pour 2.9682, « ~60 ms » pour 0.0587 s. Une comparaison exacte ne
    reconnaitrait aucun de ces deux cas, qui sont pourtant la lecture correcte
    d'une sortie.
    """
    for scale in PROVENANCE_SCALES:
        scaled = carried * scale
        if not scaled:
            continue
        if abs(scaled - prose) <= PROVENANCE_TOLERANCE * max(abs(scaled), abs(prose)):
            return True
    return False


def _output_values(data: dict) -> list[float]:
    """Nombres portes par les SORTIES de cellules du notebook.

    Les blobs `image/*` sont exclus : ils ne portent aucun nombre lisible et
    leur base64 produisait des correspondances fortuites.
    """
    budget = _OUTPUT_CHAR_BUDGET
    chunks: list[str] = []
    for cell in data.get("cells", []):
        for out in cell.get("outputs", []) or []:
            if not isinstance(out, dict):
                continue
            texts: list = []
            if "text" in out:
                texts.append(out["text"])
            payload = out.get("data") or {}
            if isinstance(payload, dict):
                for mime, val in payload.items():
                    if mime.startswith("image/"):
                        continue
                    texts.append(val)
            for t in texts:
                if isinstance(t, list):
                    t = "".join(str(x) for x in t)
                if not isinstance(t, str):
                    continue
                chunks.append(t[:budget])
                budget -= len(t)
                if budget <= 0:
                    return _parse_numbers("\n".join(chunks))
    return _parse_numbers("\n".join(chunks))


def _source_values(data: dict) -> list[float]:
    """Nombres declares dans les cellules de CODE (constantes, parametres).

    Une prose qui cite `Thread.Sleep(500)` en disant « 500 ms » ne fabrique
    rien : elle lit une specification du notebook lui-meme.
    """
    chunks: list[str] = []
    for cell in data.get("cells", []):
        if cell.get("cell_type") != "code":
            continue
        src = cell.get("source", "")
        if isinstance(src, list):
            src = "".join(src)
        if isinstance(src, str):
            chunks.append(src)
    return _parse_numbers("\n".join(chunks))


def _companion_values(nb_path: Path) -> list[float]:
    """Nombres portes par les fichiers compagnons du repertoire du notebook.

    Un notebook qui pilote un `Program.cs` cite legitimement les constantes de
    ce programme : c'est une SPECIFICATION, pas une mesure machine.
    """
    key = str(nb_path.parent)
    cached = _COMPANION_CACHE.get(key)
    if cached is not None:
        return cached

    budget = _COMPANION_CHAR_BUDGET
    chunks: list[str] = []
    try:
        for path in sorted(nb_path.parent.rglob("*")):
            if budget <= 0:
                break
            if not path.is_file() or path.suffix.lower() not in _COMPANION_SUFFIXES:
                continue
            if any(part in _COMPANION_SKIP_DIRS for part in path.parts):
                continue
            try:
                text = path.read_text(encoding="utf-8", errors="ignore")
            except OSError:
                continue
            chunks.append(text[:budget])
            budget -= len(text)
    except OSError:
        pass

    values = _parse_numbers("\n".join(chunks))
    _COMPANION_CACHE[key] = values
    return values


def _derived_ratios(values: list[float], top_n: int = 60, cap: int = 4000) -> list[float]:
    """Ratios entre valeurs de sortie -- les facteurs « ~72x », « ~40 ».

    Un notebook qui mesure 2.97 s et 0.041 s et ecrit « ~72x plus rapide »
    n'affirme rien qui ne soit dans ses sorties : le facteur EST la lecture.
    Bornes (`top_n`, `cap`) : le produit cartesien est quadratique.
    """
    top = sorted({v for v in values if v}, reverse=True)[:top_n]
    ratios: list[float] = []
    for a in top:
        for b in top:
            if not b:
                continue
            r = a / b
            if 1.0 < r < 100_000.0:
                ratios.append(r)
                if len(ratios) >= cap:
                    return ratios
    return ratios


def _annotate_provenance(findings: list[dict], data: dict, nb_path: Path) -> None:
    """Passe 4 (opt-in) : annote chaque finding d'une cle ``provenance``.

    Ne change AUCUNE categorie : la provenance est une lecture ORTHOGONALE a la
    classification. Un `wallclock` reste `wallclock` ; on dit seulement si le
    nombre qu'il pointe est porte par le notebook ou non.
    """
    if not findings:
        return
    outputs = _output_values(data)
    sources = _source_values(data)
    ratios = _derived_ratios(outputs)
    companions: list[float] | None = None  # charge paresseusement (couteux)

    for f in findings:
        prose = _parse_numbers(f.get("snippet", ""))
        if not prose:
            f["provenance"] = PROVENANCE_UNBACKED
            continue
        if any(_values_close(p, o) for p in prose for o in outputs):
            f["provenance"] = "OUT"
        elif any(_values_close(p, r) for p in prose for r in ratios):
            f["provenance"] = "DER"
        elif any(_values_close(p, s) for p in prose for s in sources):
            f["provenance"] = "SRC"
        else:
            if companions is None:
                companions = _companion_values(nb_path)
            if any(_values_close(p, c) for p in prose for c in companions):
                f["provenance"] = "COMP"
            else:
                f["provenance"] = PROVENANCE_UNBACKED


def _scan_notebook(nb_path: Path, provenance: bool = False) -> list[dict]:
    """Scan un notebook ; retourne la liste des findings structures.

    Chaque finding est un dict ``{cell_index, line_index, snippet, line,
    category}``. Les cellules code + outputs sont SAUTEES (jamais inspectees)
    -- cf. #10158 acceptance : "les cellules de code et les outputs (une
    sortie doit porter la valeur reelle mesuree -- c'est sa fonction)".

    Strategie en 3 passes (FP-2 #10162 + residu 1 #10169) :

    1. **Passe ligne** : pour chaque ligne markdown, on applique les exemptions
       (pacing pedagogique, tilde colle/detache, fourchette/borne, constante de
       protocole) et on classifie selon le contexte de la ligne (wallclock /
       distribution_param / domain_quantity / ambiguous).
    2. **Passe cellule** : si une cellule porte >=1 finding ``distribution_param``,
       tous les autres findings ``wallclock`` de la meme cellule basculent en
       ``domain_quantity`` -- l'unite de temps est le sujet du modele, pas une
       mesure d'execution (cf. FP-2 sur Infer-2-Gaussian-Mixtures).
    3. **Passe notebook** : si le notebook ENTIER porte >=1 ``distribution_param``,
       les ``wallclock`` residuels (cellules sans mot-cle stat) basculent aussi
       en ``domain_quantity`` (residu 1 #10169 : les 6 findings Infer-2 dont les
       moyennes ajustees 15.07 / 26.69 min). La granularite per-cell etait trop
       etroite -- l'unite de temps est le sujet du notebook, pas d'une cellule.
    4. **Passe provenance** (opt-in ``provenance=True``, #9434) : annote chaque
       finding d'une cle ``provenance`` disant si le nombre cite est PORTE par le
       notebook (``OUT`` sortie / ``DER`` ratio de sorties / ``SRC`` cellule de
       code / ``COMP`` fichier compagnon) ou ``unbacked``. Aucune categorie n'est
       modifiee : la provenance est orthogonale a la classification. Par defaut la
       passe ne tourne PAS et la sortie est byte-identique a l'existant.
    """
    try:
        data = json.loads(nb_path.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, UnicodeDecodeError, OSError):
        return []

    # Passe 1 : scan ligne par ligne.
    findings: list[dict] = []
    for ci, cell in enumerate(data.get("cells", [])):
        if cell.get("cell_type") != "markdown":
            continue
        for li, line in enumerate(_iter_markdown_lines(cell)):
            # Pacing pedagogique : ligne entiere exoneree.
            if STUDENT_PACING_RE.search(line):
                continue
            for m in MACHINE_RE.finditer(line):
                snippet = m.group(0)
                # Deja conforme : `~10 s` = ordre de grandeur, conforme au
                # mandat #9434. On ne signale pas (cf. acceptance #10158).
                if snippet.startswith("~"):
                    continue
                # CHANGES_REQUESTED #10162 : fourchette/borne = soft signal
                # (`N-M min`, `< N sec`, `N+ min`). On ne signale pas, comme
                # pour le tilde.
                if _is_range_bound(line, m.start(), m.end()):
                    continue
                # Residu 2 #10169 : tilde DETACHE (`~ 2 min`, marqueur + espace).
                # Ordre de grandeur, comme le tilde colle et la fourchette.
                if _is_detached_approximate(line, m.start()):
                    continue
                # Tranche SymbolicAI #9434 : token derive d'une constante
                # (numero de section decimal, conversion d'unite
                # parenthetique, traduction d'un sleep() du code).
                if _is_section_number(line, m.start(), snippet):
                    continue
                if _is_unit_conversion(line, m.start()):
                    continue
                if _is_code_constant_translation(line, m.start()):
                    continue
                category = _categorize(line, snippet)
                findings.append({
                    "cell_index": ci,
                    "line_index": li,
                    "snippet": snippet,
                    "line": line.strip()[:200],
                    "category": category,
                })

    # Passe 2 : propagation per-cell domain_quantity. Si une cellule porte
    # >=1 finding distribution_param, tous les findings wallclock de cette
    # cellule basculent en domain_quantity (FP-2 #10162).
    by_cell: dict[int, list[dict]] = {}
    for f in findings:
        by_cell.setdefault(f["cell_index"], []).append(f)
    for ci, cell_findings in by_cell.items():
        has_distribution = any(
            f["category"] == CATEGORY_DISTRIBUTION for f in cell_findings
        )
        if not has_distribution:
            continue
        for f in cell_findings:
            if f["category"] == CATEGORY_WALLCLOCK:
                f["category"] = CATEGORY_DOMAIN_QUANTITY

    # Passe 3 : propagation per-NOTEBOOK domain_quantity (residu 1 #10169).
    # La propagation per-cell (passe 2) est trop etroite : 6 findings Infer-2
    # restent wallclock parce que leur cellule ne porte aucun mot-cle statistique,
    # alors que le notebook entier modelise un temps de trajet. Si le notebook
    # porte >=1 finding distribution_param, l'unite de temps est le SUJET du
    # modele -> tous les wallclock residuels basculent en domain_quantity.
    nb_has_distribution = any(
        f["category"] == CATEGORY_DISTRIBUTION for f in findings
    )
    if nb_has_distribution:
        for f in findings:
            if f["category"] == CATEGORY_WALLCLOCK:
                f["category"] = CATEGORY_DOMAIN_QUANTITY

    # Passe 4 : provenance (opt-in). Hors --provenance, on ne paie ni la
    # lecture des outputs ni le scan des compagnons.
    if provenance:
        _annotate_provenance(findings, data, nb_path)

    return findings


def _repo_root() -> Path:
    """Racine du depot : ``git rev-parse --show-toplevel`` (authoritatif),
    fallback ``parents[2]`` du script.

    Residu 3 #10169 : ``parents[2]`` resolu depuis l'emplacement du script
    fonctionne seulement tant que le script vit a ``<root>/scripts/...``. Un
    outil invoque hors du repertoire (le cas d'usage canonique ``--all``)
    doit trouver ses cibles depuis la racine git reelle, pas depuis un
    chemin calcule par hypothese.
    """
    try:
        out = subprocess.check_output(
            ["git", "rev-parse", "--show-toplevel"],
            cwd=str(Path(__file__).resolve().parent),
            stderr=subprocess.DEVNULL,
            text=True, encoding="utf-8", errors="replace",
        ).strip()
        if out:
            return Path(out).resolve()
    except (OSError, subprocess.CalledProcessError, subprocess.SubprocessError):
        pass
    return Path(__file__).resolve().parents[2]


def _collect_targets(args: argparse.Namespace) -> list[Path]:
    """Resout la liste des notebooks a scanner depuis la CLI.

    Precedence (fix #10445 partie b) : des ``paths`` explicites sont TOUJOURS
    honors, meme quand ``--json``/``--check`` sont passes. Avant, ``--json``
    impliquait ``--all`` en silence (``if args.all or args.json or args.check``
    en premiere branche) : un appel ``--json chemin.ipynb`` scannait les 1015
    notebooks du depot et jetait ``chemin.ipynb`` sans un mot -- produisant des
    mesures fausses chez tous les appelants (incident merge-gate #10442 : 215
    timings du repo attribues a 1 notebook GameTheory qui en contribuait 0).
    Un outil qui jette un argument en silence est un bug de correctness, pas
    un defaut d'ergonomie ; on ne l'ignore donc jamais sans prevenir.
    ``--all`` explicite force l'inventaire complet (sa semantique) meme si des
    paths sont aussi donnes -- cas contradictoire qui emet un avertissement
    stderr pour ne pas jeter ``paths`` en silence.
    """
    root = _repo_root()
    if args.paths and not args.all:
        # paths explicites = scan cible, quel que soit --json/--check.
        candidates = []
        for p in args.paths:
            pp = Path(p)
            if pp.is_file() and pp.suffix == ".ipynb":
                candidates.append(pp)
            elif pp.is_dir():
                candidates.extend(sorted(pp.rglob("*.ipynb")))
    elif args.all or args.json or args.check:
        # Cible canonique : notebooks pedagogiques. Les READMEs et `assets/`
        # sont exclus -- le scope de #10158 est uniquement les ``.ipynb``.
        if args.all and args.paths:
            # --all force l'inventaire mais des paths etaient donnes : on ne
            # les jette pas en silence (regle : ne jamais ignorer un argument).
            print(
                "Avertissement : --all force le scan repo-entier ; "
                "les paths fournis sont ignores.",
                file=sys.stderr,
            )
        candidates = sorted(root.glob("MyIA.AI.Notebooks/**/*.ipynb"))
    else:
        return []
    # Filtre sortie : cibles _output.ipynb (artefacts transitoires) et
    # notebooks PII-governed -- le scope de l'inventaire est la prose
    # pedagogique statique.
    out = []
    for c in candidates:
        if "_output.ipynb" in c.name:
            continue
        try:
            data = json.loads(c.read_text(encoding="utf-8"))
        except (json.JSONDecodeError, OSError):
            continue
        if data.get("metadata", {}).get("pii_no_output") is True:
            continue
        out.append(c)
    return out


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Detecteur dedie : temps d'horloge machine-dependants en prose "
            "de notebook (markdown). Sortie JSON/TSV. Mode advisory (exit 0)."
        )
    )
    parser.add_argument(
        "paths",
        nargs="*",
        help="Notebooks ou repertoires a scanner (defaut: --all).",
    )
    parser.add_argument(
        "--all",
        action="store_true",
        help="Scanner tous les .ipynb de MyIA.AI.Notebooks/**.",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Sortie JSON structuree (par defaut: TSV lisible).",
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="Mode CI : exit 1 si findings wallclock detectes (futur).",
    )
    parser.add_argument(
        "--category",
        choices=[CATEGORY_WALLCLOCK, CATEGORY_DISTRIBUTION, CATEGORY_AMBIGUOUS, CATEGORY_DOMAIN_QUANTITY, "all"],
        default="wallclock",
        help=(
            "Filtre categorie de sortie (defaut: wallclock = cible drainage). "
            "ATTENTION : ce filtre ne s'applique qu'a la sortie TSV. En --json, "
            "`findings` porte TOUTES les categories (c'est `summary` qui les "
            "ventile) -- sommer `findings` en croyant lire une categorie donne "
            "un compte survalue."
        ),
    )
    parser.add_argument(
        "--provenance",
        action="store_true",
        help=(
            "Annote chaque finding d'une provenance (OUT/DER/SRC/COMP/unbacked) : "
            "le nombre cite est-il PORTE par le notebook (sortie, ratio de sorties, "
            "cellule de code, fichier compagnon) ou non ? Sans ce flag, la sortie "
            "est inchangee."
        ),
    )
    args = parser.parse_args(argv)

    targets = _collect_targets(args)
    if not targets:
        # Residu 3 #10169 : un resultat vide sur une invocation explicite
        # (--all/--json/--check ou paths nommes) est une ERREUR bruyante, pas
        # un succes silencieux. Sinon la lane suivante apprend qu'il n'y a
        # rien a faire alors que l'outil a juste rate la racine git.
        explicit_scan = bool(args.all or args.json or args.check or args.paths)
        if explicit_scan:
            print(
                "Aucun notebook a scanner sous la racine git. "
                "Invoque depuis le depot, ou passe des chemins explicites.",
                file=sys.stderr,
            )
            return 1
        parser.print_help(sys.stderr)
        return 1

    repo_root = _repo_root()
    all_findings: dict[str, list[dict]] = {}
    wallclock_count = 0
    distribution_count = 0
    ambiguous_count = 0
    domain_quantity_count = 0
    for nb_path in targets:
        rel = str(nb_path)
        # Afficher le chemin relatif a la racine du depot si possible.
        try:
            rel = str(nb_path.resolve().relative_to(repo_root))
        except ValueError:
            pass
        findings = _scan_notebook(nb_path, provenance=args.provenance)
        if findings:
            all_findings[rel] = findings
        for f in findings:
            if f["category"] == CATEGORY_WALLCLOCK:
                wallclock_count += 1
            elif f["category"] == CATEGORY_DISTRIBUTION:
                distribution_count += 1
            elif f["category"] == CATEGORY_DOMAIN_QUANTITY:
                domain_quantity_count += 1
            else:
                ambiguous_count += 1

    # Ventilation provenance par categorie (uniquement sous --provenance).
    # Elle repond a la question que le compte brut ne posait pas : parmi les
    # findings d'une categorie, combien citent un nombre que le notebook porte
    # deja ? Le residu `unbacked` est le seul tri qui merite un regard humain.
    provenance_summary: dict[str, dict[str, int]] = {}
    if args.provenance:
        for findings in all_findings.values():
            for f in findings:
                bucket = provenance_summary.setdefault(
                    f["category"],
                    {k: 0 for k in PROVENANCE_ORDER + (PROVENANCE_UNBACKED,)},
                )
                bucket[f.get("provenance", PROVENANCE_UNBACKED)] += 1

    if args.json:
        out = {
            "scanned": len(targets),
            "summary": {
                "wallclock": wallclock_count,
                "distribution_param": distribution_count,
                "domain_quantity": domain_quantity_count,
                "ambiguous": ambiguous_count,
                "total": wallclock_count + distribution_count + domain_quantity_count + ambiguous_count,
            },
            "findings": all_findings,
        }
        if args.provenance:
            out["provenance_summary"] = provenance_summary
        print(json.dumps(out, ensure_ascii=False, indent=2))
    else:
        # Mode TSV lisible (par defaut : wallclock = cible drainage).
        cat_filter = None if args.category == "all" else args.category
        print(f"# check_machine_dep_timing -- scanned={len(targets)}")
        print(f"# wallclock={wallclock_count} distribution_param={distribution_count} "
              f"domain_quantity={domain_quantity_count} ambiguous={ambiguous_count}")
        if args.provenance:
            shown = args.category if cat_filter else "all"
            bucket = provenance_summary.get(cat_filter, {}) if cat_filter else {}
            if not cat_filter:  # agrege toutes categories
                bucket = {k: 0 for k in PROVENANCE_ORDER + (PROVENANCE_UNBACKED,)}
                for b in provenance_summary.values():
                    for k, v in b.items():
                        bucket[k] = bucket.get(k, 0) + v
            detail = " ".join(f"{k}={bucket.get(k, 0)}"
                              for k in PROVENANCE_ORDER + (PROVENANCE_UNBACKED,))
            print(f"# provenance[{shown}] {detail}")
        for nb_rel, findings in sorted(all_findings.items()):
            for f in findings:
                if cat_filter and f["category"] != cat_filter:
                    continue
                prov = f"\t{f['provenance']}" if args.provenance else ""
                print(f"{nb_rel}\tcell[{f['cell_index']}]\t{f['snippet']}\t{f['category']}{prov}\t{f['line'][:120]}")

    # Mode advisory par defaut (exit 0). --check reserved pour le futur quand
    # le stock wallclock sera draine (cf. condition de sortie de #9434).
    if args.check and wallclock_count > 0:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
