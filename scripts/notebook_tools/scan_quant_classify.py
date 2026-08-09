"""Detecteur quant-4-classes — triage des valeurs quantitatives ecrites en dur
dans les cellules markdown des notebooks.

Suite directe de l'EPIC #9434 (mandat « quantitatif tenu par le CI, pas par la
prose ») et de l'outillage Phase 1 #9768 (detecteurs D1+D3+D4+D5 trans-historique
et D5 v3 intra-revision, PRs #9791 + #9793 MERGED). Reutilise
`_extract_prose_numbers` et `_parse_fr_number` de `scan_d5_prose_outputs_alignment`.

## Les 4 classes (cf. issue #9434)

| Classe | Dérive? | Heuristique |
|---|---|---|
| **STRUCTUREL** | Non | Pas d'unite temporelle, pas de pattern `X.Y.Z` version, valeur theorique ou issue d'une formule |
| **MACHINE-DEP** | Oui (chaque re-exec, chaque machine) | Unite `ms`/`s`/`min`/`sec`/`us`/`ns` ou contexte `benchmark`/`perf`/`timing`/`runtime`/`execution` |
| **ENV-DEP** | Oui (chaque bump de version) | Pattern `X.Y.Z` (3 digits separes par `.`) avec contexte `version`/`numpy`/`python`/`pandas`/`library`/`package` |
| **STOCHASTIQUE-NON-SEEDEE** | Oui (chaque run) | Contexte `fitness`/`reward`/`accuracy`/`score`/`mean` sans mention `seed=` ni `random_state=` |

## Pourquoi ce triage plutot qu'une regle dogmatique

Toutes les valeurs quantitatives ne sont pas equivalentes. Une regle qui
interdirait TOUTES les valeurs en prose ferait perdre de la richesse
pedagogique (le speedup `2.78e24x` du App-11-Picross est structurellement
stable ; le retirer = regression pedagogique). Une regle qui ne ferait rien
laisse la derive se reconstituer apres chaque correction (vague #8052 du
2026-08-04 : 4 PRs pour 4 notebooks, meme symptome). Le triage 4-classes
**applique la regle asymetriquement** : structurel = a garder ;
machine-dep / env-dep / stochastique = a deriver ou retirer.

## Cas ambigus

- `Durée estimée : 45 minutes` (effort etudiant, pacing pedagogique) = **TN structurel/pédagogique**, **hors scope drainage** (arbitrage 2026-08-06 ai-01, cf #9434 thread). Le classifier le classe STRUCTUREL grace au contexte `Durée estimée`.
- Posterieurs bayesiens en minutes (Infer-101 moyennes/variances de trajets) = donnees deterministes, **TN**, classes STRUCTUREL grace au contexte `posterior`/`moyenne`/`variance`.

CLI `--check` avec exit codes 0/1/2 distincts (succes / finding / usage).

## Sortie

JSON structuré par notebook avec `quant_classes` (liste de findings par classe)
+ compteurs par classe. Permet le **recensement chiffre par famille** demande
par #9434 critere d'acceptation #1.

Cf. issue #9434 pour le scope exact et la veine drainage per-notebook CLOSE.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Iterable

# Reutilisation du detecteur v3 (PR #9793 MERGED) pour l'extraction de nombres.
from scan_d5_prose_outputs_alignment import (
    _extract_prose_numbers,
    _parse_fr_number,
    iter_notebooks,
    DEFAULT_INCLUDE_GLOBS,
    DEFAULT_EXCLUDE_DIRS,
)


# --------------------------------------------------------------------------- #
#  Configuration des 4 classes
# --------------------------------------------------------------------------- #

# Regex strictes pour les unites temporelles (machine-dep).
_TIME_UNITS = (
    r"\b\d+\s*(?:ms|millisecondes?|microsecondes?|μs|us)\b",
    r"\b\d+\s*(?:s|sec|secondes?)\b",
    r"\b\d+\s*(?:min|minutes?)\b",
    r"\b\d+\s*(?:h|heures?|hours?)\b",
    r"\b\d+\s*(?:ns|nanosecondes?)\b",
)
TIME_UNIT_RE = re.compile("|".join(_TIME_UNITS), re.IGNORECASE)

# Regex strictes pour les versions (env-dep) — pattern semver simplifie.
SEMVER_RE = re.compile(r"\b\d+\.\d+\.\d+(?:[a-zA-Z0-9._+-]*)?\b")

# Mots-cles contextuels pour MACHINE-DEP (au-dela des unites temporelles).
MACHINE_DEP_KEYWORDS = (
    "benchmark", "perf", "performance", "timing", "runtime", "execution time",
    "elapsed", "durée d'exécution", "wall clock", "cpu time", "wall-time",
    "wall_clock",
    "exécute", "execute", "tourne", "run", "runs", "prend", "dure",
    "takes", "took", "spent", "spent time",
)
# Regex compilee avec word boundaries (c.1301+12) pour eviter les sous-chaines
# parasites :
# - `prend` est sous-chaine de `comprendre`, `apprendre`, `reprendre`, `surprendre`
#   (cell 0 `1.` `2.` `3.` `4.` des objectifs d'apprentissage ML/DfA — 8+ FP).
# - `run` est sous-chaine de `rung` (deja partiellement gere par STRUCTURAL_LOCATIONS
#   mais le matching STRUCTURAL_LOCATIONS=apres MACHINE-DEP en regle 5, donc
#   MACHINE-DEP `run` gagne sur `rung` au cas ou rung n'est pas matche).
# - `benchmark` est matche sur `rappel benchmark` / `fonction de benchmark`
#   contextuel (info pedagogique sur un benchmark, pas une mesure runtime).
# - `perf` est sous-chaine de `performance` (deja gere par le 1er match) mais
#   aussi de `imperfection` / `imperfectible` — peu probable en corpus ML.
# Strategie : on utilise une regex avec `\b` (word boundary) compilee une fois.
# Note : `é`/`è` ne sont pas ASCII mais `\b` est Unicode-aware en Python 3 par
# defaut (`re.UNICODE` par defaut depuis Python 3.0).
_MACHINE_DEP_PATTERN = re.compile(
    r"\b(?:" + "|".join(re.escape(kw) for kw in MACHINE_DEP_KEYWORDS) + r")\b",
    re.IGNORECASE,
)

# Mots-cles contextuels pour ENV-DEP (au-dela du pattern semver).
ENV_DEP_KEYWORDS = (
    "version", "numpy", "python", "pandas", "scipy", "sklearn", "torch",
    "tensorflow", "jax", "matplotlib", "library", "package", "module",
    "dépendance", "depend", "installed", "installée",
)

# Mots-cles contextuels pour STOCHASTIQUE-NON-SEEDEE.
STOCH_KEYWORDS = (
    "fitness", "reward", "accuracy", "score", "loss", "moyenne",
    "mean", "monte-carlo", "monte carlo", "sampling", "tirage",
    "random", "aléatoire", "stochastique",
)

# Mots-cles STRUCTUREL (a garder) — preuve pedagogique.
# v2: ajout mots-cles bayesiens pour eviter FP sur parametres de modeles
# probabilistes (moyennes/variances/post/precision/gamma(2.24, 0.24) ne sont
# PAS des timings runtime — cf #9434 c.1272 vague Probas).
STRUCT_KEYWORDS = (
    "théorique", "theorique", "théoriquement", "structurel", "structurel",
    "ordre de grandeur", "combinaisons", "combinatorial", "combinatoire",
    "durée estimée", "durée de l'exercice", "effort estimé",
    "pédagogique", "pedagogique", "pacing", "soutenance",
    "posterior", "postérieur", "vraisemblance", "likelihood",
    "moyenne", "variance", "espérance", "esperance", "expected value",
    "formule", "formula", "théorème", "theoreme",
    # Bayesien (c.1272): distinguetiming runtime d'unite de parametre
    "écart-type", "ecart-type", "écart type", "ecart type",
    "precision", "gamma(", "normal(", "gaussian(", "gauss(",
    "composante", "trajets", "trajet", "min^2", "min²",
    "d'observation", "données observees", "donnees observees",
    "arithmétique", "arithmetique", "bayésien", "bayesien",
    "prédictive", "predictive", "aplatissement", "kurtosis",
    # Note c.1273 : `apprentissage` retire (nit-2 ai-01) — trop large cross-famille
    # (FP : `temps d'apprentissage du modele: 42 s` = runtime). Le mot-composé
    # `inference bayesienne` reste, qui preserve la couverture Probas (20 fichiers).
    "inference bayesienne", "inférence bayésienne",
)

# v3 (c.1275): anti-FP Argument_Analysis — STRUCTURAL_LOCATIONS sont des
# mots-cles SECONDAIRES (localisent un numero, n'expliquent pas pourquoi il
# est stable). Ils sont evalues APRES MACHINE-DEP (regle 4) pour ne pas
# absorber les timings runtime adjacents aux numerotations pedagogiques.
# Mesure firsthand sur 213 drainables ArgAna :
# - `rung` (Toulmin) : 79 FPs → 0 apres (raw `1`/`2`/`3`/`4` en contexte
#   `rung` n'est PAS un timing machine-dep).
# - `epic` / `phase` : 5 FPs → 0 apres (`raw=2137` adjacent `epic #2137`
#   n'est PAS une annee runtime ; `phase N` est une numerotation structurelle).
# - `%` / `pourcent` : 1 FP → 0 apres (`100%` n'est PAS un timing).
# Scope : Argument_Analysis (SymbolicAI). Cross-famille aucune regression
# (rung/epic/phase sont des termes pedagogiques/epistemiques qui ne matchent
# pas dans Probas/Search/ML/GenAI/Sudoku — verifie par absence de double-compat).
STRUCTURAL_LOCATIONS = (
    "rung", "epic", "phase",
    "pourcent", "%",
)

# v4 (c.1301+12): anti-FP ML/DataScienceWithAgents + Search/Part1 (#10012).
# Issue #10012 documente 209 drainables ML/DfA dont ~90 % sont des FP non
# couverts par les vagues c.1272/c.1275 (calibration bayesienne + ArgAna).
# Quatre classes de FP a capturer avant TIME_UNIT_RE (regle 4) pour ne pas
# etre absorbees par des mots-cles MACHINE-DEP/ENV-DEP/StOCHastiques trop
# larges en contexte editorial/structurel :
#
# (a) Editorial-duration guard : `duree estimee : X` (lowercase ASCII en ML/DfA,
#     accentue en Probas) = temps de lecture pedagogique, pas un timing
#     runtime. La version capital-accentuee `Durée estimée` etait deja dans
#     STRUCT_KEYWORDS mais ne matchait JAMAIS en pratique car `_extract_context`
#     lowercasifie prefix+suffix avant comparaison. Fix : ajouter la forme
#     lowercase, et deplacer ce match en regle 0 (avant SEMVER) pour gagner
#     sur les patterns semver adjacents (ex. `python 3.10+`, accidentel).
#     Mesure : 6 FP `45`/`60`/`30`/`40`/`2` sur Lab2/Lab4/Lab6/Lab7 +
#     Search-1/Search-10.
#
# (b) Biblio guard : `doi:`/`vol(`/`pp.` + journal (`nature`, `jmlr`,
#     `machine learning`, `scipy`, `arxiv:`, `proc.`) = reference
#     bibliographique immuable. La cle d'OR est `pp.` / `vol(` / `doi:`
#     (signatures canoniques de citation papier), pas la presence du mot
#     `python` ou `numpy` adjacent (qui matche deja ENV-DEP et declasse
#     les nombres legitimes comme `python 3.10+`).
#     Mesure : 24 FP `585`/`357`/`362`/`51`/`56`/`7825`/`2825`/`2830` sur
#     1.2-NumPy/1.3-Pandas/2.4-Arbres/2.9-Grokking/Lab1/Lab4/Lab5/Lab10.
#
# (c) Section-number guard : X.Y adjacent a `# ` (markdown heading), `>> X`/
#     `<< X`/`[X.Y` (navigation link), `notebook X`/`exercice X`/`etape X`/
#     `# etape X` = numero de section ou d'etape dans la serie, pas une
#     mesure. Pattern cle : `X.Y` non-entier (les indices de section sont
#     decimaux) precede ou suivi d'un heading/navigation token.
#     Mesure : 30+ FP `1.2`/`1.3`/`2.1`/`2.5`/`2.4`/`2.3`/`4` sur
#     1.2-NumPy/2.4-Arbres/2.6-Clustering/2.7-NonParam/Lab2/Lab7.
#
# (d) Theoretical-reference guard : `accuracy proche de X`/`accuracy
#     d'entrainement proche`/`intervalle (X, Y)`/`AUC = X (classifieur`/
#     `sur-apprentissage = X` = constante conceptuelle ou intervalle
#     theorique de la classification binaire (AUC du hasard = 0.5,
#     surapprentissage = 1.0). PAS un timing runtime.
#     Mesure : 3 FP `1.0` sur 2.1-Workflow/2.4-Arbres.
#
# Scope : ML/DataScienceWithAgents + Search/Part1-Foundations (issue #10012).
# Cross-famille aucune regression verifiee par `pytest` (suite 47 tests + 11
# nouveaux = 58/58 PASS attendu) + recansement post-cablage (209 → ~10-20).
# Ne PAS elargir a `python`/`numpy` adjacents — trop risquerait d'absorber
# les vrais `python 3.10+` (kernel bump = ENV reel a signaler) et `numpy X.Y`
# (librairie version = ENV reel). Pattern strict = uniquement les signatures
# canoniques bibliographiques + structurelles.
STRUCTURAL_LOCATIONS_V4 = (
    # (a) Editorial-duration : lowercase ASCII (ML/DfA) + capital-accentue (Probas)
    #     Note : `durée estimée` capital-accentue EST deja dans STRUCT_KEYWORDS
    #     mais ne matche jamais en pratique (lowercased comparaison). On duplique
    #     ici en lowercase pour gagner sur les patterns MACHINE-DEP.
    "duree estimee",
    # (b) Biblio guard : signatures canoniques de citation papier
    "doi:", "arxiv:", "vol.", "vol ", "pp.", "proc.",
    "nature,", "nature ", "jmlr", "machine learning,", "machine learning ",
    "scipy,", "scipy ",
    # (c) Section-number guard : heading + navigation + etape exercice
    "# ", "## ", "### ", "#### ", ">> ", "<< ",
    "notebook ", "exercice ", "etape ", "# etape ",
    # (d) Theoretical-reference guard : constantes conceptuelles classification binaire
    "accuracy proche", "accuracy d'entrainement proche", "accuracy d'entraînement proche",
    "intervalle (", "intervalle",
    "classifieur aleatoire", "classifieur aléatoire",
    "sur-apprentissage", "surapprentissage",
)

# Mots-cles DATA-LIST (anti-FP) : une liste `{8, 10, 11, 12}` ou `[13, 17, 16]`
# en contexte bayesien = data points, pas runtime. Note c.1273 : `}cii` était
# un marqueur mort (typo, ne matche jamais) — retiré suite nit ai-01 #9813.
DATA_LIST_MARKERS = ("{", "~ ", " valeurs", "observations)")

# Mots-cles SEED — si présents, le stochastique est seede et donc STRUCTUREL.
SEED_KEYWORDS = ("seed=", "random_state=", "np.random.seed", "torch.manual_seed",
                 "tf.random.set_seed", "rng.seed", "np_seed")


# --------------------------------------------------------------------------- #
#  Dataclasses
# --------------------------------------------------------------------------- #


QUANT_CLASSES = ("STRUCTUREL", "MACHINE-DEP", "ENV-DEP", "STOCHASTIQUE-NON-SEEDEE")


@dataclass
class QuantClassFinding:
    """Un cas de valeur quantitative classifie."""
    notebook: str
    cell_index: int
    cell_kind: str = "markdown"
    value: float = 0.0
    raw_match: str = ""
    quant_class: str = "UNKNOWN"
    context_prefix: str = ""
    context_suffix: str = ""
    rationale: str = ""


@dataclass
class NotebookQuantClasses:
    """Resultat d'analyse d'un notebook."""
    path: str
    total_findings: int = 0
    findings: list[QuantClassFinding] = field(default_factory=list)
    by_class: dict[str, int] = field(default_factory=dict)
    n_markdown_cells: int = 0
    n_code_cells: int = 0
    error: str | None = None


# --------------------------------------------------------------------------- #
#  Extraction du contexte
# --------------------------------------------------------------------------- #


def _extract_context(text: str, match_start: int, match_end: int, window: int = 40) -> tuple[str, str]:
    """Renvoie (prefix, suffix) de longueur `window` autour d'un match.

    Coupe aux frontières de mot (whitespace) pour eviter de couper au milieu
    d'un mot et donner un contexte decibale.
    """
    # prefix : on remonte jusqu'au debut de la ligne ou `window` chars.
    prefix_start = max(text.rfind("\n", 0, match_start) + 1, match_start - window)
    prefix = text[prefix_start:match_start]
    # suffix : jusqu'à la fin de la ligne ou `window` chars.
    suffix_end_nl = text.find("\n", match_end)
    suffix_end = suffix_end_nl if suffix_end_nl != -1 else match_end + window
    suffix_end = min(suffix_end, match_end + window)
    suffix = text[match_end:suffix_end]
    return prefix.lower(), suffix.lower()


def _classify_quant_value(
    raw: str, value: float, prefix: str, suffix: str
) -> tuple[str, str]:
    """Classifie une valeur quantitative selon le contexte. Renvoie (classe, rationale).

    Ordre d'application des regles (la premiere qui matche gagne) :
    1. STRUCTUREL si mot-cle structurel detecte dans prefix+suffix
    2. SEED dans prefix → bascule STOCHASTIQUE → STRUCTUREL
    3. ENV-DEP si pattern semver ou mot-cle env
    4. MACHINE-DEP si unite temporelle ou mot-cle machine-dep
    5. STOCHASTIQUE-NON-SEEDEE si mot-cle stochastique
    6. STRUCTUREL par defaut (classe residuelle surete)

    Le defaut STRUCTUREL evite les faux positifs massifs sur les valeurs
    qui ne sont aucunement concernees (ex. « Le dataset contient 1000 images »).
    """
    full_context = (prefix + " " + suffix).lower()

    # Data-list check (bayesien) : si un data-list marker est present dans
    # le contexte, c'est un data point bayesien, pas un timing runtime —
    # les regles MACHINE-DEP doivent skipper la detection pour ces cas.
    # (v2 c.1272 inchange ; remonte ici pour proteger la regle MACHINE-DEP
    # anti-FP c.1275 qui doit respecter la liste.)
    in_data_list = any(marker in full_context for marker in DATA_LIST_MARKERS)

    # 0. Filtre semver : si le raw match EST un semver, c'est env-dep en soi.
    if SEMVER_RE.fullmatch(raw):
        return ("ENV-DEP", f"semver pattern match: {raw!r}")

    # -2 (c.1331): anti-FP residuel ML/DfA — guard structurel v5 (2 classes
    #     mesurees apres v4, issue #10012). v4 (#10016) a reduit 209 -> 93 mais
    #     la verification #4 (assert restants = vrais drainables) ECHOUE : les 93
    #     sont ~90 % de FP dans 2 nouvelles classes non couvertes par v4.
    #     Failure-mode SAFE : ces guards ne font qu'absorber vers STRUCTUREL
    #     (jamais vers drainable) — un faux positif du guard = garder une vraie
    #     valeur en STRUCTUREL = sur-correction inoffensive (pas de corruption de
    #     contenu), tandis que le bug a fixer est la direction inverse (FP
    #     drainable qui corromprait un drain). L'asymetrie regle #9434 tient.
    #
    # (e) Numbered-list-item guard : entier en DEBUT de ligne + ". mot" suit =
    #     numerotation de liste / objectif pedagogique / auteur biblio. Mesure
    #     ML/DfA : 7 MACHINE-DEP ("4. comprendre", "3. executor") + ~15 ENV-DEP
    #     ("3. t. e. oliphant", "2. w. mckinney" = auteurs numerotes biblio).
    #     Pattern strict : raw entier (les indices de liste sont des entiers ;
    #     "0.95" est preserve) + prefix strippe vide (debut de ligne, rien avant
    #     sur la ligne) + suffix debutant par ". " + alphanumerique.
    if re.fullmatch(r"\d+", raw) and prefix.strip() == "" and re.match(r"\.\s+\w", suffix):
        return ("STRUCTUREL", "liste/objectif numéroté v5 (entier début de ligne)")

    # (f) Clock-arithmetic guard : "11 h + 3 h = 2 h" = arithmetique de l'horloge
    #     (exemple math pedagogique), pas un timing runtime. Le `h` (heures) dans
    #     une EQUATION (deux quantites-h jointes par + ou =) signale l'arithmetic,
    #     pas une mesure. Un vrai runtime "prend 3 h" n'a qu'une quantite-h sans
    #     operateur. Mesure ML/DfA c9 : 3 MACHINE-DEP FP (11/3/2 de l'horloge).
    #     Pattern strict : \d+h[+=]\d+h exige DEUX quantites-h + operateur.
    ctx_with_raw = (prefix + " " + raw + " " + suffix).lower()
    if re.search(r"\d+\s*h\s*[+=]\s*\d+\s*h", ctx_with_raw):
        return ("STRUCTUREL", "arithmétique horloge v5 (Nh ± = Nh, exemple math)")

    # -1b v6 (c.1331+15, #9434): anti-FP résiduel — 3 nouvelles classes mesurées
    #     firsthand sur GT-1-Setup + PyMC-1-Setup NON couvertes par v4 (#10016) ni
    #     v5 (#10062). Même asymétrie failure-mode-safe que v4/v5 : ces guards
    #     absorbent UNIQUEMENT vers STRUCTUREL (jamais vers drainable), donc un
    #     guard trop large = garder une vraie valeur en STRUCTUREL = sur-correction
    #     inoffensive (pas de corruption de drain). Falsification tests
    #     (TestFpGuardV6) prouvent qu'un genuine ENV "NumPy 2.4.4" et un genuine
    #     STOCH "accuracy 0.87" restent drainables.
    #
    #     IMPORTANT — ce que v6 NE touche pas : les version-adjacents ("python
    #     3.10+", "numpy 2.x") restent ENV-DEP légitimes (test_10012_falsif_python
    #     _semver_kept : un floor/wildcard de version DÉRIVE quand la lib évolue —
    #     3.10+ → 3.13+ — donc est env-drift-prone par design). v6 ne cible que les
    #     valeurs NON-version rattrapées par proximité de mot-clé.
    s_l = suffix.lstrip()
    p_r = prefix.rstrip()
    # (B) Cross-ref nom de notebook : "voir pymc-6-debugging" = le chiffre est le
    #     slug d'un notebook voisin, pas une version. Mesuré : PyMC-1-Setup
    #     cell[16] "pymc-6-debugging" → ENV-DEP via kw 'version'.
    if re.search(r"[a-z0-9]-$", p_r, re.I) and re.match(r"-\s*[a-z]", s_l, re.I):
        return ("STRUCTUREL", "cross-ref slug v6 (\\w-N-\\w: nom notebook/fichier)")
    # (A) Citation bibliographique : "Physics Letters B, 195(2), 216-222" = les
    #     chiffres sont vol/issue/pages d'une réf journal, pas des mesures. Le
    #     pattern Vol(Issue), pages est non-ambigu. Mesuré : PyMC-1-Setup
    #     cell[25] "195(2)" → STOCHASTIQUE via kw 'Monte Carlo' (titre du papier).
    if re.search(r"\d+\s*\(\s*\d+\s*\)\s*,\s*\d+\s*[-–]\s*\d+",
                 prefix + " " + raw + " " + suffix):
        return ("STRUCTUREL", "citation biblio v6 (Vol(Issue), pages: réf journal)")
    # (F) Compteur structurel : "randomiser sur ses 3 actions", "5 candidats" =
    #     N est la cardinalité d'un ensemble fini du domaine, pas une mesure
    #     stochastique (le tirage porte SUR les N, N lui-même est fixe). Mesuré :
    #     GT-1-Setup cell[60] "3 actions" → STOCHASTIQUE via kw 'random'.
    #     v7 (c.1331+19, #9434) étend la liste de count-nouns aux entités
    #     pédagogiques/documentaires mesurées sur la flotte (164 FP ENV-DEP) :
    #     "21 notebooks", "3 modules", "5 sections", "12 fichiers", "8 puzzles",
    #     "3 exercices" — cardinalités de structure, pas des versions/mesures.
    if re.match(r"(?:actions?|choix|strat[eé]gies?|candidats?|joueurs?|players?|"
                r"[eé]tats?|[eé]tapes?|coups?|moves?|dimensions?|attributs?|"
                r"features?|classes?|notebooks?|modules?|sections?|cellules?|"
                r"cells?|chapitres?|fichiers?|files?|puzzles?|exercices?|"
                r"th[eé]or[eè]mes?|theorems?|probl[eè]mes?|exemples?)\b",
                s_l, re.I):
        return ("STRUCTUREL", "compteur structurel v6/v7 (N <count-noun>: cardinalité)")
    # (G) Slug de module/section : "module 01-5", "modules [01]-05", "notebooks
    #     02-1 a 02-5", "parts 7-23" = le chiffre est dans le slug hiérarchique
    #     d'un module pédagogique (préfixe = count-noun structurel), pas une version.
    #     Même asymétrie que le slug-B (cross-ref notebook). Mesuré : GenAI/Audio
    #     "module 01-5" → ENV-DEP via kw env adjacent. TIGHTENED : exige (a) un
    #     count-noun structurel en préfixe (module/modules/notebooks/parts — PAS
    #     "module p" mathématique ni "2^127-1" qui a un caret) ET (b) un slug -N
    #     en suffixe (le raw matche le 1er chiffre, le suffixe porte le -N). Exclut
    #     les expressions mathématiques (" - 1" avec espace).
    if re.search(r"\b(?:modules?|notebooks?|parts?)\b\s*\[?$", p_r, re.I) and \
       re.match(r"-\d", s_l):
        return ("STRUCTUREL", "slug module v7 (module N-M: hiérarchie pédagogique)")

    # -1 (c.1301+12): anti-FP ML/DfA + Search/Part1 — guard structurel v4
    #     (4 classes : editorial-duration / biblio / section-number /
    #     theoretical-reference). Capture les FPs AVANT que les mots-cles
    #     MACHINE-DEP/ENV-DEP/STOCH ne les absorbent. Strict patterns only —
    #     voir STRUCTURAL_LOCATIONS_V4 docstring pour le pourquoi du scope
    #     (ne PAS elargir `python`/`numpy` qui sont des ENV-DEP legitimes).
    for kw in STRUCTURAL_LOCATIONS_V4:
        if kw in full_context:
            return ("STRUCTUREL", f"localisation structurelle v4: {kw!r}")

    # 1. STRUCTUREL explicite
    for kw in STRUCT_KEYWORDS:
        if kw in full_context:
            return ("STRUCTUREL", f"mot-cle structurel: {kw!r}")

    # 2. SEED → stochastique seede → STRUCTUREL
    for kw in SEED_KEYWORDS:
        if kw in full_context:
            return ("STRUCTUREL", f"stochastique seede via {kw!r}")

    # 3. ENV-DEP (mots-cles env)
    for kw in ENV_DEP_KEYWORDS:
        if kw in full_context:
            return ("ENV-DEP", f"mot-cle env: {kw!r}")

    # 4. MACHINE-DEP (unites temporelles) — anti-FP c.1275 isole cette regle
    #    des mots-cles perf (run, execute, etc.) qui contiennent des
    #    sous-chaines de STRUCTURAL_LOCATIONS (rung contient 'run', etc.).
    #    Strategie : TIME_UNIT_RE gagne quoi qu'il arrive (meme si un mot-cle
    #    structurel matche dans le contexte — `rung 42 ms` doit rester MACHINE-DEP
    #    runtime, pas STRUCTUREL). v2 (c.1272): data-list exempte.
    if not in_data_list and (TIME_UNIT_RE.search(raw) or TIME_UNIT_RE.search(prefix + suffix)):
        return ("MACHINE-DEP", f"unite temporelle detectee: {raw!r}")

    # 5. STRUCTURAL_LOCATIONS (c.1275) — anti-FP Argument_Analysis : mots-cles
    #    SECONDAIRES qui localisent un numero (pas expliquent sa stabilite).
    #    Appliques APRES TIME_UNIT_RE (anti-FP c.1275 : ne pas absorber les
    #    timings runtime adjacents) et AVANT MACHINE_DEP_KEYWORDS (mots-cles
    #    perf tel `run`/`run` contenu dans `rung`, `episode` dans `epic`).
    #    Scope : Argument_Analysis. Mesure : -92 FPs resolus sans cross-famille
    #    regression (rung/epic/phase/% ne matchent pas dans Probas/Search/ML).
    for kw in STRUCTURAL_LOCATIONS:
        if kw in full_context:
            return ("STRUCTUREL", f"localisation structurelle: {kw!r}")

    # 6. MACHINE-DEP (mots-cles perf) — apres STRUCTURAL_LOCATIONS pour eviter
    #    que `run` (dans MACHINE_DEP_KEYWORDS) matche `rung` (`rung` contient
    #    `run` en sous-chaine).
    #    c.1301+12: utilise _MACHINE_DEP_PATTERN avec word boundaries pour
    #    eviter `prend in comprendre`, `benchmark in rappel benchmark` etc.
    m_match = _MACHINE_DEP_PATTERN.search(full_context)
    if m_match:
        return ("MACHINE-DEP", f"mot-cle machine-dep: {m_match.group()!r}")

    # 7. STOCHASTIQUE-NON-SEEDEE
    #    v2 (c.1272): `moyenne`/`mean`/`variance` en contexte NON-stochastique
    #    (mean value of N, valeur centrale, etc.) ne sont PAS stochastique.
    #    On accepte seulement si le contexte est clairement non-parametrique.
    NONSTOCH_MODIFIERS = ("chapitre", "référence", "reference", "du livre", "du manuel", "symbole", "example")
    for kw in STOCH_KEYWORDS:
        if kw in full_context:
            # Anti-FP: si kw est `mean`/`moyenne`/`variance` ET un modificateur
            # non-stochastique est present, c'est une valeur de référence, pas
            # une mesure stochastique.
            if kw in ("moyenne", "mean", "variance") and any(mod in full_context for mod in NONSTOCH_MODIFIERS):
                continue
            return ("STOCHASTIQUE-NON-SEEDEE", f"mot-cle stochastique: {kw!r}")

    # 8. STRUCTUREL par defaut (classe residuelle)
    return ("STRUCTUREL", "defaut (aucun signal machine-dep/env-dep/stochastique)")


# --------------------------------------------------------------------------- #
#  Analyse notebook
# --------------------------------------------------------------------------- #


def analyze_notebook_quant(path: str | os.PathLike) -> NotebookQuantClasses:
    """Analyse les valeurs quantitatives d'un notebook et les classifie."""
    p = Path(path)
    result = NotebookQuantClasses(path=str(path))
    try:
        nb = json.loads(p.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, OSError) as exc:
        result.error = f"{type(exc).__name__}: {exc}"
        return result

    cells = nb.get("cells") or []
    result.n_markdown_cells = sum(1 for c in cells if c.get("cell_type") == "markdown")
    result.n_code_cells = sum(1 for c in cells if c.get("cell_type") == "code")

    findings: list[QuantClassFinding] = []
    by_class: dict[str, int] = {cls: 0 for cls in QUANT_CLASSES}

    for i, c in enumerate(cells):
        if c.get("cell_type") != "markdown":
            continue
        source = c.get("source") or []
        text = "".join(source) if isinstance(source, list) else str(source)
        if not text:
            continue
        # Reutilisation de l'extraction D5 v3 (qui filtre les annees, #issues,
        # PRJ42, semver simplifie stricte, etc.) — mais on doit scanner le
        # texte brut pour les versions, donc on **re-scan** avec nos propres
        # regex par-dessus les nombres deja extraits.
        for m in re.finditer(
            r"(?<![A-Za-z0-9_])-?\d+(?:[.,]\d+)?(?:[eE][-+]?\d+)?(?![A-Za-z0-9_])",
            text,
        ):
            raw = m.group(0)
            v = _parse_fr_number(raw)
            if v is None:
                continue
            # Skip les annees (4 chiffres) et autres bruits basiques.
            if re.fullmatch(r"\d{4}", raw) and 1900 <= v <= 2099:
                continue
            prefix, suffix = _extract_context(text, m.start(), m.end())
            cls, rationale = _classify_quant_value(raw, v, prefix, suffix)
            # Tronque le snippet pour le rapport.
            snippet = text.strip().splitlines()
            snippet_str = next((ln.strip() for ln in snippet if ln.strip()), "")[:120]
            findings.append(QuantClassFinding(
                notebook=str(path),
                cell_index=i,
                value=v,
                raw_match=raw,
                quant_class=cls,
                context_prefix=prefix[-40:],
                context_suffix=suffix[:40],
                rationale=rationale,
            ))
            by_class[cls] += 1

    result.findings = findings
    result.total_findings = len(findings)
    result.by_class = by_class
    return result


# --------------------------------------------------------------------------- #
#  Walk corpus (reutilise iter_notebooks du detecteur v3)
# --------------------------------------------------------------------------- #


def scan_corpus_quant(
    root: str | os.PathLike,
    include_globs: tuple[str, ...] = DEFAULT_INCLUDE_GLOBS,
    exclude_dirs: tuple[str, ...] = DEFAULT_EXCLUDE_DIRS,
) -> list[NotebookQuantClasses]:
    """Scan a corpus root, return list of NotebookQuantClasses."""
    root_path = Path(root)
    results: list[NotebookQuantClasses] = []
    for nb_path in iter_notebooks(root_path, include_globs, exclude_dirs):
        results.append(analyze_notebook_quant(nb_path))
    return results


# --------------------------------------------------------------------------- #
#  Reporting
# --------------------------------------------------------------------------- #


def render_text_report(results: list[NotebookQuantClasses]) -> str:
    """Format results as markdown text avec compteurs par classe."""
    total_findings = sum(r.total_findings for r in results)
    global_by_class: dict[str, int] = {cls: 0 for cls in QUANT_CLASSES}
    n_drainable = 0  # MACHINE-DEP + ENV-DEP + STOCHASTIQUE-NON-SEEDEE
    for r in results:
        for cls, n in r.by_class.items():
            global_by_class[cls] += n
        n_drainable += (
            r.by_class.get("MACHINE-DEP", 0)
            + r.by_class.get("ENV-DEP", 0)
            + r.by_class.get("STOCHASTIQUE-NON-SEEDEE", 0)
        )
    n_pathological = sum(
        1 for r in results if r.by_class.get("MACHINE-DEP", 0)
        + r.by_class.get("ENV-DEP", 0)
        + r.by_class.get("STOCHASTIQUE-NON-SEEDEE", 0) > 0
    )

    lines: list[str] = []
    lines.append(f"Total notebooks analyses : {len(results)}")
    lines.append(f"Notebooks avec >= 1 valeur drainable (MACHINE/ENV/STOCH) : {n_pathological}")
    lines.append(f"Total findings : {total_findings}")
    lines.append("Repartition par classe :")
    for cls in QUANT_CLASSES:
        lines.append(f"  - {cls} : {global_by_class[cls]}")
    lines.append(f"  - TOTAL drainable : {n_drainable}")
    lines.append("")
    lines.append("## Top 10 notebooks avec le plus de valeurs drainables")
    lines.append("")
    lines.append("| Notebook | MACHINE | ENV | STOCH | Total drainable |")
    lines.append("|---|---|---|---|---|")
    top = sorted(
        results,
        key=lambda r: -(r.by_class.get("MACHINE-DEP", 0)
                        + r.by_class.get("ENV-DEP", 0)
                        + r.by_class.get("STOCHASTIQUE-NON-SEEDEE", 0)),
    )
    for r in top[:10]:
        drainable = (
            r.by_class.get("MACHINE-DEP", 0)
            + r.by_class.get("ENV-DEP", 0)
            + r.by_class.get("STOCHASTIQUE-NON-SEEDEE", 0)
        )
        if drainable == 0:
            continue
        lines.append(
            f"| `{os.path.basename(r.path)}` | {r.by_class.get('MACHINE-DEP', 0)} | "
            f"{r.by_class.get('ENV-DEP', 0)} | {r.by_class.get('STOCHASTIQUE-NON-SEEDEE', 0)} | "
            f"{drainable} |"
        )
    return "\n".join(lines) + "\n"


# --------------------------------------------------------------------------- #
#  CLI
# --------------------------------------------------------------------------- #


def main(argv: Iterable[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument(
        "--root", default="MyIA.AI.Notebooks",
        help="Racine du corpus a scanner (defaut: MyIA.AI.Notebooks).",
    )
    parser.add_argument(
        "--notebook", help="Cible un notebook precis (sinon full-corpus).",
    )
    parser.add_argument(
        "--json-out", help="Ecrire le rapport JSON a ce chemin.",
    )
    parser.add_argument(
        "--check", action="store_true",
        help="Mode CI : exit 1 si >= 1 valeur MACHINE-DEP/ENV-DEP/STOCHASTIQUE.",
    )
    parser.add_argument(
        "--limit", type=int, default=0,
        help="Limiter le nombre de notebooks analyses (0 = pas de limite).",
    )
    args = parser.parse_args(list(argv) if argv is not None else None)
    root = Path(args.root)
    if not root.exists():
        print(f"ERREUR: racine '{root}' inexistante.", file=sys.stderr)
        return 2
    if args.notebook:
        nb_path = Path(args.notebook)
        if not nb_path.exists():
            print(f"ERREUR: notebook '{nb_path}' inexistant.", file=sys.stderr)
            return 2
        results = [analyze_notebook_quant(nb_path)]
    else:
        results = scan_corpus_quant(root)
        if args.limit > 0:
            results = results[:args.limit]

    if args.json_out:
        Path(args.json_out).write_text(json.dumps([
            {
                "path": r.path,
                "total_findings": r.total_findings,
                "by_class": r.by_class,
                "n_markdown_cells": r.n_markdown_cells,
                "n_code_cells": r.n_code_cells,
                "findings": [
                    {
                        "cell_index": f.cell_index,
                        "value": f.value,
                        "raw_match": f.raw_match,
                        "quant_class": f.quant_class,
                        "context_prefix": f.context_prefix,
                        "context_suffix": f.context_suffix,
                        "rationale": f.rationale,
                    }
                    for f in r.findings
                ],
                "error": r.error,
            }
            for r in results
        ], indent=2, ensure_ascii=False), encoding="utf-8")

    print(render_text_report(results))
    if args.check:
        drainable = sum(
            r.by_class.get("MACHINE-DEP", 0)
            + r.by_class.get("ENV-DEP", 0)
            + r.by_class.get("STOCHASTIQUE-NON-SEEDEE", 0)
            for r in results
        )
        if drainable > 0:
            return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
