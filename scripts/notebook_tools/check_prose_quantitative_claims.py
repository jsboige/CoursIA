"""Refuse les compteurs quantitatifs ecrits a la main dans la prose.

Mandat user 2026-08-04 : « les donnees quantitatives doivent etre tenues par le
CI, pas dans la prose manuelle ». Registre : issue #9377 (compteurs d'artefacts
du depot) ET issue #9434 (mesures non reproductibles : machine/env/stochastique).

Le catalogue genere (`COURSE_CATALOG.generated.*` + marqueurs `CATALOG-STATUS`)
a ete mis en place parce que les agents ouvraient des PR sans fin pour
resynchroniser des decomptes de notebooks. Le genre n'a pas disparu : il a
migre vers la prose, ou aucun generateur ne l'atteint. 11 PR de resynchro
mergees en 3 semaines au 2026-08-04, dont une (#9153) dont le titre avoue
« re-drift post #6914 ».

Le tri est celui de l'issue : **calcule = legitime, prose = interdit**.

  - Une cellule *code* qui compte et affiche est la bonne facon de porter un
    chiffre : il se recalcule a chaque execution. On ne la regarde pas --
    ni ses sorties, ni son code source (docstrings et commentaires compris :
    « forward 1 ligne » decrit un appel, « negligeables sur 1 ligne » une
    empreinte memoire ; aucun des deux n'est une mesure figee, #22564 D3).
  - Une cellule *markdown* qui affirme « (140 lignes) » fige une mesure que
    rien ne remesure. Elle derive des qu'un tiers touche au fichier cite --
    y compris pour une raison sans rapport (sur game_theory_lean, 4 des 6
    commits de juillet sont des flips de docstrings FR/EN, qui changent le
    nombre de lignes sans toucher une ligne de mathematiques).

Ce qui reste autorise : les predicats (`0 sorry` dit que la preuve est
complete), et tout nombre qui n'est pas une mesure d'artefact du depot.

Angle mort connu -- mesure VIVANTE vs mesure FIGEE
--------------------------------------------------
Le scanner voit la forme (« N lignes »), pas le temps du recit. Il flague donc
aussi les chiffres qui datent d'un incident **clos**, ou le nombre decrit un
fait passe et ne peut plus deriver : personne n'ouvrira de PR pour
resynchroniser une mesure d'evenement. Exemple rencontre a la mise en service
(`variation-protocol-detail.md`) : « ~98 lignes redigees trois fois » chiffre
le doublon #8961/#8983/#8996 du 2026-07-31 -- c'est la PIECE qui fonde le
verdict, pas un compteur a tenir.

La ligne de partage : un decompte d'**artefact vivant** derive et revient au
CI ; un decompte **fige dans un recit au passe** est une preuve, et se garde.
D'ou le mode advisory par defaut -- l'arbitrage est humain. Ne PAS « corriger »
un chiffre d'incident au motif que le guard l'a signale : ce serait supprimer
la preuve pour faire taire l'organe.

Taxonomie #9434 -- quatre classes de mesures non reproductibles
---------------------------------------------------------------
Le scanner couvre desormais, en plus du compteur d'artefacts #9377, les quatre
classes de l'EPIC #9434 (mesures que la prose ne devrait pas figer parce qu'elles
ne se recalculent pas a l'execution) :

  - ``artifact``   (defaut, #9377) : nombre colle a un artefact du depot
                    (« 140 lignes », « 224 notebooks »). Derive a chaque commit.
  - ``machine``    (#9434) : duree absolue machine-dependante (« 24-127 ms »,
                    « ~530 ms », « 1.9 s »). Derive avec la charge machine.
  - ``env``        (#9434) : version de librairie / ecosystem / interprete
                    figee en prose (« NumPy 2.4.2 », « Python 3.13.3 », ligne
                    de tableau « | numpy | 2.2.6 | »). Derive quand
                    l'environnement monte de version -- doit etre tenu par le
                    fichier d'environnement (toolchain, requirements), pas la prose.
  - ``stochastic`` (#9434) : valeur a flotant non reproductible (« fitness 41.71 »)
                    quand le carnet ne seme pas (pas de seed amont). Derive a
                    chaque execution.
  - ``structural`` (#9434) : ordre de grandeur d'un speedup determine par la
                    taille du probleme (« 2.78e24x », « 4x »). **LEGITIME en
                    prose** : deterministe, ne derive pas. Explicitement EXCLU
                    du signalement -- il faut le demander explicitement
                    (``--class structural``) pour le voir inventorier, et il
                    ne fait jamais echouer.

Exemption ligne-complet (arbitrage jsboige 14:05:37Z sur #9434) : un
« (Durée|Duree) (estimée|estimee) : X minutes » dans une cellule markdown
reflete l'effort demande a l'etudiant (pacing pedagogique), pas une mesure
machine. Le mot-cle bascule la ligne entiere en TN pour la classe ``machine``
(cf STUDENT_PACING_RE). Les autres classes (artifact/env/stochastic) restent
actives : un « ~50 minutes » colle a un autre artefact reste flague. Les
vraies wall-clock measures (sans le mot-cle pacing) restent capturees.

La classe par defaut reste ``artifact`` : le contrat CI
(``prose-counts-guard.yml`` appelle ``--diff`` sans ``--class``) est preserve
exact. Les classes #9434 s'auditent en opt-in, pour poser le before/after d'un
drainage par classe.

Certaines occurrences sont des faux positifs de SENS, pas des mesures d'etat :
« 36 cellules vivantes » d'un canon du Jeu de la Vie compte des cellules de
l'automate, et « 248 818 lignes » d'un depot externe pine mesure un run, pas un
compteur du depot. Les supprimer n'aurait pas de sens, et les laisser flaguer
fait re-trancher le meme arbitrage a chaque tranche. Elles sont couvertes par
une allowlist ``(fichier, motif)`` -- ``ARTIFACT_EXEMPTIONS`` -- ou chaque
entree porte son motif ECRIT, et dont le motif ne couvre que son propre span
sur la ligne. Une entree qui ne couvre plus rien est signalee
``[ALLOWLIST-PERIMEE]`` en ``--all`` : une exemption se perime en silence si
rien ne la relit (#23111).

Usage
-----
    # CI sur une PR : ne juge que les lignes AJOUTEES (classe artifact, defaut)
    python check_prose_quantitative_claims.py --diff origin/main...HEAD

    # Inventaire du stock #9377 restant
    python check_prose_quantitative_claims.py --all

    # Inventaire d'une classe #9434 (drainage)
    python check_prose_quantitative_claims.py --all --class machine
    python check_prose_quantitative_claims.py --all --class env
    python check_prose_quantitative_claims.py --all --class stochastic
    python check_prose_quantitative_claims.py --all --class structural  # legitime, rc=0

    # Toutes les classes flaggables (artifact + machine + env + stochastic)
    python check_prose_quantitative_claims.py --all --class all

    # Bloquant -- contrat CI actif depuis #17636 (seules les lignes AJOUTEES
    # sont jugees : le stock #9377 ne fait echouer aucune PR)
    python check_prose_quantitative_claims.py --diff origin/main...HEAD --strict
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import NamedTuple

# ----------------------------------------------------------------------------
# Classe « artifact » (#9377) -- compteurs d'artefacts du depot
# ----------------------------------------------------------------------------
# Noms d'artefacts du depot. Un nombre colle a l'un d'eux est une mesure d'etat
# du depot, donc perissable. Volontairement restreint : « 4 proprietes de Nash »
# ou « 3 joueurs » sont du contenu pedagogique, pas de l'etat de depot, et ne
# doivent jamais declencher.
ARTIFACT_NOUNS = r"(?:lignes?|lines?|cellules?|cells?|notebooks?|modules?|fichiers?|files?)"

# Formes attrapees : « (140 lignes) », « ~525 lignes », « **224** notebooks »,
# « 87 cellules ». Le nombre doit preceder immediatement le nom d'artefact.
#
# Note fix (#9434 angle-mort t2) : le lookbehind exclut aussi « # » -- un nombre
# precedent immediatement un diese est une reference (issue/PR GitHub « #5101 »,
# couleur hex « #333333 », ancre/titre markdown), jamais une mesure d'artefact.
COUNT_RE = re.compile(
    r"(?<![\w.#])~?\*{0,2}\d{1,6}\*{0,2}\s+" + ARTIFACT_NOUNS + r"(?![\w-])",
    re.IGNORECASE,
)

# ----------------------------------------------------------------------------
# Allowlist MOTIVEE de la classe « artifact » (#23111)
# ----------------------------------------------------------------------------
# Un compte peut etre un faux positif de SENS et non une mesure d'etat : « 36
# cellules vivantes » d'un canon du Jeu de la Vie compte les cellules de
# l'automate, pas celles d'un carnet ; « 248 818 lignes » d'un depot externe
# pine mesure un run, il ne derive pas avec CE depot. Supprimer le nombre
# n'aurait alors aucun sens -- il faudrait reecrire le propos -- et le laisser
# flaguer fait re-trancher le meme arbitrage a chaque tranche.
#
# Trois proprietes rendent l'exemption auditable plutot que commode :
#
# 1. Elle est un TRIO (chemin exact, motif de ligne, raison ECRITE). Pas de
#    glob : une exemption large se perime en silence.
# 2. Le motif ne couvre que les compteurs dont le span tombe DANS un de ses
#    matches. Un « 87 cellules » sur la meme ligne reste flague, et un compte
#    de cellules de carnet ajoute ailleurs dans le meme fichier aussi.
# 3. Le motif est ETROIT : il nomme le contexte, pas seulement le nombre. S'il
#    cesse de matcher apres une reecriture, l'occurrence est re-signalee et un
#    humain re-tranche -- le sens contraire (motif large qui avale en silence
#    un vrai compteur ajoute plus tard) est le seul vrai danger.
#
# L'allowlist est relue a chaque ``--all`` : ce qu'elle couvre est restitue,
# et une entree qui ne couvre plus rien est nommee PERIMEE.


class ArtifactExemption(NamedTuple):
    """Une exemption motivee de la classe ``artifact``."""

    path: str                  # chemin relatif POSIX exact, jamais un glob
    motif: re.Pattern[str]     # motif de LIGNE ; couvre les compteurs dans son span
    raison: str                # pourquoi ce nombre n'est pas un etat du depot


ARTIFACT_EXEMPTIONS: tuple[ArtifactExemption, ...] = (
    ArtifactExemption(
        path="MyIA.AI.Notebooks/SymbolicAI/Lean/conway_lean/README.md",
        motif=re.compile(r"Gosper Glider Gun \(36 cellules vivantes"),
        raison=(
            "« 36 cellules » = cellules VIVANTES du canon de Gosper dans le Jeu "
            "de la Vie, pas des cellules de carnet. Le nombre est une propriete "
            "du motif (il definit le canon), il ne derive pas avec le depot."
        ),
    ),
    ArtifactExemption(
        path="MyIA.AI.Notebooks/SymbolicAI/Lean/conway_lean/README.md",
        motif=re.compile(r"Pulsar \(48 cellules\)"),
        raison=(
            "« 48 cellules » = periode-3 Pulsar du Jeu de la Vie, cite comme cas "
            "a la limite de native_decide ; ce sont des cellules de l'automate."
        ),
    ),
    ArtifactExemption(
        path="MyIA.AI.Notebooks/SymbolicAI/Lean/conway_lean/README.en.md",
        motif=re.compile(r"Pulsar \(48 cells\)"),
        raison=(
            "Sibling anglais du README precedent : meme Pulsar, memes cellules de "
            "l'automate. Une paire FR/EN se traite ensemble, sinon le drainage "
            "rouvre le meme arbitrage sur l'autre langue."
        ),
    ),
    ArtifactExemption(
        path="MyIA.AI.Notebooks/SymbolicAI/Lean/README.md",
        motif=re.compile(r"248 818 lignes compil"),
        raison=(
            "Mesure d'un run de reproduction sur le depot externe pine "
            "plby/HopfProblem : ce ne sont pas les lignes de CE depot, et le "
            "nombre decrit le resultat du run (248 818 lignes compilees en "
            "1154 s), pas un etat de CoursIA qui derive a chaque ajout."
        ),
    ),
)

# ----------------------------------------------------------------------------
# Classe « machine » (#9434) -- durees absolues machine-dependantes
# ----------------------------------------------------------------------------
# Formes attrapees : « 24-127 ms », « ~144 ms », « 0.006 ms », « ~1.9 sec »,
# « 0.2 s », « 2 min ». Unite monolettre « s » (secondes) exige un espace
# avant elle pour eviter les collisions (suffixes, abreviations) ; les unites
# multilettres (ms/sec/min/...) tolerent un espace optionnel. Advisory : un FP
# residuel est acceptable, l'arbitrage est humain (cf angle-mort header).
#
# Note fix (#9434 angle-mort t2, incident ICT-21) : le lookbehind exclut « # »
# -- sinon un numero d'issue « #5101 s'en dérive » (cell26 ICT-21) etait matche
# comme la duree « 5101 s ». Idem pour toute reference « #NNNN » suivie d'un mot
# en s-/m-/ms/sec/min (144 occurrences repertoriees : issues, couleurs hex).
# Une vraie mesure « ~50 s » (precedee de ~, pas de #) reste capturee.
#
# Note fix (#9434 angle-mort t3) : le lookahead final exclut aussi les
# apostrophes (' et '). Sinon « s » (secondes) collidait avec le debut d'un
# verbe reflechi francais : « les annees 80 s'ecoulent », « 3 s'appliquent »
# etaient matches comme les durees « 80 s », « 3 s ». Une mesure reelle n'est
# JAMAIS suivie immediatement d'une apostrophe (toujours espace/fin/ponctuation) ;
# un « s' » est le debut de s'en/s'applique/s'etend, pas l'unite secondes. Les
# vraies mesures (« ~50 s sur GPU », « 12 s ») restent capturees.
MACHINE_RE = re.compile(
    r"(?<![\w.#])~?\d{1,6}(?:[.,]\d{1,3})?"
    r"(?:"
    r"\s?(?:ms|millisecondes?|sec(?:ondes?)?|min(?:utes?)?)"
    r"|\ss"
    r")"
    r"(?![\w\-'’-])",
    re.IGNORECASE,
)

# ----------------------------------------------------------------------------
# Classe « env » (#9434) -- versions de librairie / ecosystem / interprete
# ----------------------------------------------------------------------------
# Formes attrapees : « NumPy 2.4.2 », « JAX 0.4 », « Mathlib v4.31.0-rc1 »,
# « PyTorch 2.1.0 ». Une version en prose derive quand l'env monte ; elle doit
# etre portee par le fichier d'environnement (lean-toolchain, requirements,
# .csproj), pas par la prose. Liste curee des libs presentes dans le depot,
# interprete « Python » compris : sa version est une mesure env au meme titre.
#
# Note fix (#14314) : le separateur nom/version ne se limite plus a l'espace
# simple. Le critere 2 de #9434 (tableaux de regression env) presente la forme
# « | numpy | 2.2.6 | » : nom et version separes par « | », spans code
# « `numpy` `2.2.6` » compris (le nom ET la version peuvent etre trenchés).
# Le separateur tolere tout melange espace/pipeline/backtick -- c'est la forme
# reelle d'une ligne de tableau markdown. Un FP residuel (ligne de statistiques
# « | numpy | 2.2.6 | 0.1 | » voisine) est advisory, l'arbitrage est humain.
# Garde anti-FP (le mot le plus courant de la liste) : « X.Y (fois|×) » est un
# multiplicateur, pas une version citee -- « Python 2.5 fois plus rapide » ne
# doit pas matcher comme version d'interpreteur.
ENV_LIBS = (
    r"NumPy|Pandas|PyTorch|TensorFlow|Keras|scikit-learn|sklearn|SciPy|"
    r"Transformers|LangChain|spaCy|OpenCV|cv2|Matplotlib|Seaborn|NetworkX|"
    r"SymPy|PyMC|ArviZ|Statsmodels|XGBoost|LightGBM|ONNX|vLLM|fastembed|"
    r"jpype|Tweety|OpenSpiel|SemanticKernel|Mathlib|JAX|PyPhi|pyphi|Python"
)
ENV_RE = re.compile(
    r"\b(?:" + ENV_LIBS + r")[|`\s]+v?\d+(?:\.\d+){1,3}(?!\s*(?:fois\b|×))\b",
    re.IGNORECASE,
)

# ----------------------------------------------------------------------------
# Classe « stochastic » (#9434) -- valeurs non reproductibles sans seed
# ----------------------------------------------------------------------------
# Une mesure a virgule (>=2 decimales, signature d'un resultat numerique) co-
# occurrent avec un mot-clef de metrique stochastique sur la meme ligne. Pour
# un .ipynb, on n'accepte le signalement QUE si le carnet ne seme pas (aucun
# seed amont) ; un carnet seme est reproductible, le chiffre est legitime. Pour
# un .md isole (pas de cellule code amont a verifier), on signale en advisory
# en documentant l'incertitude. Heuristique conservatrice : un carnet avec un
# seed n'importe ou est suppose reproductible.
STOCHASTIC_KW_RE = re.compile(
    r"\b(?:fitness|accuracy|pr[eé]cision|score|scores|loss|perte|pertes|"
    r"rendement|f1|wer|bleu|entropy|entropie|exactitude|rappel|recall|"
    r"auc|roc|moyenne|moyen)\b",
    re.IGNORECASE,
)
STOCHASTIC_NUM_RE = re.compile(r"(?<![\w.#])~?\*{0,2}\d{1,6}\.\d{2,}\*{0,2}(?![\w])")
SEED_RE = re.compile(
    r"(?:np\.random\.seed|numpy\.random\.seed|random\.seed|"
    r"torch\.manual_seed|tf\.random\.set_seed|jax\.random\.PRNGKey|"
    r"random_state\s*=|seed\s*=\s*\d|rng\s*=\s*\d)",
    re.IGNORECASE,
)

# ----------------------------------------------------------------------------
# Classe « structural » (#9434) -- speedup deterministe par taille (LEGITIME)
# ----------------------------------------------------------------------------
# Formes attrapees : « 2.78e24x », « 2.78e24 », « 4x », « 1,5x ». C'est l'ordre
# de grandeur d'un speedup fixe par la taille du probleme : deterministe, ne
# derive pas. Explicitement EXCLU du signalement (header taxonomie #9434) ;
# ne figure que sur demande explicite ``--class structural``, en banniere LEGITIME.
#
# Note fix (#9434 angle-mort t1) : la forme « 2.78e24x » (notation scientifique
# SUIVIE du suffixe 'x', PR #9427 App-11-Picross) n'etait PAS attrapee par
# l'alternance originale ``(?:e\d+|x)`` : apres avoir consomme « e24 », le
# ``\b`` echouait car le 'x' suivant est un caractere mot. La branche est
# desormais ``(?:e\d+x?|x)`` : la notation scientifique peut etre suivie d'un
# 'x' optionnel. Les dimensions WxH (ex. « 100x100 », « 1280x720 ») restent
# exclues : le ``\b`` apres le premier 'x' echoue (suivi d'un chiffre).
STRUCTURAL_RE = re.compile(
    r"(?<![\w.#])~?\d+(?:[.,]\d+)?(?:e\d+x?|x)\b",
    re.IGNORECASE,
)

# Classes reconnues par --class. L'ordre sert seulement a l'affichage.
CLASS_CHOICES = ("artifact", "machine", "env", "stochastic", "structural", "all")
# Classes flaggables (peuvent faire echouer en --strict). « structural » exclu.
FLAGGABLE = ("artifact", "machine", "env", "stochastic")


def _resolve_classes(klass: str) -> tuple[set[str], bool]:
    """Rend (ensemble de classes a detecter, est_purement_structural)."""
    if klass == "all":
        return set(FLAGGABLE), False
    if klass == "structural":
        return {"structural"}, True
    return {klass}, False


# Une ligne de diff .ipynb qui ouvre un champ JSON autre que "source" est une
# metadonnee machine-ecrite, pas de la prose.
JSON_KEY_RE = re.compile(r'"(?!source")[A-Za-z_][A-Za-z0-9_]*"\s*:')

# Blocs generes : le catalogue a le droit de porter des chiffres, c'est son role.
GENERATED_MARKERS = ("CATALOG-STATUS", "COURSE_CATALOG.generated")

# Pacing pedagogique : un « ### Durée estimée : X minutes » (ou son pendant ASCII
# « Duree estimee : X minutes ») dans une cellule markdown reflete l'effort
# demande a l'etudiant, pas une mesure machine. Le scanner FP sur l'unite
# « minutes » des qu'elle apparait dans ce contexte. Arbitrage jsboige 14:05:37Z
# sur #9434 : TN structurel/pédagogique, HORS scope drainage, à GARDER. Ligne
# entiere exoneree de la classe ``machine`` : la presence du motif (avec ou sans
# « : » final, entre « ** ** » ou en tete H2/H3 suivant le prefixe) bascule la
# ligne en TN. Les vraies wall-clock measures (sans le mot-cle pacing) restent
# capturees.
#
# Note fix (#9434 angle-mort t4) : la cle d'exemption est le mot-cle
# « (?:Durée|Duree) + estimée? » (avec ou sans accent, en ASCII ou UTF-8). Le
# suffixe (:, **, espace) est optionnel, le mot-cle seul suffit. L'exemption
# est ligne-complet : un « env. 5 min » isole (sans le mot-cle) reste flague.
# Cf test_machine_re_exempts_student_pacing_lines.
STUDENT_PACING_RE = re.compile(
    r"(?:Dur[ée])e\s+estim[ée]e?",
    re.IGNORECASE,
)

# Hors perimetre. `.claude` est le harnais (regles, memoires d'agents, plans,
# worktrees d'autres sessions) : ce n'est pas de la prose livree a un etudiant,
# et il y cite legitimement des seuils chiffres (« > 3000 lignes »).
SKIP_PARTS = (
    ".claude",
    ".lake",
    "node_modules",
    ".git",
    "_peters",
    "foundry-lib/lib",
    ".pytest_cache",
    "bin",
    "obj",
    "tmp",  # gitignore:582 -- scratch d'execution, pas du contenu livre
)

# Le catalogue genere porte des chiffres : c'est exactement son role.
SKIP_NAME_PREFIXES = ("COURSE_CATALOG.generated",)

# Un fichier qui se declare genere a le droit de porter des chiffres : c'est
# precisement le motif vise (« les donnees quantitatives sont tenues par le
# CI »). L'exemption n'est donc pas une liste de noms a maintenir, mais la
# presence d'un generateur proprietaire, declaree en tete de fichier.
GENERATED_HEADER_RE = re.compile(
    r"fichier\s+g[eé]n[eé]r[eé]"
    r"|ne\s+pas\s+[eé]diter\s+[aà]\s+la\s+main"
    r"|n'est\s+pas\s+maintenu\s+[aà]\s+la\s+main"
    r"|do\s+not\s+edit\s+(?:this\s+file\s+)?(?:by\s+hand|manually)"
    r"|auto(?:matically)?[-\s]generated",
    re.IGNORECASE,
)


def _declares_generated(text: str) -> bool:
    """Vrai si l'en-tete revendique un generateur proprietaire."""
    head = "\n".join(text.splitlines()[:20])
    return bool(GENERATED_HEADER_RE.search(head))


def _skipped(path: Path) -> bool:
    if any(part in SKIP_PARTS for part in path.parts):
        return True
    return path.name.startswith(SKIP_NAME_PREFIXES)


def _iter_markdown_sources(nb_path: Path):
    """Rend (index_cellule, source) pour les seules cellules markdown."""
    try:
        nb = json.loads(nb_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return
    for idx, cell in enumerate(nb.get("cells", [])):
        if cell.get("cell_type") != "markdown":
            continue
        src = cell.get("source", "")
        if isinstance(src, list):
            src = "".join(src)
        yield idx, src


def _notebook_is_seeded(nb_path: Path) -> bool:
    """Vrai si le carnet seme (une cellule code contient un seed).

    Heuristique conservatrice : un seed n'importe ou dans le carnet rend le
    resultat reproductible, donc la mesure stochastique est legitime.
    """
    try:
        nb = json.loads(nb_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return False  # indetermine -> on ne supprime pas le signalement
    for cell in nb.get("cells", []):
        if cell.get("cell_type") != "code":
            continue
        src = cell.get("source", "")
        if isinstance(src, list):
            src = "".join(src)
        if SEED_RE.search(src):
            return True
    return False


def _exempt_spans(path: str, line: str) -> list[tuple[int, int]]:
    """Spans de la ligne couverts par une exemption motivee propre a ce fichier.

    Le span est ce qui rend l'exemption BORNEE : elle ne protege pas le
    fichier, elle protege une portion de ligne. Un compteur voisin -- meme
    ligne, meme nom d'artefact -- reste flague.
    """
    spans: list[tuple[int, int]] = []
    for exemption in ARTIFACT_EXEMPTIONS:
        if exemption.path != path:
            continue
        spans.extend(m.span() for m in exemption.motif.finditer(line))
    return spans


def _findings_in_text(
    text: str, location: str, classes: set[str], path: str | None = None
) -> list[tuple[str, str, str]]:
    """Rend [(location, classe, snippet)] pour les classes demandees.

    La ligne est l'unite de co-occurrence pour stochastic (mot-clef + nombre sur
    la meme ligne) : evite les faux positifs d'un nombre et d'un mot-clef eloignes.
    La ligne est aussi l'unite d'exemption pacing (cf STUDENT_PACING_RE) : un
    « (Duree) (estimée) : X minutes » est TN pedagogique, jamais un compteur
    machine ; la ligne entiere est exoneree de la classe ``machine``.

    ``path`` (defaut : la partie fichier de ``location``, qui porte un suffixe
    `` MD[<i>]`` pour une cellule de carnet) selectionne les exemptions motivees
    de la classe ``artifact`` (cf ARTIFACT_EXEMPTIONS).
    """
    target = location.split(" MD[")[0] if path is None else path
    out: list[tuple[str, str, str]] = []
    for line in text.splitlines():
        if any(m in line for m in GENERATED_MARKERS):
            continue
        # Student-pacing exemption (arbitrage jsboige 14:05:37Z #9434) :
        # la ligne est TN pedagogique, on ne rapporte pas la duree machine.
        # Les autres classes (artifact, env, structural, stochastic) restent
        # actives : un « ~50 minutes » colle a un artefact (lignes) reste flag.
        is_pacing = STUDENT_PACING_RE.search(line) is not None
        if "artifact" in classes:
            exempt = _exempt_spans(target, line)
            for m in COUNT_RE.finditer(line):
                if any(start <= m.start() and m.end() <= end for start, end in exempt):
                    continue
                out.append((location, "artifact", m.group(0).strip()))
        if "machine" in classes and not is_pacing:
            for m in MACHINE_RE.finditer(line):
                out.append((location, "machine", m.group(0).strip()))
        if "env" in classes:
            for m in ENV_RE.finditer(line):
                out.append((location, "env", m.group(0).strip()))
        if "structural" in classes:
            for m in STRUCTURAL_RE.finditer(line):
                out.append((location, "structural", m.group(0).strip()))
        if "stochastic" in classes and STOCHASTIC_KW_RE.search(line):
            for m in STOCHASTIC_NUM_RE.finditer(line):
                out.append((location, "stochastic", m.group(0).strip()))
    return out


def scan_all(root: Path, classes: set[str]) -> list[tuple[str, str, str]]:
    findings: list[tuple[str, str, str]] = []

    for nb in root.rglob("*.ipynb"):
        if _skipped(nb):
            continue
        rel = nb.relative_to(root).as_posix()
        # stochastic : un carnet seme est reproductible -> on ne signale pas
        # cette classe pour lui (les autres classes restent actives).
        eff_classes = set(classes)
        if "stochastic" in eff_classes and _notebook_is_seeded(nb):
            eff_classes = eff_classes - {"stochastic"}
        for idx, src in _iter_markdown_sources(nb):
            findings += _findings_in_text(src, f"{rel} MD[{idx}]", eff_classes)

    for md in root.rglob("*.md"):
        if _skipped(md):
            continue
        rel = md.relative_to(root).as_posix()
        try:
            text = md.read_text(encoding="utf-8")
        except OSError:
            continue
        if _declares_generated(text):
            continue
        # Neutralise les blocs generes delimites par des marqueurs.
        if "CATALOG-STATUS:START" in text:
            text = re.sub(
                r"<!--\s*CATALOG-STATUS:START.*?CATALOG-STATUS:END\s*-->",
                "",
                text,
                flags=re.DOTALL,
            )
        # Pour un .md isole, on n'a pas de cellule code amont a verifier : on
        # garde stochastic en advisory (incertitude documentee, pas de gate seed).
        findings += _findings_in_text(text, rel, classes)

    return findings


# Ouverture d'un bloc `outputs` dans un notebook pretty-print. Le `\s*$` final
# est load-bearing : `"outputs": []` (cellule jamais executee) se referme sur sa
# propre ligne, l'ouvrir ferait avaler tout le reste du fichier.
OUTPUTS_OPEN_RE = re.compile(r'^(\s*)"outputs"\s*:\s*\[\s*$')

# Un bloc "source" ouvre sur sa propre ligne : `"source": [` (un tableau vide
# ou mono-ligne ne colle pas au motif et n'ouvre rien, comme `"outputs": []`).
SOURCE_OPEN_RE = re.compile(r'^(\s*)"source"\s*:\s*\[\s*$')

# Type de la cellule courante : le "source" d'une cellule code est du code
# (region non-prose), celui d'une cellule markdown est LA prose visee.
CELL_TYPE_RE = re.compile(r'^\s*"cell_type"\s*:\s*"(\w+)"')

# En-tete de hunk : `@@ -<a>[,<b>] +<c>[,<d>] @@`. Seul <c> (numero de depart dans
# le fichier NOUVEAU) nous interesse -- c'est lui qui ancre la numerotation.
HUNK_RE = re.compile(r"^@@ -\d+(?:,\d+)? \+(\d+)(?:,\d+)? @@")


def _ipynb_non_prose_lines(rel: str) -> set[int]:
    """Lignes (1-based) situees dans une region NON-PROSE d'un notebook.

    Deux regions :

    - le bloc ``outputs`` d'une cellule : la prose d'une cellule et une charge
      utile de sortie se ressemblent ligne a ligne (toutes deux sont des
      chaines nues, `    "print(...)\\n",` contre `      "  Angel.lean   65
      lignes\\n",`), et seul le bloc les separe ;
    - le bloc ``source`` d'une cellule **code** (#22564 D3) : docstrings et
      commentaires compris. « Une cellule code qui compte et affiche ... On
      ne la regarde pas » (en-tete) : un commentaire Python qui decrit un
      appel (« forward 1 ligne ») ou une empreinte memoire (« negligeables
      sur 1 ligne ») est de la prose technique legitime, pas une mesure
      figee en markdown. Le ``source`` d'une cellule markdown reste LA prose
      visee et n'entre pas dans la carte.

    Les champs `"source"` et `"outputs"` sont a la MEME profondeur, et chaque
    bloc se referme sur une ligne dont l'indentation est celle de la cle.
    C'est cette carte qui separe les regions -- le filtre ligne-a-ligne de
    `scan_diff` ne peut pas le faire seul (il ignore ``cell_type``).
    """
    try:
        text = Path(rel).read_text(encoding="utf-8", errors="replace")
    except OSError:
        return set()
    inside: set[int] = set()
    base: int | None = None
    cell_type: str | None = None
    for num, raw in enumerate(text.splitlines(), start=1):
        indent = len(raw) - len(raw.lstrip(" "))
        if base is None:
            match = CELL_TYPE_RE.match(raw)
            if match:
                cell_type = match.group(1)
            outputs_match = OUTPUTS_OPEN_RE.match(raw)
            if outputs_match:
                base = len(outputs_match.group(1))
                continue
            if cell_type == "code":
                source_match = SOURCE_OPEN_RE.match(raw)
                if source_match:
                    base = len(source_match.group(1))
                    continue
            continue
        if indent == base and raw.strip().startswith("]"):
            base = None
            continue
        inside.add(num)
    return inside


class DiffUnreadable(RuntimeError):
    """git diff n'a pas produit de diff exploitable (rc != 0, binaire absent, timeout).

    Un organe injoignable n'est pas une ardoise propre (#20194) : jamais de
    ``[OK]`` sur un diff non mesure.
    """


def scan_diff(diff_range: str, classes: set[str]) -> list[tuple[str, str, str]]:
    """Ne juge que les lignes AJOUTEES : le stock existant ne fait pas echouer.

    Leve :class:`DiffUnreadable` quand git ne resout pas la plage -- l'echec
    d'infrastructure ne se confond pas avec un diff propre.
    """
    try:
        proc = subprocess.run(
            ["git", "diff", "--unified=0", diff_range],
            capture_output=True, text=True, encoding="utf-8", errors="replace",
            timeout=180, check=False,
        )
    except (OSError, subprocess.SubprocessError) as exc:
        raise DiffUnreadable(f"git diff a echoue : {exc}") from exc
    if proc.returncode != 0:
        detail = (proc.stderr or "").strip().splitlines()
        hint = detail[-1] if detail else "sortie d'erreur vide"
        raise DiffUnreadable(f"git diff rc={proc.returncode} : {hint}")
    diff = proc.stdout

    findings: list[tuple[str, str, str]] = []
    generated_cache: dict[str, bool] = {}
    non_prose_cache: dict[str, set[int]] = {}

    def _is_generated_file(rel: str) -> bool:
        if rel not in generated_cache:
            try:
                head = Path(rel).read_text(encoding="utf-8", errors="replace")
                generated_cache[rel] = _declares_generated(head)
            except OSError:
                generated_cache[rel] = False
        return generated_cache[rel]

    def _is_non_prose(rel: str, ln: int) -> bool:
        if rel not in non_prose_cache:
            non_prose_cache[rel] = _ipynb_non_prose_lines(rel)
        return ln in non_prose_cache[rel]

    # Pour le mode diff, la verification seed par carnet est couteuse et le
    # contrat CI ne demande que la classe artifact par defaut : on applique le
    # gate seed stochastic seulement en --all (scan_all). En diff, stochastic
    # reste advisory brut (incertitude documentee).
    current = "?"
    new_ln = 0
    for line in diff.splitlines():
        if line.startswith("+++ b/"):
            current = line[6:]
            new_ln = 0
            continue
        hunk = HUNK_RE.match(line)
        if hunk:
            # `--unified=0` : le corps du hunk ne porte que les lignes ajoutees
            # et supprimees, donc la 1re ligne "+" est la ligne <c> du nouveau
            # fichier. On se place juste avant pour que `+= 1` y tombe.
            new_ln = int(hunk.group(1)) - 1
            continue
        if not line.startswith("+") or line.startswith("+++"):
            continue
        if not (current.endswith(".ipynb") or current.endswith(".md")):
            continue
        new_ln += 1
        if _skipped(Path(current)):
            continue
        if current.endswith(".md") and _is_generated_file(current):
            continue
        # La charge utile d'une SORTIE et le SOURCE d'une cellule CODE
        # ressemblent a s'y meprendre a de la prose (`"      \"  Angel.lean
        # 65 lignes\\n\","` comme `"""... forward 1 ligne."""`) : le premier
        # est le compte-rendu d'une cellule *code* qui compte et affiche, le
        # second est du code -- docstrings et commentaires compris --, et la
        # doctrine de l'en-tete declare les deux legitimes ("On ne la regarde
        # pas."). Le filtre ligne-a-ligne ne peut pas les attribuer a un type
        # de cellule ; la carte par fichier, si.
        if current.endswith(".ipynb") and _is_non_prose(current, new_ln):
            continue
        # Dans un .ipynb, seule une valeur de "source" est de la prose. Les
        # champs de metadonnees (`"notes": "... 14/14 cells executed."`, ecrit
        # par le populateur metadata.cost) sont machine-ecrits : ils portent
        # legitimement des chiffres et ne derivent pas en prose.
        if current.endswith(".ipynb"):
            body = line[1:].lstrip()
            if any(k in line for k in ('"output_type"', '"execution_count"', '"outputs"')):
                continue
            if JSON_KEY_RE.match(body):  # "<cle>": ... avec <cle> != source
                continue
            if '"source"' not in line and not body.startswith('"'):
                continue
        findings += _findings_in_text(line[1:], current, classes)

    return findings


def _emit_grouped(findings: list[tuple[str, str, str]], strict: bool, structural_only: bool) -> int:
    """Sortie multi-classes : une section par classe, ou banniere LEGITIME."""
    if structural_only:
        # structural est legitime (speedup deterministe) : on inventorie sans signaler.
        if not findings:
            print("[OK] classe structural : aucun speedup deterministe en prose.")
            return 0
        by_file: dict[str, list[str]] = {}
        for loc, _klass, snippet in findings:
            by_file.setdefault(loc.split(" MD[")[0], []).append(snippet)
        print(
            f"[LEGITIME -- structural] {len(findings)} speedup(s) deterministe(s) en "
            f"prose, {len(by_file)} fichier(s). Exclus du signalement (ne derive pas). :\n"
        )
        for path in sorted(by_file):
            preview = ", ".join(sorted(set(by_file[path]))[:6])
            print(f"  {path}  ({len(by_file[path])})  {preview}")
        return 0  # structural ne fait jamais echouer

    if not findings:
        print("[OK] aucun compteur quantitatif en prose (classe(s) demandee(s)).")
        return 0

    # Regroupe les findings par classe, puis par fichier dans chaque classe.
    by_class: dict[str, dict[str, list[str]]] = {}
    for loc, klass, snippet in findings:
        by_class.setdefault(klass, {}).setdefault(loc.split(" MD[")[0], []).append(snippet)

    total = len(findings)
    label = "REFUS" if strict else "ADVISORY"
    classes_hdr = "/".join(by_class.keys())
    print(f"[{label}] {total} compteur(s) quantitatif(s) en prose ({classes_hdr}), {len(by_class)} classe(s) :\n")
    for klass in (k for k in FLAGGABLE if k in by_class):  # ordre stable
        files = by_class[klass]
        nclass = sum(len(v) for v in files.values())
        print(f"=== [{klass}] {nclass} compteur(s), {len(files)} fichier(s) ===")
        for path in sorted(files):
            preview = ", ".join(sorted(set(files[path]))[:6])
            print(f"  {path}  ({len(files[path])})  {preview}")
        print()

    print(
        "Les donnees quantitatives sont tenues par le CI, pas par la prose "
        "(#9377 compteurs d'artefacts, #9434 mesures non reproductibles).\n"
        "Supprimer la mesure, garder le predicat : `(140 lignes, 0 sorry)` -> `(0 sorry)`."
    )
    return 1 if strict else 0


def _emit_legacy(findings: list[tuple[str, str, str]], strict: bool) -> int:
    """Sortie mono-classe artifact (format d'origine, contrat CI preserve)."""
    if not findings:
        print("[OK] aucun compteur quantitatif en prose.")
        return 0

    by_file: dict[str, list[str]] = {}
    for loc, _klass, snippet in findings:
        by_file.setdefault(loc.split(" MD[")[0], []).append(snippet)

    label = "REFUS" if strict else "ADVISORY"
    print(f"[{label}] {len(findings)} compteur(s) quantitatif(s) en prose, {len(by_file)} fichier(s) :\n")
    for path in sorted(by_file):
        snippets = by_file[path]
        preview = ", ".join(sorted(set(snippets))[:6])
        print(f"  {path}  ({len(snippets)})  {preview}")

    print(
        "\nLes donnees quantitatives sont tenues par le CI, pas par la prose (issue #9377)."
        "\nSupprimer la mesure, garder le predicat : `(140 lignes, 0 sorry)` -> `(0 sorry)`."
    )
    return 1 if strict else 0


def _exemption_audit(root: Path) -> tuple[list[tuple[ArtifactExemption, int]], list[ArtifactExemption]]:
    """Rend (exemptions vivantes avec le nombre de compteurs couverts, perimees).

    « Vivante » veut dire : le motif matche encore ET il couvre au moins un
    compteur que COUNT_RE aurait flague. Un motif qui matche sans couvrir de
    compteur ne protege rien non plus : il est perime au meme titre.
    """
    live: list[tuple[ArtifactExemption, int]] = []
    stale: list[ArtifactExemption] = []
    for exemption in ARTIFACT_EXEMPTIONS:
        try:
            text = (root / exemption.path).read_text(encoding="utf-8")
        except OSError:
            stale.append(exemption)
            continue
        covered = 0
        for line in text.splitlines():
            spans = [m.span() for m in exemption.motif.finditer(line)]
            if not spans:
                continue
            covered += sum(
                1
                for m in COUNT_RE.finditer(line)
                if any(start <= m.start() and m.end() <= end for start, end in spans)
            )
        if covered:
            live.append((exemption, covered))
        else:
            stale.append(exemption)
    return live, stale


def _report_exemptions(root: Path) -> None:
    """Restitue l'allowlist en ``--all`` : ce qu'elle couvre, et ce qui est mort.

    Jamais un echec : le stock ne fait rougir aucune PR (#17636). Ce qui est
    rendu visible, c'est la DECISION -- et son eventuelle peremption, qui sans
    cette ligne se lirait comme une exemption encore vivante.
    """
    if not ARTIFACT_EXEMPTIONS:
        return
    live, stale = _exemption_audit(root)
    if live:
        total = sum(n for _exemption, n in live)
        print(
            f"\n[ALLOWLIST] {len(live)} exemption(s) motivee(s) de la classe artifact, "
            f"{total} compteur(s) couvert(s) :"
        )
        for exemption, covered in live:
            print(f"  {exemption.path}  ({covered})  {exemption.motif.pattern}")
            print(f"    pourquoi : {exemption.raison}")
    if stale:
        print(
            f"\n[ALLOWLIST-PERIMEE] {len(stale)} entree(s) ne couvre(nt) plus aucun "
            f"compteur -- retirer l'entree : une decision morte se lit comme une "
            f"decision vivante."
        )
        for exemption in stale:
            print(f"  {exemption.path}  {exemption.motif.pattern}")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--all", action="store_true", help="inventaire complet du stock (suivi #9377/#9434)")
    g.add_argument("--diff", metavar="RANGE", help="ne juge que les lignes ajoutees (ex: origin/main...HEAD)")
    ap.add_argument(
        "--class",
        dest="klass",
        default="artifact",
        choices=CLASS_CHOICES,
        help="classe a auditer (defaut: artifact=#9377 ; machine/env/stochastic=#9434 ; "
             "structural=legitime-exclu ; all=toutes les flaggables)",
    )
    ap.add_argument("--strict", action="store_true", help="rc=1 sur finding (defaut : advisory, rc=0)")
    ap.add_argument("--root", default=".", help="racine du depot")
    args = ap.parse_args()

    classes, structural_only = _resolve_classes(args.klass)

    if args.all:
        findings = scan_all(Path(args.root).resolve(), classes)
    else:
        try:
            findings = scan_diff(args.diff, classes)
        except DiffUnreadable as exc:
            # #20194 : le check-run CI doit distinguer « diff propre » (rc=0,
            # [OK]) de « diff non mesurable » -- jamais le meme verdict.
            print(f"[NON-MESURABLE] {exc}", file=sys.stderr)
            print("[NON-MESURABLE] diff non mesurable : aucune conclusion de "
                  "proprete n'est valable (#20194).")
            return 2

    # Format legacy exact pour la classe artifact seule (contrat CI : --diff sans --class).
    if args.klass == "artifact":
        rc = _emit_legacy(findings, args.strict)
    else:
        rc = _emit_grouped(findings, args.strict, structural_only)

    # L'allowlist ne se relit qu'en inventaire : en mode --diff, un fichier non
    # touche par la PR n'est pas "perime", il est simplement hors champ.
    if args.all and "artifact" in classes:
        _report_exemptions(Path(args.root).resolve())

    return rc


if __name__ == "__main__":
    sys.exit(main())
