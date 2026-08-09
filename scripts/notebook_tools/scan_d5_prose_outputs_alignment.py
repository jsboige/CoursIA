"""Detecteur v3 -- coherence prose <-> outputs intra-revision (D5), full-corpus.

Suite logique de l'EPIC #9768 (Phase 1 outillage #9791 + Phase 0 audit #9787).
Le detecteur D5 de :mod:`scan_d1_d3_d4_d5` compare les outputs **entre revisions
consecutives** -- d'ou la dependance a l'historique git et l'impossibilite de
signaler les drifts dont les outputs n'ont jamais bouge (cf. le cas fondateur
ICT-1-PhiTrajectories commit ``7de14792c`` / issue #9416, prose « un pic a
2,31, le reste a 0,19 » qui omettait le 3ᵉ niveau 0.6875 deja present dans
les outputs ``cell[7]`` depuis toujours).

Ce module leve cette limitation en travaillant **intra-revision** :
il extrait les nombres de la prose (cellules markdown) et des outputs
(cellules code) du **meme** notebook tel qu'il est sur disque (HEAD par
defaut, ou n'importe quelle revision), puis signale deux classes de
desalignement :

1. **MISSING_FROM_OUTPUTS** : un nombre est affirme dans la prose mais n'a
   aucun correspondant dans les outputs de la revision, a tolerance
   relative 5% / absolue 1e-6 pres. Ex. : « Phi = 0.69 » alors que les
   outputs ne contiennent que 0.1875 et 2.3125.
2. **MISSING_FROM_PROSE_ENUMERATION** : la prose enumere une liste de
   niveaux (ou valeurs distinctes) en indiquant un compte N, mais les
   outputs exhibent strictement plus de niveaux distincts a tolerance
   raisonnable. C'est la classe #9416 -- **la plus dangereuse**, parce que
   la prose parait complete et l'omission est invisible a un lecteur qui
   ne recompte pas les outputs.

Pas de dependance externe. NumPy n'est PAS requis. CLI ``--check`` avec
exit codes argparse 0/1/2 distincts (succes / finding / usage -- lecon
po-2024 #9783 : un chemin inexistant ne PEUT PAS retourner 1).

Cf. issue #9790 pour le scope exact et le cas fondateur.
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


# --------------------------------------------------------------------------- #
#  Configuration
# --------------------------------------------------------------------------- #

# Formes numeriques reconnues dans la prose francaise ET anglaise :
# - decimale anglaise : 0.69, 1,234.56, 1e-3
# - decimale francaise : 0,69 ; 1 234,56 ; 1,5e-3
# On accepte virgule ET point comme separateurs ; l'ambiguite « 1,234 » est
# resolue par contexte (presence d'un second separateur desambiguisant).
FR_DECIMAL_RE = re.compile(
    r"""
    (?<![A-Za-z0-9_])              # pas au milieu d'un identifier
    -?
    (?:
        \d{1,3}(?:[\s ]\d{3})*(?:[.,]\d+)?    # 1 234,56 ou 1,234.56
      | \d+[.,]\d+                                  # 0.69 ou 0,69
      | \d+                                         # 1234
    )
    (?:[eE][-+]?\d+)?
    (?![A-Za-z0-9_])                # pas au milieu d'un identifier
    """,
    re.VERBOSE,
)


# Bruits a filtrer systematiquement : annees, numeros de PR / issue, versions.
# On filtre en post-processing -- le filtre strict etait trop fragile en c.1264.
EXCLUDE_PATTERNS = (
    re.compile(r"^\d{4}$"),                # annees 1900-2099 (detectees par 4 chiffres seuls)
    re.compile(r"^#\d+$"),                 # numeros d'issue/PR : #9416
    re.compile(r"^v\d+$"),                 # versions semver simplifiees
    re.compile(r"^cell\[\d+\]$"),          # indices cell[N]
    re.compile(r"^[A-Z]+\d+$"),            # PRJ42, ABC123 -- discutable, mais limite
)


# Identifiants de reference (DOI / arXiv) : classes dominantes de faux positifs
# observees firsthand en EPIC #9768 Phase 0 (po-2025, c.1291) sur les familles
# riches en citations -- Probas/Infer.NET (~40 findings/notebook) et ML.NET labs.
# Ces identifiants sont parses comme des floats par FR_DECIMAL_RE mais ne sont
# jamais des mesures calculees.
#   (a) prefix registrant DOI : 10.1109, 10.1145, 10.1002 ... (10. + >=4 chiffres)
#   (b) suffixe d'URL DOI     : le nombre suit immediatement un prefixe
#       registrant sur la meme ligne (10.1145/564376.564421 -> 564376.564421)
#   (c) arXiv ID              : YYMM.NNNNN (annee plausible 19-30) ou contexte
#       explicite « arXiv: » (2402.0103, 2309.07864)
_DOI_PREFIX_RE = re.compile(r"^10\.\d{4,}$")          # (a) 10.1109 / 10.1145
_DOI_SUFFIX_RE = re.compile(r"10\.\d{4,}/\S*$")        # (b) prefix-line = URL DOI
_ARXIV_ID_RE = re.compile(r"^\d{4}\.\d{4,5}$")         # (c) 2402.0103 (4-5 decimales)
_ARXIV_HINT_RE = re.compile(r"arxiv", re.IGNORECASE)   # (c) contexte explicite


def _is_reference_identifier(raw: str, line_prefix: str) -> bool:
    """Vrai si `raw` est un identifiant de reference (DOI / arXiv), pas une mesure.

    `line_prefix` = texte de la meme ligne precedant le token (lowercase),
    deja calcule par l'appelant pour les autres filtres semantiques.
    """
    # (a) prefix registrant DOI (10.1109, 10.1145) -- impossible comme mesure.
    if _DOI_PREFIX_RE.match(raw):
        return True
    # (c) arXiv ID YYMM.NNNNN : on n'exclut qu'a annee plausible (19-30) ou si
    # le contexte cite explicitement arXiv, pour ne pas tuer un resultat legit
    # type 1234.56789 (annee 12 hors plage).
    if _ARXIV_ID_RE.match(raw):
        yy = int(raw[:2])
        if 19 <= yy <= 30 or _ARXIV_HINT_RE.search(line_prefix):
            return True
    # (b) suffixe d'URL DOI : le prefix contient un registrant suivi de `/` puis
    # de non-whitespace jusqu'a ce token (ex. « ...10.1145/ » avant 564376...).
    # Un nombre legit apres un DOI separes par une espace n'est pas atteint
    # (la regex exige \S* jusqu'a la fin du prefix, sans espace intercalaire).
    if _DOI_SUFFIX_RE.search(line_prefix):
        return True
    return False


# Ligne de titre markdown ATX (CommonMark) : 0-3 espaces puis 1-6 `#` puis un
# espace ou fin de ligne. Les hints `## `/`### `/`#### ` ci-dessous couvraient
# H2-H6 mais laissaient fuiter les titres H1 (`# SC-8-...`, `# MGS-9`,
# `# SocialChoice 03`), source documentee de FP dans le corpus run #9790 (taux
# de FP ~90 %, echantillon relu main). Un nombre sur une ligne de titre est un
# numero de section/exercice/titre, jamais une mesure calculee.
_ATX_HEADING_LINE_RE = re.compile(r"\s{0,3}#{1,6}(?:\s|$)")


# Math inline LaTeX (cellules markdown pedagogiques) : un nombre dans une
# formule ($2^n - 1$, $v(S) \in \{0, 1\}$, $3^n$) est une constante/base
# mathematique, pas une mesure citee des outputs. Source documentee de FP
# dans le corpus run #9790 : firsthand c.1293 sur Sudoku/Planners/GameTheory
# montre que la classe residuelle dominante de MISSING_FROM_PROSE_ENUMERATION
# est la math inline (Planners-6 cell[13] "$2^n - 1$" -> prose_number 2.0 FP ;
# GameTheory-15b cell[28] "$v(S) \in \{0, 1\}$" -> FP). On exclut donc tout
# nombre tombant dans un span math. Display math $$...$$ est matche en premier
# (plus long) ; inline $...$ n'accepte ni $ ni newline interne (evite de
# gobler un $ de monnaie isole jusqu'au prochain $ distant).
_LATEX_MATH_SPAN_RE = re.compile(r"\$\$.*?\$\$|\$[^\$\n]*?\$", re.DOTALL)

# Codes couleur hex (#RRGGBB / #RGB / #RRGGBBAA) dans les diagrammes mermaid
# et le CSS inline. Un canal comme #084298 etait extrait comme le nombre
# 84298 (c.1295 firsthand : SW-6-CSharp-RDFS cell[6] classDef mermaid ->
# stroke:#084298, plus #0f5132/#b8860b/#5c4400 dans la meme cellule ; la
# classe est systematique des qu'un notebook embarque du mermaid style).
# On exclut tout token `#` + 3 a 8 chiffres hex ; une mesure reelle n'est
# jamais prefixee de `#` (et les references `#123` sont deja filtrees par
# les hints semantiques / _is_reference_identifier).
_HEX_COLOR_RE = re.compile(r"#[0-9a-fA-F]{3,8}")

# Exposants en notation plaine (2^3, 10^5, n^2), hors math LaTeX ($2^3$ est
# deja couvert par _LATEX_MATH_SPAN_RE). La base et l'exposant sont des
# constituants d'une expression mathematique, pas des mesures separees
# (c.1295 firsthand : Infer-7-Skills-IRT cell[64] "2^3 combinaisons" ->
# prose_number 2.0 et 3.0 FP). On saute tout nombre tombant dans un span
# alphanum^alphanum (couvre 2^3, n^2, 2^32 ; le caret est distinctif).
_PLAINTEXT_EXPONENT_RE = re.compile(r"[0-9a-zA-Z]+\^[0-9a-zA-Z]+")

# Marqueur de liste ordonnee markdown/CommonMark (po-2023 #9790, FP class 7) :
# une ligne debutant par <= 3 espaces, un entier, puis `.` ou `)` puis un
# espace (ou fin de ligne) est un ITEM de liste ordonnee -- l'entier est
# l'INDICE d'enumeration, jamais une mesure d'output. Source documentee dans
# le corpus run #9790 : po-2023 a quantifie 345 occurrences (14 %) de
# `ordered-list-marker` sur SymbolicAI. Re-verifie firsthand (G.1, 2026-08-09,
# classifier SAFE-by-construction sur le corpus full) : 770/10411 findings
# MISSING_FROM_OUTPUTS (7.4 %) sont des marqueurs purs -- echantillon 12/12
# est 100 % d'items de liste (« 5. Analyser le jeu de la Chasse au Cerf »,
# « 6. **Exercices** », « 3. **Monitoring** : Necessaire uniquement en
# production »).
#
# Falsifiable both-directions (0 sur-filtrage par construction) : on ne filtre
# QUE si le nombre extrait est le PREMIER token non-blanc de sa ligne ET est
# immediatement suivi de `.`/`)` puis d'un espace/EOL. Une mesure decimale
# (`1.15`, `0.73`) ne rend jamais sous cette forme -- le `.` est un separateur
# decimal interne au token, donc apres le token matche le caractere suivant
# n'est pas `.`/`)`+espace (c'est le contexte de la phrase). Une mesure entiere
# en milieu de phrase (« on obtient 5 widgets ») a du texte avant elle ->
# n'est pas le premier token de la ligne -> non filtree. Verifie : aucun
# marqueur de liste dans l'echantillon n'est une mesure citee.
_ORDERED_LIST_MARKER_LINE_RE = re.compile(r"\s{0,3}(\d+)[.)](?:[ \t]|$)")


# Faux positifs semantiques : regex strictes (mot complet + caractere de
# liaison) pour eviter de matcher au milieu d'une phrase legit.
# Format : hint = substring qui DOIT etre immediatement suivi du nombre matche.
SEMANTIC_FALSE_POSITIVE_HINTS = (
    "## ", "### ", "#### ",            # titres markdown (ligne commence par titres)
    "year ", "annee ",                  # contexte temporel
    "PR #", "issue #", "cf. #", "see #",   # references croisees (suivi de #)
    "§ ", "section ", "chapter ",      # structure
    "depuis ", "after ", "before ",    # contexte temporel
)


# Tolerances pour le matching prose <-> outputs.
RELATIVE_TOLERANCE = 0.05     # 5%
ABSOLUTE_TOLERANCE = 1e-6

# Bornes physiques pour eviter les nombres triviaux ou astronomiques.
MIN_NUMBER_VALUE = 1e-9
MAX_NUMBER_VALUE = 1e15

# Gate anti-bruit pour MISSING_FROM_OUTPUTS (EPIC #9768 Phase 0 : le detecteur
# v2 emettait 21589 findings full-corpus dont l'inspection firsthand montre
# ~99% de faux positifs -- nombres de prose qui sont des references, numeros
# de section, dates, identifiants, et non des mesures). Comme le detecteur D1
# (scan_d1_d3_d4_d5.py D1_ORPHAN_RATIO_THRESHOLD), on ne signale une cellule
# que si une fraction significative de SES nombres prose sont orphelins : une
# cellule dont 1 nombre sur 10 est absent = bruit (reference croisee) ; une
# cellule dont 5 sur 10 sont absents = derive authentique (la prose decrit des
# resultats non calcules).
MISSING_FROM_OUTPUTS_CELL_RATIO = 0.50   # >=50% des nombres prose orphelins (cell dense)
MISSING_FROM_OUTPUTS_CELL_MIN = 3        # seuil "dense" (cell >=3 nombres prose)

# FP class 2 (#9995) : cellules stub d'exercice. La prose d'enonce qui precede
# immediatement un stub decrit le PROBLEME (maison 200 000 EUR, P=2%, prime
# 5 000) -- ses nombres sont des DONNEES, pas des MESURES, et le stub n'a pas
# de sortie reelle ("Exercice a completer") donc ne peut rien verifier contre.
# Falsifiable both-directions : un stub n'a pas de sortie reelle -> ne peut
# pas deriver. Un stub qui produirait des nombres n'est PAS un stub (ses nombres
# sont des sorties reelles). Verifie firsthand : DecPyMC-1 cell[25]->[26],
# Pyro_RSA_Hyperbole cell[15]->[16] (corpus Probas : 112/1023 = 11% FP).
_STUB_OUTPUT_RE = re.compile(
    r"(?:exercice|exercise|exerc[cí]icio).{0,20}(?:compl[eé]t|termin[eé])"
    r"|à compléter|a completer|non compl[eé]t"
    r"|\bTODO\b",
    re.IGNORECASE,
)
_STUB_SOURCE_RE = re.compile(
    r"#\s*TODO|raise NotImplementedError|return None\s*(?:#.*)?$|\bpass\b\s*(?:#.*)?$",
    re.MULTILINE,
)

# FP class 4 (#9995) : references bibliographiques au format volume:page-page.
# La prose qui cite une source (Comptes Rendus 25:536-538, textbook 12:2825-2830,
# journal vol. 183:301-324) contient des nombres qui ne sont PAS des mesures
# calculees -- ce sont des identifiants de citation, aucun output ne peut les
# "verifier". Falsifiable both-directions : un nombre n'est filtre QUE s'il
# apparait comme volume ou page d'un pattern N:N-N ET qu'une fenetre autour
# porte un marqueur bibliographique (volume, pp., Comptes Rendus, journal,
# proceedings...). Sans contexte biblio, le nombre demeure un orphelin a
# signaler (conservateur : evite le sur-filtrage des coïncidences N:N-N
# non bibliographiques). Verifie firsthand : 40/10895 orphelins corpus
# supprimes (0.37%), 0 sur-filtrage (chaque suppression confirmee etre le
# volume ou une page d'une citation reelle -- Comptes Rendus 25:536-538,
# JMLR 12:2825-2830 / 14:567-599 / 6:1939-1959 / 3:993-1022 / 11:1297-1332,
# Nature 323:533-536, NumPy 585:357-362, LNCS 4963:337-340, GameTheory
# 183:301-324 / 100:295-320). Concentres dans ML\DataScienceWithAgents
# (textbook 12:2825-2830, 8+ notebooks), Probas/Infer + PyMC, GameTheory.
_BIBLIO_RANGE_RE = re.compile(r"(\d+)\s*:\s*(\d+)\s*-\s*(\d+)")
_BIBLIO_CONTEXT_RE = re.compile(
    r"comptes\s+rendus|\bvolume|\bvol\.?|\bpp\.?|\bpages?|\bjournal\b"
    r"|proceedings|ann(?:a|e)les|transac|réf(?:érence)?|biblio|citation",
    re.IGNORECASE,
)
_BIBLIO_CONTEXT_WINDOW = 200  # fenêtre de recherche du contexte (chars avant/après)

# FP class 5 (#9998) : references croisees structurelles vers un autre notebook
# de la serie. La prose pedagogique pointe frequemment un notebook voisin via un
# lien markdown dont le TEXTE et/ou l'URL portent l'indice du notebook :
# « la theorie du [2.8](2.8-Theorie-PAC.ipynb) », « l'ACP du
# [2.6](2.6-Clustering-KMeans-PCA.ipynb) », « [<< 2.8-Theorie-PAC](...ipynb) ».
# Le nombre extrait (2.8, 2.6, 1.3) est l'IDENTIFIANT du notebook pointe, pas une
# mesure calculee -- aucun output ne peut le verifier. SAFE par construction : on
# ne filtre la decimale N.M que si TOUTES ses occurrences dans la cellule
# tombent a l'interieur d'un span de lien markdown ciblant un .ipynb. Si une
# seule occurrence est hors-lien (potentielle mesure en prose), on ne filtre pas
# (conservateur, 0 sur-filtrage). Verifie firsthand : 20/10895 orphelins corpus
# supprimes (0.18%), concentres dans 2.9-Grokking-Generalisation (cellules de
# conclusion/navigation referencent 2.5/2.6/2.8 via liens .ipynb -- chaque indice
# y apparait exclusivement dans un lien). Les cellules ou l'indice apparait
# AUSSI hors-lien (ex 1.2-NumPy « Pandas (1.3) » en prose + lien [1.3]) ne sont
# PAS filtrees (conservateur : l'occurrence prose pourrait etre un measurand).
# On ne s'appuie PAS sur le pattern keyword « section N.M » / prose-xref (plus
# ambigu, defer -- grain futur si material).
_MARKDOWN_IPYNB_LINK_RE = re.compile(r"\[([^\]]*)\]\(([^)]*\.ipynb)\)")
# FP class 6 (#9998) : references bibliographiques au format volume(issue):pages,
# p.ex. ``Nature 585(7825):357-362``, ``Econometrica 50(6):1431-1451``,
# ``Annals of Mathematics 54(2):286-295``, ``J. American Statistical Association
# 88(421):309-319``. Le pattern ``vol(issue):pages`` ancre 4 nombres par des
# separateurs specifiques (parens + tiret) ; c'est un identifiant de citation
# beaucoup plus restrictif que le pattern ``vol:page-page`` de #9995. Verifie
# firsthand (G.1, 2026-08-08, scan Python du corpus) :
#   - 270 occurrences du pattern ``N(M):P-Q`` dans 56 notebooks
#   - 173 portaient un keyword biblio (Nature/Journal/etc.) en proximite 60 chars
#     -> absorbees par _BIBLIO_RANGE_RE + _BIBLIO_CONTEXT_RE existants
#   - 97 sans keyword biblio : 100% sont des refs biblio avec journaux
#     sans mot-cle (Annals of Mathematics, Econometrica, Mathematische Annalen,
#     Management Science, Theory and Decision, Int. Journal of Game Theory,
#     J. American Statistical Association, etc.)
#   - 81/97 ont une annee (19xx/20xx) sur la meme ligne : 0 faux-positifs mesures
#   - 1/97 sans keyword ni annee = quand meme biblio (J. American Statistical
#     Association 88(421):309-319 avec parenthese sur l'annee qui rend la regex
#     `\b(19|20)\d{2}\b` silencieuse). Garde-fou = Tier 1 (keyword) OU
#     Tier 2 (anchor + year on line). Cumul : 173 + 81 = 254 hits biblio.
#   - 0 sur-filtrage mesure (le pattern ``N(M):P-Q`` est specifique a 4 nombres
#     distincts separes par ()-: ; aucune mesure reelle ne rend sous cette forme).
_BIBLIO_VOL_ISSUE_RE = re.compile(r"\b(\d{1,4})\((\d{1,4})\):(\d{1,4})-(\d{1,4})\b")
_BIBLIO_EXTENDED_CONTEXT_RE = re.compile(
    # Keywords biblio (mêmes que _BIBLIO_CONTEXT_RE + journaux sans "Journal" explicite)
    r"comptes\s+rendus|\bvolume|\bvol\.?|\bpp\.?|\bpages?|\bjournal\b"
    r"|proceedings|ann(?:a|e)les|transac|réf(?:érence)?|biblio|citation"
    r"|nature|science|\bseries\b|\bmethodolog|\bstatistical\s+assoc"
    # + journaux où le nom NE contient PAS "Journal" explicite
    r"|econometrica|management\s+science|theory\s+and\s+decision"
    r"|mathematische\s+annalen|annals\s+of\s+mathematics"
    r"|communications\s+of\s+the\s+acm|acm\s+computing\s+surveys"
    r"|artificial\s+intelligence\s+(?:journal|\(?\b)",
    re.IGNORECASE,
)
_BIBLIO_YEAR_ON_LINE_RE = re.compile(r"\(\d{4}\)|\b(?:19|20)\d{2}\b")


# --------------------------------------------------------------------------- #
#  Dataclasses
# --------------------------------------------------------------------------- #


@dataclass
class AlignmentFinding:
    """Un cas de desalignement detecte."""
    notebook: str
    cell_index: int                  # index de la cellule markdown fautive
    cell_kind: str                   # toujours 'markdown' ici
    category: str                    # 'MISSING_FROM_OUTPUTS' ou 'MISSING_FROM_PROSE_ENUMERATION'
    prose_text: str                  # extrait du markdown (tronque)
    prose_number: float
    closest_output_number: float | None
    tolerance_used: str             # 'relative' ou 'absolute' ou 'none'
    details: str = ""


@dataclass
class NotebookAlignment:
    """Resultat d'analyse d'un notebook."""
    path: str
    total_findings: int
    findings: list[AlignmentFinding]
    n_prose_numbers: int = 0
    n_output_numbers: int = 0
    n_markdown_cells: int = 0
    n_code_cells: int = 0
    error: str | None = None

    @property
    def is_pathological(self) -> bool:
        return self.total_findings > 0 and self.error is None


# --------------------------------------------------------------------------- #
#  Extraction de nombres
# --------------------------------------------------------------------------- #


def _parse_fr_number(text: str) -> float | None:
    """Parse un token numerique au format FR ou EN vers float.

    Heuristique : si le token contient un point ET une virgule, le dernier
    des deux est le separateur decimal ; les autres sont des separateurs de
    milliers et doivent etre retires. Sinon, la presence d'un des deux
    suffit comme decimal.
    """
    t = text.replace(" ", "").replace(" ", "")  # espaces insécables
    if not t:
        return None
    has_dot = "." in t
    has_comma = "," in t
    if has_dot and has_comma:
        # dernier séparateur = décimal
        if t.rfind(".") > t.rfind(","):
            t = t.replace(",", "")
        else:
            t = t.replace(".", "").replace(",", ".")
    elif has_comma:
        t = t.replace(",", ".")
    # Exposant e déjà ASCII
    try:
        v = float(t)
    except ValueError:
        return None
    if abs(v) < MIN_NUMBER_VALUE or abs(v) > MAX_NUMBER_VALUE:
        return None
    return v


def _extract_prose_numbers(text: str) -> list[float]:
    """Extrait les nombres d'un texte markdown en filtrant les faux positifs semantiques."""
    if not text:
        return []
    # Precompute les spans a ignorer une fois (evite un finditer par nombre) :
    # math LaTeX ($2^n - 1$), codes couleur hex (#084298), exposants plaine
    # (2^3). Un nombre tombant dans un de ces spans n'est pas une mesure
    # d'output (constante de formule / canal de couleur / constituant
    # d'exposant). c.1293 (LaTeX), c.1295 (hex + exposant).
    skip_spans = (
        [m.span() for m in _LATEX_MATH_SPAN_RE.finditer(text)]
        + [m.span() for m in _HEX_COLOR_RE.finditer(text)]
        + [m.span() for m in _PLAINTEXT_EXPONENT_RE.finditer(text)]
    )
    out: list[float] = []
    for m in FR_DECIMAL_RE.finditer(text):
        raw = m.group(0)
        # Filtre spans a ignorer (math LaTeX, hex, exposant) : voir ci-dessus.
        if any(a <= m.start() < b for a, b in skip_spans):
            continue
        # Filtre bruit : années, numéros d'issue, etc.
        if any(p.match(raw) for p in EXCLUDE_PATTERNS):
            continue
        # Filtre semantique : on regarde **la meme ligne** (avant-dernier
        # newline), pas les 60 chars precedents. Un header `## 4.2` sur
        # la ligne N ne doit pas filtrer un nombre legit sur la ligne N+1.
        # Les hints sont concis (chacun demarre par un mot complet) pour
        # eviter de matcher au milieu d'un titre.
        line_start = text.rfind("\n", 0, m.start()) + 1
        prefix = text[line_start:m.start()].lower()
        # Filtre titres ATX (H1-H6) : la ligne entiere du nombre est un titre
        # markdown. Les hints `## `/`### ` filtraient deja H2+ par prefixe ;
        # ce check regex (ancre debut de ligne) ferme le gap H1 et durcit la
        # detection (titre = structural, jamais une mesure d'output). On
        # examine le debut de ligne brut (le `#` n'a pas de casse).
        if _ATX_HEADING_LINE_RE.match(text[line_start:m.start() + len(raw)]):
            continue
        # Filtre marqueur de liste ordonnee (po-2023 #9790, FP class 7) : le
        # nombre extrait est-il le MARQUEUR d'un item (`N.` / `N)` en debut de
        # ligne) ? Un indice d'enumeration n'est jamais une mesure d'output.
        # SAFE-by-construction : exige (a) le nombre est le premier token
        # non-blanc de sa ligne (prefix purement blanc) ET (b) immediatement
        # suivi de `.`/`)` puis d'un espace/EOL -- forme distincte d'une mesure
        # decimale ou entiere en milieu de phrase (cf. _ORDERED_LIST_MARKER_LINE_RE).
        if prefix.strip() == "":
            after = text[m.end():m.end() + 2]
            if after and after[0] in ".)" and (
                len(after) == 1 or after[1] in " \t" or after[1] == "\n"
            ):
                continue
        if any(h in prefix for h in SEMANTIC_FALSE_POSITIVE_HINTS):
            continue
        # Filtre DOI / arXiv : identifiants de reference (jamais des mesures).
        # EPIC #9768 Phase 0 (c.1291) -- classe dominante de FP sur les familles
        # riches en citations (Probas/Infer.NET, ML.NET labs).
        if _is_reference_identifier(raw, prefix):
            continue
        v = _parse_fr_number(raw)
        if v is None:
            continue
        out.append(v)
    return out


def _extract_output_numbers(output: dict) -> list[float]:
    """Extrait les nombres d'un dict output Jupyter (text/plain ou data)."""
    nums: list[float] = []
    if not isinstance(output, dict):
        return nums
    # 1. 'text' peut etre str OU list[str] (format Jupyter stream).
    t = output.get("text")
    if isinstance(t, str):
        nums.extend(_extract_prose_numbers(t))
    elif isinstance(t, list):
        for item in t:
            if isinstance(item, str):
                nums.extend(_extract_prose_numbers(item))
    # 2. data['text/plain'] (liste ou string)
    data = output.get("data")
    if isinstance(data, dict):
        tp = data.get("text/plain")
        if isinstance(tp, str):
            nums.extend(_extract_prose_numbers(tp))
        elif isinstance(tp, list):
            for item in tp:
                if isinstance(item, str):
                    nums.extend(_extract_prose_numbers(item))
    # 3. data['text/latex'] ou similaire -- on laisse pour l'instant.
    return nums


def _is_stub_code_cell(cell: dict) -> bool:
    """Vrai si une cellule code est un stub d'exercice (placeholder, pas de resultat reel).

    Critere falsifiable (FP class 2, #9995) : la cellule ne produit AUCUN nombre
    (pas de sortie numerique reelle) ET son output texte est une phrase-placeholder
    pedagogique ("Exercice a completer", "TODO") OU sa source porte un marqueur
    stub (`# TODO etudiant`, `pass`, `return None`). Un stub qui produirait quand
    meme des nombres n'est pas un stub : ses nombres sont des sorties reelles que
    le detecteur doit pouvoir verifier.
    """
    if cell.get("cell_type") != "code":
        return False
    out_text_parts: list[str] = []
    has_numbers = False
    for out in (cell.get("outputs") or []):
        if not isinstance(out, dict):
            continue
        if _extract_output_numbers(out):
            has_numbers = True
        t = out.get("text")
        if isinstance(t, str):
            out_text_parts.append(t)
        elif isinstance(t, list):
            out_text_parts.extend(x for x in t if isinstance(x, str))
        data = out.get("data")
        if isinstance(data, dict):
            tp = data.get("text/plain")
            if isinstance(tp, str):
                out_text_parts.append(tp)
            elif isinstance(tp, list):
                out_text_parts.extend(x for x in tp if isinstance(x, str))
    if has_numbers:
        return False
    out_text = "\n".join(out_text_parts)
    if _STUB_OUTPUT_RE.search(out_text):
        return True
    source = "".join(cell.get("source") or [])
    return bool(_STUB_SOURCE_RE.search(source))


def _is_bibliographic_reference(value: float, text: str) -> bool:
    """Vrai si ``value`` est le volume ou une page d'une reference bibliographique.

    Critere falsifiable (FP class 4, #9995) : un nombre orphelin n'est pas une
    mesure manquante s'il appartient a une reference de citation au format
    ``volume:page-page`` (ex ``Comptes Rendus 25:536-538``, textbook
    ``12:2825-2830``, ``vol. 183:301-324``) ET qu'une fenetre autour porte un
    marqueur bibliographique. Le contexte bibliographique est EXIGE (pas
    d'inférence sur un pattern N:N-N seul) pour eviter le sur-filtrage des
    coïncidences non bibliographiques (intervals d'indices, ranges de donnees).

    Falsifiable both-directions : un nombre qui n'apparait comme volume/page
    d'AUCUN ``vol:page-page``, ou dont le match n'a pas de contexte biblio,
    n'est PAS filtre -- il demeure un orphelin a signaler.

    Note anti-sur-filtrage : un volume ou une page bibliographique est
    TOUJOURS un entier (``12:2825-2830``). Une decimale (``12.2``, ``6.2``)
    ne peut PAS etre un volume/page -> n'est JAMAIS filtree par cette voie
    (sinon une mesure ``12.2`` serait supprimee parce qu'elle s'arrondit au
    volume ``12``). Les decimales demeurent des orphelins a signaler ; si ce
    sont des references de section (``section 12.2``), c'est un filtre
    distinct hors scope biblio vol:page.
    """
    if value != int(value):
        return False  # un volume/page biblio est entier ; une decimale ne l'est pas
    iv = int(value)
    # FP class 4 (#9995) : vol:page-page + keyword biblio
    for m in _BIBLIO_RANGE_RE.finditer(text):
        vol, p1, p2 = int(m.group(1)), int(m.group(2)), int(m.group(3))
        if iv != vol and iv != p1 and iv != p2:
            continue
        window = text[max(0, m.start() - _BIBLIO_CONTEXT_WINDOW): m.end() + _BIBLIO_CONTEXT_WINDOW]
        if _BIBLIO_CONTEXT_RE.search(window):
            return True
    # FP class 6 (#9998) : vol(issue):pages, double-tier safe-by-construction
    # Tier 1 : keyword biblio (etendu) en proximite 60 chars
    # Tier 2 : pattern anchor + year (19xx/20xx) sur la meme ligne
    # -> 0 sur-filtrage verifie firsthand (270 hits : 173 Tier1 + 81 Tier2 + 16 sans year)
    for m in _BIBLIO_VOL_ISSUE_RE.finditer(text):
        vol, issue, p1, p2 = int(m.group(1)), int(m.group(2)), int(m.group(3)), int(m.group(4))
        if iv != vol and iv != issue and iv != p1 and iv != p2:
            continue
        # Tier 1 : keyword biblio etendu en proximite 60 chars (meme seuil que le
        # _BIBLIO_CONTEXT_RE original, mais avec journaux additionnels)
        window_60 = text[max(0, m.start() - 60): m.end() + 60]
        if _BIBLIO_EXTENDED_CONTEXT_RE.search(window_60):
            return True
        # Tier 2 : pattern anchor + annee sur la meme ligne. Garde-fou : la
        # ligne contenant le pattern porte une marque d'annee explicite (parenthese
        # type "(1982)" ou annee 4 chiffres), ce qui est quasi-universel pour
        # une entree biblio (volume(issue):pages est TOUJOURS date).
        line_start = text.rfind("\n", 0, m.start()) + 1
        line_end = text.find("\n", m.end())
        if line_end == -1:
            line_end = len(text)
        line = text[line_start:line_end]
        if _BIBLIO_YEAR_ON_LINE_RE.search(line):
            return True
    return False

def _is_notebook_cross_reference(value: float, text: str) -> bool:
    """Vrai si ``value`` est l'indice d'un notebook pointe par un lien markdown.

    Critere falsifiable (FP class 5, #9998) : un nombre orphelin n'est pas une
    mesure manquante s'il apparait comme l'indice d'un autre notebook de la
    serie, cite via un lien markdown ciblant un ``.ipynb`` -- « la theorie du
    [2.8](2.8-Theorie-PAC.ipynb) », « l'ACP du [2.6](2.6-Clustering.ipynb) »,
    « [<< 2.8-Theorie-PAC](2.8-Theorie-PAC.ipynb) ». Le nombre est alors
    l'IDENTIFIANT du notebook pointe (dans le texte du lien ou dans le nom du
    fichier .ipynb), pas un resultat de calcul.

    SAFE par construction (0 sur-filtrage) : on ne filtre la decimale N.M que si
    **toutes** ses occurrences dans la cellule tombent a l'interieur d'un span de
    lien markdown ``[...](...ipynb)``. Ainsi, si la meme cellule contient aussi
    N.M comme vraie mesure en prose (hors-lien), au moins une occurrence est
    hors-lien -> on ne filtre pas (l'orphelin legitime survive). Les indices de
    notebook etant toujours decimaux (2.8, 1.3), un entier n'est jamais filtre.

    On ne s'appuie PAS sur le pattern keyword « section N.M » (plus ambigu, defer).

    Falsifiable both-directions : un nombre qui n'apparait dans AUCUN lien
    markdown .ipynb, ou dont une occurrence est hors-lien, n'est PAS filtre.
    """
    if value == int(value):
        return False  # un indice de notebook est decimal (2.8), jamais entier
    token = f"{value:g}"
    token_re = re.compile(r"(?<![\d.])" + re.escape(token) + r"(?![\d.])")
    link_spans = [(m.start(), m.end()) for m in _MARKDOWN_IPYNB_LINK_RE.finditer(text)]
    if not link_spans:
        return False
    found_inside = False
    for m in token_re.finditer(text):
        if not any(a <= m.start() < b for a, b in link_spans):
            return False  # occurrence hors-lien -> potentielle mesure, ne pas filtrer
        found_inside = True
    return found_inside


# --------------------------------------------------------------------------- #
#  Alignement prose <-> outputs
# --------------------------------------------------------------------------- #


def _is_close(a: float, b: float) -> bool:
    """Vrai si a == b à tolérance relative 5% / absolue 1e-6 près."""
    if a == b:
        return True
    diff = abs(a - b)
    if diff <= ABSOLUTE_TOLERANCE:
        return True
    base = max(abs(a), abs(b))
    if base == 0:
        return False
    return diff / base <= RELATIVE_TOLERANCE


def _closest_output(prose_val: float, output_vals: list[float]) -> float | None:
    """Trouve la valeur de output la plus proche de prose_val, si dans la tolérance."""
    if not output_vals:
        return None
    best = min(output_vals, key=lambda v: abs(v - prose_val))
    if _is_close(prose_val, best):
        return best
    return None


# --------------------------------------------------------------------------- #
#  Détection d'énumération prose (MISSING_FROM_PROSE_ENUMERATION)
# --------------------------------------------------------------------------- #
#
# Catégorie #9416 : la prose déclare une liste de N niveaux/valeurs distincts
# (via un mot-clé d'énumération : « N niveaux : a, b, c », « les3 valeurs sont »,
# « on observe3 phases »), mais les outputs exhibent strictement plus de niveaux
# distincts à tolérance raisonnable. L'omission est invisible au lecteur qui
# ne recompte pas les outputs.
#
# Limites assumées :
# - On ne parse que les énumérations **explicites** (mot-clé d'annonce avant la
#   liste). Une prose vague (« il y a plusieurs pics ») n'est pas attrapée — la
#   catégorie #2 reste un point de départ d'investigation.
# - La tolérance de groupement est RELATIVE_TOLERANCE (5%) pour rester cohérent
#   avec MISSING_FROM_OUTPUTS ; on n'invente pas une métrique distincte.
#
# Heuristique regex :
#   - Mot-clé d'annonce : `(N|niveau|niveaux|valeur|valeurs|état|états|
#     phase|phases|pic|pics|cluster|clusters|classe|classes|catégorie|
#     catégories|étape|étapes|graphe|graphes)`.
#   - Séparateur d'annonce : `:` ou `sont` ou `observ(e|ent|ons)` ou
#     `correspondent à` ou ` vaut `.
#   - Suite : nombres FR/EN séparés par virgules (accepte «, », « , », « ; »).


# Heuristique d'annonce d'une énumération : soit (a) un mot-clé fort
# (« N niveaux : », « les 3 valeurs sont »), soit (b) une formulation
# naturelle « un/une <mot> à X, ... le reste à Y » qui déclare implicitement
# 2 groupes. (b) attrape le cas fondateur ICT-1 (#9416) sans surcharger.
#
# NB : on utilise un lookbehind pour ne PAS consommer le chiffre qui suit
# « à/a » -- sinon on mange la 1ère valeur de l'énumération.
_ENUMERATION_KEYWORDS_RE = re.compile(
    r"""
    (?:
        \d+\s+
        (?:niveaux|valeurs|états|phases|pics|clusters|classes|
            catégories|étapes|graphes|sommets|options)
      | les\s+\d+\s+\w+
      | on\s+observ(?:e|ent|ons)\s+\d+\s+\w+
      | il\s+y\s+a\s+\d+\s+\w+
      | (?<!\d)(?:un|une|le|la|des)\s+(?:pic|pics|cluster|clusters|groupe|
            groupes|paquet|paquets|état|états|niveau|niveaux|phase|phases|
            valeur|valeurs|classe|classes|catégorie|catégories)\s+[àa]
    )
    """,
    re.VERBOSE | re.IGNORECASE,
)


def _latex_math_to_text(content: str) -> str:
    """Convertit le contenu d'un span math LaTeX en texte extractible.

    Retourne le nombre (ex. ``2.31``) si le span est un decimal LaTeX pur
    (``$2{,}31$`` apres fusion des separateurs), sinon une chaine vide : un
    span de formule/ensemble (``$2^n - 1$``, ``$v(S) \\in \\{0, 1\\}$``) n'est
    pas une mesure enumeree -- c'est une constante mathematique. Source de FP
    documentee c.1293 sur Planners-6/GameTheory-15b.
    """
    s = content.replace("{,}", ".").replace("{\\,}", ".").replace("{\\;}", ".")
    s = s.replace("\\", " ").replace("{", " ").replace("}", " ").strip()
    # Entier ou decimal pur uniquement (apres fusion LaTeX). Tout le reste
    # (exposant ^, indice _, lettres, multi-valeurs) = formule, on jette.
    if re.fullmatch(r"-?\d+[.,]\d+|-?\d+", s):
        return s
    return ""


def _detect_prose_enumeration(text: str) -> list[float] | None:
    """Si `text` annonce une liste de N valeurs, retourne la liste parsee.

    Retourne None si le pattern d'annonce n'est pas trouvé (la cellule ne
    déclare pas une énumération, donc la catégorie #9416 ne s'applique pas).

    Cas couverts :
    (a) « N niveaux : a, b, c » -- la liste suit le mot-clé d'annonce.
    (b) « un pic à X, le reste à Y » -- formulation naturelle à 2 valeurs :
        on extrait TOUS les nombres de la phrase, dans l'ordre (l'auteur
        déclare implicitement qu'il n'y en a que 2 dans cette formulation).

    Heuristique de portee : on s'arrete au prochain signe de « fin
    d'enumeration » ou 200 chars. C'est CLAIREMENT plus restrictif que le
    paragraphe entier, sinon la cellule Conclusion d'ICT-1 (avec son cycle
    2-3-3 et l'attracteur 1) declencherait prose=6 distincts alors que
    l'auteur n'en annonce que 2.

    Filtre LaTeX : `$2{,}31$` ne doit pas être découpé en 3 tokens (`2`,
    `31`). On retire les délimiteurs LaTeX `{,}` (et la TeX thin space)
    ainsi que les dollars `$...$` avant l'extraction.
    """
    latex_clean = text.replace("{,}", ".").replace("{\\,}", ".").replace("{\\;}", ".")
    # Math LaTeX : on distingue un decimal pur ($2{,}31$ -> 2.31, a garder)
    # d'une formule/ensemble ($2^n - 1$, $v(S) \\in \\{0, 1\\}$ -> a jeter).
    # L'ancien strip `\\1` gardait le contenu des formules : le "2" de $2^n$
    # etait extrait comme un niveau enumere (FP documente c.1293 : Planners-6
    # cell[13], GameTheory-15b cell[28]). Un span qui ne se reduit pas a un
    # nombre pur apres fusion des separateurs LaTeX n'est pas une mesure.
    latex_clean = re.sub(r"\$\$(.*?)\$\$", lambda mm: " " + _latex_math_to_text(mm.group(1)) + " ", latex_clean)
    latex_clean = re.sub(r"\$([^$]*)\$", lambda mm: " " + _latex_math_to_text(mm.group(1)) + " ", latex_clean)
    m = _ENUMERATION_KEYWORDS_RE.search(latex_clean)
    if not m:
        return None
    # On extrait les nombres UNIQUEMENT APRES le mot-cle d'annonce.
    # Le `N` dans « les 3 valeurs » est avant le mot-cle et doit etre ignore.
    after = latex_clean[m.end():m.end()+200]
    # Cas (a)/(b) : on prend la PHRASE courante a partir du mot-cle.
    sentence = after.split("\n", 1)[0]
    # Domain-range descriptions (« 81 valeurs (1-9) », « valeurs 1–9 ») ne sont
    # PAS des enumerations de niveaux output : la paire `lo-hi` denote les
    # bornes de l'espace de valeurs (domaine), pas des niveaux distincts
    # observes. Une vraie enumeration #9416 liste des valeurs mesurees separees
    # par des virgules/conjonctions, jamais un intervalle entier. On retire ces
    # ranges avant extraction, sinon « 81 valeurs (1-9) » etait lu comme une
    # enumeration de 2 niveaux (1 et 9) puis comparee aux outputs globaux ->
    # FP systematique (confirme firsthand Sudoku-5-PSO cell[9], GameTheory).
    sentence = re.sub(r"\b\d{1,4}\s*[-–—]\s*\d{1,4}\b", " ", sentence)
    nums = _extract_prose_numbers(sentence)
    return nums if len(nums) >= 2 else None


def _distinct_levels(values: list[float], tol: float = RELATIVE_TOLERANCE) -> int:
    """Compte le nombre de valeurs distinctes dans `values` à tolérance près.

    Algorithme : tri O(n log n) puis groupement linéaire. Deux valeurs sont
    « même niveau » si leur ratio <= tol (et > 0).
    """
    if not values:
        return 0
    s = sorted(values)
    count = 1
    for v in s[1:]:
        base = max(abs(s[count - 1]), abs(v))
        if base == 0:
            # 0 == 0 -> même niveau.
            continue
        if abs(v - s[count - 1]) / base > tol:
            count += 1
    return count


def analyze_notebook(path: str | os.PathLike) -> NotebookAlignment:
    """Analyse l'alignement prose <-> outputs pour un notebook."""
    p = Path(path)
    try:
        nb = json.loads(p.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, OSError) as exc:
        return NotebookAlignment(
            path=str(path), total_findings=0, findings=[],
            error=f"{type(exc).__name__}: {exc}",
        )
    cells = nb.get("cells") or []
    n_md = sum(1 for c in cells if c.get("cell_type") == "markdown")
    n_code = sum(1 for c in cells if c.get("cell_type") == "code")
    output_vals: list[float] = []
    prose_vals_per_cell: list[tuple[int, str, list[float]]] = []
    for i, c in enumerate(cells):
        ctype = c.get("cell_type")
        source = c.get("source") or []
        if isinstance(source, list):
            text = "".join(source)
        else:
            text = str(source)
        if ctype == "code":
            for out in (c.get("outputs") or []):
                output_vals.extend(_extract_output_numbers(out))
        elif ctype == "markdown":
            nums = _extract_prose_numbers(text)
            if nums:
                prose_vals_per_cell.append((i, text, nums))
    # Alignement : pour chaque cellule markdown, pour chaque nombre,
    # cherche le plus proche dans output_vals.
    findings: list[AlignmentFinding] = []
    for cell_idx, text, nums in prose_vals_per_cell:
        # FP class 2 (#9995) : prose d'enonce d'exercice precedant immediatement
        # un stub. La cellule code suivante est un placeholder ("Exercice a
        # completer") sans sortie numerique -> les nombres de l'enonce sont les
        # donnees du probleme, pas des mesures a verifier. On saute l'emission
        # de MISSING_FROM_OUTPUTS pour cette cellule d'enonce.
        if cell_idx + 1 < len(cells) and _is_stub_code_cell(cells[cell_idx + 1]):
            continue
        # Tronque le texte pour le rapport (60 premiers chars non vides).
        snippet = text.strip().splitlines()
        snippet = next((ln.strip() for ln in snippet if ln.strip()), "")[:120]
        # Gate anti-bruit (EPIC #9768 Phase 0) : on collecte d'abord les
        # orphelins de cette cellule. Pour les cellules DENSES (>= MIN nombres
        # prose), on n'emet QUE si la majorite des nombres sont orphelins
        # (ratio >= seuil) -- une cellule avec 1 orphelin sur 10 = reference
        # croisee (bruit), une cellule avec 5/10 = derive authentique. Les
        # cellules clairsemes (1-2 nombres) sont preservees : une seule
        # mesure manquante ("Sharpe = 0.512") reste un signal valide.
        orphans: list[float] = []
        for v in nums:
            closest = _closest_output(v, output_vals)
            if closest is None:
                orphans.append(v)
        if len(nums) >= MISSING_FROM_OUTPUTS_CELL_MIN:
            ratio = len(orphans) / len(nums)
            if ratio < MISSING_FROM_OUTPUTS_CELL_RATIO:
                continue  # bruit : pas assez d'orphelins sur cette cellule dense
        # Emet les orphelins survivants.
        for v in orphans:
            # FP class 4 (#9995) : reference bibliographique (volume:page-page).
            # Un orphelin qui est le volume ou une page d'une citation n'est
            # pas une mesure manquante -- skip (conservateur : exige contexte
            # biblio, cf ``_is_bibliographic_reference``).
            if _is_bibliographic_reference(v, text):
                continue
            # FP class 5 (#9998) : reference croisee vers un autre notebook de
            # la serie (lien markdown [N.M](fichier.ipynb)). L'indice du notebook
            # pointe n'est pas une mesure -> skip (SAFE par construction, cf
            # ``_is_notebook_cross_reference``).
            if _is_notebook_cross_reference(v, text):
                continue
            findings.append(AlignmentFinding(
                notebook=str(path),
                cell_index=cell_idx,
                cell_kind="markdown",
                category="MISSING_FROM_OUTPUTS",
                prose_text=snippet,
                prose_number=v,
                closest_output_number=None,
                tolerance_used="none",
            ))
    # Tour 2 : MISSING_FROM_PROSE_ENUMERATION (#9416).
    # Pour chaque cellule markdown qui annonce une énumération de N niveaux,
    # compare N au nombre de niveaux distincts dans output_vals.
    if output_vals:
        output_levels = _distinct_levels(output_vals)
        for cell_idx, text, nums in prose_vals_per_cell:
            enum = _detect_prose_enumeration(text)
            if not enum:
                continue
            prose_levels = _distinct_levels(enum)
            if prose_levels == 0 or output_levels <= prose_levels:
                continue
            # Trouve la valeur output « orpheline » la plus loin de la liste prose.
            orphan = None
            orphan_dist = -1.0
            for ov in output_vals:
                closest_p = min(enum, key=lambda p: abs(p - ov))
                base = max(abs(closest_p), abs(ov))
                if base == 0:
                    continue
                dist = abs(ov - closest_p) / base
                if dist > orphan_dist:
                    orphan_dist = dist
                    orphan = ov
            snippet = text.strip().splitlines()
            snippet = next((ln.strip() for ln in snippet if ln.strip()), "")[:120]
            findings.append(AlignmentFinding(
                notebook=str(path),
                cell_index=cell_idx,
                cell_kind="markdown",
                category="MISSING_FROM_PROSE_ENUMERATION",
                prose_text=snippet,
                prose_number=float(prose_levels),
                closest_output_number=orphan if orphan is not None else None,
                tolerance_used="enumeration-vs-outputs",
                details=(
                    f"prose enumere {prose_levels} niveaux distincts, "
                    f"outputs exhibent {output_levels} niveaux distincts "
                    f"(orphan={orphan:.4g}, dist={orphan_dist:.1%})"
                ),
            ))
    return NotebookAlignment(
        path=str(path),
        total_findings=len(findings),
        findings=findings,
        n_prose_numbers=sum(len(v) for _, _, v in prose_vals_per_cell),
        n_output_numbers=len(output_vals),
        n_markdown_cells=n_md,
        n_code_cells=n_code,
    )


# --------------------------------------------------------------------------- #
#  Walk full-corpus
# --------------------------------------------------------------------------- #


DEFAULT_INCLUDE_GLOBS = ("*.ipynb",)
DEFAULT_EXCLUDE_DIRS = (
    "_archive", "_archives", "archive", "archives",
    "node_modules", ".git", "__pycache__",
)


def iter_notebooks(
    root: Path,
    include_globs: tuple[str, ...] = DEFAULT_INCLUDE_GLOBS,
    exclude_dirs: tuple[str, ...] = DEFAULT_EXCLUDE_DIRS,
) -> Iterable[Path]:
    """Yield notebook paths under root, honoring exclusion dirs."""
    if not root.exists():
        return
    for dirpath, dirnames, filenames in os.walk(root):
        # Prune excluded dirs in-place so os.walk skips them.
        dirnames[:] = [d for d in dirnames if d not in exclude_dirs]
        for fn in filenames:
            if any(fn.endswith(g.lstrip("*")) for g in include_globs):
                yield Path(dirpath) / fn


def scan_corpus(
    root: str | os.PathLike,
    include_globs: tuple[str, ...] = DEFAULT_INCLUDE_GLOBS,
    exclude_dirs: tuple[str, ...] = DEFAULT_EXCLUDE_DIRS,
) -> list[NotebookAlignment]:
    """Scan a corpus root, return list of NotebookAlignment."""
    root_path = Path(root)
    results: list[NotebookAlignment] = []
    for nb_path in iter_notebooks(root_path, include_globs, exclude_dirs):
        results.append(analyze_notebook(nb_path))
    return results


# --------------------------------------------------------------------------- #
#  Reporting
# --------------------------------------------------------------------------- #


def render_text_report(results: list[NotebookAlignment]) -> str:
    """Format results as markdown text."""
    total_findings = sum(r.total_findings for r in results)
    n_pathological = sum(1 for r in results if r.is_pathological)
    by_cat: dict[str, int] = {}
    for r in results:
        for f in r.findings:
            by_cat[f.category] = by_cat.get(f.category, 0) + 1
    lines: list[str] = []
    lines.append(f"Total notebooks analyses : {len(results)}")
    lines.append(f"Notebooks avec >= 1 finding : {n_pathological}")
    lines.append(f"Total findings : {total_findings}")
    if by_cat:
        lines.append("Repartition par categorie :")
        for k, v in sorted(by_cat.items()):
            lines.append(f"  - {k} : {v}")
    lines.append("")
    lines.append("## Notebooks avec findings")
    lines.append("")
    lines.append("| Notebook | Findings | n_prose | n_outputs | Top finding |")
    lines.append("|---|---|---|---|---|")
    for r in sorted(results, key=lambda x: -x.total_findings):
        if r.total_findings == 0:
            continue
        top = r.findings[0]
        snippet = f"{top.category}: {top.prose_number:.4g} (cell[{top.cell_index}])"
        lines.append(
            f"| `{os.path.basename(r.path)}` | {r.total_findings} | "
            f"{r.n_prose_numbers} | {r.n_output_numbers} | {snippet} |"
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
        help="Mode CI : exit 1 si >= 1 finding, exit 2 si usage/erreur.",
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
        results = [analyze_notebook(nb_path)]
    else:
        results = scan_corpus(root)
        if args.limit > 0:
            results = results[:args.limit]
    if args.json_out:
        Path(args.json_out).write_text(json.dumps([
            {
                "path": r.path,
                "total_findings": r.total_findings,
                "n_prose_numbers": r.n_prose_numbers,
                "n_output_numbers": r.n_output_numbers,
                "n_markdown_cells": r.n_markdown_cells,
                "n_code_cells": r.n_code_cells,
                "findings": [
                    {
                        "cell_index": f.cell_index,
                        "category": f.category,
                        "prose_number": f.prose_number,
                        "closest_output_number": f.closest_output_number,
                        "prose_text": f.prose_text,
                    }
                    for f in r.findings
                ],
                "error": r.error,
            }
            for r in results
        ], indent=2, ensure_ascii=False), encoding="utf-8")
    print(render_text_report(results))
    if args.check and any(r.is_pathological for r in results):
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
