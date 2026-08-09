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
    r"intervalle?\s+de\s+confiance|IC\s+\d|probabilit[ée]?)\b",
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
    r"canal\s+de\s+paiement|payment\s+channel)\b",
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
    r"|\bdur[ée]e\s+(?:cible|totale|maximale|optimale)\b"
    r"|\bdur[ée]e\s+de\s+la\s+vid[ée]o\b"
    r"|\bYouTube\s+Shorts\b"
    r"|\bmodule\s+de\s+cours\b)",
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
    r"|\d+\s*(?:min(?:utes?)?|sec(?:ondes?)?|h(?:eures)?)\s*\(\s*(?:lecture|cours|travaux\s+pratiques|tp\b))",
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
    # Test 2 : borne superieure '< N' ou '<= N' -- le '<' est en fin de fenetre.
    if re.search(r"<\s*=?\s*\d\s*$", window):
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
    return bool(re.search(r"[~≈]\s*$", window))


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
    # Frontiere FP (frontier issue) : cout d'action dans une table de plan.
    # La duree est le RESULTAT d'une arithmetique « N + M = K unit » (ex
    # Planners-8-Temporal cell[37] « 5 + 4 = 9 min » = duree d'une livraison
    # drone). C'est un parametre DETERMINISTE du domaine planifie, pas une
    # duree machine. Le motif est precis (un vrai wallclock ne se rend presque
    # jamais comme une somme explicite `a + b = c unit`) -- Sudoku-13 (controle
    # positif) n'a aucune ligne de cette forme, donc reste detecte.
    if re.search(r"\d+\s*\+\s*\d+\s*=\s*\d+\s*(?:min(?:utes?)?|sec(?:ondes?)?|s\b|h(?:eures)?)", line):
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


def _scan_notebook(nb_path: Path) -> list[dict]:
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
            text=True,
        ).strip()
        if out:
            return Path(out).resolve()
    except (OSError, subprocess.CalledProcessError, subprocess.SubprocessError):
        pass
    return Path(__file__).resolve().parents[2]


def _collect_targets(args: argparse.Namespace) -> list[Path]:
    """Resout la liste des notebooks a scanner depuis la CLI."""
    root = _repo_root()
    if args.all or args.json or args.check:
        # Cible canonique : notebooks pedagogiques. Les READMEs et `assets/`
        # sont exclus -- le scope de #10158 est uniquement les ``.ipynb``.
        candidates = sorted(root.glob("MyIA.AI.Notebooks/**/*.ipynb"))
    elif args.paths:
        candidates = []
        for p in args.paths:
            pp = Path(p)
            if pp.is_file() and pp.suffix == ".ipynb":
                candidates.append(pp)
            elif pp.is_dir():
                candidates.extend(sorted(pp.rglob("*.ipynb")))
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
        help="Filtre categorie de sortie (defaut: wallclock = cible drainage).",
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
        findings = _scan_notebook(nb_path)
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
        print(json.dumps(out, ensure_ascii=False, indent=2))
    else:
        # Mode TSV lisible (par defaut : wallclock = cible drainage).
        cat_filter = None if args.category == "all" else args.category
        print(f"# check_machine_dep_timing -- scanned={len(targets)}")
        print(f"# wallclock={wallclock_count} distribution_param={distribution_count} "
              f"domain_quantity={domain_quantity_count} ambiguous={ambiguous_count}")
        for nb_rel, findings in sorted(all_findings.items()):
            for f in findings:
                if cat_filter and f["category"] != cat_filter:
                    continue
                print(f"{nb_rel}\tcell[{f['cell_index']}]\t{f['snippet']}\t{f['category']}\t{f['line'][:120]}")

    # Mode advisory par defaut (exit 0). --check reserved pour le futur quand
    # le stock wallclock sera draine (cf. condition de sortie de #9434).
    if args.check and wallclock_count > 0:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
