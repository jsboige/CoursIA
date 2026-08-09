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

Note : `ambiguous=0` est structural (defaut conservateur = wallclock). Aucun
finding ne reste ambigue apres la passe 1 -- le defaut de `_categorize`
classe toute ligne sans mot-cle en wallclock. La categorie `ambiguous`
reste dans la taxonomie pour compatibilite (cf. migrations futures) mais
n'est pas emise en pratique avec l'heuristique courante.
"""

from __future__ import annotations

import argparse
import json
import re
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
    r"\|\s*\d+\s*(?:-\s*\d+)?\s*(?:min(?:utes?)?|sec(?:ondes?)?|h(?:eures?)?)\s*\|)",
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

    Strategie en 2 passes (CHANGES_REQUESTED #10162 c.1331+59) :

    1. **Passe ligne** : pour chaque ligne markdown, on applique les exemptions
       (pacing pedagogique, tilde, fourchette/borne) et on classifie selon le
       contexte de la ligne (wallclock / distribution_param / ambiguous).
    2. **Passe cellule** : si une cellule porte >=1 finding ``distribution_param``,
       tous les autres findings ``wallclock`` de la meme cellule basculent en
       ``domain_quantity`` -- l'unite de temps est le sujet du modele, pas une
       mesure d'execution (cf. FP-2 sur Infer-2-Gaussian-Mixtures).
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

    return findings


def _collect_targets(args: argparse.Namespace) -> list[Path]:
    """Resout la liste des notebooks a scanner depuis la CLI."""
    root = Path(__file__).resolve().parents[2]
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
        print("Aucun notebook a scanner.", file=sys.stderr)
        return 0

    all_findings: dict[str, list[dict]] = {}
    wallclock_count = 0
    distribution_count = 0
    ambiguous_count = 0
    domain_quantity_count = 0
    for nb_path in targets:
        rel = str(nb_path)
        # Afficher le chemin relatif a la racine du depot si possible.
        try:
            rel = str(nb_path.resolve().relative_to(Path(__file__).resolve().parents[2]))
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
