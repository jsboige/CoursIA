"""scan_knots_extracts.py -- voie (B) prevention KNOTS #21007.

Issue #21007 a documente 3 classes de defaut relevees sur KNOTS-01 :
  - classe 1 : stale in-cell path (ref. PR #20134 V5.3, hook pre-commit
    ``knots-extracts`` deja livre en c.1747 / PR #21364)
  - classe 2 : stale identite (la cellule 16 §5 de KNOTS-01 disait
    "FigureEight.lean (noeud 8_1)" alors que le fichier modelise 4_1)
  - classe 3 : stale TODO (la cellule 23 §4.2 de KNOTS-01 affirmait que
    le PD-code de 11n102 n'etait pas encore entre, alors que
    ``knot_11n102_diagram`` est defini au head, avec ``numEdges := 22``)

Le present script couvre les classes 2 et 3 en cross-checkant chaque
cellule de chaque carnet KNOTS contre la verite du depot (``main``
courant). Le scan est *read-only* : il ne modifie rien, il rend la
liste des findings au format ``path:cell_NN: STALE_<class> <detail>``
et exit 1 sur tout finding, exit 0 sinon.

Garde anti-recit-V4 : le script n'utilise pas le recit V4 de la PR #20134
(qui affirmait a tort un refactor manquant ``Lean/KNOTS-01-...`` vers
``SymbolicAI/Lean/KNOTS/...``). Les defauts releves sont strictement
les 3 classes documentees par le body V5.3 de la PR #20134 (mesure
c.1419-c.1421).

Usage :
  python scripts/notebook_tools/scan_knots_extracts.py
  python scripts/notebook_tools/scan_knots_extracts.py --notebook <path>
  python scripts/notebook_tools/scan_knots_extracts.py --repo-root <path>

Sortie : une ligne par finding, ou rien si main est propre.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Iterable

# ---------------------------------------------------------------------------
# Constantes -- ground truth tirée du depot (classe 2 + classe 3)
# ---------------------------------------------------------------------------

# Classe 2 : FigureEight.lean modelise le noeud 4_1 (le 8_1 est la famille
# 2-twist de 4_1, pas le sujet du fichier). Header du module (l. 2) :
#   "Knots.FigureEight -- Invariants du noeud en huit sur son code PD plan"
# Le pattern ground truth cherche "4_1" (ou "noeud en huit" / "figure-eight")
# dans le fichier ; un finding = la cellule parle de 8_1 comme si c'etait
# le sujet du fichier.
FIGURE_EIGHT_GROUND_TRUTH = "4_1"
FIGURE_EIGHT_FILE = (
    "MyIA.AI.Notebooks/SymbolicAI/Lean/KNOTS/knot_lean/Knots/FigureEight.lean"
)

# Classe 3 : Lidman.lean definit knot_11n102_diagram (l. 67) avec
# numEdges := 22 (l. 81), et knot_11n102 (l. 83) dont diagram :=
# knot_11n102_diagram. Le PD-code EST entre au head.
# Un finding = la cellule affirme que 11n102_diagram "n'est pas entre" /
# "manquant" / "TODO PD-code" sans caveat "perime par rapport au head".
LIDMAN_FILE = (
    "MyIA.AI.Notebooks/SymbolicAI/Lean/KNOTS/knot_lean/Knots/Lidman.lean"
)

# Pattern qui declenche la classe 2 sur une cellule : la cellule mentionne
# "FigureEight" (le fichier) et un numero de noeud qui n'est PAS 4_1.
FIGURE_EIGHT_CELL_RE = re.compile(
    r"FigureEight(?:\.lean)?\b",
)
NODE_NUM_RE = re.compile(r"\b([0-9]+)_([0-9]+)\b")
WRONG_FIGURE_EIGHT_NUMBERS = {"8_1", "8_2", "8_19", "8_20", "8_21"}

# Pattern qui declenche la classe 3 sur une cellule : la cellule parle
# de 11n102_diagram (ou PD-code de 11n102) et porte un des marqueurs
# d'absence ("n'est pas entre", "manquant", "pas encore", "TODO PD-code",
# "PD-code from KnotInfo" sans caveat).
LIDMAN_CELL_RE = re.compile(
    r"\b(11n102_diagram|11n102|PD-code (?:de |du )?11n102|"
    r"k11n102_diagram|unknotting[_ ]?11n102)\b",
    re.IGNORECASE,
)
STALE_TODO_MARKERS = [
    # "pas encore entre/defini/..." (avec ou sans accent sur le participe
    # passe -- "entre" est une graphie fautive mais le scan la capte pour
    # eviter de la laisser passer ; on accepte "entre" (sans accent) ;
    # on refuse "entree" / "entrer" (mots distincts))
    re.compile(r"\bpas\s+(?:encore\s+)?(?:entré|défini|fourni|codé|implémenté|entr[éé]?|entr(?!e))", re.IGNORECASE),
    # "n'est pas entre/defini/..." (verbe entre n' et pas)
    re.compile(r"\b(n'|n’)\s*(est|était|a)\s+pas\s+(?:encore\s+)?(?:entré|défini|fourni|codé|implémenté|entr[éé]?|entr(?!e))", re.IGNORECASE),
    re.compile(r"\bmanquant\b", re.IGNORECASE),
    re.compile(r"\bà\s+entrer\b", re.IGNORECASE),
    re.compile(r"TODO\s*:?\s*PD-code", re.IGNORECASE),
    re.compile(r"PD-code\s+from\s+KnotInfo\b", re.IGNORECASE),
    re.compile(r"diagram\s*:=\s*sorry\s*--\s*TODO", re.IGNORECASE),
]
# Caveat qui annule un finding classe 3 : la cellule reconnait explicitement
# la perimation par rapport au head (note "depuis la redaction", "au head",
# "l'etat actuel contredit le TODO", etc.).
STALE_TODO_CAVEAT_RE = re.compile(
    r"("
    r"depuis\s+la\s+rédaction|au\s+head|état\s+actuel|"
    r"périmé|extrait\s+statique\s+ci-dessous\s+conserve|"
    r"réfutation\s+du\s+TODO|cross.?check"
    r")",
    re.IGNORECASE,
)


# ---------------------------------------------------------------------------
# Utilitaires notebook
# ---------------------------------------------------------------------------

def iter_notebook_cells(notebook_path: Path) -> Iterable[tuple[int, str, str]]:
    """Yield (cell_index, cell_type, source) pour chaque cellule d'un .ipynb.

    Ignore les cellules vides. Sortie en lecture seule, ne mute pas le
    notebook (le scan est read-only par construction).
    """
    with notebook_path.open("r", encoding="utf-8") as f:
        nb = json.load(f)
    cells = nb.get("cells", [])
    for idx, cell in enumerate(cells):
        cell_type = cell.get("cell_type", "")
        src_list = cell.get("source", [])
        if isinstance(src_list, list):
            src = "".join(src_list)
        else:
            src = str(src_list)
        if not src.strip():
            continue
        yield idx, cell_type, src


# ---------------------------------------------------------------------------
# Scans
# ---------------------------------------------------------------------------

def scan_classe2(
    notebook_path: Path,
    cell_idx: int,
    source: str,
    repo_root: Path,
) -> list[str]:
    """Verifie classe 2 (stale identite FigureEight = 4_1)."""
    findings: list[str] = []
    if not FIGURE_EIGHT_CELL_RE.search(source):
        return findings
    # ground truth : le header du module FigureEight.lean doit contenir 4_1
    # (defensive : si le fichier n'existe pas, on ne peut pas conclure
    # -- on ne signale pas, on laisse un autre garde le capter).
    gt = repo_root / FIGURE_EIGHT_FILE
    if not gt.exists():
        return findings
    gt_text = gt.read_text(encoding="utf-8")
    gt_has_4_1 = bool(re.search(r"\b4_1\b", gt_text)) or "nœud en huit" in gt_text
    if not gt_has_4_1:
        # Le ground truth lui-meme est casse -- on ne sait pas conclure.
        return findings
    for line_no, line in enumerate(source.splitlines(), start=1):
        if not FIGURE_EIGHT_CELL_RE.search(line):
            continue
        for m in NODE_NUM_RE.finditer(line):
            num = f"{m.group(1)}_{m.group(2)}"
            if num in WRONG_FIGURE_EIGHT_NUMBERS:
                findings.append(
                    f"{notebook_path}:cell_{cell_idx:02d}:L{line_no}:"
                    f" STALE_IDENTITY (classe 2) -- cellule cite FigureEight"
                    f" comme etant le noeud {num} ; ground truth (header "
                    f"FigureEight.lean) = {FIGURE_EIGHT_GROUND_TRUTH} (4_1)"
                )
    return findings


def scan_classe3(
    notebook_path: Path,
    cell_idx: int,
    source: str,
    repo_root: Path,
) -> list[str]:
    """Verifie classe 3 (stale TODO knot_11n102_diagram)."""
    findings: list[str] = []
    if not LIDMAN_CELL_RE.search(source):
        return findings
    # ground truth : knot_11n102_diagram est defini et porte numEdges := 22
    gt = repo_root / LIDMAN_FILE
    if not gt.exists():
        return findings
    gt_text = gt.read_text(encoding="utf-8")
    has_diagram = bool(re.search(r"\bdef\s+knot_11n102_diagram\b", gt_text))
    has_numedges = bool(re.search(r"numEdges\s*:=\s*22\b", gt_text))
    if not (has_diagram and has_numedges):
        # Le ground truth n'est pas conforme -- on ne sait pas conclure.
        return findings
    for line_no, line in enumerate(source.splitlines(), start=1):
        if not LIDMAN_CELL_RE.search(line):
            continue
        # Caveat sur la meme ligne (ou cellule) annule le finding.
        if STALE_TODO_CAVEAT_RE.search(line) or STALE_TODO_CAVEAT_RE.search(source):
            continue
        for marker in STALE_TODO_MARKERS:
            if marker.search(line):
                findings.append(
                    f"{notebook_path}:cell_{cell_idx:02d}:L{line_no}:"
                    f" STALE_TODO (classe 3) -- cellule affirme une absence"
                    f" sur 11n102_diagram ; ground truth (Lidman.lean "
                    f"l. 67) = 'def knot_11n102_diagram' avec "
                    f"numEdges := 22 (l. 81)"
                )
                break
    return findings


# ---------------------------------------------------------------------------
# Orchestration
# ---------------------------------------------------------------------------

def default_knots_dir(repo_root: Path) -> Path:
    return repo_root / "MyIA.AI.Notebooks" / "SymbolicAI" / "Lean" / "KNOTS"


def discover_knots_notebooks(knots_dir: Path) -> list[Path]:
    if not knots_dir.exists():
        return []
    return sorted(p for p in knots_dir.glob("*.ipynb"))


def scan_notebook(
    notebook_path: Path,
    repo_root: Path,
) -> list[str]:
    findings: list[str] = []
    try:
        cells = list(iter_notebook_cells(notebook_path))
    except Exception as e:
        return [f"{notebook_path}:load_error: lecture du .ipynb impossible ({e})"]
    for cell_idx, _cell_type, source in cells:
        findings.extend(scan_classe2(notebook_path, cell_idx, source, repo_root))
        findings.extend(scan_classe3(notebook_path, cell_idx, source, repo_root))
    return findings


def main() -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Voie (B) prevention KNOTS #21007 : scan read-only des classes "
            "2 (stale identite FigureEight) et 3 (stale TODO knot_11n102)."
        ),
    )
    parser.add_argument(
        "--notebook",
        type=Path,
        default=None,
        help="Cible un carnet unique (par defaut : tous les KNOTS/*.ipynb).",
    )
    parser.add_argument(
        "--repo-root",
        type=Path,
        default=None,
        help="Racine du depot (par defaut : grand-parent du script).",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Sortie JSON structuree (par defaut : une ligne par finding).",
    )
    args = parser.parse_args()

    repo_root = args.repo_root
    if repo_root is None:
        # scripts/notebook_tools/scan_knots_extracts.py -> 2 niveaux au-dessus
        repo_root = Path(__file__).resolve().parent.parent.parent
    repo_root = repo_root.resolve()

    if args.notebook is not None:
        notebooks = [args.notebook.resolve()]
    else:
        notebooks = discover_knots_notebooks(default_knots_dir(repo_root))

    if not notebooks:
        print("scan_knots_extracts: 0 carnet KNOTS trouve, scan vide", file=sys.stderr)
        return 0

    all_findings: list[str] = []
    for nb in notebooks:
        all_findings.extend(scan_notebook(nb, repo_root))

    if args.json:
        out = {
            "scanned_notebooks": [str(n) for n in notebooks],
            "findings": all_findings,
            "exit_code": 0 if not all_findings else 1,
        }
        print(json.dumps(out, ensure_ascii=False, indent=2))
    else:
        for line in all_findings:
            print(line)
        if not all_findings:
            print(
                f"scan_knots_extracts: {len(notebooks)} carnet(s) scanne(s), "
                f"0 finding (main propre, classes 2 + 3)",
                file=sys.stderr,
            )

    return 0 if not all_findings else 1


if __name__ == "__main__":
    raise SystemExit(main())
