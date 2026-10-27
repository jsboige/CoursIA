"""scan_knots_extracts.py -- voie (B) prevention KNOTS #21007.

Issue #21007 a documente 3 classes de defaut relevees sur KNOTS-01 :
  - classe 1 : stale in-cell path -- hook pre-commit ``knots-extracts``
    (``check_knots_extracts.py``, livre en c.1747 / PR #21364)
  - classe 2 : stale identite -- une cellule attribue a un module Lean une
    identite de noeud que ce module ne modelise pas (cas fondateur : la
    cellule 16 de KNOTS-01 disait "FigureEight.lean (noeud 8_1)" alors que
    le module modelise 4_1)
  - classe 3 : stale TODO -- une cellule affirme qu'un element n'est pas
    encore entre alors qu'il est defini au head (cas fondateur : la cellule
    23 de KNOTS-01 declarait le PD-code de 11n102 "pas encore entre" alors
    que ``knot_11n102_diagram`` est defini, avec ``numEdges := 22``)

CE QUE CE SCRIPT EST (c.478). La premiere version ne savait detecter que
les deux instances fondatrices, cablees en dur (``FIGURE_EIGHT_FILE``,
``LIDMAN_FILE``) : elle rendait 0 finding sur un corpus propre et ne
pouvait, par construction, jamais en rendre un autre. Un organe qui ne
peut que rejouer son propre cas fondateur est un test de regression, pas
un detecteur. Cette version derive la verite du depot lui-meme et applique
deux regles generales (voir ``scan_classe2`` / ``scan_classe3``) : les
deux instances fondatrices restent couvertes, et le sont par la regle.

Le scan est *read-only* : il ne modifie rien. Il rend une ligne par finding
au format ``path:cell_NN:Lxx: STALE_<CLASSE> <detail>`` et exit 1.

Usage :
  python scripts/notebook_tools/scan_knots_extracts.py
  python scripts/notebook_tools/scan_knots_extracts.py --notebook <path>
  python scripts/notebook_tools/scan_knots_extracts.py --json
  # hook pre-commit : les carnets modifies arrivent en arguments positionnels
  python scripts/notebook_tools/scan_knots_extracts.py --changed a.ipynb b.ipynb
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Iterable

# ---------------------------------------------------------------------------
# Regles de detection
# ---------------------------------------------------------------------------

# Une reference a un module Lean, par son nom de fichier. On capture le
# basename (``FigureEight.lean`` -> ``FigureEight``) ; un chemin complet est
# capture par le meme groupe.
LEAN_MODULE_RE = re.compile(r"\b([A-Z][A-Za-z0-9_]*)\.lean\b")

# Forme NUE du meme nom, sans l'extension ("see FigureEight (8_2)"). On ne
# l'accepte que si le token EST un module connu de l'arbre (``truth.defs``) :
# sans ce filtre, tout mot capitalise en prose deviendrait une reference.
# Mesure (c.478) : sur le corpus reel, accepter la forme nue en plus de
# ``.lean`` rend 0 finding supplementaire -- donc aucun cout, et un rappel
# plus large.
BARE_MODULE_RE = re.compile(r"\b([A-Z][A-Za-z0-9_]*)\b")

# Un numero de noeud au format KnotInfo/SnapPy (``4_1``, ``8_19``, ``11n102``
# n'est PAS de cette forme -- c'est un nom de noeud, pas un couple).
NODE_NUM_RE = re.compile(r"\b(\d{1,2})_(\d{1,2})\b")

# Un identifiant Lean "metier". Le underscore est le discriminant mesure :
# sur ce corpus, une regle acceptant n'importe quel identifiant declaration
# rend 2 faux positifs sur 2 candidats (``existe`` et ``trefoil`` sont des
# noms de ``def`` ailleurs dans l'arbre et des mots ordinaires en prose).
# Le premier caractere peut etre un CHIFFRE : un nom de noeud s'ecrit
# ``11n102_diagram`` (l'identifiant Lean ne peut pas commencer par un
# chiffre, mais la reference en prose le fait couramment). Une regex
# exigeant une lettre initiale manquait cette forme -- deux tests
# d'heritage l'ont attrapee, c'est une perte de rappel silencieuse.
METIER_IDENT_RE = re.compile(r"\b([a-z0-9][a-z0-9]*_[a-z0-9_]+)\b")

# Discriminants du repli de ligne (classe 2, cf. ``_is_sentence_wrap``).
_SENTENCE_END_RE = re.compile(r"[.;:!?]\s*$")
_LIST_ENTRY_RE = re.compile(r"^\s*(?:[-*+•]\s|\||\d+[.)]\s)")

# Marqueurs d'absence (classe 3). Une cellule qui les porte affirme qu'un
# element manque ; le ground truth est la declaration reelle au head.
ABSENCE_MARKERS: tuple[re.Pattern[str], ...] = (
    re.compile(r"\bpas\s+(?:encore\s+)?(?:entr[ée]|d[ée]fini|fourni|cod[ée]|impl[ée]ment[ée])", re.I),
    re.compile(r"n['’]\s*(?:est|était|a)\s+pas\s+(?:encore\s+)?(?:entr[ée]|d[ée]fini|fourni|cod[ée]|impl[ée]ment[ée])", re.I),
    re.compile(r"\bmanquant\b", re.I),
    # La classe visee est « absence affirmee », pas la formulation de son
    # instance fondatrice. Mesure c.478 : quatre formulations reelles
    # rendaient rc 0 -- « manque encore », « : TODO », « reste a
    # implementer », « n'existe pas encore ». Un marqueur large garde la
    # regle a la largeur de sa classe (cf. #21007).
    re.compile(r"\bmanqu(?:e|ent|ait|er|é)\b", re.I),
    re.compile(r"n['’]\s*existe\s+pas", re.I),
    re.compile(r"reste\s+[àa]\s+(?:[êe]tre\s+)?impl[ée]ment[ée]", re.I),
    # ``TODO`` nu subsume ``TODO: PD-code`` ; la forme etroite est conservee
    # pour que l'instance fondatrice reste lisible dans le fichier.
    re.compile(r"\bTODO\b"),
    re.compile(r"TODO\s*:?\s*PD-code", re.I),
    re.compile(r"diagram\s*:=\s*sorry\s*--\s*TODO", re.I),
    re.compile(r"\bnot\s+yet\b", re.I),
    re.compile(r"\bmissing\b", re.I),
)

# Caveat qui annule un finding de classe 3 : la cellule reconnait
# explicitement la perimation par rapport au head.
#
# PORTEE -- le caveat porte sur la LIGNE du finding, ou sur l'IDENTIFIANT
# qu'il a trouve, jamais sur la cellule entiere. Mesure c.478 : a portee
# cellule, un « un autre passage est perime » ecrit ailleurs avalait un vrai
# TODO perime -- la neutralisation etait a portee de cellule la ou le
# finding est a portee de ligne. Le body revendique le cadrage ligne : le
# code le suit.
STALE_TODO_CAVEAT_RE = re.compile(
    r"(depuis\s+la\s+r[ée]daction|au\s+head|état\s+actuel|p[ée]rim[ée]|"
    r"r[ée]futation\s+du\s+TODO|cross.?check)",
    re.I,
)

# Dossiers de dependances vendorees : un nom de ``def`` y est hors-sujet
# (Mathlib entier), et le compter gonfle la surface de faux positifs.
_VENDORED_DIRS = frozenset({".lake", "_peters", "node_modules", ".git"})


# ---------------------------------------------------------------------------
# Verite du depot
# ---------------------------------------------------------------------------

# Longueur minimale d'un alias de suffixe. Un suffixe court ("diagram",
# "invariant") n'est pas un identifiant metier : la regex ne l'extrait pas
# de toute facon (elle exige un underscore), mais la borne garde la regle
# lisible si elle change.
_MIN_ALIAS_LEN = 8


def _suffix_aliases(name: str) -> set[str]:
    """Suffixes de ``name`` alignes sur un underscore.

    ``knot_11n102_diagram`` -> {"11n102_diagram", "diagram"} ; la prose
    ecrit couramment la premiere forme sans le prefixe de module.
    """
    parts = name.split("_")
    out: set[str] = set()
    for i in range(1, len(parts)):
        suffix = "_".join(parts[i:])
        if len(suffix) >= _MIN_ALIAS_LEN:
            out.add(suffix)
    return out


@dataclass
class LeanTruth:
    """Ce que l'arbre Lean declare reellement, par module.

    ``defs[module]``  : noms declares (def/theorem/lemma/abbrev/structure/
                        inductive) dans ``<module>.lean``.
    ``nodes[module]`` : numeros de noeud (``N_M``) cites dans le module.
    ``all_defs``      : union, pour la classe 3.
    """

    defs: dict[str, set[str]] = field(default_factory=dict)
    nodes: dict[str, set[str]] = field(default_factory=dict)
    all_defs: set[str] = field(default_factory=set)
    # Suffixes alignes sur un underscore des noms declares : la prose designe
    # souvent ``11n102_diagram`` la ou le head declare ``knot_11n102_diagram``.
    # Sans ces alias, la regle rate cette forme -- perte de rappel attrapee
    # par deux tests d'heritage de la v1 (qui detectaient ``11n102`` par
    # contenu, pas par identifiant).
    aliases: set[str] = field(default_factory=set)
    modules_read: int = 0

    @classmethod
    def build(cls, lean_root: Path) -> "LeanTruth":
        truth = cls()
        if not lean_root.exists():
            return truth
        for f in sorted(lean_root.rglob("*.lean")):
            if _VENDORED_DIRS & set(f.parts):
                continue
            try:
                text = f.read_text(encoding="utf-8", errors="replace")
            except OSError:
                continue
            truth.modules_read += 1
            declared = set(
                re.findall(
                    r"^\s*(?:noncomputable\s+|private\s+|protected\s+|partial\s+)?"
                    r"(?:def|theorem|lemma|abbrev|structure|inductive)\s+"
                    r"([A-Za-z_][A-Za-z0-9_']*)",
                    text,
                    re.M,
                )
            )
            truth.defs[f.stem] = declared
            truth.all_defs |= declared
            truth.nodes[f.stem] = {f"{a}_{b}" for a, b in NODE_NUM_RE.findall(text)}
        for name in truth.all_defs:
            truth.aliases |= _suffix_aliases(name)
        truth.aliases -= truth.all_defs
        return truth


# ---------------------------------------------------------------------------
# Utilitaires notebook
# ---------------------------------------------------------------------------

def iter_notebook_cells(notebook_path: Path) -> Iterable[tuple[int, str, str]]:
    """Yield (cell_index, cell_type, source). Ignore les cellules vides."""
    with notebook_path.open("r", encoding="utf-8") as f:
        nb = json.load(f)
    for idx, cell in enumerate(nb.get("cells", [])):
        src = cell.get("source", [])
        text = "".join(src) if isinstance(src, list) else str(src)
        if text.strip():
            yield idx, cell.get("cell_type", ""), text


# ---------------------------------------------------------------------------
# Scans
# ---------------------------------------------------------------------------

def scan_classe2(
    notebook_path: Path,
    cell_idx: int,
    source: str,
    truth: LeanTruth,
) -> list[str]:
    """Classe 2 -- identite : un module cite avec un noeud qu'il ne modelise pas.

    Regle : sur une MEME LIGNE, une reference ``<Module>.lean`` et un numero
    ``N_M``. Si le module est connu et cite lui-meme des numeros de noeud
    (``truth.nodes[Module]`` non vide), et si aucun des numeros revendiques
    n'appartient a cet ensemble, c'est une identite perimee.

    Cadrage LIGNE, mesure (c.478) : un cadrage CELLULE rend un faux positif
    sur la cellule 16 de KNOTS-01 (l'arbre d'architecture y liste
    ``Invariant.lean`` et ``FigureEight.lean (noeud 4_1)`` ; la cellule parle
    donc de ``4_1`` sans rien revendiquer sur ``Invariant``, dont les seuls
    numeros sont ``3_1``). Le cadrage ligne attrape l'instance fondatrice et
    ne rend pas ce faux positif.
    """
    findings: list[str] = []
    lines = source.splitlines()
    for line_no, line in enumerate(lines, start=1):
        _classe2_line(notebook_path, cell_idx, line_no, line, truth, findings)
    # Repli a 80 colonnes : la prose courante coupe « ... FigureEight.lean »
    # et « (noeud 8_1) ... » sur deux lignes, et un cadrage strictement
    # mono-ligne perd ce cas (mesure c.478). La fenetre n'est ouverte que
    # pour une VRAIE continuation : la ligne suivante ne porte ni module ni
    # marqueur de liste/arbre, et la premiere ne termine pas sa phrase. Sans
    # ce discriminant, l'arbre d'architecture de la cellule 16 de KNOTS-01
    # (`|-- Invariant.lean` puis `|-- FigureEight.lean (4_1)`) redevient le
    # faux positif mesure.
    for idx in range(len(lines) - 1):
        head, tail = lines[idx], lines[idx + 1]
        if not _is_sentence_wrap(head, tail):
            continue
        _classe2_line(
            notebook_path, cell_idx, idx + 1, f"{head} {tail}", truth, findings
        )
    return findings


def _classe2_line(
    notebook_path: Path,
    cell_idx: int,
    line_no: int,
    text: str,
    truth: LeanTruth,
    findings: list[str],
) -> None:
    """Applique la regle de classe 2 a un fragment de texte (une ligne, ou
    une ligne et son repli)."""
    modules = set(LEAN_MODULE_RE.findall(text))
    modules |= {t for t in BARE_MODULE_RE.findall(text) if t in truth.defs}
    if not modules:
        return
    claimed = {f"{a}_{b}" for a, b in NODE_NUM_RE.findall(text)}
    if not claimed:
        return
    for module in sorted(modules):
        known = truth.nodes.get(module, set())
        if not known:
            # Le module ne cite aucun noeud (ou n'existe pas) : on ne
            # sait pas conclure, on ne signale pas.
            continue
        if claimed & known:
            continue
        findings.append(
            f"{notebook_path}:cell_{cell_idx:02d}:L{line_no}:"
            f" STALE_IDENTITY (classe 2) -- la cellule attribue le(s)"
            f" noeud(s) {sorted(claimed)} a {module}.lean, qui n'en cite"
            f" aucun ; le module cite {sorted(known)}"
        )


def _is_sentence_wrap(head: str, tail: str) -> bool:
    """Vrai si ``tail`` est la continuation enroulee de ``head``.

    Trois exclusions, toutes mesurees sur des faux positifs reels : une tete
    qui termine sa phrase (ponctuation finale), une queue qui ouvre une
    entree de liste ou d'arbre (``-``, ``*``, ``|``, ``1.``), et les deux
    cotes qui portent deja leur propre module ou leur propre numero de noeud
    (deux revendications voisines, pas une phrase coupee).
    """
    if _SENTENCE_END_RE.search(head):
        return False
    if _LIST_ENTRY_RE.match(tail):
        return False
    if NODE_NUM_RE.search(head) or LEAN_MODULE_RE.search(tail):
        return False
    return True


def scan_classe3(
    notebook_path: Path,
    cell_idx: int,
    source: str,
    truth: LeanTruth,
) -> list[str]:
    """Classe 3 -- TODO perime : un identifiant declare au head est dit absent.

    Regle : sur une MEME LIGNE, un marqueur d'absence et un identifiant
    metier (underscore). Si l'identifiant est declare au head dans l'arbre
    Lean, la cellule affirme une absence qui n'existe plus.

    Le caveat de perimation annule le finding quand il porte sur la LIGNE du
    finding, ou sur une ligne qui cite le MEME identifiant (portee de la
    phrase, pas de la cellule -- cf. STALE_TODO_CAVEAT_RE).
    """
    findings: list[str] = []
    caveat_lines: set[int] = set()
    caveat_idents: set[str] = set()
    for idx, line in enumerate(source.splitlines(), start=1):
        if STALE_TODO_CAVEAT_RE.search(line):
            caveat_lines.add(idx)
            caveat_idents.update(METIER_IDENT_RE.findall(line))
    for line_no, line in enumerate(source.splitlines(), start=1):
        if not any(marker.search(line) for marker in ABSENCE_MARKERS):
            continue
        for ident in METIER_IDENT_RE.findall(line):
            if ident not in truth.all_defs and ident not in truth.aliases:
                continue
            if line_no in caveat_lines or ident in caveat_idents:
                continue
            findings.append(
                f"{notebook_path}:cell_{cell_idx:02d}:L{line_no}:"
                f" STALE_TODO (classe 3) -- la cellule affirme une absence sur"
                f" '{ident}', qui est declare au head dans l'arbre Lean"
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


def scan_notebook(notebook_path: Path, truth: LeanTruth) -> list[str]:
    findings: list[str] = []
    try:
        cells = list(iter_notebook_cells(notebook_path))
    except Exception as e:  # noqa: BLE001 -- un carnet illisible ne doit pas tuer le scan
        return [f"{notebook_path}:load_error: lecture du .ipynb impossible ({e})"]
    for cell_idx, _cell_type, source in cells:
        findings.extend(scan_classe2(notebook_path, cell_idx, source, truth))
        findings.extend(scan_classe3(notebook_path, cell_idx, source, truth))
    return findings


def _filter_knots(paths: list[Path], knots_dir: Path) -> list[Path]:
    """Ne garde que les .ipynb sous le dossier KNOTS (entree pre-commit)."""
    out: list[Path] = []
    for p in paths:
        if p.suffix != ".ipynb":
            continue
        try:
            p.resolve().relative_to(knots_dir.resolve())
        except ValueError:
            continue
        out.append(p)
    return out


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Voie (B) prevention KNOTS #21007 : scan read-only des classes "
            "2 (identite perimee) et 3 (TODO perime)."
        ),
    )
    parser.add_argument(
        "--notebook", type=Path, default=None,
        help="Cible un carnet unique (defaut : tous les KNOTS/*.ipynb).",
    )
    parser.add_argument(
        "--changed", type=Path, nargs="*", default=None,
        help="Carnets passes par pre-commit ; ceux hors KNOTS sont ignores.",
    )
    parser.add_argument(
        "--repo-root", type=Path, default=None,
        help="Racine du depot (defaut : trois niveaux au-dessus du script).",
    )
    parser.add_argument(
        "--lean-root", type=Path, default=None,
        help="Racine de l'arbre Lean (defaut : <KNOTS>/knot_lean).",
    )
    parser.add_argument(
        "--json", action="store_true", help="Sortie JSON structuree.",
    )
    args = parser.parse_args(argv)

    repo_root = (args.repo_root or Path(__file__).resolve().parents[2]).resolve()
    knots_dir = default_knots_dir(repo_root)
    lean_root = (args.lean_root or (knots_dir / "knot_lean")).resolve()

    if args.notebook is not None:
        notebooks = [args.notebook.resolve()]
    elif args.changed is not None:
        notebooks = _filter_knots(list(args.changed), knots_dir)
        if not notebooks:
            # Aucun carnet KNOTS modifie : rien a faire (rc 0, hook silencieux).
            if args.json:
                print(json.dumps({"scanned_notebooks": [], "findings": [],
                                  "exit_code": 0}, ensure_ascii=False, indent=2))
            return 0
    else:
        notebooks = discover_knots_notebooks(knots_dir)

    if not notebooks:
        print("scan_knots_extracts: 0 carnet KNOTS trouve, scan vide", file=sys.stderr)
        return 0

    truth = LeanTruth.build(lean_root)
    if truth.modules_read == 0:
        # Sans verite du depot, aucune conclusion n'est possible -- on le dit
        # au lieu de rendre un vert trompeur (la classe 1 avait le defaut
        # inverse : 0 fichier scanne et rc 0 sans un mot).
        msg = (f"scan_knots_extracts: arbre Lean introuvable sous {lean_root} -- "
               f"aucune verite a confronter, scan NON CONCLU")
        if args.json:
            print(json.dumps({"scanned_notebooks": [str(n) for n in notebooks],
                              "findings": [msg], "exit_code": 2},
                             ensure_ascii=False, indent=2))
        else:
            print(msg, file=sys.stderr)
        return 2

    all_findings: list[str] = []
    for nb in notebooks:
        all_findings.extend(scan_notebook(nb, truth))

    if args.json:
        print(json.dumps({
            "scanned_notebooks": [str(n) for n in notebooks],
            "lean_modules_read": truth.modules_read,
            "findings": all_findings,
            "exit_code": 0 if not all_findings else 1,
        }, ensure_ascii=False, indent=2))
    else:
        for line in all_findings:
            print(line)
        if not all_findings:
            print(
                f"scan_knots_extracts: {len(notebooks)} carnet(s) scanne(s) "
                f"contre {truth.modules_read} module(s) Lean, 0 finding "
                f"(classes 2 + 3)",
                file=sys.stderr,
            )

    return 0 if not all_findings else 1


if __name__ == "__main__":
    raise SystemExit(main())
