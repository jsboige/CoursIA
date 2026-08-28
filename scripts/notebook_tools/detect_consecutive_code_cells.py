#!/usr/bin/env python3
"""Detect runs of >=2 consecutive code cells in a notebook (#12797).

Pourquoi cet outil existe
-------------------------
User (2026-08-24): dans un notebook pedagogique, deux cellules code qui **se
suivent** (aucune cellule markdown entre elles) sont "quasiment toujours
l'opportunite de proposer une cellule de markdown intermediaire, et sinon, c'est
un motif de fusion." Ce detecteur mesure cette adjacence et la rend visible sur
la PR qui touche le notebook.

ADVISORY by design (decision user 2026-08-24): il sort TOUJOURS 0. Le signal
actionnable est le label ``consecutive-code-cells`` que le workflow pose, jamais
la conclusion verte du job (green by construction -- le piege #8797 : une PR
non-conforme est passee parce qu'un job vert etait lu comme un conformite).

Consumes, never re-implemented: la classification corpus/kind de
``count_exercises.py``. Les kinds out-of-corpus (artifact/template/vendored/
archive/legacy/tooling/student) et l'exemption setup sont importes, pas
re-implementes (issue #10479 acceptance: le label et l'outil canonique ne
doivent pas diverger). La regle s'applique aux kinds ``standard`` et ``lean``
(corpus pedagogique) ; un notebook ``setup`` est exempt (scaffolding
d'environnement porte legitiment de longues sequences code-only sans budget de
prose) ; un notebook out-of-corpus est exempt.

Deux labels distincts, precedente densite (#10479) transposee avec la lecon
#8819 : ``consecutive-code-cells`` (mesure, run >=2 present) /
``consecutive-code-cells-unmeasured`` (JSON illisible). Un notebook a zero
cellule code n'est PAS ``unmeasured`` ici (contrairement a la densite, il n'y a
pas de division par zero) -- il n'a aucun defaut d'adjacence, statut ``ok``.

Usage:
    python detect_consecutive_code_cells.py                    # corpus entier
    python detect_consecutive_code_cells.py <dir>|*.ipynb ...  # cibles
    git diff --name-only BASE HEAD -- '*.ipynb' | python detect_consecutive_code_cells.py --stdin --json
"""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import asdict, dataclass, field
from pathlib import Path

_TOOLS_DIR = Path(__file__).resolve().parent
if str(_TOOLS_DIR) not in sys.path:
    sys.path.insert(0, str(_TOOLS_DIR))

from count_exercises import (  # noqa: E402
    EXCLUDE_DIRS,
    NOTEBOOKS_DIR,
    OUT_OF_CORPUS_KINDS,
    classify_notebook,
)

#: Le seuil de longueur d'une serie de cellules code consecutives. Decision user
#: 2026-08-24 : lecture litterale "cellules qui se suivent" = >= 2. Non expose en
#: option CLI pour la meme raison que DENSITY_THRESHOLD : un seuil mutable
#: changerait silencieusement ce que le label signifie d'une invocation a l'autre.
CONSECUTIVE_MIN = 2

#: Kinds juges contre la regle d'adjacence. ``standard`` = notebook de cours
#: ordinaire ; ``lean`` reste dans le corpus pedagogique meme si la regle des
#: exercices l'exempte (0-2) -- c'est aussi une serie d'enseignement. L'exemption
#: exercices et l'exemption densite/adjacence sont des regles differentes avec des
#: rationales differentes ; chacune consomme ``classify_notebook`` et applique son
#: propre jugement par-dessus.
JUDGED_KINDS = frozenset({"standard", "lean"})

#: Label pour "mesure, run de cellules code consecutives present" (#12797).
LABEL_NAME = "consecutive-code-cells"

#: Un SECOND, distinct, pour les notebooks que l'outil n'a PAS pu lire (lecon
#: #8819 transposee) : parse JSON echoue. Jamais fusionne avec le label ci-dessus.
LABEL_UNMEASURED = "consecutive-code-cells-unmeasured"


@dataclass
class AdjacencyRun:
    """Une serie maximale de cellules code consecutives."""

    start: int  # index de la premiere cellule code de la serie
    length: int  # nombre de cellules code consecutives


@dataclass
class AdjacencyVerdict:
    """Verdict d'un notebook, avec la preuve dont le label a besoin."""

    path: str
    kind: str
    exempt: bool  # exempt de la regle (out of corpus, ou setup)
    min_run: int  # le seuil juge (2), pour l'affichage
    max_run: int  # plus longue serie de cellules code consecutives (tout run confondu)
    runs: int  # nombre de series de longueur >= CONSECUTIVE_MIN
    code_cells: int  # nb total de cellules code
    status: str  # 'consecutive' | 'ok' | 'exempt' | 'unmeasured'
    detail: str = ""


@dataclass
class AdjacencyResult:
    """Verdict agrege sur tous les notebooks scannes."""

    consecutive: list[AdjacencyVerdict] = field(default_factory=list)
    ok: list[AdjacencyVerdict] = field(default_factory=list)
    exempt: list[AdjacencyVerdict] = field(default_factory=list)
    unmeasured: list[AdjacencyVerdict] = field(default_factory=list)

    def as_payload(self) -> dict:
        """Payload machine-readable pour que le workflow decide des labels.

        Lecon #8819 appliquee a l'adjacence : un notebook que l'outil n'a pas pu
        lire n'est PAS conforme -- il est UNMEASURED. Le summary expose
        ``unmeasured`` EN PREMIER pour que l'ecart saute aux yeux, et porte DEUX
        labels : ``consecutive`` (mesure, run present) et ``unmeasured`` (n'a pas
        pu lire). Le workflow leve chacun quand son compte > 0 et ne pretend
        jamais "tous conformes" tant que ``unmeasured > 0``.
        """
        n_cons = len(self.consecutive)
        n_un = len(self.unmeasured)
        n_ok = len(self.ok)
        n_exempt = len(self.exempt)
        return {
            "labels": {
                "consecutive": {"name": LABEL_NAME, "count": n_cons},
                "unmeasured": {"name": LABEL_UNMEASURED, "count": n_un},
            },
            "summary": {
                # unmeasured EN PREMIER : un coup d'oeil rend l'ecart evident (#8819).
                "unmeasured": n_un,
                "total": n_cons + n_ok + n_exempt + n_un,
                "judged": n_cons + n_ok + n_un,  # soumis a la regle
                "exempt": n_exempt,  # out of corpus, ou setup
                "consecutive": n_cons,
            },
            "consecutive": [asdict(v) for v in self.consecutive],
            "ok": [asdict(v) for v in self.ok],
            "exempt": [asdict(v) for v in self.exempt],
            "unmeasured": [asdict(v) for v in self.unmeasured],
        }


def _consecutive_runs(data: dict) -> list[AdjacencyRun]:
    """Toutes les series maximales de cellules code consecutives.

    Un run maximal = un bloc contigu de cellules ``code`` sans cellule markdown
    entre elles. On renvoie chaque bloc maximal avec son (start, length), que la
    longueur soit >= CONSECUTIVE_MIN ou non -- le max_run reporte la plus longue
    serie du notebook, celle qui juge.
    """
    cells = data.get("cells", [])
    runs: list[AdjacencyRun] = []
    i = 0
    n = len(cells)
    while i < n:
        if cells[i].get("cell_type") == "code":
            j = i
            while j < n and cells[j].get("cell_type") == "code":
                j += 1
            runs.append(AdjacencyRun(start=i, length=j - i))
            i = j
        else:
            i += 1
    return runs


def _measure(data: dict) -> tuple[int, int, int]:
    """Retourne ``(max_run, n_qualifying, n_code)`` pour un notebook.

    ``max_run`` = plus longue serie de cellules code consecutives (0 si aucune
    cellule code). ``n_qualifying`` = nombre de series de longueur >=
    CONSECUTIVE_MIN. ``n_code`` = nombre total de cellules code.
    """
    runs = _consecutive_runs(data)
    n_code = sum(r.length for r in runs)
    if not runs:
        return (0, 0, 0)
    max_run = max(r.length for r in runs)
    n_qualifying = sum(1 for r in runs if r.length >= CONSECUTIVE_MIN)
    return (max_run, n_qualifying, n_code)


def _read_notebook(path: Path) -> dict:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise ValueError(f"cannot parse: {exc}") from exc


def check_paths(paths: list[Path]) -> AdjacencyResult:
    """Classifie + mesure chaque path, en le rangeant par statut d'adjacence.

    Un notebook est ``consecutive`` seulement s'il est d'un kind juge (standard
    ou lean), lisible, et porte au moins une serie de >= CONSECUTIVE_MIN cellules
    code consecutives. Un notebook ``setup`` ou out-of-corpus est exempt -- la
    classification est CONSOMMEE depuis ``count_exercises.py``, pas re-decidee ici.
    """
    result = AdjacencyResult()
    for path in paths:
        kind, _ = classify_notebook(path)
        exempt = kind in OUT_OF_CORPUS_KINDS or kind == "setup"
        if exempt:
            result.exempt.append(
                AdjacencyVerdict(
                    path=str(path), kind=kind, exempt=True, min_run=CONSECUTIVE_MIN,
                    max_run=0, runs=0, code_cells=0, status="exempt",
                    detail=(
                        f"exempt de la regle (kind={kind}) -- la regle "
                        "ne s'applique pas"
                    ),
                )
            )
            continue
        try:
            data = _read_notebook(path)
        except ValueError as exc:
            result.unmeasured.append(
                AdjacencyVerdict(
                    path=str(path), kind=kind, exempt=False, min_run=CONSECUTIVE_MIN,
                    max_run=0, runs=0, code_cells=0, status="unmeasured",
                    detail=str(exc),
                )
            )
            continue
        max_run, n_qualifying, n_code = _measure(data)
        status = "consecutive" if n_qualifying > 0 else "ok"
        verdict = AdjacencyVerdict(
            path=str(path), kind=kind, exempt=False, min_run=CONSECUTIVE_MIN,
            max_run=max_run, runs=n_qualifying, code_cells=n_code, status=status,
            detail=(
                f"{n_qualifying} run(s) de longueur >= {CONSECUTIVE_MIN}"
                if status == "consecutive" else ""
            ),
        )
        if n_qualifying > 0:
            result.consecutive.append(verdict)
        else:
            result.ok.append(verdict)
    return result


def _collect_paths(argv_paths: list[str], from_stdin: bool) -> list[Path]:
    """Resout les cibles depuis les args CLI et/ou stdin en chemins de notebook.

    Une cible peut etre un fichier notebook OU un repertoire (globbe pour
    ``*.ipynb`` en dessous, en sautant les dirs exclus canoniques). Les lignes
    vides et doublons sont droppes ; les cibles inexistantes sont averties et
    sautees.
    """
    raw: list[str] = list(argv_paths)
    if from_stdin:
        raw += [ln.strip() for ln in sys.stdin if ln.strip()]
    seen: set[str] = set()
    paths: list[Path] = []
    for r in raw:
        if r in seen:
            continue
        seen.add(r)
        p = Path(r)
        if p.is_dir():
            paths.extend(
                q for q in _glob_notebooks(p)
                if str(q) not in seen and not seen.add(str(q))
            )
            continue
        if not p.exists():
            print(f"warning: {r} does not exist (deleted?), skipping", file=sys.stderr)
            continue
        if p.suffix != ".ipynb":
            continue
        paths.append(p)
    return paths


def _glob_notebooks(directory: Path) -> list[Path]:
    """Tous les ``*.ipynb`` sous ``directory``, en sautant les dirs exclus canoniques.

    Consomme :data:`EXCLUDE_DIRS` de ``count_exercises.py`` pour que le mode scan
    et le scan flotte voient le meme monde.
    """
    out: list[Path] = []
    for p in sorted(directory.rglob("*.ipynb")):
        if any(part in EXCLUDE_DIRS for part in p.parts):
            continue
        if p.name.startswith("."):  # .ipynb_checkpoints/* (aussi dans EXCLUDE_DIRS)
            continue
        out.append(p)
    return out


def _render_text(result: AdjacencyResult) -> str:
    """Resume lisible (le log du workflow ; les labels sont separes).

    Miroir de pedagogy_density : la ligne de cloture n'affirme QUE ce qui a ete
    mesure -- ``unmeasured > 0`` signifie que la phrase honnete est "N non
    mesure", jamais un blanket conformity claim sur des notebooks jamais lus.
    """
    s = result.as_payload()["summary"]
    lines = [
        f"Notebooks scanned   : {s['total']}",
        f"Judged vs rule      : {s['judged']}",
        f"Exempt              : {s['exempt']}",
        f"Run >= {CONSECUTIVE_MIN}: {s['consecutive']}",
        f"Unmeasured          : {s['unmeasured']}",
    ]
    if result.consecutive:
        lines.append(f"\n--- Run >= {CONSECUTIVE_MIN} (label: {LABEL_NAME}) ---")
        for v in result.consecutive:
            lines.append(
                f"  [max={v.max_run} runs={v.runs}] ({v.kind}) {v.path}"
            )
    if result.exempt:
        lines.append("\n--- Exempt (kind-classified, not labelled) ---")
        for v in result.exempt:
            lines.append(f"  ({v.kind}) {v.path} -- {v.detail}")
    if result.unmeasured:
        lines.append(f"\n--- Unmeasured (label: {LABEL_UNMEASURED}) ---")
        for v in result.unmeasured:
            lines.append(f"  {v.path}: {v.detail[:120]}")
    if s["unmeasured"] > 0:
        lines.append(
            f"\n{s['unmeasured']} notebook(s) could not be read -- "
            "conformity neither claimed nor denied."
        )
    elif not result.consecutive:
        lines.append(
            "\nNo judged notebook carries a run of consecutive code cells."
        )
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Detect runs of >=2 consecutive code cells in notebooks (#12797). "
            "Always exits 0 (advisory): the signal is the "
            f"'{LABEL_NAME}' label, not this exit code."
        ),
    )
    parser.add_argument(
        "targets", nargs="*", default=[],
        help="Notebook files or directories to scan (default: whole corpus).",
    )
    parser.add_argument(
        "--paths", nargs="*", default=[],
        help="Explicit notebook paths (PR mode).",
    )
    parser.add_argument(
        "--stdin", action="store_true",
        help="Also read paths from stdin (one per line; e.g. git diff output).",
    )
    parser.add_argument(
        "--json", dest="json_out", action="store_true",
        help="Emit machine-readable JSON (the workflow parses this for the label).",
    )
    # Le seuil n'est volontairement PAS un flag CLI : il est verrouille par la
    # decision user 2026-08-24. Un seuil mutable changerait silencieusement ce que
    # le label signifie d'une invocation a l'autre.
    args = parser.parse_args(argv)

    targets = list(args.paths) + list(args.targets)
    if not targets and not args.stdin:
        targets = [str(NOTEBOOKS_DIR)]  # fleet scan mode (comme count_exercises)
    paths = _collect_paths(targets, args.stdin)
    if not paths:
        msg = "No notebooks to measure."
        if args.json_out:
            payload = AdjacencyResult().as_payload()
            payload["note"] = msg
            print(json.dumps(payload, indent=2, ensure_ascii=False))
        else:
            print(msg)
        return 0

    result = check_paths(paths)
    if args.json_out:
        print(json.dumps(result.as_payload(), indent=2, ensure_ascii=False))
    else:
        print(_render_text(result))
    # Advisory: NEVER exit non-zero (decision user 2026-08-24).
    return 0


if __name__ == "__main__":
    sys.exit(main())
