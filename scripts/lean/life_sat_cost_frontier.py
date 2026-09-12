#!/usr/bin/env python3
"""Mesure reproductible de la frontière de coût du synthétiseur SAT Life.

La campagne varie séparément période, déplacement, boîte et borne de cardinalité.
Chaque taille ``k`` reçoit le même budget Z3. Un dépassement est conservé comme
``TIMEOUT`` : il ne devient jamais un faux certificat ``IMPOSSIBLE``.
"""

from __future__ import annotations

import argparse
import json
import platform
import sys
import time
from collections.abc import Iterable
from dataclasses import asdict, dataclass
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from life_synthesize_sat import search_minimal, universe_bounds, z3


@dataclass(frozen=True)
class FrontierCase:
    """Un point nommé de la campagne factorielle bornée."""

    case_id: str
    axis: str
    n: int
    vx: int
    vy: int
    box_w: int
    box_h: int
    max_cells: int
    role: str = "measure"


CASES: tuple[FrontierCase, ...] = (
    FrontierCase("control-found-glider", "control", 4, 1, -1, 4, 4, 5, "positive"),
    FrontierCase("control-impossible-superluminal", "control", 2, 3, 0, 3, 3, 4, "negative"),
    FrontierCase("period-n2", "period", 2, 1, 0, 4, 4, 6),
    FrontierCase("period-n3", "period", 3, 1, 0, 4, 4, 6),
    FrontierCase("period-n4", "period", 4, 1, 0, 4, 4, 6),
    FrontierCase("displacement-diagonal", "displacement", 4, 1, -1, 4, 4, 6),
    FrontierCase("displacement-orthogonal-c2", "displacement", 4, 2, 0, 5, 5, 9),
    FrontierCase("displacement-orthogonal-c4", "displacement", 4, 1, 0, 5, 5, 9),
    FrontierCase("box-3x3", "box", 4, 1, -1, 3, 3, 5),
    FrontierCase("box-4x4", "box", 4, 1, -1, 4, 4, 5),
    FrontierCase("box-5x5", "box", 4, 1, -1, 5, 5, 5),
    FrontierCase("cardinality-k7", "cardinality", 4, 2, 0, 5, 5, 7),
    FrontierCase("cardinality-k8", "cardinality", 4, 2, 0, 5, 5, 8),
    FrontierCase("cardinality-k9", "cardinality", 4, 2, 0, 5, 5, 9),
)


def run_case(case: FrontierCase, timeout_ms: int) -> dict:
    """Exécute un point et ajoute les paramètres nécessaires à sa reproduction."""
    xs, ys = universe_bounds(
        case.box_w, case.box_h, case.n, (case.vx, case.vy)
    )
    result = search_minimal(
        n=case.n,
        v=(case.vx, case.vy),
        box_w=case.box_w,
        box_h=case.box_h,
        max_cells=case.max_cells,
        enumerate_all=False,
        timeout_ms=timeout_ms,
    )
    return {
        **asdict(case),
        "encoded_width": len(xs),
        "encoded_height": len(ys),
        "encoded_cells_per_generation": len(xs) * len(ys),
        "boolean_state_variables": (case.n + 1) * len(xs) * len(ys),
        **result,
    }


def run_campaign(
    cases: Iterable[FrontierCase], timeout_ms: int, repeats: int = 1
) -> dict:
    """Exécute les points dans l'ordre déclaré et résume les verdicts."""
    selected = list(cases)
    started = time.perf_counter()
    results = [
        {"repeat": repeat, **run_case(case, timeout_ms)}
        for repeat in range(1, repeats + 1)
        for case in selected
    ]
    counts = {
        verdict: sum(result["verdict"] == verdict for result in results)
        for verdict in ("FOUND", "IMPOSSIBLE", "TIMEOUT")
    }
    return {
        "schema_version": 1,
        "timeout_ms_per_k": timeout_ms,
        "repeats": repeats,
        "environment": {
            "python": platform.python_version(),
            "platform": platform.platform(),
            "z3": z3.get_version_string(),
        },
        "counts": counts,
        "elapsed_s": round(time.perf_counter() - started, 3),
        "results": results,
    }


def main(argv: Iterable[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--timeout-ms",
        type=int,
        default=10_000,
        help="budget Z3 par taille k (défaut : 10000)",
    )
    parser.add_argument(
        "--case",
        action="append",
        dest="case_ids",
        help="limiter à un case_id ; option répétable",
    )
    parser.add_argument(
        "--repeats",
        type=int,
        default=1,
        help="répéter chaque point dans le même processus (défaut : 1)",
    )
    parser.add_argument(
        "--output",
        type=Path,
        help="écrire le JSON dans ce fichier plutôt que sur stdout",
    )
    args = parser.parse_args(list(argv) if argv is not None else None)

    if z3 is None:
        print("z3 est requis : pip install z3-solver", file=sys.stderr)
        return 2
    if args.timeout_ms <= 0:
        parser.error("--timeout-ms doit être strictement positif")
    if args.repeats <= 0:
        parser.error("--repeats doit être strictement positif")

    by_id = {case.case_id: case for case in CASES}
    unknown = sorted(set(args.case_ids or []) - set(by_id))
    if unknown:
        parser.error(f"case_id inconnu : {', '.join(unknown)}")
    selected = (
        [by_id[case_id] for case_id in args.case_ids]
        if args.case_ids
        else list(CASES)
    )

    report = run_campaign(selected, args.timeout_ms, args.repeats)
    payload = json.dumps(report, ensure_ascii=False, indent=2) + "\n"
    if args.output:
        args.output.write_text(payload, encoding="utf-8")
    else:
        print(payload, end="")

    positive_controls = [
        result for result in report["results"] if result["role"] == "positive"
    ]
    negative_controls = [
        result for result in report["results"] if result["role"] == "negative"
    ]
    controls_are_discriminant = (
        positive_controls
        and negative_controls
        and all(result["verdict"] == "FOUND" for result in positive_controls)
        and all(result["verdict"] == "IMPOSSIBLE" for result in negative_controls)
    )
    if not controls_are_discriminant:
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
