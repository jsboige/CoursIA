#!/usr/bin/env python3
"""Controle positif #17464 : execute l'organe sur les deux notebooks de #17021
(base `6d46b9c684~1` -> tete `6d46b9c684`) et verifie qu'il signale les 26 + 16
insertions de la campagne densite, avec les 3 buckets attendus.

Pourquoi ce script : le ticket #17464 exige que la PR de l'organe porte la
preuve que le controle positif mord (les 26 + 16 insertions capturees). Les
donnees ne peuvent pas vivre dans le depot (les blobs d'avant revert ne sont
plus sur main), elles sont donc materialisees via ``git show`` au moment du
controle : exactement le geste que l'auditeur et le coordinateur referont en
cas de reclamation.

Usage :
    python scripts/ci/check_17464_positive_control.py [BASE_SHA] [HEAD_SHA]
    defauts : BASE = 6d46b9c684~1, HEAD = 6d46b9c684 (avant la revert #17040)

Codes de retour : 0 = les 3 controles (NQueens=26, ConnectFour=16, >=1
EXERCISE_READING pour NQueens) passent ; 1 = au moins un echoue, avec
diagnostic sur stderr.
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/notebook_tools/check_split_reading_cells.py"

NQ_BASE_PATH = "MyIA.AI.Notebooks/Search/Applications/CSP/App-1-NQueens.ipynb"
C4_BASE_PATH = "MyIA.AI.Notebooks/Search/Applications/Search/App-14b-ConnectFour.ipynb"

NQ_EXPECTED = 26
C4_EXPECTED = 16
NQUEENS_EXERCISE_READING_EXPECTED = 1  # au moins 1 EXERCISE_READING attendu


def git_show_blob(sha: str, path: str) -> str | None:
    proc = subprocess.run(
        ["git", "show", f"{sha}:{path}"],
        cwd=str(ROOT), capture_output=True, text=True, encoding="utf-8", errors="replace",
    )
    if proc.returncode != 0:
        return None
    return proc.stdout


def scan_against_base(head_text: str, base_text: str, label: str) -> tuple[int, dict]:
    """Run the organ with --base on two temp files. Return (count, by_kind)."""
    scratch = Path("/tmp")
    base_p = scratch / f"_base_{label}.ipynb"
    head_p = scratch / f"_head_{label}.ipynb"
    base_p.write_text(base_text, encoding="utf-8")
    head_p.write_text(head_text, encoding="utf-8")
    proc = subprocess.run(
        ["python", str(SCRIPT), str(head_p), "--base", str(base_p), "--json"],
        capture_output=True, text=True, encoding="utf-8", errors="replace",
        env={"PYTHONIOENCODING": "utf-8", "PYTHONUTF8": "1", "PATH": "C:\\Program Files\\Python313"},
    )
    if proc.returncode not in (0, 2):
        raise RuntimeError(f"organ crashed for {label}: rc={proc.returncode}\nstderr={proc.stderr}")
    rows = json.loads(proc.stdout)
    by_kind: dict[str, int] = {}
    for r in rows:
        by_kind[r["type"]] = by_kind.get(r["type"], 0) + 1
    return len(rows), by_kind


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("base_sha", nargs="?", default="6d46b9c684~1",
                    help="SHA de la base (defaut : 6d46b9c684~1, avant #17021)")
    ap.add_argument("head_sha", nargs="?", default="6d46b9c684",
                    help="SHA de la tete (defaut : 6d46b9c684, la PR #17021 avant revert)")
    args = ap.parse_args(argv)

    base_nq = git_show_blob(args.base_sha, NQ_BASE_PATH)
    head_nq = git_show_blob(args.head_sha, NQ_BASE_PATH)
    base_c4 = git_show_blob(args.base_sha, C4_BASE_PATH)
    head_c4 = git_show_blob(args.head_sha, C4_BASE_PATH)

    if not all([base_nq, head_nq, base_c4, head_c4]):
        print(
            f"ERREUR : un ou plusieurs blobs introuvables. base={args.base_sha}, "
            f"head={args.head_sha}. Verifier que la revert #197a22ceda5a est sur main.",
            file=sys.stderr,
        )
        return 1

    fails = []

    n_nq, kinds_nq = scan_against_base(head_nq, base_nq, "nqueens")
    n_c4, kinds_c4 = scan_against_base(head_c4, base_c4, "c4")

    if n_nq != NQ_EXPECTED:
        fails.append(f"App-1-NQueens : attendu {NQ_EXPECTED}, trouve {n_nq} ({kinds_nq})")
    if n_c4 != C4_EXPECTED:
        fails.append(f"App-14b-ConnectFour : attendu {C4_EXPECTED}, trouve {n_c4} ({kinds_c4})")
    if kinds_nq.get("EXERCISE_READING", 0) < NQUEENS_EXERCISE_READING_EXPECTED:
        fails.append(
            f"App-1-NQueens : {NQUEENS_EXERCISE_READING_EXPECTED} EXERCISE_READING "
            f"attendu(s), trouve {kinds_nq.get('EXERCISE_READING', 0)}"
        )

    # Verifier que les 3 buckets sont exprimes dans au moins un des deux notebooks.
    all_kinds = set(kinds_nq) | set(kinds_c4)
    for required in ("SECOND_READING", "READING_BEFORE_CODE", "EXERCISE_READING"):
        if required not in all_kinds:
            fails.append(f"bucket {required!r} jamais exprime dans les positifs")

    print(f"=== Controle positif #17464 (base {args.base_sha[:9]} -> head {args.head_sha[:9]}) ===")
    print(f"App-1-NQueens        : {n_nq:3d} ({kinds_nq})  -- attendu {NQ_EXPECTED}")
    print(f"App-14b-ConnectFour  : {n_c4:3d} ({kinds_c4})  -- attendu {C4_EXPECTED}")
    print()
    if fails:
        print("ECHEC :")
        for f in fails:
            print(f"  - {f}")
        return 1
    print("PASS : les 3 buckets sont exprimes, les totaux correspondent, EXERCISE_READING est present.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
