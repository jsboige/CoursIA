"""Verifier independent du moteur `simulate_payoff` du notebook GameTheory-06e.

Issue #15173 (Tranche A) acceptance #3 :
> Matrice reproduite par le moteur et un verificateur independant, avec assertion
> d'egalite.

Ce script est le **deuxieme organe** : une table de verite 25 entrees, encodee
a la main depuis la specification documentee (Critch-Dennis-Russell 2022 §3,
Shoham-Leyton-Brown §3.4.2). L'independance est **structurelle** : la table ne
reencodage pas la logique du moteur, elle declare le verdict attendu.

Mode 1 (--engine table) : on parse la cellule 14 du notebook (sortie texte du
moteur) et on la compare a la table oracle. Pas de re-execution du notebook
(le notebook a deja ete execute et ses outputs sont valides au commit).

Mode 2 (--engine re-execute) : on execute le notebook via papermill/jupyter,
puis on extrait la variable `rows` du namespace du kernel post-execution.

Mode 3 (defaut) : mode 1.

Usage :
    python scripts/notebook_tools/verify_program_games_table.py
    python scripts/notebook_tools/verify_program_games_table.py --json
    python scripts/notebook_tools/verify_program_games_table.py --engine re-execute

Convention : bots suffixes `_toy` (heuristiques locales au notebook,
frontiere pedagogie vs publication, cf. notebook cellule 1).

Sortie :
    exit 0 si tous les verdicts agree
    exit 1 si mismatch detecte
    exit 2 si erreur d'execution (notebook introuvable, kernel timeout, etc.)
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

# Constantes du PD canonique (T > R > P > S, 2R > T + S) -- Shoham-Leyton-Brown §3.4.2
PAYOFFS = {
    ("C", "C"): (3, 3),
    ("C", "D"): (0, 5),
    ("D", "C"): (5, 0),
    ("D", "D"): (1, 1),
}

# Table de verite 25 entrees -- encodee a la main depuis la spec cellule 11 du
# notebook. Chaque entree documente le verdict attendu (action_a, action_b,
# payoff) tel qu'un lecteur lisant la spec et appliquant les regles des bots
# `CooperateBot_toy`, `DefectBot_toy`, `FairBot_toy`, `CUPOD_toy`, `PrudentBot_toy`
# le predirait mentalement.
#
# Spec rappelee :
#   CooperateBot_toy(_) -> 'C' (inconditionnel)
#   DefectBot_toy(_)    -> 'D' (inconditionnel)
#   FairBot_toy(src)    -> 'C' si 'return "C"' in src, sinon 'D'
#   CUPOD_toy(src)      -> 'C' si 'return "C"' in src, sinon 'D'
#   PrudentBot_toy(src) -> 'D' si 'DefectBot_toy' in src ET pas 'CUPOD_toy'/'FairBot_toy'
#                          sinon 'C' si 'return "C"' in src, sinon 'D'
#
# Independance structurelle : ce fichier n'importe AUCUNE logique du moteur
# du notebook. Si le moteur boguait (regex copiée, string-match fautif, etc.),
# cette table continuerait à rendre le bon verdict car elle ne depend
# d'aucun module du notebook -- uniquement de la constante PAYOFFS (PD canonique).

EXPECTED_TABLE: dict[tuple[str, str], tuple[str, str, tuple[int, int]]] = {
    # --- Confrontations CooperateBot_toy ---
    ("CooperateBot_toy", "CooperateBot_toy"): ("C", "C", (3, 3)),
    ("CooperateBot_toy", "DefectBot_toy"):    ("C", "D", (0, 5)),
    ("CooperateBot_toy", "FairBot_toy"):      ("C", "C", (3, 3)),
    ("CooperateBot_toy", "CUPOD_toy"):        ("C", "C", (3, 3)),
    ("CooperateBot_toy", "PrudentBot_toy"):   ("C", "C", (3, 3)),
    # --- Confrontations DefectBot_toy ---
    ("DefectBot_toy", "CooperateBot_toy"):    ("D", "C", (5, 0)),
    ("DefectBot_toy", "DefectBot_toy"):       ("D", "D", (1, 1)),
    ("DefectBot_toy", "FairBot_toy"):         ("D", "D", (1, 1)),
    ("DefectBot_toy", "CUPOD_toy"):           ("D", "D", (1, 1)),
    ("DefectBot_toy", "PrudentBot_toy"):      ("D", "D", (1, 1)),
    # --- Confrontations FairBot_toy ---
    ("FairBot_toy", "CooperateBot_toy"):      ("C", "C", (3, 3)),
    ("FairBot_toy", "DefectBot_toy"):         ("D", "D", (1, 1)),
    ("FairBot_toy", "FairBot_toy"):           ("C", "C", (3, 3)),
    ("FairBot_toy", "CUPOD_toy"):             ("C", "C", (3, 3)),
    ("FairBot_toy", "PrudentBot_toy"):        ("C", "C", (3, 3)),
    # --- Confrontations CUPOD_toy ---
    ("CUPOD_toy", "CooperateBot_toy"):        ("C", "C", (3, 3)),
    ("CUPOD_toy", "DefectBot_toy"):           ("D", "D", (1, 1)),
    ("CUPOD_toy", "FairBot_toy"):             ("C", "C", (3, 3)),
    ("CUPOD_toy", "CUPOD_toy"):               ("C", "C", (3, 3)),
    ("CUPOD_toy", "PrudentBot_toy"):          ("C", "C", (3, 3)),
    # --- Confrontations PrudentBot_toy ---
    ("PrudentBot_toy", "CooperateBot_toy"):   ("C", "C", (3, 3)),
    ("PrudentBot_toy", "DefectBot_toy"):      ("D", "D", (1, 1)),
    ("PrudentBot_toy", "FairBot_toy"):        ("C", "C", (3, 3)),
    ("PrudentBot_toy", "CUPOD_toy"):          ("C", "C", (3, 3)),
    ("PrudentBot_toy", "PrudentBot_toy"):     ("C", "C", (3, 3)),
}


def parse_engine_table_from_cell_14(notebook_path: Path) -> dict:
    """Parse la sortie de la cellule 14 du notebook (moteur `simulate_payoff`).

    La cellule imprime une table :
        A              B              act  payoff_A payoff_B status
        CooperateBot_toy CooperateBot_toy C/C         3        3 play
        ...

    Returns
    -------
    dict[(name_a, name_b), (action_a, action_b, (payoff_a, payoff_b))]
    """
    import nbformat

    nb = nbformat.read(str(notebook_path), as_version=4)
    # Localiser la cellule moteur par son id (e22d0b5a) au lieu d'un index
    # figé -- l'insertion d'une cellule markdown (ex. ajout Aumann/Nash en
    # PR #15862, c.1130) peut décaler l'index.
    ENGINE_CELL_ID = "e22d0b5a"
    cell = None
    for c in nb["cells"]:
        if c.get("id") == ENGINE_CELL_ID:
            cell = c
            break
    if cell is None:
        raise ValueError(
            f"cellule moteur id={ENGINE_CELL_ID} introuvable dans le notebook"
        )
    if cell.get("cell_type") != "code":
        raise ValueError(f"cellule moteur id={ENGINE_CELL_ID} inattendue: type={cell.get('cell_type')}")

    outputs = cell.get("outputs", [])
    text = ""
    for o in outputs:
        if o.get("output_type") == "stream":
            text += "".join(o.get("text", []))
        elif o.get("output_type") in ("execute_result", "display_data"):
            data = o.get("data", {})
            text += "".join(data.get("text/plain", []))

    table: dict[tuple[str, str], tuple[str, str, tuple[int, int]]] = {}
    for line in text.splitlines():
        line = line.rstrip()
        if not line or line.startswith("A ") or line.startswith("-"):
            continue
        # Format attendu : NAME_A NAME_B act payoff_A payoff_B status
        # NAME_A NAME_B ont 14 colonnes chacun (alignement du print).
        # act est au format "X/Y" (4 colonnes).
        parts = line.split()
        if len(parts) < 6:
            continue
        name_a = parts[0]
        name_b = parts[1]
        act = parts[2]
        try:
            pay_a = int(parts[3])
            pay_b = int(parts[4])
        except ValueError:
            continue
        a, b = act.split("/")
        table[(name_a, name_b)] = (a, b, (pay_a, pay_b))

    if len(table) != 25:
        raise ValueError(
            f"table moteur extraite a {len(table)} lignes (attendu 25) -- "
            f"format de sortie change ?"
        )
    return table


def load_notebook_engine_reexecute(notebook_path: Path) -> dict:
    """Execute le notebook via papermill et extrait la table du moteur.

    Lent et dependant de jupyter -- preferez `parse_engine_table_from_cell_14`
    si le notebook a deja des outputs valides au commit.
    """
    import nbformat
    from nbclient import NotebookClient

    nb = nbformat.read(str(notebook_path), as_version=4)
    client = NotebookClient(nb, kernel_name="python3", timeout=300)
    client.execute()

    km = client.kernel_manager
    kernel = km.kernel
    rows = kernel.shell.user_ns.get("rows", [])
    out: dict[tuple[str, str], tuple[str, str, tuple[int, int]]] = {}
    for r in rows:
        a, b = r["act"].split("/")
        out[(r["A"], r["B"])] = (a, b, r["payoff"])
    return out


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--notebook",
        type=Path,
        default=Path("MyIA.AI.Notebooks/GameTheory/GameTheory-06e-Open-Source-Game-Theory.ipynb"),
    )
    parser.add_argument(
        "--engine",
        choices=["table", "re-execute"],
        default="table",
        help="Mode d'extraction de la table moteur (defaut: parse cellule 14).",
    )
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()

    if not args.notebook.exists():
        print(f"ERREUR: notebook introuvable: {args.notebook}", file=sys.stderr)
        return 2

    try:
        if args.engine == "re-execute":
            engine_table = load_notebook_engine_reexecute(args.notebook)
        else:
            engine_table = parse_engine_table_from_cell_14(args.notebook)
    except Exception as e:
        print(f"ERREUR: echec extraction table moteur: {e}", file=sys.stderr)
        return 2

    mismatches: list[dict] = []
    agrees = 0
    for key, expected in EXPECTED_TABLE.items():
        actual = engine_table.get(key)
        if actual != expected:
            mismatches.append({
                "pair": key,
                "expected": expected,
                "actual": actual,
            })
        else:
            agrees += 1

    summary = {
        "notebook": Path(args.notebook).name,
        "engine_mode": args.engine,
        "table_size": len(EXPECTED_TABLE),
        "agrees": agrees,
        "mismatches": mismatches,
        "exit_code": 0 if not mismatches else 1,
    }

    if args.json:
        print(json.dumps(summary, indent=2, ensure_ascii=False))
    else:
        print(f"Notebook: {Path(args.notebook).name}")
        print(f"Mode extraction moteur: {args.engine}")
        print(f"Table oracle: {len(EXPECTED_TABLE)} paires (independance structurelle)")
        print(f"Agreements: {agrees}/{len(EXPECTED_TABLE)}")
        if mismatches:
            print(f"MISMATCHES: {len(mismatches)}")
            for m in mismatches:
                print(f"  {m['pair']}: attendu={m['expected']} obtenu={m['actual']}")
        else:
            print("Aucun mismatch : la matrice du moteur est conforme à l'oracle declaratif.")

    return summary["exit_code"]


if __name__ == "__main__":
    sys.exit(main())
