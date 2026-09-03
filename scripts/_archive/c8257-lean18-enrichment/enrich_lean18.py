#!/usr/bin/env python3
"""c.8257 enrichment script: appends a `**Le pont**` block to markdown cells in
Lean-18-Search-AStar-Optimality.ipynb (13 markdown cells).

Preserves the original `source` list-of-strings format (L935 ★: all but last have `\n`).
Only modifies targeted cell_ids; all other cells untouched (minimal diff).

Pattern aligned with c.8255 (PR #10715) and c.8256 (PR #10717).
L944 ★★ : atomic Python script with cell_id -> dict.
"""

import json
from pathlib import Path

NB_PATH = Path("MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-18-Search-AStar-Optimality.ipynb")

# For each cell_id: a short appended "Le pont" block.
APPENDS = {
    "153addc9": (
        "\n\n---\n\n"
        "**Le pont** : Lean-18 ↔ Lean-6 (Mathlib / `NNReal`, `List`, `linarith`) ↔ Lean-12b "
        "(cérémonie `#check` / `#print axioms`, c.8256) ↔ Search-3-Informed (A* heuristique "
        "en Python, vue empirique). Lean-18 est la version *formelle* de Search-3 : on calcule "
        "les chemins en Python sur des cas concrets, on prouve l'optimalité en Lean.\n"
    ),
    "54d2b874": (
        "\n\n---\n\n"
        "**Le pont** : A* unifie BFS / UCS / Dijkstra / A* dans un cadre unique. Lean-12b "
        "(Sensitivity) unifie aussi 4 techniques distinctes en un seul cadre. Lean-18 reprend "
        "la structure 4-modules (vocabulaire / lemme / théorème / portée) de Lean-12b mais "
        "pour l'algorithmique plutôt que l'algèbre linéaire. Search-3-Informed est la "
        "sister empirique.\n"
    ),
    "ad0e26ad": (
        "\n\n---\n\n"
        "**Le pont** : `NNReal` est utilisé dans Lean-6 (Mathlib / `Data.NNReal`) pour toute "
        "mesure d'une grandeur physique (durée, coût, probabilité). Lean-18 l'instancie pour "
        "les poids d'arêtes. Search-3-Informed et App-2-GraphColoringemploient `Real` ou `Int` "
        "en Python — Lean-18 est plus rigoureux sur la non-négativité.\n"
    ),
    "d1a30e36": (
        "\n\n---\n\n"
        "**Le pont** : `pathCost` est `Finset.sum` en Lean-6 (Mathlib / BigOperators), et "
        "`PathFrom` est `List.Chain` en Lean-6 (Mathlib / Data.List.Chain). Lean-18 les "
        "spécialise pour les graphes pondérés. Search-3-Informed calcule `pathCost` "
        "explicitement en Python sur des cas concrets.\n"
    ),
    "726d522b": (
        "\n\n---\n\n"
        "**Le pont** : l'admissibilité est `∀ n, h n ≤ hStar n` en Lean-6 (Mathlib, un simple "
        "`∀`). La consistance est `∀ n m, h n ≤ edge n m + h m` (idem). Lean-18 ne réinvente "
        "rien — il **instancie** les concepts de Lean-6 dans le cadre des graphes pondérés. "
        "Search-3-Informed vérifie empiriquement l'admissibilité sur des exemples concrets.\n"
    ),
    "85e7c5cf": (
        "\n\n---\n\n"
        "**Le pont** : `zero_admissible` est l'archétype du lemme trivial mais pédagogiquement "
        "crucial. Lean-6 (Mathlib) regorge de tels lemmes (`add_zero`, `mul_one`, etc.) qui "
        "ancrent les structures algébriques. Lean-18 ancre la théorie A* dans un lemme "
        "analogue. Search-3-Informed illustre les trois heuristiques (`h ≡ 0`, euclidienne, "
        "Manhattan) en Python.\n"
    ),
    "c942eb65": (
        "\n\n---\n\n"
        "**Le pont** : la structure induction sur les listes + lemme auxiliaire est la même "
        "qu'en Lean-6 / `Mathlib.Data.List`. Lean-12b utilise la même structure pour la "
        "sensibilité booléenne. Lean-18 l'instancie pour A*. Search-3-Informed illustre cette "
        "optimalité empiriquement sur des graphes concrets.\n"
    ),
    "a19783f4": (
        "\n\n---\n\n"
        "**Le pont** : l'induction sur les listes est `List.recOn` en Lean-6 / `Mathlib`. Le "
        "lemme auxiliaire `suffix_pathFrom` est un `List.drop` + induction. Lean-18 ne "
        "réinvente rien — il utilise les primitives de Lean-6 sur le type `PathFrom`. "
        "Lean-12b (Sensitivity) utilise exactement la même structure pour ses preuves "
        "spectrales.\n"
    ),
    "928ccb5c": (
        "\n\n---\n\n"
        "**Le pont** : la récurrence sur la queue est `List.recOn` (Lean-6 / Mathlib). La "
        "tactique `linarith` est Lean-6 / `Mathlib.Tactic.Linarith`. Lean-18 ne dépend que "
        "de Lean-6 pour ces preuves. Lean-12b (Sensitivity) utilise la même mécaniquepour "
        "les preuves spectrales (`f² = n Id` puis optimalité).\n"
    ),
    "05bb11e7": (
        "\n\n---\n\n"
        "**Le pont** : `linarith` est `Mathlib.Tactic.Linarith` en Lean-6. L'induction sur "
        "les listes est `List.recOn` en Lean-6 / `Mathlib.Data.List`. Lean-18 est "
        "**structurellement** un Lean-6 (Mathlib) instance : il ne réinvente aucune tactique, "
        "il assemble les primitives existantes pour A*. Lean-12b fait pareil pour la sensibilité.\n"
    ),
    "b454a17d": (
        "\n\n---\n\n"
        "**Le pont** : Lean-18 et Lean-12b sont **structurellement jumeaux** : 4 modules, "
        "preuve par induction sur les listes, théorème final issu d'une accumulation "
        "locale → globale. C'est le **template** de la série Lean : un grand théorème "
        "décomposé en 4 modules factorisés pour réutilisation.\n"
    ),
    "10e00a65": (
        "\n\n---\n\n"
        "**Le pont** : Search-3-Informed (Python, sister de Lean-18) illustre la même "
        "triade d'exercices (prédiction, reproduction, contre-exemple) sur le même "
        "sujet A*. Lean-18 est la **version formelle** de Search-3 : ce qu'on observe "
        "empiriquement en Python est **prouvé** en Lean dans ce notebook.\n"
    ),
    "1259861b": (
        "\n\n---\n\n"
        "**Le pont** : Lean-18 ↔ Lean-12b (cérémonie commune) ↔ Lean-6 (Mathlib / "
        "primitives `List`, `NNReal`, `linarith`) ↔ Search-3-Informed (vue empirique "
        "Python du même sujet). Lean-18 ferme la boucle : on a maintenant la version "
        "*formelle* et la version *empirique* de l'optimalité A*, comparables et "
        "complémentaires. Lean-13 (Kochen-Specker) et Lean-14 (Finiteness) poursuivent "
        "la série Lean avec d'autres théorèmes.\n"
    ),
}


def main():
    raw = NB_PATH.read_text(encoding="utf-8")
    nb = json.loads(raw)
    target_count = len(APPENDS)
    applied = 0
    for cell in nb["cells"]:
        cid = cell.get("id")
        if cid in APPENDS:
            append = APPENDS[cid]
            # L935 ★: source is a list of strings. Append to last item (with \n) or create new entry.
            src = cell["source"]
            if isinstance(src, list):
                # Append as new element preserving list semantics.
                cell["source"] = src + [append]
            else:
                # source is a single string (non-standard nbformat but tolerated).
                cell["source"] = [src, append]
            applied += 1
            print(f"OK: cell_id={cid} append=+{len(append)}c")
    existing_ids = {c.get("id") for c in nb["cells"]}
    missing = [k for k in APPENDS if k not in existing_ids]
    if missing:
        print(f"MISSING cell_ids: {missing}")
    out = json.dumps(nb, indent=1, ensure_ascii=False)
    NB_PATH.write_bytes(out.encode("utf-8"))
    print(f"APPLIED={applied}/{target_count} WROTE {NB_PATH} ({len(out)} chars)")


if __name__ == "__main__":
    main()