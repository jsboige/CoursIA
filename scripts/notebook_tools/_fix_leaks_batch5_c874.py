"""Batch fix solution leaks tranche #c874 — Issue #8053.

6 confirmed HIGH leaks across 5 families (FP Lean-17 cell#14 removed - was
preceded by "Interprétation" not "Exercice", content = methodological table).

Strategy: stub the solution code (replace with # TODO etudiant + # Indice)
following the pattern proven by PR #8402 (DecPyMC-5 cells 70/72/73).
Special case: 2.6-Clustering cell#14 is a DUPLICATE solution to cell#15
(real Exercice 2 stub) — DELETE cell#14 entirely.

Output clearing: cells whose output reveals the numerical answer have
outputs cleared (C.1 leak-semantics trumps C.2 outputs-preservation).
execution_count is preserved where possible to keep cell state aware.

Sub-genre: re-execution of these 6 cells deferred to per-NB owner
(LE-1: GPU/Pyro, QC-2: QuantConnect Cloud, Search-3: Python local,
   ML-4: Python local). This PR scope = structure only, no kernel re-exec.
"""

import json
import sys
from pathlib import Path

WORKTREE = Path("D:/Dev/CoursIA-2-c874-8053-de-leak")

# (rel_path, cell_idx, action, new_source_or_special)
# action: 'stub' (replace source, clear outputs) or 'delete' (remove cell)
AFFECTED = [
    # 1. 2.6-Clustering-KMeans-PCA: cell#14 is a DUPLICATE solution to cell#15 (real stub)
    (
        "MyIA.AI.Notebooks/ML/DataScienceWithAgents/02-ML-Cours/2.6-Clustering-KMeans-PCA.ipynb",
        14,
        "delete",
        None,
    ),
    # 2. QC-Py-12-Backtesting-Analysis: Exercice 2 has no stub. Replace day-of-week solution with stub.
    (
        "MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-12-Backtesting-Analysis.ipynb",
        50,
        "stub",
        "# --- TODO etudiant : analyse temporelle des returns par jour de semaine et par mois ---\n"
        "# Indice :\n"
        "#   1. Ajouter une colonne 'day_of_week' extraite de backtest_df.index.dayofweek\n"
        "#      Noms : ['Lundi', 'Mardi', 'Mercredi', 'Jeudi', 'Vendredi']\n"
        "#   2. Grouper par 'day_of_week' puis par 'month' et calculer la moyenne de 'strategy_returns'\n"
        "#   3. Afficher deux bar plots cote a cote (1x2 subplots) :\n"
        "#      - axes[0] : returns moyens par jour, colour green/red selon signe\n"
        "#      - axes[1] : returns moyens par mois (Jan..Dec), idem\n"
        "#      Titre : 'Returns Moyens par Jour de Semaine' / '... par Mois' fontweight='bold'\n"
        "#      ylabel = 'Return Moyen (%)', grid alpha=0.3, axhline(0, color='black', lw=0.5)\n"
        "#   4. Imprimer 'Returns par jour de semaine :' puis le DataFrame agrege\n"
        "pass  # TODO etudiant\n",
    ),
    # 3. QC-Py-13-Alpha-Models: Exercice 2 has no stub. Replace AdvancedSymbolData template with stub.
    (
        "MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-13-Alpha-Models.ipynb",
        36,
        "stub",
        "# --- TODO etudiant : template SymbolData avance (multi-indicateurs) ---\n"
        "# Indice : creer une classe AdvancedSymbolData qui wrap plusieurs indicateurs\n"
        "#   quantconnect.AlgorithmImports afin d'eviter de les reinstancier pour chaque Alpha Model.\n"
        "# Structure attendue :\n"
        "#   class AdvancedSymbolData:\n"
        "#       def __init__(self, algorithm, symbol, resolution=Resolution.Daily):\n"
        "#           # Stocker self.algorithm, self.symbol\n"
        "#           # Initialiser : SMA(10), SMA(50), EMA(20), RSI(14), MACD(12,26,9),\n"
        "#           #               MOM%(20), ATR(14), BB(20,2)\n"
        "#           # Enregistrer chaque indicateur avec algorithm.RegisterIndicator(...)\n"
        "#           # Warmup : charger ~100 barres via algorithm.History(symbol, ...)\n"
        "#       @property IsReady(self): tous les indicateurs doivent renvoyer True\n"
        "#       @property IsBullishTrend(self): SMA fast > SMA slow\n"
        "#       @property IsOversold(self): RSI < 30\n"
        "#       @property IsOverbought(self): RSI > 70\n"
        "#       @property MacdBullishCross(self): MACD > signal\n"
        "pass  # TODO etudiant\n",
    ),
    # 4. App-20-SudokuBenchmark-Python: Exercice 2 has no stub. Replace DLXSolverInstrumented with stub.
    (
        "MyIA.AI.Notebooks/Search/Applications/CSP/App-20-SudokuBenchmark-Python.ipynb",
        19,
        "stub",
        "# --- TODO etudiant : instrumenter DLXSolver pour compter les noeuds explores ---\n"
        "# Indice :\n"
        "#   - Creer une sous-classe DLXSolverInstrumented(DLXSolver) qui override la methode _search\n"
        "#     pour incrementer aussi stats['nodes_visited'] (different de stats['calls']).\n"
        "#   - Creer une fonction run_dlx_instrumented(grid) qui :\n"
        "#       1. deep-copy la grille,\n"
        "#       2. instancie DLXSolverInstrumented(),\n"
        "#       3. appelle solver.solve(g, stats) avec stats = {'calls': 0, 'nodes_visited': 0},\n"
        "#       4. chronometre avec time.perf_counter(),\n"
        "#       5. renvoie (succes, elapsed_ms, stats['calls'], stats['nodes_visited']).\n"
        "#   - Tester sur HARD_GRID et imprimer le resultat pour verifier (n'appelez PAS cette\n"
        "#     fonction ici : executez-la dans la cellule suivante apres implementation).\n"
        "pass  # TODO etudiant\n",
    ),
    # 5. App-9-EdgeDetection: Exercice 1 has no stub. Replace Laplacian reference code with stub.
    (
        "MyIA.AI.Notebooks/Search/Applications/Hybrid/App-9-EdgeDetection.ipynb",
        36,
        "stub",
        "# --- TODO etudiant : reference Laplacien pour la fitness du GA ---\n"
        "# Indice :\n"
        "#   - Importer 'from scipy.ndimage import laplace'.\n"
        "#   - laplacian_reference = np.abs(laplace(original_image.astype(np.float64)))\n"
        "#   - Normaliser en [0, 255] si max > 0 :\n"
        "#       laplacian_reference = (laplacian_reference / laplacian_reference.max()) * 255.0\n"
        "#   - Afficher 1x2 subplots : axes[0] sobel_reference (cmap='gray', title='Reference Sobel'),\n"
        "#                              axes[1] laplacian_reference (cmap='gray', title='Reference Laplacien')\n"
        "#   - plt.suptitle('Exercice 1 : Sobel vs Laplacien', fontweight='bold')\n"
        "#   - plt.tight_layout(); plt.show(); plt.close()\n"
        "# Question : relancez le GA en remplacant 'sobel_reference' par 'laplacian_reference'\n"
        "#            dans la fonction de fitness. Le GA converge-t-il plus ou moins vite ? Pourquoi ?\n"
        "pass  # TODO etudiant\n",
    ),
    # 6. Oncology-Planning: Exercice 3 has no stub. Replace Pyro predictive simulation with stub.
    (
        "MyIA.AI.Notebooks/CaseStudies/Oncology-Planning/solution/Oncology-Planning.ipynb",
        23,
        "stub",
        "# --- TODO etudiant : simulation predictive de l'avenir avec le profil infere ---\n"
        "# Indice :\n"
        "#   - predictive = Predictive(onco_model.model, guide=onco_model.guide,\n"
        "#                            num_samples=100, return_sites=['obs_gb_3'])\n"
        "#   - Scénario 1 - maintien de la dose (100mg) :\n"
        "#       doses_std = torch.tensor([100.0, 0.0, 0.0, 100.0])\n"
        "#       samples_std = predictive(doses_std)\n"
        "#       gb_std = samples_std['obs_gb_3']\n"
        "#       risque_std = (gb_std < 2000).float().mean()\n"
        "#   - Scénario 2 - reduction de dose (50mg) :\n"
        "#       doses_red = torch.tensor([100.0, 0.0, 0.0, 50.0])\n"
        "#       samples_red = predictive(doses_red)\n"
        "#       gb_red = samples_red['obs_gb_3']\n"
        "#       risque_red = (gb_red < 2000).float().mean()\n"
        "#   - Imprimer les deux risques (en %) et conclure sur l'interet d'une reduction de dose.\n"
        "pass  # TODO etudiant\n",
    ),
]


def stub_cell(cell: dict, new_source: str) -> tuple[bool, str]:
    """Replace cell source with stub, clear outputs. Returns (success, msg)."""
    if cell.get("cell_type") != "code":
        return False, "not a code cell"
    # Preserve execution_count (cell stays 'executed' state per papermill C.2)
    old_count = cell.get("execution_count")
    old_outputs = cell.get("outputs", [])
    new_lines = new_source.split("\n")
    cell["source"] = [line + "\n" for line in new_lines[:-1]]
    if new_lines[-1]:
        cell["source"].append(new_lines[-1])
    # Clear outputs (the leaked solution's outputs reveal the answer)
    cell["outputs"] = []
    # Note: keep execution_count to mark the cell as already-runnable
    # (after stubification, re-exec by kernel produces expected stub output)
    return True, f"stubbed (was {len(old_outputs)} outputs, count={old_count}, now 0)"


def delete_cell(cells: list, idx: int) -> tuple[bool, str]:
    """Remove cell at idx. Returns (success, msg)."""
    if idx < 0 or idx >= len(cells):
        return False, f"idx {idx} out of range"
    removed = cells.pop(idx)
    return True, f"deleted cell (was {removed.get('cell_type')}, len={len(''.join(removed.get('source', [])) if isinstance(removed.get('source'), list) else removed.get('source', ''))})"


def fix_notebook(rel_path: str, ops: list) -> tuple[bool, str]:
    """Apply operations to notebook. Returns (success, msg)."""
    nb_path = WORKTREE / rel_path
    if not nb_path.exists():
        return False, f"file not found: {nb_path}"

    with open(nb_path, "rb") as f:
        raw = f.read()
    lf_check = raw.count(b"\r\n") == 0
    nb = json.loads(raw.decode("utf-8"))
    cells = nb.get("cells", [])

    msgs = []
    # Process operations in REVERSE order to preserve indexes if any deletes
    # (only one delete here, so order matters slightly)
    for rel_path_check, idx, action, new_source in sorted(ops, key=lambda x: -x[1]):
        if rel_path_check != rel_path:
            continue
        if idx >= len(cells):
            msgs.append(f"  SKIP cell#{idx} ({action}): out of range (len={len(cells)})")
            continue
        if action == "stub":
            ok, m = stub_cell(cells[idx], new_source)
            msgs.append(f"  cell#{idx} stub: {m}" if ok else f"  cell#{idx} SKIP: {m}")
        elif action == "delete":
            ok, m = delete_cell(cells, idx)
            msgs.append(f"  cell#{idx} delete: {m}" if ok else f"  cell#{idx} SKIP: {m}")
        else:
            msgs.append(f"  cell#{idx} UNKNOWN action: {action}")

    # Write back via binary, LF-only
    new_raw = json.dumps(nb, indent=1, ensure_ascii=False).encode("utf-8")
    if not new_raw.endswith(b"\n"):
        new_raw += b"\n"
    assert new_raw.count(b"\r\n") == 0, "LF-only violation!"
    if not lf_check:
        msgs.append(f"  WARNING: original file had CRLF, now normalized to LF")
    nb_path.write_bytes(new_raw)

    return True, "\n".join(msgs)


def main():
    print("c.874 batch fix #8053 starting...")
    # Group by notebook
    by_nb = {}
    for rel_path, idx, action, new_source in AFFECTED:
        by_nb.setdefault(rel_path, []).append((rel_path, idx, action, new_source))

    total_nb = 0
    total_ok = 0
    for rel_path, ops in sorted(by_nb.items()):
        print(f"\n=== {rel_path} ({len(ops)} ops) ===")
        total_nb += 1
        ok, msg = fix_notebook(rel_path, ops)
        print(msg)
        if ok:
            total_ok += 1

    print(f"\n{'='*60}")
    print(f"Batch fix: {total_ok}/{total_nb} notebooks processed (atomic per-NB)")


if __name__ == "__main__":
    main()
