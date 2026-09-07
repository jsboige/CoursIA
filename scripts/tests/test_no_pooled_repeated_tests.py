"""Garde non-regression : refuser mannwhitneyu/ttest_ind sur mesures repetees pooled (#14827).

Le defaut que cette garde attrape (issue #14816, constat sur Sudoku-18b avant le
fix ba922303ee / PR #14828) : une boucle double ``for p in puzzles:`` x
``for _ in range(N_RUNS):`` verse les ``n_puzzles * N_RUNS`` chronos dans des
listes plates, puis les passe a un test NON-APPARIE (``mannwhitneyu`` /
``ttest_ind``) comme si c'etaient des echantillons independants. Deux faux
niveaux d'independance en un seul geste :

1. **Pseudo-replication** -- les repetitions d'un meme puzzle sont des mesures
   repetees sur la meme unite ; l'unite experimentale est le puzzle (n=8), pas
   le chrono (n=120).
2. **Test non-apparie sur plan apparie** -- les deux solveurs courent sur le
   MEME puzzle dans la meme iteration de boucle ; ``mannwhitneyu`` est le test
   non-apparie.

Le tell structurel (AST, pas regex) : un nom qui subit ``.append`` dans le
corps d'une boucle ``for ... in range(...)`` elle-meme imbriquee dans une autre
boucle (repetitions x unites), puis atteint un test non-apparie. Le defect
historique reel (cellule 8 pre-fix, ba922303ee~1) blanchit le nom par un
rebinding ``naive_times = np.array(naive_times) * 1000`` (conversion d'unite,
statistiquement transparent) et la cellule 12 testait via une indirection
``pairs = [(..., naive_times, ...)]`` puis ``for name, a, b in pairs``. La garde
propage donc le taint par assignation (une expression AGREGATIVE --
``np.median``/``np.mean``/... -- est le seul bouclier qui le leve), par cible
de boucle iterant un objet tainte, et PORTe le taint d'une cellule a la
suivante (le pool etait en cellule 8, le test en cellule 12). La forme legitime
-- aggregation ``np.median`` par unite dans le corps de la boucle externe, puis
``stats.wilcoxon`` apparie (cellule 8 corrigee de Sudoku-18b) -- n'accumule le
nom teste qu'au niveau externe et n'est pas signalee.

Le motif se valide par ses faux negatifs et ses faux positifs (lecon
count_code_sorry) : voir TestPatternCatches / TestPatternSpares, et le controle
positif sur le notebook HISTORIQUE pre-fix (le defect fondateur lui-meme).

Le scan corpus (TestSudokuFamilyClean) est BLOQUANT : la famille Sudoku doit
rester libre du pattern. Familles extensibles en editant SCANNED_FAMILIES.
"""

from __future__ import annotations

import ast
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "notebook_tools"))

from count_exercises import (  # noqa: E402
    EXCLUDE_DIRS,
    NOTEBOOKS_DIR,
    OUT_OF_CORPUS_KINDS,
    classify_notebook,
)

#: Tests non-apparies vises par la garde. Le wilcoxon signe (apparie) est hors
#: scope : c'est la forme CORRIGEE, et un wilcoxon sur donnees poolees est un
#: defaut d'un autre genre (paired test sur plan pseudo-replique), pas celui
#: que #14827 demande d'attraper.
UNPAIRED_TESTS = frozenset({"mannwhitneyu", "ttest_ind"})

#: Fonctions d'AGREGATION : la seule famille d'expressions qui levent le taint.
#: ``np.median(chunk_par_unite)`` produit une valeur par unite experimentale --
#: c'est la forme corrigee de reference. Tout le reste (``np.array``,
#: ``np.concatenate``, arithmetique element-wise, slicing) preserve le pooling.
AGGREGATORS = frozenset({
    "median", "mean", "average", "percentile", "quantile", "nanmedian", "nanmean",
})

#: Familles de notebooks scannees par la garde bloquante. #14827 : Sudoku d'abord,
#: extensible aux autres familles de benchmark (la detection est family-agnostique).
SCANNED_FAMILIES = ("Sudoku",)


def _is_range_iter(node: ast.expr) -> bool:
    """L'iterable d'une boucle est-il un appel a ``range(...)`` ?

    Une boucle ``range`` est une boucle de REPETITION (compte), pas une
    boucle d'unites (items). C'est la distinction structurelle entre
    ``for _ in range(N_RUNS)`` (re-mesure la meme unite) et
    ``for p in puzzles`` (mesure des unites distinctes).
    """
    return isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "range"


def _is_aggregation(expr: ast.expr) -> bool:
    """``expr`` est-il un appel agregatif (``np.median(x)``, ``x.mean()``...) ?"""
    if isinstance(expr, ast.Call):
        func = expr.func
        name = (
            func.attr if isinstance(func, ast.Attribute)
            else func.id if isinstance(func, ast.Name)
            else None
        )
        return name in AGGREGATORS
    return False


def _aggregation_shield(expr: ast.expr) -> bool:
    """``expr`` produit-il des valeurs par-unite (donc testables legitimement) ?

    Un appel agregatif, une comprehension d'agregats par element, ou une
    arithmetique par-dessus une aggregation (``np.median(x) * 1000`` -- la
    conversion d'unite ne re-pool pas).
    """
    if _is_aggregation(expr):
        return True
    if isinstance(expr, (ast.ListComp, ast.SetComp, ast.GeneratorExp)):
        return _aggregation_shield(expr.elt)
    if isinstance(expr, ast.BinOp):
        return _aggregation_shield(expr.left) or _aggregation_shield(expr.right)
    if isinstance(expr, ast.UnaryOp):
        return _aggregation_shield(expr.operand)
    return False


def _contains_tainted(expr: ast.AST, tainted: set[str]) -> bool:
    return any(
        isinstance(n, ast.Name) and n.id in tainted for n in ast.walk(expr)
    )


def _pool_fed_names(tree: ast.Module) -> set[str]:
    """Noms POOL-FED d'origine : ``.append`` dans une boucle range imbriquee.

    Forme attrapee : ``for p in puzzles:`` ... ``for _ in range(N):`` ...
    ``xs.append(mesure_de_p)`` -- chaque entree de ``xs`` est une repetition
    de la meme unite. La forme corrigee append le nom teste dans le corps de
    la boucle EXTERNE uniquement (agregation par unite) : non tainte ici. Les
    comprehensions en produit croise
    ``[f(p) for p in puzzles for _ in range(N)]`` sont taintees pareil.
    """
    tainted: set[str] = set()
    fors = [n for n in ast.walk(tree) if isinstance(n, ast.For)]
    for node in fors:
        if not _is_range_iter(node.iter):
            continue
        nested_under_another_for = any(
            node is not f and any(sub is node for sub in ast.walk(f))
            for f in fors
        )
        if not nested_under_another_for:
            continue
        for sub in ast.walk(node):
            if (
                isinstance(sub, ast.Call)
                and isinstance(sub.func, ast.Attribute)
                and sub.func.attr == "append"
                and isinstance(sub.func.value, ast.Name)
            ):
                tainted.add(sub.func.value.id)
    for node in ast.walk(tree):
        if isinstance(node, ast.Assign):
            targets = [t.id for t in node.targets if isinstance(t, ast.Name)]
            if isinstance(node.value, ast.ListComp):
                gens = node.value.generators
                if len(gens) >= 2 and any(
                    _is_range_iter(g.iter) for g in gens[1:]
                ):
                    tainted.update(targets)
    return tainted


def _propagate_taint(tree: ast.Module, tainted: set[str]) -> set[str]:
    """Propage le taint dans une cellule : assignations, rebinding, cibles de boucle.

    Le defect historique blanchissait le nom par ``naive_times = np.array(
    naive_times) * 1000`` puis testait via ``pairs = [...]; for name, a, b in
    pairs``. Regles :

    - ``X = <expr>`` : X devient tainte si ``expr`` contient un nom taint ET
      n'est pas bouclier d'agregation ; X est DETAINTEE si ``expr`` l'est
      (le rebinding remplace le contenu -- une mediane n'est pas un pool).
    - ``for a, b in <iter tainte et non-bouclier>`` : cibles taintes
      (l'unpacking de la cellule 12). ``range(...)`` ne taint jamais ses cibles.
    - Fixpoint borne : les rebinding apres coup convergent en quelques passes.
    """
    tainted = set(tainted)
    for _ in range(4):
        before = set(tainted)
        for node in ast.walk(tree):
            if isinstance(node, ast.Assign):
                targets = [t.id for t in node.targets if isinstance(t, ast.Name)]
                shielded = _aggregation_shield(node.value)
                hits = _contains_tainted(node.value, tainted)
                for name in targets:
                    if shielded:
                        tainted.discard(name)
                    elif hits:
                        tainted.add(name)
            elif isinstance(node, ast.AugAssign):
                if (
                    isinstance(node.target, ast.Name)
                    and _contains_tainted(node.value, tainted)
                ):
                    tainted.add(node.target.id)
            elif isinstance(node, ast.For):
                if _is_range_iter(node.iter):
                    continue
                if _aggregation_shield(node.iter):
                    continue
                if _contains_tainted(node.iter, tainted):
                    target = node.target
                    elts = (
                        target.elts if isinstance(target, ast.Tuple)
                        else [target]
                    )
                    for e in elts:
                        if isinstance(e, ast.Name):
                            tainted.add(e.id)
        if tainted == before:
            break
    return tainted


def _unpaired_test_violations(tree: ast.Module, pooled: set[str]) -> list[str]:
    """Appels de test non-apparie dont un argument est pool-fed (directement
    ou dans une expression non-agregative : le rebinding ``np.array(x)*1000``
    du defect historique ne blanchit pas)."""
    out: list[str] = []
    for node in ast.walk(tree):
        if not isinstance(node, ast.Call):
            continue
        func = node.func
        name = (
            func.attr if isinstance(func, ast.Attribute)
            else func.id if isinstance(func, ast.Name)
            else None
        )
        if name not in UNPAIRED_TESTS:
            continue
        for arg in [*node.args, *[kw.value for kw in node.keywords]]:
            if (
                not _aggregation_shield(arg)
                and _contains_tainted(arg, pooled)
            ):
                out.append(
                    f"{name}() argument pool-fed -- mesures repetees versees "
                    "a un test non-apparie sans agregation par unite"
                )
    return out


def violations_in_source(src: str, prior_tainted: set[str] | None = None) -> tuple[list[str], set[str]]:
    """Violations du pattern pooling->test-non-apparie dans un source.

    ``prior_tainted`` : noms deja pool-fes par des cellules precedentes du
    meme notebook (le kernel partage l'etat entre cellules). Retourne
    ``(violations, taint_final)`` pour que l'appelant enchainne les cellules.
    """
    try:
        tree = ast.parse(src)
    except SyntaxError:
        return ([], set(prior_tainted or set()))
    tainted = _propagate_taint(tree, _pool_fed_names(tree) | set(prior_tainted or set()))
    return (_unpaired_test_violations(tree, tainted), tainted)


def violations_in_notebook(path: Path) -> list[tuple[int, str]]:
    """Violations par cellule code d'un notebook : ``[(cell_index, detail)]``.

    Le taint PORTE entre cellules (defect historique : pool en cellule 8,
    mannwhitneyu en cellule 12).
    """
    try:
        nb = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return []
    out: list[tuple[int, str]] = []
    tainted: set[str] = set()
    for i, cell in enumerate(nb.get("cells", [])):
        if cell.get("cell_type") != "code":
            continue
        src = cell.get("source", "")
        src = "".join(src) if isinstance(src, list) else src
        violations, tainted = violations_in_source(src, tainted)
        for v in violations:
            out.append((i, v))
    return out


def _family_notebooks() -> list[Path]:
    """Notebooks des familles scannees, hors dirs exclues et hors corpus."""
    paths: list[Path] = []
    for family in SCANNED_FAMILIES:
        for p in sorted((NOTEBOOKS_DIR / family).rglob("*.ipynb")):
            if any(part in EXCLUDE_DIRS for part in p.parts):
                continue
            if p.name.startswith("."):
                continue
            kind, _ = classify_notebook(p)
            if kind in OUT_OF_CORPUS_KINDS:
                continue
            paths.append(p)
    return paths


def _cell_sources(path: Path) -> list[tuple[int, str]]:
    """Sources de code du notebook, ``[(cell_index, src)]`` (fixture helper)."""
    nb = json.loads(Path(path).read_text(encoding="utf-8"))
    out = []
    for i, cell in enumerate(nb.get("cells", [])):
        if cell.get("cell_type") != "code":
            continue
        src = cell.get("source", "")
        out.append((i, "".join(src) if isinstance(src, list) else src))
    return out


# -------- Validation du motif : formes qui DOIVENT etre attrapees (FN) --------

class TestPatternCatches:
    """Faux negatifs : chaque forme ici non-attrapee est un trou de la garde."""

    def test_pooling_mannwhitneyu_exact_cell8_shape(self):
        """La forme exacte de l'ancienne cellule 8 de Sudoku-18b (defaut fondateur),
        SANS le rebinding np.array -- la forme nue du body de l'issue."""
        src = (
            "naive_times, mrv_times = [], []\n"
            "for p in puzzles:\n"
            "    for _ in range(N_RUNS):\n"
            "        g = [row[:] for row in p]\n"
            "        naive_times.append(solve_naive(g))\n"
            "        mrv_times.append(solve_mrv(g))\n"
            "u, p_value = stats.mannwhitneyu(naive_times, mrv_times)\n"
        )
        violations, _ = violations_in_source(src)
        assert len(violations) == 2

    def test_rebinding_np_array_does_not_launder(self):
        """Le defect historique reel : ``naive_times = np.array(naive_times)*1000``
        est une conversion d'unite statistiquement transparente -- le nom
        reste pool-fed."""
        src = (
            "naive_times, mrv_times = [], []\n"
            "for p in puzzles:\n"
            "    for _ in range(N_RUNS):\n"
            "        naive_times.append(run_a(p))\n"
            "        mrv_times.append(run_b(p))\n"
            "naive_times = np.array(naive_times) * 1000\n"
            "mrv_times = np.array(mrv_times) * 1000\n"
            "u, p_value = stats.mannwhitneyu(naive_times, mrv_times)\n"
        )
        violations, _ = violations_in_source(src)
        assert len(violations) == 2

    def test_indirection_through_pairs_loop(self):
        """La cellule 12 historique : test via ``pairs`` puis unpacking de boucle."""
        src = (
            "pairs = [('n vs m', naive_times, mrv_times),\n"
            "         ('n vs r', naive_times, reverse_times)]\n"
            "for name, a, b in pairs:\n"
            "    _, p = stats.mannwhitneyu(a, b, alternative='two-sided')\n"
        )
        violations, _ = violations_in_source(
            src, prior_tainted={"naive_times", "mrv_times", "reverse_times"}
        )
        assert len(violations) == 2

    def test_taint_carries_across_cells(self):
        """Pool en cellule A, test en cellule B : le kernel partage l'etat."""
        cell_a = (
            "naive_times = []\n"
            "for p in puzzles:\n"
            "    for _ in range(N_RUNS):\n"
            "        naive_times.append(run(p))\n"
        )
        cell_b = "u, p_value = stats.mannwhitneyu(naive_times, baseline)\n"
        violations_a, taint = violations_in_source(cell_a)
        assert violations_a == []
        violations_b, _ = violations_in_source(cell_b, taint)
        assert len(violations_b) == 1

    def test_pooling_ttest_ind(self):
        src = (
            "xs, ys = [], []\n"
            "for case in cases:\n"
            "    for rep in range(15):\n"
            "        xs.append(time_a(case))\n"
            "        ys.append(time_b(case))\n"
            "t, p = ttest_ind(xs, ys)\n"
        )
        violations, _ = violations_in_source(src)
        assert len(violations) == 2

    def test_scipy_attribute_form(self):
        src = (
            "for p in puzzles:\n"
            "    for _ in range(N_RUNS):\n"
            "        times.append(run(p))\n"
            "res = scipy.stats.mannwhitneyu(times, baseline)\n"
        )
        violations, _ = violations_in_source(src)
        assert violations != []

    def test_pooling_via_list_comprehension(self):
        src = (
            "times = [solve(p) for p in puzzles for _ in range(N_RUNS)]\n"
            "u, p_value = stats.mannwhitneyu(times, other)\n"
        )
        violations, _ = violations_in_source(src)
        assert violations != []

    def test_keyword_argument_form(self):
        src = (
            "for p in puzzles:\n"
            "    for _ in range(N_RUNS):\n"
            "        naive.append(run(p))\n"
            "res = stats.mannwhitneyu(x=naive, y=ref, alternative='two-sided')\n"
        )
        violations, _ = violations_in_source(src)
        assert violations != []


# -------- Validation du motif : formes legitimes qui DOIVENT passer (FP) --------

class TestPatternSpares:
    """Faux positifs : chaque forme ici signalee serait une garde inutilisable."""

    def test_corrected_form_median_per_unit_then_wilcoxon(self):
        """La cellule 8 corrigee de Sudoku-18b (ba922303ee) : forme de reference.

        Le nom teste (naive_times) n'est append QUE dans le corps de la boucle
        externe, avec agregation np.median par unite ; le test est wilcoxon
        (apparie). Les temporaires internes (ts_naive) sont taintes mais ne
        rejoignent jamais un test non-apparie.
        """
        src = (
            "naive_times, mrv_times = [], []\n"
            "for p in puzzles:\n"
            "    ts_naive, ts_mrv = [], []\n"
            "    for _ in range(N_RUNS):\n"
            "        ts_naive.append(time_naive(p))\n"
            "        ts_mrv.append(time_mrv(p))\n"
            "    naive_times.append(np.median(ts_naive) * 1000)\n"
            "    mrv_times.append(np.median(ts_mrv) * 1000)\n"
            "w_stat, p_value = stats.wilcoxon(naive_times, mrv_times)\n"
        )
        violations, _ = violations_in_source(src)
        assert violations == []

    def test_truly_independent_units_disjoint_puzzles(self):
        """Benchmarks disjoints : chaque liste est alimentee par SES puzzles propres,
        en boucle simple -- les unites sont reellement independantes."""
        src = (
            "times_a = [time_it(p) for p in puzzles_a]\n"
            "times_b = [time_it(p) for p in puzzles_b]\n"
            "u, p = stats.mannwhitneyu(times_a, times_b)\n"
        )
        violations, _ = violations_in_source(src)
        assert violations == []

    def test_aggregation_between_pool_and_test(self):
        """Le nom teste n'est PAS le nom poole : l'agregation intermediaire
        neutralise le pooling (une valeur par unite atteint le test)."""
        src = (
            "raw = []\n"
            "for p in puzzles:\n"
            "    for _ in range(N_RUNS):\n"
            "        raw.append(run(p))\n"
            "medians = [np.median(raw[i * N_RUNS:(i + 1) * N_RUNS]) for i in range(len(puzzles))]\n"
            "u, p = stats.mannwhitneyu(medians, baseline)\n"
        )
        violations, _ = violations_in_source(src)
        assert violations == []

    def test_pooled_name_to_paired_test_out_of_scope(self):
        """Wilcoxon sur un nom poole : defaut reel mais d'un autre genre
        (test apparie sur plan pseudo-replique) -- hors scope #14827."""
        src = (
            "xs, ys = [], []\n"
            "for p in puzzles:\n"
            "    for _ in range(N_RUNS):\n"
            "        xs.append(a(p)); ys.append(b(p))\n"
            "w, p = stats.wilcoxon(xs, ys)\n"
        )
        violations, _ = violations_in_source(src)
        assert violations == []

    def test_solver_internals_nested_range_loops_never_tested(self):
        """Boucles range imbriquees legitimes (recherche de case, backtracking) :
        aucun nom tainte n'atteint un test statistique."""
        src = (
            "def solve(g):\n"
            "    for r in range(9):\n"
            "        for c in range(9):\n"
            "            steps.append((r, c))\n"
            "    return True\n"
            "u, p = stats.mannwhitneyu(reference_a, reference_b)\n"
        )
        violations, _ = violations_in_source(src)
        assert violations == []

    def test_single_level_loop_over_units(self):
        """Une seule boucle, une mesure par unite : n = nombre d'unites, pas de pooling."""
        src = (
            "times = []\n"
            "for p in puzzles:\n"
            "    times.append(time_it(p))\n"
            "u, p = stats.mannwhitneyu(times, ref)\n"
        )
        violations, _ = violations_in_source(src)
        assert violations == []

    def test_aggregated_median_inside_test_call(self):
        """La mediane (scalaire) du pool comparee : aggregation dans l'argument
        meme du test -- pas un pooling d'echantillons."""
        src = (
            "for p in puzzles:\n"
            "    for _ in range(N_RUNS):\n"
            "        xs.append(run(p)); ys.append(run_b(p))\n"
            "res = stats.mannwhitneyu(np.median(xs), np.median(ys))\n"
        )
        violations, _ = violations_in_source(src)
        assert violations == []


# -------- Controle positif : le defect HISTORIQUE reel doit etre attrape --------

class TestHistoricalDefect:
    """La garde doit attraper le notebook pre-fix (ba922303ee~1), pas seulement
    des formes synthetiques. C'est le controle positif qui a manque a la
    premiere version de cette garde (detecteur Name-seul) : le rebinding
    ``np.array(x) * 1000`` et l'indirection ``pairs`` la blanchissaient."""

    def test_pre_fix_cell8_pooled_mannwhitneyu_is_caught(self):
        """Cellule 8 pre-fix extraite verbatim : le defaut fondateur."""
        src = (
            "naive_times, mrv_times = [], []\n"
            "for p in puzzles:\n"
            "    for _ in range(N_RUNS):\n"
            "        g = [row[:] for row in p]\n"
            "        t0 = time.perf_counter(); solve_naive(g)\n"
            "        naive_times.append(time.perf_counter() - t0)\n"
            "        g = [row[:] for row in p]\n"
            "        t0 = time.perf_counter(); solve_mrv(g)\n"
            "        mrv_times.append(time.perf_counter() - t0)\n"
            "naive_times = np.array(naive_times) * 1000\n"
            "mrv_times = np.array(mrv_times) * 1000\n"
            "u_stat, p_value = stats.mannwhitneyu(naive_times, mrv_times, alternative='two-sided')\n"
        )
        violations, _ = violations_in_source(src)
        assert len(violations) == 2

    def test_pre_fix_cell12_indirection_is_caught(self):
        """Cellule 12 pre-fix extraite verbatim, avec le taint porte de la cellule 8."""
        src = (
            "reverse_times = []\n"
            "for p in puzzles:\n"
            "    for _ in range(N_RUNS):\n"
            "        reverse_times.append(time_reverse(p))\n"
            "pairs = [('naif vs MRV', naive_times, mrv_times),\n"
            "         ('MRV vs reverse', mrv_times, reverse_times)]\n"
            "for name, a, b in pairs:\n"
            "    _, p = stats.mannwhitneyu(a, b, alternative='two-sided')\n"
        )
        violations, _ = violations_in_source(
            src, prior_tainted={"naive_times", "mrv_times"}
        )
        assert len(violations) == 2


# -------- Scan corpus bloquant : la famille Sudoku doit rester propre --------

class TestSudokuFamilyClean:
    """Non-regression bloquante (#14827) : aucun notebook de la famille Sudoku
    ne verse de mesures repetees pooled a un test non-apparie."""

    def test_family_scanned_is_not_empty(self):
        """Controle positif : le scan voit bien des notebooks (garde contre un
        repertoire deplace/renomme qui rendrait la garde vide donc muette)."""
        notebooks = _family_notebooks()
        assert notebooks, "SCANNED_FAMILIES n'a trouve aucun notebook -- la garde scanne un corpus vide"
        names = [p.name for p in notebooks]
        assert "Sudoku-18b-Statistical-Comparison-Python.ipynb" in names

    def test_sudoku_18b_reference_form_passes(self):
        """Le notebook fondateur, dans sa forme corrigee (ba922303ee), doit passer."""
        path = NOTEBOOKS_DIR / "Sudoku" / "Sudoku-18b-Statistical-Comparison-Python.ipynb"
        assert violations_in_notebook(path) == []

    def test_no_pooled_repeated_tests_in_family(self):
        violations = []
        for p in _family_notebooks():
            for cell_idx, detail in violations_in_notebook(p):
                violations.append(f"{p.name} cell {cell_idx}: {detail}")
        assert not violations, (
            "Tests non-apparies sur mesures repetees pooled (pseudo-replication) :\n"
            + "\n".join(violations)
        )
