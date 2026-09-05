#!/usr/bin/env python3
"""Gate: refuse repeated-measures POOLED into an UNPAIRED test (#14827).

Fondation (#14816, main pre-fix, cellules 8 et 12 de Sudoku-18b) : la
boucle chronometre 2 solveurs sur 8 puzzles x 15 repetitions, verse les
120 chronos dans deux listes plates accumulees dans la boucle INTERIEURE
de repetition, puis les passe a ``stats.mannwhitneyu`` comme 120
observations independantes. Deux defauts en un geste :

1. **Pseudo-replication** -- l'unite experimentale est le puzzle : n = 8,
   pas 120. Les 15 repetitions d'un meme puzzle sont des mesures repetees
   sur la meme unite, pas 15 tirages.
2. **Test non-apparie sur un plan apparie** -- les deux solveurs tournent
   sur le MEME puzzle dans la meme iteration ; les mesures sont appariees
   par construction, et ``mannwhitneyu`` suppose des echantillons
   independants.

La section 2 du meme notebook avait deja mesure que la variance
inter-puzzles domine (medianes 0,3 a 3,3 ms sur des puzzles de meme
difficulte nominale) ; le test poole traite ce facteur dominant comme du
bruit d'echantillonnage. Sur les 8 vraies unites, le verdict
``MRV vs reverse`` S'INVERSE (p ~ 1e-23 -> 1,95e-01). Le p poole n'etait
pas une mesure de l'effet : en separation quasi-complete il ne depend
plus que de n et du rang.

Detection AST, pas regex, a l'echelle du NOTEBOOK. Un defaut est un
ACCUMULATEUR -- un nom de liste alimente par ``.append(...)`` dans une
boucle IMBRIQUEE dans une autre boucle, ou construit par une
comprehension a >= 2 generateurs dont au moins un itere un ``range()``
-- qui atteint un appel de test NON APPARIE (``mannwhitneyu`` /
``ttest_ind``), directement (argument Name, eventuellement enveloppe
dans ``np.array`` / ``np.asarray``), via une TABLE DE PAIRES (``pairs =
[(label, x, y), ...]`` deballée ``for name, a, b in pairs:`` -- la
forme reelle de la cellule fondatrice 12), ou PAR DELA LES CELLULES
(l'accumulateur est construit dans une cellule anterieure et teste dans
une ulterieure ; l'etat est porte par le nom, comme le kernel le porte).
La correction legitime -- agreger par unite (``np.median`` des
repetitions) dans la boucle EXTERIEURE, puis un test APPARIE
(``wilcoxon``) sur les listes agregees -- ne declenche rien : les listes
brutes de repetition (``ts_naive``, ...) n'atteignent jamais le test,
et les listes testees sont agregees dans la boucle externe. Le
discriminateur est STRUCTUREL (ou l'accumulation se produit par rapport
a l'imbrication), pas lexical.

Le nesting general (toute boucle dans une boucle, pas seulement
``range``) est deliberé : une boucle grille x graine poussee vers un test
non apparie est la MEME erreur statistique (mesures repetees sur la meme
unite). Le bootstrap legitime -- une boucle SEULE de resampling -- est
exempt par structure.

Un detecteur se valide par ses FAUX NEGATIFS (``--self-test``) : les
cellules fondatrices DOIVENT etre attrapees -- y compris la cellule 12
fondatrice, dont le test ne nomme JAMAIS les accumulateurs (tables de
paires + deballage), forme qu'une premiere version de ce detecteur a
manquee et qui est restee fixture -- les cellules corrigees et les
formes legitimes voisines (bootstrap, wilcoxon apparie, demo marquee)
DOIVENT passer. Un detecteur qui ne matche que le texte exact de la
fondation est une liste de hits, pas un garde.

Demo pedagogique deliberée : une cellule code portant le marqueur
``# pooled-demo`` dans sa source est sautee et comptee ``skipped`` -- un
notebook peut MONTRER la mauvaise methode, a condition de le dire.

Modes :
    <base-ref>          GATE (ratchet) : ne juger que les cellules code
                        AJOUTEES ou MODIFIEES entre
                        merge-base(base-ref, HEAD) et HEAD. La dette
                        pre-existante ne gate jamais -- c'est un
                        ratchet, pas une morale retroactive.
    --all               balayage de toute la famille sur HEAD.
    --self-test         rejouer les fixtures embarquees (sans git).
    --series <name>     famille a balayer (defaut : Sudoku).
    --json              sortie machine-lisible.

Exit : 0 propre, 1 defauts trouves (ou self-test KO), 2 usage.
"""

from __future__ import annotations

import argparse
import ast
import json
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent

UNPAIRED_TESTS = {"mannwhitneyu", "ttest_ind"}
ARRAY_WRAPPERS = {"array", "asarray"}
DEMO_MARKER = "# pooled-demo"
DEFAULT_SERIES = "Sudoku"
EXCLUDED_PATH_PARTS = ("_archive", ".ipynb_checkpoints", "_peters", ".lake")


# ---------------------------------------------------------------------------
# Detection AST -- une cellule code
# ---------------------------------------------------------------------------

def _iter_appends(node: ast.AST):
    """Tous les appels ``X.append(...)`` du sous-arbre, avec le nom X."""
    for sub in ast.walk(node):
        if (isinstance(sub, ast.Call)
                and isinstance(sub.func, ast.Attribute)
                and sub.func.attr == "append"
                and isinstance(sub.func.value, ast.Name)):
            yield sub.func.value.id, sub.lineno


def _nested_loop_accumulators(tree: ast.AST) -> dict[str, int]:
    """Noms alimentes par .append dans une boucle IMBRIQUEE dans une autre.

    La cellule corrigee accumule ses chronos bruts (``ts_naive``) dans la
    boucle interieure mais ne les teste jamais : ces noms sont collectes
    ici et n'ont d'effet que s'ils atteignent un test non apparie.
    """
    acc: dict[str, int] = {}
    for outer in ast.walk(tree):
        if not isinstance(outer, ast.For):
            continue
        for sub in ast.walk(outer):
            if sub is outer or not isinstance(sub, ast.For):
                continue
            for name, line in _iter_appends(sub):
                acc.setdefault(name, line)
    return acc


def _comprehension_accumulators(tree: ast.AST) -> dict[str, int]:
    """Noms construits par comprehension a >= 2 generateurs dont un range.

    Forme : ``x = [f(p) for p in puzzles for _ in range(N_RUNS)]`` puis
    ``mannwhitneyu(x, y)`` -- le pooling reeloge en expression.
    """
    acc: dict[str, int] = {}
    for node in ast.walk(tree):
        if not (isinstance(node, ast.Assign)
                and isinstance(node.value, ast.ListComp)):
            continue
        comp = node.value
        if len(comp.generators) < 2:
            continue
        has_range = any(
            isinstance(g.iter, ast.Call)
            and isinstance(g.iter.func, ast.Name)
            and g.iter.func.id == "range"
            for g in comp.generators
        )
        if not has_range:
            continue
        for target in node.targets:
            if isinstance(target, ast.Name):
                acc.setdefault(target.id, node.lineno)
    return acc


def _names_reaching_test(node: ast.AST) -> set[str]:
    """Noms passes (directement ou via np.array/np.asarray) a un test."""
    if isinstance(node, ast.Name):
        return {node.id}
    if (isinstance(node, ast.Call)
            and isinstance(node.func, ast.Attribute)
            and node.func.attr in ARRAY_WRAPPERS
            and len(node.args) == 1):
        return _names_reaching_test(node.args[0])
    return set()


def _is_unpaired_test(call: ast.Call) -> str | None:
    f = call.func
    if isinstance(f, ast.Name) and f.id in UNPAIRED_TESTS:
        return f.id
    if isinstance(f, ast.Attribute) and f.attr in UNPAIRED_TESTS:
        return f.attr
    return None


def _alias_map(tree: ast.AST, pooled_names: set[str]) -> dict[str, set[str]]:
    """Alias deballés d'une table de paires vers les noms pools qu'ils portent.

    Forme fondatrice (cellule 12) : ``pairs = [(label, x, y), ...]`` puis
    ``for name, a, b in pairs: ... stats.mannwhitneyu(a, b)`` -- le test
    ne nomme jamais les accumulateurs. La table projette les positions :
    la position i de chaque tuple porte le nom pooled (ou None).
    """
    tables_pos: dict[str, list[list[str | None]]] = {}
    for node in ast.walk(tree):
        if not (isinstance(node, ast.Assign)
                and isinstance(node.value, ast.List)):
            continue
        elts = node.value.elts
        if not elts or not all(isinstance(e, ast.Tuple) for e in elts):
            continue
        target = node.targets[0]
        if not isinstance(target, ast.Name):
            continue
        cols: list[list[str | None]] = []
        for tup in elts:
            row: list[str | None] = []
            for item in tup.elts:
                if isinstance(item, ast.Name) and item.id in pooled_names:
                    row.append(item.id)
                else:
                    row.append(None)
            cols.append(row)
        tables_pos[target.id] = cols
    aliases: dict[str, set[str]] = {}
    for node in ast.walk(tree):
        if not (isinstance(node, ast.For)
                and isinstance(node.iter, ast.Name)
                and node.iter.id in tables_pos):
            continue
        cols = tables_pos[node.iter.id]
        if not (isinstance(node.target, ast.Tuple)
                and cols
                and len(node.target.elts) == len(cols[0])):
            continue
        for i, t in enumerate(node.target.elts):
            if not isinstance(t, ast.Name):
                continue
            carried = {row[i] for row in cols
                       if i < len(row) and row[i] is not None}
            if carried:
                aliases[t.id] = carried
    return aliases


def analyze_cell(source: str, pooled_in: dict[str, int] | None = None,
                 cell_index: int = 0) -> tuple[list[dict], dict[str, int]]:
    """Defauts de pooling d'une cellule code + etat pooled mis a jour.

    ``pooled_in`` porte les accumulateurs des cellules ANTERIEURES (le
    kernel partage l'etat entre cellules ; le detecteur fait de meme).
    Retour : (defauts, pooled_out). Les defauts sont des dicts
    {test, pooled, append_cell, append_line, test_line, cell}.
    Une cellule marquee ``# pooled-demo`` ne teste ni n'accumule.
    """
    if DEMO_MARKER in source:
        return [], dict(pooled_in or {})
    try:
        tree = ast.parse(source)
    except SyntaxError:
        return [], dict(pooled_in or {})  # non parsable: #13326
    pooled = dict(pooled_in or {})
    acc = _nested_loop_accumulators(tree)
    acc.update(_comprehension_accumulators(tree))
    for name, line in acc.items():
        pooled.setdefault(name, (cell_index, line))
    # relier un nom a une valeur neuve lui retire son statut pooled
    for node in ast.walk(tree):
        if not isinstance(node, ast.Assign):
            continue
        target = node.targets[0]
        if not (isinstance(target, ast.Name)
                and target.id in pooled
                and target.id not in acc):
            continue
        refs = {n.id for n in ast.walk(node.value)
                if isinstance(n, ast.Name)}
        if not (refs & set(pooled)) and not (refs & set(acc)):
            del pooled[target.id]
    aliases = _alias_map(tree, set(pooled))
    defects: list[dict] = []
    for node in ast.walk(tree):
        if not isinstance(node, ast.Call):
            continue
        test = _is_unpaired_test(node)
        if test is None:
            continue
        tested: set[str] = set()
        for arg in list(node.args) + [kw.value for kw in node.keywords]:
            tested |= _names_reaching_test(arg)
        hit: set[str] = set()
        for name in tested:
            if name in pooled:
                hit.add(name)
            elif name in aliases:
                hit |= {a for a in aliases[name] if a in pooled}
        if hit:
            append_cell = min(pooled[n][0] for n in hit)
            append_line = min(pooled[n][1] for n in hit
                              if pooled[n][0] == append_cell)
            defects.append({
                "cell": cell_index,
                "test": test,
                "pooled": sorted(hit),
                "append_cell": append_cell,
                "append_line": append_line,
                "test_line": node.lineno,
            })
    return defects, pooled


def is_demo_cell(source: str) -> bool:
    return DEMO_MARKER in source


# ---------------------------------------------------------------------------
# Balayage notebook / famille
# ---------------------------------------------------------------------------

def scan_notebook(path: Path) -> list[dict]:
    out: list[dict] = []
    try:
        nb = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return out
    code_cells = [(i, "".join(c.get("source", [])))
                  for i, c in enumerate(nb.get("cells", []))
                  if c.get("cell_type") == "code"]
    pooled: dict[str, int] = {}
    for idx, source in code_cells:
        if is_demo_cell(source):
            out.append({"cell": idx, "skipped_demo": True,
                        "path": str(path)})
            continue
        defects, pooled = analyze_cell(source, pooled, idx)
        for d in defects:
            out.append({"path": str(path), **d})
    return out


def family_notebooks(series: str = DEFAULT_SERIES) -> list[Path]:
    d = REPO_ROOT / "MyIA.AI.Notebooks" / series
    if not d.is_dir():
        return []
    nbs = []
    for p in sorted(d.rglob("*.ipynb")):
        if any(part in p.parts for part in EXCLUDED_PATH_PARTS):
            continue
        nbs.append(p)
    return nbs


def sweep(series: str = DEFAULT_SERIES) -> list[dict]:
    out: list[dict] = []
    for nb in family_notebooks(series):
        out.extend(scan_notebook(nb))
    return out


# ---------------------------------------------------------------------------
# Gate ratchet -- cellules ajoutees/modifiees vs merge-base
# ---------------------------------------------------------------------------

def _merge_base(base_ref: str) -> str | None:
    r = subprocess.run(
        ["git", "merge-base", base_ref, "HEAD"],
        cwd=REPO_ROOT, capture_output=True, text=True, encoding="utf-8",
    )
    if r.returncode != 0:
        return None
    return r.stdout.strip()


def _changed_notebooks(base: str, series: str) -> list[str]:
    r = subprocess.run(
        ["git", "diff", "--name-only", base, "HEAD"],
        cwd=REPO_ROOT, capture_output=True, text=True, encoding="utf-8",
    )
    if r.returncode != 0:
        return []
    prefix = f"MyIA.AI.Notebooks/{series}/"
    return [ln for ln in r.stdout.splitlines()
            if ln.startswith(prefix) and ln.endswith(".ipynb")]


def _base_cell_sources(base: str, rel: str) -> set[str] | None:
    """Sources de cellules code de la version base ; None si absent."""
    r = subprocess.run(
        ["git", "show", f"{base}:{rel}"],
        cwd=REPO_ROOT, capture_output=True, text=True, encoding="utf-8",
    )
    if r.returncode != 0:
        return None
    try:
        nb = json.loads(r.stdout)
    except json.JSONDecodeError:
        return None
    return {"".join(c.get("source", []))
            for c in nb.get("cells", []) if c.get("cell_type") == "code"}


def gate(base_ref: str, series: str = DEFAULT_SERIES) -> list[dict]:
    """Defauts portees par des cellules AJOUTEES ou MODIFIEES sur HEAD.

    Ratchet : une cellule dont la source est byte-identique dans la base
    est de la dette pre-existante -- jamais gatee, surfacée par --all.
    L'etat pooled se construit sur TOUTES les cellules (le kernel ne
    distingue pas ancien/neuf) ; seules les defauts dont l'APPEL de test
    vit dans une cellule nouvelle/modifiee sont rapportees.
    """
    base = _merge_base(base_ref)
    if base is None:
        print(f"ERREUR: pas de merge-base avec {base_ref}", file=sys.stderr)
        return [{"error": f"no-merge-base:{base_ref}"}]
    new_defects: list[dict] = []
    for rel in _changed_notebooks(base, series):
        head_path = REPO_ROOT / rel
        if not head_path.exists():
            continue  # notebook supprime -- rien a proteger
        base_sources = _base_cell_sources(base, rel)
        nb = json.loads(head_path.read_text(encoding="utf-8"))
        code_cells = [(i, "".join(c.get("source", [])))
                      for i, c in enumerate(nb.get("cells", []))
                      if c.get("cell_type") == "code"]
        pooled: dict[str, int] = {}
        for idx, source in code_cells:
            preexisting = (base_sources is not None
                           and source in base_sources)
            if is_demo_cell(source):
                continue
            defects, pooled = analyze_cell(source, pooled, idx)
            if preexisting:
                continue  # la dette pre-existante ne gate pas
            for d in defects:
                new_defects.append({"path": rel, **d})
    return new_defects


# ---------------------------------------------------------------------------
# Self-test -- valider par les faux negatifs (lecons count_code_sorry)
# ---------------------------------------------------------------------------

FOUNDING_CELL_8_CORE = '''
naive_times, mrv_times = [], []
for p in puzzles:
    for _ in range(N_RUNS):
        g = [row[:] for row in p]
        t0 = time.perf_counter(); solve_naive(g)
        naive_times.append(time.perf_counter() - t0)
        g = [row[:] for row in p]
        t0 = time.perf_counter(); solve_mrv(g)
        mrv_times.append(time.perf_counter() - t0)

u_stat, p_value = stats.mannwhitneyu(naive_times, mrv_times, alternative="two-sided")
'''

FOUNDING_CELL_12_CORE = '''
reverse_times = []
for p in puzzles:
    for _ in range(N_RUNS):
        g = [row[:] for row in p]
        t0 = time.perf_counter(); solve_reverse(g)
        reverse_times.append(time.perf_counter() - t0)
reverse_times = np.array(reverse_times) * 1000

# 3 comparaisons 2 a 2
pairs = [("naif vs MRV", naive_times, mrv_times),
         ("naif vs reverse", naive_times, reverse_times),
         ("MRV vs reverse", mrv_times, reverse_times)]
for name, a, b in pairs:
    _, p = stats.mannwhitneyu(a, b, alternative="two-sided")
'''

CORRECTED_CELL_8_CORE = '''
naive_times, mrv_times = [], []
for p in puzzles:
    ts_naive, ts_mrv = [], []
    for _ in range(N_RUNS):
        g = [row[:] for row in p]
        t0 = time.perf_counter(); solve_naive(g)
        ts_naive.append(time.perf_counter() - t0)
        g = [row[:] for row in p]
        t0 = time.perf_counter(); solve_mrv(g)
        ts_mrv.append(time.perf_counter() - t0)
    naive_times.append(np.median(ts_naive) * 1000)
    mrv_times.append(np.median(ts_mrv) * 1000)

w_stat, p_value = stats.wilcoxon(naive_times, mrv_times)
'''

CORRECTED_CELL_12_CORE = '''
reverse_times = []
for p in puzzles:
    ts = []
    for _ in range(N_RUNS):
        g = [row[:] for row in p]
        t0 = time.perf_counter(); solve_reverse(g)
        ts.append(time.perf_counter() - t0)
    reverse_times.append(np.median(ts) * 1000)

pairs = [("naif vs MRV", naive_times, mrv_times),
         ("naif vs reverse", naive_times, reverse_times),
         ("MRV vs reverse", mrv_times, reverse_times)]
for name, a, b in pairs:
    _, p = stats.wilcoxon(a, b)
'''

TTEST_INDEPENDANT_POOLED = '''
scores_a, scores_b = [], []
for subj in subjects:
    for _ in range(N_REPS):
        scores_a.append(run_a(subj))
        scores_b.append(run_b(subj))

t, p = stats.ttest_ind(scores_a, scores_b)
'''

COMPREHENSION_POOLED = '''
flat = [solve(p) for p in puzzles for _ in range(N_RUNS)]
other = [solve_rev(p) for p in puzzles for _ in range(N_RUNS)]
u, p = stats.mannwhitneyu(flat, other)
'''

LEGIT_BOOTSTRAP_SINGLE_LOOP = '''
boot_means = []
for _ in range(5000):
    sample = rng.choice(data, size=len(data), replace=True)
    boot_means.append(sample.mean())
lo, hi = np.percentile(boot_means, [2.5, 97.5])
u, p = stats.mannwhitneyu(boot_means, ref_means)  # test sur resamples independants
'''

LEGIT_ARRAY_WRAPPER_ON_AGGREGATED = '''
med_a = np.array([np.median(ts) for ts in per_puzzle_a])
med_b = np.array([np.median(ts) for ts in per_puzzle_b])
w, p = stats.wilcoxon(med_a, med_b)
'''


def self_test() -> bool:
    ok = True
    checks = 0

    def check(label: str, cond: bool, detail: str = "") -> None:
        nonlocal ok, checks
        checks += 1
        if not cond:
            print(f"SELF-TEST KO [{label}]{': ' + detail if detail else ''}")
            ok = False

    # Fondation cellule 8 : pooling direct vers mannwhitneyu.
    d8, pooled = analyze_cell(FOUNDING_CELL_8_CORE)
    check("founding-8 count", len(d8) == 1, repr(d8))
    if d8:
        check("founding-8 names",
              set(d8[0]["pooled"]) == {"naive_times", "mrv_times"})
        check("founding-8 test", d8[0]["test"] == "mannwhitneyu")

    # Fondation cellule 12, SEQUNCEE apres la 8 (etat kernel partage) :
    # la table de paires + le deballage -- le test ne nomme jamais les
    # accumulateurs. Un seul SITE d'appel AST (la boucle l'execute 3
    # fois) ; les deux alias couvrent les trois noms pools.
    d12, _ = analyze_cell(FOUNDING_CELL_12_CORE, pooled, 1)
    check("founding-12 count", len(d12) == 1, repr(d12))
    if d12:
        check("founding-12 names via table",
              set(d12[0]["pooled"]) ==
              {"naive_times", "mrv_times", "reverse_times"},
              repr(d12[0]["pooled"]))
        check("founding-12 cross-cell", d12[0]["append_cell"] in (0, 1))

    # Variante ttest_ind : meme plan, autre test non apparie.
    dt, _ = analyze_cell(TTEST_INDEPENDANT_POOLED)
    check("ttest_ind count", len(dt) == 1, repr(dt))
    if dt:
        check("ttest_ind names",
              set(dt[0]["pooled"]) == {"scores_a", "scores_b"})
        check("ttest_ind test", dt[0]["test"] == "ttest_ind")

    # Pooling reloge en comprehension double-generateur.
    dc, _ = analyze_cell(COMPREHENSION_POOLED)
    check("comprehension count", len(dc) == 1, repr(dc))
    if dc:
        check("comprehension names", set(dc[0]["pooled"]) == {"flat", "other"})

    # Formes legitimes : RAS.
    dfix, pooled_fix = analyze_cell(CORRECTED_CELL_8_CORE)
    check("corrected-8 clean", dfix == [], repr(dfix))
    # l'etat pooled issu de la correction ne contient QUE les listes
    # brutes jamais testees ; les medianes agregees n'y figurent pas.
    check("corrected-8 aggregated not pooled",
          "naive_times" not in pooled_fix and "mrv_times" not in pooled_fix,
          repr(sorted(pooled_fix)))
    check("corrected-8 raw reps tracked",
          {"ts_naive", "ts_mrv"} <= set(pooled_fix))
    # la cellule 12 corrigee (wilcoxon apparie) reste propre meme avec
    # l'etat de la 8 corrigee.
    d12fix, _ = analyze_cell(CORRECTED_CELL_12_CORE, pooled_fix, 1)
    check("corrected-12 clean", d12fix == [], repr(d12fix))

    dboot, _ = analyze_cell(LEGIT_BOOTSTRAP_SINGLE_LOOP)
    check("bootstrap single-loop clean", dboot == [], repr(dboot))

    dagg, _ = analyze_cell(LEGIT_ARRAY_WRAPPER_ON_AGGREGATED)
    check("aggregated arrays clean", dagg == [], repr(dagg))

    # Demo marquee : la fondation + marqueur ne teste ni n'accumule.
    ddemo, pooled_after = analyze_cell(FOUNDING_CELL_8_CORE + "\n# pooled-demo",
                                       {"naive_times": 0})
    check("demo-marked skipped", ddemo == [] and pooled_after == {"naive_times": 0},
          repr((ddemo, pooled_after)))

    print("SELF-TEST " + ("PASS" if ok else "FAIL") + f" ({checks} cas)")
    return ok


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("base_ref", nargs="?", help="ref de base du gate ratchet")
    ap.add_argument("--all", action="store_true",
                    help="balayer toute la famille sur HEAD")
    ap.add_argument("--self-test", action="store_true",
                    help="rejouer les fixtures embarquees")
    ap.add_argument("--series", default=DEFAULT_SERIES,
                    help=f"famille (defaut {DEFAULT_SERIES})")
    ap.add_argument("--json", action="store_true", dest="as_json")
    args = ap.parse_args(argv)

    if args.self_test:
        return 0 if self_test() else 1

    if args.all:
        defects = [d for d in sweep(args.series) if not d.get("skipped_demo")]
        skipped = [d for d in sweep(args.series) if d.get("skipped_demo")]
        if args.as_json:
            print(json.dumps({"defects": defects, "skipped_demo": skipped},
                             ensure_ascii=False, indent=1))
        else:
            for d in defects:
                rel = Path(d["path"]).relative_to(REPO_ROOT)
                print(f"POOLED_REPEATED_MEASURES {rel} cell {d['cell']}: "
                      f"{d['test']}({', '.join(d['pooled'])}) "
                      f"[append l.{d['append_line']}, test l.{d['test_line']}]")
            if skipped:
                print(f"({len(skipped)} cellule(s) demo marquee(s) sautee(s))")
            print(f"{len(defects)} defaut(s) dans la famille {args.series}")
        return 1 if defects else 0

    if not args.base_ref:
        ap.error("fournir <base-ref>, --all ou --self-test")
        return 2

    defects = gate(args.base_ref, args.series)
    if args.as_json:
        print(json.dumps({"new_defects": defects}, ensure_ascii=False,
                         indent=1))
    else:
        for d in defects:
            if "error" in d:
                print(f"ERREUR: {d['error']}")
                continue
            print(f"POOLED_REPEATED_MEASURES (nouvelle cellule) "
                  f"{d['path']} cell {d['cell']}: "
                  f"{d['test']}({', '.join(d['pooled'])})")
        print(f"{len(defects)} defaut(s) nouveau(x) vs {args.base_ref}")
    return 1 if defects else 0


if __name__ == "__main__":
    sys.exit(main())
