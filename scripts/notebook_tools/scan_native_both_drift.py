#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Scan twin_pairs.d/ pour le drift 'native-both' vs sens applique (parite de moteur).

Contexte (issue #11200, arbitrage ai-01 2026-08-16 Option A) :
  - parity_level = descripteur de l'ETAT livre (les deux cotes tournent-ils
    sur un moteur ?)
  - bridge_verdict = jugeur du TRAVAIL (a-t-on saute un moteur atteignable ?)
  - Correlation : native-both => SOTA-OK (36/37) ; SOTA-OK /=>
    native-both (84 contre-exemples sous semantic, 4 sous surface).

L'arbitrage retient que `native-both` documente la parite de MOTEUR (chaque
cote fait le travail du notebook au moyen d'un moteur de production externe),
pas la correspondance structurelle cellule-par-cellule. La correlation a
sens unique entraine que les paires `parity_level: semantic|surface` +
`bridge_verdict: SOTA-OK` ne sont pas toutes a basculer : certaines sont
solver-free by design (csp-9-distributed, gt-17-multiagent-rl, ...), d'autres
sont ambigues (au moins un cote n'a pas de lib SOTA documentee).

Ce script distingue TROIS categories pour les paires `parity_level in
{semantic, surface}` ET `bridge_verdict: SOTA-OK` :
  - TRIVIAL_BASCULE   : les deux cotes citent une lib SOTA de leur ecosysteme
    dans known_differences / bridge_verdict_reason (regex ci-dessous).
  - SOLVER_FREE       : la paire declare explicitement 'solver-free by design'
    ou equivalente dans bridge_verdict_reason (a garder semantic|surface).
  - AMBIGUOUS         : au moins un cote sans lib SOTA documentee, decision
    humaine requise.

Usage :
  python scripts/notebook_tools/scan_native_both_drift.py [--json] [--quiet]
  python scripts/notebook_tools/scan_native_both_drift.py --csv > candidates.csv

Sortie : tableau par categorie + verdict par entree. Aucune mutation du
registre -- le script diagnostique, il ne re-ecrit pas (cf G.9 + regle C.2
verification avant bascule).
"""
import argparse
import csv
import glob
import json
import os
import re
import sys
import yaml

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
TWINDIR = os.path.join(ROOT, 'scripts', 'notebook_tools', 'twin_pairs.d')
SCHEMA = os.path.join(TWINDIR, '_schema.yaml')

# Paquets SOTA Python (noms canoniques, lowercase).
SOTA_PACKAGES_PY = [
    'ortools', 'gurobi', 'cplex', 'pyscipopt', 'python-constraint',
    'networkx', 'deap', 'pygad', 'mealpy', 'pyomo', 'z3-solver', 'pulp',
    'scipy.optimize', 'cvxpy', 'pymprog', 'pyspiel', 'open-spiel',
    'docplex', 'pydrake', 'sympy', 'numba',
    'quantlib', 'pymc', 'pymc3', 'stan', 'emcee', 'arviz', 'pystan',
    'rdflib', 'owlready2', 'sparqlwrapper', 'fuseki',
    'jpype', 'tweety', 'jpype1',
    'pytorch', 'tensorflow', 'jax', 'scikit-learn', 'sklearn',
    'transformers', 'datasets', 'huggingface', 'optuna',
    'xgboost', 'lightgbm', 'catboost',
    'nltk', 'spacy', 'gensim', 'stanza',
]

# Paquets SOTA C# (.NET).
SOTA_PACKAGES_CS = [
    'Google.OrTools', 'OrTools', 'QuikGraph', 'QuickGraph',
    'GeneticSharp', 'MetaGeneticSharp',
    'Microsoft.SemanticKernel', 'SemanticKernel',
    'Accord.MachineLearning', 'Accord.Statistics', 'Accord',
    'NumSharp', 'Infer.NET', 'Microsoft.ML', 'ML.NET',
    'DotNet.Graphics', 'SkiaSharp', 'OpenCvSharp', 'Emgu.CV',
    'Z3', 'MathNet.Numerics', 'TensorFlow.NET', 'TorchSharp',
    'NUnit', 'xunit',
    'protobuf', 'Google.Protobuf',
    'AutoGen', 'KernelMemory',
    'dotnetrdf', 'dotNetRDF',
    'IKVM',
]

# Pattern solver-free by design (regex compile) -- basee sur les tournures
# observees dans bridge_verdict_reason des paires qui ne sont PAS native-both.
# Les paires solver-free LE DISENT EXPLICITEMENT ("solver-free by design", "by
# design"). Une mention "from-scratch" ne suffit pas si elle designe une
# MOITIE seulement -- une moitie from-scratch + l'autre sur moteur = le
# moteur est la partie decisive (cote solver). Le pattern matche des
# ENONCES PLEINS, pas des mots isoles.
SOLVER_FREE_PATTERN = re.compile(
    r'(solver[- ]free\s+by\s+design|'
    r'from[- ]scratch.*\s+des\s+deux\s+c.t.s|from[- ]scratch.*\s+both\s+sides|'
    r'aucun\s+moteur\s+SOTA\s+.?\s+bridger|'
    r'no\s+SOTA\s+(engine|lib).*to\s+bridg|'
    r'algorithm\s+(is|=|:)\s+the\s+subject|'
    r'aucun\s+moteur\s+atteignable|'
    r'neither\s+SOTA\s+(engine|lib)|'
    r'l.?algorithme\s+distribu.?\s+EST\s+le\s+sujet)',
    re.IGNORECASE,
)


def load_entries():
    """Charge toutes les entrees du registre. Chaque yaml = liste de 1 dict."""
    entries = []
    for path in sorted(glob.glob(os.path.join(TWINDIR, '*.yaml'))):
        base = os.path.basename(path)
        if base.startswith('_'):
            continue
        try:
            with open(path, 'r', encoding='utf-8') as f:
                d = yaml.safe_load(f)
        except yaml.YAMLError:
            entries.append({'path': path, 'name': base, 'parse_error': True})
            continue
        if not isinstance(d, list) or len(d) == 0:
            continue
        e = d[0]
        if not isinstance(e, dict):
            continue
        e['_path'] = path
        e['_file'] = base
        entries.append(e)
    return entries


def detect_libs(text):
    """Retourne (py_libs_trouvees, cs_libs_trouvees) dans le texte."""
    if not text:
        return [], []
    t = text.lower()
    py = sorted({lib for lib in SOTA_PACKAGES_PY if lib.lower() in t})
    cs = sorted({lib for lib in SOTA_PACKAGES_CS if lib.lower() in t})
    return py, cs


def classify(e):
    """Classifie une entree selon les 3 categories."""
    p = e.get('parity_level', '')
    b = e.get('bridge_verdict', '')
    if p in ('native-both',):
        return 'ALREADY_NATIVE_BOTH', [], [], False
    if b != 'SOTA-OK':
        return 'NOT_CANDIDATE', [], [], False
    # p in {semantic, surface}, b = SOTA-OK
    kd = e.get('known_differences', [])
    kd_text = '\n'.join(kd) if isinstance(kd, list) else str(kd)
    brv = e.get('bridge_verdict_reason', '') or ''
    full = kd_text + '\n' + brv
    py, cs = detect_libs(full)
    is_solver_free = bool(SOLVER_FREE_PATTERN.search(brv) or SOLVER_FREE_PATTERN.search(kd_text))
    if is_solver_free:
        return 'SOLVER_FREE', py, cs, True
    if py and cs:
        return 'TRIVIAL_BASCULE', py, cs, False
    return 'AMBIGUOUS', py, cs, False


def main():
    ap = argparse.ArgumentParser(description=__doc__.split('\n\n')[0])
    ap.add_argument('--json', action='store_true', help='Sortie JSON machine-readable.')
    ap.add_argument('--csv', action='store_true', help='Sortie CSV (categorie, name, family, py_libs, cs_libs, reason).')
    ap.add_argument('--quiet', action='store_true', help='N imprime que le resume.')
    ap.add_argument('--only', choices=['TRIVIAL_BASCULE', 'SOLVER_FREE', 'AMBIGUOUS'],
                    help='Filtre une seule categorie.')
    args = ap.parse_args()

    entries = load_entries()
    n_total = len(entries)
    by_cat = {'TRIVIAL_BASCULE': [], 'SOLVER_FREE': [], 'AMBIGUOUS': [],
              'ALREADY_NATIVE_BOTH': [], 'NOT_CANDIDATE': []}
    for e in entries:
        if e.get('parse_error'):
            continue
        cat, py, cs, sf = classify(e)
        by_cat[cat].append({
            'path': e['_path'],
            'file': e['_file'],
            'name': e.get('name', '?'),
            'family': e.get('family', '?'),
            'parity_level': e.get('parity_level'),
            'bridge_verdict': e.get('bridge_verdict'),
            'py_libs': py,
            'cs_libs': cs,
            'solver_free_pattern': sf,
            'bridge_verdict_reason_excerpt': (e.get('bridge_verdict_reason', '') or '')[:200],
        })

    summary = {k: len(v) for k, v in by_cat.items()}
    if args.json:
        out = {'summary': summary, 'entries': {k: v for k, v in by_cat.items() if k != 'NOT_CANDIDATE'}}
        json.dump(out, sys.stdout, indent=2, ensure_ascii=False)
        return 0
    if args.csv:
        cols = ['category', 'name', 'family', 'parity_level', 'bridge_verdict',
                'py_libs', 'cs_libs', 'solver_free_pattern', 'file']
        w = csv.writer(sys.stdout)
        w.writerow(cols)
        for cat, items in by_cat.items():
            if args.only and cat != args.only:
                continue
            for it in items:
                w.writerow([cat, it['name'], it['family'], it['parity_level'],
                            it['bridge_verdict'], '|'.join(it['py_libs']),
                            '|'.join(it['cs_libs']), it['solver_free_pattern'],
                            it['file']])
        return 0

    print(f"# Scan twin_pairs.d/ native-both drift (issue #11200, arbitrage ai-01 2026-08-16)")
    print(f"# Total entries: {n_total}")
    for k in ['TRIVIAL_BASCULE', 'SOLVER_FREE', 'AMBIGUOUS', 'ALREADY_NATIVE_BOTH']:
        print(f"#   {k}: {summary[k]}")
    if args.quiet:
        return 0

    print()
    for cat in ['TRIVIAL_BASCULE', 'SOLVER_FREE', 'AMBIGUOUS']:
        items = by_cat[cat]
        if not items:
            continue
        print(f"## {cat} ({len(items)})")
        for it in items[:50]:
            py = '|'.join(it['py_libs']) or '-'
            cs = '|'.join(it['cs_libs']) or '-'
            print(f"  {it['file']:48s}  {it['family']:30s}  py=[{py}] cs=[{cs}]")
        if len(items) > 50:
            print(f"  ... ({len(items)-50} additional, use --csv or --json)")
        print()
    return 0


if __name__ == '__main__':
    sys.exit(main())