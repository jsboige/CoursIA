"""
Sudoku notebooks output integrity validation (Issue #1780, Epic #1765).
Checks: execution_count, outputs, errors, forbidden patterns, kernel spec.
"""
import json
import os
import re
import glob
import sys


def validate_notebook(nb_path):
    """Validate a single notebook. Returns dict with results."""
    with open(nb_path, 'r', encoding='utf-8') as f:
        try:
            nb = json.load(f)
        except json.JSONDecodeError as e:
            return {'path': nb_path, 'error': f'Invalid JSON: {e}'}

    metadata = nb.get('metadata', {})
    kernelspec = metadata.get('kernelspec', {})
    kernel_name = kernelspec.get('name', 'unknown')
    kernel_lang = kernelspec.get('language', 'unknown')

    cells = nb.get('cells', [])

    issues = {
        'null_exec_count': [],
        'empty_outputs': [],
        'error_outputs': [],
        'forbidden_patterns': [],
    }

    total_code_cells = 0
    code_cells_with_exec = 0

    for idx, cell in enumerate(cells):
        if cell.get('cell_type') != 'code':
            continue

        total_code_cells += 1
        source = ''.join(cell.get('source', []))
        exec_count = cell.get('execution_count')
        outputs = cell.get('outputs', [])

        # Check 1 & 6: execution_count null with non-empty source
        if exec_count is None and source.strip():
            issues['null_exec_count'].append(idx)

        # Check 2: non-empty outputs
        if (not outputs) and source.strip():
            issues['empty_outputs'].append(idx)

        # Check 3: error outputs
        for out in outputs:
            if out.get('output_type') == 'error':
                ename = out.get('ename', '')
                evalue = out.get('evalue', '')[:80]
                issues['error_outputs'].append((idx, ename, evalue))
                break

        # Check 5: forbidden patterns
        if source.strip():
            forbidden = []
            if re.search(r'raise\s+NotImplementedError', source):
                forbidden.append('raise NotImplementedError')
            if re.search(r'assert\s+False', source):
                forbidden.append('assert False')
            if re.search(r'(?<![#\w])1\s*/\s*0(?!\w)', source):
                forbidden.append('1/0')
            if forbidden:
                issues['forbidden_patterns'].append((idx, forbidden))

        if exec_count is not None:
            code_cells_with_exec += 1

    return {
        'path': nb_path,
        'kernel': kernel_name,
        'kernel_lang': kernel_lang,
        'total_code_cells': total_code_cells,
        'code_with_exec': code_cells_with_exec,
        'issues': issues,
    }


def classify_kernel(result):
    """Classify notebook as .NET, Python, or Other."""
    k = result.get('kernel', '').lower()
    if '.net' in k or 'csharp' in k or 'fsharp' in k:
        return 'dotnet'
    elif 'python' in k:
        return 'python'
    else:
        return 'other'


def main():
    base_dir = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    sudoku_dir = os.path.join(base_dir, 'MyIA.AI.Notebooks', 'Sudoku')
    notebooks = sorted(glob.glob(os.path.join(sudoku_dir, '**', '*.ipynb'), recursive=True))

    results = []
    for nb_path in notebooks:
        results.append(validate_notebook(nb_path))

    # Group by kernel type
    groups = {'dotnet': [], 'python': [], 'other': []}
    for r in results:
        if 'error' in r:
            groups['other'].append(r)
        else:
            groups[classify_kernel(r)].append(r)

    # Print results
    def print_group(title, group):
        print(f'\n{"=" * 80}')
        print(f'  {title} ({len(group)} notebooks)')
        print(f'{"=" * 80}')
        for r in group:
            name = os.path.basename(r['path'])
            iss = r.get('issues', {})

            if 'error' in r:
                print(f'  [ERROR] {name}: {r["error"]}')
                print()
                continue

            total = r['total_code_cells']
            exec_ = r['code_with_exec']
            kernel = r.get('kernel', 'unknown')

            flags = []
            if iss['null_exec_count']:
                flags.append(f'null_exec_count: cells {iss["null_exec_count"]}')
            if iss['empty_outputs']:
                flags.append(f'empty_outputs: cells {iss["empty_outputs"]}')
            if iss['error_outputs']:
                errs = '; '.join(
                    f'cell {e[0]}: {e[1]}: {e[2]}'
                    for e in iss['error_outputs']
                )
                flags.append(f'error_outputs: {errs}')
            if iss['forbidden_patterns']:
                fps = '; '.join(
                    f'cell {fp[0]}: {", ".join(fp[1])}'
                    for fp in iss['forbidden_patterns']
                )
                flags.append(f'forbidden_patterns: {fps}')

            status = 'OK' if not flags else 'ISSUES'
            exec_pct = f'{exec_}/{total}' if total > 0 else 'N/A'

            print(f'  [{status}] {name}')
            print(f'    Kernel: {kernel} | Code cells: {exec_pct} executed')
            if flags:
                for f_ in flags:
                    print(f'    FLAG: {f_}')
            print()

    print_group('.NET Interactive (C#) Notebooks', groups['dotnet'])
    print_group('Python Notebooks', groups['python'])
    print_group('Other / Unknown Kernel', groups['other'])

    # Summary
    total_nbs = len(results)
    clean = sum(1 for r in results if not any(r.get('issues', {}).values()) and 'error' not in r)
    issue = total_nbs - clean

    print(f'\n{"=" * 80}')
    print(f'  SUMMARY')
    print(f'{"=" * 80}')
    print(f'  Total notebooks: {total_nbs}')
    print(f'  Clean (no issues): {clean}')
    print(f'  With issues: {issue}')
    print(f'  .NET: {len(groups["dotnet"])} | Python: {len(groups["python"])} | Other: {len(groups["other"])}')

    # List notebooks needing fixes
    needs_fix = [r for r in results if any(r.get('issues', {}).values()) or 'error' in r]
    if needs_fix:
        print(f'\n  NOTEBOOKS NEEDING FIXES:')
        for r in needs_fix:
            name = os.path.basename(r['path'])
            print(f'    - {name}')

    return 0 if issue == 0 else 1


if __name__ == '__main__':
    sys.exit(main())
