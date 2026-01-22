#!/usr/bin/env python3
"""
Script de vérification complète de tous les notebooks Tweety
Exécute chaque notebook et analyse les sorties pour identifier les problèmes
"""

import json
import subprocess
import sys
from pathlib import Path
from datetime import datetime

def execute_notebook(notebook_path):
    """Exécute un notebook avec papermill et retourne le chemin de sortie"""
    output_path = notebook_path.replace('.ipynb', '_verified.ipynb')

    cmd = [
        sys.executable, '-m', 'papermill',
        notebook_path, output_path,
        '--kernel', 'python3'
    ]

    result = subprocess.run(cmd, capture_output=True, text=True, timeout=600)

    return output_path, result.returncode, result.stdout, result.stderr

def analyze_notebook(notebook_path):
    """Analyse un notebook exécuté pour trouver erreurs, warnings, et problèmes"""
    with open(notebook_path, 'r', encoding='utf-8') as f:
        nb = json.load(f)

    issues = {
        'errors': [],
        'warnings': [],
        'long_outputs': [],
        'empty_outputs': [],
        'java_warnings': []
    }

    code_cell_count = 0
    successful_count = 0

    for i, cell in enumerate(nb['cells']):
        if cell['cell_type'] != 'code':
            continue

        code_cell_count += 1
        outputs = cell.get('outputs', [])

        has_error = False
        cell_output_length = 0

        for output in outputs:
            # Vérifier les erreurs
            if output.get('output_type') == 'error':
                issues['errors'].append({
                    'cell': i,
                    'type': output.get('ename'),
                    'message': output.get('evalue'),
                    'traceback': output.get('traceback', [])[:3]
                })
                has_error = True

            # Vérifier les streams (stdout/stderr)
            elif output.get('output_type') == 'stream':
                text = ''.join(output.get('text', []))
                cell_output_length += len(text)

                # Erreurs dans le texte
                if 'error' in text.lower() and 'no default' not in text.lower():
                    if 'exception' in text.lower() or 'traceback' in text.lower():
                        issues['warnings'].append({
                            'cell': i,
                            'text': text[:200]
                        })

                # Warnings Java Tweety
                if 'No default MUS enumerator' in text or 'No default SAT solver' in text:
                    if i not in [issue['cell'] for issue in issues['java_warnings']]:
                        issues['java_warnings'].append({
                            'cell': i,
                            'type': 'MUS/SAT' if 'MUS' in text else 'SAT',
                            'count': text.count('No default')
                        })

        # Outputs très longs (> 5000 caractères)
        if cell_output_length > 5000:
            issues['long_outputs'].append({
                'cell': i,
                'length': cell_output_length
            })

        # Cellule de code sans output (peut être normal)
        if not outputs and cell.get('source'):
            source = ''.join(cell.get('source', []))
            if 'import' not in source and 'def ' not in source and '#' not in source[:5]:
                issues['empty_outputs'].append({
                    'cell': i,
                    'source_preview': source[:50]
                })

        if not has_error:
            successful_count += 1

    return issues, code_cell_count, successful_count

def main():
    notebooks = [
        'Tweety-1-Setup.ipynb',
        'Tweety-2-Basic-Logics.ipynb',
        'Tweety-3-Advanced-Logics.ipynb',
        'Tweety-4-Belief-Revision.ipynb',
        'Tweety-5-Abstract-Argumentation.ipynb',
        'Tweety-6-Structured-Argumentation.ipynb',
        'Tweety-7-Advanced-Argumentation.ipynb'
    ]

    print('='*70)
    print('VERIFICATION COMPLETE DE LA SERIE TWEETY')
    print('='*70)
    print(f'Date: {datetime.now().strftime("%Y-%m-%d %H:%M:%S")}')
    print(f'Notebooks: {len(notebooks)}\n')

    all_results = {}

    for notebook in notebooks:
        print(f'\n{"="*70}')
        print(f'Testing: {notebook}')
        print('='*70)

        # Exécuter le notebook
        try:
            output_path, returncode, stdout, stderr = execute_notebook(notebook)

            if returncode != 0:
                print(f'❌ EXECUTION FAILED (code {returncode})')
                print(f'Error: {stderr[:500]}')
                all_results[notebook] = {'status': 'FAILED', 'error': stderr[:200]}
                continue

            print(f'✓ Execution completed')

            # Analyser les résultats
            issues, code_cells, successful = analyze_notebook(output_path)

            print(f'  Code cells: {code_cells}')
            print(f'  Successful: {successful}')
            print(f'  Errors: {len(issues["errors"])}')
            print(f'  Warnings: {len(issues["warnings"])}')
            print(f'  Java warnings: {len(issues["java_warnings"])} cells')

            if issues['errors']:
                print('\n  ERRORS:')
                for err in issues['errors']:
                    print(f'    Cell {err["cell"]}: {err["type"]}: {err["message"][:100]}')

            if issues['warnings']:
                print('\n  WARNINGS:')
                for warn in issues['warnings'][:3]:
                    print(f'    Cell {warn["cell"]}: {warn["text"][:100]}')

            if issues['java_warnings']:
                total_warnings = sum(w['count'] for w in issues['java_warnings'])
                print(f'\n  JAVA WARNINGS (MUS/SAT): {total_warnings} total in {len(issues["java_warnings"])} cells')
                print('    → Non-critical: Tweety using default SAT solver')

            all_results[notebook] = {
                'status': 'SUCCESS',
                'code_cells': code_cells,
                'successful': successful,
                'issues': issues
            }

        except subprocess.TimeoutExpired:
            print(f'❌ TIMEOUT (>10 minutes)')
            all_results[notebook] = {'status': 'TIMEOUT'}
        except Exception as e:
            print(f'❌ ERROR: {e}')
            all_results[notebook] = {'status': 'ERROR', 'error': str(e)}

    # Résumé final
    print(f'\n\n{"="*70}')
    print('SUMMARY')
    print('='*70)

    success_count = sum(1 for r in all_results.values() if r.get('status') == 'SUCCESS')
    total_errors = sum(len(r.get('issues', {}).get('errors', [])) for r in all_results.values())
    total_warnings = sum(len(r.get('issues', {}).get('warnings', [])) for r in all_results.values())

    print(f'\nNotebooks executed: {len(notebooks)}')
    print(f'Successful: {success_count}/{len(notebooks)}')
    print(f'Total errors: {total_errors}')
    print(f'Total warnings: {total_warnings}')

    if success_count == len(notebooks) and total_errors == 0:
        print('\n✅ ALL NOTEBOOKS PASSED!')
    else:
        print('\n⚠️ Some notebooks have issues')

    print('\n' + '='*70)

if __name__ == '__main__':
    main()
