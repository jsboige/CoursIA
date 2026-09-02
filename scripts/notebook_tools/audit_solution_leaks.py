#!/usr/bin/env python3
"""Audit solution leaks in pedagogical notebooks.

Detects 5 patterns:
1. Function body leak (issue #362): function defined under # Exercice N with >3 lines of logic
2. Commented-out solution leak (issue #362): # comment blocks >3 lines with code/data
3. Pre-resolved cells (issue #362): # Solution / # Exemple resolu with complete answers
4. C# candidates (#5179 complement): ``// Exercice`` / ``// Solution`` code cells FLAGged for review
5. Markdown-borne solutions, class (h) (#14327 / PR #14161): a complete Lean proof
   protocol written in a MARKDOWN cell in the window of an exercise. All other
   patterns are conditioned on ``code`` cells, so this shape was structurally
   invisible to the scanner. Emits FLAG candidates (see pattern 5 regex block).
"""

import argparse
import json
import sys
import re
import glob
import os
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
NOTEBOOKS_DIR = REPO_ROOT / "MyIA.AI.Notebooks"

# Marcheur canonique centralise dans notebook_walk (#8650) : SKIP_DIRS canonique
# (sur-ensemble strict de l'ancienne exclusion locale -- ajoute ``.lake``,
# ``archive``, ``_archive``, ``foundry-lib``, ``.ipynb_checkpoints``, etc., donc
# les arborescences vendored/archivees ne sont plus auditees), filtre git
# tracked_only, et filtre sur le chemin RELATIF a la racine (immunise contre la
# classe #8858 -- un filtre abs-parts reduit le scan au silence sous un parent
# nomme ``_archives/`` / ``archive/``).
from notebook_walk import iter_notebooks as _walk_notebooks  # noqa: E402

EXERCICE_MARKERS = re.compile(
    r'#\s*(Exercice|TODO\s+etudiant|Etape)\s*\d*', re.IGNORECASE
)
EXERCICE_MD_MARKERS = re.compile(
    r'(##?\s*Exercice\s+\d+|###?\s*Exercice\s+\d+)', re.IGNORECASE
)
SOLUTION_MARKERS = re.compile(
    r'#\s*(Solution|Exemple\s+résolu|Réponse\s*:)'
    r'|#\s*(Solution|Exemple\s+resolu|Reponse\s*:)', re.IGNORECASE
)
EXAMPLE_RESOLU_MARKERS = re.compile(
    r'#\s*(Exemple\s+résolu|Exemple\s+resolu|Solution\s*[:-]?\s*$)', re.IGNORECASE
)

# --- C# / .NET Interactive markers (#2161 blind-spot, complement to count_exercises #5179) ---
# The Python leak detectors above only match `#` comments. C# notebooks use `//`.
# C# exercise cells are flagged for MANUAL review -- the example-vs-leak verdict is a
# content judgment (exercise-example-labeling rule) that must NOT be automated. The
# detector emits CANDIDATES only, never an auto-verdict.
CSHARP_EXERCICE_MARKER = re.compile(r'^\s*//\s*[Ee]xercice', re.IGNORECASE)
CSHARP_SOLUTION_MARKER = re.compile(
    r'^\s*//\s*(Solution|Exemple\s+résolu|Exemple\s+resolu|Réponse\s*:|Reponse\s*:)',
    re.IGNORECASE,
)
# C# stub markers -- their presence means the cell is a legit student stub, not a leak.
CSHARP_STUB_MARKERS = re.compile(
    r'(//\s*TODO|//\s*Indice|//\s*Étape|//\s*Etape|\bpass\b|\breturn\s*;|\breturn\s+null\b)',
    re.IGNORECASE,
)

# --- Pattern 5 (class (h), #14327 / PR #14161): markdown-borne solutions ---
# A complete solution written in a MARKDOWN cell in the window of an exercise
# (fenced ```lean proof protocol, expected output, cost) is invisible to every
# other pattern here -- they are all conditioned on `code` cells. Like the C#
# detector above, this emits FLAG candidates for manual review, never an
# auto-verdict: md cells legitimately carry worked examples and interpretation
# cells with fenced proofs, so the exemple-vs-leak verdict is a content
# judgment (exercise-example-labeling rule).
#
# Sanctioned pattern (established PR #14161): a final section
# "Annexe -- solutions des exercices" is the approved home for worked
# solutions -- every md cell at or after the first annexe header is EXEMPT.
LEAN_EXERCICE_LINE = re.compile(
    r'^\s*--\s*(Exercice\s*\d+|TODO\s+etudiant)\b', re.IGNORECASE
)
LEAN_FENCE_BLOCK = re.compile(
    r'```(?:lean|mathlib)\b[^\n]*\n(.*?)```', re.DOTALL | re.IGNORECASE
)
# A fenced block counts as a complete proof script when it carries a `:= by`
# goal AND a closing tactic line solving it. Bare backticked tactic mentions
# (indices like "Indice : `exact foo h`") are deliberately NOT a trigger:
# measured 2026-09-02 on main, that shape fires 10x, all legitimate
# pedagogical indices in exercise headers. Likewise "sortie attendue" alone
# is NOT a trigger (11 legitimate interpretation cells in the very notebook
# of the golden set) -- it stays a reported detail, never a verdict.
LEAN_COMPLETE_PROOF_LINE = re.compile(
    r'^\s{1,10}(?:exact|simp|simp_all|rw|rewrite|calc|refine|apply|decide|'
    r'native_decide|omega|ring|linarith|norm_num|aesop|tauto|constructor|'
    r'induction|rcases|obtain|unfold)\b.*$',
    re.MULTILINE,
)
MD_ANNEXE_HEADER = re.compile(
    r'^#{1,6}\s*(?:Annexe\b[^\n]*(?:solution|corrig|exercice)'
    r'|(?:Solution|Corrigé|Corrige)s?\s+des\s+exercices)',
    re.IGNORECASE | re.MULTILINE,
)
# C# language detection: kernelspec language_info.name OR a .net-csharp kernel.
def _is_csharp_notebook(nb):
    """True if the notebook is C# / .NET Interactive (so `//` comments apply)."""
    meta = nb.get('metadata', {})
    lang = (meta.get('language_info') or {}).get('name', '')
    if lang and lang.lower() in ('c#', 'csharp', 'f#', 'fsharp'):
        return True
    ks = (meta.get('kernelspec') or {}).get('name', '')
    return '.net-csharp' in ks or '.net-fsharp' in ks or '.net-polyglot' in ks


def get_cells_after_exercice_md(cells, start_idx):
    """Get code cells that follow a markdown exercice header."""
    code_cells = []
    for i in range(start_idx + 1, min(start_idx + 5, len(cells))):
        cell = cells[i]
        if cell['cell_type'] == 'markdown':
            src = ''.join(cell.get('source', []))
            if EXERCICE_MD_MARKERS.search(src):
                break
            if src.strip().startswith('#'):
                break
        if cell['cell_type'] == 'code':
            code_cells.append((i, cell))
    return code_cells


def detect_function_body_leak(source_lines):
    """Pattern 1: Function with >3 lines of real logic under exercice."""
    leaks = []
    in_function = False
    func_name = ""
    logic_lines = 0
    func_start = 0
    current_indent = 0

    for lineno, line in enumerate(source_lines):
        stripped = line.strip()

        # Detect function definition
        func_match = re.match(r'def\s+(\w+)\s*\(', stripped)
        if func_match:
            if in_function and logic_lines > 3:
                leaks.append({
                    'type': 'function_body_leak',
                    'func_name': func_name,
                    'start_line': func_start + 1,
                    'logic_lines': logic_lines,
                    'severity': 'HIGH' if logic_lines > 5 else 'MEDIUM',
                })
            in_function = True
            func_name = func_match.group(1)
            logic_lines = 0
            func_start = lineno
            current_indent = len(line) - len(line.lstrip())
            continue

        if in_function:
            indent = len(line) - len(line.lstrip()) if stripped else current_indent + 4
            if stripped and indent > current_indent:
                # Skip stub patterns
                if stripped in ('pass', 'return None', 'return None  # TODO etudiant',
                                'print("Exercice a completer")', 'return 0', 'return ""',
                                'return []', 'return {}', 'return False', 'return True'):
                    logic_lines = 0
                    in_function = False
                    continue
                if stripped.startswith('#') or stripped.startswith('"""') or stripped.startswith("'''"):
                    continue
                if stripped.startswith('return ') and 'TODO' in stripped:
                    continue
                if stripped.startswith('return ') and stripped.endswith('None'):
                    continue
                logic_lines += 1

            # Function ended (dedent or blank line after logic)
            if stripped and indent <= current_indent and lineno > func_start + 1:
                if logic_lines > 3:
                    leaks.append({
                        'type': 'function_body_leak',
                        'func_name': func_name,
                        'start_line': func_start + 1,
                        'logic_lines': logic_lines,
                        'severity': 'HIGH' if logic_lines > 5 else 'MEDIUM',
                    })
                in_function = False
                logic_lines = 0

    # Check last function
    if in_function and logic_lines > 3:
        leaks.append({
            'type': 'function_body_leak',
            'func_name': func_name,
            'start_line': func_start + 1,
            'logic_lines': logic_lines,
            'severity': 'HIGH' if logic_lines > 5 else 'MEDIUM',
        })

    return leaks


def detect_commented_solution_leak(source_lines):
    """Pattern 2: Comment blocks >3 lines with code/data that constitute solution."""
    leaks = []
    comment_block = []
    block_start = 0

    for lineno, line in enumerate(source_lines):
        stripped = line.strip()
        if stripped.startswith('#') and not stripped.startswith('#!') and not stripped.startswith('# @'):
            # Check if comment looks like code
            content = stripped[1:].strip()
            if re.match(r'(prof|profil|expected|result|solution|answer|correct)\w*\s*[=:]', content, re.IGNORECASE):
                comment_block.append((lineno + 1, stripped))
            elif re.match(r'\w+\s*[=\[\(].*\)', content):
                comment_block.append((lineno + 1, stripped))
            elif re.match(r'(if|for|while|return|def|class)\s+', content):
                comment_block.append((lineno + 1, stripped))
        else:
            if len(comment_block) > 3:
                leaks.append({
                    'type': 'commented_solution_leak',
                    'start_line': comment_block[0][0],
                    'lines': len(comment_block),
                    'severity': 'MEDIUM',
                })
            comment_block = []

    if len(comment_block) > 3:
        leaks.append({
            'type': 'commented_solution_leak',
            'start_line': comment_block[0][0],
            'lines': len(comment_block),
            'severity': 'MEDIUM',
        })

    return leaks


def detect_preresolved_cells(cells):
    """Pattern 3: # Solution or # Exemple resolu cells with complete answers."""
    leaks = []
    for i, cell in enumerate(cells):
        if cell['cell_type'] != 'code':
            continue
        source = ''.join(cell.get('source', []))
        if SOLUTION_MARKERS.search(source.split('\n')[0] if source else ''):
            code_lines = [l for l in source.split('\n') if l.strip() and not l.strip().startswith('#')]
            if len(code_lines) > 3:
                leaks.append({
                    'type': 'preresolved_cell',
                    'cell_index': i,
                    'code_lines': len(code_lines),
                    'first_line': source.split('\n')[0][:80],
                    'severity': 'LOW',
                })
    return leaks


def detect_csharp_leak_candidates(cells):
    """Pattern 4 (C#): FLAG ``// Exercice`` / ``// Solution`` code cells for manual review.

    The Python leak detectors only match ``#`` comments, so every C# notebook
    was invisible. This detector emits **candidates** for human review -- it
    does NOT auto-classify, because the example-vs-leak verdict is a content
    judgment (exercise-example-labeling rule: a cell with complete working code
    under ``// Exercice`` is a leak; under ``// Exemple`` it is a legit demo).

    Heuristic for "candidate worth flagging" (mirrors the Python >3-logic-line
    rule + #5179's stub detection, adapted to C#):

      - a ``// Exercice`` cell WITHOUT a stub marker (TODO/pass/return;/return
        null) AND with >3 non-comment, non-brace code lines -> FLAG
        (``csharp_exercice_body``); this is the analogue of a Python
        function_body_leak under ``# Exercice``.
      - a ``// Solution`` / ``// Exemple resolu`` cell with >3 such code lines
        -> FLAG (``csharp_preresolved``); legit demos exist, so the verdict is
        left to the reviewer.

    Returns leak dicts with ``severity`` = ``FLAG`` (a distinct severity so the
    report makes clear these are candidates, not auto-verdicted leaks).
    """
    candidates = []
    for i, cell in enumerate(cells):
        if cell.get('cell_type') != 'code':
            continue
        source = ''.join(cell.get('source', []))
        if not source:
            continue
        # Does this cell carry a C# exercice/solution marker on any line?
        is_exercice = any(
            CSHARP_EXERCICE_MARKER.match(ln) for ln in source.split('\n')
        )
        is_solution = any(
            CSHARP_SOLUTION_MARKER.match(ln) for ln in source.split('\n')
        )
        if not (is_exercice or is_solution):
            continue
        # Count non-comment, non-brace, non-trivial code lines.
        code_lines = [
            ln for ln in source.split('\n')
            if ln.strip()
            and not ln.strip().startswith('//')
            and ln.strip() not in ('{', '}', '(', ')', ';')
        ]
        if len(code_lines) <= 3:
            continue
        # An exercice cell with a stub marker is a legit student stub, not a leak.
        if is_exercice and not is_solution and CSHARP_STUB_MARKERS.search(source):
            continue
        kind = 'csharp_preresolved' if is_solution else 'csharp_exercice_body'
        candidates.append({
            'type': kind,
            'cell_index': i,
            'code_lines': len(code_lines),
            'first_line': source.split('\n')[0][:80],
            'severity': 'FLAG',
        })
    return candidates


def detect_markdown_solution_candidates(cells):
    """Pattern 5 (class (h), #14327): FLAG md cells carrying a complete proof
    protocol in the window of an exercise.

    A md cell is a candidate when it sits within the 3 cells upstream of an
    exercise anchor (the anchor itself counts when it is the md header cell),
    is not part of a sanctioned final "Annexe -- solutions des exercices"
    section, and contains a fenced ```lean``` block holding a complete proof
    script (a ``:= by`` goal closed by a tactic line). Anchors are md
    ``### Exercice N`` headers, Python ``# Exercice`` code cells and Lean
    ``-- Exercice N`` / ``-- TODO etudiant`` code cells (the golden set of
    PR #14161 uses the Lean form, which no other anchor regex matches).

    Returns FLAG-severity candidates for manual review (see the pattern 5
    regex block for why this is not an auto-verdict).
    """
    anchors = set()
    for i, cell in enumerate(cells):
        src = ''.join(cell.get('source', []))
        if not src:
            continue
        if cell['cell_type'] == 'markdown':
            if EXERCICE_MD_MARKERS.search(src):
                anchors.add(i)
        elif cell['cell_type'] == 'code':
            lines = src.split('\n')
            if EXERCICE_MARKERS.search(lines[0]):
                anchors.add(i)
            elif any(LEAN_EXERCICE_LINE.match(ln) for ln in lines[:3]):
                anchors.add(i)

    annexe_at = None
    for i, cell in enumerate(cells):
        if cell['cell_type'] == 'markdown':
            if MD_ANNEXE_HEADER.search(''.join(cell.get('source', []))):
                annexe_at = i
                break

    candidates = []
    flagged = set()
    for k in sorted(anchors):
        for j in range(max(0, k - 3), k + 1):
            if j in flagged:
                continue
            cell = cells[j]
            if cell['cell_type'] != 'markdown':
                continue
            if annexe_at is not None and j >= annexe_at:
                continue
            src = ''.join(cell.get('source', []))
            for m in LEAN_FENCE_BLOCK.finditer(src):
                block = m.group(1)
                if ':= by' in block and LEAN_COMPLETE_PROOF_LINE.search(block):
                    flagged.add(j)
                    candidates.append({
                        'type': 'md_solution_protocol',
                        'cell_index': j,
                        'context': f'window_of_anchor_{k}',
                        'first_line': src.strip().split('\n')[0][:80],
                        'severity': 'FLAG',
                    })
                    break
    return candidates


def audit_notebook(path):
    """Audit a single notebook for solution leaks."""
    try:
        nb = json.load(open(path, encoding='utf-8'))
    except (json.JSONDecodeError, UnicodeDecodeError):
        return []

    cells = nb.get('cells', [])
    all_leaks = []

    # Track which cells are "exercise context"
    exercice_context = set()

    for i, cell in enumerate(cells):
        if cell['cell_type'] == 'markdown':
            src = ''.join(cell.get('source', []))
            if EXERCICE_MD_MARKERS.search(src):
                exercice_context.add(i)
        elif cell['cell_type'] == 'code':
            src = ''.join(cell.get('source', []))
            if EXERCICE_MARKERS.search(src.split('\n')[0] if src else ''):
                exercice_context.add(i)

    # Check code cells under exercice context for pattern 1 & 2
    for i in exercice_context:
        cell = cells[i]
        if cell['cell_type'] != 'code':
            continue
        source = ''.join(cell.get('source', []))
        lines = source.split('\n')

        # Skip cells that are legitimate demos (# Exemple resolu, # Solution)
        if EXAMPLE_RESOLU_MARKERS.search(lines[0] if lines else ''):
            continue

        # Pattern 1: function body leak
        body_leaks = detect_function_body_leak(lines)
        for leak in body_leaks:
            leak['cell_index'] = i
            leak['context'] = 'exercice_marker'
            all_leaks.append(leak)

        # Pattern 2: commented solution
        comment_leaks = detect_commented_solution_leak(lines)
        for leak in comment_leaks:
            leak['cell_index'] = i
            all_leaks.append(leak)

    # Also check code cells immediately after exercice markdown headers
    for i, cell in enumerate(cells):
        if cell['cell_type'] == 'markdown':
            src = ''.join(cell.get('source', []))
            if EXERCICE_MD_MARKERS.search(src):
                following_code = get_cells_after_exercice_md(cells, i)
                for j, code_cell in following_code:
                    source = ''.join(code_cell.get('source', []))
                    lines = source.split('\n')
                    # Skip cells that are legitimate demos
                    if EXAMPLE_RESOLU_MARKERS.search(lines[0] if lines else ''):
                        continue
                    body_leaks = detect_function_body_leak(lines)
                    for leak in body_leaks:
                        leak['cell_index'] = j
                        leak['context'] = f'after_md_exercice_{i}'
                        all_leaks.append(leak)

    # Pattern 3: pre-resolved cells (all code cells)
    preresolved = detect_preresolved_cells(cells)
    all_leaks.extend(preresolved)

    # Pattern 4 (C#): FLAG // Exercice / // Solution cells for manual review.
    # Only run on C# notebooks -- the Python detectors above cover `#` cells.
    if _is_csharp_notebook(nb):
        all_leaks.extend(detect_csharp_leak_candidates(cells))

    # Pattern 5 (class (h), #14327): md cells carrying complete proof protocols
    # in the window of an exercise -- FLAG candidates for manual review.
    all_leaks.extend(detect_markdown_solution_candidates(cells))

    return all_leaks


def _run_audit():
    """Scan all notebooks and return (output_dict, notebook_count).

    Shared by the human-readable report (default) and the ``--json`` machine
    output consumed by ``solution_leak_delta.py`` (CI WARN-mode gate, #8053).
    """
    notebooks = [n for n in _walk_notebooks(NOTEBOOKS_DIR)
                 if '_executed' not in n.name]

    results = {}
    total_leaks = {
        'function_body_leak': 0, 'commented_solution_leak': 0, 'preresolved_cell': 0,
        'csharp_exercice_body': 0, 'csharp_preresolved': 0,
        'md_solution_protocol': 0,
    }

    for nb_path in sorted(notebooks):
        leaks = audit_notebook(nb_path)
        if leaks:
            rel_path = nb_path.relative_to(REPO_ROOT)
            results[str(rel_path)] = leaks
            for leak in leaks:
                total_leaks[leak['type']] = total_leaks.get(leak['type'], 0) + 1

    output = {
        'total_notebooks': len(notebooks),
        'notebooks_with_leaks': len(results),
        'leak_counts': total_leaks,
        'findings': {k: v for k, v in results.items()},
    }
    return output, len(notebooks)


def main(argv=None):
    parser = argparse.ArgumentParser(
        description="Audit solution leaks in pedagogical notebooks (issue #362, #8053 CI gate)."
    )
    parser.add_argument(
        '--json', action='store_true',
        help="Emit the findings dict as a single JSON document on stdout (for "
             "solution_leak_delta.py CI consumption). Suppresses the markdown "
             "report and the results-file write.",
    )
    args = parser.parse_args(argv)

    output, nb_count = _run_audit()

    if args.json:
        # Machine output for CI delta comparison. No file write, no human report.
        json.dump(output, sys.stdout, indent=2, ensure_ascii=False, default=str)
        sys.stdout.write('\n')
        return

    # --- human-readable report (default, unchanged behaviour) ---
    total_leaks = output['leak_counts']
    results = output['findings']

    print(f"Auditing {nb_count} notebooks for solution leaks...")
    print()
    print(f"## Audit Results: {len(results)} notebooks with findings")
    print(f"Total: function_body_leak={total_leaks.get('function_body_leak', 0)}, "
          f"commented_solution_leak={total_leaks.get('commented_solution_leak', 0)}, "
          f"preresolved_cell={total_leaks.get('preresolved_cell', 0)}")
    cs_body = total_leaks.get('csharp_exercice_body', 0)
    cs_pre = total_leaks.get('csharp_preresolved', 0)
    if cs_body or cs_pre:
        print(f"C# candidates (FLAGGED FOR REVIEW, not auto-verdicted): "
              f"csharp_exercice_body={cs_body}, csharp_preresolved={cs_pre}")
    md_proto = total_leaks.get('md_solution_protocol', 0)
    if md_proto:
        print(f"Markdown solution-protocol candidates (FLAGGED FOR REVIEW, not "
              f"auto-verdicted): md_solution_protocol={md_proto}")
    print()

    # Sort by severity (HIGH first). FLAG = C# candidates for manual review.
    for path, leaks in sorted(results.items()):
        high = [l for l in leaks if l.get('severity') == 'HIGH']
        medium = [l for l in leaks if l.get('severity') == 'MEDIUM']
        low = [l for l in leaks if l.get('severity') == 'LOW']
        flags = [l for l in leaks if l.get('severity') == 'FLAG']

        if high or medium or flags:
            print(f"### {path}")
            for leak in high + medium + flags:
                leak_desc = f"  [{leak['severity']}] {leak['type']}"
                if 'func_name' in leak:
                    leak_desc += f" `{leak['func_name']}` ({leak['logic_lines']} logic lines)"
                elif 'lines' in leak:
                    leak_desc += f" ({leak['lines']} comment lines)"
                elif 'code_lines' in leak:
                    leak_desc += f" ({leak['code_lines']} code lines)"
                if 'cell_index' in leak:
                    leak_desc += f" cell {leak['cell_index']}"
                if 'start_line' in leak:
                    leak_desc += f" L{leak['start_line']}"
                print(leak_desc)
            print()

    output_path = REPO_ROOT / 'audit_solution_leaks_results.json'
    with open(output_path, 'w', encoding='utf-8') as f:
        json.dump(output, f, indent=2, ensure_ascii=False, default=str)

    print(f"Full results saved to {output_path}")


if __name__ == '__main__':
    main()
