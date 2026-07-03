#!/usr/bin/env python3
"""Audit notebook markdown cells for typographic-hierarchy pathologies.

Detects (source-level, render-agnostic):
  - HINT-AS-HEADING: a heading line (#..######) whose text reads like a hint/step/
    comment/aside (Indice, Astuce, Etape, Conseil, TODO, Note, Remarque, Attention,
    Solution, Exemple...) -> renders in a LARGE font when it should be small/body.
  - H1-DEEP: an H1 (`# `) appearing in a cell that is NOT the first markdown cell
    (multiple competing H1s / H1 used mid-notebook -> title hierarchy muddled).
  - MULTI-H1: more than one H1 across the whole notebook.

Usage: python scan_md_hierarchy.py <notebook-or-dir> [more...]
Outputs a per-notebook report + a machine-readable summary line per finding.
"""
import json, re, sys, pathlib

HEADING_RE = re.compile(r'^(#{1,6})\s+(.*\S)\s*$')
# Fenced code block delimiter (```... or ~~~...), possibly indented. Lines inside
# a fence are code, not markdown: a `# comment` there is a shell/python comment,
# NOT a heading, and must not be counted as H1 / HINT-AS-HEADING.
FENCE_RE = re.compile(r'^\s*(`{3,}|~{3,})')
# Text that should NOT be a heading (it's an aside / hint / step / inline label)
HINT_RE = re.compile(
    r'^(indice|astuce|hint|tip|conseil|note|remarque|attention|todo|'
    r'etape|étape|step|rappel|warning|important|aide|piste|nb)\b',
    re.IGNORECASE)
# A numbered step WITH a descriptive title (`Step 1: Load Data`, `Étape 3 :
# Installation`) is a real titled SECTION header, not a bare aside. Without
# this exclusion the level-agnostic HINT_RE flags the tutorial's backbone H2s
# as hint-asides (false positives). Bare asides (`## Note`, `## Étape 3`,
# `### Note pédagogique`) carry no colon+title, so they stay flagged. See #3968.
TITLED_STEP_RE = re.compile(
    r'^(step|etape|étape)\s+\d+\s*:\s*\S',
    re.IGNORECASE)
# A hint word that is the FIRST PART of a hyphenated compound noun
# (`Aide-mémoire des commandes`) is a real titled section, not a bare aside:
# the hyphenated compound is a single lexical unit naming the section. A bare
# aside (`## Note`, `### Aide`) has no hyphenated compound, so it stays flagged.
# Without this, demoting `### Aide-mémoire des commandes` while its sibling
# `### Points clés à retenir` stays H3 would create an asymmetric hierarchy.
# See #3968.
COMPOUND_HINT_RE = re.compile(
    r'^(indice|astuce|hint|tip|conseil|note|remarque|attention|todo|'
    r'etape|étape|step|rappel|warning|important|aide|piste|nb)-',
    re.IGNORECASE)
# `Step`/`Étape` followed by a NON-numeric word forms a technical compound
# noun (`Step recursif` = the recursive step of an algorithm, `Step function`,
# `Step response`, `Étape méthodologique`) — a real subsection title, not the
# bare numbered aside `## Étape 3` (which stays flagged). Distinct from
# TITLED_STEP_RE (`Step N: Title`). Deliberately scoped to step/etape ONLY,
# NOT the whole hint list, so `## Note pédagogique` (a legit bare aside per
# the design above) stays flagged. See #3968.
STEP_COMPOUND_RE = re.compile(
    r'^(step|etape|étape)\s+[^\d\s:-]',
    re.IGNORECASE)
# `Rappel` followed by a reference token that contains a digit (`Rappel ICT-10`,
# `Rappel du chapitre 3`, `Rappel ... la strate 4`) = a recap SECTION pointing
# back at prior named content, not a bare aside (`## Rappel`). A bare
# `## Rappel` has no digit reference, so it stays flagged. See #3968.
RAPPEL_REFERENCE_RE = re.compile(
    r'^rappel\s+.*\d',
    re.IGNORECASE)

def scan_notebook(path):
    try:
        nb = json.loads(pathlib.Path(path).read_text(encoding='utf-8'))
    except Exception as e:
        return [{'kind': 'READ_ERROR', 'detail': str(e), 'cell': -1, 'text': ''}]
    findings = []
    h1_cells = []
    first_md_seen = False
    for ci, cell in enumerate(nb.get('cells', [])):
        if cell.get('cell_type') != 'markdown':
            continue
        src = cell.get('source', [])
        if isinstance(src, str):
            src = src.splitlines(keepends=False)
        is_first_md = not first_md_seen
        first_md_seen = True
        in_fence = False
        for line in src:
            if FENCE_RE.match(line):
                in_fence = not in_fence
                continue
            if in_fence:
                continue
            m = HEADING_RE.match(line.rstrip('\n'))
            if not m:
                continue
            level = len(m.group(1))
            text = m.group(2).strip()
            if level == 1:
                h1_cells.append(ci)
                if not is_first_md:
                    findings.append({'kind': 'H1-DEEP', 'cell': ci, 'level': level, 'text': text[:90]})
            if (HINT_RE.match(text)
                    and not TITLED_STEP_RE.match(text)
                    and not COMPOUND_HINT_RE.match(text)
                    and not STEP_COMPOUND_RE.match(text)
                    and not RAPPEL_REFERENCE_RE.match(text)):
                findings.append({'kind': 'HINT-AS-HEADING', 'cell': ci, 'level': level, 'text': text[:90]})
    if len(h1_cells) > 1:
        findings.insert(0, {'kind': 'MULTI-H1', 'cell': h1_cells[0], 'level': 1,
                            'text': f'{len(h1_cells)} H1 across cells {h1_cells}'})
    return findings

def iter_notebooks(args):
    for a in args:
        p = pathlib.Path(a)
        if p.is_dir():
            yield from sorted(p.rglob('*.ipynb'))
        elif p.suffix == '.ipynb':
            yield p

def main():
    targets = sys.argv[1:]
    total = 0
    flagged = 0
    for nb in iter_notebooks(targets):
        if '_output' in nb.name or '.ipynb_checkpoints' in str(nb):
            continue
        total += 1
        fs = scan_notebook(nb)
        if fs:
            flagged += 1
            print(f'\n## {nb.as_posix()}')
            for f in fs:
                print(f"  [{f['kind']}] cell {f['cell']}  L{f.get('level','?')}  {f['text']}")
    print(f'\n=== {flagged}/{total} notebooks flagged ===')

if __name__ == '__main__':
    main()
