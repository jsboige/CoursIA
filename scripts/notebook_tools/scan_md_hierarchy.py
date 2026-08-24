#!/usr/bin/env python3
"""Audit notebook markdown cells for typographic pathologies.

Detects (source-level, render-agnostic):
  - COLLAPSED-MARKDOWN: a markdown cell whose newlines were stripped, gluing a
    heading + prose + GFM table rows (`| col ||---|`) + fenced code onto ONE
    line. Renders as broken text (the #3966 "mal affiche" / "titres
    difficilement visibles" defect). Signature: the cell contains a table
    separator fragment (`|` + 2+ dashes) but NO line is a clean GFM separator
    row (i.e. the separator is glued to other content, not on its own line).
    NOT caught by the heading checks below — a collapsed cell still parses as
    valid headings; the table structure is what breaks. See #3966.
  - HINT-AS-HEADING: a heading line (#..######) whose text reads like a hint/step/
    comment/aside (Indice, Astuce, Etape, Conseil, TODO, Note, Remarque, Attention,
    Solution, Exemple...) -> renders in a LARGE font when it should be small/body.
  - H1-DEEP: an H1 (`# `) appearing in a cell that is NOT the first markdown cell
    (multiple competing H1s / H1 used mid-notebook -> title hierarchy muddled).
  - MULTI-H1: more than one H1 across the whole notebook.

Usage: python scan_md_hierarchy.py <notebook-or-dir> [more...] [--fail-on-findings]
Outputs a per-notebook report + a machine-readable summary line per finding.

Drift mode (#11831): `--baseline --diff` compares the CURRENT per-notebook
finding counts against a committed baseline (`md_hierarchy_baseline.json`,
repo-relative posix paths -> {kind: count}). Exit 2 when any notebook/kind
INCREASED (new rendering defects introduced -- per-notebook, not net: fixing 10
in notebook A does not excuse adding 3 in notebook B), exit 0 when every delta
is <= 0 (pure cosmetic fixes are OK), exit 1 on broken input (unreadable
baseline, vacuous scan). `--update-baseline` re-seeds the file (deterministic:
sorted paths, sorted kinds) -- run it in the SAME commit as a scanner rule
change, else every subsequent PR shows false drift.

PR-scoping (#12735): `--pr-diff <file>` restricts both the scan target and the
drift report to the notebooks modified by the PR (paths listed one per line,
typically `git diff -M --name-only origin/main...HEAD`). This stops the
constant-on-every-PR drift that pre-dated the fix: when a notebook is renamed
elsewhere in the repo, an unscoped scan reads the new path against the old
baseline key and emits a spurious regression. Path lists outside the repo are
treated as forward slashes; non-notebook paths in the list are ignored at
scan time. When `--pr-diff` is supplied WITHOUT any positional `paths`, the
list itself supplies them.

An EMPTY scan is never reported as a clean scan: no argument, a mistyped path,
or a directory holding no notebook exits 2 with a message on stderr instead of
printing `0/0 notebooks flagged`. This scanner has already been fooled once by
a vacuous zero (the #3968 acceptance criterion, see HINT_RE below); `0/0` was
the second mouth of the same trap.
"""
import argparse, json, re, sys, pathlib

BASELINE_DEFAULT = pathlib.Path(__file__).with_name('md_hierarchy_baseline.json')

HEADING_RE = re.compile(r'^(#{1,6})\s+(.*\S)\s*$')
# Heading nested inside a list item or blockquote (`- # Indice : ...`,
# `> # Note`, `1. # Astuce`, nested `  - 1. # ...`). CommonMark renders an ATX
# heading inside a container as a REAL H1-H6, so `- # Indice` renders in the
# same giant font as a bare `# Indice` -- but HEADING_RE's `^` anchor never saw
# it, which is how 1325 in-list H1s across 138 notebooks survived the #3968
# burndown unflagged (repro: PR #11823, 6 hits, scanner said 0/1 flagged). The
# prefix grammar covers up to 3 container markers (bullet / ordered / blockquote,
# each optionally indented). A heading here is reported as HEADING-IN-LIST and
# deliberately does NOT feed the H1-DEEP / MULTI-H1 counters: the in-list
# placement is the primary defect, reported once, by its own kind. See #11829.
CONTAINER_HEADING_RE = re.compile(
    r'^(?:[ \t]*(?:[-*+]|\d+[.)]|>)[ \t]+){1,3}(#{1,6})\s+(.*\S)\s*$')
# Fenced code block delimiter (```... or ~~~...), possibly indented. Lines inside
# a fence are code, not markdown: a `# comment` there is a shell/python comment,
# NOT a heading, and must not be counted as H1 / HINT-AS-HEADING.
FENCE_RE = re.compile(r'^\s*(`{3,}|~{3,})')
# Text that should NOT be a heading (it's an aside / hint / step / inline label).
# Every stem is optionally-plural (`indices?`, `astuces?`, ...): the bare `\b`
# after a singular stem FAILS to match the plural form (`indice\b` does not match
# `Indices` — the `s` is inside the word, no boundary before it). That gap made
# `### Indices` / `### Astuces` / `### Conseils` invisible to this scanner, which
# is why it reported 0 hint-headings while ~194 plural-form hint-headings across
# ~102 notebooks survived the #3968 remediation uncaught (the "scanner reports 0"
# acceptance criterion of #3968 was vacuously satisfied). See #3966 follow-up.
HINT_RE = re.compile(
    r'^(indices?|astuces?|hints?|tips?|conseils?|notes?|remarques?|attention|todo|'
    r'etapes?|étapes?|steps?|rappels?|warnings?|important|aides?|pistes?|nb)\b',
    re.IGNORECASE)
# A numbered step WITH a descriptive title (`Step 1: Load Data`, `Step 1
# Import configuration`, `Étape 3 : Installation`) is a real titled SECTION
# header, not a bare aside. Without this exclusion the level-agnostic HINT_RE
# flags the tutorial's backbone H2s/H3s as hint-asides (false positives). Bare
# asides (`## Note`, `## Étape 3`, `### Note pédagogique`) carry no title
# after the number, so they stay flagged. See #3968 + #3966 c.754 follow-up
# (G.1 firsthand on GenAI/SemanticKernel/dotnet/notebooks/00-AI-settings.ipynb
# cells 1/3/5/7 — `### Step 1 Import configuration...` is a real section
# header with prose body, same pattern as `### Step 4: Save Configuration`).
TITLED_STEP_RE = re.compile(
    r'^(step|etape|étape)\s+\d+(?:\s*:\s*|\s+)\S',
    re.IGNORECASE)
# A hint word that is the FIRST PART of a hyphenated compound noun
# (`Aide-mémoire des commandes`) is a real titled section, not a bare aside:
# the hyphenated compound is a single lexical unit naming the section. A bare
# aside (`## Note`, `### Aide`) has no hyphenated compound, so it stays flagged.
# Without this, demoting `### Aide-mémoire des commandes` while its sibling
# `### Points clés à retenir` stays H3 would create an asymmetric hierarchy.
# See #3968.
COMPOUND_HINT_RE = re.compile(
    r'^(indices?|astuces?|hints?|tips?|conseils?|notes?|remarques?|attention|todo|'
    r'etapes?|étapes?|steps?|rappels?|warnings?|important|aides?|pistes?|nb)-',
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
    r'^rappels?\s+.*\d',
    re.IGNORECASE)
# --- COLLAPSED-MARKDOWN detection (#3966) ---
# A GFM table separator fragment: a pipe followed (after optional spaces) by a
# run of 2+ dashes. Presence means "the cell contains a table separator SOMEWHERE".
TABLE_SEP_FRAGMENT_RE = re.compile(r'\|[\s-]*-{2,}')
# A clean GFM separator/alignment ROW on its own line, optionally blockquote
# prefixed (`> |---|---|` is a legit blockquoted table, NOT collapsed). The line
# is made ONLY of pipes / dashes / colons / spaces (after an optional `>`), with
# a leading pipe and at least one dash run. The trailing pipe is OPTIONAL: GFM
# allows tables without trailing pipes (`| a | b` / `|---|---`), which are NOT
# collapsed — requiring a trailing pipe would false-positive on those (caught on
# Sudoku-6 cell 1, a valid no-trailing-pipe table). A collapsed cell has its
# separator glued to other content on the same physical line, so NO line matches.
CLEAN_SEP_LINE_RE = re.compile(r'^\s*>?\s*\|[\s:|-]*-{2,}[\s:|-]*\|?\s*$')


def _strip_fenced_code(cell_text):
    """Blank out fenced-code-block CONTENTS so code is invisible to the detector.

    A file tree (`sensitivity_lean/\n|-- lakefile`) or an ASCII payoff diagram
    inside a ``` / ~~~ fence is CODE, not a markdown table — its `|--` must NOT
    trigger the table-separator fragment. Fences are tracked line-by-line via
    FENCE_RE; fence-marker lines are kept, code lines between them are blanked.

    A truly COLLAPSED cell (newlines stripped, the fence opener ``` glued to a
    heading like `### Archi ``` ...`) has no real fence structure: the glued
    line does not START with ``` (FENCE_RE is anchored), so nothing is blanked
    and the glued table fragment is still detected -> correct (true positive
    preserved). See Lean-12 cell 16 FP (#3966).
    """
    out = []
    in_fence = False
    for line in cell_text.split('\n'):
        if FENCE_RE.match(line):
            in_fence = not in_fence
            out.append(line)  # keep the fence-marker line itself
            continue
        out.append('' if in_fence else line)
    return '\n'.join(out)


def _has_collapsed_markdown(cell_text):
    """True if a markdown cell's table structure is collapsed (#3966).

    The cell contains a GFM table-separator fragment but none of its lines is a
    clean separator row -> the separator (and the rows around it) are glued onto
    one line by a newline-strip event. Fenced code is blanked first so file
    trees / ASCII art are not mistaken for table fragments. ``cell_text`` is the
    raw joined source (newlines preserved, NOT splitlines-normalized).
    """
    stripped = _strip_fenced_code(cell_text)
    if not TABLE_SEP_FRAGMENT_RE.search(stripped):
        return False
    return not any(CLEAN_SEP_LINE_RE.match(line) for line in stripped.split('\n'))

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
        raw = cell.get('source', [])
        # cell_text preserves original newlines (collapsed-markdown detection
        # needs to know whether the separator is on its own line); src is the
        # splitlines-normalized list used by the heading loop below.
        if isinstance(raw, str):
            cell_text = raw
            src = raw.splitlines(keepends=False)
        else:
            cell_text = ''.join(raw)
            # Normalize to real LINES, not list elements: nbformat allows a
            # whole cell as a single-element multi-line list (e.g. QC-Py-Cloud-04
            # cells 2/10/12), and iterating elements makes every line inside
            # such an element invisible to all the line-based checks below.
            # Rendering-wise source is the concatenation, so splitlines of the
            # join IS what the renderer sees. See #11829.
            src = cell_text.splitlines(keepends=False)
        # COLLAPSED-MARKDOWN (#3966): table separator glued on one line.
        if _has_collapsed_markdown(cell_text):
            findings.append({'kind': 'COLLAPSED-MARKDOWN', 'cell': ci, 'level': 0,
                             'text': cell_text[:90].replace('\n', ' ')})
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
                cm = CONTAINER_HEADING_RE.match(line.rstrip('\n'))
                if cm:
                    findings.append({'kind': 'HEADING-IN-LIST', 'cell': ci,
                                     'level': len(cm.group(1)),
                                     'text': cm.group(2).strip()[:90]})
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
    """Yield the notebooks designated by `args` (dirs are walked recursively).

    Raises ValueError if a target designates nothing, so that a typo can never
    be mistaken for a clean scan (see `main`).
    """
    unresolved = []
    for a in args:
        p = pathlib.Path(a)
        if p.is_dir():
            yield from sorted(p.rglob('*.ipynb'))
        elif p.suffix == '.ipynb' and p.is_file():
            yield p
        else:
            unresolved.append(a)
    if unresolved:
        raise ValueError('not a notebook nor a directory: ' + ', '.join(unresolved))


# --- Drift mode (#11831) ------------------------------------------------------

def _repo_root():
    """Git toplevel du depot, sinon cwd (les corpus de test vivent hors repo)."""
    import subprocess
    try:
        out = subprocess.run(['git', 'rev-parse', '--show-toplevel'],
                             capture_output=True, text=True, timeout=10)
        if out.returncode == 0:
            return pathlib.Path(out.stdout.strip())
    except Exception:
        pass
    return pathlib.Path.cwd()


def notebook_key(nb_path, repo_root=None):
    """Cle stable d'un notebook dans la baseline : posix RELATIVE au repo root.

    Seeded depuis la racine du repo (CI comme local), la cle est
    `MyIA.AI.Notebooks/...ipynb` -- identique que l'invocation passe un chemin
    relatif ou absolu. Hors repo (corpus de test tmp), retombe sur un chemin
    relatif au cwd : stable au sein d'un meme run, ce qui suffit aux fixtures.
    """
    p = pathlib.Path(nb_path)
    root = repo_root if repo_root is not None else _repo_root()
    for base in (root, pathlib.Path.cwd()):
        try:
            return p.resolve().relative_to(base.resolve()).as_posix()
        except ValueError:
            continue
    return p.as_posix()


def compute_counts(paths):
    """Per-notebook finding counts: {stable key: {kind: count}}.

    Keys are POSIX repo-relative (see notebook_key) so the baseline matches
    across invocation styles and OSes. READ_ERROR (unparseable notebook) counts
    as its own kind: a newly-corrupted notebook IS a regression the gate should
    catch, not a silent skip.
    """
    root = _repo_root()
    counts = {}
    for nb in iter_notebooks(paths):
        if '_output' in nb.name or '.ipynb_checkpoints' in str(nb):
            continue
        kinds = {}
        for f in scan_notebook(nb):
            kinds[f['kind']] = kinds.get(f['kind'], 0) + 1
        if kinds:
            counts[notebook_key(nb, root)] = kinds
    return counts


def diff_against_baseline(current, baseline):
    """(regressions, improvements) -- per notebook/kind deltas.

    regressions: [(key, kind, delta)] with delta > 0 (new defects; a kind
    absent from the baseline entry counts its full count as delta). improvements:
    same shape with delta < 0 -- burndown progress, reported, never a failure.
    A notebook that went fully clean (or was deleted) burns down every one of
    its baseline kinds: the per-kind detail IS the review, an aggregate "gone"
    line would hide it.
    Per-notebook, deliberately NOT netted: offsetting a new defect in notebook B
    by a fix in notebook A must still flag B (the fix in A and the defect in B
    are two different reviews).
    """
    regressions, improvements = [], []
    keys = set(current) | set(baseline)
    for path in sorted(keys):
        cur = current.get(path, {})
        base = baseline.get(path, {})
        for kind in sorted(set(cur) | set(base)):
            delta = cur.get(kind, 0) - base.get(kind, 0)
            if delta > 0:
                regressions.append((path, kind, delta))
            elif delta < 0:
                improvements.append((path, kind, delta))
    return regressions, improvements


def load_baseline(path):
    """Parse the baseline JSON -> {relpath: {kind: count}}. Raises on garbage."""
    raw = json.loads(pathlib.Path(path).read_text(encoding='utf-8'))
    notebooks = raw.get('notebooks')
    if not isinstance(notebooks, dict):
        raise ValueError(
            f"baseline '{path}' lacks a 'notebooks' mapping -- regenerate with "
            f"--update-baseline (format is owned by this scanner)")
    return notebooks


def load_pr_diff_paths(path):
    """Read a `git diff -M --name-only` style file -> set of repo-root POSIX keys.

    Normalises backslashes to slashes and strips the leading './' if present.
    The returned set is matched against `notebook_key()` outputs (which are
    also POSIX-relative to the repo root), so a path written by `git diff
    --name-only` round-trips without further normalisation.

    Empty lines and pure whitespace are skipped. A missing file raises; the
    caller decides whether `--pr-diff` was optional.
    """
    p = pathlib.Path(path)
    if not p.exists():
        raise FileNotFoundError(f"--pr-diff file not found: {path}")
    out = set()
    for raw_line in p.read_text(encoding='utf-8').splitlines():
        line = raw_line.strip()
        if not line:
            continue
        line = line.replace('\\', '/')
        if line.startswith('./'):
            line = line[2:]
        out.add(line)
    return out


def write_baseline(path, counts):
    """Serialize counts deterministically (sorted paths, sorted kinds)."""
    payload = {
        '_comment': ('Per-notebook finding counts of scan_md_hierarchy.py. '
                     'BURNDOWN, do not grow: a PR that increases any count is '
                     'flagged by scan-md-hierarchy-drift.yml (#11831). '
                     'Regenerate (same commit as any scanner rule change) with: '
                     'python scripts/notebook_tools/scan_md_hierarchy.py '
                     'MyIA.AI.Notebooks/ --update-baseline'),
        'total_findings': sum(sum(k.values()) for k in counts.values()),
        'notebooks': {p: dict(sorted(k.items())) for p, k in sorted(counts.items())},
    }
    pathlib.Path(path).write_text(
        json.dumps(payload, ensure_ascii=False, indent=1, sort_keys=False) + '\n',
        encoding='utf-8')


def main(argv=None):
    parser = argparse.ArgumentParser(
        description=__doc__.splitlines()[0],
        formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('paths', nargs='+', metavar='NOTEBOOK-OR-DIR',
                        help='notebooks and/or directories to scan (recursive)')
    parser.add_argument('--fail-on-findings', action='store_true',
                        help='exit 1 when at least one notebook is flagged '
                             '(default: always exit 0, census mode)')
    parser.add_argument('--baseline', nargs='?', const=str(BASELINE_DEFAULT),
                        default=None, metavar='BASELINE_JSON',
                        help='baseline path for drift mode '
                             '(default: scripts/notebook_tools/md_hierarchy_baseline.json)')
    parser.add_argument('--diff', action='store_true',
                        help='drift mode: report per-notebook deltas vs the '
                             'baseline; exit 2 on any increase, 0 on pure '
                             'burndown, 1 on broken input (#11831)')
    parser.add_argument('--update-baseline', action='store_true',
                        help='(re)seed the baseline from the current scan '
                             'instead of diffing -- SAME commit as any scanner '
                             'rule change, else every PR shows false drift')
    parser.add_argument('--pr-diff', default=None, metavar='PATH_FILE',
                        help='restrict the scan (and the drift report) to '
                             'notebooks modified by the PR -- a file listing '
                             'one path per line, typically the output of '
                             '`git diff -M --name-only origin/main...HEAD` '
                             '(see #12735). When supplied WITHOUT positional '
                             'paths, the list itself supplies them. '
                             'In drift mode: regressions/improvements outside '
                             'the list are NOT printed (the baseline still '
                             'participates so renames upstream do not bleed).')
    args = parser.parse_args(argv)

    try:
        notebooks = list(iter_notebooks(args.paths))
    except ValueError as exc:
        parser.error(str(exc))

    if args.baseline is not None and not (args.diff or args.update_baseline):
        parser.error('--baseline requires --diff or --update-baseline')
    drift = args.diff or args.update_baseline

    # PR-scoping (#12735): when `--pr-diff` is given, restrict BOTH the scan
    # target and the drift report to the files modified by the PR. A path is
    # considered "in scope" if it appears in the diff list (POSIX-relative to
    # repo root) AND ends in `.ipynb`. Other paths in the diff (Markdown,
    # scripts, ...) are acknowledged but ignored here -- this scanner only
    # cares about notebooks. Empty diff = vacuous; do NOT collapse to "clean".
    pr_diff_paths = None
    if args.pr_diff is not None:
        try:
            pr_diff_paths = load_pr_diff_paths(args.pr_diff)
        except (OSError, ValueError) as e:
            print(f'ERROR: unreadable --pr-diff file {args.pr_diff}: {e}',
                  file=sys.stderr)
            return 1
        nb_in_pr = {p for p in pr_diff_paths if p.endswith('.ipynb')}
        if not nb_in_pr:
            print(f'ERROR: --pr-diff {args.pr_diff} contains no .ipynb paths '
                  '-- nothing to scan, this is NOT an all-clear.',
                  file=sys.stderr)
            return 1
        before = len(notebooks)
        notebooks = [nb for nb in notebooks
                     if notebook_key(nb) in nb_in_pr]
        if not notebooks:
            print(f'ERROR: --pr-diff restricts the scan to {len(nb_in_pr)} '
                  f'notebook(s) but the positional `paths` resolved to none '
                  f'of them ({before} candidate(s) outside the PR).',
                  file=sys.stderr)
            return 1

    if drift:
        # Diff mode re-scans through compute_counts (same filters as census).
        # A scan where every notebook is CLEAN yields counts={} -- legitimate;
        # vacuous means iter_notebooks itself designated nothing.
        if not notebooks:
            print('ERROR: no notebook found under the given paths -- nothing '
                  'was scanned, this is NOT an all-clear.', file=sys.stderr)
            return 1
        baseline_path = args.baseline or str(BASELINE_DEFAULT)
        counts = compute_counts(args.paths)
        if args.update_baseline:
            write_baseline(baseline_path, counts)
            print(f'baseline updated: {baseline_path} '
                  f'({len(counts)} notebooks, '
                  f'{sum(sum(k.values()) for k in counts.values())} findings)')
            return 0
        try:
            baseline = load_baseline(baseline_path)
        except (OSError, ValueError, json.JSONDecodeError) as e:
            print(f'ERROR: unreadable baseline {baseline_path}: {e}',
                  file=sys.stderr)
            return 1
        regressions, improvements = diff_against_baseline(counts, baseline)
        if pr_diff_paths is not None:
            # Keep ONLY the deltas that touch files modified by this PR.
            # Baselines may still have stale keys (e.g. renamed notebooks) --
            # those don't print here because no PR actually introduces them.
            regressions = [(p, k, d) for p, k, d in regressions
                           if p in pr_diff_paths]
            improvements = [(p, k, d) for p, k, d in improvements
                            if p in pr_diff_paths]
        for path, kind, delta in regressions:
            print(f'  +{delta} {kind}  {path}')
        for path, kind, delta in improvements:
            print(f'  {delta} {kind}  {path}  (burndown)')
        # Last stdout line, same contract as census mode (CI reads tail -1).
        print(f'\n=== drift: +{sum(d for _, _, d in regressions)} '
              f'across {len({p for p, _, _ in regressions})} notebook(s), '
              f'{sum(-d for _, _, d in improvements)} burned down ===')
        return 2 if regressions else 0

    total = 0
    flagged = 0
    for nb in notebooks:
        if '_output' in nb.name or '.ipynb_checkpoints' in str(nb):
            continue
        total += 1
        fs = scan_notebook(nb)
        if fs:
            flagged += 1
            print(f'\n## {nb.as_posix()}')
            for f in fs:
                print(f"  [{f['kind']}] cell {f['cell']}  L{f.get('level','?')}  {f['text']}")
    if total == 0:
        # An empty scan is NOT a clean scan: say so, and fail. `0/0 flagged`
        # otherwise reads as an all-clear while nothing has been looked at.
        print('ERROR: no notebook found under the given paths -- nothing was '
              'scanned, this is NOT an all-clear.', file=sys.stderr)
        return 2
    # Keep this the LAST stdout line: the CI census reads it with `tail -1`.
    print(f'\n=== {flagged}/{total} notebooks flagged ===')
    return 1 if (flagged and args.fail_on_findings) else 0

if __name__ == '__main__':
    sys.exit(main())
