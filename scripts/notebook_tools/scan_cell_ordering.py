#!/usr/bin/env python3
"""Scan notebooks for cell-ordering and enchainement (flow) problems.

Productionises the throwaway audit script of Epic #2639 (#3240). The class
friction it targets: "certaines choses n'etaient pas a leur place" -- canonical
order slippage and forgotten/misplaced cells that slip through upstream review.

It reads the BEGINNING and the END of every cell and looks for:

  HIGH   SECTION_ORDER      numbered markdown headers going backwards
                            (e.g. "## 3." then "## 2." under the same parent)
  HIGH   EXERCISE_ORDER     "Exercice N" / "Exemple N" labels out of order
  MED    DANGLING_INTRO     a markdown cell ends by announcing imminent code
                            ("executons", "ci-dessous", "le code suivant"...)
                            but the next cell is NOT code -> forgotten/misplaced
  MED    INTERP_BEFORE_CODE an interpretation markdown ("on observe", "le
                            resultat montre"...) sits directly BEFORE the code
                            it comments instead of after its output
  LOW    SECTION_GAP        a numbered header skips a value (possible omission)
  LOW    CONSECUTIVE_CODE   > 3 code cells in a row with no markdown between

The #2639 scanner flagged EVERY "## N." header (~100% false positives). The
fix here: legitimate numbering is never flagged -- only a genuine DECREASE at a
given numbering depth under the same parent prefix is reported as HIGH. A normal
increment (1 -> 2), a sub-section start (3 -> 3.1) and a sub-section close
(3.2 -> 4) are all silent.

Every finding cites the offending text so it is spot-checkable.

Usage:
    python scan_cell_ordering.py <notebook.ipynb>
    python scan_cell_ordering.py --family SymbolicAI/SymbolicLearning
    python scan_cell_ordering.py --all
    python scan_cell_ordering.py --all --json
    python scan_cell_ordering.py --all --severity HIGH   # filter

Exit codes:
    0 - no findings at or above --fail-on (default HIGH)
    1 - findings at or above --fail-on
    2 - usage / IO error
"""

import argparse
import json
import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
NOTEBOOKS_DIR = REPO_ROOT / "MyIA.AI.Notebooks"

EXCLUDE_DIRS = {
    ".ipynb_checkpoints", ".git", "__pycache__", "obj", "bin",
    "_output", "research", "archive", "partner-course", "examples",
    ".venv", "node_modules",
}

SEVERITY_ORDER = {"LOW": 0, "MED": 1, "HIGH": 2}

# A numbered markdown header: leading #'s, then a dotted number, then a label.
# Accepts "## 3. Titre", "### 3.2 Titre", "## 3 - Titre".
_HEADER_RE = re.compile(r"^(#{1,6})\s+(\d+(?:\.\d+)*)\b[.\)\-:]?\s*(.*)$")

# "Exercice 2" / "Exemple 3" used as a LABEL: anchored to the start of a
# header (#...) or a bold (**...) line, so a prose mention of "exercice 3"
# buried mid-sentence (e.g. inside an "**Indice** : ..." line) is NOT taken
# for a section label.
_EXO_RE = re.compile(
    r"^(?:#{1,6}\s+|\*\*\s*)(exerc\w*|exemple|example)\s*(?:n[o°]?\s*)?(\d+)\b", re.I)

# Announce-imminent-code detection, precision-first (two tiers):
#  - a code-NOUN phrase ("le code suivant", "la cellule ci-dessous", "voici le
#    code"...) always counts as an announcement;
#  - a bare imperative verb ("executons", "implementons"...) counts ONLY when
#    the line ends with a colon -- real code intros read "Executons le code
#    suivant :", whereas prose like "nous implementons les concepts a la main"
#    (period, no colon, no code noun) must not trigger.
_CODE_NOUN_RE = re.compile(
    r"(le code (?:qui suit|suivant|ci[- ]?dessous|ci[- ]?apr[eè]s)"
    r"|la cellule (?:suivante|ci[- ]?dessous|qui suit)"
    r"|dans la cellule (?:suivante|ci[- ]?dessous)"
    r"|la fonction ci[- ]?dessous"
    r"|le script (?:suivant|ci[- ]?dessous)"
    r"|voici (?:le code|la fonction|l'impl[eé]mentation))",
    re.I,
)
_IMPERATIVE_RE = re.compile(
    r"\b(ex[eé]cutons|lan[cç]ons|codons|impl[eé]mentons|d[eé]finissons|"
    r"cr[eé]ons|testons|essayons)\b",
    re.I,
)


def _announces_code(line: str) -> bool:
    line = line.strip()
    if _CODE_NOUN_RE.search(line):
        return True
    return bool(_IMPERATIVE_RE.search(line)) and line.endswith(":")

# A markdown cell that BEGINS interpreting an output.
_INTERP_RE = re.compile(
    r"^(on (observe|constate|voit|remarque|note)|le r[eé]sultat|"
    r"ces r[eé]sultats|la sortie|l'output|comme (le montre|on (le )?voit)|"
    r"on peut (voir|constater|observer)|cette sortie|ces sorties)",
    re.I,
)


def find_notebooks(family: str | None = None) -> list[Path]:
    """Discover pedagogical notebooks (same convention as audit_c1_c3.py)."""
    root = NOTEBOOKS_DIR / family if family else NOTEBOOKS_DIR
    if not root.exists():
        return []
    out = []
    for p in root.rglob("*.ipynb"):
        if any(part in EXCLUDE_DIRS for part in p.parts):
            continue
        out.append(p)
    return sorted(out)


_FENCE_RE = re.compile(r"^\s*(```+|~~~+)")


def _lines(source) -> list[str]:
    """All lines, EXCLUDING those inside fenced code blocks (``` or ~~~).

    A markdown cell can embed a shell/code snippet whose comment lines start
    with '#'; those are NOT section headers, so everything between matching
    fences is dropped before any header / exercise / enchainement analysis.
    """
    text = source if isinstance(source, str) else "".join(source)
    out, in_fence = [], False
    for ln in text.splitlines():
        if _FENCE_RE.match(ln):
            in_fence = not in_fence
            continue
        if not in_fence:
            out.append(ln.rstrip("\n"))
    return out


def _nonempty(lines: list[str]) -> list[str]:
    return [ln for ln in lines if ln.strip()]


def head_tail(source, n: int = 2) -> tuple[list[str], list[str]]:
    """Return (first n non-empty lines, last n non-empty lines) of a cell."""
    ne = _nonempty(_lines(source))
    if not ne:
        return [], []
    return ne[:n], ne[-n:]


def _num_tuple(s: str) -> tuple[int, ...]:
    return tuple(int(x) for x in s.split("."))


def scan_section_order(cells: list[dict]) -> list[dict]:
    """Flag numbered headers that regress, under the same parent prefix.

    last_child[parent_tuple] = highest child number seen for that parent.
    A header (parent, child) regresses iff child < last_child[parent].
    A gap is child > last_child[parent] + 1.
    """
    findings = []
    # key = (heading_level, parent_number_tuple). Keying on the heading level
    # keeps an H1 title like "# 13. ..." (the notebook's series number) in a
    # separate namespace from its "## 0.", "## 1." ... H2 sections, so the
    # title number never looks like a section regression.
    last_child: dict[tuple, int] = {}
    for i, cell in enumerate(cells):
        if cell.get("cell_type") != "markdown":
            continue
        for ln in _lines(cell.get("source", [])):
            m = _HEADER_RE.match(ln.strip())
            if not m:
                continue
            level = len(m.group(1))
            num = _num_tuple(m.group(2))
            parent, child = num[:-1], num[-1]
            key = (level, parent)
            prev = last_child.get(key)
            parent_label = ".".join(map(str, parent)) or "<root>"
            if prev is None:
                last_child[key] = child
            elif child < prev and child == 1:
                # Reset to 1 = legitimate new numbering group (new part, items
                # after a table-of-contents cell, multi-section notebook).
                # Start a fresh group and clear any deeper nested counters.
                last_child[key] = 1
                for k in [k for k in last_child if len(k[1]) > len(parent) and k[1][:len(parent)] == parent]:
                    del last_child[k]
            elif child < prev:
                # Genuine mid-sequence backwards jump (e.g. 4 then 2) = real slippage.
                findings.append({
                    "cell_index": i, "category": "SECTION_ORDER", "severity": "HIGH",
                    "evidence": ln.strip()[:120],
                    "message": f"section {m.group(2)} appears after {'.'.join(map(str, parent + (prev,))) if parent else prev} "
                               f"(numbering goes backwards under parent {parent_label})",
                })
                last_child[key] = max(prev, child)
            elif child > prev + 1:
                findings.append({
                    "cell_index": i, "category": "SECTION_GAP", "severity": "LOW",
                    "evidence": ln.strip()[:120],
                    "message": f"section {m.group(2)} skips from {prev} to {child} under parent "
                               f"{parent_label} (possible omitted section)",
                })
                last_child[key] = child
            else:
                last_child[key] = child
    return findings


def scan_exercise_order(cells: list[dict]) -> list[dict]:
    """Flag Exercice/Exemple labels whose number decreases (separate sequences).

    A single markdown cell that lists >= 2 labels of the same kind is treated as
    a table-of-contents / overview cell and skipped for sequencing -- otherwise
    a TOC enumerating "Exercice 2..5" before the exercises themselves restart at
    2 would read as a backwards jump (false positive).
    """
    findings = []
    last = {"exerc": 0, "exemp": 0}  # exercices and exemples cohabit -> separate
    for i, cell in enumerate(cells):
        if cell.get("cell_type") != "markdown":
            continue
        labels = []  # (kind, n, line) in document order
        for ln in _lines(cell.get("source", [])):
            m = _EXO_RE.match(ln.strip())
            if not m:
                continue
            kind = "exemp" if m.group(1).lower().startswith(("exemple", "example")) else "exerc"
            labels.append((kind, int(m.group(2)), ln.strip()))
        per_kind = {"exerc": 0, "exemp": 0}
        for kind, _, _ in labels:
            per_kind[kind] += 1
        for kind, n, stripped in labels:
            if per_kind[kind] >= 2:
                continue  # TOC / overview cell -> not a sequence point
            if last[kind] and n < last[kind] and n == 1:
                last[kind] = 1  # restart, legitimate
            elif last[kind] and n < last[kind]:
                findings.append({
                    "cell_index": i, "category": "EXERCISE_ORDER", "severity": "HIGH",
                    "evidence": stripped[:120],
                    "message": f"{'Exemple' if kind == 'exemp' else 'Exercice'} {n} appears after "
                               f"{'Exemple' if kind == 'exemp' else 'Exercice'} {last[kind]} (out of order)",
                })
                last[kind] = max(last[kind], n)
            else:
                last[kind] = max(last[kind], n)
    return findings


def scan_enchainement(cells: list[dict]) -> list[dict]:
    """Read begin/end of cells: dangling intros and misplaced interpretations."""
    findings = []
    n = len(cells)
    for i, cell in enumerate(cells):
        if cell.get("cell_type") != "markdown":
            continue
        head, tail = head_tail(cell.get("source", []))
        nxt = cells[i + 1] if i + 1 < n else None
        prev = cells[i - 1] if i > 0 else None

        # DANGLING_INTRO: ends announcing code, but next cell is not code.
        if tail and _announces_code(tail[-1]) and nxt is not None and nxt.get("cell_type") != "code":
            findings.append({
                "cell_index": i, "category": "DANGLING_INTRO", "severity": "MED",
                "evidence": tail[-1].strip()[:120],
                "message": "markdown announces imminent code but the next cell is not code "
                           "(forgotten or misplaced code cell?)",
            })

        # INTERP_BEFORE_CODE: begins interpreting output, sits before code rather than after.
        if head and _INTERP_RE.search(head[0].strip()):
            prev_is_code = prev is not None and prev.get("cell_type") == "code"
            next_is_code = nxt is not None and nxt.get("cell_type") == "code"
            if not prev_is_code and next_is_code:
                findings.append({
                    "cell_index": i, "category": "INTERP_BEFORE_CODE", "severity": "MED",
                    "evidence": head[0].strip()[:120],
                    "message": "interpretation markdown precedes the code it comments "
                               "(interpretation should follow the output)",
                })
    return findings


def scan_consecutive_code(cells: list[dict], threshold: int = 3) -> list[dict]:
    findings = []
    streak = 0
    start = None
    for i, cell in enumerate(cells):
        if cell.get("cell_type") == "code":
            if streak == 0:
                start = i
            streak += 1
        else:
            if streak > threshold:
                findings.append({
                    "cell_index": start, "category": "CONSECUTIVE_CODE", "severity": "LOW",
                    "evidence": f"cells {start}..{i - 1}",
                    "message": f"{streak} consecutive code cells with no markdown between",
                })
            streak = 0
    if streak > threshold:
        findings.append({
            "cell_index": start, "category": "CONSECUTIVE_CODE", "severity": "LOW",
            "evidence": f"cells {start}..{len(cells) - 1}",
            "message": f"{streak} consecutive code cells with no markdown between",
        })
    return findings


def scan_notebook(path: Path) -> dict:
    try:
        nb = json.loads(path.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, UnicodeDecodeError, OSError) as exc:
        return {"path": str(path), "error": str(exc), "findings": []}
    cells = nb.get("cells", [])
    findings = (
        scan_section_order(cells)
        + scan_exercise_order(cells)
        + scan_enchainement(cells)
        + scan_consecutive_code(cells)
    )
    findings.sort(key=lambda f: (f["cell_index"], -SEVERITY_ORDER[f["severity"]]))
    return {"path": str(path), "findings": findings}


def _rel(path: str) -> str:
    try:
        return str(Path(path).resolve().relative_to(REPO_ROOT))
    except ValueError:
        return path


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description="Scan notebooks for cell-ordering / enchainement problems.")
    ap.add_argument("notebook", nargs="?", help="single notebook path")
    ap.add_argument("--family", help="scan a family dir under MyIA.AI.Notebooks/ (e.g. SymbolicAI/SymbolicLearning)")
    ap.add_argument("--all", action="store_true", help="scan all pedagogical notebooks")
    ap.add_argument("--json", action="store_true", help="JSON output")
    ap.add_argument("--severity", choices=["LOW", "MED", "HIGH"], help="only show findings at/above this severity")
    ap.add_argument("--fail-on", choices=["LOW", "MED", "HIGH"], default="HIGH",
                    help="exit 1 if any finding at/above this severity (default HIGH)")
    args = ap.parse_args(argv)

    if args.notebook:
        targets = [Path(args.notebook)]
    elif args.family:
        targets = find_notebooks(args.family)
    elif args.all:
        targets = find_notebooks()
    else:
        ap.error("provide a notebook path, --family, or --all")
        return 2

    if not targets:
        print("No notebooks found.", file=sys.stderr)
        return 2

    min_show = SEVERITY_ORDER[args.severity] if args.severity else -1
    fail_at = SEVERITY_ORDER[args.fail_on]

    reports = []
    worst = -1
    for path in targets:
        rep = scan_notebook(path)
        rep["findings"] = [f for f in rep["findings"] if SEVERITY_ORDER[f["severity"]] >= min_show]
        if rep["findings"]:
            worst = max(worst, max(SEVERITY_ORDER[f["severity"]] for f in rep["findings"]))
        reports.append(rep)

    if args.json:
        print(json.dumps({"reports": [r for r in reports if r.get("findings") or r.get("error")]},
                         ensure_ascii=False, indent=2))
    else:
        total = 0
        for rep in reports:
            if rep.get("error"):
                print(f"  ERROR {_rel(rep['path'])}: {rep['error']}")
                continue
            if not rep["findings"]:
                continue
            print(f"\n{_rel(rep['path'])}")
            for f in rep["findings"]:
                total += 1
                print(f"  [{f['severity']:4}] cell#{f['cell_index']:<3} {f['category']:18} {f['message']}")
                print(f"         > {f['evidence']}")
        scanned = len(targets)
        clean = sum(1 for r in reports if not r.get("findings") and not r.get("error"))
        print(f"\nScanned {scanned} notebook(s): {clean} clean, {total} finding(s).")

    return 1 if worst >= fail_at else 0


if __name__ == "__main__":
    sys.exit(main())
