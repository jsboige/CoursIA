#!/usr/bin/env python3
"""Detect SVG ``decimal-comma`` rendering defects in ``.ipynb`` notebook outputs.

Why this tool exists
--------------------
An inline-C# SVG builder that formats coordinates via interpolated strings like
``$"<polyline points='{px:F1},{py:F1}'>"`` is **culture-sensitive**: on a fr-FR
worker (the cluster default), ``:F1`` / ``:F2`` / ``:F3`` emit a **comma** as the
decimal separator (``70,0`` instead of ``70.0``). Per the SVG spec, a comma is a
**coordinate separator** — so Chromium parses ``cx='70,0'`` as two values
(console ``Expected length`` -> defaults to ``0``), and a polyline
``points="70,0,334,4 84,7,342,5"`` is read as **44 zigzag points** instead of
22. The chart silently mis-renders (or collapses to origin), defeating the PR's
explicit goal "render on GitHub / nbviewer".

This defect is **invisible to every code forensic**: CI validates structure +
source, the JSON is well-formed, the SVG tag is present. Only **render QA**
(vision-capable lane) catches it — established firsthand on PRs #6946
(Infer-17) and #6960 (MGS-15), where 4 code-forensics passed and a single
vision-QA review (po-2024 c.581) flagged it. By the time a vision lane runs,
the broken chart is already committed.

This scanner makes the defect **un-committable** by flagging, in committed
notebook *outputs*, any SVG coordinate attribute whose value contains a
``digit,digit`` where the comma acts as a decimal separator. It is a CI gate
(sibling of ``banner-guard.yml`` / ``pip-leak-guard.yml``) — see
``svg-decimal-comma-guard.yml``.

Detection logic (precise, low false-positive)
---------------------------------------------
The naive ``\\d,\\d`` regex over-matches the LEGITIMATE coordinate separator:
a correct point ``"70,334.362"`` (x=70, y=334.362, comma = separator) also
contains ``0,3``. So the detector targets the two unambiguous bug signatures:

1. **Multi-comma points**: a polyline/points coordinate with MORE than one
   comma in a single space-separated token is always broken
   (``70,0,334,4`` = 4 numbers, never valid: an SVG point is exactly x,y).
2. **Single-quoted/double-quoted single-value attrs with a comma**: ``cx='70,0'``,
   ``x="10,5"``, ``width='3,0'`` — a single coordinate value must be ONE number;
   a comma inside it is always the decimal-comma bug.

Graphviz model-diagram SVGs (``<g id="graph0" class="graph">`` with integer
coords like ``points="10,20 30,40"``) are **legitimate** (each token is exactly
2 integers, comma = separator) and do NOT trip either signature. Confirmed on
a repo-wide scan: the only true positives are inline-C# SVG builders using
``:F*`` formatting without ``InvariantCulture`` (cf #6946 / #6960).

Usage
-----
    python detect_svg_decimal_comma.py --scan <path>      # dry-run, list only
    python detect_svg_decimal_comma.py --scan-all         # dry-run repo-wide
    python detect_svg_decimal_comma.py --scan-all --check # exit 1 if defects found
    python detect_svg_decimal_comma.py --apply <path>     # fix in place (culture note)

Note: ``--apply`` is intentionally a NO-OP guide (prints the root-cause fix).
Unlike the probeAddresses banner (which has a deterministic output-only strip),
the decimal-comma defect's durable fix is at the **SOURCE** (replace ``:F*``
with an ``InvariantCulture`` format) and requires re-execution — there is no
honest output-only patch (hand-editing the output would falsify execution
evidence, banned by secrets-hygiene.md rule 6 / Stop & Repair). The scan
flags the defect so the author fixes the source + re-executes.

Scope: main-repo notebooks only (``--exclude-submodules``), same as
banner-guard. Submodules are separate repos with their own CI.
"""

from __future__ import annotations

import argparse
import glob
import json
import os
import re
import sys

# --- SVG coordinate attributes where a single value is expected (x, y, cx, cy,
# r, width, height, x1, y1, x2, y2). If such an attr's value contains a comma,
# it is the decimal-comma bug (a coordinate value is a single number).
SINGLE_VALUE_COORD_ATTRS = ("cx", "cy", "r", "width", "height", "x1", "y1", "x2", "y2", "x", "y", "fx", "fy", "rx", "ry")

# Match attr='val' or attr="val" for a coord attribute; capture the value.
# Value containing a digit-comma-digit = decimal-comma bug.
_ATTR_RE = {a: re.compile(r"\b" + a + r"\s*=\s*(['\"])([^'\"]*?\d,\d[^'\"]*?)\1") for a in SINGLE_VALUE_COORD_ATTRS}

# polyline/polygon points: space-separated tokens, each must be "x,y" (exactly one comma).
_POINTS_RE = re.compile(r"<(?:polyline|polygon)\b[^>]*\bpoints\s*=\s*(['\"])([^'\"]+?)\1", re.IGNORECASE)


def _html_blob_to_str(blob):
    """Normalize a notebook output ``data["text/html"]`` value to a single string.

    On-disk format is a ``list[str]`` (one line per element); a bare string is
    tolerated for robustness.
    """
    if isinstance(blob, list):
        return "".join(blob)
    if isinstance(blob, str):
        return blob
    return ""


def _is_graphviz(svg_chunk: str) -> bool:
    """Graphviz-generated SVGs use legit integer coords (no decimal-comma bug).

    They carry a distinctive ``<g id="graph0" class="graph">`` marker. We still
    run the precise signatures on them (they won't trip), but this lets us label
    them in the report so a reviewer understands why a big SVG is clean.
    """
    return 'id="graph0"' in svg_chunk or "id='graph0'" in svg_chunk or 'class="graph"' in svg_chunk


def find_decimal_comma_defects(html: str):
    """Return a list of human-readable defect strings for one HTML blob.

    Each defect names the precise broken token/attr so the fix is actionable.
    Empty list = clean (or no SVG present).
    """
    if "<svg" not in html:
        return []
    defects = []

    # Signature 1: polyline/polygon points with a token that has >1 comma.
    for m in _POINTS_RE.finditer(html):
        points_value = m.group(2)
        for token in points_value.split():
            # An SVG point token is exactly "x,y" -> one comma. More than one
            # comma (e.g. "70,0,334,4") is the decimal-comma bug.
            if token.count(",") > 1:
                defects.append(
                    "polyline/polygon point token %r has %d commas (decimal-comma bug; "
                    "should be a single x,y pair)" % (token, token.count(","))
                )
                break  # one bad token per points attribute is enough to flag

    # Signature 2: single-value coord attr whose value contains a digit,digit.
    for attr, regex in _ATTR_RE.items():
        for m in regex.finditer(html):
            val = m.group(2)
            defects.append(
                "%s=%r contains a digit,digit (decimal-comma bug; a single coord "
                "value must be one number)" % (attr, val)
            )

    return defects


def scan_notebook(nb_path):
    """Yield (cell_index, defect_strings) for each code cell carrying defects.

    Returns an empty list when the notebook is clean.
    """
    found = []
    try:
        with open(nb_path, encoding="utf-8") as f:
            nb = json.load(f)
    except (OSError, json.JSONDecodeError):
        return found

    for ci, cell in enumerate(nb.get("cells", [])):
        if cell.get("cell_type") != "code":
            continue
        for output in cell.get("outputs", []):
            data = output.get("data", {}) if isinstance(output, dict) else {}
            html = _html_blob_to_str(data.get("text/html", ""))
            if not html:
                continue
            defects = find_decimal_comma_defects(html)
            if defects:
                found.append((ci, defects))
    return found


def count_defect_lines(nb_path):
    """Total decimal-comma defect count across the notebook (for the summary)."""
    return sum(len(defects) for _, defects in scan_notebook(nb_path))


def iter_notebooks(nb_root):
    """Yield every ``.ipynb`` under ``nb_root`` (sorted, deterministic)."""
    for p in sorted(glob.glob(os.path.join(nb_root, "**", "*.ipynb"), recursive=True)):
        if os.path.islink(p):
            continue
        if os.sep + "_archives" + os.sep in p or p.endswith(os.sep + "_archives"):
            continue
        yield p


def submodule_dirs(repo_root):
    """Return absolute paths of active git submodules (best-effort)."""
    gitmodules = os.path.join(repo_root, ".gitmodules")
    if not os.path.isfile(gitmodules):
        return []
    subs = []
    try:
        with open(gitmodules, encoding="utf-8") as f:
            for line in f:
                line = line.strip()
                if line.startswith("path"):
                    _, _, rel = line.partition("=")
                    rel = rel.strip()
                    if rel:
                        subs.append(os.path.abspath(os.path.join(repo_root, rel)))
    except OSError:
        pass
    return subs


def main():
    parser = argparse.ArgumentParser(
        description="Detect SVG decimal-comma rendering defects in notebook outputs"
    )
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--scan", metavar="PATH",
                       help="dry-run scan a file or dir; list decimal-comma defects")
    group.add_argument("--scan-all", action="store_true",
                       help="dry-run scan repo-wide")
    group.add_argument("--apply", metavar="PATH",
                       help="guide only (NO-OP): the durable fix is source-level "
                            "(replace :F* with InvariantCulture) + re-exec; there is "
                            "no honest output-only patch")
    group.add_argument("--apply-all", action="store_true",
                       help="guide only repo-wide (NO-OP, see --apply)")
    parser.add_argument("--check", action="store_true",
                        help="with --scan-all: exit 1 if any defect found")
    parser.add_argument("--exclude-submodules", action="store_true",
                        help="skip notebooks inside git submodules (main-repo only; "
                             "used by the CI guard so it stays green while a submodule "
                             "residual is tracked in its own repo)")
    args = parser.parse_args()

    repo_root = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    nb_root = os.path.join(repo_root, "MyIA.AI.Notebooks")

    do_apply = args.apply is not None or args.apply_all
    target = args.apply if args.apply else (args.scan if args.scan else nb_root)

    paths = []
    if args.scan_all or args.apply_all:
        paths = list(iter_notebooks(nb_root))
    elif os.path.isdir(target):
        paths = list(iter_notebooks(target))
    elif os.path.isfile(target):
        paths = [target]
    else:
        parser.error("path not found: %s" % target)

    if args.exclude_submodules:
        subs = submodule_dirs(repo_root)
        if subs:
            before = len(paths)
            paths = [p for p in paths
                     if not any(os.path.abspath(p).startswith(s + os.sep) for s in subs)]
            excluded = before - len(paths)
            if excluded:
                print("(excluded %d notebook(s) inside %d submodule(s))"
                      % (excluded, len(subs)))

    total_files = 0
    total_defects = 0
    files_with_defect = 0
    for p in sorted(paths):
        found = scan_notebook(p)
        if not found:
            continue
        total_files += 1
        files_with_defect += 1
        rel = os.path.relpath(p, repo_root)
        n = sum(len(d) for _, d in found)
        total_defects += n
        if do_apply:
            # Source-level fix guidance (no output patch -- Stop & Repair).
            print("[GUIDE] %s  (%d defect(s) -- source fix: replace :F* with" % (rel, n))
            print("         string F(double v) => v.ToString(\"0.###\", CultureInfo.InvariantCulture);")
            print("         then re-exec the cell. See #6946 / #6960.)")
        else:
            print("[DEFECT] %s  (%d defect(s))" % (rel, n))
            for ci, defects_list in found:
                for d in defects_list[:3]:  # cap per-cell noise
                    print("    cell[%d]: %s" % (ci, d))

    mode = "apply" if do_apply else "scan"
    print("\n%s summary: %d notebook(s) carrying %d SVG decimal-comma defect(s)"
          % (mode, files_with_defect, total_defects))
    if do_apply:
        print("  (apply is a NO-OP guide: the durable fix is source-level + re-exec, "
              "not an output patch)")

    if args.check and total_defects > 0:
        sys.exit(1)


if __name__ == "__main__":
    main()
