#!/usr/bin/env python3
"""
Scrub absolute machine-local paths from notebook papermill metadata.

When a notebook is re-executed via papermill with an absolute output path
(e.g. ``C:/Users/jsboi/AppData/Local/Temp/x.ipynb`` or ``D:/tmp/x.ipynb``),
papermill records that absolute path in ``metadata.papermill.output_path``
(and sometimes ``input_path``). This:

  - leaks the contributor's local directory structure,
  - breaks reproducibility (the temp path no longer exists),
  - is inconsistent with cleanly-executed notebooks (e.g. SC-10), where both
    fields carry the notebook's relative basename.

The target state is a relative path equal to the notebook's own basename.
This script replaces any absolute ``output_path``/``input_path`` value with
the basename, using a text-level surgical edit so the rest of the notebook
(byte-for-byte code, outputs, cell metadata) is preserved.

Usage:
    python scrub_papermill_paths.py --scan <path>      # dry-run, list only
    python scrub_papermill_paths.py --scan-all          # dry-run repo-wide
    python scrub_papermill_paths.py --scan-all --check  # exit 1 if defects
    python scrub_papermill_paths.py --apply <path>      # fix in place
    python scrub_papermill_paths.py --apply-all         # fix repo-wide
"""

import argparse
import glob
import json
import os
import re
import sys

# Matches a Windows drive-absolute path (C:\, C:/, D:\ ...) or a POSIX-absolute
# path (/tmp/...). Forward and back slashes both appear in committed notebooks.
ABS_PATH_RE = re.compile(r'^[A-Za-z]:[\\/]|^/')


def is_absolute(p):
    return isinstance(p, str) and bool(ABS_PATH_RE.match(p))


def _read_notebook(nb_path):
    try:
        with open(nb_path, encoding="utf-8") as f:
            return json.load(f)
    except (OSError, json.JSONDecodeError):
        return None


def find_papermill_defects(nb_path):
    """Return list of (key, current_value) for absolute papermill paths.

    Only inspects ``metadata.papermill``. Returns [] if notebook is not
    papermill-executed or has only relative paths.
    """
    nb = _read_notebook(nb_path)
    if nb is None:
        return []
    pm = nb.get("metadata", {}).get("papermill", {})
    if not isinstance(pm, dict):
        return []
    defects = []
    for key in ("output_path", "input_path"):
        val = pm.get(key)
        if is_absolute(val):
            defects.append((key, val))
    return defects


def scrub_notebook(nb_path, apply=False):
    """Replace absolute papermill paths with the notebook basename.

    Uses a text-level surgical edit (string replace of the exact JSON
    key:value substring) so the rest of the file is byte-identical. No
    JSON re-serialization = no float coercion, no metadata churn.

    Returns (defects_found, defects_fixed).
    """
    defects = find_papermill_defects(nb_path)
    if not defects:
        return ([], [])

    basename = os.path.basename(nb_path)
    with open(nb_path, encoding="utf-8") as f:
        text = f.read()

    fixed = []
    new_text = text
    for key, old_val in defects:
        # Match the JSON substring regardless of quote style / spacing that
        # json.dump may have produced. The value is a JSON string literal:
        # escape backslashes present in the raw file form.
        raw_old = json.dumps(old_val)  # exact JSON string literal as parsed
        raw_new = json.dumps(basename)
        needle = '"%s": %s' % (key, raw_old)
        replacement = '"%s": %s' % (key, raw_new)
        count = new_text.count(needle)
        if count == 0:
            # The on-disk literal differs from the parsed value (e.g. single
            # quotes, spacing). Skip rather than risk a wrong edit.
            continue
        if count > 1:
            # Ambiguous: the same absolute path appears twice. Skip to stay
            # surgical; flagged in scan output for manual review.
            continue
        new_text = new_text.replace(needle, replacement, 1)
        fixed.append((key, old_val))

    if apply and fixed and new_text != text:
        with open(nb_path, "w", encoding="utf-8", newline="") as f:
            f.write(new_text)

    return (defects, fixed)


def iter_notebooks(nb_root):
    for path in glob.glob(os.path.join(nb_root, "**", "*.ipynb"), recursive=True):
        if "_output" in os.path.basename(path) or "_executed" in os.path.basename(path):
            continue
        yield path


def main():
    parser = argparse.ArgumentParser(
        description="Scrub absolute paths from notebook papermill metadata"
    )
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--scan", metavar="PATH", help="dry-run scan a file or dir")
    group.add_argument("--scan-all", action="store_true", help="dry-run scan repo-wide")
    group.add_argument("--apply", metavar="PATH", help="fix a file or dir in place")
    group.add_argument("--apply-all", action="store_true", help="fix repo-wide in place")
    parser.add_argument("--check", action="store_true",
                        help="with --scan-all: exit 1 if any defect found")
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

    total_defects = 0
    total_fixed = 0
    files_with_defect = 0
    skipped = []
    for p in sorted(paths):
        defects, fixed = scrub_notebook(p, apply=do_apply)
        if not defects:
            continue
        files_with_defect += 1
        total_defects += len(defects)
        rel = os.path.relpath(p, repo_root)
        if do_apply:
            unfixed = [d for d in defects if d not in fixed]
            total_fixed += len(fixed)
            tag = "FIXED" if fixed and not unfixed else ("PARTIAL" if fixed else "SKIP")
            print("[%s] %s" % (tag, rel))
            for key, val in fixed:
                print("        %s: %s -> %s" % (key, val, os.path.basename(p)))
            for key, val in unfixed:
                print("        [unfixed] %s: %s" % (key, val))
                skipped.append((rel, key, val))
        else:
            print("[DEFECT] %s" % rel)
            for key, val in defects:
                print("        %s: %s" % (key, val))

    mode = "apply" if do_apply else "scan"
    print("\n%s summary: %d notebook(s) with %d absolute papermill path(s)"
          % (mode, files_with_defect, total_defects))
    if do_apply:
        print("  fixed: %d   skipped: %d" % (total_fixed, len(skipped)))

    if args.check and total_defects > 0:
        sys.exit(1)


if __name__ == "__main__":
    main()
