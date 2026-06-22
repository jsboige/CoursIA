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

A second, related defect class is covered by ``--outputs``: machine-local
absolute paths that leak *inside output text* (stdout/stderr streams and
text/plain data). These come from non-deterministic environment noise that
re-execution cannot fix because it regenerates a fresh leak each run:

  - ipykernel temp paths in matplotlib UserWarnings
    (``C:\\Users\\<user>\\AppData\\Local\\Temp\\ipykernel_<PID>\\<hash>.py:line``)
  - pip ``already satisfied: ... in C:\\Users\\<user>\\AppData\\Local\\Packages`` lines
  - .NET Interactive ``Loading extensions from C:\\Users\\<user>\\.nuget\\packages`` lines
  - tempfile paths in user messages (``CSV cree: C:\\Users\\<user>\\...\\Temp\\tmpXXXX``)

These leak the contributor's home directory and are non-portable. The
``--outputs`` mode anonymizes only the machine-local *prefix* (home dir ->
``~``, process PID -> ``<pid>``, temp file id -> ``<tmpid>``) while keeping
the rest of the path, which carries diagnostic/pedagogical value. The edit is
text-level (string replace on the on-disk JSON) so cell structure is preserved.

Usage:
    python scrub_papermill_paths.py --scan <path>      # dry-run, list only
    python scrub_papermill_paths.py --scan-all          # dry-run repo-wide
    python scrub_papermill_paths.py --scan-all --check  # exit 1 if defects
    python scrub_papermill_paths.py --apply <path>      # fix in place
    python scrub_papermill_paths.py --apply-all         # fix repo-wide

    # output-path leaks (ipykernel/nuget/pip/temp inside output text):
    python scrub_papermill_paths.py --scan <path> --outputs
    python scrub_papermill_paths.py --apply <path> --outputs
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
        # Match the JSON substring as it appears on disk. The value is a JSON
        # string literal; Jupyter/papermill may store non-ASCII characters
        # either literally (ensure_ascii=False) or escaped as \uXXXX
        # (ensure_ascii=True). Build both candidate needles and use whichever
        # occurs exactly once in the file. For pure-ASCII values both encodings
        # are identical, so this is a no-op vs. the previous single-needle form.
        candidates = []
        seen = set()
        for ensure_ascii in (False, True):
            raw_old = json.dumps(old_val, ensure_ascii=ensure_ascii)
            raw_new = json.dumps(basename, ensure_ascii=ensure_ascii)
            needle = '"%s": %s' % (key, raw_old)
            if needle in seen:
                continue
            seen.add(needle)
            candidates.append((needle, '"%s": %s' % (key, raw_new)))
        # Keep only needles that occur exactly once: count==0 means the on-disk
        # literal differs (quote/spacing); count>1 is ambiguous (same path
        # twice). Both are skipped to stay surgical.
        matches = [(n, r) for (n, r) in candidates if new_text.count(n) == 1]
        if len(matches) != 1:
            continue
        needle, replacement = matches[0]
        new_text = new_text.replace(needle, replacement, 1)
        fixed.append((key, old_val))

    if apply and fixed and new_text != text:
        with open(nb_path, "w", encoding="utf-8", newline="") as f:
            f.write(new_text)

    return (defects, fixed)


# ---------------------------------------------------------------------------
# Output-path leaks (--outputs mode)
# ---------------------------------------------------------------------------

# Machine-local home-directory prefixes. We anonymize the *home root* (user
# name) and keep the rest of the path. Backslash form (Windows) and forward
# slash form both appear in committed notebooks. Separators use [\\/]+ (one or
# more) rather than a single [\\/] so repr-doubled backslashes are matched too:
# Python formats paths inside exception messages via repr(), so FileNotFoundError
# / PermissionError etc. carry 'C:\\Users\\<user>' (two literal backslashes) not
# 'C:\Users\<user>'. A single-separator regex misses those entirely (regression:
# archive Fast-Downward-Legacy #3891, where traceback frames scrubbed but the
# final exception line did not).
_HOME_RES = [
    # Windows drive home: C:\Users\<user> or C:/Users/<user>  (single capture -> ~)
    re.compile(r"[A-Za-z]:[\\/]+(?:Users|home)[\\/]+[^\\/]+"),
    # POSIX-style home root as written by some MSYS/git-bash tools: /c/Users/<user>
    re.compile(r"/[a-zA-Z]/(?:Users|home)/[^/]+"),
]

# Checkout-root prefixes: a drive-absolute path into the repo checkout (any
# clone location, e.g. D:\dev\CoursIA-2\ or C:\dev\CoursIA\). Anonymized to
# <repo>; the repo-relative tail stays informative. This is distinct from the
# home root (no Users/home segment) so the home regexes never match it, and it
# needs its own pattern (regression: #3892 D:\dev\CoursIA-2\ leak flagged by
# ai-01). The drive prefix makes it specific to machine-local absolute paths, so
# a relative discussion ("the CoursIA repo") or a URL is never touched.
_REPO_RES = [
    # Negative lookbehind (?<![a-zA-Z]) forbids a letter before the drive letter,
    # so the 'e:' inside a 'file:' URL scheme (where 'e' is preceded by 'l') is
    # never matched, nor the 'p:' in 'http:'. Only a real drive letter preceded by
    # a separator (e.g. the 'D:' in 'file:///D:/dev/CoursIA/...', preceded by '/')
    # matches, so the URL scheme is preserved while the checkout-root path is
    # anonymized. Regression: SW-8 '<file:///D:/dev/CoursIA/...>' was mangled into
    # '<fil<repo>...>' because 'e:///D:/dev/CoursIA/' matched (PR #3899, caught
    # pre-commit by diff inspection).
    re.compile(r"(?<![a-zA-Z])[A-Za-z]:[\\/]+(?:[^\\/'\"<>|]+[\\/]+)*CoursIA(?:-2)?[\\/]+"),
]

# Process/file-specific ids that sit *inside* a home-relative temp path. These
# change every run (PID, temp file id), so scrubbing them keeps the output
# stable across re-executions. Applied after home -> ~ normalization.
_IPYKERNEL_PID = re.compile(r"(ipykernel_)\d+")
_CLAUDE_IPYKERNEL_PID = re.compile(r"(/Temp/claude/ipykernel_)\d+")
_TEMP_FILE_ID = re.compile(r"(/Temp/tmp)[A-Za-z0-9_\-]+")


def _scrub_output_text(text):
    """Anonymize machine-local path prefixes in a single output string.

    Returns ``(scrubbed_text, changed_bool)``. Only the home root and
    process/temp ids are replaced; the rest of the path is preserved.
    """
    if not isinstance(text, str):
        return text, False
    orig = text
    for pat in _HOME_RES:
        text = pat.sub("~", text)
    for pat in _REPO_RES:
        text = pat.sub("<repo>", text)
    text = _IPYKERNEL_PID.sub(lambda m: m.group(1) + "<pid>", text)
    text = _CLAUDE_IPYKERNEL_PID.sub(lambda m: m.group(1) + "<pid>", text)
    text = _TEMP_FILE_ID.sub(lambda m: m.group(1) + "<tmpid>", text)
    return text, (text != orig)


def find_output_path_defects(nb_path):
    """Return count of machine-local path leaks found in output text.

    Inspects ``outputs[].text`` (stream) and ``outputs[].data["text/plain"]``
    of every code cell. Returns the total occurrence count (0 if clean).
    """
    nb = _read_notebook(nb_path)
    if nb is None:
        return 0
    count = 0
    for cell in nb.get("cells", []):
        if cell.get("cell_type") != "code":
            continue
        for out in cell.get("outputs", []):
            text = out.get("text", "")
            if isinstance(text, list):
                text = "".join(text)
            _, c = _scrub_output_text(text)
            if c:
                count += 1
            data = out.get("data", {})
            if isinstance(data, dict):
                tp = data.get("text/plain", "")
                if isinstance(tp, list):
                    tp = "".join(tp)
                _, c = _scrub_output_text(tp)
                if c:
                    count += 1
    return count


def scrub_output_paths(nb_path, apply=False):
    """Anonymize machine-local path prefixes in output text, in place.

    Uses a text-level surgical edit: collect the distinct machine-local
    *home-root substrings* that appear in any code-cell output (stream text
    or text/plain data), then replace each one directly on the on-disk JSON
    with ``~``. Process/temp ids (ipykernel PID, temp file id) are scrubbed
    the same way. This preserves cell structure, source, and all other bytes
    (no JSON re-serialization, no float coercion, no metadata churn).

    Returns ``(leaks_found, leaks_fixed)`` as counts. ``leaks_found`` counts
    output blobs that contained a leak; ``leaks_fixed`` counts distinct
    substrings replaced on disk.
    """
    nb = _read_notebook(nb_path)
    if nb is None:
        return (0, 0)

    # Collect every distinct home-root + process-id substring that appears in
    # outputs. These are the exact needles we will replace on the raw text.
    needles = set()
    leaks_found = 0
    for cell in nb.get("cells", []):
        if cell.get("cell_type") != "code":
            continue
        for out in cell.get("outputs", []):
            blobs = []
            t = out.get("text", "")
            if isinstance(t, list):
                t = "".join(t)
            blobs.append(t)
            data = out.get("data", {})
            if isinstance(data, dict):
                tp = data.get("text/plain", "")
                if isinstance(tp, list):
                    tp = "".join(tp)
                blobs.append(tp)
            for blob in blobs:
                scrubbed, changed = _scrub_output_text(blob)
                if not changed:
                    continue
                leaks_found += 1
                # Recover the distinct literal substrings this blob contributed
                # by diffing original vs scrubbed char-by-char is overkill; the
                # home-root and id patterns are few and unambiguous, so record
                # the matched spans directly.
                for pat in _HOME_RES:
                    for m in pat.finditer(blob):
                        needles.add(m.group(0))
                for pat in _REPO_RES:
                    for m in pat.finditer(blob):
                        needles.add(m.group(0))
                for m in _IPYKERNEL_PID.finditer(blob):
                    needles.add(m.group(0))
                for m in _CLAUDE_IPYKERNEL_PID.finditer(blob):
                    needles.add(m.group(0))
                for m in _TEMP_FILE_ID.finditer(blob):
                    needles.add(m.group(0))

    if not needles:
        return (0, 0)

    with open(nb_path, encoding="utf-8") as f:
        text = f.read()

    new_text = text
    fixed = 0
    for needle in sorted(needles, key=len, reverse=True):
        # Determine the replacement for this needle.
        if needle.startswith("ipykernel_"):
            repl = "ipykernel_<pid>"
        elif "/Temp/claude/ipykernel_" in needle:
            repl = needle[:needle.rfind("ipykernel_")] + "ipykernel_<pid>"
        elif "/Temp/tmp" in needle:
            repl = needle[:needle.find("/Temp/tmp") + len("/Temp/tmp")] + "<tmpid>"
        elif any(pat.search(needle) for pat in _REPO_RES):
            # Checkout-root: anonymize the repo clone prefix to <repo>
            repl = "<repo>"
        else:
            # Home root: anonymize to ~
            repl = "~"
        # The on-disk JSON may encode backslashes doubled; also try the raw
        # form. Replace every occurrence of whichever form is present.
        candidates = {needle, needle.replace("\\", "\\\\")}
        replaced = False
        for cand in candidates:
            if cand and cand in new_text:
                new_text = new_text.replace(cand, repl)
                replaced = True
        if replaced:
            fixed += 1

    if apply and new_text != text:
        with open(nb_path, "w", encoding="utf-8", newline="") as f:
            f.write(new_text)

    return (leaks_found, fixed)


def iter_notebooks(nb_root):
    for path in glob.glob(os.path.join(nb_root, "**", "*.ipynb"), recursive=True):
        if "_output" in os.path.basename(path) or "_executed" in os.path.basename(path):
            continue
        yield path


def main():
    parser = argparse.ArgumentParser(
        description="Scrub absolute machine-local paths from notebooks"
    )
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--scan", metavar="PATH", help="dry-run scan a file or dir")
    group.add_argument("--scan-all", action="store_true", help="dry-run scan repo-wide")
    group.add_argument("--apply", metavar="PATH", help="fix a file or dir in place")
    group.add_argument("--apply-all", action="store_true", help="fix repo-wide in place")
    parser.add_argument("--outputs", action="store_true",
                        help="scrub machine-local paths in OUTPUT text "
                             "(ipykernel/nuget/pip/temp leaks) instead of papermill metadata")
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
        if args.outputs:
            found, fixed = scrub_output_paths(p, apply=do_apply)
            defects = found  # count of leaked output blobs
            if not found:
                continue
            files_with_defect += 1
            total_defects += found
            total_fixed += fixed
            rel = os.path.relpath(p, repo_root)
            tag = "FIXED" if do_apply and fixed else ("DEFECT" if not do_apply else "PARTIAL")
            print("[%s] %s  (%d output leak(s)%s)" % (
                tag, rel, found, ", %d fixed" % fixed if do_apply else ""))
            continue

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
    what = "output path leak(s)" if args.outputs else "absolute papermill path(s)"
    print("\n%s summary: %d notebook(s) with %d %s"
          % (mode, files_with_defect, total_defects, what))
    if do_apply:
        print("  fixed: %d   skipped: %d" % (total_fixed, len(skipped)))

    if args.check and total_defects > 0:
        sys.exit(1)


if __name__ == "__main__":
    main()
