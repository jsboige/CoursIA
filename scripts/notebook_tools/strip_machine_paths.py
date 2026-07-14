#!/usr/bin/env python3
"""Strip the .NET Interactive ``Loading extensions from <NuGet cache>`` artifact
from notebooks.

When ``dotnet-interactive`` (the .NET kernel) processes a ``#r "nuget:..."``
cell that ships an **interactive extension**, it injects a ``display_data``
output whose ``data["text/plain"]`` is a single line such as::

    Loading extensions from `C:\\Users\\<user>\\.nuget\\packages\\skiasharp\\2.88.9\\interactive-extensions\\dotnet\\SkiaSharp.DotNet.Interactive.dll`

The backtick-delimited path is the worker's **local NuGet package cache**, which
embeds the machine username (``C:\\Users\\<user>\\``) — a PII-lite leak on a
public repo (the username is the maintainer's GitHub handle / prof identity,
correlable but not a rotatable secret, cf. ``#6443`` / ``#6529``). The message is
**dead noise in a static notebook**: it only matters inside a live kernel
session (it confirms an extension loaded), and it is **re-injected at every
kernel re-execution** — so, exactly like the ``probeAddresses`` banner (cf.
``strip_probe_banner.py``, ``#6309``), re-exec does NOT fix it. The durable fix
is to make the leak **un-committable** via this pre-commit hook.

This is the **category-A (kernel-injected / env-dependent)** leak family of
rule-6 (``secrets-hygiene.md``): the username comes from the worker's
``%USERPROFILE%``, not from source code. Contrast with category-C
(source-leak), which must be fixed at the source. This hook is the sanctioned
durable approach for category-A kernel-injected leaks (cf. ``strip_probe_banner.py``
post-mortem).

The strip is **output-only** — no source code is touched, ``execution_count``
is preserved, the surrounding ``outputs: [...]`` shape is unchanged. Same
surgical philosophy as ``strip_probe_banner.py`` / ``scrub_papermill_paths.py``:
a text-level edit on the on-disk JSON so the rest of the file is byte-identical
(no JSON re-serialization, no float coercion, no metadata churn).

Scope (this hook): the ``Loading extensions from`` NuGet-cache message only.
The other username-path patterns catalogued in ``#6529`` (HuggingFace-cache
download warnings, pip ``AppData`` tracebacks, conda env paths) are Python-side
and multi-line; they are tracked for follow-up hooks. See ``gh issue view 6529``.

Usage:
    python strip_machine_paths.py --scan <path>      # dry-run, list only
    python strip_machine_paths.py --scan-all         # dry-run repo-wide
    python strip_machine_paths.py --scan-all --check # exit 1 if defects found
    python strip_machine_paths.py --apply <path>     # fix in place
    python strip_machine_paths.py --apply-all        # fix repo-wide
"""

import argparse
import glob
import json
import os
import re
import sys


# Distinctive substrings of the dotnet-interactive extension-load messages.
# ``dotnet-interactive`` emits TWO kernel-injected messages carrying the same
# ``C:\Users\<user>\.nuget\packages\...dll`` local NuGet-cache path:
#   (1) success: ``Loading extensions from `<local-path>```
#   (2) failure: ``Failed to load kernel extension "..." from assembly <path>``
# Both are injected at ``#r "nuget:..."`` (not printed by notebook source) and
# re-inject on every re-exec, so both signatures are matched. Each is specific
# to the ``#r "nuget:..."`` interactive-extension load (verified on .NET notebooks
# produced by dotnet-interactive 1.0.x — 8/8 occurrences across 53 username-leaking
# notebooks carry a user-profile path, 0 false positives).
EXT_LOAD_SIGNATURES = ("Loading extensions from", "Failed to load kernel extension")

# Backward-compat alias (legacy single-signature name kept for existing callers).
EXT_LOAD_SIGNATURE = EXT_LOAD_SIGNATURES[0]

# A line is flagged as a leak only if it carries BOTH the signature AND a
# user-profile / NuGet-cache path token. The path token requirement is the
# FP guard: a hypothetical "Loading extensions from <relative-path>" without
# a user-profile segment would not be a username leak and is left untouched.
USER_PATH_TOKENS = (".nuget", "Users\\", "Users/", "/home/", "AppData\\")

# The kernel injects the message in ``data["text/plain"]`` (observed shape).
# ``text/html`` is scanned too for robustness (future kernel versions may emit
# it there), matching ``strip_probe_banner.py``'s defensive dual-scan.
DATA_KEYS = ("text/plain", "text/html")


def _has_leak(text):
    """Return True if ``text`` (a str, or one element of a list) carries the
    extension-load leak (success or failure variant)."""
    if not isinstance(text, str):
        return False
    if not any(sig in text for sig in EXT_LOAD_SIGNATURES):
        return False
    return any(tok in text for tok in USER_PATH_TOKENS)


def _output_has_leak(blob):
    """Return True if any element of a ``data[*]`` value (list or str) leaks."""
    if isinstance(blob, list):
        return any(_has_leak(el) for el in blob)
    return _has_leak(blob)


def count_leak_lines(nb_path):
    """Count leak-bearing list elements / string outputs across the notebook.

    Semantic is **distinct leak-bearing elements** (one per line for list-form,
    one per string output for string-form), aligned with what the strip removes.
    """
    try:
        with open(nb_path, encoding="utf-8") as f:
            nb = json.load(f)
    except (OSError, json.JSONDecodeError):
        return 0
    n = 0
    for cell in nb.get("cells", []):
        if cell.get("cell_type") != "code":
            continue
        for out in cell.get("outputs", []):
            data = out.get("data", {})
            if not isinstance(data, dict):
                continue
            for key in DATA_KEYS:
                v = data.get(key)
                if isinstance(v, list):
                    n += sum(1 for el in v if _has_leak(el))
                elif _has_leak(v):
                    n += 1
    return n


def find_leak_outputs(nb_path):
    """Return list of ``(cell_index, output_index, data_key)`` for leak outputs."""
    try:
        with open(nb_path, encoding="utf-8") as f:
            nb = json.load(f)
    except (OSError, json.JSONDecodeError):
        return []
    hits = []
    for ci, cell in enumerate(nb.get("cells", [])):
        if cell.get("cell_type") != "code":
            continue
        for oi, out in enumerate(cell.get("outputs", [])):
            data = out.get("data", {})
            if not isinstance(data, dict):
                continue
            for key in DATA_KEYS:
                if _output_has_leak(data.get(key)):
                    hits.append((ci, oi, key))
    return hits


def _find_data_list_bounds(raw, key):
    """Return list of ``(body_start, body_end)`` for each ``"<key>": [...]``
    block in ``raw`` notebook JSON (JSON-string-aware bracket balancing).

    Mirrors ``strip_probe_banner.py._find_text_html_list_bounds`` but
    parameterized on the data key. ``body_start`` is the offset right after
    the opening ``[``, ``body_end`` is the closing ``]`` (exclusive).

    JSON-string-awareness is essential: ``]`` inside a JSON string literal
    (e.g. a path with a bracket, or a JS array literal the kernel may embed)
    must not prematurely close the list.
    """
    blocks = []
    head_pat = re.compile(r'"' + re.escape(key) + r'"\s*:\s*\[')
    for head in head_pat.finditer(raw):
        body_start = head.end()
        depth = 1
        i = body_start
        in_string = False
        escape_next = False
        while i < len(raw):
            ch = raw[i]
            if escape_next:
                escape_next = False
                i += 1
                continue
            if in_string:
                if ch == "\\":
                    escape_next = True
                elif ch == '"':
                    in_string = False
                i += 1
                continue
            if ch == '"':
                in_string = True
                i += 1
                continue
            if ch == "[":
                depth += 1
            elif ch == "]":
                depth -= 1
                if depth == 0:
                    blocks.append((body_start, i))
                    break
            i += 1
    return blocks


def strip_in_place(nb_path):
    """Remove leak-bearing ``data[*]`` outputs by editing the on-disk JSON.

    Surgical text-level edit preserving every other byte (no JSON
    re-serialization, no metadata churn). Handles both on-disk shapes:

    1. **list[str]** (the observed shape for ``text/plain``): each
       leak-bearing element is dropped in place, the list shape ``[...]`` is
       preserved (if it becomes a single-element drop, the element content is
       replaced by ``""`` to keep a valid list value).
    2. **str** (inline string): the whole string is replaced by ``""``.

    Returns ``(outputs_with_leak, lines_fixed)``.
    """
    hits = find_leak_outputs(nb_path)
    if not hits:
        return (0, 0)

    with open(nb_path, encoding="utf-8") as f:
        text = f.read()

    try:
        with open(nb_path, encoding="utf-8") as f:
            nb = json.load(f)
    except (OSError, json.JSONDecodeError):
        return (len(hits), 0)

    new_text = text
    fixed = 0
    str_pat = re.compile(r'"((?:text/plain|text/html))"\s*:\s*"((?:[^"\\]|\\.)*)"')
    elem_pat = re.compile(r'"((?:[^"\\]|\\.)*)"')

    # --- String-form: replace the whole "<key>": "<...>" with "<key>": "" ---
    # Collect (key, leak_string) targets from the parsed notebook.
    str_targets = []
    for ci, oi, key in hits:
        try:
            cell = nb["cells"][ci]
        except (IndexError, KeyError):
            continue
        outs = cell.get("outputs", [])
        if oi >= len(outs):
            continue
        v = outs[oi].get("data", {}).get(key)
        if isinstance(v, str) and _has_leak(v):
            str_targets.append((key, v))

    for key, leak_str in reversed(str_targets):
        for m in list(str_pat.finditer(new_text)):
            if m.group(1) != key:
                continue
            raw_value = m.group(2)
            try:
                decoded = json.loads('"' + raw_value + '"')
            except json.JSONDecodeError:
                continue
            if decoded == leak_str:
                replacement = '"%s": ""' % key
                new_text = new_text[:m.start()] + replacement + new_text[m.end():]
                fixed += 1
                break

    # --- List-form: drop leak-bearing elements (+ trailing/preceding comma) ---
    for key in DATA_KEYS:
        blocks = _find_data_list_bounds(new_text, key)
        # Filter to blocks that contain at least one leak-bearing element.
        leak_blocks = []
        for body_start, body_end in blocks:
            body = new_text[body_start:body_end]
            for em in elem_pat.finditer(body):
                try:
                    decoded = json.loads('"' + em.group(1) + '"')
                except json.JSONDecodeError:
                    continue
                if _has_leak(decoded):
                    leak_blocks.append((body_start, body_end))
                    break
        # Process in REVERSE file-offset order so earlier offsets stay valid.
        for body_start, body_end in reversed(leak_blocks):
            body = new_text[body_start:body_end]
            elems = list(elem_pat.finditer(body))
            if not elems:
                continue
            drop_spans = []  # (start, end, mode)
            replaced_here = 0
            for em in elems:
                try:
                    decoded = json.loads('"' + em.group(1) + '"')
                except json.JSONDecodeError:
                    continue
                if not _has_leak(decoded):
                    continue
                replaced_here += 1
                after = em.end()
                tail_match = re.match(r'\s*,', body[after:])
                if tail_match:
                    drop_spans.append((em.start(), after + tail_match.end(), "trail"))
                else:
                    before = em.start()
                    pre_match = re.search(r',\s*$', body[:before])
                    if pre_match:
                        drop_spans.append((pre_match.start(), em.end(), "head"))
                    else:
                        drop_spans.append((em.start(), em.end(), "only"))
            if not replaced_here:
                continue
            if len(drop_spans) == 1 and drop_spans[0][2] == "only":
                new_body = '""'
            else:
                parts = []
                prev_end = 0
                for ds, de, _mode in drop_spans:
                    parts.append(body[prev_end:ds])
                    prev_end = de
                parts.append(body[prev_end:])
                new_body = "".join(parts)
            if new_body != body:
                new_text = new_text[:body_start] + new_body + new_text[body_end:]
                fixed += replaced_here

    if new_text != text:
        with open(nb_path, "w", encoding="utf-8", newline="") as f:
            f.write(new_text)

    return (len(hits), fixed)


def iter_notebooks(nb_root):
    for path in glob.glob(os.path.join(nb_root, "**", "*.ipynb"), recursive=True):
        if "_output" in os.path.basename(path) or "_executed" in os.path.basename(path):
            continue
        yield path


def main():
    parser = argparse.ArgumentParser(
        description="Strip the .NET 'Loading extensions from <NuGet cache>' "
                    "machine-username leak from notebooks"
    )
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--scan", metavar="PATH",
                       help="dry-run scan a file or dir; list leak outputs")
    group.add_argument("--scan-all", action="store_true",
                       help="dry-run scan repo-wide")
    group.add_argument("--apply", metavar="PATH",
                       help="fix a file in place (strip leaks)")
    group.add_argument("--apply-all", action="store_true",
                       help="fix repo-wide in place")
    parser.add_argument("--check", action="store_true",
                        help="with --scan-all: exit 1 if any leak found")
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

    total_files = 0
    total_found = 0
    total_fixed = 0
    skipped = []
    for p in sorted(paths):
        found = count_leak_lines(p)
        fixed = 0
        if do_apply and found:
            fixed = strip_in_place(p)[1]
        if not found:
            continue
        total_files += 1
        total_found += found
        total_fixed += fixed
        rel = os.path.relpath(p, repo_root)
        if do_apply:
            tag = "FIXED" if fixed == found else ("PARTIAL" if fixed else "SKIP")
            print("[%s] %s  (%d leak line(s), %d fixed)" % (tag, rel, found, fixed))
            if fixed < found:
                skipped.append(rel)
        else:
            print("[DEFECT] %s  (%d leak line(s))" % (rel, found))

    mode = "apply" if do_apply else "scan"
    print("\n%s summary: %d notebook(s) carrying %d NuGet-ext leak line(s)"
          % (mode, total_files, total_found))
    if do_apply:
        print("  fixed: %d   skipped: %d file(s)" % (total_fixed, len(skipped)))
        for rel in skipped:
            print("    [unfixed] %s" % rel)

    if args.check and total_found > 0:
        sys.exit(1)


if __name__ == "__main__":
    main()
