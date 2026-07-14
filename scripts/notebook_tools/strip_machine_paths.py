#!/usr/bin/env python3
"""Strip machine-username path leaks from notebook cell outputs.

Several runtimes — the .NET Interactive kernel, CPython's import machinery,
ipykernel, HuggingFace libraries — emit warnings / messages in cell outputs
that embed the worker's **local cache path**, which carries the machine
username (``C:\\Users\\<user>\\``). On a public repo the username is the
maintainer's GitHub handle / prof identity, correlable but not a rotatable
secret (cf. ``#6443`` / ``#6529``). The messages are **dead noise in a static
notebook**: they only matter inside a live kernel session (they confirm /
warn about a load), and they are **re-injected at every kernel re-execution**
— so, exactly like the ``probeAddresses`` banner (cf. ``strip_probe_banner.py``,
``#6309``), re-exec does NOT fix them. The durable fix is to make the leaks
**un-committable** via this pre-commit hook.

This is the **category-A (kernel-injected / env-dependent)** leak family of
rule-6 (``secrets-hygiene.md``): the username comes from the worker's
``%USERPROFILE%``, not from source code. Contrast with category-C
(source-leak), which must be fixed at the source. This hook is the sanctioned
durable approach for category-A kernel-injected leaks (cf. ``strip_probe_banner.py``
post-mortem).

## Leak categories covered

| Label       | Token (cache-context marker)                            | Source                                              |
|-------------|---------------------------------------------------------|-----------------------------------------------------|
| ``nuget``   | ``.nuget``                                              | ``dotnet-interactive`` ext-load messages (#6537)    |
| ``pip``     | ``AppData\\Roaming\\Python`` / ``AppData\\Local\\pip``  | CPython pip-import warnings (peft/torch/...)        |
| ``ipykernel`` | ``AppData\\Local\\Temp\\ipykernel``                   | ipykernel temp-file deprecation warnings            |
| ``conda``   | ``.conda\\envs``                                        | conda-env import warnings (deprecated nn.utils...)  |
| ``hfcache`` | ``.cache\\huggingface``                                 | HF transformers / datasets download warnings        |

Each token is path-relative (no leading ``C:\\Users\\<u>\\``) and is keyed
alongside the username markers (``Users\\``, ``Users/``, ``/home/``): a line
is a leak iff it embeds BOTH a cache-context token AND a real machine
username. The **tilde** variant (``~\.nuget\packages\...``, the
``%USERPROFILE%`` HOME *placeholder*) carries no username and is correctly
left untouched (no PII).

**Detection is path-based, not signature-based.** Keying on the username path
(rather than the message prefix) catches both kernel messages uniformly per
category and is robust to future message rewording (cf. ``#6537`` review: the
v1 hook keyed on ``Loading extensions from`` and both missed the ``stream``
``Failed to load`` variant AND false-positive stripped legitimate tilde
``Loading extensions from`` lines).

The strip is **output-only** — no source code is touched, ``execution_count``
is preserved, the surrounding ``outputs: [...]`` shape is unchanged. Same
surgical philosophy as ``strip_probe_banner.py`` / ``scrub_papermill_paths.py``:
a text-level edit on the on-disk JSON so the rest of the file is byte-identical
(no JSON re-serialization, no float coercion, no metadata churn).

Usage:
    python strip_machine_paths.py --scan <path>      # dry-run, list only
    python strip_machine_paths.py --scan-all         # dry-run repo-wide
    python strip_machine_paths.py --scan-all --check # exit 1 if defects found
    python strip_machine_paths.py --apply <path>     # fix in place
    python strip_machine_paths.py --apply-all        # fix repo-wide
    python strip_machine_paths.py --scan-all --category nuget   # filter
    python strip_machine_paths.py --scan-all --category pip      # filter
"""

import argparse
import glob
import json
import os
import re
import sys


# Detection is **path-based, multi-category**. A line is a leak iff it
# references ANY of the runtime-specific cache-context tokens below AND
# embeds a real machine username. Each ``(label, token)`` pair maps to one
# category — see the docstring for which kernel/runtime emits what.
#
# Tokens are path-relative (no leading ``C:\\Users\\<u>\\``); the username-
# marker check rules out the dotnet-interactive **tilde** variant
# (``~\.nuget\packages\...``), the ``%USERPROFILE%`` HOME *placeholder*, which
# carries NO username and is correctly left untouched.
CACHE_TOKENS = (
    ("nuget",     ".nuget"),
    ("pip",       "AppData\\Roaming\\Python"),
    ("ipykernel", "AppData\\Local\\Temp\\ipykernel"),
    ("conda",     ".conda\\envs"),
    ("hfcache",   ".cache\\huggingface"),
)

# Username-bearing absolute-path markers — the actual PII payload. The
# dotnet-interactive **tilde** variant is the ``%USERPROFILE%`` HOME
# *placeholder* and carries NONE of these, so it is correctly left
# untouched (no username = no leak).
USERNAME_MARKERS = ("Users\\", "Users/", "/home/")

# Output fields that can carry the leak:
# - ``data["text/plain"]`` / ``data["text/html"]`` for ``display_data`` /
#   ``execute_result`` outputs (the ``Loading extensions from`` message).
# - top-level ``text`` for ``stream`` outputs (the ``Failed to load kernel
#   extension ... from assembly`` message lives in stderr ``text``).
DATA_KEYS = ("text/plain", "text/html")
STREAM_KEY = "text"
ALL_KEYS = DATA_KEYS + (STREAM_KEY,)

# Module-level mutable, set by ``main()`` from CLI. ``None`` == ALL categories.
ACTIVE_CATEGORIES = None


def _iter_tokens():
    """Yield ``(label, token)`` for each active category (respects CLI filter)."""
    if ACTIVE_CATEGORIES is None:
        return list(CACHE_TOKENS)
    return [t for t in CACHE_TOKENS if t[0] in ACTIVE_CATEGORIES]


def _has_leak(text):
    """Return True if ``text`` carries a runtime-cache + username leak.

    Path-based: requires BOTH a cache-context token (``.nuget``,
    ``AppData\\Roaming\\Python``, ...) AND a username absolute-path marker
    (``Users\\``, ``Users/``, ``/home/``). The tilde HOME placeholder
    (no username) carries neither marker and is left untouched.
    """
    if not isinstance(text, str):
        return False
    if not any(marker in text for marker in USERNAME_MARKERS):
        return False
    return any(token in text for _label, token in _iter_tokens())


def _field_value(out, key):
    """Return the list/str value of output field ``key``, or None.

    ``data["text/plain"|"text/html"]`` for display_data/execute_result;
    top-level ``text`` for stream outputs. (A bare ``"text"`` key is
    stream-specific in nbformat outputs — display_data nests text under
    ``data``, so there is no collision with ``text/plain``.)
    """
    if key in DATA_KEYS:
        data = out.get("data", {})
        if not isinstance(data, dict):
            return None
        return data.get(key)
    if key == STREAM_KEY:
        return out.get(STREAM_KEY)
    return None


def _output_has_leak(blob):
    """Return True if any element of a field value (list or str) leaks."""
    if isinstance(blob, list):
        return any(_has_leak(el) for el in blob)
    return _has_leak(blob)


def count_leak_lines(nb_path):
    """Count leak-bearing list elements / string outputs across the notebook.

    Semantic is **distinct leak-bearing elements** (one per line for list-form,
    one per string output for string-form), aligned with what the strip removes.
    Scans both ``display_data`` data keys and ``stream`` ``text``.
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
            for key in ALL_KEYS:
                v = _field_value(out, key)
                if isinstance(v, list):
                    n += sum(1 for el in v if _has_leak(el))
                elif _has_leak(v):
                    n += 1
    return n


def find_leak_outputs(nb_path):
    """Return list of ``(cell_index, output_index, field_key)`` for leak outputs.

    ``field_key`` is one of ``text/plain`` / ``text/html`` (display_data /
    execute_result) or ``text`` (stream).
    """
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
            for key in ALL_KEYS:
                if _output_has_leak(_field_value(out, key)):
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
    str_pat = re.compile(r'"((?:text/plain|text/html|text))"\s*:\s*"((?:[^"\\]|\\.)*)"')
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
        v = _field_value(outs[oi], key)
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
    for key in ALL_KEYS:
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
        description="Strip machine-username path leaks from notebook cell "
                    "outputs (NuGet/pip/ipykernel/conda/HF cache categories)."
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
    parser.add_argument("--category", metavar="CAT",
                        choices=[t[0] for t in CACHE_TOKENS] + ["all"],
                        default="all",
                        help="restrict to one category: " +
                             ", ".join(t[0] for t in CACHE_TOKENS) +
                             " (default: all)")
    args = parser.parse_args()

    global ACTIVE_CATEGORIES
    if args.category == "all":
        ACTIVE_CATEGORIES = None
    else:
        ACTIVE_CATEGORIES = {args.category}

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
    cat_label = "all" if ACTIVE_CATEGORIES is None else args.category
    print("\n%s summary (%s categories): %d notebook(s) carrying %d leak line(s)"
          % (mode, cat_label, total_files, total_found))
    if do_apply:
        print("  fixed: %d   skipped: %d file(s)" % (total_fixed, len(skipped)))
        for rel in skipped:
            print("    [unfixed] %s" % rel)

    if args.check and total_found > 0:
        sys.exit(1)


if __name__ == "__main__":
    main()
