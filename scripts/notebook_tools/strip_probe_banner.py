#!/usr/bin/env python3
"""Strip the .NET Interactive ``probeAddresses`` HTTP-bootstrap banner from notebooks.

When ``dotnet-interactive`` (the .NET kernel) executes the first code cell of a
notebook, it injects a ``display_data`` output whose ``data["text/html"]`` is a
``<script>`` that calls ``probeAddresses`` / ``loadDotnetInteractiveApi`` /
``probingAddresses``. The script text embeds the worker's full network interface
list, including:

- host **LAN IPv4** (``192.168.x.x``),
- **WSL/Docker bridge** IPs (``172.x.x.x``),
- **link-local IPv6** (``fe80::...``),
- and the host's **public globally-routable IPv6** (``2a01:e0a:...`` Orange-FR /32,
  ISP + geo, internet-reachable).

On a **public** repo this leaks the maintainer's real internet-facing host
addresses. The banner is dead noise in a static notebook (only acts inside a
live kernel session) — zero pedagogical value.

This is a regression of #2727/#2733 (the original scrub was output-only and
**non-durable**: every kernel re-exec re-injects the banner). See
``gh issue view 6309`` for the full post-mortem (183 notebooks affected at the
time of writing; subsequent firsthand scans show 203 .NET notebooks carrying
the banner). The fix is to make the leak **un-committable** by running this
script as a pre-commit hook so every commit is screened before landing.

The strip is **output-only** — no source code is touched, ``execution_count``
is preserved, the surrounding ``outputs: [...]`` shape is unchanged. This is
the same surgical philosophy as ``scrub_papermill_paths.py``: a text-level edit
on the on-disk JSON so the rest of the file is byte-identical (no JSON
re-serialization, no float coercion, no metadata churn).

Usage:
    python strip_probe_banner.py --scan <path>      # dry-run, list only
    python strip_probe_banner.py --scan-all         # dry-run repo-wide
    python strip_probe_banner.py --scan-all --check # exit 1 if defects found
    python strip_probe_banner.py --apply <path>     # fix in place
    python strip_probe_banner.py --apply-all        # fix repo-wide
"""

import argparse
import glob
import json
import os
import re
import sys


# Distinctive substrings the dotnet-interactive kernel always embeds in the
# probeAddresses banner. ANY of these in ``data["text/html"]`` flags the
# output as the banner (verified on .NET notebooks produced by
# dotnet-interactive 1.0.x — also covers ``probingAddresses`` and the
# ``loadDotnetInteractiveApi`` bootstrap helper the script calls).
BANNER_SIGNATURES = ("probeAddresses", "probingAddresses", "loadDotnetInteractiveApi")


def has_banner(blob):
    """Return True if any banner signature appears in the HTML blob.

    The on-disk format is a ``list[str]`` (one line per element) but a single
    string is also tolerated for robustness.
    """
    if isinstance(blob, list):
        return any(any(sig in line for sig in BANNER_SIGNATURES) for line in blob)
    if isinstance(blob, str):
        return any(sig in blob for sig in BANNER_SIGNATURES)
    return False


def count_banner_lines(nb_path):
    """Count the total banner-bearing list elements across the notebook.

    Each ``text/html`` output can contain multiple lines that embed a banner
    signature (the .NET bootstrap script is multi-line: ``probeAddresses`` is
    on one line, ``loadDotnetInteractiveApi`` on another, etc.). ``find_banner_outputs``
    counts OUTPUTS (one per cell); this counts the number of *distinct*
    banner-bearing list elements (multiple per output) so the strip PASS/FAIL
    decision is meaningful.

    The semantic is **distinct banner-bearing elements**, not **signature
    occurrences** — a single element like
    ``"async function probeAddresses(probingAddresses) {"`` embeds two
    signatures but counts once (matches what the strip removes). Without this
    semantic alignment, `count_banner_lines` and the strip return count
    diverge (3 banner elements vs 9 signature hits on real
    GameTheory-10 notebook), and the ``FIXED == pre`` reporting invariant
    fails.
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
            html = data.get("text/html")
            if isinstance(html, list):
                for line in html:
                    # One banner-bearing list element = +1, regardless of how
                    # many of the 3 signatures it embeds.
                    if any(sig in line for sig in BANNER_SIGNATURES):
                        n += 1
            elif isinstance(html, str):
                if any(sig in html for sig in BANNER_SIGNATURES):
                    n += 1
    return n


def find_banner_outputs(nb_path):
    """Return list of (cell_index, output_index) for banner outputs.

    Only inspects code-cell ``outputs[].data["text/html"]``. Markdown cells and
    other output types (``stream``, ``error``) are never banner targets — the
    kernel only injects ``display_data``.
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
            data = out.get("data", {})
            if not isinstance(data, dict):
                continue
            html = data.get("text/html")
            if has_banner(html):
                hits.append((ci, oi))
    return hits


def _find_text_html_list_bounds(raw):
    """Return list of ``(body_start, body_end)`` for each ``"text/html": [...]``
    block in ``raw`` notebook JSON.

    ``body_start`` is the offset of the first char AFTER the opening ``[``,
    ``body_end`` is the offset of the closing ``]`` (exclusive — so the body
    is ``raw[body_start:body_end]``).

    The scan is **JSON-string-aware**: ``]`` characters appearing inside JSON
    string literals (e.g. a banner element containing a JS array literal
    ``"probeAddresses([\"http://...\"])"``) are NOT treated as list-end
    markers. This is essential because the .NET bootstrap banner embeds an
    inline JS array literal ``probeAddresses(["http://...","http://..."])``
    that would otherwise prematurely close the JSON list-form value.

    Naive regex ``r'"text/html"\\s*:\\s*\\[([^\\]]*)\\]'`` fails on real
    GameTheory-10 notebook because of this — ``[^\\]]*`` stops at the first ``]``
    inside a banner element, truncating the body to ~970 chars and missing
    6 of 9 banner elements.

    Returned bounds are valid against the raw bytes; callers should re-scan
    after each text edit (since the body shifts when banner elements are
    dropped).
    """
    blocks = []
    head_pat = re.compile(r'"text/html"\s*:\s*\[')
    for head in head_pat.finditer(raw):
        body_start = head.end()  # index right after the [
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
            # not in string
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


def strip_banner_in_place(nb_path):
    """Remove banner ``text/html`` outputs by editing the data key on disk.

    Surgical text-level edit preserving every other byte (no JSON
    re-serialization, no float coercion, no metadata churn — same philosophy
    as ``scrub_papermill_paths.py``).

    Two on-disk shapes for ``data["text/html"]`` are handled:

    1. **list[str]** (one HTML line per element, common in older Jupyter /
       nbformat 4): each banner-bearing element is dropped in place via a
       regex rewrite on the raw JSON. The list shape (``[... , ..., ...]``)
       is preserved.

    2. **str** (one inline HTML string, common when the kernel emits a single
       ``<script>...</script>`` block): the whole banner string is replaced
       by ``""`` (empty string) in the on-disk JSON via a targeted text
       rewrite. The empty string is still a valid ``text/html`` data value
       (no display), and the surrounding ``outputs: [...]`` shape is preserved.

    Returns ``(outputs_with_banner, lines_fixed)``. ``lines_fixed`` counts
    banner-bearing JSON list elements rewritten (case 1) or string
    replacements performed (case 2, always 1 per output).
    """
    hits = find_banner_outputs(nb_path)
    if not hits:
        return (0, 0)

    with open(nb_path, encoding="utf-8") as f:
        text = f.read()

    # Build a per-cell per-output picture from the JSON: for each hit, decide
    # whether the data["text/html"] is a string (case 2 — easy: replace the
    # whole string with "") or a list (case 1 — rewrite each banner element).
    try:
        with open(nb_path, encoding="utf-8") as f:
            nb = json.load(f)
    except (OSError, json.JSONDecodeError):
        return (len(hits), 0)

    new_text = text
    fixed = 0
    # String-form: anchor on the JSON substring pattern ``"text/html": "<...>"``.
    str_pat = re.compile(
        r'"text/html"\s*:\s*"((?:[^"\\]|\\.)*)"',
    )
    # List-form: bounds are computed by _find_text_html_list_bounds() (JSON-
    # string-aware bracket-balancing scanner), not by a regex, because banner
    # elements can embed inner ``[...]`` JS array literals (e.g.
    # ``probeAddresses([\"http://...\"]);``) that would prematurely close
    # ``[^\]]*``.

    # First, handle string-form banners by replacing the full string with "".
    # We walk the list of (cell_idx, output_idx) hits in REVERSE order of
    # file offset (so earlier offsets stay valid after each edit).
    str_targets = []  # list of (output_idx_in_file_offset_terms, sigs, full_str)
    # Rebuild (file_offset, full_banner_string) pairs for string-form hits.
    for ci, oi in hits:
        try:
            cell = nb["cells"][ci]
        except (IndexError, KeyError):
            continue
        outs = cell.get("outputs", [])
        if oi >= len(outs):
            continue
        html = outs[oi].get("data", {}).get("text/html")
        if isinstance(html, str) and has_banner(html):
            str_targets.append((ci, oi, html))
        # list-form is handled by the bracket-scanner below; we don't need
        # to rebuild it.

    # Apply string-form replacements first (each one shrinks the file, so we
    # walk from the END of the file backwards to keep earlier offsets valid).
    # We re-search after each edit to get fresh offsets.
    for ci, oi, banner_str in reversed(str_targets):
        for m in list(str_pat.finditer(new_text)):
            raw_value = m.group(1)
            # Decode JSON escape sequences to compare with the parsed string.
            try:
                decoded = json.loads('"' + raw_value + '"')
            except json.JSONDecodeError:
                continue
            if decoded == banner_str:
                # Replace the whole "text/html": "<...>" with "text/html": "".
                new_text = new_text[:m.start()] + '"text/html": ""' + new_text[m.end():]
                fixed += 1
                break

    # Then, handle list-form banners by dropping banner-bearing elements.
    # Process blocks in REVERSE order of file offset so earlier offsets stay
    # valid after each edit (each edit shrinks the file).
    blocks = _find_text_html_list_bounds(new_text)
    # Filter to blocks that correspond to banner outputs (recompute via
    # JSON parse + per-block signature scan, matching find_banner_outputs
    # semantic: any signature-bearing element → block is "banner-bearing").
    banner_block_bounds = []
    elem_pat = re.compile(r'"((?:[^"\\]|\\.)*)"')
    for body_start, body_end in blocks:
        body = new_text[body_start:body_end]
        for em in elem_pat.finditer(body):
            try:
                decoded = json.loads('"' + em.group(1) + '"')
            except json.JSONDecodeError:
                continue
            if has_banner(decoded):
                banner_block_bounds.append((body_start, body_end))
                break
    # Process list-form banner blocks: drop each banner-bearing element AND its
    # following comma (if any), OR its preceding comma (if it's the last
    # element in the list). Walk blocks in REVERSE file-offset order so
    # earlier offsets stay valid after each edit (each edit shrinks the
    # file). For each block, walk elements in NATURAL (forward) order over
    # the ORIGINAL `body` (captured before any modification), then assemble
    # the new body once at the end — this avoids offset drift caused by
    # repeated `new_body` rewrites.
    for body_start, body_end in reversed(banner_block_bounds):
        body = new_text[body_start:body_end]
        elems = list(elem_pat.finditer(body))
        if not elems:
            continue

        # Decide spans to DROP from the original body. Each drop span covers
        # either: (a) the entire element plus its trailing comma+whitespace,
        # (b) the entire element plus its preceding comma+whitespace (if the
        # element is the last in the list, no trailing comma), or (c) the
        # element only (single-element list — we later replace its content
        # with "" to preserve list shape).
        drop_spans = []  # list of (start, end, mode) where mode in {"trail","head","only"}
        replaced_here = 0
        for em in elems:
            try:
                decoded = json.loads('"' + em.group(1) + '"')
            except json.JSONDecodeError:
                continue
            if not has_banner(decoded):
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
                    # Only element in the list. Replace its content with "".
                    drop_spans.append((em.start(), em.end(), "only"))

        if not replaced_here:
            continue

        # Build new_body by walking drop_spans (sorted by start) and
        # concatenating kept regions. For the single-element case, replace
        # the element content with "".
        if len(drop_spans) == 1 and drop_spans[0][2] == "only":
            new_body = '""'
        else:
            new_body_parts = []
            prev_end = 0
            for ds, de, mode in drop_spans:
                new_body_parts.append(body[prev_end:ds])
                prev_end = de
            new_body_parts.append(body[prev_end:])
            new_body = ''.join(new_body_parts)

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
        description="Strip the .NET Interactive probeAddresses banner from notebooks"
    )
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--scan", metavar="PATH",
                       help="dry-run scan a file or dir; list banner outputs")
    group.add_argument("--scan-all", action="store_true",
                       help="dry-run scan repo-wide")
    group.add_argument("--apply", metavar="PATH",
                       help="fix a file in place (strip banners)")
    group.add_argument("--apply-all", action="store_true",
                       help="fix repo-wide in place")
    parser.add_argument("--check", action="store_true",
                        help="with --scan-all: exit 1 if any banner found")
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
    total_banners_found = 0
    total_banners_fixed = 0
    files_with_banner = 0
    skipped = []
    for p in sorted(paths):
        # Count FIRST so the apply report shows pre-strip banner count (after
        # the strip the count drops to 0; we'd otherwise miss the file in the
        # summary).
        found = count_banner_lines(p)
        fixed = 0
        if do_apply and found:
            fixed = strip_banner_in_place(p)[1]
        if not found:
            continue
        total_files += 1
        files_with_banner += 1
        total_banners_found += found
        total_banners_fixed += fixed
        rel = os.path.relpath(p, repo_root)
        if do_apply:
            tag = "FIXED" if fixed == found else ("PARTIAL" if fixed else "SKIP")
            print("[%s] %s  (%d banner line(s)%s)" % (
                tag, rel, found, ", %d fixed" % fixed))
            if fixed < found:
                skipped.append(rel)
        else:
            print("[DEFECT] %s  (%d banner line(s))" % (rel, found))

    mode = "apply" if do_apply else "scan"
    print("\n%s summary: %d notebook(s) carrying %d probeAddresses banner line(s)"
          % (mode, files_with_banner, total_banners_found))
    if do_apply:
        print("  fixed: %d   skipped: %d file(s)" % (total_banners_fixed, len(skipped)))
        for rel in skipped:
            print("    [unfixed] %s" % rel)

    if args.check and total_banners_found > 0:
        sys.exit(1)


if __name__ == "__main__":
    main()
