#!/usr/bin/env python3
"""
Strip the .NET Interactive ``probeAddresses`` HTTP-bootstrap banner from
notebook outputs (security hygiene).

Problem
-------
The ``dotnet-interactive`` kernel injects a ``probeAddresses`` JavaScript
bootstrap script as a ``display_data`` (``text/html``) output on the first
executed code cell of every .NET notebook. That script embeds the worker's
full network interface list, including:

  - host LAN IPv4 (``192.168.x.x``),
  - WSL/Docker bridge IPs (``172.x.x.x``),
  - link-local IPv6 (``fe80::...``),
  - and the host's **public globally-routable IPv6** (``2a01:...``).

On a public repo this leaks the maintainer's real internet-facing host
addresses. The banner is dead noise in a static notebook (it only acts
inside a live kernel session) -- zero pedagogical value.

This is a structural recurrence: a prior scrub (#2733, 2026-06-09) removed
the banner output-only from 51 notebooks, but the kernel RE-INJECTS it on
every first-execution, so every .NET notebook created or re-executed since
carries the leak again (183+ notebooks as of 2026-07-12, see issue #6309).
Manual cleanup cannot keep up; the kernel injects unconditionally and no
``dotnet-interactive`` flag suppresses it (``--http-local-only`` binds the
server to localhost but the JS probe still enumerates all host interfaces
client-side -- verified firsthand, see #6309).

Fix
-----
This is an INTRINSIC leak (no kernel-side cause to fix; the cause is the
kernel's own bootstrap which we do not control). The honest documented
plafond is to strip the banner output at commit time. This script:

  - detects any output whose ``data`` (any mimetype) contains one of the
    bootstrap symbols (``probeAddresses`` / ``loadDotnetInteractiveApi`` /
    ``probingAddresses``),
  - removes that WHOLE output object (output-only strip; ``execution_count``
    is left intact; source is untouched -- rule C.2 honored, the banner was
    never a real cell result, only kernel boot noise),
  - writes the notebook back with ``json.dump(indent=1, ensure_ascii=False)``
    which is byte-faithful to the repo convention (verified round-trip
    identical on the .NET C# notebooks), so only the removed output object
    changes.

Usage
-----
    # dry-run: list notebooks that still carry the banner
    python strip_dotnet_banner.py --scan-all
    python strip_dotnet_banner.py --scan-all --check   # exit 1 if any (CI)

    # fix specific file(s) -- this is the pre-commit hook entry point
    python strip_dotnet_banner.py --apply path/to/nb.ipynb [more.ipynb ...]

    # fix every notebook in the repo (one-time regression cleanup)
    python strip_dotnet_banner.py --apply-all

The pre-commit hook is registered in ``.pre-commit-config.yaml`` so the
banner can no longer be committed; see issue #6309.
"""

import argparse
import glob
import json
import os
import re
import sys

# Bootstrap symbols injected by dotnet-interactive's HTTP probe. Any of these
# appearing inside a `display_data`/`execute_result` output's `data` blob marks
# the whole output as the banner (these are kernel-internal JS symbols that
# never appear in legitimate pedagogical content).
BANNER_RE = re.compile(
    r"probeAddresses|loadDotnetInteractiveApi|probingAddresses",
    re.IGNORECASE,
)


def _read_notebook(nb_path):
    try:
        with open(nb_path, encoding="utf-8") as f:
            return json.load(f)
    except (OSError, json.JSONDecodeError):
        return None


def _output_blob(out):
    """Concatenate every mimetype value of a display/execute_result output.

    The banner's HTML lives under ``data["text/html"]`` but we scan all
    mimetypes defensively (the kernel could ship the probe under a different
    mime in a future version).
    """
    data = out.get("data", {})
    if not isinstance(data, dict):
        return ""
    blob = ""
    for val in data.values():
        if isinstance(val, list):
            blob += "".join(str(x) for x in val)
        elif isinstance(val, str):
            blob += val
    return blob


def is_banner_output(out):
    """True if a single output object is the probeAddresses bootstrap banner."""
    if out.get("output_type") not in ("display_data", "execute_result"):
        return False
    return bool(BANNER_RE.search(_output_blob(out)))


def find_banner_outputs(nb):
    """Return list of (cell_index, output_index) for banner outputs."""
    hits = []
    for ci, cell in enumerate(nb.get("cells", [])):
        if cell.get("cell_type") != "code":
            continue
        for oi, out in enumerate(cell.get("outputs", [])):
            if is_banner_output(out):
                hits.append((ci, oi))
    return hits


def strip_notebook(nb_path, apply=False):
    """Remove banner outputs from one notebook.

    Returns ``(banners_found, banners_removed, output_count_delta)``.
    ``output_count_delta`` is the net number of output objects removed (equals
    ``banners_removed`` here, but kept separate for clarity in the summary).

    Encoding preservation: the repo has two notebook populations -- some
    authored with ``ensure_ascii=False`` (literal UTF-8) and the .NET jumeau
    series authored with ``ensure_ascii=True`` (non-ASCII escaped as
    ``\\uXXXX``). A blind round-trip with either setting churns the other
    population's markdown (a massive unrelated diff). So we detect which
    ``ensure_ascii`` setting reproduces the source byte-for-byte and reuse it
    on write -- same candidate-encoding approach as ``scrub_papermill_paths``.
    """
    with open(nb_path, encoding="utf-8") as f:
        raw_text = f.read()
    try:
        nb = json.loads(raw_text)
    except json.JSONDecodeError:
        return (0, 0, 0)

    hits = find_banner_outputs(nb)
    if not hits:
        return (0, 0, 0)

    # Remove outputs in reverse (cell, output) index order so earlier indices
    # stay valid as we delete.
    removed = 0
    for ci, oi in sorted(hits, reverse=True):
        del nb["cells"][ci]["outputs"][oi]
        removed += 1

    if apply:
        had_trailing_nl = raw_text.endswith("\n")
        # Detect the source's ensure_ascii setting from the raw text:
        # ensure_ascii=True source -> raw is pure ASCII but contains \uXXXX
        # escapes for every non-ASCII char. ensure_ascii=False source -> raw
        # carries literal non-ASCII bytes. Match the source to avoid churning
        # the markdown encoding (the .NET jumeau series is ensure_ascii=True).
        import re as _re
        has_unicode_escapes = bool(_re.search(r"\\u[0-9a-fA-F]{4}", raw_text))
        try:
            raw_text.encode("ascii")
            source_is_ascii = True
        except UnicodeEncodeError:
            source_is_ascii = False
        ensure_ascii = True if (has_unicode_escapes and source_is_ascii) else False

        new_text = json.dumps(nb, ensure_ascii=ensure_ascii, indent=1)
        if had_trailing_nl:
            new_text += "\n"
        if new_text != raw_text:
            with open(nb_path, "w", encoding="utf-8", newline="") as f:
                f.write(new_text)

    return (len(hits), removed, removed)


def iter_notebooks(nb_root):
    for path in glob.glob(os.path.join(nb_root, "**", "*.ipynb"), recursive=True):
        base = os.path.basename(path)
        if "_output" in base or "_executed" in base:
            continue
        yield path


def _repo_root():
    return os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


def _resolve_targets(args):
    """Return (list_of_paths, nb_root). Raises SystemExit on bad args."""
    nb_root = os.path.join(_repo_root(), "MyIA.AI.Notebooks")
    if args.scan_all or args.apply_all:
        return list(iter_notebooks(nb_root)), nb_root
    if args.paths:
        paths = []
        for p in args.paths:
            if os.path.isdir(p):
                paths.extend(iter_notebooks(p))
            elif os.path.isfile(p):
                paths.append(p)
            else:
                print("warning: path not found: %s" % p, file=sys.stderr)
        return paths, nb_root
    # No paths and no -all flag: nothing to do.
    return [], nb_root


def main():
    parser = argparse.ArgumentParser(
        description="Strip .NET Interactive probeAddresses banner from notebooks"
    )
    parser.add_argument("paths", nargs="*",
                        help="notebook files or dirs to process (used by pre-commit)")
    parser.add_argument("--scan-all", dest="scan_all", action="store_true",
                        help="dry-run: scan the whole repo (no fix)")
    parser.add_argument("--apply", action="store_true",
                        help="remove banner outputs from the given paths (in place)")
    parser.add_argument("--apply-all", action="store_true",
                        help="remove banner outputs from every notebook in the repo")
    parser.add_argument("--check", action="store_true",
                        help="with --scan-all: exit 1 if any banner found (CI mode)")
    args = parser.parse_args()

    do_apply = args.apply or args.apply_all
    if not (args.scan_all or do_apply):
        # Default behavior when invoked with bare paths (e.g. pre-commit with
        # only filenames and no explicit flag): scan those paths.
        if args.paths:
            args.scan_all = False
        else:
            parser.error("specify --scan-all / --apply-all, or pass notebook paths with --apply")

    paths, nb_root = _resolve_targets(args)
    if not paths:
        print("no notebooks to process")
        return

    repo_root = _repo_root()
    total_found = 0
    total_removed = 0
    files_with_banner = 0
    for p in sorted(paths):
        found, removed, _ = strip_notebook(p, apply=do_apply)
        if not found:
            continue
        files_with_banner += 1
        total_found += found
        total_removed += removed
        rel = os.path.relpath(p, repo_root)
        if do_apply:
            print("[STRIPPED] %s  (%d banner output(s) removed)" % (rel, removed))
        else:
            print("[BANNER] %s  (%d banner output(s))" % (rel, found))

    mode = "apply" if do_apply else "scan"
    print("\n%s summary: %d notebook(s) with %d banner output(s)"
          % (mode, files_with_banner, total_found))
    if do_apply:
        print("  removed: %d" % total_removed)

    if args.check and total_found > 0:
        sys.exit(1)


if __name__ == "__main__":
    main()
