#!/usr/bin/env python3
"""
Detect machine-local path leaks in Jupyter notebooks.

This is the read-only companion of ``scrub_papermill_paths.py``. It scans a
notebook (or every notebook in a directory tree) and reports two defect
classes that are **content-based anti-patterns** (cf
[secrets-hygiene.md Stop & Repair rule 6](../../docs/reference/secrets-and-coord-detail.md#1-secrets-hygiene--content-based-pas-path-based)):

**Defect class A — ``metadata.papermill`` absolute path leak.**
When a notebook is re-executed via papermill with an absolute output path
(e.g. ``C:/Users/jsboi/AppData/Local/Temp/x.ipynb`` or ``/home/user/x.ipynb``),
papermill records that path in ``metadata.papermill.output_path`` (and
sometimes ``input_path``). This leaks the contributor's local directory
structure and is inconsistent with cleanly-executed notebooks where both
fields carry the notebook's relative basename.

**Defect class B — machine-local path inside ``outputs`` text streams.**
ipykernel temp paths in matplotlib UserWarnings
(``C:\\Users\\<user>\\AppData\\Local\\Temp\\ipykernel_<PID>\\<hash>.py:line``),
pip ``already satisfied: ... in C:\\Users\\<user>\\AppData\\Local\\Packages``
lines, .NET Interactive ``Loading extensions from C:\\Users\\<user>\\.nuget\\packages``
lines, and ``tempfile`` paths in user messages all leak the contributor's
home directory. Re-executing them regenerates a fresh leak each run, so
they are non-portable by construction.

**Scope vs ``scrub_papermill_paths.py``.** That script *fixes* defects in
place (text-level surgical edit, preserving cell structure). This detector
is **read-only** and CI-friendly: it returns a structured JSON report and
proper exit codes (``0`` clean, ``1`` defects found, ``2`` usage error) so
a pre-commit hook or CI workflow can gate a PR on this signal without
touching the notebook bytes. The fix-up is intentionally a separate
concern.

**Usage.**

    # Single file, JSON output to stdout:
    python detect_papermill_path_leak.py --scan path/to/notebook.ipynb

    # Single file, also include class B (output-text leaks). Off by default
    # because class B can be noisy on first scan; opt in once the metadata
    # leaks are clean:
    python detect_papermill_path_leak.py --scan path/to/nb.ipynb --outputs

    # Whole directory tree, JSON to stdout:
    python detect_papermill_path_leak.py --scan-all notebooks/

    # Repo-wide from repo root (skips ``.git``/``_archives``/``__pycache__``):
    python detect_papermill_path_leak.py --scan-all .

    # CI gate: exit 1 if any defect is found, suppress JSON:
    python detect_papermill_path_leak.py --scan-all . --check

    # Human-readable summary alongside JSON:
    python detect_papermill_path_leak.py --scan-all . --summary

**Design choices.**

- **No external deps** beyond the Python 3.10 stdlib (``json``, ``re``,
  ``argparse``, ``pathlib``). Mirrors the style of the other detectors in
  ``scripts/notebook_tools/``.
- **Path leak regexes are conservative.** A path is flagged only when it
  contains *both* a strong machine-local marker (``C:\\Users\\``,
  ``/home/``, ``/Users/`` macOS, ``/root/``, ``/tmp/ipykernel``) and a
  separator (``\\`` or ``/``) — single ``C:\\`` alone is too noisy (any
  Windows error message contains it). This matches the leak patterns
  documented in ``scrub_papermill_paths.py`` docstring §1.6.
- **Class B output scan** walks ``cell.outputs[*].text`` (stdout/stderr)
  and ``data['text/plain']`` only. Image and HTML data is skipped (binary
  / non-text). ``stream`` outputs (stderr) and ``display_data`` with
  ``text/plain`` are the two realistic leak channels.
- **Severity is binary** (``high`` for class A — metadata pollution;
  ``medium`` for class B — output noise). Future work: weight by leak
  density if a CI dashboard needs a numeric score.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any


# --- Defect class A: metadata.papermill absolute paths ---

# ``metadata.papermill.output_path`` / ``input_path`` should carry the
# notebook's relative basename (e.g. ``MyNotebook.ipynb``). Absolute paths
# indicate the notebook was re-executed with an absolute papermill target.
ABS_PATH_RE = re.compile(
    r"""(?xi)
    ^
    (?:
        [a-z]:[\\/]              # Windows: C:\ C:/ D:\ ...
        | /                      # POSIX root: /home /Users /root /tmp
        | \\\\ [^\\/.\s]+ [\\/]  # UNC: \\server\share
    )
    """
)


def _is_absolute(p: Any) -> bool:
    return isinstance(p, str) and bool(ABS_PATH_RE.match(p))


def _read_notebook(nb_path: Path) -> dict | None:
    try:
        with nb_path.open(encoding="utf-8") as f:
            data = json.load(f)
    except (OSError, json.JSONDecodeError, UnicodeDecodeError):
        return None
    return data if isinstance(data, dict) else None


def _scan_metadata_papermill(nb: dict) -> list[dict]:
    """Return a list of defects in ``metadata.papermill.{input,output}_path``."""
    pm = nb.get("metadata", {}).get("papermill")
    if not isinstance(pm, dict):
        return []
    defects: list[dict] = []
    for key in ("output_path", "input_path"):
        val = pm.get(key)
        if _is_absolute(val):
            defects.append({
                "kind": "metadata_papermill_absolute",
                "location": f"metadata.papermill.{key}",
                "value": val,
                "severity": "high",
            })
    return defects


# --- Defect class B: machine-local paths inside output text streams ---

# Conservative: require BOTH a strong machine-local marker (home-dir or
# python-specific temp/ipykernel) AND a path separator. This filters out
# generic Windows path mentions in error messages that don't actually leak
# the contributor's identity.
#
# Rationale: ``C:\`` alone matches virtually every Windows error traceback
# and is too noisy to be useful. ``C:\Users\`` is a reliable indicator that
# the contributor's home directory is being exposed.
#
# Each pattern matches the *full leaked path* (home dir + rest of the path
# until a whitespace / quote / bracket / newline boundary), so consumers
# see exactly what to scrub. The trailing ``(?:[\\/][^\\\s:"'<>]*)?``
# is optional — the home-dir root alone (e.g. ``/home/jesse``) is enough
# to flag a leak, but longer paths are preferred when present.
#
# The POSIX patterns use a negative look-behind for ``:`` so that a Windows
# path like ``C:/Users/jsboi/foo`` is matched only by the Windows rule, not
# also by the macOS rule (which would otherwise see ``/Users/jsboi/foo``
# inside the Windows path). Without this guard, every Windows user-profile
# leak would be double-flagged.
LEAK_PATTERNS: tuple[re.Pattern[str], ...] = (
    re.compile(r"""(?xi)
        C: [\\/] Users [\\/] [^\\\s:"'<>]+           # Windows user profile
    """),
    re.compile(r"""(?xi)
        (?<! :) / home / [^\\\s:"'<>]+               # Linux home dir
    """),
    re.compile(r"""(?xi)
        (?<! :) / Users / [^\\\s:"'<>]+              # macOS home dir
    """),
    re.compile(r"""(?xi)
        (?<! :) / root (?:[\\/][^\\\s:"'<>]*)?       # Linux root home
    """),
    re.compile(r"""(?xi)
        (?<! :) / tmp / ipykernel [_\-] [^\\\s:"'<>]*  # ipykernel temp
    """),
    re.compile(r"""(?xi)
        C: [\\/] Windows [\\/] system32 [^\\\s:"'<>]*  # Windows system path
    """),
)


def _scan_output_text(nb: dict) -> list[dict]:
    """Walk ``cells[*].outputs[*].text`` and ``data['text/plain']`` for leaks.

    Skips image and HTML data. ``stream`` (stderr) and ``display_data`` with
    ``text/plain`` are the two realistic leak channels; ``execute_result``
    with ``text/plain`` is included for completeness.
    """
    defects: list[dict] = []
    cells = nb.get("cells") or []
    for ci, cell in enumerate(cells):
        if not isinstance(cell, dict):
            continue
        outputs = cell.get("outputs") or []
        if not isinstance(outputs, list):
            continue
        for oi, out in enumerate(outputs):
            if not isinstance(out, dict):
                continue
            # Channel 1: stream outputs (stdout/stderr). nbformat wraps
            # text as ``str`` for short outputs and as ``list[str]`` for
            # longer streams (one element per line break); handle both.
            text = out.get("text")
            if isinstance(text, str):
                _collect_leaks(defects, ci, oi, "stream.text", text)
            elif isinstance(text, list):
                for li, piece in enumerate(text):
                    if isinstance(piece, str):
                        _collect_leaks(
                            defects, ci, oi,
                            f"stream.text[{li}]", piece,
                        )
            # Channel 2: display_data / execute_result with text/plain
            data = out.get("data")
            if isinstance(data, dict):
                tp = data.get("text/plain")
                if isinstance(tp, str):
                    _collect_leaks(defects, ci, oi, "data['text/plain']", tp)
                elif isinstance(tp, list):
                    # nbformat sometimes wraps long text in a list of strings
                    for li, piece in enumerate(tp):
                        if isinstance(piece, str):
                            _collect_leaks(
                                defects, ci, oi,
                                f"data['text/plain'][{li}]", piece,
                            )
    return defects


def _collect_leaks(
    defects: list[dict],
    cell_idx: int,
    output_idx: int,
    location: str,
    text: str,
) -> None:
    """Append a defect for each regex match in ``text``."""
    for pat in LEAK_PATTERNS:
        for m in pat.finditer(text):
            defects.append({
                "kind": "output_text_path_leak",
                "location": f"cells[{cell_idx}].outputs[{output_idx}].{location}",
                "match": m.group(0),
                "severity": "medium",
            })


# --- Scanner glue ---

# Directories skipped during recursive scans. Mirrors the conventions in
# ``scrub_papermill_paths.py`` and the other detectors.
_SKIP_DIR_NAMES = frozenset({
    ".git",
    "_archives",
    "__pycache__",
    "node_modules",
    ".venv",
    "venv",
})


def iter_notebooks(root: Path) -> list[Path]:
    """Yield every ``*.ipynb`` under ``root`` recursively, skipping noise dirs."""
    if root.is_file():
        return [root] if root.suffix == ".ipynb" else []
    if not root.is_dir():
        return []
    out: list[Path] = []
    for p in root.rglob("*.ipynb"):
        if any(part in _SKIP_DIR_NAMES for part in p.parts):
            continue
        out.append(p)
    return sorted(out)


def scan_notebook(nb_path: Path, *, include_outputs: bool = False) -> list[dict]:
    """Return the defects list for a single notebook."""
    nb = _read_notebook(nb_path)
    if nb is None:
        return [{
            "kind": "unreadable_notebook",
            "location": str(nb_path),
            "severity": "high",
            "reason": "JSON decode error or unreadable file",
        }]
    defects = _scan_metadata_papermill(nb)
    if include_outputs:
        defects.extend(_scan_output_text(nb))
    return defects


def scan_tree(
    root: Path,
    *,
    include_outputs: bool = False,
) -> list[dict]:
    """Scan every notebook under ``root``; return a flat defects report.

    Each defect is augmented with ``file`` (relative to ``root`` when
    possible) so a CI gate can pinpoint the offender. Defects from
    different notebooks are not merged — order is preserved.
    """
    report: list[dict] = []
    for nb_path in iter_notebooks(root):
        try:
            rel = str(nb_path.relative_to(root))
        except ValueError:
            rel = str(nb_path)
        for d in scan_notebook(nb_path, include_outputs=include_outputs):
            d_with_file = {"file": rel, **d}
            report.append(d_with_file)
    return report


# --- CLI ---

def _build_arg_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        prog="detect_papermill_path_leak.py",
        description=(
            "Detect machine-local path leaks in Jupyter notebooks "
            "(read-only companion of scrub_papermill_paths.py)."
        ),
    )
    mode = p.add_mutually_exclusive_group(required=True)
    mode.add_argument(
        "--scan", metavar="PATH",
        help="Scan a single notebook file (.ipynb).",
    )
    mode.add_argument(
        "--scan-all", metavar="DIR", nargs="?", const=".",
        help="Scan every notebook under DIR (default: current directory).",
    )
    p.add_argument(
        "--outputs", action="store_true",
        help="Also scan output text streams for path leaks (class B). "
             "Off by default — class B can be noisy on first scan.",
    )
    p.add_argument(
        "--check", action="store_true",
        help="CI gate: exit 1 if any defect is found, suppress JSON.",
    )
    p.add_argument(
        "--summary", action="store_true",
        help="Print a human-readable summary alongside the JSON report.",
    )
    return p


def main(argv: list[str] | None = None) -> int:
    args = _build_arg_parser().parse_args(argv)
    target = Path(args.scan if args.scan is not None else args.scan_all)
    if not target.exists():
        print(f"error: path does not exist: {target}", file=sys.stderr)
        return 2
    include_outputs = bool(args.outputs)
    if args.scan is not None:
        report = [
            {"file": str(target), **d}
            for d in scan_notebook(target, include_outputs=include_outputs)
        ]
    else:
        report = scan_tree(target, include_outputs=include_outputs)

    if args.summary and not args.check:
        _print_summary(report)
    elif not args.check:
        print(json.dumps(report, indent=2, ensure_ascii=False))

    if args.check and report:
        if args.summary:
            _print_summary(report)
        return 1
    return 0


def _print_summary(report: list[dict]) -> None:
    n = len(report)
    by_kind: dict[str, int] = {}
    files_with_defects: set[str] = set()
    for d in report:
        by_kind[d.get("kind", "?")] = by_kind.get(d.get("kind", "?"), 0) + 1
        if "file" in d:
            files_with_defects.add(d["file"])
    print(
        f"[detect_papermill_path_leak] {n} defect(s) in "
        f"{len(files_with_defects)} file(s).",
        file=sys.stderr,
    )
    for kind, count in sorted(by_kind.items()):
        print(f"  - {kind}: {count}", file=sys.stderr)


if __name__ == "__main__":
    raise SystemExit(main())