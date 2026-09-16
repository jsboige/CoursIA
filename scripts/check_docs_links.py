#!/usr/bin/env python3
"""Check for broken relative markdown links and orphan docs across the repository.

Scans CLAUDE.md, index.md, PARCOURS.md, docs/, .claude/rules/, .claude/agents/,
.claude/skills/, every ``slides/<deck>/slides.md`` deck, and all README.md files
for relative links and verifies targets exist.

Also detects orphan .md files in docs/ (not referenced by any scanned file).

Usage:
    python scripts/check_docs_links.py                        # Full scan
    python scripts/check_docs_links.py --baseline             # Write baseline report
    python scripts/check_docs_links.py --check                # Check against baseline
    python scripts/check_docs_links.py --check --base origin/main
    python scripts/check_docs_links.py --quiet                # Minimal output (for CI)
    python scripts/check_docs_links.py --orphans              # Also report orphan docs
    python scripts/check_docs_links.py --expect-broken 1      # Positive control (see below)

Positive control
----------------
``--expect-broken N`` arms an in-band control: the scan must find AT LEAST ``N``
broken links, otherwise it exits 2. Without it, "no broken link" is
indistinguishable from a dead detection path (model:
``scripts/notebook_tools/scan_slidev_composition.py``, ``controle_positif_*``).
Point it at a tree where a link was deliberately broken, and a healthy organ
renders rc=1 (a real finding), while a dead one renders rc=2 (control unmet).

``--check`` accepts two independent excuses for a broken link. The frozen
``baseline_docs_links.json`` covers paths with no comparison revision (manual
dispatch, plain full scan). ``--base REF`` additionally excuses a link that was
ALREADY broken at REF: without it, a single broken link on ``main`` reddens
``check-links`` on every open PR until someone regenerates the baseline, which
nothing does (#15766).

Exit codes:
    0 = all links valid (or only excused broken links)
    1 = new broken links found (regression)
    2 = error during execution
"""

import argparse
import json
import posixpath
import re
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path
from urllib.parse import unquote

REPO_ROOT = Path(__file__).resolve().parent.parent

# Directories and files to scan for links
SCAN_SCOPES = [
    "CLAUDE.md",
    # Root entry points (#7422 root slice): index.md rotted historically precisely
    # because no organ watched it -- the portal and the parcours front page are
    # now link-checked like everything else.
    "index.md",
    "PARCOURS.md",
    "docs/",
    ".claude/rules/",
    ".claude/agents/",
    ".claude/skills/",
]

# Deck scope (#15867). `slides/<deck>/slides.md` was watched by NO organ: the
# #15023 content tranche wrote 17 dead relative links on `03-logique` (PR
# #15865) and this organ still reported "0 broken". Same failure mode as the
# root entry points above -- `index.md` rotted because nothing watched it.
#
# Decks are NOT added to SCAN_SCOPES on purpose: that list rglobs `*.md`, which
# under `slides/` would drag in 119 non-deck markdown files (`analysis/`,
# `extracted/`, the `.marp.md` siblings) holding 734 broken links of 1367 --
# measured on `origin/main` 2026-09-13. Those are working artifacts, not the
# delivered deck; merging them here would redden every PR. Only the deck file
# the course actually ships is in scope.
DECK_DIR = "slides"
DECK_FILENAME = "slides.md"

# Directories to skip when scanning and resolving.
#
# NOTE on archive variants (EPIC #9535 item 10): the canonical code-archive
# convention is `_archive/` (no trailing 's'). These notebook archives hold
# READMEs that link to ACTIVE notebooks, so a broken link there is a real
# defect -- incident #9814 proved it: a structurally-broken `../../` link in
# SymbolicLearning/_archive/ was masked for as long as a STALE `_archives`
# (with 's') entry skipped the folder, then surfaced as a CI REGRESSION when
# the folder was renamed to `_archive/` (no longer skipped). We therefore
# DELIBERATELY do NOT skip `_archive/` -- its READMEs are validated. Do not
# "harmonize" by adding `_archive` here without first checking the link
# health of the archived READMEs (see test_check_docs_links TestShouldSkip).
#
# `archive/` (docs historical archives, ~319 files) stays skipped: those are
# frozen historical reports out of scope for link validation.
SKIP_DIRS = {
    ".lake", "node_modules", ".git", "venv", "__pycache__",
    "archive", "_output", ".ipynb_checkpoints", "worktrees",
    ".mypy_cache", ".pytest_cache", ".ruff_cache",
    "custom_nodes",  # Third-party ComfyUI plugins, not ours to fix
}

# Baseline file location
BASELINE_PATH = REPO_ROOT / "scripts" / "tests" / "baseline_docs_links.json"


def _load_submodule_paths() -> set[str]:
    """Read git submodule paths from .gitmodules (repo-relative, posix form).

    Submodule internals are third-party checkouts (Argumentum, MetaGeneticSharp):
    their broken links are not ours to fix, so we skip them like SKIP_DIRS.
    Returns an empty set if .gitmodules is absent or unparsable.
    """
    gitmodules = REPO_ROOT / ".gitmodules"
    if not gitmodules.is_file():
        return set()
    paths: set[str] = set()
    try:
        for line in gitmodules.read_text(encoding="utf-8").splitlines():
            line = line.strip()
            if line.startswith("path"):
                _, _, value = line.partition("=")
                value = value.strip().strip("/")
                if value:
                    paths.add(value)
    except OSError:
        return set()
    return paths


SUBMODULE_PATHS = _load_submodule_paths()

# Pattern: [link text](relative/path) — captures relative paths only (no http/https/#anchors)
LINK_PATTERN = re.compile(
    r"\[([^\]]*)\]\((?!https?://)(?!mailto:)(?!#)([^)\s#]+)\)"
)


@dataclass
class LinkRef:
    """A single link reference found in a file."""
    source: str       # relative path from repo root
    target: str       # the link target (raw)
    line: int         # line number
    text: str         # link text


@dataclass
class ScanResult:
    """Result of a full link scan."""
    broken: list[LinkRef] = field(default_factory=list)
    valid: list[LinkRef] = field(default_factory=list)
    orphans: list[str] = field(default_factory=list)
    scanned_files: int = 0
    total_links: int = 0


def _should_skip(path: Path) -> bool:
    """Check if a path should be skipped (in SKIP_DIRS, a submodule, or problematic)."""
    try:
        rel = path.relative_to(REPO_ROOT)
    except ValueError:
        return True
    if any(skip in rel.parts for skip in SKIP_DIRS):
        return True
    rel_posix = rel.as_posix()
    return any(rel_posix == sm or rel_posix.startswith(sm + "/") for sm in SUBMODULE_PATHS)


def _is_valid_target(target: str) -> bool:
    """Filter out non-file links (anchors, URLs, template variables)."""
    if not target:
        return False
    # Skip template variables, absolute paths, URLs
    if target.startswith(("{", "<", "http:", "https:", "mailto:", "#", "/")):
        return False
    # Skip image references in some edge cases
    if target.endswith((".png", ".jpg", ".jpeg", ".gif", ".svg", ".ico")):
        return True  # Still check these
    # Only check file-like targets
    if "." not in Path(target).name and not target.endswith("/"):
        return False
    return True


class DeckScopeEmpty(RuntimeError):
    """`slides/` exists yet holds no deck file: the scope would be silently empty.

    A scope that matches nothing renders "0 broken links" -- indistinguishable
    from a detection path that never ran. Refusing loudly is the whole point
    (#15867).
    """


def find_deck_files() -> list[Path]:
    """Every `slides/<deck>/slides.md` under the deck directory, in path order.

    Resolving the ``_archive/`` question the same way ``SKIP_DIRS`` does: an
    archived deck is NOT skipped (this organ deliberately validates `_archive/`
    READMEs -- see the SKIP_DIRS note). Returns [] only when `slides/` itself is
    absent, which is the case in the tmp-tree tests; an existing but empty deck
    scope raises instead.
    """
    slides = REPO_ROOT / DECK_DIR
    if not slides.is_dir():
        return []
    decks = sorted(
        p for p in slides.rglob(DECK_FILENAME) if not _should_skip(p)
    )
    if not decks:
        raise DeckScopeEmpty(
            f"{DECK_DIR}/ exists but no {DECK_DIR}/**/{DECK_FILENAME} was found -- "
            f"refusing to report a clean scan from an empty scope (#15867)."
        )
    return decks


def find_scan_files() -> list[Path]:
    """Collect all files to scan for links."""
    files = []
    for scope in SCAN_SCOPES:
        p = REPO_ROOT / scope
        if p.is_file():
            files.append(p)
        elif p.is_dir():
            for f in sorted(p.rglob("*.md")):
                if not _should_skip(f):
                    files.append(f)

    # Add all README.md files (excluding skipped dirs)
    for readme in sorted(REPO_ROOT.rglob("README.md")):
        if not _should_skip(readme):
            if readme not in files:
                files.append(readme)

    # Add the slide decks (deck-only scope, see DECK_DIR).
    for deck in find_deck_files():
        if deck not in files:
            files.append(deck)

    return files


def scan_content(content: str, rel_source: str) -> list[LinkRef]:
    """Extract all relative links from markdown ``content``.

    ``rel_source`` is the repo-relative posix path the content comes from: link
    targets resolve against its directory, so the same routine serves both the
    working tree and a ``git show`` read of an arbitrary revision.

    Skips links inside fenced code blocks (```...```).
    """
    refs = []
    in_code_block = False
    for line_num, line in enumerate(content.splitlines(), 1):
        stripped = line.strip()
        if stripped.startswith("```"):
            in_code_block = not in_code_block
            continue
        if in_code_block:
            continue

        # Strip inline code spans (`...`): their contents render as literal text,
        # so a [text](target) inside backticks is not a clickable link. This avoids
        # false positives on format templates in review ledgers, e.g. `[Foo](...)`.
        line = re.sub(r"`[^`]*`", "", line)

        for match in LINK_PATTERN.finditer(line):
            text = match.group(1)
            target = match.group(2)
            if _is_valid_target(target):
                refs.append(LinkRef(
                    source=rel_source,
                    target=target,
                    line=line_num,
                    text=text,
                ))
    return refs


def scan_file(filepath: Path) -> list[LinkRef]:
    """Extract all relative links from a markdown file on disk."""
    try:
        content = filepath.read_text(encoding="utf-8")
    except (UnicodeDecodeError, PermissionError, OSError):
        return []
    try:
        rel_source = filepath.relative_to(REPO_ROOT).as_posix()
    except ValueError:
        rel_source = str(filepath)
    return scan_content(content, rel_source)


def _is_quarto_render_target(html_path: Path, root: Path) -> bool:
    """Return whether Quarto generates ``html_path`` from a listed notebook."""
    notebook = html_path.with_suffix(".ipynb")
    if not notebook.is_file():
        return False
    try:
        notebook_rel = notebook.relative_to(root).as_posix()
        quarto = (root / "_quarto.yml").read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError, ValueError):
        return False
    return f'"{notebook_rel}"' in quarto


def check_link(target: str, source_path: Path, root: Path = REPO_ROOT) -> bool:
    """Check if a relative link target exists.

    Args:
        target: The link target (relative path).
        source_path: Path of the file containing the link.
        root: Root directory for safety check (default: REPO_ROOT).
    """
    # Resolve relative to source file's directory (decode URL-encoded chars)
    try:
        decoded_target = unquote(target)
        resolved = (source_path.parent / decoded_target).resolve()
    except (OSError, ValueError):
        return False

    # Must be within root (safety: no escaping outside the repo)
    try:
        rel_posix = resolved.relative_to(root).as_posix()
    except ValueError:
        return False

    # Links into a git submodule are valid regardless of checkout state: CI uses
    # submodules: false, so the mount dir may be absent. Submodule content is
    # third-party — its presence is not this repo's concern to verify.
    if any(rel_posix == sm or rel_posix.startswith(sm + "/") for sm in SUBMODULE_PATHS):
        return True

    if resolved.exists():
        return True

    # Quarto-generated pages are absent from the source tree by design. They are
    # valid only when the sibling notebook exists and is explicitly listed in
    # project.render; otherwise the link remains a genuine broken render target.
    return resolved.suffix.lower() == ".html" and _is_quarto_render_target(
        resolved, root
    )


def _git_show(rev: str, rel_path: str) -> str | None:
    """Content of ``rel_path`` at ``rev``, or None when it is not readable.

    The return code is inspected BEFORE the stdout is used: a partial clone can
    exit non-zero and still emit a body, which would then be scanned as if it
    were the file (#15387).
    """
    proc = subprocess.run(
        ["git", "show", f"{rev}:{rel_path}"],
        cwd=REPO_ROOT, capture_output=True, text=True,
        encoding="utf-8", errors="replace",
    )
    return proc.stdout if proc.returncode == 0 else None


def _git_tree_files(rev: str) -> set[str] | None:
    """Every blob path (repo-relative posix) at ``rev``, or None if unreachable.

    None is the caller's signal that the comparison revision could not be read;
    the caller then falls back to the frozen baseline rather than inventing
    regressions it cannot substantiate.
    """
    proc = subprocess.run(
        ["git", "ls-tree", "-r", "--name-only", rev],
        cwd=REPO_ROOT, capture_output=True, text=True,
        encoding="utf-8", errors="replace",
    )
    if proc.returncode != 0:
        return None
    return {line.strip() for line in proc.stdout.splitlines() if line.strip()}


def _tree_dirs(files: set[str]) -> set[str]:
    """Directories implied by a file listing (git stores no empty directory)."""
    dirs: set[str] = set()
    for name in files:
        parts = name.split("/")
        for i in range(1, len(parts)):
            dirs.add("/".join(parts[:i]))
    return dirs


def _link_exists_in_tree(target: str, source_rel: str, files: set[str],
                         dirs: set[str], quarto_yml: str | None) -> bool:
    """Existence oracle over a git tree listing, mirroring ``check_link``."""
    try:
        decoded = unquote(target)
    except (ValueError, TypeError):
        return False

    rel = posixpath.normpath(posixpath.join(posixpath.dirname(source_rel), decoded))
    if rel.startswith(("/", "..")):
        return False  # escapes the repo, as in check_link
    if any(rel == sm or rel.startswith(sm + "/") for sm in SUBMODULE_PATHS):
        return True
    if rel in files or rel.rstrip("/") in dirs:
        return True
    # Quarto-generated pages are absent from the source tree by design: valid
    # only when the sibling notebook exists and project.render lists it.
    if rel.endswith(".html") and quarto_yml is not None:
        notebook = rel[:-5] + ".ipynb"
        return notebook in files and f'"{notebook}"' in quarto_yml
    return False


def preexisting_broken(broken_refs: list[LinkRef], rev: str) -> set[tuple[str, str]] | None:
    """Among ``broken_refs``, those already broken at ``rev``.

    Only the sources carrying a broken link at HEAD are read at ``rev``: the
    question is never "what was broken there" but "was THIS link already
    broken", so the base revision is consulted source by source instead of
    being scanned wholesale.

    A link counts as pre-existing only when the source existed at ``rev``,
    carried the same target, and that target was already absent there. A target
    deleted by the branch, or a link the branch introduced, stays a regression.

    Returns None when ``rev`` cannot be read.
    """
    if not broken_refs:
        return set()
    tree = _git_tree_files(rev)
    if tree is None:
        return None
    dirs = _tree_dirs(tree)
    quarto_yml = _git_show(rev, "_quarto.yml")

    wanted: dict[str, set[str]] = {}
    for ref in broken_refs:
        wanted.setdefault(ref.source, set()).add(ref.target)

    preexisting: set[tuple[str, str]] = set()
    for source, targets in wanted.items():
        if source not in tree:
            continue  # created by this branch: nothing pre-existed
        content = _git_show(rev, source)
        if content is None:
            continue
        base_targets = {r.target for r in scan_content(content, source)}
        for target in targets:
            if target in base_targets and not _link_exists_in_tree(
                target, source, tree, dirs, quarto_yml
            ):
                preexisting.add((source, target))
    return preexisting


def find_orphan_docs(scanned_files: list[Path], all_refs: list[LinkRef]) -> list[str]:
    """Find .md files in docs/ not referenced by any link in scanned files."""
    # Collect all link targets (resolved to repo-relative paths)
    referenced = set()
    for ref in all_refs:
        source_path = REPO_ROOT / ref.source
        resolved = (source_path.parent / ref.target).resolve()
        try:
            rel = str(resolved.relative_to(REPO_ROOT)).replace("\\", "/")
            referenced.add(rel)
        except ValueError:
            pass

    orphans = []
    docs_dir = REPO_ROOT / "docs"
    if docs_dir.exists():
        for md_file in sorted(docs_dir.rglob("*.md")):
            if _should_skip(md_file):
                continue
            try:
                rel = str(md_file.relative_to(REPO_ROOT)).replace("\\", "/")
            except ValueError:
                continue
            if rel not in referenced:
                orphans.append(rel)

    return orphans


def run_scan(report_orphans: bool = False) -> ScanResult:
    """Run a full link scan across the repository."""
    result = ScanResult()
    files = find_scan_files()
    result.scanned_files = len(files)

    all_refs = []
    for filepath in files:
        refs = scan_file(filepath)
        all_refs.extend(refs)

    result.total_links = len(all_refs)

    for ref in all_refs:
        source_path = REPO_ROOT / ref.source
        if check_link(ref.target, source_path):
            result.valid.append(ref)
        else:
            result.broken.append(ref)

    if report_orphans:
        result.orphans = find_orphan_docs(files, all_refs)

    return result


def write_baseline(result: ScanResult, path: Path = BASELINE_PATH) -> None:
    """Write scan results as a baseline JSON file."""
    path.parent.mkdir(parents=True, exist_ok=True)
    data = {
        "broken_links": [
            {"source": r.source, "target": r.target, "line": r.line, "text": r.text}
            for r in result.broken
        ],
        "orphans": result.orphans,
        "scanned_files": result.scanned_files,
        "total_links": result.total_links,
    }
    path.write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n",
                    encoding="utf-8")


def load_baseline(path: Path = BASELINE_PATH) -> dict | None:
    """Load a baseline JSON file. Returns None if not found."""
    if not path.exists():
        return None
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, UnicodeDecodeError):
        return None


def check_regression(result: ScanResult, baseline: dict,
                     preexisting: set[tuple[str, str]] | None = None) -> list[LinkRef]:
    """Find broken links that are NOT already excused (new regressions).

    Two independent excuses apply. The frozen ``baseline`` covers the
    non-PR paths (dispatch, plain full scan) where no comparison revision is
    available. ``preexisting`` — computed against the branch's base revision —
    covers the PR path: a link already broken before the branch is not this
    branch's regression, and would otherwise redden every open PR at once
    (#15766).
    """
    baseline_targets = {
        (b["source"], b["target"]) for b in baseline.get("broken_links", [])
    }
    excused = baseline_targets | (preexisting or set())
    return [ref for ref in result.broken if (ref.source, ref.target) not in excused]


def format_report(result: ScanResult, show_orphans: bool = False) -> str:
    """Format scan results as a human-readable report."""
    lines = []
    lines.append(f"Scanned {result.scanned_files} files, {result.total_links} links")

    if result.broken:
        lines.append(f"\nBroken links ({len(result.broken)}):")
        for ref in sorted(result.broken, key=lambda r: (r.source, r.line)):
            lines.append(f"  {ref.source}:{ref.line} -> {ref.target}")
    else:
        lines.append("\nNo broken links found.")

    if show_orphans and result.orphans:
        lines.append(f"\nOrphan docs ({len(result.orphans)}) [WARN, non-blocking]:")
        for orphan in result.orphans:
            lines.append(f"  {orphan}")

    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(
        description="Check for broken relative links in markdown files",
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument("--baseline", action="store_true",
                        help="Write current state as baseline")
    parser.add_argument("--check", action="store_true",
                        help="Check for regressions against baseline")
    parser.add_argument("--base", metavar="REF", default=None,
                        help="With --check: a broken link already broken at REF "
                             "(e.g. origin/main) is not a regression")
    parser.add_argument("--orphans", action="store_true",
                        help="Also report orphan docs")
    parser.add_argument("--quiet", action="store_true",
                        help="Minimal output")
    parser.add_argument("--expect-broken", metavar="N", type=int, default=None,
                        help="Positive control: require at least N broken links, "
                             "else exit 2. Without it, 'no broken link' is "
                             "indistinguishable from a dead detection path.")
    args = parser.parse_args()

    try:
        result = run_scan(report_orphans=args.orphans)

        # The positive control is evaluated BEFORE any mode branch, so it is
        # never silently ignored by --check/--baseline.
        if args.expect_broken is None:
            # Advisory, and only in the bare diagnostic scan: `--check` is the
            # gate mode, whose contract is a single summary line on success
            # (docs-link-check.yml), and a line printed on every green PR would
            # be trained away within a week.
            if not args.quiet and not args.check and not args.baseline:
                print("WARNING: scan without an armed positive control -- "
                      "'no broken link' is indistinguishable from a dead "
                      "detection path (pass --expect-broken 1 to tell them apart).",
                      file=sys.stderr)
        elif len(result.broken) < args.expect_broken:
            print(f"POSITIVE CONTROL FAILED: {len(result.broken)} broken link(s) "
                  f"found, at least {args.expect_broken} expected -- the "
                  f"instrument does not detect what it should.",
                  file=sys.stderr)
            sys.exit(2)

        if args.baseline:
            write_baseline(result)
            if not args.quiet:
                print(f"Baseline written to {BASELINE_PATH}")
                print(format_report(result, show_orphans=True))
            return

        if args.check:
            preexisting = None
            if args.base:
                preexisting = preexisting_broken(result.broken, args.base)
                if preexisting is None and not args.quiet:
                    print(f"WARNING: {args.base!r} is not readable, comparing against the "
                          f"frozen baseline only.", file=sys.stderr)

            baseline = load_baseline()
            if baseline is None and preexisting is None:
                if not args.quiet:
                    print("No baseline found. Run with --baseline first.")
                # Nothing can excuse a broken link: every one is a regression
                if result.broken:
                    if not args.quiet:
                        print(format_report(result))
                    sys.exit(1)
                sys.exit(0)

            new_broken = check_regression(result, baseline or {}, preexisting)
            if new_broken:
                if not args.quiet:
                    print(f"REGRESSION: {len(new_broken)} new broken link(s):")
                    for ref in new_broken:
                        print(f"  {ref.source}:{ref.line} -> {ref.target}")
                    print(f"\nExcused: {len((baseline or {}).get('broken_links', []))} from baseline"
                          f" + {len(preexisting or ())} already broken at {args.base or '(no base)'}.")
                sys.exit(1)

            if not args.quiet:
                print(f"OK: No new broken links. "
                      f"({len(result.broken)} pre-existing, {result.total_links} total)")
            sys.exit(0)

        # Default: full scan
        if not args.quiet:
            print(format_report(result, show_orphans=args.orphans))

        if result.broken:
            sys.exit(1)
        sys.exit(0)

    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(2)


if __name__ == "__main__":
    main()
