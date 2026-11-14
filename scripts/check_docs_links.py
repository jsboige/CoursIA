#!/usr/bin/env python3
"""Check for broken relative markdown links and orphan docs across the repository.

Scans CLAUDE.md, index.md, PARCOURS.md, docs/, .claude/rules/, .claude/agents/,
.claude/skills/, every ``slides/<deck>/slides.md`` deck, all README.md files and
Quarto ``.qmd`` pages for relative links and verifies targets exist.

Also detects orphan .md files in docs/ (not referenced by any scanned file).

Usage:
    python scripts/check_docs_links.py                        # Full scan
    python scripts/check_docs_links.py --baseline             # Write baseline report
    python scripts/check_docs_links.py --check                # Check against baseline
    python scripts/check_docs_links.py --check --base origin/main
    python scripts/check_docs_links.py --quiet                # Minimal output (for CI)
    python scripts/check_docs_links.py --orphans              # Also report orphan docs
    python scripts/check_docs_links.py --expect-broken 1      # Positive control (see below)

Code-comment citations (#24410)
-------------------------------
``--code`` runs a second pass over the comments of `.py`, `.lean` and `.cs`
files: a doc path cited there (`docs/...md`) is invisible to the markdown scan
whether it is alive or dead. It is a SEPARATE mode, not an addition: `main`
already carries broken markdown links the baseline does not excuse, and merging
the two counts would make a code finding indistinguishable from that red. All
the differential machinery applies unchanged -- ``--check --base REF`` excuses a
citation already dead at REF, and ``--expect-broken N`` arms the positive
control on THIS pass.

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
import ast
import io
import json
import os
import posixpath
import re
import subprocess
import sys
import tokenize
import warnings
from dataclasses import dataclass, field
from pathlib import Path
from typing import Callable
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
    # Book inventory (#18899): every row must point at a path that exists on
    # main. The two former inventories drifted apart because no organ watched
    # their links -- this one is now the single inventory, so it is checked.
    "MyIA.AI.Notebooks/QuantConnect/BOOK_MAPPING.md",
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
#
# `_site/` is the Quarto BUILD ARTIFACT (generated from our own sources, and
# gitignored). It is skipped for the same reason `node_modules` is: it is not
# source, so a broken link inside it is not a defect of the repository -- it is
# a re-render of a link that the SOURCE already declares. Without this entry,
# the organ's result depends on whether the machine happens to have run a
# Quarto build: on a developer machine that has, it reports "dead links" for
# pages that are not in the repository at all. In CI the situation does not
# arise (the artifact is gitignored, hence never checked out), which is exactly
# why the divergence went unnoticed: the organ's verdict was machine-dependent.
SKIP_DIRS = {
    ".lake", "node_modules", ".git", "venv", "__pycache__",
    "archive", "_output", ".ipynb_checkpoints", "worktrees",
    ".mypy_cache", ".pytest_cache", ".ruff_cache",
    "custom_nodes",  # Third-party ComfyUI plugins, not ours to fix
    "_site",  # Quarto build artifact -- gitignored, not source
    # Agent scratch (fleet rule: throwaway artefacts live in the workspace's
    # gitignored `.tmp/`). Same defect class as `_site`: not source, gitignored,
    # hence never checked out in CI. Measured on 2026-11-03 -- the README sweep
    # below is repo-wide, so three scratch worktrees under `.tmp/` supplied 29
    # of the 31 "broken links" the organ reported locally, against 2 real ones
    # (#24410). A verdict that depends on what a lane happens to have scratched
    # is not a verdict, and it buries the real defects in noise.
    ".tmp",
}

# Baseline file location
BASELINE_PATH = REPO_ROOT / "scripts" / "tests" / "baseline_docs_links.json"

# The code-citation pass (#24410) keeps its own baseline: the two instruments
# answer different questions, and sharing one file would make `--baseline` in
# one mode silently rewrite the other's frozen state.
CODE_BASELINE_PATH = REPO_ROOT / "scripts" / "tests" / "baseline_docs_code_citations.json"


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
            # Quarto ``.qmd`` pages in addition to ``.md`` (#26457): the site is
            # built from .qmd sources (docs/index.qmd, docs/parcours.qmd, the
            # series index.qmd), and globbing ``*.md`` alone never opened them --
            # a move that left 19 dead links in a .qmd read as a clean scan
            # (#26281). The union is de-duplicated, so a file matching neither
            # pattern is simply absent, as before.
            for f in sorted(set(p.rglob("*.md")) | set(p.rglob("*.qmd"))):
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


# ---------------------------------------------------------------------------
# Code-comment citation pass (#24410)
# ---------------------------------------------------------------------------
#
# The markdown scan above never opens a `.py`, `.lean` or `.cs` file, so a doc
# path cited in a code comment is invisible to this organ whether it is alive or
# dead. Measured on `origin/main` 2026-11-03: four citations point at a path that
# no longer exists (the target moved), across three languages -- the same hole,
# one fix.
#
# A naive extension is worthless: scanning every `docs/...md`-shaped string in
# code yields 118 absent paths, and only a minority are citations. The three
# noise families are excluded BY CONSTRUCTION below, not by an allow/deny list
# that rots on the next rename:
#
#   1. test fixtures (a path in a test tree is a value, not a claim about the
#      repo) -- `_is_test_tree`;
#   2. generated-output positions (`--out`, `open(..., "w")`, `write_text`) --
#      `_is_output_position`: write the path down is not cite it;
#   3. third-party repo paths (`lean/docs/132.md` belongs to openai/math) --
#      `_is_scoped_doc_citation`: a citation must be anchored at a top-level
#      entry of OUR tree, otherwise it does not resolve against it at all.

CODE_SCAN_SUFFIXES = (".py", ".lean", ".cs")

# Directories whose contents are test data. Matched on whole path segments, so
# `scripts/tests/...` and `.../tests/...` are both excluded while a source file
# that merely has "test" in its name is not.
TEST_TREE_PARTS = {"tests", "test", "__tests__", "testdata", "fixtures"}

# A citation must carry at least one `/` and end in `.md`. A bare `README.md` in
# a comment names no resolvable file (which directory?), so it is not a
# citation; the `\b` keeps `.mdx` from matching as `.md`. Every segment must
# START with a letter, digit or underscore (one leading dot allowed for
# `.claude/`), so a shape such as `docs/...md` -- how prose describes the pattern
# rather than citing a page -- does not match.
_SEGMENT = r"\.?[A-Za-z0-9_][A-Za-z0-9_.\-]*"
DOC_CITATION_PATTERN = re.compile(
    rf"(?<![\w./~-])((?:\.\.?/)*(?:{_SEGMENT}/)+{_SEGMENT}\.md)\b"
)

# Position markers that make the following text an OUTPUT of a command or a
# write call rather than a reference to a document that should exist.
_OUTPUT_MARKER_RE = re.compile(
    r"(?:--out(?:put|-dir)?|(?<![\w-])-o\s|(?<![-=])>(?!>)|>>|"
    r"open\(|write_text\(|write_bytes\(|savefig\(|to_csv\(|to_json\(|\.write\()",
    re.IGNORECASE,
)

# Line-comment / block-comment syntax per language. Lean nests its block
# comments (`/- /- -/ -/`), C# does not; getting this wrong on Lean would end a
# comment at the first inner `-/` and scan the rest of the block as code.
COMMENT_SYNTAX: dict[str, tuple[str, str, str, bool]] = {
    ".lean": ("--", "/-", "-/", True),
    ".cs": ("//", "/*", "*/", False),
}


def _is_test_tree(path: Path) -> bool:
    """Whether ``path`` lives in a test tree (fixtures are values, not claims)."""
    try:
        rel = path.relative_to(REPO_ROOT)
    except ValueError:
        return True
    if any(part.lower() in TEST_TREE_PARTS for part in rel.parts[:-1]):
        return True
    name = rel.name.lower()
    return name.startswith("test_") or name.endswith("_test.py")


def _repo_top_level() -> set[str]:
    """Names present at the repository root, recomputed per call.

    Recomputed rather than cached so a tmp-tree test that rebinds ``REPO_ROOT``
    gets its own answer instead of this machine's.
    """
    try:
        return {p.name for p in REPO_ROOT.iterdir()}
    except OSError:
        return set()


def _is_scoped_doc_citation(path: str, top_level: set[str]) -> bool:
    """Whether ``path`` is a citation of OUR tree, not of a third-party one.

    ``lean/docs/132.md`` is anchored at `lean`, which is not a top-level entry
    here -- it belongs to the upstream project the comment talks about, so it is
    out of scope. A `./`/`../` path is in scope: it resolves against the citing
    file, which is exactly what ``check_link`` will do.
    """
    first = path.split("/", 1)[0]
    if first in (".", ".."):
        return True
    return first in top_level


def _is_output_position(prefix: str) -> bool:
    """Whether the text before a path marks it as an output/write position."""
    return _OUTPUT_MARKER_RE.search(prefix) is not None


def _generic_comment_spans(
    content: str, line_marker: str, block_open: str, block_close: str,
    nestable: bool,
) -> list[tuple[int, str]]:
    """Comment text of a C-family/Lean source, as ``(line, text)`` pairs.

    A line marker preceded by an ODD number of `"` sits inside a string literal
    (`let s := "--"`), so it is not a comment. That guard is a heuristic, not a
    lexer; it covers the case that actually occurs and is documented as such.
    """
    spans: list[tuple[int, str]] = []
    depth = 0
    for lineno, line in enumerate(content.splitlines(), 1):
        buf: list[str] = []
        i = 0
        while i < len(line):
            if depth == 0:
                if line.startswith(block_open, i):
                    depth = 1
                    i += len(block_open)
                    continue
                if line.startswith(line_marker, i) and line[:i].count('"') % 2 == 0:
                    spans.append((lineno, line[i + len(line_marker):]))
                    break
                i += 1
                continue
            if nestable and line.startswith(block_open, i):
                depth += 1
                i += len(block_open)
                continue
            if line.startswith(block_close, i):
                depth -= 1
                i += len(block_close)
                continue
            buf.append(line[i])
            i += 1
        if buf:
            spans.append((lineno, "".join(buf)))
    return spans


def _python_comment_spans(content: str) -> list[tuple[int, str]]:
    """`#` comments (via ``tokenize``) plus module/class/function docstrings.

    ``tokenize`` is the only way to tell a `#` comment from a `#` inside a
    string literal; ``ast`` is the only way to tell a docstring from an
    arbitrary string expression. Both are stdlib and exact, which is why Python
    does not go through ``_generic_comment_spans``.
    """
    spans: list[tuple[int, str]] = []
    # A source that the interpreter would warn about (invalid escape sequences
    # in a legacy regex string, say) is still a source we must read. Parsing it
    # here must not spray SyntaxWarning on the organ's own output: the verdict
    # is a link report, not a lint of unrelated files.
    with warnings.catch_warnings():
        warnings.simplefilter("ignore", SyntaxWarning)
        try:
            for tok in tokenize.generate_tokens(io.StringIO(content).readline):
                if tok.type == tokenize.COMMENT:
                    spans.append((tok.start[0], tok.string))
        except (tokenize.TokenError, IndentationError, SyntaxError):
            pass

        try:
            tree = ast.parse(content)
        except (SyntaxError, ValueError):
            return spans
    owners = (ast.Module, ast.ClassDef, ast.FunctionDef, ast.AsyncFunctionDef)
    for node in ast.walk(tree):
        body = getattr(node, "body", None)
        if not isinstance(node, owners) or not body:
            continue
        first = body[0]
        if not (isinstance(first, ast.Expr)
                and isinstance(first.value, ast.Constant)
                and isinstance(first.value.value, str)):
            continue
        for offset, doc_line in enumerate(first.value.value.splitlines()):
            spans.append((first.lineno + offset, doc_line))
    return spans


def _comment_spans(suffix: str, content: str) -> list[tuple[int, str]]:
    """Comment text of ``content`` according to the language of ``suffix``."""
    if suffix == ".py":
        return _python_comment_spans(content)
    syntax = COMMENT_SYNTAX.get(suffix)
    if syntax is None:
        return []
    return _generic_comment_spans(content, *syntax)


def _git_tracked_code_files() -> list[str] | None:
    """Repo-relative code files git tracks, or None when git cannot be asked.

    The scope of this organ is what the REPOSITORY ships, not what a machine
    happens to have under its working tree: an unpruned walk of a developer
    checkout enumerated 93 876 `*.py|*.lean|*.cs` files against 4 339 tracked
    ones (measured 2026-11-04), i.e. it spent its time on installed packages.
    ``None`` keeps a tmp-tree test working: it rebuilds the engine over the
    pruned walk instead of reporting an empty scope.
    """
    proc = subprocess.run(
        ["git", "ls-files", "-z"],
        cwd=REPO_ROOT, capture_output=True, text=True,
        encoding="utf-8", errors="replace",
    )
    if proc.returncode != 0:
        return None
    return [p for p in proc.stdout.split("\0") if p.endswith(CODE_SCAN_SUFFIXES)]


def find_code_files() -> list[Path]:
    """Every scannable code file: tracked, non-test, outside skipped trees.

    Pruned at DIRECTORY level when git is unavailable rather than filtered
    afterwards: `.lake/` holds a full Mathlib checkout, so an unpruned
    ``rglob`` would enumerate thousands of files only to discard them.
    """
    tracked = _git_tracked_code_files()
    if tracked is not None:
        return [
            REPO_ROOT / rel for rel in sorted(tracked)
            if (REPO_ROOT / rel).is_file()
            and not _should_skip(REPO_ROOT / rel)
            and not _is_test_tree(REPO_ROOT / rel)
        ]

    files: list[Path] = []
    for dirpath, dirnames, filenames in os.walk(REPO_ROOT):
        rel_dir = Path(dirpath).relative_to(REPO_ROOT).as_posix()
        kept: list[str] = []
        for name in dirnames:
            if name in SKIP_DIRS or name.lower() in TEST_TREE_PARTS:
                continue
            child = name if rel_dir == "." else f"{rel_dir}/{name}"
            if any(child == sm or child.startswith(sm + "/") for sm in SUBMODULE_PATHS):
                continue
            kept.append(name)
        dirnames[:] = kept
        for name in filenames:
            if not name.endswith(CODE_SCAN_SUFFIXES):
                continue
            path = Path(dirpath) / name
            if _should_skip(path) or _is_test_tree(path):
                continue
            files.append(path)
    files.sort()
    return files


def _citation_exists(target: str, source_rel: str) -> bool:
    """Whether a code-comment citation resolves, under EITHER anchoring.

    A comment in `MyIA.AI.Notebooks/IIT/ICT-Series/ict/foo.py` writes
    `docs/ict/<page>.md` meaning the REPOSITORY ROOT; `check_link` resolves against
    the citing file's directory and calls every such citation dead (measured
    2026-11-04: 224 "broken" against 6 alive, while the issue's line-by-line
    reading found 30 dead of ~275). Both conventions are in use in this repo, so
    a citation is dead only when NEITHER anchor finds it. An explicit
    `./`/`../` path names one anchor only, and is not re-anchored at the root.
    """
    if check_link(target, REPO_ROOT / source_rel, root=REPO_ROOT):
        return True
    if target.startswith(("./", "../")):
        return False
    # A dummy source directly under REPO_ROOT makes check_link's `parent` the
    # root itself, reusing its decoding, submodule and Quarto rules verbatim
    # instead of growing a second existence oracle that could diverge. `root` is
    # passed explicitly: the default argument is bound at import time and would
    # not follow a rebound REPO_ROOT in tests.
    return check_link(target, REPO_ROOT / "__root_anchor__", root=REPO_ROOT)


def scan_code_content(content: str, rel_source: str) -> list[LinkRef]:
    """Doc paths cited in the comments of ``content`` (repo-relative source).

    Returns one ``LinkRef`` per distinct ``(line, target)``: the same path cited
    twice on one line is one citation, and a path repeated across the file keeps
    one occurrence per line so the report points at every place to fix.
    """
    # Cheap pre-filter before the lexers: a file without a single `.md` cannot
    # hold a doc citation, and tokenize+ast over 3 000 files costs ~70 s.
    if ".md" not in content:
        return []
    top_level = _repo_top_level()
    suffix = Path(rel_source).suffix.lower()
    seen: set[tuple[int, str]] = set()
    refs: list[LinkRef] = []
    for lineno, text in _comment_spans(suffix, content):
        for match in DOC_CITATION_PATTERN.finditer(text):
            target = match.group(1)
            if not _is_scoped_doc_citation(target, top_level):
                continue
            if _is_output_position(text[:match.start()]):
                continue
            key = (lineno, target)
            if key in seen:
                continue
            seen.add(key)
            refs.append(LinkRef(
                source=rel_source, target=target, line=lineno, text="doc citation",
            ))
    return refs


def scan_code_file(filepath: Path) -> list[LinkRef]:
    """Doc paths cited in the comments of a code file on disk."""
    try:
        content = filepath.read_text(encoding="utf-8")
    except (UnicodeDecodeError, PermissionError, OSError):
        return []
    try:
        rel_source = filepath.relative_to(REPO_ROOT).as_posix()
    except ValueError:
        rel_source = str(filepath)
    return scan_code_content(content, rel_source)


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


def _citation_exists_in_tree(target: str, source_rel: str, files: set[str],
                             dirs: set[str], quarto_yml: str | None) -> bool:
    """``_link_exists_in_tree`` under both anchors, as ``_citation_exists``."""
    if _link_exists_in_tree(target, source_rel, files, dirs, quarto_yml):
        return True
    if target.startswith(("./", "../")):
        return False
    # An empty dirname makes ``posixpath.join`` yield the target unchanged, i.e.
    # resolved against the repository root -- the second anchor.
    return _link_exists_in_tree(target, "__root_anchor__", files, dirs, quarto_yml)


def preexisting_broken(broken_refs: list[LinkRef], rev: str,
                       scanner: Callable[[str, str], list[LinkRef]] = scan_content,
                       exists_in_tree: Callable[..., bool] = _link_exists_in_tree,
                       ) -> set[tuple[str, str]] | None:
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
        base_targets = {r.target for r in scanner(content, source)}
        for target in targets:
            if target in base_targets and not exists_in_tree(
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


def run_scan(report_orphans: bool = False, code: bool = False) -> ScanResult:
    """Run a full scan across the repository.

    ``code=True`` runs the code-comment citation pass (#24410) INSTEAD of the
    markdown pass -- not in addition to it. The two verdicts are kept apart on
    purpose: `main` already carries broken markdown links that the frozen
    baseline does not excuse (measured 2026-11-03), so folding a new signal into
    the same count would make a code finding indistinguishable from that
    pre-existing red, which is exactly what #24410 warns against.
    """
    result = ScanResult()
    files = find_code_files() if code else find_scan_files()
    result.scanned_files = len(files)

    all_refs = []
    for filepath in files:
        refs = scan_code_file(filepath) if code else scan_file(filepath)
        all_refs.extend(refs)

    result.total_links = len(all_refs)

    for ref in all_refs:
        if code:
            ok = _citation_exists(ref.target, ref.source)
        else:
            ok = check_link(ref.target, REPO_ROOT / ref.source)
        (result.valid if ok else result.broken).append(ref)

    if report_orphans and not code:
        result.orphans = find_orphan_docs(files, all_refs)
    # In code mode `--orphans` is meaningless (orphan detection asks which PAGE
    # links to a doc; a comment is not a page) and leaves `orphans` empty --
    # main() refuses the combination rather than printing "0 orphans", which
    # would read as a clean result from an unscanned question.

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


def _is_generated_source(source: Path) -> bool:
    """Detect a generated page by its header, not by a hardcoded path.

    A content branch must leave generated artifacts unchanged: the catalogue
    cron repairs their links after the merge (#22651). Only the explicit
    production header grants this excuse; prose mentioning generation later in
    a hand-written page does not.
    """
    try:
        with source.open(encoding="utf-8") as handle:
            prefix = handle.read(4096)
    except (OSError, UnicodeDecodeError):
        return False
    header = re.match(r"\s*<!--(.*?)-->", prefix, re.DOTALL)
    if header is None:
        return False
    return re.search(r"\bFICHIER GENERE\b", header.group(1), re.IGNORECASE) is not None


def generated_source_excuses(result: ScanResult) -> list[LinkRef]:
    """Broken links carried by explicitly generated source pages."""
    return [
        ref for ref in result.broken
        if _is_generated_source(REPO_ROOT / ref.source)
    ]


def check_regression(result: ScanResult, baseline: dict,
                     preexisting: set[tuple[str, str]] | None = None) -> list[LinkRef]:
    """Find broken links that are NOT already excused (new regressions).

    The frozen baseline and comparison revision excuse pre-existing defects.
    A generated source carries a third, visible excuse: repairing it on the
    branch is forbidden by catalogue hygiene, and its cron regenerates it after
    the merge (#22651).
    """
    baseline_targets = {
        (b["source"], b["target"]) for b in baseline.get("broken_links", [])
    }
    excused = baseline_targets | (preexisting or set())
    excused.update((ref.source, ref.target)
                   for ref in generated_source_excuses(result))
    return [ref for ref in result.broken if (ref.source, ref.target) not in excused]


def format_generated_excuses(refs: list[LinkRef]) -> str:
    """Report generated-source excuses separately, never silently."""
    lines = [f"Excused: {len(refs)} generated source"]
    lines.extend(f"  {ref.source}:{ref.line} -> {ref.target}"
                 for ref in sorted(refs, key=lambda r: (r.source, r.line)))
    return "\n".join(lines)


def format_report(result: ScanResult, show_orphans: bool = False,
                  code: bool = False) -> str:
    """Format scan results as a human-readable report."""
    lines = []
    noun = "doc citations in code comments" if code else "links"
    lines.append(f"Scanned {result.scanned_files} files, {result.total_links} {noun}")

    if result.broken:
        lines.append(f"\nBroken {noun} ({len(result.broken)}):")
        for ref in sorted(result.broken, key=lambda r: (r.source, r.line)):
            lines.append(f"  {ref.source}:{ref.line} -> {ref.target}")
    else:
        lines.append(f"\nNo broken {noun} found.")

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
    parser.add_argument("--code", action="store_true",
                        help="Scan doc paths cited in CODE COMMENTS (.py/.lean/"
                             ".cs) instead of markdown links. Kept separate so a "
                             "code finding is never confused with a markdown "
                             "one; --check/--base/--baseline/--expect-broken all "
                             "apply to the selected pass (#24410).")
    parser.add_argument("--quiet", action="store_true",
                        help="Minimal output")
    parser.add_argument("--expect-broken", metavar="N", type=int, default=None,
                        help="Positive control: require at least N broken links, "
                             "else exit 2. Without it, 'no broken link' is "
                             "indistinguishable from a dead detection path.")
    args = parser.parse_args()

    if args.code and args.orphans:
        print("Error: --orphans is meaningless with --code -- orphan detection "
              "asks which PAGE links to a doc, and a code comment is not a page.",
              file=sys.stderr)
        sys.exit(2)

    baseline_path = CODE_BASELINE_PATH if args.code else BASELINE_PATH

    try:
        result = run_scan(report_orphans=args.orphans, code=args.code)

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
            write_baseline(result, path=baseline_path)
            if not args.quiet:
                print(f"Baseline written to {baseline_path}")
                print(format_report(result, show_orphans=not args.code,
                                    code=args.code))
            return

        if args.check:
            preexisting = None
            if args.base:
                if args.code:
                    preexisting = preexisting_broken(
                        result.broken, args.base,
                        scanner=scan_code_content,
                        exists_in_tree=_citation_exists_in_tree,
                    )
                else:
                    preexisting = preexisting_broken(result.broken, args.base)
                if preexisting is None and not args.quiet:
                    print(f"WARNING: {args.base!r} is not readable, comparing against the "
                          f"frozen baseline only.", file=sys.stderr)

            baseline = load_baseline(path=baseline_path)
            if baseline is None and preexisting is None:
                if not args.quiet:
                    print(f"No baseline found at {baseline_path}. Run with "
                          f"--baseline first.")
                # Nothing can excuse a broken link: every one is a regression
                if result.broken:
                    if not args.quiet:
                        print(format_report(result, code=args.code))
                    sys.exit(1)
                sys.exit(0)

            new_broken = check_regression(result, baseline or {}, preexisting)
            generated = generated_source_excuses(result)
            if generated:
                print(format_generated_excuses(generated))
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
            print(format_report(result, show_orphans=args.orphans, code=args.code))

        if result.broken:
            sys.exit(1)
        sys.exit(0)

    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(2)


if __name__ == "__main__":
    main()
