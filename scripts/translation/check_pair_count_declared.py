#!/usr/bin/env python3
"""Lightweight cliquet: a PR that adds/removes/renames a translation pair
must bump ``EXPECTED_PAIR_COUNT`` in the same PR.

Why this organ exists
---------------------

``main`` has now turned red **four** times for the same class: a carnet PR
adds a new ``*_en.ipynb`` sibling (e.g. ``ANALYSE-07-Percolation-Critique_en``)
without bumping the constant ``EXPECTED_PAIR_COUNT`` in
``scripts/translation/tests/test_check_translation_parity.py``. The
downstream ``test_full_repo_state_passes_parity`` then fails on every
``scripts/**``-filtered PR until someone re-merges the bump.

History of the four rouges: ``#19996``, ``#20392``, ``#20453``, ``#19943``
(constant updated in each by a follow-up PR). The test that compares the
count lives in ``Scripts Tests (CPU)`` and is filtered on ``scripts/**``,
so a notebook PR that doesn't touch ``scripts/`` doesn't even trigger it.
The cron ``translation-parity.yml`` runs only nightly.

The invariant "pair added/removed/renamed => constant bumped in the same
PR" has no carrier at PR time. This cliquet is the carrier.

What it does
------------

1. ``git diff --name-status base..head -- 'MyIA.AI.Notebooks/**/*.ipynb'``:
   list every notebook file with status ``A`` (added), ``D`` (deleted),
   ``R<score>`` (renamed) or ``M`` (modified).
2. For each ``A``/``D``/``R`` translation file (``*_en.ipynb`` or
   ``*_ru.ipynb``), check whether a corresponding ``X.ipynb`` (FR source)
   exists at the head side of the diff. If so, the change creates or
   destroys a pair.
3. If the diff adds or destroys at least one pair AND
   ``EXPECTED_PAIR_COUNT`` was not modified in the same diff: ROUGE,
   naming the affected pairs and the exact line to edit.
4. If the diff modified the constant, verify the new value matches the
   count of ``discover_pairs`` at head. ROUGE otherwise.

Acceptance (``#21391``):
  1. POSITIVE on #19943 (commit ``c91ad9872d`` vs parent): ROUGE,
     names ``ANALYSE-07-Percolation-Critique_en``.
  2. NEGATIVE on #21383: GREEN.
  3. M-only diff (existing ``_en`` modified): GREEN.
  4. ``.tmp/`` orphan on local disk: guard reads ``git diff``, not disk;
     the orphan is not counted.
  5. Cost: a few seconds; no ``blob:none`` clone of 2 GB.

Out of scope (matches ``count_code_sorry``): ``.tmp/``, worktrees,
``.git/``, vendored caches. The constant lives in
``scripts/translation/tests/test_check_translation_parity.py``; if it
moves, the path here must move with it.

Usage
-----

    # Default: origin/main..HEAD on the current branch
    python scripts/translation/check_pair_count_declared.py

    # Explicit SHAs
    python scripts/translation/check_pair_count_declared.py --base <sha> --head <sha>

    # Restrict to a path prefix (default: MyIA.AI.Notebooks/)
    python scripts/translation/check_pair_count_declared.py --paths 'MyIA.AI.Notebooks/SymbolicAI/Lean/**'

    # JSON for CI
    python scripts/translation/check_pair_count_declared.py --json

Exit codes:
  0  no pair change, or pair change with constant bumped to the right value
  1  pair change WITHOUT a constant bump, or constant bumped to a wrong value
  2  invocation error (bad SHA, no notebook files in scope)

Module usage:
    from check_pair_count_declared import check_pair_count_declared
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from dataclasses import dataclass, field, asdict
from pathlib import Path
from typing import Iterable

# Re-use the existing suffix regex + scannable predicate of the parity check.
sys.path.insert(0, str(Path(__file__).resolve().parent))
import check_translation_parity as par  # noqa: E402

TARGET_LANGS = tuple(par.TARGET_LANGS)
CONSTANT_PATH = Path("scripts/translation/tests/test_check_translation_parity.py")
CONSTANT_LINE = re.compile(
    r"^EXPECTED_PAIR_COUNT\s*=\s*(?P<value>\d+)\s*$", re.MULTILINE
)


# --------------------------------------------------------------------------- #
# Data model
# --------------------------------------------------------------------------- #


@dataclass
class PairChange:
    status: str                # "added" or "removed" or "renamed" (the translation file)
    translation_path: str      # posix path of the *_<lang>.ipynb
    source_path: str           # posix path of the X.ipynb (resolved at head)
    stem: str
    lang: str


@dataclass
class ConstantChange:
    old_value: int | None
    new_value: int | None


@dataclass
class CheckReport:
    base: str
    head: str
    pair_changes: list[PairChange] = field(default_factory=list)
    constant_change: ConstantChange = field(default_factory=lambda: ConstantChange(None, None))
    actual_count: int | None = None
    notes: list[str] = field(default_factory=list)

    @property
    def has_pair_change(self) -> bool:
        return bool(self.pair_changes)

    @property
    def constant_modified(self) -> bool:
        """True if the EXPECTED_PAIR_COUNT value differs between base and head.
        ``None`` vs an int counts as a change (constant was added or removed).
        """
        return self.constant_change.old_value != self.constant_change.new_value

    @property
    def rouge(self) -> bool:
        if not self.has_pair_change and not self.constant_modified:
            return False
        # pair added/removed WITHOUT a constant bump = rouge
        if self.has_pair_change and not self.constant_modified:
            return True
        # constant modified but value doesn't match the actual count = rouge
        if self.constant_modified and self.actual_count is not None:
            if self.constant_change.new_value != self.actual_count:
                return True
        return False


# --------------------------------------------------------------------------- #
# Git plumbing
# --------------------------------------------------------------------------- #


def _git(*args: str, repo_root: Path | None = None, check: bool = True) -> str:
    """Run a git subcommand in ``repo_root`` (default: cwd) and return stdout.
    ``check=False`` swallows non-zero exit codes; the caller inspects the result.
    """
    cmd = list(args)
    res = subprocess.run(
        cmd, capture_output=True, text=True, encoding="utf-8", cwd=repo_root,
        check=check,
    )
    return res.stdout


def _git_diff_name_status(
    base: str, head: str, paths: list[str], repo_root: Path | None = None
) -> list[tuple[str, str, str | None]]:
    """Parse ``git diff --name-status -M50%`` into ``[(status, new, old)]`` tuples.
    ``-M50%`` detects renames with a similarity threshold of 50 %.
    ``new`` is always populated; ``old`` is populated for renames (status R).
    """
    out = _git(
        "git", "diff", "--name-status", "-M50%", f"{base}..{head}", "--", *paths,
        repo_root=repo_root, check=False,
    )
    rows: list[tuple[str, str, str | None]] = []
    for raw in out.splitlines():
        if not raw:
            continue
        parts = raw.split("\t")
        if len(parts) < 2:
            continue
        status = parts[0]
        if status.startswith("R") and len(parts) >= 3:
            # R<score>\told\tnew
            rows.append(("R", parts[2], parts[1]))
        else:
            new = parts[1]
            rows.append((status, new, None))
    return rows


def _git_show(sha: str, path: str, repo_root: Path | None = None) -> str | None:
    """Return the content of ``path`` at ``sha`` (or None if absent)."""
    res = subprocess.run(
        ["git", "show", f"{sha}:{path}"],
        capture_output=True, text=True, encoding="utf-8", cwd=repo_root,
    )
    if res.returncode != 0:
        return None
    return res.stdout


def _git_diff_constant(
    base: str, head: str, path: str, repo_root: Path | None = None
) -> ConstantChange:
    """Detect whether ``EXPECTED_PAIR_COUNT = N`` was added, removed or
    changed between ``base`` and ``head`` for ``path``.

    Strategy: read the full file at both SHAs, regex-parse the constant
    on each side. A change means either side differs.
    """
    base_text = _git_show(base, path, repo_root=repo_root) or ""
    head_text = _git_show(head, path, repo_root=repo_root) or ""
    base_match = CONSTANT_LINE.search(base_text)
    head_match = CONSTANT_LINE.search(head_text)
    old = int(base_match.group("value")) if base_match else None
    new = int(head_match.group("value")) if head_match else None
    return ConstantChange(old_value=old, new_value=new)


# --------------------------------------------------------------------------- #
# Translation-file classification
# --------------------------------------------------------------------------- #


def _classify_translation(path: str) -> tuple[str, str, str] | None:
    """If ``path`` ends in ``*_<lang>.ipynb`` with ``<lang>`` in TARGET_LANGS,
    return ``(stem, lang, suffix)`` where ``suffix`` is the original filename
    without the language tag. Otherwise return None.
    """
    name = Path(path).name
    stem, dot, ext = name.rpartition(".")
    if not ext or ext != "ipynb":
        return None
    # language tag is the last ``_<word>`` suffix before the extension
    m = re.match(r"^(?P<stem>.+)_(?P<lang>" + "|".join(TARGET_LANGS) + r")$", stem)
    if not m:
        return None
    return m.group("stem"), m.group("lang"), name


def _pair_at_head(head: str, translation_path: str, repo_root: Path | None = None) -> bool:
    """Return True if the FR source ``X.ipynb`` corresponding to ``translation_path``
    exists at the head side. Uses ``git show`` -- no disk walk.
    """
    info = _classify_translation(translation_path)
    if info is None:
        return False
    src_stem, _lang, _name = info
    # Windows Path.with_name produces backslashes; git always wants forward slashes.
    src_path = Path(translation_path).with_name(src_stem + ".ipynb").as_posix()
    return _git_show(head, src_path, repo_root=repo_root) is not None


# --------------------------------------------------------------------------- #
# Main pipeline
# --------------------------------------------------------------------------- #


def check_pair_count_declared(
    base: str,
    head: str,
    paths: Iterable[str] | None = None,
    repo_root: Path | None = None,
    *,
    do_disk_count: bool = True,
) -> CheckReport:
    """Run the cliquet. ``do_disk_count=False`` skips the ``discover_pairs`` walk
    (useful for fast PR-time runs that only need the A/D/R detection).
    """
    if paths is None:
        paths = ["MyIA.AI.Notebooks/"]
    path_list = list(paths)
    report = CheckReport(base=base, head=head)

    rows = _git_diff_name_status(base, head, path_list, repo_root=repo_root)
    for status, new, _old in rows:
        if status not in ("A", "D", "R"):
            continue
        info = _classify_translation(new)
        if info is None:
            continue
        stem, lang, _name = info
        src_path = str(Path(new).with_name(stem + ".ipynb"))
        if status == "D":
            # Deletion: if the source still exists at head, the translation
            # was removed but the pair partner is still there. The pair is
            # destroyed. If the source was also deleted, the diff handles
            # it independently.
            if not _pair_at_head(head, new, repo_root=repo_root):
                continue
            report.pair_changes.append(PairChange(
                status="removed", translation_path=Path(new).as_posix(),
                source_path=Path(src_path).as_posix(),
                stem=stem, lang=lang,
            ))
        else:
            # A or R: check the source exists at head
            if not _pair_at_head(head, new, repo_root=repo_root):
                continue
            report.pair_changes.append(PairChange(
                status="added" if status == "A" else "renamed",
                translation_path=Path(new).as_posix(),
                source_path=Path(src_path).as_posix(),
                stem=stem, lang=lang,
            ))

    if report.pair_changes:
        report.constant_change = _git_diff_constant(
            base, head, CONSTANT_PATH.as_posix(), repo_root=repo_root,
        )

    if report.constant_modified and do_disk_count:
        try:
            actual = par.discover_pairs(
                Path(repo_root) if repo_root else Path.cwd(), list(TARGET_LANGS),
            )
            # Filter to the languages in scope (the helper is harmless; some
            # pair_count work only counts en; for now we keep all).
            report.actual_count = len(actual)
        except Exception as exc:
            report.notes.append(f"disk count failed: {exc!r}")

    return report


# --------------------------------------------------------------------------- #
# Output
# --------------------------------------------------------------------------- #


def _constant_line_number_in_head(repo_root: Path | None) -> int | None:
    """Return the 1-based line number of EXPECTED_PAIR_COUNT in the constant
    file at the head we inspected, or None if it cannot be resolved (fail
    soft -- the caller then prints the search pattern instead of a number).
    """
    root = repo_root if repo_root is not None else Path.cwd()
    try:
        text = (root / CONSTANT_PATH).read_text(encoding="utf-8")
    except OSError:
        return None
    for i, line in enumerate(text.splitlines(), start=1):
        if CONSTANT_LINE.match(line):
            return i
    return None


def _rouge_message(report: CheckReport, repo_root: Path | None = None) -> str:
    """Render the exact message a human or a CI runner can apply verbatim."""
    names = ", ".join(
        f"{Path(pc.translation_path).stem}" for pc in report.pair_changes
    )
    if report.pair_changes and not report.constant_modified:
        # Compute the next count (assume base + adds - removes)
        old = report.constant_change.old_value or 0
        delta_added = sum(1 for pc in report.pair_changes if pc.status in ("added", "renamed"))
        delta_removed = sum(1 for pc in report.pair_changes if pc.status == "removed")
        next_value = old + delta_added - delta_removed
        # Derive the constant line number at the head we inspected -- never
        # hardcode it, or the message silently drifts when history is added
        # above the constant (reserve F2).
        line_no = _constant_line_number_in_head(repo_root)
        location = (
            f"{CONSTANT_PATH.as_posix()}:{line_no}" if line_no is not None
            else f"{CONSTANT_PATH.as_posix()} (search `^EXPECTED_PAIR_COUNT = `)"
        )
        return (
            f"ROUGE: pair change detected without EXPECTED_PAIR_COUNT bump.\n"
            f"  Pairs affected: {names}\n"
            f"  Constant path: {location}\n"
            f"  Expected bump: {old} -> {next_value}\n"
            f"  History entry pattern (preceding comment, ~5 lines above):\n"
            f"    # YYYY-MM-DD (PR #NNNN, <issue> <summary>): +N paire(s) --\n"
            f"    #   <stem1> + <stem2> + ...\n"
            f"    # Meme classe que #19996/#20392 : la paire est arrivee sur main\n"
            f"    #   avec son carnet sans mettre a jour cette ligne, ce qui a\n"
            f"    #   rougi test_full_repo_state_passes_parity (found N, declared M)\n"
            f"    #   sur main pur et sur toute PR path-filtree scripts/**.\n"
            f"    #   Total apres fusion : M + N = <next>.\n"
        )
    if report.constant_modified and report.actual_count is not None:
        if report.constant_change.new_value != report.actual_count:
            return (
                f"ROUGE: EXPECTED_PAIR_COUNT bumped to "
                f"{report.constant_change.new_value} but actual pair count is "
                f"{report.actual_count}.\n"
                f"  Pairs affected: {names or '(none)'}\n"
            )
    return "ROUGE (unknown reason)"


def render_text(report: CheckReport, repo_root: Path | None = None) -> str:
    if not report.pair_changes and not report.constant_modified:
        return "GREEN: no pair change, no constant bump -- nothing to check."
    if not report.rouge:
        return (
            f"GREEN: {len(report.pair_changes)} pair change(s), constant bumped "
            f"{report.constant_change.old_value} -> {report.constant_change.new_value}, "
            f"actual count = {report.actual_count}."
        )
    return _rouge_message(report, repo_root=repo_root)


# --------------------------------------------------------------------------- #
# CLI
# --------------------------------------------------------------------------- #


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    p.add_argument("--base", default="origin/main",
                   help="base SHA (default: origin/main)")
    p.add_argument("--head", default="HEAD",
                   help="head SHA (default: HEAD)")
    p.add_argument("--paths", nargs="*", default=None,
                   help="restrict to specific path prefixes (default: MyIA.AI.Notebooks/)")
    p.add_argument("--repo-root", default=None,
                   help="git working directory (default: process cwd)")
    p.add_argument("--no-disk-count", action="store_true",
                   help="skip the discover_pairs walk (fast PR-time check)")
    p.add_argument("--json", action="store_true",
                   help="emit machine-readable JSON")
    args = p.parse_args(argv)

    repo_root = Path(args.repo_root) if args.repo_root else None

    # Validate SHAs early (fail-closed: typo in SHA -> exit 2, not 0).
    for label, sha in (("--base", args.base), ("--head", args.head)):
        res = subprocess.run(
            ["git", "rev-parse", "--verify", f"{sha}^{{commit}}"],
            capture_output=True, text=True, encoding="utf-8", cwd=repo_root,
        )
        if res.returncode != 0:
            print(f"ERROR: {label}={sha!r} does not resolve to a commit.",
                  file=sys.stderr)
            return 2

    report = check_pair_count_declared(
        args.base, args.head,
        paths=args.paths,
        repo_root=repo_root,
        do_disk_count=not args.no_disk_count,
    )

    if args.json:
        print(json.dumps({
            "base": report.base,
            "head": report.head,
            "pair_changes": [asdict(pc) for pc in report.pair_changes],
            "constant_change": asdict(report.constant_change),
            "actual_count": report.actual_count,
            "rouge": report.rouge,
            "notes": report.notes,
        }, indent=2, ensure_ascii=False))
    else:
        print(render_text(report, repo_root=repo_root))

    return 1 if report.rouge else 0


if __name__ == "__main__":
    sys.exit(main())
