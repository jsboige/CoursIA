#!/usr/bin/env python3
"""Measure pedagogy DENSITY (prose per code cell) per notebook (#10479 Grain 2).

The user's observation (2026-08-11) was that the introductive part of a series
can lack pedagogical notes in markdown. The metric the user proposed --
percentage of markdown -- was MEASURED and detects nothing: on the five
incriminated Lean notebooks the markdown share was 44-51%, with no run of >=3
code cells without prose between. The metric that discriminates is **chars of
prose per code cell** -- how much text accompanies each thing to explain:

    chars / cellule code = sum(len(markdown cell sources)) / count(code cells)

Calibration (this tool's definition, verified against the issue table): for
every notebook published in #10479, the raw ``len()`` of the joined markdown
sources divided by the code-cell count reproduces the published value EXACTLY
(Lean-15b 1126=1126, Lean-13 1985=1985; and the post-enrichment values
Lean-2 1620, Lean-4 2100, Lean-5 1039, Lean-6 1263 on the enriched files).
Whitespace and newlines count: the length is the raw source length.

This is the missing ORGAN for that observation: it wires the density measure to
PRs, exactly as check_pr_exercises.py did for the >=3 exercises convention
(#8814). It is ADVISORY by design (issue #10479 acceptance): it always exits 0;
the actionable payload is the ``pedagogy-density-below-threshold`` LABEL the
workflow poses, never the green conclusion of the job (green by construction --
the same trap that let #8797 through for exercises).

Consumes, never re-implements, the corpus/kind classification of
``count_exercises.py`` (issue #10479 acceptance): the out-of-corpus kinds
(artifact/template/vendored/archive/legacy/tooling/student) and the setup
exemption are imported, not duplicated -- the label and the canonical tool must
not diverge. The density floor applies to the ``standard`` AND ``lean`` kinds
(the series that motivated the issue is a Lean series); a ``setup`` notebook is
exempt (environment scaffolding has no prose budget); an out-of-corpus notebook
is exempt. The md% share is REPORTED but never the criterion (measured: it
cannot discriminate).

A SECOND label, ``pedagogy-density-unmeasured``, covers notebooks the tool could
not read (JSON parse failure) or that have no code cell to divide by. This is
the #8819 lesson applied to density: "I could not measure" and "I measured, it
is below threshold" call for different reactions, so they never collapse into
one label -- and the summary never claims conformity while ``unmeasured > 0``.

Usage:
    python pedagogy_density.py                                   # whole corpus
    python pedagogy_density.py MyIA.AI.Notebooks/SymbolicAI/Lean # one family
    python pedagogy_density.py path/to/a.ipynb path/to/b.ipynb   # explicit
    python pedagogy_density.py --paths a.ipynb --json
    git diff --name-only BASE HEAD -- '*.ipynb' \\
        | python pedagogy_density.py --stdin --json

Always exits 0 (advisory): the signal is the label, not this exit code.
Sole exception -- ``--check-orphans`` exits 1 when the baseline and the tracked
tree disagree in a way that costs the ratchet a reference: #13815
``ORPHAN_KEY`` (a key with no file) or #16122 ``LOST_KEY`` (a rename that
deleted a key instead of moving it -- the #15917 regression). It also REPORTS
``UNKEYED_FILE``, the inventory of judged notebooks the baseline does not key;
that inventory is not a failure (measured: mostly notebooks added after the
baseline freeze, never under the ratchet). That mode is a correctness check,
not a pedagogical judgement: its non-zero is a verdict, never a crash. Each
direction is printed under its own label so the message names which question
failed.
"""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import asdict, dataclass, field
from pathlib import Path

# Import the canonical classification rather than re-implementing it (issue
# #10479 acceptance: the two must not diverge).
_TOOLS_DIR = Path(__file__).resolve().parent
if str(_TOOLS_DIR) not in sys.path:
    sys.path.insert(0, str(_TOOLS_DIR))

from count_exercises import (  # noqa: E402
    EXCLUDE_DIRS,
    NOTEBOOKS_DIR,
    OUT_OF_CORPUS_KINDS,
    classify_notebook,
)

#: The density floor: chars of markdown prose per code cell. Calibrated on the
#: Lean series (#10479): the five language-teaching notebooks stood at 303-550
#: chars/code-cell vs ~2000 in the applied notebooks; the floor is the bottom
#: of the applied band (Lean-18 at 1056, Lean-15b at 1126), not its mean (a
#: homage-notebook target unsuited to a learning notebook).
DENSITY_THRESHOLD = 1200

#: Kinds judged against the density floor. ``standard`` is the ordinary course
#: notebook; ``lean`` stays in the density corpus even though the exercises
#: rule exempts it (0-2) -- the series that motivated this organ IS a Lean
#: series, so exempting Lean would make the tool detect nothing where it is
#: needed. The exercises exemption and the density exemption are different
#: rules with different rationales; each consumes ``classify_notebook`` and
#: applies its own judgment on top.
DENSITY_JUDGED_KINDS = frozenset({"standard", "lean"})

#: Label for "measured, below the density floor" (issue #10479 acceptance).
LABEL_NAME = "pedagogy-density-below-threshold"
#: A SECOND, distinct label for notebooks the tool could NOT measure (issue
#: #8819 lesson, transposed): unparseable JSON or zero code cells. Never
#: collapsed into the below-threshold label.
LABEL_UNMEASURED = "pedagogy-density-unmeasured"

#: Baseline file (issue #10479 amendment, 2026-08-11 19:31Z): the tool records
#: the density of every tracked pedagogical notebook from Phase 1 onward, so
#: the Phase-2 regression ratchet ("do not grow") is never retro-fitted on an
#: already-reworked corpus. The metric is CONTINUOUS (float per notebook), not
#: a set of hashes. Population derives from `git ls-files` (amendment
#: 19:40Z), never an rglob -- untracked files would silently skew it.
BASELINE_FILE = _TOOLS_DIR / "pedagogy_density_baseline.json"

#: A UNKEYED_FILE is reported for every judged notebook the baseline does not
#: key, because that is the population the ratchet silently exempts (#16122).
#: It is NOT what the gate fails on, and the distinction is measured, not
#: stylistic: on 2026-09-15 the baseline holds 811 keys while the judged tracked
#: population is 1094, and the 283 un-keyed notebooks were almost all ADDED on
#: 2026-09-07..13 -- i.e. after the 2026-08-11 freeze ("burn down, do not grow",
#: confirmed over 7 baseline-touching commits whose ``count`` stayed 811 through
#: two large rename waves). Failing on the inventory would therefore redden every
#: PR that ADDS a notebook -- a brand-new notebook was never under the ratchet,
#: so its absence weakens nothing -- and the fleet would inherit a gate that
#: cries on its most common change.
#:
#: What the gate DOES fail on is the regression the #15917 incident actually
#: produced: a notebook that HELD a key and lost it while remaining tracked
#: (a renumber whose key was deleted rather than moved). That one is a real loss
#: -- the ratchet drops a reference it used to hold -- and it is detectable
#: exactly, by pairing the baseline's keys with git's rename detection against
#: the change's base (``--base``), so it needs no allowance file and cannot be
#: confused with the growth of the corpus.


@dataclass
class DensityVerdict:
    """One notebook's density verdict, with the evidence the label needs."""

    path: str
    kind: str
    exempt: bool  # exempt from the density floor (out of corpus, or setup)
    threshold: int  # the floor it would be judged against (1200), for display
    prose_chars: int  # total markdown source chars
    code_cells: int
    md_cells: int
    density: int | None  # chars per code cell; None if exempt or unmeasured
    md_pct: float | None  # reported, never the criterion (#10479 measurement)
    status: str  # 'below_threshold' | 'ok' | 'exempt' | 'unmeasured'
    detail: str = ""


@dataclass
class DensityResult:
    """Aggregate verdict over all scanned notebooks."""

    below_threshold: list[DensityVerdict] = field(default_factory=list)
    ok: list[DensityVerdict] = field(default_factory=list)
    exempt: list[DensityVerdict] = field(default_factory=list)
    unmeasured: list[DensityVerdict] = field(default_factory=list)

    def as_payload(self) -> dict:
        """Machine-readable payload for the workflow to decide the labels.

        Issue #8819 applied to density: a notebook the tool could not measure is
        NOT conforming -- it is UNMEASURED. The summary exposes ``unmeasured``
        FIRST, and carries TWO labels: ``below_threshold`` (measured, below the
        floor) and ``unmeasured`` (could not measure). The workflow raises each
        when its count is > 0 and never claims "all meet the floor" while
        ``unmeasured > 0``.
        """
        n_below = len(self.below_threshold)
        n_un = len(self.unmeasured)
        n_ok = len(self.ok)
        n_exempt = len(self.exempt)
        return {
            "labels": {
                "below_threshold": {"name": LABEL_NAME, "count": n_below},
                "unmeasured": {"name": LABEL_UNMEASURED, "count": n_un},
            },
            "summary": {
                # unmeasured FIRST: a glance makes the gap obvious (#8819).
                "unmeasured": n_un,
                "total": n_below + n_ok + n_exempt + n_un,
                "judged": n_below + n_ok + n_un,  # subject to the floor
                "exempt": n_exempt,  # out of corpus, or setup
                "below_threshold": n_below,
            },
            "below_threshold": [asdict(v) for v in self.below_threshold],
            "ok": [asdict(v) for v in self.ok],
            "exempt": [asdict(v) for v in self.exempt],
            "unmeasured": [asdict(v) for v in self.unmeasured],
        }


def _cell_source(cell: dict) -> str:
    """The cell source as one string (nbformat may store a list of lines)."""
    src = cell.get("source", "")
    if isinstance(src, list):
        return "".join(src)
    return src or ""


def _measure(path: Path) -> tuple[int, int, int, int]:
    """Return ``(prose_chars, code_chars, n_code, n_md)`` for a notebook.

    ``prose_chars`` is the raw length of every markdown cell source -- the
    definition calibrated against the #10479 table (whitespace and newlines
    count). ``code_chars`` (raw length of every code cell source) feeds the
    REPORTED markdown share. Raises ValueError on JSON parse failure.
    """
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:  # unreadable = unmeasured
        raise ValueError(f"cannot parse: {exc}") from exc
    md_chars = 0
    code_chars = 0
    n_code = 0
    n_md = 0
    for cell in data.get("cells", []):
        ctype = cell.get("cell_type")
        if ctype == "markdown":
            md_chars += len(_cell_source(cell))
            n_md += 1
        elif ctype == "code":
            code_chars += len(_cell_source(cell))
            n_code += 1
    return md_chars, code_chars, n_code, n_md


def check_paths(paths: list[Path]) -> DensityResult:
    """Classify + measure each path, bucketing by density status.

    A notebook is ``below_threshold`` only when it is a density-judged kind
    (standard or lean), measurable (>=1 code cell, parseable), and its
    chars-per-code-cell is below :data:`DENSITY_THRESHOLD`. A ``setup`` or
    out-of-corpus notebook is exempt -- the classification is CONSUMED from
    ``count_exercises.py``, not re-decided here.
    """
    result = DensityResult()
    for path in paths:
        kind, _ = classify_notebook(path)
        exempt = kind in OUT_OF_CORPUS_KINDS or kind == "setup"
        if exempt:
            result.exempt.append(
                DensityVerdict(
                    path=str(path), kind=kind, exempt=True,
                    threshold=DENSITY_THRESHOLD, prose_chars=0, code_cells=0,
                    md_cells=0, density=None, md_pct=None, status="exempt",
                    detail=(
                        f"exempt from the density floor (kind={kind}) -- "
                        "the rule does not apply"
                    ),
                )
            )
            continue
        try:
            prose_chars, code_chars, n_code, n_md = _measure(path)
        except ValueError as exc:
            result.unmeasured.append(
                DensityVerdict(
                    path=str(path), kind=kind, exempt=False,
                    threshold=DENSITY_THRESHOLD, prose_chars=0, code_cells=0,
                    md_cells=0, density=None, md_pct=None, status="unmeasured",
                    detail=str(exc),
                )
            )
            continue
        if n_code == 0:
            result.unmeasured.append(
                DensityVerdict(
                    path=str(path), kind=kind, exempt=False,
                    threshold=DENSITY_THRESHOLD, prose_chars=prose_chars,
                    code_cells=0, md_cells=n_md, density=None, md_pct=None,
                    status="unmeasured",
                    detail="no code cell to divide by -- density undefined",
                )
            )
            continue
        density = prose_chars // n_code
        # Reported, never the criterion: #10479 measured that the markdown
        # share alone cannot discriminate (44-51% on both sides of the gap).
        md_pct = round(100 * prose_chars / max(prose_chars + code_chars, 1), 1)
        status = "ok" if density >= DENSITY_THRESHOLD else "below_threshold"
        verdict = DensityVerdict(
            path=str(path), kind=kind, exempt=False,
            threshold=DENSITY_THRESHOLD, prose_chars=prose_chars,
            code_cells=n_code, md_cells=n_md, density=density,
            md_pct=md_pct, status=status,
        )
        if density < DENSITY_THRESHOLD:
            result.below_threshold.append(verdict)
        else:
            result.ok.append(verdict)
    return result


def _collect_paths(argv_paths: list[str], from_stdin: bool) -> list[Path]:
    """Resolve targets from CLI args and/or stdin into notebook paths.

    A target may be a notebook file OR a directory (globbed for ``*.ipynb``
    under it, skipping the canonical excluded dirs). Blank lines and duplicates
    are dropped; non-existent targets are warned and skipped.
    """
    raw: list[str] = list(argv_paths)
    if from_stdin:
        raw += [ln.strip() for ln in sys.stdin if ln.strip()]
    seen: set[str] = set()
    paths: list[Path] = []
    for r in raw:
        if r in seen:
            continue
        seen.add(r)
        p = Path(r)
        if p.is_dir():
            paths.extend(
                q for q in _glob_notebooks(p)
                if str(q) not in seen and not seen.add(str(q))
            )
            continue
        if not p.exists():
            print(f"warning: {r} does not exist (deleted?), skipping", file=sys.stderr)
            continue
        if p.suffix != ".ipynb":
            continue
        paths.append(p)
    return paths


def _glob_notebooks(directory: Path) -> list[Path]:
    """All ``*.ipynb`` under ``directory``, skipping canonical excluded dirs.

    Consumes :data:`EXCLUDE_DIRS` from ``count_exercises.py`` so the scan mode
    and the fleet scan see the same world.
    """
    out: list[Path] = []
    for p in sorted(directory.rglob("*.ipynb")):
        if any(part in EXCLUDE_DIRS for part in p.parts):
            continue
        if p.name.startswith("."):  # .ipynb_checkpoints/* (also in EXCLUDE_DIRS)
            continue
        out.append(p)
    return out


def _baseline_population() -> list[Path]:
    """Tracked pedagogical notebooks, derived from ``git ls-files``.

    The population of the density baseline (#10479 amendment 19:40Z): exactly
    the notebooks git tracks, never an rglob -- untracked files (papermill
    ``_output.ipynb``, scratchpads) would inflate the population and skew the
    stored values. The kind filter (density-judged kinds only: standard +
    lean) drops setup and out-of-corpus notebooks, mirroring the 859
    "notebooks suivis" figure of the amendment.
    """
    import subprocess

    repo_root = _TOOLS_DIR.parents[1]  # scripts/notebook_tools -> repo root
    listed = subprocess.run(
        ["git", "-C", str(repo_root), "-c", "core.quotepath=false", "ls-files", "--", "MyIA.AI.Notebooks/**/*.ipynb"],
        capture_output=True, text=True, encoding="utf-8", errors="replace", check=True,
    ).stdout.splitlines()
    out: list[Path] = []
    for line in listed:
        p = Path(line)
        if any(part in EXCLUDE_DIRS for part in p.parts):
            continue
        kind, _ = classify_notebook(p)
        if kind in DENSITY_JUDGED_KINDS:
            out.append(p)
    return out


def _update_baseline() -> int:
    """Write :data:`BASELINE_FILE` with one float per tracked notebook.

    The float is the CONTINUOUS metric (prose_chars / code_cells), not the
    integer floor the advisory label uses -- the Phase-2 regression ratchet
    compares continuous densities. Notebooks that cannot be measured (parse
    failure, zero code cells) have no float and are recorded separately: a
    continuous metric with a hole is not continuous.
    """
    population = _baseline_population()
    values: dict[str, float] = {}
    unmeasured: list[dict[str, str]] = []
    for path in population:
        try:
            prose_chars, _code_chars, n_code, _n_md = _measure(path)
        except ValueError as exc:
            unmeasured.append({"path": str(path), "detail": str(exc)})
            continue
        if n_code == 0:
            unmeasured.append(
                {"path": str(path), "detail": "no code cell to divide by"}
            )
            continue
        values[str(path).replace("\\", "/")] = round(prose_chars / n_code, 3)
    payload = {
        "_comment": (
            "Pedagogy-density baseline (#10479). Burn down, do not grow. "
            "One float per TRACKED pedagogical notebook: chars of markdown "
            "prose per code cell (continuous metric). Population: "
            "`git ls-files 'MyIA.AI.Notebooks/**/*.ipynb'` minus EXCLUDE_DIRS "
            "minus setup/out-of-corpus kinds. Regenerate with: "
            "python scripts/notebook_tools/pedagogy_density.py --update-baseline"
        ),
        "metric": "prose_chars / code_cells",
        "count": len(values),
        "notebooks": dict(sorted(values.items())),
    }
    if unmeasured:
        payload["unmeasured"] = unmeasured
    BASELINE_FILE.write_text(
        json.dumps(payload, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    print(f"Baseline written: {BASELINE_FILE}")
    print(f"Notebooks recorded : {len(values)}")
    print(f"Unmeasured (no float): {len(unmeasured)}")
    return 0


def _tracked_notebook_paths() -> set[str]:
    """All tracked ``*.ipynb`` paths, relative to the repo root.

    The orphan test is against *any* tracked notebook (not just the
    density-judged kinds): a baseline key whose path is not tracked at all is a
    stale density whatever kind the notebook once had.
    """
    import subprocess

    repo_root = _TOOLS_DIR.parents[1]  # scripts/notebook_tools -> repo root
    listed = subprocess.run(
        ["git", "-C", str(repo_root), "-c", "core.quotepath=false", "ls-files", "--", "*.ipynb"],
        capture_output=True, text=True, encoding="utf-8", errors="replace", check=True,
    ).stdout.splitlines()
    return {line for line in listed if line}


def _baseline_orphan_keys(baseline: dict[str, float], tracked: set[str]) -> list[str]:
    """Baseline keys whose path is no longer a tracked notebook.

    #13815 -- a rename or a delete leaves the old path out of ``git ls-files``;
    its density float becomes a stale measurement that the Phase-2 ratchet would
    read as if the notebook still existed there. Sorted for a deterministic diff.
    """
    return sorted(k for k in baseline if k not in tracked)


def _baseline_unkeyed_files(
    baseline: dict[str, float],
    population: set[str],
) -> list[str]:
    """Density-judged tracked notebooks with NO baseline key (the #16122 organ).

    The counterpart of :func:`_baseline_orphan_keys`. #13815 asks "does every
    key have a file?"; this asks the opposite question -- "does every file have
    a key?" -- which the guard never posed. A notebook the baseline does not key
    is not "uncovered", it is EXEMPT IN SILENCE: no future density regression of
    it can ever be refused, and nothing says so.

    The comparison is against :func:`_baseline_population` (density-judged
    kinds), NOT against every tracked notebook: ``setup`` and out-of-corpus
    notebooks are legitimately absent from the baseline, and flagging them would
    be a false positive by construction. Sorted for a deterministic diff.
    """
    return sorted(p for p in population if p not in baseline)


def _baseline_at(ref: str) -> dict | None:
    """Parse :data:`BASELINE_FILE` as it stood at ``ref``; ``None`` if unreadable.

    LOST_KEY is defined against the change's BASE, so the organ must read the
    key set the ratchet held before the change. ``None`` means "could not read"
    (shallow clone, absent object) and is propagated as "not evaluated" -- never
    silently treated as an empty baseline, which would report every key as
    newly added and every rename as clean.
    """
    import subprocess

    repo_root = _TOOLS_DIR.parents[1]
    rel = BASELINE_FILE.resolve().relative_to(repo_root.resolve())
    proc = subprocess.run(
        ["git", "-C", str(repo_root), "show", f"{ref}:{rel.as_posix()}"],
        capture_output=True, text=True, encoding="utf-8", errors="replace",
    )
    if proc.returncode != 0:
        return None
    try:
        return json.loads(proc.stdout)
    except json.JSONDecodeError:
        return None


def _renamed_notebook_pairs(base_ref: str) -> list[tuple[str, str]] | None:
    """``(old, new)`` pairs git reports as renames between ``base_ref`` and HEAD.

    ``-M`` enables rename detection; ``--name-status`` gives ``R<score> old new``.
    Returns ``None`` when the base ref cannot be resolved (shallow clone, absent
    object), so the caller can say "not evaluated" instead of claiming a
    conformity it never measured -- the #8819 lesson transposed.
    """
    import subprocess

    repo_root = _TOOLS_DIR.parents[1]
    proc = subprocess.run(
        ["git", "-C", str(repo_root), "-c", "core.quotepath=false", "diff",
         "-M", "--name-status", f"{base_ref}...HEAD", "--", "*.ipynb"],
        capture_output=True, text=True, encoding="utf-8", errors="replace",
    )
    if proc.returncode != 0:
        return None
    pairs: list[tuple[str, str]] = []
    for line in proc.stdout.splitlines():
        parts = line.split("\t")
        if len(parts) == 3 and parts[0].startswith("R"):
            pairs.append((parts[1], parts[2]))
    return pairs


def _keys_lost_by_rename(
    base_baseline: dict[str, float],
    head_baseline: dict[str, float],
    renamed: list[tuple[str, str]],
) -> list[tuple[str, str]]:
    """Renames that DROPPED a baseline key instead of moving it (#16122).

    The regression the #15917 incident produced: ``02-7-Song-Generation.ipynb``
    was renamed to ``02-7-YuE2-Song-Generation.ipynb`` and its key was deleted
    rather than moved -- the check-run stayed green and the ratchet silently
    lost its reference (count 811 -> 810). A rename that MOVES its key (what the
    renumber waves do) is not a finding.

    Returns ``(old, new)`` pairs, sorted, for a deterministic diff.
    """
    lost = [
        (old, new)
        for old, new in renamed
        if old in base_baseline and new not in head_baseline
    ]
    return sorted(lost)


def _check_orphans(base_ref: str | None = None) -> int:
    """Report EVERY direction of the baseline <-> tree correspondence (#13815, #16122).

    Loads :data:`BASELINE_FILE`, cross-references against ``git ls-files``, and
    prints each finding under the direction that produced it:

    - ``ORPHAN_KEY``   -- a baseline key whose path is no longer tracked
                          (renamed or deleted, #13815);
    - ``UNKEYED_FILE`` -- a density-judged tracked notebook with no baseline key
                          (#16122): the inventory of what the ratchet exempts in
                          silence. REPORTED, never a failure -- see the module
                          constant's note: these are overwhelmingly notebooks
                          ADDED after the baseline freeze, and a brand-new
                          notebook was never under the ratchet;
    - ``LOST_KEY``     -- a rename that DELETED a key the baseline held instead
                          of moving it (#16122), the #15917 regression. BLOCKING,
                          and reported only when ``base_ref`` is given: it is
                          defined against the change's base, so without one the
                          organ says "not evaluated" rather than "clean".

    Intentionally NOT advisory (unlike the density label): ORPHAN_KEY and
    LOST_KEY are correctness defects, not soft pedagogical thresholds -- so a
    non-empty finding exits non-zero. The directions are printed separately so
    the message names which question failed instead of collapsing distinct
    failures into one count.
    """
    data = json.loads(BASELINE_FILE.read_text(encoding="utf-8"))
    baseline = data.get("notebooks", {})
    tracked = _tracked_notebook_paths()
    orphans = _baseline_orphan_keys(baseline, tracked)

    population = {str(p).replace("\\", "/") for p in _baseline_population()}
    unkeyed = _baseline_unkeyed_files(baseline, population)

    lost: list[tuple[str, str]] = []
    if not base_ref:
        lost_note = (
            "LOST_KEY non evalue (pas de --base : la perte se definit contre la base)"
        )
    else:
        base_data = _baseline_at(base_ref)
        renamed = _renamed_notebook_pairs(base_ref)
        if base_data is None or renamed is None:
            lost_note = (
                f"LOST_KEY non evalue (base {base_ref} illisible dans ce clone) "
                f"-- conformite ni affirmee ni niee"
            )
        else:
            lost = _keys_lost_by_rename(base_data.get("notebooks", {}), baseline, renamed)
            lost_note = (
                f"LOST_KEY evalue contre {base_ref} "
                f"({len(renamed)} renommage(s) de notebook detecte(s))"
            )

    failed = False
    if orphans:
        print(f"WARN: {len(orphans)} ORPHAN_KEY (cle(s) du baseline sans fichier suivi):")
        for key in orphans:
            print(f"  ORPHAN_KEY {key}")
        failed = True
    if lost:
        print(
            f"WARN: {len(lost)} LOST_KEY (renommage(s) ayant SUPPRIME une cle du "
            f"baseline au lieu de la deplacer -- cliquet amputé en silence):"
        )
        for old, new in lost:
            print(f"  LOST_KEY {old} -> {new}")
        failed = True

    # The inventory is reported on BOTH paths: a failing gate must not hide the
    # state of the ratchet it just refused (the reader needs the whole picture).
    print(
        f"INFO: inventaire UNKEYED_FILE : {len(unkeyed)} notebook(s) juge(s) sans cle "
        f"sur {len(population)} (non bloquant), "
        f"vs {len(tracked)} notebooks suivi(s). {lost_note}"
    )
    if failed:
        return 1
    print(f"OK: {len(baseline)} cles du baseline, 0 ORPHAN_KEY, 0 LOST_KEY.")
    return 0


def _render_text(result: DensityResult) -> str:
    """Human-readable summary (the workflow log; the labels are separate).

    Mirrors check_pr_exercises: the closing line asserts ONLY what was
    measured -- ``unmeasured > 0`` means the honest statement is "N not
    measured", never a blanket conformity claim over notebooks never read.
    """
    s = result.as_payload()["summary"]
    lines = [
        f"Notebooks scanned   : {s['total']}",
        f"Judged vs floor     : {s['judged']}",
        f"Exempt              : {s['exempt']}",
        f"Below {DENSITY_THRESHOLD} c/cell: {s['below_threshold']}",
        f"Unmeasured          : {s['unmeasured']}",
    ]
    if result.below_threshold:
        lines.append(f"\n--- Below threshold (label: {LABEL_NAME}) ---")
        for v in result.below_threshold:
            lines.append(
                f"  [{v.density}/{v.threshold}] ({v.kind}) "
                f"md%={v.md_pct} {v.path}"
            )
    if result.exempt:
        lines.append("\n--- Exempt (kind-classified, not labelled) ---")
        for v in result.exempt:
            lines.append(f"  ({v.kind}) {v.path} -- {v.detail}")
    if result.unmeasured:
        lines.append(f"\n--- Unmeasured (label: {LABEL_UNMEASURED}) ---")
        for v in result.unmeasured:
            lines.append(f"  {v.path}: {v.detail[:120]}")
    if s["unmeasured"] > 0:
        lines.append(
            f"\n{s['unmeasured']} notebook(s) could not be measured -- "
            "conformity neither claimed nor denied."
        )
    elif not result.below_threshold:
        lines.append(
            "\nAll judged notebooks meet the density floor."
        )
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Measure pedagogy density (chars of prose per code cell) per "
            "notebook (#10479). Always exits 0 (advisory): the signal is the "
            f"'{LABEL_NAME}' label, not this exit code."
        ),
    )
    parser.add_argument(
        "targets", nargs="*", default=[],
        help="Notebook files or directories to scan (default: whole corpus).",
    )
    parser.add_argument(
        "--paths", nargs="*", default=[],
        help="Explicit notebook paths (PR mode).",
    )
    parser.add_argument(
        "--stdin", action="store_true",
        help="Also read paths from stdin (one per line; e.g. git diff output).",
    )
    parser.add_argument(
        "--json", dest="json_out", action="store_true",
        help="Emit machine-readable JSON (the workflow parses this for the label).",
    )
    parser.add_argument(
        "--update-baseline", action="store_true",
        help=(
            "Rewrite the density baseline (#10479 amendment 19:31Z). Population "
            "= tracked pedagogical notebooks (git ls-files, never rglob), one "
            "CONTINUOUS float per notebook. Records Phase-1 densities so the "
            "Phase-2 regression ratchet is never retro-fitted."
        ),
    )
    parser.add_argument(
        "--check-orphans", action="store_true",
        help=(
            "Report every direction of the baseline <-> tree correspondence "
            "(#13815, #16122). Fail (non-zero) on ORPHAN_KEY (a baseline key no "
            "longer tracked -- renamed or deleted) and on LOST_KEY (a rename "
            "that DELETED a key instead of moving it, the #15917 regression). "
            "UNKEYED_FILE (a judged notebook the baseline does not key) is "
            "REPORTED as an inventory, never a failure: measured 2026-09-15, "
            "those are overwhelmingly notebooks ADDED after the baseline freeze, "
            "which were never under the ratchet. NOT advisory by design: the two "
            "blocking directions are correctness defects, not soft pedagogical "
            "thresholds."
        ),
    )
    parser.add_argument(
        "--base", default=None, metavar="REF",
        help=(
            "Base ref of the change (e.g. the PR base sha). Required to evaluate "
            "LOST_KEY, which is defined against the base; without it the organ "
            "reports 'LOST_KEY non evalue' rather than claiming clean."
        ),
    )
    # The floor is deliberately NOT a CLI flag: it is locked by calibration
    # against the #10479 table. A mutable threshold would silently change what
    # the label means from one invocation to the next.
    args = parser.parse_args(argv)

    if args.update_baseline:
        return _update_baseline()

    if args.check_orphans:
        return _check_orphans(args.base)

    targets = list(args.paths) + list(args.targets)
    if not targets and not args.stdin:
        targets = [str(NOTEBOOKS_DIR)]  # fleet scan mode (like count_exercises)
    paths = _collect_paths(targets, args.stdin)
    if not paths:
        msg = "No notebooks to measure."
        if args.json_out:
            payload = DensityResult().as_payload()
            payload["note"] = msg
            print(json.dumps(payload, indent=2, ensure_ascii=False))
        else:
            print(msg)
        return 0

    result = check_paths(paths)
    if args.json_out:
        print(json.dumps(result.as_payload(), indent=2, ensure_ascii=False))
    else:
        print(_render_text(result))
    # Advisory: NEVER exit non-zero (issue #10479 acceptance).
    return 0


if __name__ == "__main__":
    sys.exit(main())
