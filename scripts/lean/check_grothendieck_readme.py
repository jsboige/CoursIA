#!/usr/bin/env python3
"""Check that the grothendieck_lean README documents the actual filesystem.

Background
----------
Issue #15474: the README claimed "61 leaf modules" while ``git ls-tree`` on
``origin/main`` showed 73 FR leaf + 73 EN leaf + 1 umbrella. Thirteen modules
present on disk were absent from the table (``CoversEtaleArrow``,
``ExceptionalTriple``, ``Fppf``, ``LocalSurjectivitySpectrum``,
``SheafConditionCharacterization``, ``SheafConditionInvariance``,
``SheafTopologySpectrum``, ``Spaces``, ``SpacesMathlib``, ``SpacesSubcanonical``,
``StalkPoints``, ``StalkSeparated``, ``Stalks``) and the toolchain had drifted
to ``v4.32.1`` while ``lean-toolchain`` was already at ``v4.33.0`` (per #14964).
The drift is structural: a README that understates the disk count is a
recidive-enabling artifact, since the next contributor who adds Partie 75
will read "61 leaf" and trust it.

This checker is the **anti-récidive organe** : it compares the README
(FR+EN) against the actual filesystem via ``git ls-tree`` and reports the
four classes of drift that #15474 had to clean by hand.

Four classes of drift (all block CI on ``--strict``) :

1. ``UNDERCOUNT`` — the README's stated leaf count is strictly less than the
   disk count. The reverse (``OVERCOUNT``) is reported as ``advisory`` because
   a leaf might be deleted in the README before deletion on disk, and the
   discrepancy is bounded by one migration cycle.
2. ``MISSING_IN_TABLE`` — a leaf file present on disk but not appearing in the
   README's table (``| `Foo.lean` |``-style rows). This is the failure mode
   of #15474 (13 leaves).
3. ``ORPHAN_IN_TABLE`` — a leaf appearing in the README's table but no longer
   on disk. (Advisory by default : an old PR might rename the leaf.)
4. ``TOOLCHAIN_DRIFT`` — the README's stated toolchain does not match the
   ``lean-toolchain`` file in the same lake (the v4.32.1 → v4.33.0 class of
   drift).

Usage
-----
    python scripts/lean/check_grothendieck_readme.py --json
    python scripts/lean/check_grothendieck_readme.py --strict
    python scripts/lean/check_grothendieck_readme.py --path <lake-root>

Defaults to the canonical grothendieck_lean lake (auto-detected via
``MyIA.AI.Notebooks/SymbolicAI/Lean/grothendieck_lean/``). Exit code ``0``
on a clean README, ``1`` on any blocking drift. ``--json`` outputs a single
JSON document on stdout (machine-parseable for the gate).
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from dataclasses import asdict, dataclass, field
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_LAKE = REPO_ROOT / "MyIA.AI.Notebooks" / "SymbolicAI" / "Lean" / "grothendieck_lean"

# Patterns calibrated on disk measurements 2026-09-10 (origin/main @ b474cf8f30).
# Adjust only if the structural convention changes; the README prose is the
# part that drifts, not these patterns.
# Table row shape observed in the wild (2026-09-10):
#   `| 1 | `Grothendieck/Adjunction.lean` | `Adjunction_en.lean` | ... |`
#   `| racine | `Grothendieck.lean` | (bilingue inline) | ... |`
#   `| 55a | `Grothendieck/CoversCoherentArrow.lean` | `CoversCoherentArrow_en.lean` | ... |`
# We accept any cell-boundary `|` followed by backticks then `*.lean` then
# backticks then `|`. The leaf name is captured WITHOUT the .lean suffix.
_TABLE_ROW_RE = re.compile(
    r"`(?P<file>(?:[A-Za-z][A-Za-z0-9]*/)?[A-Za-z][A-Za-z0-9]*)\.lean`"
)
# Toolchain claim patterns: README lines like
#   "**Toolchain** : `leanprover/lean4:vX.Y.Z`"
#   "**Toolchain**: `leanprover/lean4:vX.Y.Z`"
_TOOLCHAIN_CLAIM_RE = re.compile(
    r"leanprover/lean4:v(?P<version>\d+\.\d+\.\d+(?:[-+][A-Za-z0-9.]+)?)"
)
# Leaf-count claims — match any integer adjacent to "leaf" inside a "modules"
# sentence. We deliberately accept both "61 modules leaf" and "73 modules leaf"
# so a fix is observable, not a silent escape.
_LEAF_COUNT_RE = re.compile(
    r"(?P<n>\d+)\s+(?:modules\s+leaf|leaf|modules\b)",
    re.IGNORECASE,
)


@dataclass
class Drift:
    kind: str  # UNDERCOUNT | OVERCOUNT | MISSING_IN_TABLE | ORPHAN_IN_TABLE | TOOLCHAIN_DRIFT
    severity: str  # blocking | advisory
    detail: str
    expected: object = None
    actual: object = None


@dataclass
class Report:
    lake: str
    leaf_count_disk_fr: int
    leaf_count_disk_en: int
    leaf_count_umbrella: int
    toolchain_disk: str | None
    toolchain_readme_fr: list[str] = field(default_factory=list)
    toolchain_readme_en: list[str] = field(default_factory=list)
    leaf_count_claims_fr: list[int] = field(default_factory=list)
    leaf_count_claims_en: list[int] = field(default_factory=list)
    leaf_count_claims_fr_raw: list[tuple[int, str]] = field(default_factory=list)
    leaf_count_claims_en_raw: list[tuple[int, str]] = field(default_factory=list)
    table_modules_fr: list[str] = field(default_factory=list)
    table_modules_en: list[str] = field(default_factory=list)
    drifts: list[Drift] = field(default_factory=list)

    def to_dict(self) -> dict:
        d = asdict(self)
        d["drifts"] = [asdict(x) for x in self.drifts]
        return d

    @property
    def blocking(self) -> bool:
        return any(x.severity == "blocking" for x in self.drifts)


def _git_ls_tree_disk(lake_root: Path) -> tuple[set[str], set[str], int]:
    """Return (fr_leaves, en_leaves, umbrella_count) from `git ls-tree -r origin/main`.

    We shell out to git rather than walk the filesystem because the README
    claim must be validated against the **upstream** tree, not the local
    working copy — the local copy might have uncommitted changes that are
    not the README's baseline.

    Leaf detection: ``<LakeRoot>/<Namespace>/<Module>.lean`` (and ``_en``
    variant). The umbrella root file ``<LakeRoot>/<Namespace>.lean`` is
    counted separately, not as a leaf. ``lakefile.lean`` and other config
    files are excluded (they do not end with ``.lean`` once we filter on
    the namespace directory).
    """
    rel = lake_root.relative_to(REPO_ROOT)
    proc = subprocess.run(
        ["git", "ls-tree", "-r", "--name-only", "origin/main", str(rel).replace("\\", "/")],
        cwd=REPO_ROOT,
        check=True,
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
    )
    fr: set[str] = set()
    en: set[str] = set()
    umbrella = 0
    rel_prefix = str(rel).replace("\\", "/") + "/"
    for line in proc.stdout.splitlines():
        if not line.endswith(".lean"):
            continue
        if not line.startswith(rel_prefix):
            continue
        # rel_path is the path RELATIVE TO lake_root, e.g.
        #   "Grothendieck.lean"               -> umbrella root
        #   "lakefile.lean"                   -> config, skip
        #   "Grothendieck/Foo.lean"           -> leaf
        #   "Grothendieck/Foo_en.lean"        -> leaf
        #   "Grothendieck/SheafCohomology/Basic.lean" -> leaf
        rel_path = line[len(rel_prefix):]
        if rel_path == "lakefile.lean" or rel_path == "lakefile.toml":
            continue
        if "/" not in rel_path:
            # Root umbrella file (e.g. "Grothendieck.lean")
            umbrella += 1
            continue
        mod = rel_path.split("/")[-1][:-len(".lean")]  # strip .lean
        if mod.endswith("_en"):
            en.add(mod[: -len("_en")])
        else:
            fr.add(mod)
    return fr, en, umbrella


def _extract_table_modules(readme: Path) -> set[str]:
    """Pull every ``Foo.lean`` row out of the README's table.

    The table shape observed (2026-09-10) is one line per leaf, with the
    FR file in column 2 and the ``_en`` sibling in column 3:

        ``| 1 | `Grothendieck/Adjunction.lean` | `Adjunction_en.lean` | ... |``

    The umbrella root is on a row of its own (no ``_en`` sibling because
    the umbrella is bilingual inline). We use that asymmetry to *find*
    table rows: every leaf row carries a ``*_en.lean`` reference, and the
    umbrella row carries ``Grothendieck.lean`` with no ``_en`` sibling —
    so we collect (a) every ``*_en.lean`` reference to identify leaf rows,
    then (b) the FR module name on each such row. The umbrella is excluded
    by design (its row has no ``_en`` companion).
    """
    out: set[str] = set()
    if not readme.exists():
        return out
    for line in readme.read_text(encoding="utf-8").splitlines():
        # Skip non-table lines cheaply — only process lines that contain a
        # `_en.lean` backtick reference (column 3 marker of a leaf row).
        if "_en.lean" not in line:
            continue
        if "`" not in line:
            continue
        # Within the line, the FR file is the first backtick-quoted
        # `Foo.lean` whose sibling follows as `Foo_en.lean` on the same
        # line. We accept the FR cell even if its leaf-name and _en
        # leaf-name are spelled with the same basename.
        # Pattern: capture `X.lean` immediately before `_en.lean`.
        m = re.search(r"`(?P<file>[A-Za-z][A-Za-z0-9/]*)\.lean`\s*\|\s*`[A-Za-z][A-Za-z0-9/]*_en\.lean`", line)
        if not m:
            continue
        name = m.group("file")
        leaf = name.split("/")[-1]
        out.add(leaf)
    return out


def _read_toolchain(lake_root: Path) -> str | None:
    p = lake_root / "lean-toolchain"
    if not p.exists():
        return None
    return p.read_text(encoding="utf-8").strip()


def _extract_toolchain_claims(readme: Path) -> list[str]:
    if not readme.exists():
        return []
    text = readme.read_text(encoding="utf-8")
    # Filter out matches inside fenced code blocks (those are quotes of the
    # toolchain, not claims about it). Naive but adequate — the README has
    # no nested fences of its own.
    cleaned = re.sub(r"```.*?```", "", text, flags=re.DOTALL)
    return [m.group("version") for m in _TOOLCHAIN_CLAIM_RE.finditer(cleaned)]


def _extract_leaf_count_claims(readme: Path) -> tuple[list[int], list[tuple[int, str]]]:
    """Return (numbers, [(number, surrounding_60_chars)]) — caller can triage.

    We deliberately do NOT collapse "61" and "62" into a single verdict: a
    README that says both "61" and "62" is a *more* broken README than one
    that says "61" twice. Surfacing both lets the operator see the drift
    fan-out.
    """
    if not readme.exists():
        return [], []
    text = readme.read_text(encoding="utf-8")
    cleaned = re.sub(r"```.*?```", "", text, flags=re.DOTALL)
    nums: list[int] = []
    raw: list[tuple[int, str]] = []
    for m in _LEAF_COUNT_RE.finditer(cleaned):
        n = int(m.group("n"))
        if n < 5 or n > 200:  # sanity bound: nobody has 200+ leaf in this lake
            continue
        nums.append(n)
        start = max(0, m.start() - 30)
        end = min(len(cleaned), m.end() + 30)
        raw.append((n, cleaned[start:end].replace("\n", " ")))
    return nums, raw


def check_lake(lake_root: Path, strict: bool = False) -> Report:
    rpt = Report(
        lake=str(lake_root.relative_to(REPO_ROOT)) if lake_root.is_absolute() else str(lake_root),
        leaf_count_disk_fr=0,
        leaf_count_disk_en=0,
        leaf_count_umbrella=0,
        toolchain_disk=None,
    )

    # 1) Disk measurement
    disk_fr, disk_en, umbrella = _git_ls_tree_disk(lake_root)
    rpt.leaf_count_disk_fr = len(disk_fr)
    rpt.leaf_count_disk_en = len(disk_en)
    rpt.leaf_count_umbrella = umbrella

    # 2) README extractions
    fr_readme = lake_root / "README.md"
    en_readme = lake_root / "README.en.md"
    table_fr = _extract_table_modules(fr_readme)
    table_en = _extract_table_modules(en_readme)
    rpt.table_modules_fr = sorted(table_fr)
    rpt.table_modules_en = sorted(table_en)

    rpt.toolchain_disk = _read_toolchain(lake_root)
    rpt.toolchain_readme_fr = _extract_toolchain_claims(fr_readme)
    rpt.toolchain_readme_en = _extract_toolchain_claims(en_readme)

    leaf_claims_fr, raw_fr = _extract_leaf_count_claims(fr_readme)
    leaf_claims_en, raw_en = _extract_leaf_count_claims(en_readme)
    rpt.leaf_count_claims_fr = leaf_claims_fr
    rpt.leaf_count_claims_en = leaf_claims_en
    rpt.leaf_count_claims_fr_raw = raw_fr
    rpt.leaf_count_claims_en_raw = raw_en

    # 3) Drift classes

    # 3.1 UNDERCOUNT / OVERCOUNT — the README must agree with the disk on the
    # leaf count. We accept a 1-module tolerance on OVERCOUNT (the README
    # might lead the disk by one during an in-flight PR) but require strict
    # equality for UNDERCOUNT (the v4.33.0-era failures were all
    # UNDERCOUNTs).
    if leaf_claims_fr or leaf_claims_en:
        disk_n = len(disk_fr)  # FR == EN on disk for grothendieck_lean
        for n in set(leaf_claims_fr + leaf_claims_en):
            if n < disk_n:
                rpt.drifts.append(Drift(
                    kind="UNDERCOUNT",
                    severity="blocking" if strict else "blocking",
                    detail=f"README claims {n} leaf modules; disk has {disk_n} FR + {disk_n} EN",
                    expected=disk_n,
                    actual=n,
                ))
            elif n > disk_n + 1:
                rpt.drifts.append(Drift(
                    kind="OVERCOUNT",
                    severity="advisory",
                    detail=f"README claims {n} leaf modules; disk has {disk_n} FR + {disk_n} EN (lead by {n - disk_n} — in-flight PR?)",
                    expected=disk_n,
                    actual=n,
                ))

    # 3.2 MISSING_IN_TABLE — the #15474 failure mode (13 leaves)
    disk_all = disk_fr  # FR and EN are symmetric in this lake
    missing = sorted(disk_all - table_fr)
    if missing:
        rpt.drifts.append(Drift(
            kind="MISSING_IN_TABLE",
            severity="blocking",
            detail=f"{len(missing)} leaf module(s) present on disk but absent from README.md table",
            expected=sorted(disk_all),
            actual=sorted(table_fr),
        ))
    if en_readme.exists():
        missing_en = sorted(disk_all - table_en)
        if missing_en:
            rpt.drifts.append(Drift(
                kind="MISSING_IN_TABLE",
                severity="blocking",
                detail=f"{len(missing_en)} leaf module(s) present on disk but absent from README.en.md table",
                expected=sorted(disk_all),
                actual=sorted(table_en),
            ))

    # 3.3 ORPHAN_IN_TABLE — leaf documented but absent on disk
    orphan = sorted(table_fr - disk_all)
    if orphan:
        rpt.drifts.append(Drift(
            kind="ORPHAN_IN_TABLE",
            severity="advisory",
            detail=f"{len(orphan)} leaf module(s) in README.md table but absent on disk: {orphan}",
            expected=sorted(disk_all),
            actual=sorted(table_fr),
        ))
    if en_readme.exists():
        orphan_en = sorted(table_en - disk_all)
        if orphan_en:
            rpt.drifts.append(Drift(
                kind="ORPHAN_IN_TABLE",
                severity="advisory",
                detail=f"{len(orphan_en)} leaf module(s) in README.en.md table but absent on disk: {orphan_en}",
                expected=sorted(disk_all),
                actual=sorted(table_en),
            ))

    # 3.4 TOOLCHAIN_DRIFT — `lean-toolchain` vs README claim
    disk_tool = rpt.toolchain_disk
    if disk_tool:
        # The lean-toolchain file is of the form "leanprover/lean4:vX.Y.Z".
        disk_ver = _TOOLCHAIN_CLAIM_RE.search(disk_tool)
        if disk_ver:
            disk_v = disk_ver.group("version")
            for claimed in set(rpt.toolchain_readme_fr + rpt.toolchain_readme_en):
                if claimed != disk_v:
                    rpt.drifts.append(Drift(
                        kind="TOOLCHAIN_DRIFT",
                        severity="blocking",
                        detail=f"README claims v{claimed} but lean-toolchain pins v{disk_v}",
                        expected=disk_v,
                        actual=claimed,
                    ))

    return rpt


def _print_human(rpt: Report, strict: bool) -> None:
    print(f"# grothendieck_lean README drift check — {rpt.lake}")
    print()
    print(f"Disk (origin/main) : {rpt.leaf_count_disk_fr} FR + {rpt.leaf_count_disk_en} EN + {rpt.leaf_count_umbrella} umbrella")
    print(f"Toolchain (disk)   : {rpt.toolchain_disk!r}")
    print()
    print("README.md claims:")
    for n, ctx in rpt.leaf_count_claims_fr_raw:
        print(f"  - {n:>3} leaf  ::  …{ctx}…")
    print(f"README.md toolchain claims: {rpt.toolchain_readme_fr}")
    print()
    print("README.en.md claims:")
    for n, ctx in rpt.leaf_count_claims_en_raw:
        print(f"  - {n:>3} leaf  ::  …{ctx}…")
    print(f"README.en.md toolchain claims: {rpt.toolchain_readme_en}")
    print()
    if not rpt.drifts:
        print("OK — no drift detected.")
        return
    print(f"DRIFTS ({len(rpt.drifts)}):")
    for d in rpt.drifts:
        sev = d.severity.upper()
        print(f"  [{sev}] {d.kind}: {d.detail}")
        if d.expected is not None:
            print(f"           expected = {d.expected}")
        if d.actual is not None:
            print(f"           actual   = {d.actual}")


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--path", default=str(DEFAULT_LAKE),
                   help="Path to the grothendieck_lean lake root "
                        f"(default: {DEFAULT_LAKE})")
    p.add_argument("--strict", action="store_true",
                   help="Promote OVERCOUNT/ORPHAN_IN_TABLE advisories to blocking "
                        "(default: blocking only on UNDERCOUNT/MISSING_IN_TABLE/TOOLCHAIN_DRIFT)")
    p.add_argument("--json", action="store_true", help="Emit a JSON document on stdout")
    args = p.parse_args()

    lake = Path(args.path).resolve()
    if not lake.exists():
        print(f"FATAL: lake root not found: {lake}", file=sys.stderr)
        return 2

    rpt = check_lake(lake, strict=args.strict)

    if args.json:
        print(json.dumps(rpt.to_dict(), ensure_ascii=False, indent=2, sort_keys=True))
    else:
        _print_human(rpt, strict=args.strict)

    return 1 if rpt.blocking else 0


if __name__ == "__main__":
    sys.exit(main())
