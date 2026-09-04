#!/usr/bin/env python3
"""Compare the FULL dependency pins of every lake manifest (EPIC #4362, step 1).

The 2026-09-01 re-read of #4362 measured Mathlib revisions across the 28
``lake-manifest.json`` files and found 22/23 Mathlib-bearing lakes converged on
``520045ab`` / v4.32.1 — but explicitly did NOT compare the rest of the pin
tree (batteries, aesop, plausible, Qq, ...). Whether the lakes can share
checkouts (junctions, #4363) or a warm pool volume (#14337) depends on the
COMPLETE ``{package name -> rev}`` tree being identical, not just Mathlib:
two lakes with the same Mathlib rev but different batteries revs cannot share
a checkout.

This scanner closes that gap. It discovers every ``lake-manifest.json`` outside
``.lake/packages/``, reads the effective ``rev`` (the resolved SHA, not the
``inputRev`` tag) of every package, and groups the lakes by pin-tree identity.
Lakes excluded by the EPIC's own analysis are skipped with their reasons:

- ``conway_cgt_lean``: Mathlib arrives transitively through the upstream
  ``vihdzp/combinatorial-games`` pin (rev ``3c6dcdbc1c``) — converging it
  means bumping a project we deliberately reference, not our parc (#6116,
  #13146).
- ``agent_tests/prover/session_state/reference_docs/*/upstream``: third-party
  fixtures, out of scope per ``.claude/rules/code-style.md``.

Output is a per-identity-cluster report: identical lakes together, divergent
lakes with the exact package/rev pairs that differ. ``--json`` returns the
same data machine-readably. Exit code is always 0: this is a measurement
instrument, not a gate.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import sys
from dataclasses import dataclass, field
from pathlib import Path

# Documented exclusions of EPIC #4362 (see module docstring for the reasons).
DEFAULT_EXCLUDES: dict[str, str] = {
    "conway_cgt_lean": "transitive upstream pin (vihdzp/combinatorial-games), not ours to converge (#6116/#13146)",
    "reference_docs": "third-party prover fixtures, out of scope (code-style.md)",
}


@dataclass
class LakePins:
    """Effective pin tree of one lake: package name -> resolved rev SHA."""

    path: Path
    toolchain: str | None
    pins: dict[str, str] = field(default_factory=dict)

    @property
    def identity_key(self) -> str:
        """Stable fingerprint of the complete pin tree."""
        canonical = json.dumps(sorted(self.pins.items()), sort_keys=True)
        return hashlib.sha256(canonical.encode()).hexdigest()[:16]

    @property
    def mathlib_rev(self) -> str | None:
        return self.pins.get("mathlib")


def read_toolchain(lake_root: Path) -> str | None:
    toolchain_file = lake_root / "lean-toolchain"
    if toolchain_file.is_file():
        return toolchain_file.read_text(encoding="utf-8").strip()
    return None


def load_lake(manifest_path: Path) -> LakePins:
    data = json.loads(manifest_path.read_text(encoding="utf-8"))
    pins = {
        pkg["name"]: pkg["rev"]
        for pkg in data.get("packages", [])
        if pkg.get("type") == "git" and pkg.get("rev")
    }
    return LakePins(
        path=manifest_path.parent,
        toolchain=read_toolchain(manifest_path.parent),
        pins=pins,
    )


def discover_manifests(root: Path, excludes: dict[str, str]) -> tuple[list[LakePins], list[tuple[Path, str]]]:
    """Return (loadable lakes, skipped paths with reason)."""
    lakes: list[LakePins] = []
    skipped: list[tuple[Path, str]] = []
    for manifest in sorted(root.rglob("lake-manifest.json")):
        rel = manifest.relative_to(root)
        if ".lake" in rel.parts:
            continue
        reason = next((r for needle, r in excludes.items() if needle in str(rel)), None)
        if reason is not None:
            skipped.append((rel, reason))
            continue
        lakes.append(load_lake(manifest))
    return lakes, skipped


def diff_pin_trees(a: LakePins, b: LakePins) -> list[tuple[str, str | None, str | None]]:
    """Packages whose rev differs between two lakes (name, rev_a, rev_b)."""
    diffs = []
    for name in sorted(set(a.pins) | set(b.pins)):
        ra, rb = a.pins.get(name), b.pins.get(name)
        if ra != rb:
            diffs.append((name, ra, rb))
    return diffs


def build_report(lakes: list[LakePins], skipped: list[tuple[Path, str]]) -> dict:
    clusters: dict[str, list[LakePins]] = {}
    for lake in lakes:
        clusters.setdefault(lake.identity_key, []).append(lake)

    # Reference cluster = the largest non-empty one (the converged core, by
    # construction). An empty pin tree is never the reference: a 1-vs-1 split
    # against a real tree must not crown the empty lake as "the core".
    non_empty = {k: v for k, v in clusters.items() if v[0].pins}
    ref_key = max(non_empty, key=lambda k: len(non_empty[k])) if non_empty else None
    ref = clusters[ref_key][0] if ref_key else None

    # Lakes with NO dependency at all form their own class: they have nothing
    # to share with the core, but reporting them as "divergent" (every package
    # missing) is noise, not a finding.
    no_deps = sorted(lake.path.name for lake in lakes if not lake.pins)

    divergent = []
    for lake in lakes:
        if ref is None or lake.identity_key == ref_key or not lake.pins:
            continue
        divergent.append(
            {
                "lake": lake.path.name,
                "toolchain": lake.toolchain,
                "diffs_vs_reference": [
                    {"package": n, "reference": ra, "lake": rb}
                    for n, ra, rb in diff_pin_trees(ref, lake)
                ],
            }
        )

    return {
        "total_manifests": len(lakes) + len(skipped),
        "scanned": len(lakes),
        "skipped": [{"path": str(p), "reason": r} for p, r in skipped],
        "no_dependency_lakes": no_deps,
        "identity_clusters": {
            key: {
                "size": len(members),
                "toolchains": sorted({m.toolchain for m in members}),
                "mathlib_rev": members[0].mathlib_rev,
                "lakes": sorted(m.path.name for m in members),
            }
            for key, members in sorted(clusters.items(), key=lambda kv: -len(kv[1]))
        },
        "reference_cluster": ref_key,
        "divergent_vs_reference": divergent,
    }


def render_text(report: dict) -> str:
    lines = [
        f"Lake manifests scanned: {report['scanned']} "
        f"(skipped {len(report['skipped'])}, documented exclusions)",
    ]
    for s in report["skipped"]:
        lines.append(f"  SKIP {s['path']}: {s['reason']}")
    if report["no_dependency_lakes"]:
        lines.append(f"  no-dependency lakes (empty pin tree): {', '.join(report['no_dependency_lakes'])}")
    lines.append("")
    lines.append("Identity clusters (COMPLETE pin tree {name: rev}):")
    for key, cluster in report["identity_clusters"].items():
        marker = "  [REFERENCE]" if key == report["reference_cluster"] else ""
        lines.append(
            f"  {cluster['size']:2d} lakes | toolchain={','.join(t or '?' for t in cluster['toolchains'])} "
            f"| mathlib={cluster['mathlib_rev'] or 'none'}{marker}"
        )
        lines.append(f"      {', '.join(cluster['lakes'])}")
    if report["divergent_vs_reference"]:
        lines.append("")
        lines.append("Divergent vs reference cluster:")
        for d in report["divergent_vs_reference"]:
            lines.append(f"  {d['lake']} (toolchain={d['toolchain']}):")
            for diff in d["diffs_vs_reference"]:
                lines.append(
                    f"      {diff['package']}: ref={str(diff['reference'])[:12]} lake={str(diff['lake'])[:12]}"
                )
    else:
        lines.append("")
        lines.append("All scanned lakes share ONE complete pin tree.")
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--root", type=Path, default=Path("."), help="repository root (default: cwd)")
    parser.add_argument("--json", action="store_true", help="machine-readable output")
    args = parser.parse_args(argv)

    lakes, skipped = discover_manifests(args.root.resolve(), DEFAULT_EXCLUDES)
    if not lakes:
        print("no lake-manifest.json found under root (excluding .lake/packages/)", file=sys.stderr)
        return 2
    report = build_report(lakes, skipped)

    if args.json:
        print(json.dumps(report, indent=2))
    else:
        print(render_text(report))
    return 0


if __name__ == "__main__":
    sys.exit(main())
