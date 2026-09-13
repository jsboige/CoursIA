#!/usr/bin/env python3
r"""Block NEW oversized results artifacts from entering scripts/results/ (#15890).

Context: scripts/results/m16_har_asymmetric_debiased_7asset.json landed on
main at 7,800,634 bytes -- 40x the largest prior artifact of the directory
(193,333 o, m18_tsfm_benchmark.json) and ~37x the next four combined. The
repo is public and forked by ~95 student projects that clone the whole
history: at one such artifact per multi-asset revalidation, the trajectory
is a repo whose results outweigh the course. The falsifiability the body of
#15875 needed (signed biases, per-config DM p-values, fold evidence) fits
in a few thousand lines; it is the point-by-point prediction/target series
that make the volume -- useful, but they belong outside git.

Policy (See .claude/rules/results-artifact-policy.md -- the bar and the
beyond-bar convention live there):

  - NEW files under scripts/results/ larger than RESULTS_BAR_BYTES are
    BLOCKED. The aggregated JSON goes in the repo, the complete series go
    to GDrive, and the PR body cites the path.
  - Artifacts already on main at the base are GRANDFATHERED: they stay,
    no history rewrite, no forced migration. MODIFIED tracked files over
    the bar emit an advisory ::warning only (visible, never a block) --
    the aggregate JSON of a re-run keeps the falsifiability honest while
    the full series move is decided separately.

The bar is anchored, not round-numbered: 512,000 bytes = 2.6x headroom
over the largest legitimate artifact on main (193,333 o) while sitting
well under the 7.43 Mo that triggered the policy.

Input (CI mode, cwd = the PR checkout):
    --repo <path>         git repo to assess (default: this repository)
    --base <rev>          base ref for the merge-base diff (default origin/main)
    --results-dir <path>  guarded directory (default scripts/results)
    --bar-bytes <n>       policy bar (default 512000)

Output: one JSON verdict on stdout. Exit 0 = pass/unknown-allowed, 1 =
over-bar NEW artifact. Unknown inputs (git failure, no merge-base) exit 0
with verdict "unknown" + ::warning -- a guard must never fabricate a red
on infrastructure, only on substance (#14849).
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_RESULTS_DIR = "scripts/results"
RESULTS_BAR_BYTES = 512_000

POLICY_DOC = ".claude/rules/results-artifact-policy.md"

# module-level pour les tests ; None = REPO_ROOT
_REPO_OVERRIDE: Path | None = None


def _repo() -> Path:
    return _REPO_OVERRIDE or REPO_ROOT


def _git(args: list[str]) -> subprocess.CompletedProcess:
    return subprocess.run(
        ["git", *args], cwd=_repo(), capture_output=True, text=True,
        encoding="utf-8", errors="replace",
    )


def _merge_base(base: str) -> str | None:
    got = _git(["merge-base", base, "HEAD"])
    if got.returncode != 0 or not got.stdout.strip():
        return None
    return got.stdout.strip()


def _diffed_files(base_sha: str, results_dir: str) -> dict[str, str]:
    """{path: status} for every change under results_dir since base_sha."""
    got = _git([
        "diff", "--name-status", "--no-renames",
        base_sha, "--", results_dir,
    ])
    if got.returncode != 0:
        return {}
    statuses: dict[str, str] = {}
    for line in got.stdout.splitlines():
        parts = line.split("\t")
        if len(parts) != 2:
            continue
        status, path = parts
        # Truncation du prefix de renommage eventuel (status "R100\told\tnew"
        # est exclu par --no-renames, mais la defensive reste gratuite).
        statuses[path] = status[:1].upper()
    return statuses


def assess(base: str, results_dir: str, bar_bytes: int) -> dict:
    base_sha = _merge_base(base)
    if base_sha is None:
        return {
            "verdict": "unknown",
            "reason": (
                f"pas de merge-base avec '{base}' -- verdict non calcule, "
                "aucun rouge fabrique sur une panne d'infrastructure (#14849)"
            ),
            "blocked": [],
            "advisories": [],
        }

    changed = _diffed_files(base_sha, results_dir)
    blocked: list[dict] = []
    advisories: list[dict] = []

    for path, status in sorted(changed.items()):
        on_disk = _repo() / path
        if not on_disk.is_file():
            continue  # deleted in this PR -- nothing to weigh
        try:
            size = on_disk.stat().st_size
        except OSError:
            continue
        if size <= bar_bytes:
            continue
        entry = {"path": path, "size_bytes": size, "bar_bytes": bar_bytes}
        if status == "A":
            entry["reason"] = (
                f"NOUVEL artefact {size:,} o > barre {bar_bytes:,} o -- "
                "la falsifiabilite (biais signes, p-values DM par "
                "configuration, preuves de folds) tient en JSON agrege "
                "commite ; les series point par point vont hors depot "
                f"(chemin cite dans le body). Politique : {POLICY_DOC}"
            )
            blocked.append(entry)
        else:
            entry["reason"] = (
                f"artefact EXISTANT modifie, {size:,} o > barre "
                f"{bar_bytes:,} o -- grandfathered ({POLICY_DOC}) : il "
                "reste, aucune reecriture d'historique ; advisory seulement."
            )
            advisories.append(entry)

    return {
        "verdict": "over_bar" if blocked else "ok",
        "base": base,
        "merge_base": base_sha,
        "results_dir": results_dir,
        "bar_bytes": bar_bytes,
        "blocked": blocked,
        "advisories": advisories,
    }


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Block new oversized results artifacts (#15890)"
    )
    parser.add_argument("--repo", default=None,
                        help="git repo to assess (default: this repository)")
    parser.add_argument("--base", default="origin/main")
    parser.add_argument("--results-dir", default=DEFAULT_RESULTS_DIR)
    parser.add_argument("--bar-bytes", type=int, default=RESULTS_BAR_BYTES)
    args = parser.parse_args()

    global _REPO_OVERRIDE
    if args.repo:
        _REPO_OVERRIDE = Path(args.repo).resolve()

    verdict = assess(args.base, args.results_dir, args.bar_bytes)

    for adv in verdict.get("advisories", []):
        print(f"::warning::{adv['reason']}")

    print(json.dumps(verdict, ensure_ascii=False, indent=2))

    if verdict["verdict"] == "over_bar":
        for bad in verdict["blocked"]:
            print(f"::error::{bad['reason']}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
