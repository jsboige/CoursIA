"""Measure static harness size per lane.

Issue #11554 Phase 1 -- le fork claudish journalise le trafic Anthropic au hub
(po-2023) et peut mesurer le prefixe stable injecte. Ce script est la version
**statique** (wc -c des fichiers du harnais) -- l'integration claudish est Phase
1b et reste a faire par l'operateur hub.

Livrable : un JSON par machine avec harness_chars (CLAUDE.md + rules/ + MEMORY.md
du projet + du global) + ratio vs main 2026-08-18 (mesure 195470 chars).

Usage :
    python scripts/traffic-live/measure_harness_size.py --machine myia-po-2023 --workspace CoursIA-2
    python scripts/traffic-live/measure_harness_size.py --all-lanes
    python scripts/traffic-live/measure_harness_size.py --all-lanes --json

Prerequis :
- Python 3.10+
- Acces au clone CoursIA courant (cwd ou --repo)
- Lancer depuis le clone PRINCIPAL, pas un worktree (le MEMORY.md
  per-project est stocke sous hash du chemin du clone principal)

Voir aussi : issue #11554, ticket Phase 1, et le claim
`[CLAIMED] lane myia-po-2023:CoursIA-2 -- paths: scripts/traffic-live/**` (Tell
c.12862 scope creation).
"""

from __future__ import annotations

import argparse
import json
import os
import socket
import sys
from dataclasses import asdict, dataclass
from pathlib import Path

BASELINE_2026_08_18 = 195_470  # octets, mesure du ticket #11554 sur main `aa4a45d80`


@dataclass
class HarnessSize:
    machine: str
    workspace: str
    lane: str
    project_claude_md_chars: int
    project_rules_chars: int
    project_rules_count: int
    project_memory_md_chars: int
    global_claude_md_chars: int
    global_rules_chars: int
    total_chars: int
    baseline_2026_08_18: int
    delta_vs_baseline: int
    delta_pct: float


def _safe_wc_c(path: Path) -> int:
    try:
        return path.stat().st_size
    except (FileNotFoundError, OSError):
        return 0


def _global_user_claude_md() -> Path:
    return Path.home() / ".claude" / "CLAUDE.md"


def _global_user_rules_dir() -> Path:
    return Path.home() / ".claude" / "rules"


def _project_claude_md(repo_root: Path) -> Path:
    return repo_root / "CLAUDE.md"


def _project_rules_dir(repo_root: Path) -> Path:
    return repo_root / ".claude" / "rules"


def _project_memory_md(repo_root: Path) -> Path:
    """Locate the per-machine MEMORY.md.

    Convention : `~/.claude/projects/<hash>/memory/MEMORY.md`. The hash is
    derived from the absolute repo path -- Claude Code lowercases the
    absolute path and replaces ``\\`` / ``:`` / ``/`` with ``-`` (Windows
    is case-insensitive at the FS level, so the directory case is not
    significant).
    """
    return Path.home() / ".claude" / "projects" / _project_hash(str(repo_root)) / "memory" / "MEMORY.md"


def _project_hash(repo_path: str) -> str:
    """Compute the project hash Claude Code uses for memory storage.

    The exact algorithm is platform-specific; for our purposes the lowercase
    absolute path with separators replaced is a stable identifier.
    """
    p = os.path.abspath(repo_path).replace("\\", "-").replace("/", "-").replace(":", "-").lower()
    return p.lstrip("-")


def measure(
    machine: str, workspace: str, lane: str, repo_root: Path
) -> HarnessSize:
    project_claude = _safe_wc_c(_project_claude_md(repo_root))
    project_rules_dir = _project_rules_dir(repo_root)
    project_rules_chars = 0
    project_rules_count = 0
    if project_rules_dir.exists():
        for f in project_rules_dir.glob("*.md"):
            project_rules_chars += _safe_wc_c(f)
            project_rules_count += 1
    project_memory = _safe_wc_c(_project_memory_md(repo_root))

    global_claude = _safe_wc_c(_global_user_claude_md())
    global_rules_dir = _global_user_rules_dir()
    global_rules_chars = 0
    if global_rules_dir.exists():
        for f in global_rules_dir.glob("*.md"):
            global_rules_chars += _safe_wc_c(f)
    global_memory = project_memory  # MEMORY.md is per-project, not per-user

    total = (
        project_claude
        + project_rules_chars
        + project_memory
        + global_claude
        + global_rules_chars
    )
    delta = total - BASELINE_2026_08_18
    delta_pct = (delta / BASELINE_2026_08_18) * 100 if BASELINE_2026_08_18 else 0.0

    return HarnessSize(
        machine=machine,
        workspace=workspace,
        lane=lane,
        project_claude_md_chars=project_claude,
        project_rules_chars=project_rules_chars,
        project_rules_count=project_rules_count,
        project_memory_md_chars=project_memory,
        global_claude_md_chars=global_claude,
        global_rules_chars=global_rules_chars,
        total_chars=total,
        baseline_2026_08_18=BASELINE_2026_08_18,
        delta_vs_baseline=delta,
        delta_pct=round(delta_pct, 1),
    )


DEFAULT_LANES = [
    ("myia-po-2023", "CoursIA-2"),
    ("myia-po-2024", "CoursIA-2"),
    ("myia-po-2025", "CoursIA-2"),
    ("myia-po-2026", "CoursIA-2"),
    ("myia-po-2027", "CoursIA-2"),
    ("myia-ai-01", "CoursIA"),
    ("myia-ai-01", "CoursIA-2"),
]


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Measure static harness size per lane (Issue #11554 Phase 1)"
    )
    parser.add_argument("--machine", help="machine hostname (e.g. myia-po-2023)")
    parser.add_argument("--workspace", help="workspace (e.g. CoursIA-2)")
    parser.add_argument("--lane", help="lane label myia-po-2023:CoursIA-2")
    parser.add_argument(
        "--repo",
        default=os.getcwd(),
        help="path to CoursIA clone (default: cwd)",
    )
    parser.add_argument(
        "--all-lanes",
        action="store_true",
        help="iterate DEFAULT_LANES (note: only the current machine's home is read)",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="emit JSON instead of human-readable table",
    )
    args = parser.parse_args(argv)

    repo_root = Path(args.repo).resolve()

    if args.all_lanes:
        results = [measure(m, w, f"{m}:{w}", repo_root) for m, w in DEFAULT_LANES]
    elif args.machine and args.workspace:
        lane = args.lane or f"{args.machine}:{args.workspace}"
        results = [measure(args.machine, args.workspace, lane, repo_root)]
    else:
        host = socket.gethostname()
        parser.error(
            f"--machine and --workspace required (host={host}); or pass --all-lanes"
        )

    if args.json:
        print(json.dumps([asdict(r) for r in results], indent=2, ensure_ascii=False))
    else:
        print(f"Baseline main 2026-08-18 = {BASELINE_2026_08_18:,} chars")
        print()
        for r in results:
            print(
                f"lane {r.lane}\n"
                f"  project CLAUDE.md     = {r.project_claude_md_chars:>7,} chars\n"
                f"  project .claude/rules = {r.project_rules_chars:>7,} chars ({r.project_rules_count} files)\n"
                f"  project MEMORY.md     = {r.project_memory_md_chars:>7,} chars\n"
                f"  global  CLAUDE.md     = {r.global_claude_md_chars:>7,} chars\n"
                f"  global  rules/        = {r.global_rules_chars:>7,} chars\n"
                f"  TOTAL                 = {r.total_chars:>7,} chars\n"
                f"  delta vs baseline     = {r.delta_vs_baseline:>+7,} chars ({r.delta_pct:+.1f} %)"
            )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
