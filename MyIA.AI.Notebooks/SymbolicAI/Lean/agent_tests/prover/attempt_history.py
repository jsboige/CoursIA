"""Cross-session attempt history for the multi-agent prover.

Without this, every fresh run repeats the same failed tactics — agents have no
memory beyond the current process. We persist a small JSON file per
(filepath, sorry_line) recording each tactic tried, the build outcome, and the
error category. Future runs read it and surface a "DO NOT TRY" list to agents.

Storage layout:
    <prover_dir>/.prover_history/<file_hash>_<line>.json

Each file holds a list of records:
    {
        "tactic": "<text>",
        "outcome": "success" | "build_fail" | "no_progress" | "regression",
        "error_category": "type_mismatch" | "unknown_identifier" | ...,
        "error_excerpt": "<first 200 chars>",
        "session_id": "<uuid>",
        "timestamp": "<iso>",
    }

Records are appended; duplicates (same normalized tactic) update the latest.
The file is small (KB-scale) and safe to commit gitignored.
"""

from __future__ import annotations

import hashlib
import json
import re
from datetime import datetime
from pathlib import Path
from typing import List, Dict, Optional


_HISTORY_DIR_NAME = ".prover_history"


def _normalize_tactic(tactic: str) -> str:
    """Whitespace-normalized tactic key for dedup."""
    return re.sub(r"\s+", " ", tactic.strip())


def _history_path(prover_dir: Path, filepath: str, sorry_line: int) -> Path:
    h = hashlib.sha1(filepath.encode("utf-8")).hexdigest()[:10]
    safe_name = Path(filepath).stem
    return prover_dir / _HISTORY_DIR_NAME / f"{safe_name}_{h}_L{sorry_line}.json"


def load_history(prover_dir: Path, filepath: str, sorry_line: int) -> List[Dict]:
    """Load past attempts for a (filepath, sorry_line). Returns [] if none."""
    path = _history_path(prover_dir, filepath, sorry_line)
    if not path.exists():
        return []
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return []


def record_attempt(prover_dir: Path, filepath: str, sorry_line: int,
                   tactic: str, outcome: str,
                   error_category: Optional[str] = None,
                   error_excerpt: Optional[str] = None,
                   session_id: Optional[str] = None) -> None:
    """Append/update a tactic attempt for cross-session memory.

    `outcome` ∈ {"success", "build_fail", "no_progress", "regression"}.
    Same normalized tactic appearing twice with the same outcome is collapsed.
    """
    path = _history_path(prover_dir, filepath, sorry_line)
    path.parent.mkdir(parents=True, exist_ok=True)

    history = load_history(prover_dir, filepath, sorry_line)
    norm_new = _normalize_tactic(tactic)

    record = {
        "tactic": tactic,
        "tactic_norm": norm_new,
        "outcome": outcome,
        "error_category": error_category or "",
        "error_excerpt": (error_excerpt or "")[:200],
        "session_id": session_id or "",
        "timestamp": datetime.now().isoformat(),
    }

    # Dedup: same tactic+outcome → replace timestamp only
    for existing in history:
        if existing.get("tactic_norm") == norm_new and existing.get("outcome") == outcome:
            existing.update(record)
            break
    else:
        history.append(record)

    try:
        path.write_text(json.dumps(history, indent=2, ensure_ascii=False), encoding="utf-8")
    except OSError:
        pass  # best-effort persistence; never block the prover


def format_for_agent(history: List[Dict], max_items: int = 15) -> str:
    """Render the history as a compact context block for agents.

    Sorts by outcome (failures first, since they are the actionable warnings),
    then truncates to `max_items`.
    """
    if not history:
        return ""

    failures = [h for h in history
                if h.get("outcome") in ("build_fail", "regression", "no_progress")]
    successes = [h for h in history if h.get("outcome") == "success"]

    parts = ["[CROSS-SESSION HISTORY] tactics already tried on this sorry:"]
    for h in failures[:max_items]:
        cat = h.get("error_category") or "fail"
        excerpt = h.get("error_excerpt") or ""
        parts.append(
            f"  X [{cat}] {h.get('tactic', '')[:120]}"
            + (f" :: {excerpt[:80]}" if excerpt else "")
        )
    for h in successes[:3]:
        parts.append(f"  OK  {h.get('tactic', '')[:120]}")
    parts.append("DO NOT REPEAT the failing tactics above without a meaningful change.")
    return "\n".join(parts)
