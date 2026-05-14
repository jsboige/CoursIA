"""Mine prover session traces into structured lessons for proof_knowledge.json.

#1082: Extracts patterns from 3 data sources:
1. .prover_history/*.json — per-sorry tactic attempts (success/fail)
2. baselines/traces/*.json — full multi-agent conversations
3. Existing proof_knowledge.json — merges into it (no duplicates)

Output: enriched proof_knowledge.json with new tactic_cookbook patterns,
failed_approaches, and mathlib_api entries.

Usage:
    python -m prover.mine_lean_sessions [--dry-run] [--json-dir DIR]
"""

import json
import re
import sys
from collections import Counter, defaultdict
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Optional, Tuple

PROVER_DIR = Path(__file__).parent
HISTORY_DIR = PROVER_DIR / ".prover_history"
TRACES_DIR = PROVER_DIR / "baselines" / "traces"
KB_PATH = PROVER_DIR / "proof_knowledge.json"


def load_json(path: Path, default=None):
    if not path.exists():
        return default
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, OSError):
        return default


def save_json(path: Path, data):
    path.write_text(
        json.dumps(data, indent=2, ensure_ascii=False), encoding="utf-8"
    )


# ── Source 1: .prover_history/*.json ─────────────────────────────

def mine_attempt_history(history_dir: Path) -> Tuple[List[Dict], List[Dict]]:
    """Extract successful tactics and documented failures from attempt history."""
    successes = []
    failures = []

    for f in sorted(history_dir.glob("*.json")):
        records = load_json(f, [])
        if not records:
            continue

        file_stem = f.stem
        for r in records:
            tactic = r.get("tactic", "").strip()
            outcome = r.get("outcome", "")
            if not tactic or len(tactic) < 5:
                continue

            if outcome == "success":
                successes.append({
                    "tactic": tactic,
                    "source_file": file_stem,
                    "session_id": r.get("session_id", ""),
                    "timestamp": r.get("timestamp", ""),
                })
            elif outcome in ("build_fail", "no_progress", "regression"):
                error_excerpt = r.get("error_excerpt", "")
                error_cat = r.get("error_category", "")
                failures.append({
                    "tactic": tactic,
                    "outcome": outcome,
                    "error_category": error_cat,
                    "error_excerpt": error_excerpt[:200],
                    "source_file": file_stem,
                    "session_id": r.get("session_id", ""),
                })

    return successes, failures


# ── Source 2: baselines/traces/*.json ────────────────────────────

def mine_trace_conversations(traces_dir: Path) -> Tuple[List[Dict], List[Dict], List[Dict]]:
    """Extract patterns, failures, and API discoveries from conversation traces."""
    cookbook_entries = []
    failed_approaches = []
    api_discoveries = []

    for f in sorted(traces_dir.glob("*.json")):
        trace = load_json(f, [])
        if not trace or not isinstance(trace, list):
            continue

        trace_name = f.stem

        # Track tool calls per agent for pattern extraction
        tactic_attempts = []
        search_queries = []

        for entry in trace:
            agent = entry.get("agent", "")
            role = entry.get("role", "")
            tool = entry.get("tool_call", "")
            tool_result = entry.get("tool_result", "")
            content = entry.get("content", "")

            # Extract tactic submissions
            if tool == "submit_tactic" or tool == "file_replace_sorry":
                tactic_args = entry.get("tool_args", {})
                if isinstance(tactic_args, dict):
                    tactic_text = tactic_args.get("tactic", "") or tactic_args.get("code", "")
                else:
                    tactic_text = str(tactic_args) if tactic_args else content[:200]

                if tactic_text and len(tactic_text) > 3:
                    tactic_attempts.append({
                        "tactic": tactic_text[:500],
                        "agent": agent,
                        "trace": trace_name,
                    })

            # Extract successful search results (Mathlib API)
            if tool == "search_mathlib_lemmas" and tool_result:
                if "results" in str(tool_result).lower() or "found" in str(tool_result).lower():
                    search_queries.append({
                        "query": str(entry.get("tool_args", ""))[:200],
                        "result": str(tool_result)[:300],
                        "trace": trace_name,
                    })

            # Extract plan insights from Coordinator
            if agent == "CoordinatorAgent" and tool == "set_attack_plan":
                plan_reason = ""
                if isinstance(entry.get("tool_args"), dict):
                    plan_reason = entry.get("tool_args", {}).get("reason", "")
                plan_steps = tool_result or content
                if plan_reason or plan_steps:
                    cookbook_entries.append({
                        "name": f"plan_{trace_name}",
                        "category": "strategy",
                        "when": plan_reason[:200] if plan_reason else "multi-step proof plan",
                        "tactic": "",
                        "after": str(plan_steps)[:300] if plan_steps else "",
                        "source": trace_name,
                    })

            # Extract error patterns from TacticAgent responses
            if agent == "TacticAgent" and role in ("text_response", "respond"):
                error_patterns = _extract_error_patterns(content)
                for ep in error_patterns:
                    failed_approaches.append({
                        "what_failed": ep["what"],
                        "why": ep["why"],
                        "lesson": ep["lesson"],
                        "trace": trace_name,
                    })

    return cookbook_entries, failed_approaches, api_discoveries


def _extract_error_patterns(content: str) -> List[Dict]:
    """Extract structured error patterns from agent text responses."""
    patterns = []

    # Common Lean error patterns
    error_sigs = [
        (r"type mismatch.*expected:\s*(.{10,80})", "type_mismatch",
         "Type mismatch — check for implicit args or missing casts"),
        (r"unknown identifier\s*'(\w+)'", "unknown_identifier",
         "Unknown identifier — need import or Mathlib search"),
        (r"tactic '(\w+)' failed", "tactic_failed",
         "Tactic failed on this goal — try decomposition"),
        (r"unsolved goals?", "unsolved_goals",
         "Left unsolved subgoals — chain or decompose"),
        (r"function expected.*got\s*(.{10,60})", "function_expected",
         "Function expected — missing implicit argument"),
        (r"omega failed", "omega_failed",
         "omega can't handle this — cast to Nat/Int first or use linarith"),
    ]

    for regex, category, lesson in error_sigs:
        for m in re.finditer(regex, content, re.IGNORECASE):
            patterns.append({
                "what": m.group(0)[:120],
                "why": category,
                "lesson": lesson,
            })

    return patterns


# ── Deduplication & merging ──────────────────────────────────────

def _tactic_signature(tactic: str) -> str:
    """Normalized signature for dedup."""
    return re.sub(r"\s+", " ", tactic.strip().lower())[:150]


def dedup_cookbook(existing: List[Dict], new_entries: List[Dict]) -> List[Dict]:
    """Merge new cookbook entries, skipping duplicates."""
    existing_sigs = set()
    for e in existing:
        sig = e.get("name", "").lower() + "|" + _tactic_signature(e.get("tactic", ""))
        existing_sigs.add(sig)

    merged = list(existing)
    for ne in new_entries:
        sig = ne.get("name", "").lower() + "|" + _tactic_signature(ne.get("tactic", ""))
        if sig not in existing_sigs:
            merged.append(ne)
            existing_sigs.add(sig)
    return merged


def dedup_failures(existing: List[Dict], new_entries: List[Dict]) -> List[Dict]:
    """Merge new failed approaches, dedup by what_failed."""
    existing_whats = set()
    for e in existing:
        existing_whats.add(e.get("what_failed", "").lower()[:100])

    merged = list(existing)
    for ne in new_entries:
        what = ne.get("what_failed", "").lower()[:100]
        if what and what not in existing_whats:
            merged.append(ne)
            existing_whats.add(what)
    return merged


def _extract_successful_patterns(
    successes: List[Dict], failures: List[Dict]
) -> List[Dict]:
    """Convert successful tactics into cookbook patterns.

    Uses surrounding failure context to generate 'not' (avoid) hints.
    """
    # Group successes by source file (same sorry)
    by_source = defaultdict(list)
    for s in successes:
        by_source[s["source_file"]].append(s)

    # Group failures by source file
    fail_by_source = defaultdict(list)
    for f in failures:
        fail_by_source[f["source_file"]].append(f)

    patterns = []
    for source, succ_list in by_source.items():
        nearby_fails = fail_by_source.get(source, [])
        for s in succ_list:
            tactic = s["tactic"]
            # Skip trivial tactics
            if tactic.strip() in ("sorry", "exact?", "apply?", "skip"):
                continue

            # Determine category from tactic content
            category = _categorize_tactic(tactic)

            # Extract avoid hints from nearby failures
            avoid = []
            for f in nearby_fails[:5]:
                ft = f["tactic"]
                if ft and ft.strip() not in ("sorry",) and len(ft) > 5:
                    avoid.append(ft[:100])
            # Dedup avoid list
            avoid = list(dict.fromkeys(avoid))[:3]

            pattern = {
                "name": f"mined_{category}_{source}_{len(patterns)}",
                "category": category,
                "when": f"Goal from {source.replace('_', ' ').split(' L')[0]}",
                "tactic": tactic,
                "after": "",
                "not": avoid,
                "source": "mined_from_history",
            }
            patterns.append(pattern)

    return patterns


def _categorize_tactic(tactic: str) -> str:
    t = tactic.lower()
    if any(k in t for k in ["omega", "linarith", "ring", "nat"]):
        return "arithmetic"
    if any(k in t for k in ["simp", "rw", "unfold"]):
        return "simplification"
    if any(k in t for k in ["exact", "apply", "refine"]):
        return "application"
    if any(k in t for k in ["constructor", "cases", "rcases", "induction"]):
        return "decomposition"
    if any(k in t for k in ["intro", "obtain", "have", "use"]):
        return "introduction"
    if any(k in t for k in ["dsimp", "change", "show"]):
        return "normalization"
    return "general"


def _extract_failure_lessons(failures: List[Dict]) -> List[Dict]:
    """Convert repeated failures into structured lessons."""
    # Count tactic_norm occurrences to find repeated failures
    norm_counts = Counter()
    norm_examples = {}

    for f in failures:
        norm = _tactic_signature(f["tactic"])
        norm_counts[norm] += 1
        if norm not in norm_examples:
            norm_examples[norm] = f

    lessons = []
    for norm, count in norm_counts.most_common(20):
        if count < 2:
            continue
        example = norm_examples[norm]
        tactic = example["tactic"]
        error_cat = example.get("error_category", "")
        error_excerpt = example.get("error_excerpt", "")

        # Determine lesson from error category
        if error_cat == "type_mismatch" or "type mismatch" in error_excerpt.lower():
            lesson = "Cast or add explicit type ascription"
        elif error_cat == "unknown_identifier" or "unknown" in error_excerpt.lower():
            lesson = "Import or search for correct lemma name"
        elif "unsolved" in error_excerpt.lower():
            lesson = "Left subgoals — chain more tactics or decompose"
        else:
            lesson = f"Failed {count}x — try alternative approach"

        lessons.append({
            "what_failed": tactic[:150],
            "why": error_excerpt[:200] if error_excerpt else error_cat,
            "lesson": lesson,
            "file": example.get("source_file", ""),
            "attempts": count,
        })

    return lessons


# ── Main pipeline ────────────────────────────────────────────────

def run_mining(
    history_dir: Path = HISTORY_DIR,
    traces_dir: Path = TRACES_DIR,
    kb_path: Path = KB_PATH,
    dry_run: bool = False,
) -> Dict:
    """Run the full mining pipeline and return stats."""
    kb = load_json(kb_path, {"version": 3, "entries": {},
                              "tactic_cookbook": {"patterns": []},
                              "failed_approaches": [],
                              "mathlib_api": {}})

    existing_patterns = kb.get("tactic_cookbook", {}).get("patterns", [])
    existing_failures = kb.get("failed_approaches", [])

    # Source 1: attempt history
    hist_successes, hist_failures = mine_attempt_history(history_dir)
    mined_patterns = _extract_successful_patterns(hist_successes, hist_failures)
    mined_failure_lessons = _extract_failure_lessons(hist_failures)

    # Source 2: conversation traces
    trace_plans, trace_failures, trace_api = mine_trace_conversations(traces_dir)

    # Merge everything
    all_new_patterns = mined_patterns + trace_plans
    all_new_failures = mined_failure_lessons + trace_failures

    merged_patterns = dedup_cookbook(existing_patterns, all_new_patterns)
    merged_failures = dedup_failures(existing_failures, all_new_failures)

    stats = {
        "history_files": len(list(history_dir.glob("*.json"))),
        "trace_files": len(list(traces_dir.glob("*.json"))),
        "hist_successes": len(hist_successes),
        "hist_failures": len(hist_failures),
        "mined_patterns": len(mined_patterns),
        "mined_failure_lessons": len(mined_failure_lessons),
        "trace_plans": len(trace_plans),
        "trace_failures": len(trace_failures),
        "existing_patterns": len(existing_patterns),
        "existing_failures": len(existing_failures),
        "merged_patterns": len(merged_patterns),
        "merged_failures": len(merged_failures),
        "new_patterns_added": len(merged_patterns) - len(existing_patterns),
        "new_failures_added": len(merged_failures) - len(existing_failures),
    }

    if not dry_run:
        kb["tactic_cookbook"]["patterns"] = merged_patterns
        kb["failed_approaches"] = merged_failures
        kb["last_updated"] = datetime.now().isoformat()
        save_json(kb_path, kb)

    return stats


def main():
    dry_run = "--dry-run" in sys.argv
    json_dir = None
    for i, arg in enumerate(sys.argv):
        if arg == "--json-dir" and i + 1 < len(sys.argv):
            json_dir = Path(sys.argv[i + 1])

    history = HISTORY_DIR
    traces = TRACES_DIR
    kb = KB_PATH

    if json_dir:
        history = json_dir / ".prover_history"
        traces = json_dir / "baselines" / "traces"
        kb = json_dir / "proof_knowledge.json"

    print(f"Mining prover sessions...")
    print(f"  History: {history} ({len(list(history.glob('*.json')))} files)")
    print(f"  Traces:  {traces} ({len(list(traces.glob('*.json')))} files)")
    print(f"  KB:      {kb}")
    if dry_run:
        print("  Mode:    DRY RUN (no changes)")
    print()

    stats = run_mining(history, traces, kb, dry_run=dry_run)

    print("=== Mining Results ===")
    for k, v in stats.items():
        print(f"  {k}: {v}")

    if dry_run:
        print("\nDRY RUN — no changes written.")
    else:
        print(f"\nKB updated: {stats['merged_patterns']} patterns, {stats['merged_failures']} failures")


if __name__ == "__main__":
    main()
