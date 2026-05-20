"""Mine prover session traces into structured lessons for proof_knowledge.json.

#1082: Extracts patterns from 3 data sources:
1. .prover_history/*.json — per-sorry tactic attempts (success/fail)
2. baselines/traces/*.json — full multi-agent conversations
3. Claude Code JSONL sessions — interactive Lean proof sessions

Usage:
    python -m prover.mine_lean_sessions [--dry-run] [--json-dir DIR] [--jsonl-dir DIR]
"""

import json
import logging
import re
import sys
from collections import Counter, defaultdict
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Optional, Tuple

logging.basicConfig(level=logging.WARNING, format="%(levelname)s: %(message)s")
log = logging.getLogger(__name__)

PROVER_DIR = Path(__file__).parent
HISTORY_DIR = PROVER_DIR / ".prover_history"
TRACES_DIR = PROVER_DIR / "baselines" / "traces"
KB_PATH = PROVER_DIR / "proof_knowledge.json"
MAX_JSONL_FILE_MB = 100

LEAN_TACTIC_KW = (
    "by ", "simp", "exact ", "rw [", "sorry", "have :", "obtain",
    "cases ", "induction ", "rcases", "intro ", "apply ", "refine ",
    "constructor", "use ", "unfold ", "dsimp", "change ", "show ",
    "omega", "linarith", "ring", "norm_num", "decide",
)
LEAN_ERROR_RE = [
    (r"error:\s*(.{10,120})", "lean_error"),
    (r"unsolved goals?\b", "unsolved_goals"),
    (r"type mismatch", "type_mismatch"),
    (r"tactic '(\w+)' failed", "tactic_failed"),
    (r"unknown identifier\s+'?(\w+)'?", "unknown_identifier"),
    (r"BUILD FAIL", "build_fail"),
]
BUILD_SUCCESS_KW = ("BUILD SUCCESS", "Build completed successfully", "[100%] Built", "no errors", "0 errors")


def load_json(path: Path, default=None):
    if not path.exists():
        return default
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, OSError):
        return default


def save_json(path: Path, data):
    path.write_text(json.dumps(data, indent=2, ensure_ascii=False), encoding="utf-8")


# ── Source 1: .prover_history/*.json ─────────────────────────────

def mine_attempt_history(history_dir: Path) -> Tuple[List[Dict], List[Dict]]:
    successes, failures = [], []
    for f in sorted(history_dir.glob("*.json")):
        records = load_json(f, [])
        if not records:
            continue
        stem = f.stem
        for r in records:
            tactic = r.get("tactic", "").strip()
            outcome = r.get("outcome", "")
            if not tactic or len(tactic) < 5:
                continue
            if outcome == "success":
                successes.append({"tactic": tactic, "source_file": stem,
                                  "session_id": r.get("session_id", ""),
                                  "timestamp": r.get("timestamp", "")})
            elif outcome in ("build_fail", "no_progress", "regression"):
                failures.append({"tactic": tactic, "outcome": outcome,
                                 "error_category": r.get("error_category", ""),
                                 "error_excerpt": r.get("error_excerpt", "")[:200],
                                 "source_file": stem,
                                 "session_id": r.get("session_id", "")})
    return successes, failures


# ── Source 2: baselines/traces/*.json ────────────────────────────

def mine_trace_conversations(traces_dir: Path) -> Tuple[List[Dict], List[Dict], List[Dict]]:
    cookbook, failed, api = [], [], []
    for f in sorted(traces_dir.glob("*.json")):
        trace = load_json(f, [])
        if not trace or not isinstance(trace, list):
            continue
        name = f.stem
        for entry in trace:
            agent, role = entry.get("agent", ""), entry.get("role", "")
            tool, result = entry.get("tool_call", ""), entry.get("tool_result", "")
            content = entry.get("content", "")
            if tool in ("submit_tactic", "file_replace_sorry"):
                args = entry.get("tool_args", {})
                tac = (args.get("tactic", "") or args.get("code", "")) if isinstance(args, dict) else str(args)[:200]
                if tac and len(tac) > 3:
                    pass  # tactic_attempts tracked but not used beyond counting
            if agent == "CoordinatorAgent" and tool == "set_attack_plan":
                reason = entry.get("tool_args", {}).get("reason", "") if isinstance(entry.get("tool_args"), dict) else ""
                steps = result or content
                if reason or steps:
                    cookbook.append({"name": f"plan_{name}", "category": "strategy",
                                    "when": reason[:200] or "multi-step proof plan",
                                    "tactic": "", "after": str(steps)[:300] if steps else "",
                                    "source": name})
            if agent == "TacticAgent" and role in ("text_response", "respond"):
                for ep in _extract_error_patterns(content):
                    failed.append({"what_failed": ep["what"], "why": ep["why"],
                                   "lesson": ep["lesson"], "trace": name})
    return cookbook, failed, api


def _extract_error_patterns(content: str) -> List[Dict]:
    patterns = []
    sigs = [
        (r"type mismatch.*expected:\s*(.{10,80})", "type_mismatch",
         "Type mismatch — check for implicit args or missing casts"),
        (r"unknown identifier\s*'(\w+)'", "unknown_identifier",
         "Unknown identifier — need import or Mathlib search"),
        (r"tactic '(\w+)' failed", "tactic_failed",
         "Tactic failed on this goal — try decomposition"),
        (r"unsolved goals?", "unsolved_goals", "Left unsolved subgoals — chain or decompose"),
        (r"function expected.*got\s*(.{10,60})", "function_expected",
         "Function expected — missing implicit argument"),
        (r"omega failed", "omega_failed",
         "omega can't handle this — cast to Nat/Int first or use linarith"),
    ]
    for regex, category, lesson in sigs:
        for m in re.finditer(regex, content, re.IGNORECASE):
            patterns.append({"what": m.group(0)[:120], "why": category, "lesson": lesson})
    return patterns


# ── Source 3: Claude Code JSONL sessions ─────────────────────────

def _text_from_content(content) -> str:
    if isinstance(content, str):
        return content
    if isinstance(content, list):
        return "\n".join(i.get("text", "") for i in content
                         if isinstance(i, dict) and i.get("type") == "text")
    return ""


def _classify_errors(text: str) -> List[Dict]:
    errors = []
    for regex, category in LEAN_ERROR_RE:
        for m in re.finditer(regex, text, re.IGNORECASE):
            errors.append({"what": m.group(0)[:150], "category": category})
    return errors


def _is_success(text: str) -> bool:
    t = text.lower()
    return any(k.lower() in t for k in BUILD_SUCCESS_KW)


def _extract_tactic_blocks(text: str) -> List[str]:
    blocks, cur = [], []
    for line in text.split("\n"):
        s = line.strip()
        if s.startswith("--") or s.startswith("/-"):
            continue
        if any(k in s for k in LEAN_TACTIC_KW) or (cur and (s.endswith(",") or s.endswith("⟨"))):
            cur.append(s)
        elif cur:
            block = " ".join(cur)
            if len(block) > 5:
                blocks.append(block)
            cur = []
    if cur and len(" ".join(cur)) > 5:
        blocks.append(" ".join(cur))
    return blocks


_ERROR_LESSONS = {
    "lean_error": "Build error — check syntax and imports",
    "unsolved_goals": "Left unsolved subgoals — chain more tactics or decompose",
    "type_mismatch": "Type mismatch — check for implicit args or missing casts",
    "tactic_failed": "Tactic failed on this goal — try decomposition or alternative",
    "unknown_identifier": "Unknown identifier — need import or Mathlib search",
    "build_fail": "Build failed — review error output for root cause",
}


def mine_claude_jsonl(jsonl_dir: Path) -> Tuple[List[Dict], List[Dict]]:
    """Extract Lean proof patterns from Claude Code JSONL session files.

    Line-by-line scanning (no full-file load). Tracks tactic->build sequences
    for breakthrough detection, repeated failures, and error-pattern lessons.
    Returns (cookbook_entries, failed_approaches).
    """
    cookbook, failed = [], []
    if not jsonl_dir or not jsonl_dir.exists():
        return cookbook, failed
    jsonl_files = sorted(jsonl_dir.glob("*.jsonl"))
    if not jsonl_files:
        return cookbook, failed

    failure_streaks: Dict[str, List[Dict]] = defaultdict(list)
    tactic_fail_counts: Counter = Counter()

    for fpath in jsonl_files:
        fsize_mb = fpath.stat().st_size / (1024 * 1024)
        if fsize_mb > MAX_JSONL_FILE_MB:
            log.warning("Skipping %s (%.1f MB > %d MB limit)", fpath.name, fsize_mb, MAX_JSONL_FILE_MB)
            continue
        sid = fpath.stem
        pending: Dict[str, Tuple[str, str, int]] = {}
        recent: List[Dict] = []

        with open(fpath, encoding="utf-8") as fh:
            for lnum, raw in enumerate(fh):
                try:
                    msg = json.loads(raw)
                except (json.JSONDecodeError, ValueError):
                    continue
                mtype = msg.get("type", "")

                if mtype == "assistant":
                    inner = msg.get("message", {})
                    if not isinstance(inner, dict):
                        continue
                    content = inner.get("content", [])
                    if not isinstance(content, list):
                        continue
                    for item in content:
                        if not isinstance(item, dict):
                            continue
                        it = item.get("type", "")
                        if it == "tool_use":
                            tid = item.get("id", "")
                            if tid:
                                pending[tid] = (item.get("name", ""),
                                                json.dumps(item.get("input", {}), ensure_ascii=False),
                                                lnum)
                        elif it == "text":
                            text = item.get("text", "")
                            if any(k in text for k in LEAN_TACTIC_KW):
                                for blk in _extract_tactic_blocks(text):
                                    recent.append({"tactic": blk[:500], "session": sid, "line": lnum,
                                                   "timestamp": msg.get("timestamp", "")})
                                    if len(recent) > 50:
                                        recent.pop(0)

                elif mtype == "user":
                    inner = msg.get("message", {})
                    if not isinstance(inner, dict):
                        continue
                    content = inner.get("content", [])
                    if not isinstance(content, list):
                        continue
                    for item in content:
                        if not isinstance(item, dict) or item.get("type") != "tool_result":
                            continue
                        tuid = item.get("tool_use_id", "")
                        if not tuid or tuid not in pending:
                            continue
                        tname, inp_str, tline = pending.pop(tuid)
                        result_text = _text_from_content(item.get("content", ""))
                        is_edit = tname in ("Edit", "Write") and ".lean" in inp_str.lower()
                        is_build = tname == "Bash" and any(k in inp_str.lower() for k in ("lake build", "lake env", "lean --"))
                        if not is_edit and not is_build:
                            continue

                        edited_tac = ""
                        if is_edit:
                            try:
                                inp = json.loads(inp_str)
                                old, new = inp.get("old_string", ""), inp.get("new_string", "")
                                if "sorry" in old and new:
                                    edited_tac = new[:500]
                            except (json.JSONDecodeError, ValueError):
                                pass

                        errors = _classify_errors(result_text)
                        ok = _is_success(result_text)

                        if ok and recent:
                            for tac in recent[-5:]:
                                sig = _tactic_signature(tac["tactic"])
                                streak = failure_streaks.get(sig, [])
                                if len(streak) >= 3:
                                    cat = _categorize_tactic(tac["tactic"])
                                    avoid = [f'{s.get("category","")}: {s.get("what","")[:80]}' for s in streak[-3:]]
                                    cookbook.append({
                                        "name": f"breakthrough_{cat}_{sid[:8]}_{tline}",
                                        "category": cat,
                                        "when": f"After {len(streak)} failures, this tactic succeeded",
                                        "tactic": tac["tactic"][:500], "after": "",
                                        "not": avoid[:3], "source": f"claude_jsonl:{sid}",
                                    })
                            failure_streaks.clear()
                            if edited_tac:
                                cat = _categorize_tactic(edited_tac)
                                cookbook.append({
                                    "name": f"jsonl_{cat}_{sid[:8]}_{tline}",
                                    "category": cat,
                                    "when": f"Lean proof fix in Claude session {sid[:8]}",
                                    "tactic": edited_tac[:500], "after": "",
                                    "source": f"claude_jsonl:{sid}",
                                })
                        elif errors:
                            tac_rec = edited_tac or (recent[-1]["tactic"] if recent else "")
                            if tac_rec:
                                sig = _tactic_signature(tac_rec)
                                for err in errors:
                                    failure_streaks[sig].append(err)
                                tactic_fail_counts[sig] += 1
                                for err in errors:
                                    failed.append({
                                        "what_failed": tac_rec[:150],
                                        "why": f'{err["category"]}: {err["what"]}',
                                        "lesson": _ERROR_LESSONS.get(err["category"], "Try alternative"),
                                        "session": sid, "line": tline,
                                    })
                                    if len(failed) > 2000:
                                        failed.pop(0)
                        if len(recent) > 50:
                            recent = recent[-25:]

    for sig, count in tactic_fail_counts.most_common(30):
        if count < 3:
            continue
        streak = failure_streaks.get(sig, [])
        ex = streak[-1] if streak else {}
        failed.append({"what_failed": sig[:150],
                       "why": f"Repeated {count}x: {ex.get('what', 'unknown')[:100]}",
                       "lesson": f"Tactic failed {count} times — try alternative",
                       "session": "aggregated", "line": 0})
    return cookbook, failed


# ── Deduplication & merging ──────────────────────────────────────

def _tactic_signature(tactic: str) -> str:
    return re.sub(r"\s+", " ", tactic.strip().lower())[:150]


def dedup_cookbook(existing: List[Dict], new_entries: List[Dict]) -> List[Dict]:
    sigs = {e.get("name", "").lower() + "|" + _tactic_signature(e.get("tactic", "")) for e in existing}
    merged = list(existing)
    for ne in new_entries:
        sig = ne.get("name", "").lower() + "|" + _tactic_signature(ne.get("tactic", ""))
        if sig not in sigs:
            merged.append(ne)
            sigs.add(sig)
    return merged


def dedup_failures(existing: List[Dict], new_entries: List[Dict]) -> List[Dict]:
    whats = {e.get("what_failed", "").lower()[:100] for e in existing}
    merged = list(existing)
    for ne in new_entries:
        w = ne.get("what_failed", "").lower()[:100]
        if w and w not in whats:
            merged.append(ne)
            whats.add(w)
    return merged


def _extract_successful_patterns(successes: List[Dict], failures: List[Dict]) -> List[Dict]:
    by_src = defaultdict(list)
    for s in successes: by_src[s["source_file"]].append(s)
    fail_by = defaultdict(list)
    for f in failures: fail_by[f["source_file"]].append(f)
    patterns = []
    for source, succs in by_src.items():
        nearby = fail_by.get(source, [])
        for s in succs:
            tactic = s["tactic"]
            if tactic.strip() in ("sorry", "exact?", "apply?", "skip"): continue
            cat = _categorize_tactic(tactic)
            avoid = list(dict.fromkeys(f["tactic"][:100] for f in nearby[:5]
                                       if f["tactic"] and f["tactic"].strip() != "sorry" and len(f["tactic"]) > 5))[:3]
            patterns.append({"name": f"mined_{cat}_{source}_{len(patterns)}", "category": cat,
                             "when": f"Goal from {source.replace('_', ' ').split(' L')[0]}",
                             "tactic": tactic, "after": "", "not": avoid, "source": "mined_from_history"})
    return patterns


def _categorize_tactic(tactic: str) -> str:
    t = tactic.lower()
    if any(k in t for k in ["omega", "linarith", "ring", "nat"]): return "arithmetic"
    if any(k in t for k in ["simp", "rw", "unfold"]): return "simplification"
    if any(k in t for k in ["exact", "apply", "refine"]): return "application"
    if any(k in t for k in ["constructor", "cases", "rcases", "induction"]): return "decomposition"
    if any(k in t for k in ["intro", "obtain", "have", "use"]): return "introduction"
    if any(k in t for k in ["dsimp", "change", "show"]): return "normalization"
    return "general"


def _extract_failure_lessons(failures: List[Dict]) -> List[Dict]:
    nc, ne = Counter(), {}
    for f in failures:
        n = _tactic_signature(f["tactic"])
        nc[n] += 1
        if n not in ne: ne[n] = f
    lessons = []
    for norm, count in nc.most_common(20):
        if count < 2: continue
        ex = ne[norm]
        ec, ee = ex.get("error_category", ""), ex.get("error_excerpt", "")
        if ec == "type_mismatch" or "type mismatch" in ee.lower(): lesson = "Cast or add explicit type ascription"
        elif ec == "unknown_identifier" or "unknown" in ee.lower(): lesson = "Import or search for correct lemma name"
        elif "unsolved" in ee.lower(): lesson = "Left subgoals — chain more tactics or decompose"
        else: lesson = f"Failed {count}x — try alternative approach"
        lessons.append({"what_failed": ex["tactic"][:150], "why": ee[:200] if ee else ec,
                        "lesson": lesson, "file": ex.get("source_file", ""), "attempts": count})
    return lessons


# ── Main pipeline ────────────────────────────────────────────────

def run_mining(
    history_dir: Path = HISTORY_DIR,
    traces_dir: Path = TRACES_DIR,
    kb_path: Path = KB_PATH,
    jsonl_dir: Optional[Path] = None,
    dry_run: bool = False,
) -> Dict:
    kb = load_json(kb_path, {"version": 3, "entries": {},
                              "tactic_cookbook": {"patterns": []},
                              "failed_approaches": [], "mathlib_api": {}})
    existing_patterns = kb.get("tactic_cookbook", {}).get("patterns", [])
    existing_failures = kb.get("failed_approaches", [])

    hist_succ, hist_fail = mine_attempt_history(history_dir)
    mined_patterns = _extract_successful_patterns(hist_succ, hist_fail)
    mined_lessons = _extract_failure_lessons(hist_fail)
    trace_plans, trace_fails, _ = mine_trace_conversations(traces_dir)
    jsonl_patterns, jsonl_fails = mine_claude_jsonl(jsonl_dir) if jsonl_dir else ([], [])

    merged_p = dedup_cookbook(existing_patterns, mined_patterns + trace_plans + jsonl_patterns)
    merged_f = dedup_failures(existing_failures, mined_lessons + trace_fails + jsonl_fails)
    jsonl_count = len(list(jsonl_dir.glob("*.jsonl"))) if jsonl_dir and jsonl_dir.exists() else 0

    stats = {
        "history_files": len(list(history_dir.glob("*.json"))),
        "trace_files": len(list(traces_dir.glob("*.json"))),
        "jsonl_files": jsonl_count,
        "hist_successes": len(hist_succ), "hist_failures": len(hist_fail),
        "mined_patterns": len(mined_patterns), "mined_failure_lessons": len(mined_lessons),
        "trace_plans": len(trace_plans), "trace_failures": len(trace_fails),
        "jsonl_patterns": len(jsonl_patterns), "jsonl_failures": len(jsonl_fails),
        "existing_patterns": len(existing_patterns), "existing_failures": len(existing_failures),
        "merged_patterns": len(merged_p), "merged_failures": len(merged_f),
        "new_patterns_added": len(merged_p) - len(existing_patterns),
        "new_failures_added": len(merged_f) - len(existing_failures),
    }
    if not dry_run:
        kb["tactic_cookbook"]["patterns"] = merged_p
        kb["failed_approaches"] = merged_f
        kb["last_updated"] = datetime.now().isoformat()
        save_json(kb_path, kb)
    return stats


def main():
    dry_run = "--dry-run" in sys.argv
    json_dir = jsonl_dir = None
    for i, arg in enumerate(sys.argv):
        if arg == "--json-dir" and i + 1 < len(sys.argv):
            json_dir = Path(sys.argv[i + 1])
        if arg == "--jsonl-dir" and i + 1 < len(sys.argv):
            jsonl_dir = Path(sys.argv[i + 1])
    history, traces, kb = HISTORY_DIR, TRACES_DIR, KB_PATH
    if json_dir:
        history, traces = json_dir / ".prover_history", json_dir / "baselines" / "traces"
        kb = json_dir / "proof_knowledge.json"
    print("Mining prover sessions...")
    print(f"  History: {history} ({len(list(history.glob('*.json')))} files)")
    print(f"  Traces:  {traces} ({len(list(traces.glob('*.json')))} files)")
    jsonl_info = str(jsonl_dir) if jsonl_dir else "(none)"
    if jsonl_dir and jsonl_dir.exists():
        jc, js = len(list(jsonl_dir.glob("*.jsonl"))), sum(f.stat().st_size for f in jsonl_dir.glob("*.jsonl"))
        jsonl_info += f" ({jc} files, {js / (1024*1024):.0f} MB)"
    print(f"  JSONL:   {jsonl_info}")
    print(f"  KB:      {kb}")
    if dry_run: print("  Mode:    DRY RUN (no changes)")
    print()
    stats = run_mining(history, traces, kb, jsonl_dir=jsonl_dir, dry_run=dry_run)
    print("=== Mining Results ===")
    for k, v in stats.items(): print(f"  {k}: {v}")
    print("\nDRY RUN — no changes written." if dry_run else
          f"\nKB updated: {stats['merged_patterns']} patterns, {stats['merged_failures']} failures")


if __name__ == "__main__":
    main()
