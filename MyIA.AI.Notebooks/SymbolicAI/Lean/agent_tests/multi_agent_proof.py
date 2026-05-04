"""
Multi-Agent Lean 4 Proof System
================================
Port of Lean-9-SK-Multi-Agents.ipynb — Semantic Kernel architecture.

Architecture (from notebook):
  - Kernel + @kernel_function plugins → agents call tools via function calling
  - 5 Agent roles: Search, Tactic, Verifier, Critic, Coordinator
  - Shared ProofState updated through plugin tool calls
  - LeanVerifier backend (fast_path ~5s, full_path ~130s)
  - Full trace instrumentation with timings

Usage:
    cd MyIA.AI.Notebooks/SymbolicAI/Lean/agent_tests
    python multi_agent_proof.py --demo 1
    python multi_agent_proof.py --demo 5 --verbose
    python multi_agent_proof.py --batch --demos 1,2,3,4,5
    python multi_agent_proof.py --demo 3 --tactic zai --critic zai
"""

import os
import sys
import json
import time
import re
import uuid
import argparse
import asyncio
from pathlib import Path
from datetime import datetime
from typing import Optional, Dict, Any, List
from dataclasses import dataclass, field
from enum import Enum

# ── Bootstrap: load .env and imports ──────────────────────────────────────────

_parent = Path(__file__).resolve().parent.parent
if str(_parent) not in sys.path:
    sys.path.insert(0, str(_parent))

from dotenv import load_dotenv
load_dotenv(_parent / ".env")

# ── Configuration ─────────────────────────────────────────────────────────────

LEAN_PROJECT_DIR = os.getenv("LEAN_PROJECT_DIR")

PROVIDERS = {
    "zai": {
        "base_url": os.getenv("ZAI_BASE_URL", "https://api.z.ai/api/coding/paas/v4"),
        "api_key": os.getenv("ZAI_API_KEY", ""),
        "models": {
            "reasoning": os.getenv("ZAI_CHAT_MODEL_ID", "glm-5.1"),
            "fast": os.getenv("ZAI_FAST_MODEL_ID", "glm-5.1"),
        }
    },
    "local": {
        "base_url": os.getenv("LOCAL_LLM_BASE_URL", ""),
        "api_key": os.getenv("LOCAL_LLM_API_KEY", ""),
        "models": {
            "reasoning": os.getenv("LOCAL_LLM_MODEL_ID", "qwen3.6-35b-a3b"),
            "fast": os.getenv("LOCAL_LLM_MODEL_ID", "qwen3.6-35b-a3b"),
        }
    },
}

SHAPLEY_IMPORTS = """import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
import CooperativeGames.Basic
"""

SHAPLEY_FILE = Path(LEAN_PROJECT_DIR) / "CooperativeGames" / "Shapley.lean" if LEAN_PROJECT_DIR else None
BASIC_FILE = Path(LEAN_PROJECT_DIR) / "CooperativeGames" / "Basic.lean" if LEAN_PROJECT_DIR else None

# Social Choice (separate Lake project)
SOCIAL_CHOICE_DIR = Path(r"C:\dev\CoursIA\MyIA.AI.Notebooks\GameTheory\social_choice_lean")
VOTING_FILE = SOCIAL_CHOICE_DIR / "SocialChoice" / "Voting.lean" if SOCIAL_CHOICE_DIR.exists() else None
VOTING_IMPORTS = """import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Sort
import SocialChoice.Definitions
"""

# ── Demo Theorems ─────────────────────────────────────────────────────────────

DEMOS = {
    1: {
        "name": "DEMO_1_REFLEXIVITY",
        "theorem": "theorem demo_rfl (n : Nat) : n = n",
        "proof": "rfl",
        "imports": None,
        "description": "Trivial - rfl suffit",
        "difficulty": "trivial",
    },
    2: {
        "name": "DEMO_2_ZERO_ADD",
        "theorem": "theorem demo_zero_add (n : Nat) : 0 + n = n",
        "proof": "omega",
        "imports": None,
        "description": "Simple - omega or Nat.zero_add",
        "difficulty": "simple",
    },
    3: {
        "name": "DEMO_3_DISTRIBUTIVITY",
        "theorem": "theorem demo_dist (a b c : Nat) : a * c + b * c = (a + b) * c",
        "proof": "omega",
        "imports": None,
        "description": "Intermediate - distributivity reversed",
        "difficulty": "intermediate",
    },
    4: {
        "name": "DEMO_4_SHAPLEY_SIMPLE",
        "theorem": "theorem test_coef_shift (n s : Nat) (h : s + 2 <= n) : (s + 1) * 1 = s + 1",
        "proof": "omega",
        "imports": SHAPLEY_IMPORTS,
        "description": "Shapley-style Nat arithmetic with Mathlib",
        "difficulty": "intermediate",
    },
    5: {
        "name": "DEMO_5_FINSET_SUM_REAL",
        "theorem": "theorem demo_finset_sum_erase {a : Type*} [DecidableEq a] [Fintype a] (s : Finset a) (x : a) (f : a -> Real) (ha : x in s) : Sum x in s.erase x, f x = Sum x in s, f x - f x",
        "proof": "have h := Finset.sum_erase_add s f ha; linarith",
        "imports": SHAPLEY_IMPORTS,
        "description": "Finset sum with erase + Real subtraction (Shapley-style)",
        "difficulty": "advanced",
    },
    # ── Real Shapley.lean sorry targets ──
    6: {
        "name": "SHAPLEY_UNIQUENESS",
        "file": str(SHAPLEY_FILE),
        "line": 513,
        "sorry_type": "full_proof",
        "theorem_name": "shapley_uniqueness",
        "theorem": "shapley_uniqueness",
        "imports": SHAPLEY_IMPORTS,
        "description": (
            "Replace sorry at line 513 of Shapley.lean. Prove shapley_uniqueness:\n"
            "any solution satisfying all 4 axioms equals Shapley value.\n"
            "Uses Mobius decomposition of games into unanimity games.\n"
            "Depends on: shapley_unanimity, shapley_efficient, shapley_symmetric, shapley_null_player.\n"
            "All helper theorems are now proved (0 sorry in their proofs).\n"
            "Pre-sorry code:\n"
            "```\n"
            "  unfold shapleyValue TUGame.marginalContribution shapleyCoef\n"
            "  simp only [TUGame.unanimityGame]\n"
            "```\n"
            "Goal should involve Finset.sum with if-then-else filters."
        ),
        "difficulty": "hard",
        "context_before": (
            "  · -- Case i ∈ T: direct computation\n"
            "    -- marginal contribution = 1 iff T\\{i} ⊆ S (and i ∉ S, given by filter)\n"
            "    -- = ∑_{S : i∉S, T\\{i} ⊆ S} c(|S|, n) = 1/|T|\n"
            "    unfold shapleyValue TUGame.marginalContribution shapleyCoef\n"
            "    simp only [TUGame.unanimityGame]\n"
        ),
        "context_after": "  · -- Case i ∉ T: i is a null player",
    },
    7: {
        "name": "SHAPLEY_EFFICIENT_COEFF",
        "file": str(SHAPLEY_FILE),
        "line": 292,
        "sorry_type": "partial_proof",
        "theorem_name": "shapley_efficient (T ≠ ∅ case)",
        "theorem": "shapley_efficient",
        "imports": SHAPLEY_IMPORTS,
        "description": (
            "Replace sorry at line 292 of Shapley.lean. Context: proving efficiency.\n"
            "We're inside `Finset.sum_eq_single` proving that T ≠ univ has zero coefficient.\n"
            "Case T ≠ ∅: need to show that coefficient |T|*c(|T|-1) equals c(|T|)*(n-|T|).\n"
            "We have `hshift := shapleyCoef_shift n (T.card - 1) (by omega)`.\n"
            "Pre-sorry code:\n"
            "```\n"
            "  have hTcard : 1 ≤ T.card := Nat.pos_of_ne_zero hT0\n"
            "  have hshift := shapleyCoef_shift (Fintype.card N) (T.card - 1) (by omega)\n"
            "```\n"
            "Goal: `↑T.card * shapleyCoef (Fintype.card N) (T.card - 1) * G.v T -\n"
            "  shapleyCoef (Fintype.card N) T.card * (↑(Fintype.card N - T.card) * G.v T) = 0`\n"
            "Key: rewrite using hshift, then use Nat subtraction properties."
        ),
        "difficulty": "hard",
        "context_before": (
            "        · -- T ≠ ∅: coefficient shift applies\n"
            "          have hTcard : 1 ≤ T.card := Nat.pos_of_ne_zero hT0\n"
            "          have hshift := shapleyCoef_shift (Fintype.card N) (T.card - 1) (by omega)\n"
        ),
        "context_after": "      (fun h => (h (Finset.mem_univ _)).elim)",
    },
    8: {
        "name": "SHAPLEY_UNIQUENESS_ALT",
        "file": str(SHAPLEY_FILE),
        "line": 513,
        "sorry_type": "full_proof",
        "theorem_name": "shapley_uniqueness (alternative entry)",
        "theorem": "shapley_uniqueness",
        "imports": SHAPLEY_IMPORTS,
        "description": (
            "Same target as Demo 6 (line 513). Alias for batch/testing.\n"
            "Prove shapley_uniqueness: any solution satisfying all 4 axioms equals Shapley value.\n"
            "Uses Mobius decomposition of games into unanimity games.\n"
            "All helper theorems proved."
        ),
        "difficulty": "very_hard",
    },
    9: {
        "name": "VOTING_MEDIAN_VOTER",
        "file": str(VOTING_FILE),
        "line": 231,
        "sorry_type": "full_proof",
        "theorem_name": "median_voter_theorem",
        "theorem": "median_voter_theorem",
        "imports": VOTING_IMPORTS,
        "description": (
            "Prove median_voter_theorem (Black 1948): for odd number of single-peaked voters,\n"
            "the median peak is a Condorcet winner.\n"
            "Goal: ∃ m, condorcet_winner prof (Finset.univ.image peaks) m\n"
            "Witness: median_peak peaks\n"
            "Key steps:\n"
            "1. For y < median: > n/2 voters have peak ≥ median, prefer median by single-peakedness\n"
            "2. For y > median: > n/2 voters have peak ≤ median, prefer median by single-peakedness\n"
            "3. Strict majority prefers median to any alternative\n"
            "Available: single_peaked_peak_unique, single_peaked_peak_best, sorted_peaks_list, median_peak\n"
            "NOTE: Requires Finset counting + sorted list median properties (hard)."
        ),
        "difficulty": "very_hard",
    },
}


# ══════════════════════════════════════════════════════════════════════════════
# SORRY EXTRACTION - Read .lean files and extract sorry contexts
# ══════════════════════════════════════════════════════════════════════════════

def extract_sorry_block(filepath: str, sorry_line: int, context_lines: int = 15) -> dict:
    """Extract the sorry context from a .lean file.

    Returns dict with:
      - full_file: complete file content
      - sorry_line: 1-based line number of sorry
      - context_before: lines before sorry (indented proof context)
      - context_after: lines after sorry (continuation)
      - proof_block: the full proof block containing the sorry
      - indentation: indentation level of the sorry
      - goal_hint: extracted from comments before sorry
    """
    content = Path(filepath).read_text(encoding="utf-8")
    lines = content.split("\n")

    if sorry_line < 1 or sorry_line > len(lines):
        return {"error": f"sorry_line {sorry_line} out of range (1-{len(lines)})"}

    sorry_text = lines[sorry_line - 1]
    indent = len(sorry_text) - len(sorry_text.lstrip())
    indent_str = sorry_text[:indent]

    # Extract goal hints from comments before sorry
    goal_hints = []
    for i in range(sorry_line - 2, max(sorry_line - 20, -1), -1):
        line = lines[i].strip()
        if line.startswith("--"):
            goal_hints.insert(0, line)
        elif line and not line.startswith("--"):
            break

    # Find the start of the proof block (theorem/lemma line)
    proof_start = sorry_line - 1
    for i in range(sorry_line - 2, -1, -1):
        stripped = lines[i].strip()
        if stripped.startswith("theorem ") or stripped.startswith("lemma ") or \
           stripped.startswith("private theorem ") or stripped.startswith("private lemma "):
            proof_start = i
            break
        if stripped.startswith("def ") or stripped.startswith("noncomputable def "):
            proof_start = i
            break

    # Find the next top-level declaration after sorry to bound the proof
    proof_end = sorry_line
    for i in range(sorry_line, min(sorry_line + 30, len(lines))):
        stripped = lines[i].strip()
        if stripped.startswith("theorem ") or stripped.startswith("lemma ") or \
           stripped.startswith("/-!") or stripped.startswith("end ") or \
           (stripped and not stripped.startswith("--") and not stripped.startswith("·")
            and not stripped.startswith("have ") and not stripped.startswith("rw ")
            and not stripped.startswith("simp") and not stripped.startswith("exact")
            and not stripped.startswith("intro") and not stripped.startswith("apply")
            and not stripped.startswith("cases") and not stripped.startswith("obtain")
            and not stripped.startswith("by_cases") and not stripped.startswith("refine")
            and not stripped.startswith("fun") and not stripped.startswith("ext")
            and not stripped.startswith("constructor") and indent > 0
            and lines[i][:1] not in (" ", "\t")):
            proof_end = i
            break

    context_before_lines = lines[max(0, sorry_line - 1 - context_lines):sorry_line - 1]
    context_after_lines = lines[sorry_line:min(len(lines), sorry_line + context_lines)]

    return {
        "filepath": filepath,
        "sorry_line": sorry_line,
        "sorry_text": sorry_text.strip(),
        "indentation": indent,
        "indent_str": indent_str,
        "goal_hints": "\n".join(goal_hints),
        "context_before": "\n".join(context_before_lines),
        "context_after": "\n".join(context_after_lines),
        "proof_block": "\n".join(lines[proof_start:proof_end + 1]),
        "full_file": content,
    }


def get_goal_state(filepath: str, sorry_line: int) -> Optional[str]:
    """Extract the actual Lean goal state at a sorry by provoking a type-mismatch error.

    Tries multiple probes in sequence: exact (), exact rfl.
    Only considers errors at the EXACT sorry line to avoid cascade errors.
    For deeply nested sorries (indent >= 8), skips probing and uses heuristics.
    """
    content = Path(filepath).read_text(encoding="utf-8")
    lines = content.split("\n")

    if sorry_line < 1 or sorry_line > len(lines):
        return None

    sorry_text = lines[sorry_line - 1]
    indent = len(sorry_text) - len(sorry_text.lstrip())
    indent_str = " " * indent

    # Skip probing for deeply nested sorries — cascade errors make it unreliable
    if indent >= 8:
        print(f"  [GoalExtract] Deeply nested sorry (indent={indent}), using heuristic")
        return _heuristic_goal_extract(lines, sorry_line)

    project_dir = Path(filepath).parent.parent
    verifier = get_verifier(str(project_dir))
    subdir = Path(filepath).parent.name
    relative_path = f"{subdir}/_GoalExtract.lean"
    tmp_path = Path(filepath).parent / "_GoalExtract.lean"

    # Try multiple probes to extract goal state
    probes = [
        "exact ()",    # Works for Unit goals; also produces type mismatch for others
        "exact rfl",   # Works for equality goals (a = b)
    ]

    for probe in probes:
        new_lines = lines[:sorry_line - 1] + [indent_str + probe] + lines[sorry_line:]
        new_content = "\n".join(new_lines)
        tmp_path.write_text(new_content, encoding="utf-8")

        result = verifier.verify_project_file(relative_path)

        raw_output = result.get("raw_output", "")

        # Accept errors within ±3 lines of the sorry — nested tactic blocks
        # can shift error reporting to adjacent lines.
        LINE_TOLERANCE = 3
        target_errors = []
        collecting = False
        for line in raw_output.split("\n"):
            m_err = re.match(r".*?(\d+):\d+: error: (.*)", line)
            if m_err:
                err_line = int(m_err.group(1))
                if abs(err_line - sorry_line) <= LINE_TOLERANCE:
                    target_errors.append(line)
                    collecting = True
                else:
                    collecting = False
            elif collecting:
                # Continuation lines for the error at the exact sorry line
                # Stop if we hit another error line or empty separator
                if line.strip() == "" or re.match(r".*?\d+:\d+: ", line):
                    collecting = False
                else:
                    target_errors.append(line)

        if not target_errors:
            print(f"  [GoalExtract] Probe '{probe}': no error at exact line {sorry_line}")
            continue

        target_error_text = "\n".join(target_errors)
        print(f"  [GoalExtract] Probe '{probe}': {target_error_text[:300]}")

        goal = _parse_goal_from_error(target_error_text)
        if goal:
            try:
                tmp_path.unlink()
            except OSError:
                pass
            return goal

    # Cleanup
    try:
        tmp_path.unlink()
    except OSError:
        pass

    # All probes failed to produce parseable goal — try heuristic from context
    return _heuristic_goal_extract(lines, sorry_line)


def _parse_goal_from_error(error_text: str) -> Optional[str]:
    """Parse Lean error text to extract the goal type."""
    # Pattern 1: "but is expected to have type ..."
    m = re.search(
        r"but is expected to have type\n?(.*?)(?:\n\n|\n[a-z]|\Z)",
        error_text, re.DOTALL,
    )
    if m:
        goal = m.group(1).strip()
        return re.sub(r'\s+', ' ', goal)

    # Pattern 2: "expected to have type ..."
    m = re.search(r"expected to have type\n?(.*?)(?:\n\n|\Z)", error_text, re.DOTALL)
    if m:
        goal = m.group(1).strip()
        return re.sub(r'\s+', ' ', goal)

    # Pattern 3: "type mismatch" followed by term and expected type
    m = re.search(
        r"type mismatch\n.*?has type\n.*?\nbut is expected to have type\n?(.*?)(?:\n\n|\Z)",
        error_text, re.DOTALL,
    )
    if m:
        goal = m.group(1).strip()
        return re.sub(r'\s+', ' ', goal)

    # Pattern 4: "⊢ ..." (goal display in error context)
    m = re.search(r"⊢ (.*?)$", error_text, re.MULTILINE)
    if m:
        return m.group(1).strip()

    return None


def _heuristic_goal_extract(lines: list, sorry_line: int) -> Optional[str]:
    """Extract goal heuristically from proof context when Lean probing fails.

    Looks at the enclosing proof statement, recent tactics, and hypotheses.
    """
    # Look backwards for the proof statement (theorem/lemma/have)
    proof_start = sorry_line - 1
    for i in range(sorry_line - 1, max(0, sorry_line - 60), -1):
        line = lines[i].strip()
        if line.startswith("theorem ") or line.startswith("lemma ") or line.startswith("have "):
            proof_start = i
            break
        if line.startswith("by ") and i < sorry_line - 3:
            # "by" without theorem = inline tactic proof
            proof_start = i
            break

    # Collect context around the sorry
    context_lines = lines[proof_start:min(sorry_line + 2, len(lines))]
    context = "\n".join(context_lines)

    # Look for the most recent goal-transforming tactic before sorry
    last_rw = None
    last_show = None
    for i in range(sorry_line - 1, max(0, sorry_line - 20), -1):
        stripped = lines[i].strip()
        if stripped.startswith("rw [") or stripped.startswith("rewrite "):
            last_rw = stripped
        if stripped.startswith("show "):
            last_show = stripped[5:].rstrip(" :=")
        if stripped.startswith("·") or stripped.startswith("case "):
            # Branch marker — the goal was set up around here
            break

    if last_show:
        print(f"  [GoalExtract] Heuristic: found 'show' → {last_show[:200]}")
        return last_show

    # Build a hint from the enclosing proof and recent tactics
    hints = []
    if last_rw:
        hints.append(f"After rewrite: {last_rw}")

    # Look at hypotheses declared right before sorry
    for i in range(sorry_line - 1, max(0, sorry_line - 8), -1):
        stripped = lines[i].strip()
        if stripped.startswith("have ") and " := " in stripped:
            hints.append(stripped)
        if stripped.startswith("by_cases "):
            hints.append(stripped)

    if hints:
        hint_str = " | ".join(hints[-3:])
        print(f"  [GoalExtract] Heuristic hints: {hint_str[:200]}")
        return None  # Return None but print hints for debugging

    return None


def verify_sorry_replacement(filepath: str, sorry_line: int, replacement: str,
                             imports: Optional[str] = None) -> dict:
    """Verify a sorry replacement by writing modified file to disk and checking Lean.

    Args:
        filepath: Path to .lean file
        sorry_line: 1-based line number of the sorry
        replacement: Tactic(s) to replace the sorry (will be indented to match)
        imports: Unused (file already has imports)

    Returns: dict with success, errors, time_s
    """
    content = Path(filepath).read_text(encoding="utf-8")
    lines = content.split("\n")

    if sorry_line < 1 or sorry_line > len(lines):
        return {"success": False, "errors": f"Line {sorry_line} out of range"}

    sorry_text = lines[sorry_line - 1]
    indent = len(sorry_text) - len(sorry_text.lstrip())
    indent_str = " " * indent

    # Build replacement lines with correct indentation
    replacement_lines = []
    for line in replacement.strip().split("\n"):
        if line.strip():
            replacement_lines.append(indent_str + line.strip())

    # Replace the sorry line in the full file
    new_lines = lines[:sorry_line - 1] + replacement_lines + lines[sorry_line:]
    new_content = "\n".join(new_lines)

    # Write modified file to disk (Lean project directory)
    tmp_path = Path(filepath).parent / "_SorryVerify.lean"
    tmp_path.write_text(new_content, encoding="utf-8")

    # Verify using verify_project_file (no command-line length limit)
    verifier = get_verifier(str(Path(filepath).parent.parent))
    subdir = Path(filepath).parent.name
    relative_path = f"{subdir}/_SorryVerify.lean"
    result = verifier.verify_project_file(relative_path)

    # Clean up temp file
    try:
        tmp_path.unlink()
    except OSError:
        pass

    # Filter errors to only those near the target sorry line.
    # Pre-existing errors elsewhere in the file should NOT cause failure.
    n_replacement_lines = len(replacement_lines)
    line_shift = max(0, n_replacement_lines - 1)
    raw_output = result.get("raw_output", "")

    # Collect ALL error locations first
    all_error_lines = []  # [(line_num, error_text)]
    current_error = []
    for line in raw_output.split("\n"):
        m_err = re.match(r".*?(\d+):\d+: error: (.*)", line)
        if m_err:
            if current_error:
                all_error_lines.append(current_error)
            current_error = [(int(m_err.group(1)), line)]
        elif current_error:
            current_error.append((current_error[0][0], line))
    if current_error:
        all_error_lines.append(current_error)

    # Separate: direct errors (at exact sorry line) vs cascade errors (nearby)
    direct_errors = []  # errors at the exact sorry line
    cascade_errors = []  # errors within ±5 lines but not at exact line
    preexisting_errors = []  # errors far from sorry (pre-existing)
    nearby_range = 5 + line_shift

    for err_block in all_error_lines:
        first_line_num = err_block[0][0]
        text = "\n".join(line_text for _, line_text in err_block)
        if first_line_num == sorry_line:
            direct_errors.append(text)
        elif abs(first_line_num - sorry_line) <= nearby_range:
            cascade_errors.append(text)
        else:
            preexisting_errors.append(text)

    # Build result
    has_direct_error = len(direct_errors) > 0
    has_cascade_error = len(cascade_errors) > 0
    is_success = not has_direct_error and not has_cascade_error

    # Extract residual goals from cascade errors (lines starting with ⊢)
    residual_goals = []
    cascade_text = "\n".join(cascade_errors)
    for line in cascade_text.split("\n"):
        stripped = line.strip()
        if stripped.startswith("⊢ ") or stripped.startswith("| ⊢ "):
            goal = stripped.lstrip("| ").lstrip("⊢ ").strip()
            if goal and goal not in residual_goals:
                residual_goals.append(goal)

    # Build error message with context
    if has_direct_error:
        error_msg = "\n".join(direct_errors)
        error_type = "tactic_failed"
    elif has_cascade_error:
        error_msg = (
            "Tactic left UNSOLVED GOALS. The tactic at line "
            f"{sorry_line} executed but did not close all goals. "
            "Cascade error:\n" + "\n".join(cascade_errors[:2])
        )
        error_type = "unsolved_goals"
    else:
        error_msg = ""
        error_type = None

    return {
        "success": is_success,
        "errors": error_msg,
        "raw_error": error_msg[:500],
        "error_type": error_type,
        "residual_goals": residual_goals,
        "all_errors": result.get("errors", ""),
        "time_s": result.get("time_s", 0),
        "backend": result.get("backend", ""),
    }


# ══════════════════════════════════════════════════════════════════════════════
# TRACE LOGGER - Full instrumentation
# ══════════════════════════════════════════════════════════════════════════════

class TraceLogger:
    """Captures full multi-agent conversation traces with timing."""

    def __init__(self, output_dir: str = "traces"):
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(exist_ok=True)
        self.entries = []
        self.session_start = time.time()
        self.phase_timings: Dict[str, float] = {}

    def log(self, agent: str, role: str, content: str, duration_s: float = 0,
            tool_name: str = None, tool_args: dict = None, tool_result: str = None,
            model: str = None, tokens: dict = None, phase: str = None,
            state_snapshot: dict = None):
        entry = {
            "timestamp": round(time.time() - self.session_start, 3),
            "agent": agent,
            "role": role,
            "content": content,
            "duration_s": round(duration_s, 3),
        }
        if tool_name:
            entry["tool_call"] = tool_name
            entry["tool_args"] = tool_args
            entry["tool_result"] = (tool_result or "")[:500]
        if model:
            entry["model"] = model
        if tokens:
            entry["tokens"] = tokens
        if phase:
            entry["phase"] = phase
        if state_snapshot:
            entry["state"] = state_snapshot
        self.entries.append(entry)

        if phase:
            self.phase_timings[phase] = self.phase_timings.get(phase, 0) + duration_s

        ts = f"[+{entry['timestamp']:.1f}s]"
        if tool_name:
            print(f"  {ts} {agent} -> {tool_name}({json.dumps(tool_args or {})[:80]}) -> {duration_s:.2f}s")
        else:
            preview = (content or "")[:120].replace("\n", " ")
            print(f"  {ts} {agent} [{role}]: {preview}...")

    def save(self, name: str = None):
        if not name:
            name = f"trace_{datetime.now().strftime('%Y%m%d_%H%M%S')}"
        path = self.output_dir / f"{name}.json"
        with open(path, "w", encoding="utf-8") as f:
            json.dump(self.entries, f, indent=2, ensure_ascii=False)
        print(f"Trace saved: {path} ({len(self.entries)} entries)")
        return str(path)

    def summary(self):
        agents = {}
        for e in self.entries:
            a = e["agent"]
            if a not in agents:
                agents[a] = {"calls": 0, "tool_calls": 0, "total_s": 0, "tokens": 0}
            agents[a]["calls"] += 1
            if e.get("tool_call"):
                agents[a]["tool_calls"] += 1
            agents[a]["total_s"] += e.get("duration_s", 0)
            if e.get("tokens"):
                agents[a]["tokens"] += e["tokens"].get("total", 0)
        return agents


# ══════════════════════════════════════════════════════════════════════════════
# PROOF STATE - Shared state between agents (from notebook cell 5)
# ══════════════════════════════════════════════════════════════════════════════

class ProofStrategy(Enum):
    EXPLORATION = "exploration"
    REFINEMENT = "refinement"
    VALIDATION = "validation"
    RECOVERY = "recovery"

class ProofPhase(Enum):
    INIT = "init"
    SEARCH = "search"
    GENERATE = "generate"
    VERIFY = "verify"
    ANALYZE = "analyze"
    COMPLETE = "complete"
    FAILED = "failed"

@dataclass
class TacticAttempt:
    tactic: str
    success: bool
    error: Optional[str] = None
    timestamp: datetime = field(default_factory=datetime.now)
    state_before: Optional[str] = None
    confidence: Optional[float] = None
    explanation: Optional[str] = None

@dataclass
class ProofState:
    """Shared state for multi-agent proof sessions (ported from notebook)."""
    session_id: str = field(default_factory=lambda: str(uuid.uuid4())[:8])
    theorem_name: str = ""
    theorem_statement: str = ""
    imports: Optional[str] = None

    current_goal: str = ""
    current_proof: List[str] = field(default_factory=list)
    phase: ProofPhase = ProofPhase.INIT
    strategy: ProofStrategy = ProofStrategy.EXPLORATION

    discovered_lemmas: List[str] = field(default_factory=list)
    tactic_history: List[TacticAttempt] = field(default_factory=list)

    iteration: int = 0
    max_iterations: int = 10
    start_time: datetime = field(default_factory=datetime.now)

    last_error: Optional[str] = None
    final_proof: Optional[str] = None
    error_count: int = 0

    verification_results: List[Dict[str, Any]] = field(default_factory=list)
    total_lean_time_ms: float = 0.0

    _next_agent: Optional[str] = field(default=None, repr=False)
    sorry_context: Optional["SorryContext"] = field(default=None, repr=False)
    strategy_mode: str = "direct"  # "direct" | "decompose" | "search_first"
    decomposition_depth: int = 0  # track how deep we've decomposed

    def add_tactic_attempt(self, tactic: str, state_before: Optional[str] = None,
                           confidence: Optional[float] = None, explanation: Optional[str] = None,
                           success: bool = False, error: Optional[str] = None) -> str:
        attempt_id = f"attempt_{len(self.tactic_history) + 1}"
        self.tactic_history.append(TacticAttempt(
            tactic=tactic, success=success, error=error,
            state_before=state_before, confidence=confidence,
            explanation=explanation,
        ))
        if success:
            self.current_proof.append(tactic)
        else:
            self.error_count += 1
            self.last_error = error
        return attempt_id

    def add_lemma(self, name: str, statement: str = "", namespace: str = "",
                  relevance: float = 0.5) -> str:
        lemma_id = f"{namespace}.{name}" if namespace else name
        lemma_info = f"{lemma_id}: {statement} (relevance: {relevance})"
        if lemma_info not in self.discovered_lemmas:
            self.discovered_lemmas.append(lemma_info)
        return lemma_id

    def add_verification(self, attempt_id: str, success: bool, output: str,
                         errors: str, exec_time_ms: float = 0.0) -> str:
        verif_id = f"verif_{len(self.verification_results) + 1}"
        self.verification_results.append({
            "id": verif_id, "attempt_id": attempt_id,
            "success": success, "output": output, "errors": errors,
            "exec_time_ms": exec_time_ms,
            "timestamp": datetime.now().isoformat(),
        })
        return verif_id

    def set_proof_complete(self, proof: str):
        self.final_proof = proof
        self.phase = ProofPhase.COMPLETE

    def increment_iteration(self):
        self.iteration += 1

    def designate_next_agent(self, agent_name: str):
        self._next_agent = agent_name

    def consume_next_agent_designation(self) -> Optional[str]:
        agent = self._next_agent
        self._next_agent = None
        return agent

    def get_state_snapshot(self, summarize: bool = True) -> Dict[str, Any]:
        if summarize:
            return {
                "session_id": self.session_id,
                "theorem": self.theorem_statement,
                "goal": self.current_goal,
                "phase": self.phase.value,
                "strategy": self.strategy.value,
                "iteration": f"{self.iteration}/{self.max_iterations}",
                "proof_steps": len(self.current_proof),
                "discovered_lemmas": len(self.discovered_lemmas),
                "errors": self.error_count,
                "last_error": self.last_error,
                "previous_tactics": [a.tactic for a in self.tactic_history[-3:]],
            }
        return self.to_dict()

    @property
    def proof_complete(self) -> bool:
        return self.phase == ProofPhase.COMPLETE

    @property
    def is_done(self) -> bool:
        return self.phase in (ProofPhase.COMPLETE, ProofPhase.FAILED)

    def snapshot(self) -> dict:
        return self.get_state_snapshot(summarize=True)

    def to_dict(self) -> Dict[str, Any]:
        return {
            "session_id": self.session_id,
            "theorem_name": self.theorem_name,
            "theorem_statement": self.theorem_statement,
            "current_goal": self.current_goal,
            "current_proof": self.current_proof,
            "phase": self.phase.value,
            "strategy": self.strategy.value,
            "discovered_lemmas": self.discovered_lemmas,
            "iteration": self.iteration,
            "max_iterations": self.max_iterations,
            "error_count": self.error_count,
            "last_error": self.last_error,
        }


@dataclass
class SorryContext:
    """Context for sorry replacement in a .lean file."""
    filepath: str
    sorry_line: int
    goal_state: Optional[str] = None
    context_before: str = ""
    context_after: str = ""
    indentation: int = 0
    indent_str: str = ""
    full_file: str = ""
    sorry_count_before: int = 0  # number of sorry in the original file


# ══════════════════════════════════════════════════════════════════════════════
# LEAN VERIFICATION BACKEND
# ══════════════════════════════════════════════════════════════════════════════

_verifier = None

def get_verifier(project_dir: str = None) -> "LeanVerifier":
    """Get or create the persistent LeanVerifier instance."""
    global _verifier
    if _verifier is None:
        from lean_server import LeanVerifier
        pd = project_dir or LEAN_PROJECT_DIR
        _verifier = LeanVerifier(project_dir=pd, verbose=False)
    return _verifier


def verify_with_lean(theorem: str, tactic: str, imports: Optional[str],
                     project_dir: Optional[str], trace: TraceLogger,
                     agent_name: str = "LeanVerifier") -> dict:
    """Verify a Lean proof using LeanVerifier."""
    if imports:
        code = f"{imports}\n{theorem} := by {tactic}"
    else:
        code = f"{theorem} := by {tactic}"

    verifier = get_verifier(project_dir)
    start = time.time()
    result = verifier.verify(code)
    duration = time.time() - start

    success = result["success"]
    errors = result.get("errors", "")
    backend = result.get("backend", "lean_verifier")

    trace.log(
        agent=agent_name, role="verification",
        content=f"{theorem[:60]} := by {tactic[:60]}",
        duration_s=duration, tool_name="verify_proof",
        tool_args={"theorem": theorem[:80], "proof": tactic[:80]},
        tool_result=f"success={success}, backend={backend}, errors={errors[:200]}",
        phase="verify",
    )

    return {
        "success": success,
        "errors": errors,
        "time_s": duration,
        "backend": backend,
        "raw_output": result.get("raw_output", ""),
    }


# ══════════════════════════════════════════════════════════════════════════════
# SEMANTIC KERNEL DETECTION (from notebook cell 17)
# ══════════════════════════════════════════════════════════════════════════════

SK_AVAILABLE = False

try:
    from semantic_kernel import Kernel
    from semantic_kernel.agents import ChatCompletionAgent
    from semantic_kernel.connectors.ai.open_ai import OpenAIChatCompletion
    from semantic_kernel.functions import kernel_function
    SK_AVAILABLE = True
    print("Semantic Kernel available - using ChatCompletionAgent")
except ImportError as e:
    print(f"Semantic Kernel not available: {e}")
    # Fallback decorator (from notebook cell 8)
    def kernel_function(description="", name=None):
        def decorator(func):
            func._sk_function = True
            func._sk_description = description
            func._sk_name = name or func.__name__
            return func
        return decorator


# ══════════════════════════════════════════════════════════════════════════════
# PLUGINS - @kernel_function decorated (from notebook cells 8, 10, 12, 14)
# ══════════════════════════════════════════════════════════════════════════════

class ProofStateManagerPlugin:
    """Plugin exposing ProofState methods to agents via @kernel_function."""

    def __init__(self, state: ProofState):
        self._state = state

    @kernel_function(
        description="Get a summary of the current proof state (theorem, phase, errors, previous tactics)",
        name="get_proof_state",
    )
    def get_proof_state(self) -> str:
        return json.dumps(self._state.get_state_snapshot(summarize=True), indent=2, ensure_ascii=False)

    @kernel_function(
        description="Record a tactic attempt with confidence and explanation",
        name="log_tactic_attempt",
    )
    def log_tactic_attempt(self, tactic: str, state_before: str = "",
                           confidence: float = 0.5, explanation: str = "") -> str:
        # Don't overwrite last_error — log without error field
        attempt_id = f"log_{len(self._state.tactic_history) + 1}"
        self._state.tactic_history.append(TacticAttempt(
            tactic=tactic, success=False, error=None,
            state_before=state_before, confidence=confidence,
            explanation=explanation,
        ))
        return f"Logged: {attempt_id} ({tactic})"

    @kernel_function(
        description="Add a discovered lemma to the shared state",
        name="add_discovered_lemma",
    )
    def add_discovered_lemma(self, name: str, statement: str = "",
                             namespace: str = "", relevance: float = 0.5) -> str:
        lemma_id = self._state.add_lemma(name, statement, namespace, relevance)
        return f"Added lemma: {lemma_id}"

    @kernel_function(
        description="Record a Lean verification result",
        name="add_verification_result",
    )
    def add_verification_result(self, attempt_id: str, success: bool,
                                output: str = "", errors: str = "",
                                exec_time_ms: float = 0.0) -> str:
        verif_id = self._state.add_verification(
            attempt_id=attempt_id, success=success,
            output=output, errors=errors, exec_time_ms=exec_time_ms,
        )
        return f"Recorded: {verif_id} (success={success})"

    @kernel_function(
        description="Mark the proof as complete with the final tactic",
        name="set_proof_complete",
    )
    def set_proof_complete(self, proof: str) -> str:
        self._state.set_proof_complete(proof)
        return f"Proof complete: {proof}"


class LeanSearchPlugin:
    """Plugin for Mathlib lemma search (from notebook cell 10)."""

    def __init__(self):
        self._known_lemmas = {
            "Nat.add_zero": ("n + 0 = n", "Nat"),
            "Nat.zero_add": ("0 + n = n", "Nat"),
            "Nat.add_comm": ("n + m = m + n", "Nat"),
            "Nat.add_assoc": ("(n + m) + k = n + (m + k)", "Nat"),
            "Nat.mul_one": ("n * 1 = n", "Nat"),
            "Nat.one_mul": ("1 * n = n", "Nat"),
            "Nat.mul_comm": ("n * m = m * n", "Nat"),
            "Nat.add_mul": ("(a + b) * c = a * c + b * c", "Nat"),
            "Nat.mul_add": ("a * (b + c) = a * b + a * c", "Nat"),
            "Nat.left_distrib": ("n * (m + k) = n * m + n * k", "Nat"),
            "Nat.right_distrib": ("(n + m) * k = n * k + m * k", "Nat"),
            "Eq.refl": ("a = a", "Logic"),
            "Eq.symm": ("a = b -> b = a", "Logic"),
            "Finset.sum_erase_add": ("sum s f = sum (s.erase a) f + f a", "Finset"),
        }

    @kernel_function(
        description="Search for Mathlib lemmas relevant to a goal",
        name="search_mathlib_lemmas",
    )
    def search_mathlib_lemmas(self, goal: str, max_results: int = 10) -> str:
        goal_lower = goal.lower()
        results = []
        keywords = goal_lower.replace("+", "add").replace("*", "mul").replace("=", "eq").split()

        for name, (statement, namespace) in self._known_lemmas.items():
            score = 0.0
            name_lower = name.lower()
            for kw in keywords:
                if kw in name_lower:
                    score += 0.3
                if kw in statement.lower():
                    score += 0.2
            if "comm" in goal_lower and "comm" in name_lower:
                score += 0.4
            if "distrib" in goal_lower and "distrib" in name_lower:
                score += 0.4
            if "erase" in goal_lower and "erase" in name_lower:
                score += 0.5
            if "sum" in goal_lower and "sum" in name_lower:
                score += 0.4
            if score > 0:
                results.append({
                    "name": name, "statement": statement,
                    "namespace": namespace, "relevance": min(score, 1.0),
                })

        results.sort(key=lambda x: x["relevance"], reverse=True)
        return json.dumps(results[:max_results], indent=2, ensure_ascii=False)


class LeanTacticPlugin:
    """Plugin for tactic generation heuristics (from notebook cell 12)."""

    def __init__(self):
        self._heuristics = {
            "equality": ["rfl", "exact", "simp", "ring", "omega"],
            "nat_arithmetic": ["omega", "simp", "decide"],
            "ring_expression": ["ring", "ring_nf"],
            "forall": ["intro", "intros", "apply"],
            "exists": ["use", "exists", "exact"],
            "and": ["constructor", "exact And.intro"],
            "or": ["left", "right"],
            "implication": ["intro", "apply", "exact"],
        }

    @kernel_function(
        description="Generate tactic suggestions based on the goal pattern",
        name="generate_tactics",
    )
    def generate_tactics(self, goal: str, difficulty: str = "simple") -> str:
        suggestions = []
        goal_lower = goal.lower()
        detected = []

        if "=" in goal:
            detected.append("equality")
        if any(x in goal_lower for x in ["nat", "n +", "m +", "+ 0", "0 +"]):
            detected.append("nat_arithmetic")
        if any(x in goal for x in ["*", "+"]) and "=" in goal:
            detected.append("ring_expression")
        if "forall" in goal_lower or "∀" in goal:
            detected.append("forall")
        if "exists" in goal_lower or "∃" in goal:
            detected.append("exists")

        seen = set()
        for pattern in detected:
            for tactic in self._heuristics.get(pattern, []):
                if tactic not in seen:
                    seen.add(tactic)
                    confidence = 0.7 if difficulty == "simple" else 0.5
                    suggestions.append({
                        "tactic": tactic, "confidence": confidence,
                        "pattern": pattern,
                    })

        if not suggestions:
            suggestions = [
                {"tactic": "rfl", "confidence": 0.3, "pattern": "default"},
                {"tactic": "simp", "confidence": 0.3, "pattern": "default"},
                {"tactic": "omega", "confidence": 0.3, "pattern": "default"},
            ]

        return json.dumps(suggestions, indent=2, ensure_ascii=False)

    @kernel_function(
        description="Analyze why a tactic failed and suggest corrections",
        name="analyze_failure",
    )
    def analyze_failure(self, tactic: str, error: str, goal: str = "") -> str:
        hints = []
        if "No goals to be solved" in error:
            hints.append("First tactic already closed the goal. Remove trailing tactics like `rfl`.")
        elif "made no progress" in error:
            hints.append("Tactic didn't change the goal. Try a different approach.")
        elif "unknown tactic" in error:
            hints.append("Tactic requires Mathlib import. Try omega, simp, or rw instead.")
        elif "could not prove the goal" in error:
            hints.append("Tactic applicable but couldn't close the goal. Try a more powerful tactic.")
        elif "unknown identifier" in error:
            hints.append("Lemma name not found. Check exact spelling or search for alternatives.")

        return json.dumps({
            "tactic": tactic, "error_type": "progress" if "progress" in error else "type_error",
            "hints": hints, "suggestion": hints[0] if hints else "Try a different tactic.",
        }, indent=2, ensure_ascii=False)

    @kernel_function(
        description="Submit a decomposition: split the current goal into sub-goals using 'have'. Each sub-goal starts as sorry.",
        name="submit_decomposition",
    )
    def submit_decomposition(self, have_name: str, have_type: str,
                             have_proof: str = "sorry",
                             main_tactic: str = "sorry") -> str:
        indent = "  "
        lines = [
            f"have {have_name} : {have_type} := by {have_proof}",
            main_tactic,
        ]
        decomposition = f"\n{indent}".join(lines)
        return json.dumps({
            "decomposition": decomposition,
            "have_name": have_name,
            "have_type": have_type,
            "have_proof": have_proof,
            "main_tactic": main_tactic,
        }, indent=2, ensure_ascii=False)


class LeanVerificationPlugin:
    """Plugin for Lean verification using LeanVerifier (adapted from notebook cell 14)."""

    def __init__(self, project_dir: Optional[str] = None, imports: Optional[str] = None,
                 trace: Optional[TraceLogger] = None,
                 sorry_context: Optional[SorryContext] = None):
        self._project_dir = project_dir
        self._imports = imports or ""
        self._trace = trace
        self._sorry_context = sorry_context

    @kernel_function(
        description="Verify a complete Lean proof (theorem + tactics). Returns JSON with success/errors/time.",
        name="verify_proof",
    )
    def verify_proof(self, theorem_statement: str, proof_tactics: str) -> str:
        start = time.time()
        verifier = get_verifier(self._project_dir)

        if "by" not in proof_tactics and ":=" not in proof_tactics:
            body = f"{theorem_statement} := by {proof_tactics}"
        elif ":=" in proof_tactics:
            body = f"{theorem_statement} {proof_tactics}"
        else:
            body = f"{theorem_statement} := {proof_tactics}"

        code = f"{self._imports}\n{body}" if self._imports else body
        result = verifier.verify(code)
        exec_time_ms = (time.time() - start) * 1000

        if self._trace:
            self._trace.log(
                agent="LeanVerification", role="verification",
                content=f"{theorem_statement[:60]} := by {proof_tactics[:60]}",
                duration_s=exec_time_ms / 1000, tool_name="verify_proof",
                tool_args={"theorem": theorem_statement[:80], "proof": proof_tactics[:80]},
                tool_result=f"success={result['success']}, errors={result.get('errors', '')[:200]}",
                phase="verify",
            )

        return json.dumps({
            "success": result["success"],
            "errors": result.get("errors", ""),
            "exec_time_ms": round(exec_time_ms, 2),
            "backend": result.get("backend", "lean_verifier"),
        }, indent=2, ensure_ascii=False)

    @kernel_function(
        description="Verify a tactic as sorry replacement in the actual .lean file. Returns success/errors/residual_goals/sorry_count.",
        name="verify_sorry_replacement",
    )
    def verify_sorry_replacement(self, tactic: str) -> str:
        if not self._sorry_context:
            return json.dumps({"success": False, "errors": "No sorry context"})
        start = time.time()
        result = verify_sorry_replacement(
            filepath=self._sorry_context.filepath,
            sorry_line=self._sorry_context.sorry_line,
            replacement=tactic,
        )
        duration = time.time() - start

        # Count sorry in modified file for decomposition detection
        sorry_count = self._count_sorry_after_replacement(tactic)

        if self._trace:
            self._trace.log(
                agent="Verification", role="sorry_verify",
                content=f"tactic={tactic[:80]} → success={result['success']}",
                duration_s=duration, tool_name="verify_sorry_replacement",
                tool_result=f"success={result['success']}, sorry_count={sorry_count}",
                phase="verify",
            )

        return json.dumps({
            "success": result["success"],
            "errors": result.get("errors", "")[:500],
            "error_type": result.get("error_type"),
            "residual_goals": result.get("residual_goals", []),
            "sorry_count": sorry_count,
            "time_s": round(duration, 2),
        }, indent=2, ensure_ascii=False)

    def _count_sorry_after_replacement(self, tactic: str) -> int:
        """Count sorry occurrences in the file after replacing sorry with tactic."""
        if not self._sorry_context:
            return -1
        content = self._sorry_context.full_file
        lines = content.split("\n")
        sorry_idx = self._sorry_context.sorry_line - 1
        indent = self._sorry_context.indentation
        indent_str = " " * indent
        replacement_lines = [indent_str + l.strip() for l in tactic.strip().split("\n") if l.strip()]
        new_lines = lines[:sorry_idx] + replacement_lines + lines[sorry_idx + 1:]
        return "\n".join(new_lines).count("sorry")


# ══════════════════════════════════════════════════════════════════════════════
# AGENT INSTRUCTIONS (from notebook cell 17)
# ══════════════════════════════════════════════════════════════════════════════

SEARCH_AGENT_INSTRUCTIONS = """Tu es l'agent de RECHERCHE de lemmes pour le theorem proving en Lean 4.

TON ROLE UNIQUE:
- Chercher des lemmes Mathlib pertinents pour le theoreme courant
- Identifier les lemmes qui peuvent aider a la preuve
- Enregistrer les lemmes trouves dans l'etat partage

WORKFLOW:
1. Lis l'etat avec get_proof_state() pour comprendre le theoreme
2. Utilise search_mathlib_lemmas() avec des mots-cles pertinents
3. Enregistre les lemmes utiles avec add_discovered_lemma()
4. Delegue a TacticAgent quand tu as trouve des lemmes

IMPORTANT:
- Cherche des lemmes LIES au but (egalites, arithmetique, logique)
- Delegation: Apres avoir trouve 2-3 lemmes, delegue a TacticAgent
"""

TACTIC_AGENT_INSTRUCTIONS = """Tu es l'agent de GENERATION DE TACTIQUES pour le theorem proving en Lean 4.

TON ROLE UNIQUE:
- Generer des sequences de tactiques Lean pour prouver le but
- Utiliser OBLIGATOIREMENT submit_tactic() pour proposer une tactique
- Quand une preuve directe echoue, utiliser submit_decomposition() pour decomposer le but

MODES DE TRAVAIL:

A) Theoreme autonome (mode demo simple):
   Le but est un theoreme complet. Genere la tactique apres `:= by`.

B) Remplacement de sorry (mode proof partial):
   Tu dois remplacer un `sorry` dans une preuve partielle existante.
   IMPORTANT: tes tactiques doivent etre COHERENTES avec le contexte.
   - Respecte l'indentation du sorry
   - Utilise les hypotheses deja introduites (pas de `intro` si deja fait)
   - Utilise les lemmes locaux deja prouves (have/let dans le contexte)
   - Ne repete PAS les tactiques deja executees avant le sorry

STRATEGIE D'EXPLORATION (du plus simple au plus avance):
1. rfl, trivial, omega (arithmetique lineaire)
2. simp sans arguments, simp [hypothesis]
3. exact Lemma_name (lemmes Mathlib ou locaux)
4. rw [Lemma_name], rw [← Lemma_name]
5. linarith, ring, field_simp
6. Construction: constructor, exists, use
7. Cas: cases h, split_ifs, by_cases
8. Induction: induction n, strongInduction
9. Finset: Finset.sum_eq_single, Finset.sum_bij
10. Cast: Nat.cast_sub, Nat.cast_mul, mod_cast

DECOMPOSITION (quand la preuve directe echoue):
Si le but est complexe et qu'une tactique directe echoue avec "type mismatch" ou "unsolved goals",
decompose le but en sous-buts avec submit_decomposition():

Exemple 1 - Somme Finset:
  Goal: ∑ x ∈ S, f x = g x
  → submit_decomposition("h_eq", "∀ x ∈ S, f x = h x", "sorry", "simp [h_eq]")
  Cela cree: have h_eq : ∀ x ∈ S, f x = h x := by sorry
              simp [h_eq]

Exemple 2 - Egalite avec reecriture:
  Goal: a * b + c = d
  → submit_decomposition("h_mul", "a * b = e", "sorry", "rw [h_mul]; sorry")
  Cela cree: have h_mul : a * b = e := by sorry
              rw [h_mul]; sorry

IMPORTANT: La decomposition reussit si le fichier compile avec des sous-sorry.
Le systeme ciblera ensuite chaque sous-sorry separement.

WORKFLOW:
1. get_proof_state() pour comprendre le contexte complet
2. generate_tactics() pour des suggestions basees sur le goal
3. submit_tactic() ou submit_decomposition() pour soumettre
4. Attendre le resultat de verification

CONTRAINTES:
- Proposer UNE SEULE sequence de tactiques a la fois
- Si echec, lire le message d'erreur Lean attentivement et adapter
- Ne PAS repeter une tactique qui a deja echoue (voir FAILED ATTEMPTS)
- COMMENTAIRES: ajoute des `--` inline pour guider si la preuve est longue
"""

VERIFIER_AGENT_INSTRUCTIONS = """Tu es l'agent de VERIFICATION pour le theorem proving en Lean 4.

TON ROLE UNIQUE:
- Verifier les tactiques proposees avec le compilateur Lean
- Enregistrer les resultats de verification
- Determiner si la preuve est complete ou s'il faut continuer

WORKFLOW:
1. Lis l'etat avec get_proof_state()
2. Utilise verify_proof() pour tester la preuve
3. Enregistre le resultat avec add_verification_result()
4. Si succes: set_proof_complete() et termine
5. Si echec: delegue a CriticAgent pour analyse

IMPORTANT:
- Teste TOUJOURS la derniere tactique proposee
- Si succes, utilise set_proof_complete()
"""

CRITIC_AGENT_INSTRUCTIONS = """Tu es l'agent CRITIQUE pour le theorem proving en Lean 4.

TON ROLE UNIQUE:
- Analyser les echecs de verification Lean
- Classifier le type d'erreur
- Decider de la prochaine action (quel agent appeler et avec quelle strategie)

CLASSIFICATION DES ERREURS:

1. "type mismatch" → La tactique produit le mauvais type
   - Si 2+ fois avec le meme type → TacticAgent en mode "decompose"
   - Sinon → TacticAgent avec correction ciblee

2. "unknown identifier" → Lemme ou variable introuvable
   - → SearchAgent pour chercher le bon nom de lemme

3. "unsolved goals" → La tactique s'execute mais laisse des buts ouverts
   - Si les buts restants sont plus simples → TacticAgent (ajouter des tactiques)
   - Si les buts restants sont aussi complexes → TacticAgent en mode "decompose"

4. "tactic failed" → La tactique ne s'applique pas du tout
   - Analyser pourquoi (pattern non trouve, precondition non satisfaite...)
   - → TacticAgent avec une approche completement differente

5. "sorry detected" → La decomposition a introduit des sorry (SUCCES PARTIEL)
   - C'est BON signe! La decomposition reussit si le fichier compile avec des sous-sorry
   - → CoordinatorAgent pour cibler le sous-sorry suivant

DECISIONS STRATEGIQUES:
- Apres 3+ echecs avec le MEME type d'erreur → CoordinatorAgent (changement strategie)
- Apres 5+ echecs totaux → CoordinatorAgent (escalade)
- Si une decomposition compile avec sorry → SUCCES, rapporter

WORKFLOW:
1. Lis l'etat avec get_proof_state()
2. Utilise analyze_failure() pour comprendre l'erreur
3. Decide et indique le prochain agent via designate_next_agent()

IMPORTANT:
- Analyse les 3 derniers echecs pour detecter des patterns
- Si une tactique produit un "unsolved goals" plus simple, c'est du PROGRES
- Toujours fournir une EXPLICATION de pourquoi l'erreur s'est produite
"""

COORDINATOR_AGENT_INSTRUCTIONS = """Tu es l'agent COORDINATEUR pour le theorem proving en Lean 4.

TON ROLE UNIQUE:
- Superviser la session de preuve
- Debloquer les situations cycliques
- Ajuster la strategie globale

QUAND TU INTERVIENS:
- Appele par CriticAgent apres echecs repetes
- Pour decisions strategiques majeures

IMPORTANT:
- Tu es le dernier recours, prends des decisions audacieuses
"""


# ══════════════════════════════════════════════════════════════════════════════
# SUBMIT TACTIC PLUGIN - Forces structured tactic submission
# ══════════════════════════════════════════════════════════════════════════════

class SubmitTacticPlugin:
    """Plugin that forces the LLM to call submit_tactic() instead of free text."""

    def __init__(self, state: ProofState, trace: Optional[TraceLogger] = None):
        self._state = state
        self._trace = trace

    @kernel_function(
        description="Submit a Lean 4 tactic to prove the theorem. The theorem has `:= by` already — provide ONLY the tactic(s) after `by`.",
        name="submit_tactic",
    )
    def submit_tactic(self, tactic: str, confidence: float = 0.5,
                      reasoning: str = "") -> str:
        """Agent MUST call this to submit a tactic. Returns verification result."""
        attempt_id = self._state.add_tactic_attempt(
            tactic=tactic, confidence=confidence,
            explanation=reasoning,
        )
        return json.dumps({
            "attempt_id": attempt_id,
            "tactic": tactic,
            "confidence": confidence,
            "status": "submitted",
        }, ensure_ascii=False)


# ══════════════════════════════════════════════════════════════════════════════
# SIMPLE AGENT - Fallback with OpenAI function calling (from notebook cell 19)
# ══════════════════════════════════════════════════════════════════════════════

class SimpleAgent:
    """Agent using OpenAI client with function calling (from notebook's SimpleAgent)."""

    def __init__(self, name: str, instructions: str, plugins: Dict[str, Any],
                 provider: str = "zai", trace: TraceLogger = None,
                 thinking: bool = True):
        self.name = name
        self.instructions = instructions
        self.plugins = plugins
        self.thinking = thinking
        self.trace = trace

        cfg = PROVIDERS.get(provider, PROVIDERS["zai"])
        from openai import OpenAI
        self._client = OpenAI(api_key=cfg["api_key"], base_url=cfg["base_url"])
        self._model = cfg["models"]["reasoning"] if thinking else cfg["models"]["fast"]
        self.last_tool_results: List[Dict[str, str]] = []  # [{name, result}]

    def _build_openai_tools(self) -> list:
        """Convert @kernel_function methods to OpenAI tool format (from notebook)."""
        import inspect
        tools = []
        for plugin_name, plugin in self.plugins.items():
            for attr_name in dir(plugin):
                attr = getattr(plugin, attr_name)
                if not callable(attr):
                    continue
                is_sk = hasattr(attr, '_sk_function') or hasattr(attr, '__kernel_function__')
                if not is_sk:
                    continue

                sig = inspect.signature(attr)
                properties = {}
                required = []
                for param_name, param in sig.parameters.items():
                    if param_name == 'self':
                        continue
                    param_type = "string"
                    if param.annotation != inspect.Parameter.empty:
                        if param.annotation == bool:
                            param_type = "boolean"
                        elif param.annotation in (int, float):
                            param_type = "number"
                    properties[param_name] = {
                        "type": param_type,
                        "description": f"Parameter {param_name}",
                    }
                    if param.default == inspect.Parameter.empty:
                        required.append(param_name)

                if hasattr(attr, '__kernel_function_name__'):
                    func_name = attr.__kernel_function_name__
                    func_desc = getattr(attr, "__kernel_function_description__", "")
                elif hasattr(attr, '_sk_name'):
                    func_name = attr._sk_name
                    func_desc = getattr(attr, "_sk_description", "")
                else:
                    func_name = attr_name
                    func_desc = ""

                tools.append({
                    "type": "function",
                    "function": {
                        "name": f"{plugin_name}__{func_name}",
                        "description": func_desc,
                        "parameters": {
                            "type": "object",
                            "properties": properties,
                            "required": required,
                        },
                    },
                })
        return tools

    def _execute_tool_call(self, tool_name: str, arguments: dict) -> str:
        """Route tool call to the plugin method (from notebook)."""
        parts = tool_name.split("__", 1)
        if len(parts) != 2:
            return f"Error: invalid format: {tool_name}"

        plugin_name, func_name = parts
        plugin = self.plugins.get(plugin_name)
        if not plugin:
            return f"Error: plugin {plugin_name} not found"

        for attr_name in dir(plugin):
            attr = getattr(plugin, attr_name)
            if not callable(attr):
                continue
            is_sk = hasattr(attr, '_sk_function') or hasattr(attr, '__kernel_function__')
            if not is_sk:
                continue

            if hasattr(attr, '__kernel_function_name__'):
                name = attr.__kernel_function_name__
            elif hasattr(attr, '_sk_name'):
                name = attr._sk_name
            else:
                name = attr_name

            if name == func_name:
                try:
                    result = attr(**arguments)
                    return str(result)
                except Exception as e:
                    return f"Error {func_name}: {e}"

        return f"Error: {func_name} not found in {plugin_name}"

    def invoke(self, message: str, state: ProofState, skip_state: bool = False,
               max_tool_calls: int = 10) -> str:
        """Execute agent with function calling (from notebook _call_llm)."""
        self.last_tool_results = []
        state_summary = json.dumps(state.get_state_snapshot(summarize=True), indent=2)
        tools = self._build_openai_tools()

        user_content = message if skip_state else f"ETAT ACTUEL:\n{state_summary}\n\nTACHE:\n{message}"
        messages = [
            {"role": "system", "content": self.instructions},
            {"role": "user", "content": user_content},
        ]

        tool_results = []
        duration = 0

        for iteration in range(max_tool_calls):
            start = time.time()
            try:
                # Let model choose which tool to call (auto mode)
                tc = "auto" if tools else None
                response = self._client.chat.completions.create(
                    model=self._model,
                    messages=messages,
                    tools=tools if tools else None,
                    tool_choice=tc,
                    temperature=0.3,
                    max_tokens=16384,
                )
                duration += time.time() - start
                assistant_message = response.choices[0].message

                if self.trace:
                    reasoning = getattr(assistant_message, "reasoning_content", None) or ""
                    if reasoning:
                        self.trace.log(agent=self.name, role="thinking",
                                       content=reasoning[:500], duration_s=0,
                                       model=self._model)

                if assistant_message.tool_calls:
                    messages.append(assistant_message.model_dump())

                    for tool_call in assistant_message.tool_calls:
                        func_name = tool_call.function.name
                        try:
                            arguments = json.loads(tool_call.function.arguments)
                        except json.JSONDecodeError:
                            arguments = {}

                        result = self._execute_tool_call(func_name, arguments)
                        tool_results.append(func_name.split("__")[-1])
                        self.last_tool_results.append({
                            "name": func_name.split("__")[-1],
                            "result": result,
                        })

                        if self.trace:
                            self.trace.log(
                                agent=self.name, role="tool_call",
                                content=f"{func_name}({json.dumps(arguments)[:120]})",
                                duration_s=0, model=self._model,
                                tool_name=func_name, tool_args=arguments,
                                tool_result=result[:500],
                            )

                        messages.append({
                            "role": "tool",
                            "tool_call_id": tool_call.id,
                            "content": result,
                        })
                else:
                    final_response = assistant_message.content or "(no response)"
                    if tool_results:
                        actions = ", ".join(tool_results[:5])
                        final_response = f"Actions: {actions}\n{final_response}"

                    # Workaround: if model produced no tool call but has reasoning,
                    # try to extract a Lean tactic from the reasoning content
                    reasoning_text = getattr(assistant_message, "reasoning_content", None) or ""
                    if reasoning_text and final_response in ("(no response)", ""):
                        # Debug: save reasoning content for analysis
                        if self.trace:
                            self.trace.log(
                                agent=self.name, role="reasoning_debug",
                                content=f"reasoning length={len(reasoning_text)}, blocks found in reasoning text",
                                duration_s=0, model=self._model,
                            )
                        # Look for tactic patterns in reasoning:
                        # 1. ```lean ... ``` blocks — take the LONGEST (most complete)
                        lean_blocks = re.findall(r'```lean\s*\n(.*?)```', reasoning_text, re.DOTALL)
                        if lean_blocks:
                            extracted = max(lean_blocks, key=len).strip()
                            if self.trace:
                                self.trace.log(
                                    agent=self.name, role="reasoning_extract",
                                    content=f"extracted from {len(lean_blocks)} blocks (picked longest, {len(extracted)} chars):\n{extracted[:300]}",
                                    duration_s=0, model=self._model,
                                )
                            final_response = f"[{self.name}] EXTRACTED_FROM_REASONING:\n```lean\n{extracted}\n```"
                        else:
                            # Look for tactic-like patterns after "use" or "apply"
                            tactic_match = re.search(
                                r'(?:use|apply|submit|try|propose|suggest)[:\s]+(\w.*?)(?:\n|$)',
                                reasoning_text, re.IGNORECASE
                            )
                            if tactic_match:
                                final_response = f"[{self.name}] {tactic_match.group(1).strip()}"
                            else:
                                # Last resort: find lines with common Lean tactic starters
                                lean_lines = []
                                for line in reasoning_text.split("\n"):
                                    stripped = line.strip()
                                    if re.match(r'^(rw|simp|exact|apply|omega|ring|linarith|have|calc|conv|field_simp|push_cast|norm_cast|mod_cast)\b', stripped):
                                        lean_lines.append(stripped)
                                if lean_lines:
                                    final_response = f"[{self.name}] " + "\n".join(lean_lines[:3])

                    if self.trace:
                        tokens = {
                            "total": response.usage.total_tokens if response.usage else 0,
                        }
                        self.trace.log(agent=self.name, role="assistant",
                                       content=final_response[:500], duration_s=duration,
                                       model=self._model, tokens=tokens)

                    return f"[{self.name}] {final_response}"

            except Exception as e:
                if self.trace:
                    self.trace.log(agent=self.name, role="error", content=str(e), duration_s=0)
                return f"[{self.name}] Error: {e}"

        actions = ", ".join(tool_results[:5])
        return f"[{self.name}] Max tool calls reached. Actions: {actions}"


# ══════════════════════════════════════════════════════════════════════════════
# PROOF AGENT GROUP CHAT - Orchestrator (from notebook cell 33)
# ══════════════════════════════════════════════════════════════════════════════

class ProofAgentGroupChat:
    """Orchestrates agents for proof sessions (ported from notebook cell 33)."""

    def __init__(self, agents: Dict[str, Any], state: ProofState,
                 trace: Optional[TraceLogger] = None):
        self.agents = agents
        self.state = state
        self.trace = trace
        self.history = []

    def run(self, initial_message: str, verbose: bool = True) -> str:
        """Execute multi-agent proof session."""
        session_start = time.time()

        if verbose:
            print(f"\n{'='*70}")
            print(f"MULTI-AGENT PROOF: {initial_message[:80]}...")
            print(f"Agents: {list(self.agents.keys())}")
            print(f"{'='*70}")

        current_message = initial_message
        agent_order = ["SearchAgent", "TacticAgent", "VerifierAgent",
                       "CriticAgent", "CoordinatorAgent"]

        for i in range(self.state.max_iterations):
            self.state.iteration = i + 1
            self.state.increment_iteration()
            iter_start = time.time()

            # Determine which agent to use
            designated = self.state.consume_next_agent_designation()
            if designated and designated in self.agents:
                agent_name = designated
            else:
                agent_name = agent_order[i % len(agent_order)]

            agent = self.agents.get(agent_name)
            if not agent:
                continue

            if verbose:
                elapsed = time.time() - session_start
                print(f"\n--- Tour {self.state.iteration} | {agent_name} [+{elapsed:.1f}s] ---")

            # Invoke agent
            response = agent.invoke(current_message, self.state)
            iter_duration = time.time() - iter_start

            self.history.append({
                "iteration": self.state.iteration,
                "agent": agent_name,
                "response": response,
                "duration_s": iter_duration,
            })

            if verbose:
                for line in response.split('\n')[:10]:
                    if line.strip():
                        print(f"  {line}")

            if self.state.proof_complete:
                if verbose:
                    elapsed = time.time() - session_start
                    print(f"\nPROOF FOUND! [{elapsed:.1f}s]")
                    print(f"  Final tactic: {self.state.final_proof}")
                break

            current_message = response

        total_s = time.time() - session_start

        if not self.state.is_done:
            self.state.phase = ProofPhase.FAILED

        if verbose:
            print(f"\n{'='*60}")
            print(f"RESULT: {'SUCCESS' if self.state.proof_complete else 'FAILED'}")
            print(f"  Iterations: {self.state.iteration}")
            print(f"  Total time: {total_s:.1f}s")
            print(f"  Lemmas found: {len(self.state.discovered_lemmas)}")
            print(f"  Tactics tried: {len(self.state.tactic_history)}")
            print(f"{'='*60}")

        return self.state.final_proof or "Proof not found"


# ══════════════════════════════════════════════════════════════════════════════
# FACTORY - Create agents with plugins (from notebook cell 22)
# ══════════════════════════════════════════════════════════════════════════════

def create_proof_session(
    theorem: str,
    imports: Optional[str] = None,
    project_dir: Optional[str] = None,
    provider: str = "zai",
    max_iterations: int = 6,
    verbose: bool = False,
) -> tuple:
    """Create a complete proof session: state + plugins + agents + orchestrator.

    Returns (ProofAgentGroupChat, ProofState, TraceLogger).
    """
    trace = TraceLogger()

    # Shared state
    state = ProofState(
        theorem_statement=theorem,
        imports=imports,
        max_iterations=max_iterations,
        start_time=datetime.now(),
    )
    state.phase = ProofPhase.SEARCH

    # Plugins
    state_plugin = ProofStateManagerPlugin(state)
    search_plugin = LeanSearchPlugin()
    tactic_plugin = LeanTacticPlugin()
    verify_plugin = LeanVerificationPlugin(
        project_dir=project_dir, imports=imports, trace=trace,
    )
    submit_plugin = SubmitTacticPlugin(state, trace=trace)

    # Plugin dicts per agent (each agent sees relevant plugins)
    search_plugins = {"state": state_plugin, "search": search_plugin}
    tactic_plugins = {"state": state_plugin, "tactic": tactic_plugin, "submit": submit_plugin}
    verifier_plugins = {"state": state_plugin, "verification": verify_plugin}
    critic_plugins = {"state": state_plugin, "tactic": tactic_plugin}
    coordinator_plugins = {"state": state_plugin, "search": search_plugin}

    # Create agents
    agents = {
        "SearchAgent": SimpleAgent(
            "SearchAgent", SEARCH_AGENT_INSTRUCTIONS, search_plugins,
            provider=provider, trace=trace, thinking=True,
        ),
        "TacticAgent": SimpleAgent(
            "TacticAgent", TACTIC_AGENT_INSTRUCTIONS, tactic_plugins,
            provider=provider, trace=trace, thinking=True,
        ),
        "VerifierAgent": SimpleAgent(
            "VerifierAgent", VERIFIER_AGENT_INSTRUCTIONS, verifier_plugins,
            provider=provider, trace=trace, thinking=False,
        ),
        "CriticAgent": SimpleAgent(
            "CriticAgent", CRITIC_AGENT_INSTRUCTIONS, critic_plugins,
            provider=provider, trace=trace, thinking=False,
        ),
        "CoordinatorAgent": SimpleAgent(
            "CoordinatorAgent", COORDINATOR_AGENT_INSTRUCTIONS, coordinator_plugins,
            provider=provider, trace=trace, thinking=False,
        ),
    }

    orchestrator = ProofAgentGroupChat(agents, state, trace=trace)
    return orchestrator, state, trace


# ══════════════════════════════════════════════════════════════════════════════
# SINGLE-AGENT PROVER (baseline, uses submit_tactic function calling)
# ══════════════════════════════════════════════════════════════════════════════

class SingleAgentProver:
    """Single agent with function calling for baseline comparison."""

    def __init__(self, trace: TraceLogger, provider: str = "zai", thinking: bool = True):
        self.trace = trace
        self.provider = provider
        self.thinking = thinking
        self.config_label = f"single={provider}_{'thinkON' if thinking else 'thinkOFF'}"

    def prove(self, theorem: str, imports: Optional[str] = None,
              max_iterations: int = 4) -> dict:
        state = ProofState(
            theorem_statement=theorem,
            imports=imports,
            max_iterations=max_iterations,
            start_time=datetime.now(),
        )

        print(f"\n{'='*70}")
        print(f"SINGLE-AGENT: {theorem[:80]}...")
        print(f"Config: {self.config_label}")
        print(f"{'='*70}")

        # Create submit_tactic plugin for this session
        submit_plugin = SubmitTacticPlugin(state, trace=self.trace)

        # Build OpenAI tools from the plugin
        agent = SimpleAgent(
            "TacticAgent", TACTIC_AGENT_INSTRUCTIONS,
            {"submit": submit_plugin},
            provider=self.provider, trace=self.trace,
            thinking=self.thinking,
        )

        for attempt in range(1, max_iterations + 1):
            state.iteration = attempt
            print(f"\n--- Attempt {attempt}/{max_iterations} ---")

            if attempt == 1:
                user_msg = f"Prove this Lean 4 theorem:\n{theorem}"
                if imports:
                    user_msg += "\n\nAvailable imports: Mathlib (Finset, Real, BigOperators, Tactic)"
            else:
                user_msg = (
                    f"That tactic FAILED. Lean error:\n{state.last_error}\n\n"
                    f"Try a DIFFERENT tactic to prove:\n{theorem}"
                )

            response = agent.invoke(user_msg, state)

            # Extract submitted tactic from state (plugin records it)
            if state.tactic_history and not state.tactic_history[-1].success:
                tactic = state.tactic_history[-1].tactic
            elif state.tactic_history and state.tactic_history[-1].success:
                tactic = state.tactic_history[-1].tactic
            else:
                # Fallback: extract from response text
                tactic = response.strip()

            print(f"  Tactic: {tactic[:100]}")

            if "ERROR:" in tactic:
                state.last_error = tactic
                continue

            # Verify with Lean
            result = verify_with_lean(
                theorem=theorem, tactic=tactic, imports=imports,
                project_dir=LEAN_PROJECT_DIR, trace=self.trace,
            )

            if result["success"]:
                print(f"  PROOF VALID! ({result['time_s']:.1f}s Lean)")
                state.add_tactic_attempt(tactic, success=True,
                                         explanation=f"Verified in {result['time_s']:.1f}s")
                state.set_proof_complete(tactic)
                break
            else:
                raw_error = result["errors"][:500]
                error_type = result.get("error_type", "unknown")
                hints = []
                if error_type == "unsolved_goals":
                    hints.append(
                        "Your tactic executed but LEFT GOALS UNSOLVED. "
                        "Add more tactics (ring, omega, simp) after your rewrite."
                    )
                elif error_type == "tactic_failed":
                    if "rewrite" in raw_error.lower() and "did not find" in raw_error.lower():
                        hints.append(
                            "rw could not find the pattern. Try simp only [...] or conv."
                        )
                if "No goals to be solved" in raw_error:
                    hints.append("First tactic already closed the goal. Remove trailing tactics.")
                elif "made no progress" in raw_error:
                    hints.append("Tactic didn't change the goal. Try different approach.")
                elif "unknown tactic" in raw_error:
                    hints.append("Requires Mathlib import. Try omega, simp, or rw.")
                error = raw_error
                if hints:
                    error = raw_error + "\n" + "\n".join(hints)
                state.add_tactic_attempt(tactic, success=False, error=error)
                print(f"  FAILED [{error_type}]: {error[:200]}")

        total_s = (datetime.now() - state.start_time).total_seconds()
        if not state.is_done:
            state.phase = ProofPhase.FAILED

        return {
            "success": state.final_proof is not None,
            "proof": state.final_proof,
            "iterations": state.iteration,
            "attempts": len(state.tactic_history),
            "total_s": round(total_s, 1),
            "config": self.config_label,
        }

    def prove_sorry(self, demo: dict, max_iterations: int = 6) -> dict:
        """Prove a sorry replacement from a .lean file.

        Instead of proving a standalone theorem, this replaces a `sorry`
        in the actual proof context.
        """
        filepath = demo["file"]
        sorry_line = demo["line"]
        sorry_type = demo.get("sorry_type", "partial_proof")

        # Extract context
        ctx = extract_sorry_block(filepath, sorry_line)
        if "error" in ctx:
            return {"success": False, "proof": None, "error": ctx["error"]}

        state = ProofState(
            theorem_statement=demo.get("theorem", demo["name"]),
            imports=demo.get("imports"),
            max_iterations=max_iterations,
            start_time=datetime.now(),
        )

        print(f"\n{'='*70}")
        print(f"SORRY-REPLACEMENT: {demo['name']}")
        print(f"File: {filepath}:{sorry_line}")
        print(f"Config: {self.config_label}")
        print(f"{'='*70}")

        # Show context
        if ctx.get("context_before"):
            print(f"\n--- Context before sorry ---")
            for line in ctx["context_before"].split("\n"):
                if line.strip():
                    print(f"  {line}")

        # Extract actual goal state from Lean
        print(f"  Extracting goal state from Lean...")
        goal_state = get_goal_state(filepath, sorry_line)
        if goal_state:
            print(f"  GOAL: {goal_state[:200]}")
        else:
            print(f"  Could not extract goal state (using hints only)")

        # Build the user message with full context
        context_msg = (
            f"Replace the `sorry` in this Lean 4 proof.\n\n"
            f"THEOREM: {demo.get('theorem_name', demo['name'])}\n\n"
        )

        if demo.get("description"):
            context_msg += f"CONTEXT:\n{demo['description']}\n\n"

        if ctx.get("context_before"):
            context_msg += f"CODE BEFORE sorry:\n```lean\n{ctx['context_before']}\n```\n\n"

        if goal_state:
            context_msg += f"ACTUAL LEAN GOAL (the type Lean expects):\n```\n{goal_state}\n```\n\n"
        elif ctx.get("goal_hints"):
            context_msg += f"GOAL HINTS (from comments):\n{ctx['goal_hints']}\n\n"

        context_msg += "Provide the tactic(s) to replace `sorry`."

        submit_plugin = SubmitTacticPlugin(state, trace=self.trace)
        agent = SimpleAgent(
            "TacticAgent", TACTIC_AGENT_INSTRUCTIONS,
            {"submit": submit_plugin},
            provider=self.provider, trace=self.trace,
            thinking=self.thinking,
        )

        failed_tactics = []  # Track failed attempts to prevent repetition
        skip_count = 0  # Count skipped attempts (no-tactic + duplicates)
        consecutive_skips = 0  # Track consecutive skips for fallback logic

        attempt = 0
        while attempt < max_iterations:
            if skip_count >= max_iterations * 2:
                print(f"\n  Too many skipped attempts ({skip_count}), giving up.")
                break

            # Fallback: if too many consecutive skips, retry with thinking disabled
            if consecutive_skips >= 3 and self.thinking:
                print(f"\n  [FALLBACK] {consecutive_skips} consecutive reasoning-based skips, disabling thinking")
                agent = SimpleAgent(
                    "TacticAgent", TACTIC_AGENT_INSTRUCTIONS,
                    {"submit": submit_plugin},
                    provider=self.provider, trace=self.trace,
                    thinking=False,
                )
                consecutive_skips = 0  # Reset after creating new agent

            attempt += 1
            state.iteration = attempt
            print(f"\n--- Attempt {attempt}/{max_iterations} ---")

            if attempt == 1:
                user_msg = context_msg
            else:
                # Build retry message with goal state and failed tactics history
                failed_list = "\n".join(
                    f"  - `{t}` → {e[:100]}" for t, e in failed_tactics[-3:]
                )
                retry_msg = (
                    f"That tactic FAILED. Lean error:\n{state.last_error}\n\n"
                )
                if goal_state:
                    retry_msg += f"GOAL STATE:\n```\n{goal_state}\n```\n\n"
                retry_msg += (
                    f"FAILED ATTEMPTS (do NOT repeat these):\n{failed_list}\n\n"
                    f"Try a COMPLETELY DIFFERENT tactic. Context:\n"
                    f"CODE BEFORE sorry:\n```lean\n{ctx['context_before']}\n```\n"
                )
                user_msg = retry_msg

            # Track history before invocation to detect new submissions
            history_before = len(state.tactic_history)
            response = agent.invoke(user_msg, state, skip_state=True, max_tool_calls=1)

            # Extract submitted tactic — only use new submissions from this invocation
            tactic = None
            if len(state.tactic_history) > history_before:
                # Agent submitted a new tactic via tool call
                tactic = state.tactic_history[-1].tactic
            else:
                # Fallback: extract tactic from text response (reasoning extraction)
                lean_blocks = re.findall(r'```lean\n(.*?)```', response, re.DOTALL)
                if lean_blocks:
                    tactic = lean_blocks[0].strip()
                else:
                    # Last resort: strip agent prefix and brackets
                    tactic = re.sub(r'^\[.*?\]\s*', '', response).strip()
                    if not tactic or tactic == "(no response)":
                        tactic = None

            if tactic is None:
                # Agent didn't submit a tactic — don't count this as an attempt
                print(f"  Tactic: (none — skipping, not counted)")
                skip_count += 1
                consecutive_skips += 1
                attempt -= 1
                continue

            # Dedup: skip if identical to a previously failed tactic
            if any(tactic.strip() == ft.strip() for ft, _ in failed_tactics):
                print(f"  Tactic: (duplicate — skipping, not counted)")
                skip_count += 1
                consecutive_skips += 1
                attempt -= 1
                continue

            # Tactic is valid and new — reset consecutive skip counter
            consecutive_skips = 0

            print(f"  Tactic: {tactic[:120]}")

            # Verify by replacing sorry in the actual file
            print(f"  Verifying sorry replacement in {Path(filepath).name}...")
            result = verify_sorry_replacement(
                filepath=filepath, sorry_line=sorry_line,
                replacement=tactic, imports=demo.get("imports"),
            )

            if result["success"]:
                print(f"  PROOF VALID! ({result['time_s']:.1f}s Lean)")
                state.add_tactic_attempt(tactic, success=True,
                                         explanation=f"Verified in {result['time_s']:.1f}s")
                state.set_proof_complete(tactic)
                break
            else:
                raw_error = result["errors"][:500]
                error_type = result.get("error_type", "unknown")

                # Add contextual hints based on error type
                if error_type == "unsolved_goals":
                    residual = result.get("residual_goals", [])
                    if residual:
                        residual_str = "\n".join(f"  ⊢ {g}" for g in residual[:3])
                        hint = (
                            "Your tactic executed but LEFT THESE GOALS UNSOLVED:\n"
                            f"{residual_str}\n"
                            "Add more tactics after your rewrite to close these goals."
                        )
                    else:
                        hint = (
                            "Your tactic executed but did not close ALL goals. "
                            "The proof needs additional tactics after your rewrite. "
                            "Consider: `ring`, `omega`, `simp`, or `linarith`."
                        )
                    raw_error = hint + "\n" + raw_error
                elif error_type == "tactic_failed":
                    if "rewrite" in raw_error.lower() and "did not find" in raw_error.lower():
                        hint = (
                            "The `rw` tactic could not find the pattern in the goal. "
                            "The lemma may not match the current expression. "
                            "Try `simp only [...]` or `conv` to target the rewrite."
                        )
                        raw_error = hint + "\n" + raw_error

                state.add_tactic_attempt(tactic, success=False, error=raw_error)
                failed_tactics.append((tactic, raw_error[:200]))
                print(f"  FAILED [{error_type}]: {raw_error[:200]}")

        total_s = (datetime.now() - state.start_time).total_seconds()
        if not state.is_done:
            state.phase = ProofPhase.FAILED

        return {
            "success": state.final_proof is not None,
            "proof": state.final_proof,
            "iterations": state.iteration,
            "attempts": len(state.tactic_history),
            "total_s": round(total_s, 1),
            "config": self.config_label,
        }


# ══════════════════════════════════════════════════════════════════════════════
# MULTI-AGENT SORRY PROVER - Full 5-agent architecture with auto-verification
# ══════════════════════════════════════════════════════════════════════════════

class MultiAgentSorryProver:
    """Multi-agent sorry replacement using 5-agent architecture.

    Flow: Coordinator → Search → Tactic → [auto-verify] → Critic → (loop)
    Verification happens automatically between Tactic and Critic (no LLM needed).
    """

    def __init__(self, trace: TraceLogger, provider: str = "zai",
                 thinking: bool = True, local_provider: str = "local"):
        self.trace = trace
        self.provider = provider
        self.thinking = thinking
        self.local_provider = local_provider
        self.config_label = f"multi-sorry={provider}_{'thinkON' if thinking else 'thinkOFF'}"

    def prove_sorry(self, demo: dict, max_iterations: int = 10) -> dict:
        filepath = demo["file"]
        sorry_line = demo["line"]

        # 1. Extract sorry context
        ctx = extract_sorry_block(filepath, sorry_line)
        if "error" in ctx:
            return {"success": False, "proof": None, "error": ctx["error"]}

        # 2. Get goal state from Lean
        print(f"  Extracting goal state from Lean...")
        goal_state = get_goal_state(filepath, sorry_line)
        if goal_state:
            print(f"  GOAL: {goal_state[:200]}")
        else:
            print(f"  Could not extract goal (using hints)")

        # Count initial sorry
        initial_sorry_count = ctx["full_file"].count("sorry")

        # 3. Build SorryContext
        sorry_ctx = SorryContext(
            filepath=filepath,
            sorry_line=sorry_line,
            goal_state=goal_state,
            context_before=ctx.get("context_before", ""),
            context_after=ctx.get("context_after", ""),
            indentation=ctx.get("indentation", 0),
            indent_str=ctx.get("indent_str", ""),
            full_file=ctx.get("full_file", ""),
            sorry_count_before=initial_sorry_count,
        )

        # 4. Create shared state
        state = ProofState(
            theorem_statement=demo.get("theorem", demo["name"]),
            imports=demo.get("imports"),
            max_iterations=max_iterations,
            start_time=datetime.now(),
            sorry_context=sorry_ctx,
        )
        state.current_goal = goal_state or ""

        print(f"\n{'='*70}")
        print(f"MULTI-AGENT SORRY: {demo['name']}")
        print(f"File: {filepath}:{sorry_line}")
        print(f"Config: {self.config_label}")
        print(f"Goal: {goal_state[:150] if goal_state else '(unknown)'}")
        print(f"{'='*70}")

        if ctx.get("context_before"):
            print(f"\n--- Context before sorry ---")
            for line in ctx["context_before"].split("\n"):
                if line.strip():
                    print(f"  {line}")

        # 5. Create plugins
        state_plugin = ProofStateManagerPlugin(state)
        search_plugin = LeanSearchPlugin()
        tactic_plugin = LeanTacticPlugin()
        verify_plugin = LeanVerificationPlugin(
            project_dir=str(Path(filepath).parent.parent),
            imports=demo.get("imports"),
            trace=self.trace,
            sorry_context=sorry_ctx,
        )
        submit_plugin = SubmitTacticPlugin(state, trace=self.trace)

        # 6. Create agents with restricted plugin access
        search_plugins = {"state": state_plugin, "search": search_plugin}
        tactic_plugins = {"state": state_plugin, "tactic": tactic_plugin, "submit": submit_plugin}
        critic_plugins = {"state": state_plugin, "tactic": tactic_plugin}
        coordinator_plugins = {"state": state_plugin, "search": search_plugin}

        agents = {
            "SearchAgent": SimpleAgent(
                "SearchAgent", SEARCH_AGENT_INSTRUCTIONS, search_plugins,
                provider=self.local_provider, trace=self.trace, thinking=False,
            ),
            "TacticAgent": SimpleAgent(
                "TacticAgent", TACTIC_AGENT_INSTRUCTIONS, tactic_plugins,
                provider=self.provider, trace=self.trace, thinking=self.thinking,
            ),
            "CriticAgent": SimpleAgent(
                "CriticAgent", CRITIC_AGENT_INSTRUCTIONS, critic_plugins,
                provider=self.provider, trace=self.trace, thinking=False,
            ),
            "CoordinatorAgent": SimpleAgent(
                "CoordinatorAgent", COORDINATOR_AGENT_INSTRUCTIONS, coordinator_plugins,
                provider=self.provider, trace=self.trace, thinking=False,
            ),
        }

        # 7. Build context message for agents
        context_msg = (
            f"Replace the `sorry` in this Lean 4 proof.\n\n"
            f"THEOREM: {demo.get('theorem_name', demo['name'])}\n\n"
        )
        if demo.get("description"):
            context_msg += f"CONTEXT:\n{demo['description']}\n\n"
        if ctx.get("context_before"):
            context_msg += f"CODE BEFORE sorry:\n```lean\n{ctx['context_before']}\n```\n\n"
        if goal_state:
            context_msg += f"ACTUAL LEAN GOAL:\n```\n{goal_state}\n```\n\n"
        elif ctx.get("goal_hints"):
            context_msg += f"GOAL HINTS:\n{ctx['goal_hints']}\n\n"
        context_msg += "Provide the tactic(s) to replace `sorry`."

        # 8. Multi-agent loop with auto-verification
        failed_tactics = []
        sorry_count = initial_sorry_count
        session_start = time.time()
        phase_sequence = ["search", "generate", "verify", "analyze"]
        phase_idx = 0
        consecutive_failures = 0

        # Start with search phase
        current_agent_name = "SearchAgent"
        current_message = context_msg

        for iteration in range(1, max_iterations + 1):
            state.iteration = iteration
            iter_start = time.time()
            elapsed = time.time() - session_start

            print(f"\n--- Iteration {iteration}/{max_iterations} | {current_agent_name} [+{elapsed:.1f}s] ---")

            # === SEARCH PHASE ===
            if current_agent_name == "SearchAgent":
                agent = agents["SearchAgent"]
                response = agent.invoke(current_message, state)

                # Check if search found lemmas
                lemmas_found = len(state.discovered_lemmas)
                print(f"  Lemmas found: {lemmas_found}")

                # Always move to TacticAgent after search
                current_agent_name = "TacticAgent"
                current_message = context_msg + (
                    f"\n\nLEMmas found ({lemmas_found}): "
                    + "\n".join(state.discovered_lemmas[-5:])
                    if state.discovered_lemmas else context_msg
                )
                continue

            # === TACTIC PHASE ===
            if current_agent_name == "TacticAgent":
                agent = agents["TacticAgent"]

                # Build retry message if we have failures
                if failed_tactics:
                    failed_list = "\n".join(
                        f"  - `{t}` → {e[:100]}" for t, e in failed_tactics[-3:]
                    )
                    retry_msg = current_message + (
                        f"\n\nFAILED ATTEMPTS (do NOT repeat these):\n{failed_list}\n\n"
                        f"Error classification: {state.last_error[:200] if state.last_error else 'none'}\n"
                    )
                    if state.strategy_mode == "decompose":
                        retry_msg += "\nSTRATEGY: Use submit_decomposition() to split the goal into sub-goals.\n"
                else:
                    retry_msg = current_message

                # Track history before invocation
                history_before = len(state.tactic_history)
                response = agent.invoke(retry_msg, state, skip_state=True, max_tool_calls=5)

                # Extract submitted tactic
                tactic = None
                is_decomposition = False

                if len(state.tactic_history) > history_before:
                    tactic = state.tactic_history[-1].tactic

                if tactic is None:
                    # Try extraction from response
                    lean_blocks = re.findall(r'```lean\n(.*?)```', response, re.DOTALL)
                    if lean_blocks:
                        tactic = lean_blocks[0].strip()
                    else:
                        clean = re.sub(r'^\[.*?\]\s*', '', response).strip()
                        # Check if decomposition was submitted via tool call
                        decomp_from_tools = None
                        for tr in agent.last_tool_results:
                            if tr["name"] == "submit_decomposition":
                                try:
                                    data = json.loads(tr["result"])
                                    decomp_from_tools = data.get("decomposition", "")
                                except (json.JSONDecodeError, TypeError):
                                    pass
                                break

                        if decomp_from_tools:
                            is_decomposition = True
                            tactic = decomp_from_tools
                        elif "submit_decomposition" in clean:
                            is_decomposition = True
                            decomp_match = re.search(r'"decomposition":\s*"(.*?)"', clean, re.DOTALL)
                            if decomp_match:
                                tactic = decomp_match.group(1).replace("\\n", "\n")
                            else:
                                print(f"  Tactic: (decomposition submitted but lost)")
                                consecutive_failures += 1
                                continue
                        elif "Max tool calls" in clean:
                            print(f"  Tactic: (max tool calls reached — skipping)")
                            consecutive_failures += 1
                            continue
                        elif clean and clean != "(no response)":
                            tactic = clean

                if tactic is None:
                    print(f"  Tactic: (none — retrying)")
                    consecutive_failures += 1
                    if consecutive_failures >= 3:
                        current_agent_name = "CoordinatorAgent"
                        current_message = (
                            f"No tactics generated after {consecutive_failures} attempts. "
                            f"Goal: {goal_state}\nErrors: {state.last_error}"
                        )
                    continue

                # Dedup check
                tactic_stripped = tactic.strip()
                if any(tactic_stripped == ft.strip() for ft, _ in failed_tactics):
                    print(f"  Tactic: (duplicate — skipping)")
                    continue

                # Check if decomposition (have statement introduces sub-goals)
                if re.search(r"\bhave\s+\w+\s*:", tactic):
                    is_decomposition = True
                    print(f"  DECOMPOSITION detected (have statement)")

                print(f"  Tactic: {tactic[:120]}")
                consecutive_failures = 0

                # === AUTO-VERIFICATION PHASE ===
                print(f"  Verifying...")
                verify_result = verify_sorry_replacement(
                    filepath=filepath,
                    sorry_line=sorry_line,
                    replacement=tactic,
                    imports=demo.get("imports"),
                )

                # Check sorry count for decomposition detection
                new_sorry_count = verify_plugin._count_sorry_after_replacement(tactic)

                if verify_result["success"]:
                    # PROOF COMPLETE!
                    print(f"  PROOF VALID! ({verify_result['time_s']:.1f}s Lean)")
                    state.add_tactic_attempt(tactic, success=True)
                    state.set_proof_complete(tactic)
                    self._log_iteration(iteration, "TacticAgent", tactic, True, None,
                                        time.time() - iter_start)
                    break

                elif is_decomposition and new_sorry_count > sorry_count:
                    # Decomposition succeeded! More sorry = we split the goal
                    print(f"  DECOMPOSITION SUCCESS! sorry: {sorry_count} → {new_sorry_count}")
                    state.add_tactic_attempt(tactic, success=False,
                                             error=f"Decomposition: {sorry_count} → {new_sorry_count} sorry")
                    sorry_count = new_sorry_count
                    state.strategy_mode = "decompose"
                    # Continue trying to close the new sorry
                    failed_tactics.append((tactic, "decomposition (progress)"))
                    current_agent_name = "TacticAgent"
                    current_message = context_msg + (
                        f"\n\nDecomposition reussie! sorry count: {sorry_count}. "
                        f"Cible maintenant le sous-sorry le plus simple."
                    )
                    self._log_iteration(iteration, "TacticAgent", tactic, False,
                                        "decomposition_progress", time.time() - iter_start)
                    continue

                else:
                    # Failed — classify error and route to CriticAgent
                    raw_error = verify_result.get("errors", "")[:500]
                    error_type = verify_result.get("error_type", "unknown")
                    residual_goals = verify_result.get("residual_goals", [])

                    # Add contextual hints
                    if error_type == "unsolved_goals" and residual_goals:
                        goals_str = "\n".join(f"  ⊢ {g}" for g in residual_goals[:3])
                        hint = f"Unsolved goals:\n{goals_str}"
                        raw_error = hint + "\n" + raw_error

                    state.add_tactic_attempt(tactic, success=False, error=raw_error)
                    failed_tactics.append((tactic, raw_error[:200]))
                    print(f"  FAILED [{error_type}]: {raw_error[:200]}")

                    self._log_iteration(iteration, "TacticAgent", tactic, False,
                                        raw_error[:200], time.time() - iter_start)

                    # Route to CriticAgent for error analysis
                    current_agent_name = "CriticAgent"
                    current_message = (
                        f"Tactic FAILED:\n```lean\n{tactic}\n```\n\n"
                        f"Error type: {error_type}\n"
                        f"Error: {raw_error[:300]}\n\n"
                        f"Goal: {goal_state}\n"
                        f"Failed tactics count: {len(failed_tactics)}\n"
                        f"Classify the error and decide the next agent."
                    )
                    continue

            # === CRITIC PHASE ===
            if current_agent_name == "CriticAgent":
                agent = agents["CriticAgent"]
                response = agent.invoke(current_message, state, skip_state=True, max_tool_calls=3)

                # Parse critic's decision
                critic_text = response.lower()

                if "decompos" in critic_text or "split" in critic_text or "have" in critic_text:
                    state.strategy_mode = "decompose"
                    current_agent_name = "TacticAgent"
                    current_message = context_msg + (
                        f"\n\nCRITIC DECISION: Switch to DECOMPOSITION mode. "
                        f"Use submit_decomposition() to split the goal.\n"
                        f"Failed: {len(failed_tactics)} attempts\n"
                        f"Last error: {state.last_error[:200] if state.last_error else 'none'}"
                    )
                elif "search" in critic_text or "lemma" in critic_text:
                    current_agent_name = "SearchAgent"
                    current_message = (
                        f"Search for lemmas relevant to this goal:\n{goal_state}\n\n"
                        f"Error encountered: {state.last_error[:200] if state.last_error else 'unknown'}"
                    )
                elif "coordinat" in critic_text or "strateg" in critic_text:
                    current_agent_name = "CoordinatorAgent"
                    current_message = (
                        f"CriticAgent escalates after {len(failed_tactics)} failures.\n"
                        f"Goal: {goal_state}\n"
                        f"Last errors: {[e[:100] for _, e in failed_tactics[-3:]]}"
                    )
                else:
                    # Default: retry with TacticAgent
                    current_agent_name = "TacticAgent"
                    current_message = context_msg + (
                        f"\n\nPrevious tactic failed. Try a DIFFERENT approach.\n"
                        f"Error: {state.last_error[:200] if state.last_error else 'unknown'}"
                    )
                continue

            # === COORDINATOR PHASE ===
            if current_agent_name == "CoordinatorAgent":
                agent = agents["CoordinatorAgent"]
                response = agent.invoke(current_message, state, skip_state=True, max_tool_calls=2)

                coord_text = response.lower()

                if "decompos" in coord_text:
                    state.strategy_mode = "decompose"
                    current_agent_name = "TacticAgent"
                    current_message = context_msg + (
                        f"\n\nCOORDINATOR: Switch to DECOMPOSITION mode.\n"
                        f"Decompose the goal into sub-goals using 'have'."
                    )
                elif "search" in coord_text:
                    current_agent_name = "SearchAgent"
                    current_message = f"Search for lemmas for goal:\n{goal_state}"
                elif "give up" in coord_text or "abort" in coord_text:
                    print(f"  Coordinator: GIVING UP")
                    state.phase = ProofPhase.FAILED
                    break
                else:
                    # Try one more time with TacticAgent
                    current_agent_name = "TacticAgent"
                    current_message = context_msg + (
                        f"\n\nCOORDINATOR: Try a completely new approach.\n"
                        f"Failed: {len(failed_tactics)} attempts"
                    )
                continue

        total_s = (datetime.now() - state.start_time).total_seconds()
        if not state.is_done:
            state.phase = ProofPhase.FAILED

        print(f"\n{'='*60}")
        print(f"RESULT: {'SUCCESS' if state.proof_complete else 'FAILED'}")
        if state.final_proof:
            print(f"  Proof: {state.final_proof[:200]}")
        print(f"  Iterations: {state.iteration}, Time: {total_s:.1f}s")
        print(f"  Sorry count: {initial_sorry_count} → {sorry_count}")
        print(f"  Tactics tried: {len(state.tactic_history)}")
        print(f"  Decompositions: {sum(1 for a in state.tactic_history if 'Decomposition' in (a.error or ''))}")
        print(f"{'='*60}")

        return {
            "success": state.final_proof is not None,
            "proof": state.final_proof,
            "iterations": state.iteration,
            "attempts": len(state.tactic_history),
            "total_s": round(total_s, 1),
            "config": self.config_label,
            "sorry_evolution": f"{initial_sorry_count} → {sorry_count}",
        }

    def _log_iteration(self, iteration: int, agent: str, tactic: str,
                       success: bool, error: Optional[str], duration: float):
        self.trace.log(
            agent=agent, role="iteration",
            content=f"iter={iteration}, tactic={tactic[:100]}, success={success}",
            duration_s=duration, tool_name="verify_sorry" if not success else "proof_found",
            tool_result=error[:200] if error else "SUCCESS",
        )


# ══════════════════════════════════════════════════════════════════════════════
# AUTONOMOUS PROVER — Minimal orchestrator: agent proposes edit → compile → feed
# ══════════════════════════════════════════════════════════════════════════════

class LeanFilePlugin:
    """Plugin giving agents direct read/write access to the .lean file."""

    _global_locks: Dict[str, str] = {}  # filepath → session_id

    def __init__(self, filepath: str, session_id: str = ""):
        self._filepath = filepath
        self._session_id = session_id or str(uuid.uuid4())[:8]
        self._best_content: Optional[str] = None
        self._best_sorry_count: int = 999
        self._lock_file = Path(filepath).with_suffix(".prover.lock")

    def _acquire_lock(self) -> bool:
        """Acquire file lock. Returns False if another session holds it."""
        if self._lock_file.exists():
            existing = self._lock_file.read_text().strip()
            if existing and existing != self._session_id:
                return False
        self._lock_file.write_text(self._session_id, encoding="utf-8")
        LeanFilePlugin._global_locks[self._filepath] = self._session_id
        return True

    def _release_lock(self):
        """Release file lock."""
        if self._lock_file.exists():
            content = self._lock_file.read_text().strip()
            if content == self._session_id:
                self._lock_file.unlink(missing_ok=True)
        LeanFilePlugin._global_locks.pop(self._filepath, None)

    def _check_lock(self) -> Optional[str]:
        """Check if another session holds the lock. Returns session_id or None."""
        if self._lock_file.exists():
            existing = self._lock_file.read_text().strip()
            if existing and existing != self._session_id:
                return existing
        return None

    @kernel_function(
        description="Read the current content of the .lean file being edited",
        name="read_file",
    )
    def read_file(self) -> str:
        content = Path(self._filepath).read_text(encoding="utf-8")
        sorry_count = content.count("sorry")
        return json.dumps({
            "filepath": str(self._filepath),
            "content": content,
            "sorry_count": sorry_count,
            "total_lines": len(content.split("\n")),
        }, ensure_ascii=False)

    @kernel_function(
        description="Read a specific range of lines from the .lean file (1-based inclusive)",
        name="read_lines",
    )
    def read_lines(self, start: int, end: int) -> str:
        content = Path(self._filepath).read_text(encoding="utf-8")
        lines = content.split("\n")
        start = max(1, start)
        end = min(len(lines), end)
        selected = lines[start - 1:end]
        return "\n".join(f"{start + i}: {line}" for i, line in enumerate(selected))

    @kernel_function(
        description="Replace a range of lines in the .lean file. Lines are 1-based, inclusive. Returns the new sorry count.",
        name="replace_lines",
    )
    def replace_lines(self, start: int, end: int, new_content: str) -> str:
        lock_holder = self._check_lock()
        if lock_holder:
            return json.dumps({"error": f"File locked by session {lock_holder}. Wait or use restore_best()."})

        if not self._acquire_lock():
            return json.dumps({"error": "Could not acquire file lock"})

        try:
            content = Path(self._filepath).read_text(encoding="utf-8")
            lines = content.split("\n")
            old_lines = lines[start - 1:end] if end <= len(lines) else lines[start - 1:]
            old_text = "\n".join(old_lines)

            new_lines = new_content.split("\n")
            lines[start - 1:end if end <= len(lines) else len(lines)] = new_lines
            new_file_content = "\n".join(lines)

            Path(self._filepath).write_text(new_file_content, encoding="utf-8")
            sorry_count = new_file_content.count("sorry")

            # Track best state
            if sorry_count < self._best_sorry_count:
                self._best_sorry_count = sorry_count
                self._best_content = new_file_content

            return json.dumps({
                "replaced_lines": f"{start}-{end}",
                "old_text_preview": old_text[:200],
                "new_sorry_count": sorry_count,
                "best_sorry_count": self._best_sorry_count,
            }, ensure_ascii=False)
        finally:
            self._release_lock()

    @kernel_function(
        description="Replace the sorry at a given line number with new tactic text. Auto-detects indentation.",
        name="replace_sorry",
    )
    def replace_sorry(self, sorry_line: int, replacement: str) -> str:
        lock_holder = self._check_lock()
        if lock_holder:
            return json.dumps({"error": f"File locked by session {lock_holder}."})
        if not self._acquire_lock():
            return json.dumps({"error": "Could not acquire file lock"})
        try:
            content = Path(self._filepath).read_text(encoding="utf-8")
            lines = content.split("\n")

            if sorry_line < 1 or sorry_line > len(lines):
                return json.dumps({"error": f"Line {sorry_line} out of range"})

            sorry_text = lines[sorry_line - 1]
            if "sorry" not in sorry_text:
                return json.dumps({"error": f"Line {sorry_line} doesn't contain 'sorry': {sorry_text[:80]}"})

            indent = len(sorry_text) - len(sorry_text.lstrip())
            indent_str = " " * indent

            replacement_lines = []
            for line in replacement.strip().split("\n"):
                if line.strip():
                    replacement_lines.append(indent_str + line.strip())

            old_line = lines[sorry_line - 1]
            lines[sorry_line - 1:sorry_line] = replacement_lines
            new_content = "\n".join(lines)

            Path(self._filepath).write_text(new_content, encoding="utf-8")
            sorry_count = new_content.count("sorry")

            if sorry_count < self._best_sorry_count:
                self._best_sorry_count = sorry_count
                self._best_content = new_content

            return json.dumps({
                "replaced": old_line.strip(),
                "new_lines": len(replacement_lines),
                "new_sorry_count": sorry_count,
                "best_sorry_count": self._best_sorry_count,
            }, ensure_ascii=False)
        finally:
            self._release_lock()

    @kernel_function(
        description="Write the complete .lean file content. Use for major rewrites.",
        name="write_file",
    )
    def write_file(self, content: str) -> str:
        lock_holder = self._check_lock()
        if lock_holder:
            return json.dumps({"error": f"File locked by session {lock_holder}."})
        if not self._acquire_lock():
            return json.dumps({"error": "Could not acquire file lock"})
        try:
            Path(self._filepath).write_text(content, encoding="utf-8")
            sorry_count = content.count("sorry")

            if sorry_count < self._best_sorry_count:
                self._best_sorry_count = sorry_count
                self._best_content = content

            return json.dumps({
                "written": True,
                "sorry_count": sorry_count,
                "best_sorry_count": self._best_sorry_count,
                "total_lines": len(content.split("\n")),
            }, ensure_ascii=False)
        finally:
            self._release_lock()

    @kernel_function(
        description="Find all sorry lines in the file with their line numbers and surrounding context",
        name="find_sorry_lines",
    )
    def find_sorry_lines(self, context_chars: int = 80) -> str:
        content = Path(self._filepath).read_text(encoding="utf-8")
        lines = content.split("\n")
        sorry_lines = []
        for i, line in enumerate(lines):
            if "sorry" in line:
                start_ctx = max(0, i - 2)
                end_ctx = min(len(lines), i + 3)
                ctx = "\n".join(
                    f"  {start_ctx + j + 1}: {lines[start_ctx + j]}"
                    for j in range(end_ctx - start_ctx)
                )
                sorry_lines.append({
                    "line": i + 1,
                    "content": line.strip(),
                    "context": ctx,
                })
        return json.dumps({
            "sorry_count": len(sorry_lines),
            "sorry_lines": sorry_lines,
        }, ensure_ascii=False)

    @kernel_function(
        description="Find all build errors (not sorry) in the file. Returns line numbers, error messages, and context. Call this FIRST if the build fails — fix build errors before sorry.",
        name="find_errors",
    )
    def find_errors(self, context_chars: int = 200) -> str:
        verifier = get_verifier(self._project_dir)
        subdir = Path(self._filepath).parent.name
        filename = Path(self._filepath).name
        relative_path = f"{subdir}/{filename}"
        result = verifier.verify_project_file(relative_path)

        raw_output = result.get("raw_output", "")
        content = Path(self._filepath).read_text(encoding="utf-8")
        lines = content.split("\n")

        build_errors = []
        for m in re.finditer(r".*?(\d+):\d+: error: (.*)", raw_output):
            line_num = int(m.group(1))
            msg = m.group(2)
            if "sorry" in msg.lower():
                continue
            start_ctx = max(0, line_num - 4)
            end_ctx = min(len(lines), line_num + 3)
            ctx = "\n".join(
                f"  {start_ctx + j + 1}: {lines[start_ctx + j]}"
                for j in range(end_ctx - start_ctx)
            )
            build_errors.append({
                "line": line_num,
                "message": msg,
                "context": ctx,
            })

        return json.dumps({
            "error_count": len(build_errors),
            "build_errors": build_errors[:10],
            "sorry_count": content.count("sorry"),
        }, ensure_ascii=False)

    @kernel_function(
        description="Restore the best state seen so far (lowest sorry count). Returns True if restored.",
        name="restore_best",
    )
    def restore_best(self) -> str:
        if self._best_content:
            Path(self._filepath).write_text(self._best_content, encoding="utf-8")
            return json.dumps({
                "restored": True,
                "sorry_count": self._best_sorry_count,
            }, ensure_ascii=False)
        return json.dumps({"restored": False, "reason": "no best state recorded"})

    @property
    def best_sorry_count(self) -> int:
        return self._best_sorry_count

    @property
    def best_content(self) -> Optional[str]:
        return self._best_content


class CompilePlugin:
    """Plugin that compiles the .lean file and returns structured results."""

    def __init__(self, filepath: str, trace: Optional[TraceLogger] = None):
        self._filepath = filepath
        self._project_dir = str(Path(filepath).parent.parent)
        self._trace = trace
        self._compile_count = 0
        self._total_compile_s = 0.0

    @kernel_function(
        description="Compile the current .lean file and return errors, sorry count, and compilation time. This is the MAIN feedback mechanism.",
        name="compile",
    )
    def compile(self) -> str:
        self._compile_count += 1
        start = time.time()

        verifier = get_verifier(self._project_dir)
        subdir = Path(self._filepath).parent.name
        filename = Path(self._filepath).name
        relative_path = f"{subdir}/{filename}"
        result = verifier.verify_project_file(relative_path)

        duration = time.time() - start
        self._total_compile_s += duration

        raw_output = result.get("raw_output", "")
        success = result.get("success", False)

        # Parse errors
        errors = []
        for line in raw_output.split("\n"):
            m = re.match(r".*?(\d+):\d+: error: (.*)", line)
            if m:
                errors.append({"line": int(m.group(1)), "message": m.group(2)})

        # Parse warnings
        warnings = []
        for line in raw_output.split("\n"):
            m = re.match(r".*?(\d+):\d+: warning: (.*)", line)
            if m:
                warnings.append({"line": int(m.group(1)), "message": m.group(2)})

        # Count sorry in current file
        content = Path(self._filepath).read_text(encoding="utf-8")
        sorry_count = content.count("sorry")

        if self._trace:
            self._trace.log(
                agent="CompilePlugin", role="compile",
                content=f"compile #{self._compile_count}: success={success}, "
                        f"{len(errors)} errors, {sorry_count} sorry, {duration:.1f}s",
                duration_s=duration,
                tool_name="compile",
                tool_result=raw_output[:500],
            )

        return json.dumps({
            "success": success,
            "sorry_count": sorry_count,
            "error_count": len(errors),
            "errors": errors[:10],
            "warnings": warnings[:5],
            "compile_time_s": round(duration, 1),
            "compile_number": self._compile_count,
            "raw_output_preview": raw_output[:500],
        }, ensure_ascii=False)

    @kernel_function(
        description="Extract the Lean goal state at a specific sorry line by probing with 'exact ()'. Returns the goal text.",
        name="probe_goal",
    )
    def probe_goal(self, sorry_line: int) -> str:
        goal = get_goal_state(self._filepath, sorry_line)
        if goal:
            return json.dumps({"goal": goal, "line": sorry_line})
        return json.dumps({"goal": None, "line": sorry_line, "hint": "Could not extract goal (timeout or syntax error)"})

    @property
    def compile_count(self) -> int:
        return self._compile_count

    @property
    def total_compile_s(self) -> float:
        return self._total_compile_s


# --- Unified agent instructions for the autonomous prover ---

AUTONOMOUS_PROVER_INSTRUCTIONS = """Tu es un prouveur Lean 4. Tu édites directement le fichier .lean.

FLUX OBLIGATOIRE (max 3 appels d'outils par itération):
1. find_sorry_lines() — localise les sorry
2. read_lines(sorry_line-10, sorry_line+5) — lis le contexte LOCAL seulement
3. probe_goal(sorry_line) — extrais le but Lean
4. replace_sorry(sorry_line, tactique) — PROPOSE IMMÉDIATEMENT
5. compile() — vérifie

SI BUILD ERREURS (non-sorry):
1. find_errors() — liste les erreurs
2. read_lines autour de l'erreur
3. replace_lines pour corriger
4. compile() — vérifie

INTERDIT:
- read_file() — trop long, gaspille des tokens. Utilise read_lines(start, end)
- Plus de 2 lectures sans édition = gaspillage d'itération
- Répéter une tactique qui vient d'échouer

TACTIQUES UTILES:
- Arithmétique: omega, ring, linarith, norm_cast; omega
- Simplification: simp, simp [LemmaName], simp only [lemme]
- Réécriture: rw [lemme], rw [← lemmem], rw [show ... from ...]
- Casting: norm_cast, push_cast, Nat.cast_sub, Nat.cast_add
- Décomposition: have h : sub_goal := by sorry (crée un nouveau sorry = progrès)
- Contrôle: exact, apply, constructor, split_ifs, by_cases

FIX PATTERNS:
- "rewrite failed" → le pattern n'existe pas dans le but. Relire le but avec probe_goal
- "unknown identifier" → chercher le bon nom avec read_lines dans les imports/définitions
- "type mismatch" → essayer norm_cast, push_cast, change
- "omega failed" → essayer norm_cast; omega ou linarith

RÈGLES:
- BUILD ERRORS AVANT SORRY — un fichier cassé bloque tout
- 3 échecs consécutifs → change d'approche radicalement
- sorry qui diminue = progrès valide
- Propose VITE, même si incertain. L'essai coûte moins cher que la réflexion.
"""


class AutonomousProver:
    """Minimal orchestrator: single agent with full file editing powers.

    The agent has complete freedom to edit the .lean file. The orchestrator
    only: (1) lets the agent call tools, (2) auto-compiles after each edit,
    (3) feeds compilation results back, (4) tracks best state, (5) stops
    when done or budget exhausted.
    """

    def __init__(self, trace: TraceLogger, provider: str = "zai",
                 thinking: bool = True):
        self.trace = trace
        self.provider = provider
        self.thinking = thinking
        self.config_label = f"auto-{provider}_{'thinkON' if thinking else 'thinkOFF'}"

    def prove_sorry(self, demo: dict, max_iterations: int = 10,
                    strategic_hints: str = "") -> dict:
        filepath = demo["file"]
        sorry_line = demo["line"]

        # Read original content for backup
        original_content = Path(filepath).read_text(encoding="utf-8")
        original_sorry_count = original_content.count("sorry")

        # Auto-detect actual sorry line if the configured one is stale
        actual_sorry_lines = [
            i + 1 for i, line in enumerate(original_content.split("\n"))
            if "sorry" in line
        ]
        if actual_sorry_lines and sorry_line not in actual_sorry_lines:
            sorry_line = actual_sorry_lines[0]
            print(f"  [AutoFix] Configured line {demo['line']} has no sorry. Using actual sorry at line {sorry_line}")

        print(f"\n{'='*70}")
        print(f"AUTONOMOUS PROVER: {demo['name']}")
        print(f"File: {filepath}:{sorry_line}")
        print(f"Config: {self.config_label}")
        print(f"Original sorry count: {original_sorry_count}")
        if strategic_hints:
            print(f"Strategic hints: {strategic_hints[:200]}")
        print(f"{'='*70}")

        # Create plugins
        file_plugin = LeanFilePlugin(filepath, session_id=self.config_label)
        compile_plugin = CompilePlugin(filepath, trace=self.trace)
        state = ProofState(
            theorem_statement=demo.get("theorem", demo["name"]),
            imports=demo.get("imports"),
            max_iterations=max_iterations,
            start_time=datetime.now(),
        )
        state_plugin = ProofStateManagerPlugin(state)
        search_plugin = LeanSearchPlugin()
        tactic_plugin = LeanTacticPlugin()

        # Single agent with ALL plugins — full freedom
        all_plugins = {
            "file": file_plugin,
            "compile": compile_plugin,
            "state": state_plugin,
            "search": search_plugin,
            "tactic": tactic_plugin,
        }

        agent = SimpleAgent(
            "AutonomousProver",
            AUTONOMOUS_PROVER_INSTRUCTIONS,
            all_plugins,
            provider=self.provider,
            trace=self.trace,
            thinking=self.thinking,
        )

        # Build initial context
        goal_state = get_goal_state(filepath, sorry_line)
        context_msg = (
            f"Prouve le sorry à la ligne {sorry_line} du fichier {Path(filepath).name}.\n\n"
        )
        if demo.get("description"):
            context_msg += f"DESCRIPTION:\n{demo['description']}\n\n"
        if goal_state:
            context_msg += f"BUT LEAN (ligne {sorry_line}):\n```\n{goal_state}\n```\n\n"

        # Auto-discover proven helpers in the file (theorems with complete proofs)
        try:
            file_text = Path(filepath).read_text(encoding="utf-8")
            proven_helpers = re.findall(
                r'^(?:theorem|lemma|def)\s+(\w+)',
                file_text, re.MULTILINE
            )
            sorry_lines_in_file = [i+1 for i, l in enumerate(file_text.split("\n")) if "sorry" in l]
            # Only list helpers that are NOT on sorry lines (i.e., fully proven)
            clean_helpers = []
            for h in proven_helpers[:30]:
                pattern = re.compile(rf'(?:theorem|lemma|def)\s+{re.escape(h)}\b', re.MULTILINE)
                match = pattern.search(file_text)
                if match:
                    start_line = file_text[:match.start()].count("\n") + 1
                    if start_line not in sorry_lines_in_file:
                        clean_helpers.append(h)
            if clean_helpers:
                context_msg += f"HELPERS PROUVES dans le fichier: {', '.join(clean_helpers[:20])}\n\n"
        except Exception:
            pass

        if strategic_hints:
            context_msg += f"CONSEILS STRATÉGIQUES:\n{strategic_hints}\n\n"
        context_msg += (
            f"SORRY COUNT INITIAL: {original_sorry_count}\n"
            f"OBJECTIF: réduire le sorry count ou prouver complètement.\n"
            f"Commence par find_sorry_lines() puis read_lines() autour du sorry, puis propose une tactique."
        )

        # Main loop
        session_start = time.time()
        consecutive_no_edit = 0
        compile_data = {}

        for iteration in range(1, max_iterations + 1):
            state.iteration = iteration
            iter_start = time.time()
            elapsed = time.time() - session_start

            print(f"\n--- Iteration {iteration}/{max_iterations} [+{elapsed:.1f}s] ---")

            # Let agent think and act
            response = agent.invoke(context_msg, state, skip_state=True, max_tool_calls=10)

            # Check if agent made a file edit
            edited = any(
                tr["name"] in ("replace_lines", "replace_sorry", "write_file")
                for tr in agent.last_tool_results
            )
            compiled = any(
                tr["name"] == "compile"
                for tr in agent.last_tool_results
            )
            # Capture compile results from agent's own compile call
            if compiled:
                for tr in agent.last_tool_results:
                    if tr["name"] == "compile":
                        try:
                            compile_data = json.loads(tr["result"])
                        except (json.JSONDecodeError, TypeError):
                            compile_data = {}
                        break

            if edited:
                consecutive_no_edit = 0
            else:
                consecutive_no_edit += 1

            # Auto-compile if edited but not yet compiled
            current_sorry_count = Path(filepath).read_text(encoding="utf-8").count("sorry")
            if edited and not compiled:
                print(f"  Auto-compiling after edit...")
                compile_result_str = compile_plugin.compile()
                try:
                    compile_data = json.loads(compile_result_str)
                except json.JSONDecodeError:
                    compile_data = {}
                compiled = True
                current_sorry_count = compile_data.get("sorry_count", current_sorry_count)

            # Log iteration
            self.trace.log(
                agent="AutonomousProver", role="iteration",
                content=f"iter={iteration}, edited={edited}, sorry={current_sorry_count}",
                duration_s=time.time() - iter_start,
            )

            # Check termination conditions
            if current_sorry_count == 0 and compiled:
                # Check if actually compiles clean
                if compile_data.get("success"):
                    print(f"  ALL SORRY ELIMINATED! Proof complete!")
                    state.set_proof_complete("full_file_proof")
                    break

            if current_sorry_count < original_sorry_count:
                print(f"  PROGRESS: sorry {original_sorry_count} → {current_sorry_count}")

            if consecutive_no_edit >= 3:
                print(f"  No edits for 3 iterations — feeding compilation feedback")
                context_msg = (
                    f"Tu n'as pas fait d'edition depuis 3 iterations. "
                    f"Sorry count: {current_sorry_count} (objectif: < {original_sorry_count})\n"
                    f"Utilise find_sorry_lines() pour voir l'etat, "
                    f"puis propose IMMEDIATEMENT une modification avec replace_sorry() ou replace_lines()."
                )
                consecutive_no_edit = 0
                continue

            # Build feedback for next iteration
            feedback_parts = []
            if edited:
                feedback_parts.append(f"Modification appliquee. Sorry count: {current_sorry_count}")
            if compiled:
                if compile_data.get("success"):
                    feedback_parts.append("COMPILATION: SUCCES (pas d'erreurs)")
                else:
                    errors = compile_data.get("errors", [])
                    if errors:
                        err_summary = "\n".join(
                            f"  L{e['line']}: {e['message'][:120]}" for e in errors[:5]
                        )
                        feedback_parts.append(f"COMPILATION: {len(errors)} ERREURS:\n{err_summary}")

            # Include sorry locations to help agent focus
            if current_sorry_count > 0 and edited:
                try:
                    file_content_now = Path(filepath).read_text(encoding="utf-8")
                    sorry_locs = [str(i+1) for i, l in enumerate(file_content_now.split("\n")) if "sorry" in l]
                    feedback_parts.append(f"Sorry restants aux lignes: {', '.join(sorry_locs)}")
                except Exception:
                    pass

            context_msg = "\n".join(feedback_parts) if feedback_parts else (
                f"Continue. Sorry count: {current_sorry_count}/{original_sorry_count}. "
                f"Propose ta prochaine modification."
            )

        # Session end
        total_s = (datetime.now() - state.start_time).total_seconds()
        final_sorry = Path(filepath).read_text(encoding="utf-8").count("sorry")

        # Write back best state if current is worse
        if file_plugin.best_content and file_plugin.best_sorry_count < final_sorry:
            print(f"  Restoring best state ({file_plugin.best_sorry_count} sorry vs current {final_sorry})")
            Path(filepath).write_text(file_plugin.best_content, encoding="utf-8")
            final_sorry = file_plugin.best_sorry_count

        success = final_sorry == 0 or final_sorry < original_sorry_count

        print(f"\n{'='*60}")
        print(f"RESULT: {'SUCCESS' if success else 'FAILED'}")
        print(f"  Sorry: {original_sorry_count} → {final_sorry}")
        print(f"  Best seen: {file_plugin.best_sorry_count}")
        print(f"  Iterations: {state.iteration}")
        print(f"  Compiles: {compile_plugin.compile_count} ({compile_plugin.total_compile_s:.1f}s total)")
        print(f"  Total time: {total_s:.1f}s")
        print(f"{'='*60}")

        return {
            "success": success,
            "proof": state.final_proof,
            "iterations": state.iteration,
            "attempts": len(state.tactic_history),
            "total_s": round(total_s, 1),
            "config": self.config_label,
            "sorry_evolution": f"{original_sorry_count} → {final_sorry}",
            "best_sorry": file_plugin.best_sorry_count,
            "compile_count": compile_plugin.compile_count,
            "compile_time_s": round(compile_plugin.total_compile_s, 1),
        }


# ══════════════════════════════════════════════════════════════════════════════
# BATCH RUNNER
# ══════════════════════════════════════════════════════════════════════════════

def run_batch(demos: list = None, provider: str = "zai", max_iterations: int = 3):
    if demos is None:
        demos = [1, 2, 3]

    results = []
    for demo_num in demos:
        demo = DEMOS.get(demo_num)
        if not demo:
            continue

        for mode in ["multi", "single"]:
            label = f"{demo['name']} | {mode}-{provider}"
            print(f"\n{'#'*70}")
            print(f"# BATCH: {label}")
            print(f"{'#'*70}")

            trace = TraceLogger()
            t0 = time.time()

            try:
                if mode == "multi":
                    orchestrator, state, _ = create_proof_session(
                        theorem=demo["theorem"],
                        imports=demo.get("imports"),
                        project_dir=LEAN_PROJECT_DIR,
                        provider=provider,
                        max_iterations=max_iterations,
                    )
                    orchestrator.run(f"Prove: {demo['theorem']}", verbose=True)
                    success = state.proof_complete
                    proof = state.final_proof
                    iterations = state.iteration
                else:
                    prover = SingleAgentProver(trace=trace, provider=provider)
                    result = prover.prove(
                        theorem=demo["theorem"],
                        imports=demo.get("imports"),
                        max_iterations=max_iterations,
                    )
                    success = result["success"]
                    proof = result["proof"]
                    iterations = result["iterations"]

                trace_name = f"{demo['name']}_{mode}_{provider}"
                trace.save(trace_name)

                total_s = time.time() - t0
                results.append({
                    "demo": demo_num, "demo_name": demo["name"],
                    "mode": mode, "provider": provider,
                    "success": success, "iterations": iterations,
                    "proof": proof or "",
                    "total_s": round(total_s, 1),
                })

            except Exception as e:
                print(f"  ERROR: {e}")
                results.append({
                    "demo": demo_num, "demo_name": demo["name"],
                    "mode": mode, "provider": provider,
                    "success": False, "iterations": 0,
                    "proof": f"ERROR: {e}", "total_s": 0,
                })

    # Print summary table
    print(f"\n{'='*90}")
    print("BATCH SUMMARY")
    print(f"{'='*90}")
    print(f"{'Demo':<28} {'Mode':<10} {'OK?':<5} {'Iter':<5} {'Time':>7} {'Proof'}")
    print("-" * 90)
    for r in results:
        print(f"{r['demo_name']:<28} {r['mode']:<10} "
              f"{'OK' if r['success'] else 'FAIL':<5} {r['iterations']:<5} "
              f"{r['total_s']:>6.1f}s {(r.get('proof') or '')[:35]}")

    return results


# ══════════════════════════════════════════════════════════════════════════════
# MAIN
# ══════════════════════════════════════════════════════════════════════════════

def main():
    parser = argparse.ArgumentParser(description="Multi-Agent Lean Proof System (SK port)")
    parser.add_argument("--demo", type=int, default=1, help="Demo number (1-8)")
    parser.add_argument("--batch", action="store_true", help="Run batch over demos")
    parser.add_argument("--demos", type=str, default="1,2,3",
                        help="Comma-separated demo numbers for batch")
    parser.add_argument("--max-iterations", type=int, default=6,
                        help="Max proof iterations")
    parser.add_argument("--mode", choices=["multi", "single", "both", "autonomous"], default="multi",
                        help="Agent mode (autonomous = minimal orchestrator with full file editing)")
    parser.add_argument("--tactic", default="zai", help="Tactic agent provider")
    parser.add_argument("--no-thinking", action="store_true")
    parser.add_argument("--verify-only", action="store_true",
                        help="Just verify known proof")
    parser.add_argument("--verbose", action="store_true")

    # Autonomous mode arguments
    parser.add_argument("--lean", type=str, default=None,
                        help="Path to .lean file for autonomous proof (bypasses demos)")
    parser.add_argument("--sorry-line", type=int, default=0,
                        help="Line number of sorry to target (0 = auto-detect first sorry)")
    parser.add_argument("--hints", type=str, default="",
                        help="Strategic hints for the autonomous prover")
    parser.add_argument("--all-sorry", action="store_true",
                        help="Try to eliminate ALL sorry in the file (not just one)")
    args = parser.parse_args()

    # ── Autonomous mode: direct .lean file ──
    if args.lean:
        lean_path = Path(args.lean)
        if not lean_path.exists():
            print(f"File not found: {lean_path}")
            sys.exit(1)

        content = lean_path.read_text(encoding="utf-8")
        sorry_count = content.count("sorry")
        if sorry_count == 0:
            print(f"No sorry found in {lean_path}")
            sys.exit(0)

        # Auto-detect sorry line if not specified
        sorry_line = args.sorry_line
        if sorry_line == 0:
            for i, line in enumerate(content.split("\n"), 1):
                if "sorry" in line:
                    sorry_line = i
                    break

        # Build a synthetic demo dict
        demo = {
            "name": lean_path.stem,
            "file": str(lean_path),
            "line": sorry_line,
            "theorem": lean_path.stem,
            "description": f"Autonomous proof on {lean_path.name}, {sorry_count} sorry, targeting line {sorry_line}",
        }

        trace = TraceLogger()
        prover = AutonomousProver(
            trace=trace, provider=args.tactic,
            thinking=not args.no_thinking,
        )
        result = prover.prove_sorry(
            demo=demo,
            max_iterations=args.max_iterations,
            strategic_hints=args.hints,
        )
        trace.save(f"auto_{demo['name']}")
        return

    demo = DEMOS.get(args.demo)
    if not demo:
        print(f"Unknown demo {args.demo}. Available: {list(DEMOS.keys())}")
        sys.exit(1)

    # Sorry-mode demos (6-8) use SingleAgentProver.prove_sorry()
    is_sorry_mode = demo.get("sorry_type") is not None

    # Verify-only mode
    if args.verify_only and not is_sorry_mode:
        trace = TraceLogger()
        result = verify_with_lean(
            theorem=demo["theorem"], tactic=demo["proof"],
            imports=demo.get("imports"), project_dir=LEAN_PROJECT_DIR, trace=trace,
        )
        print(f"Known proof '{demo['proof']}': {'VALID' if result['success'] else 'INVALID'} "
              f"({result['time_s']:.1f}s via {result.get('backend', '?')})")
        if result["errors"]:
            print(f"Errors: {result['errors'][:300]}")
        return

    if args.batch:
        demo_nums = [int(x.strip()) for x in args.demos.split(",")]
        run_batch(demos=demo_nums, provider=args.tactic, max_iterations=args.max_iterations)
        return

    # ── Autonomous mode for sorry-demos ──
    if is_sorry_mode and args.mode == "autonomous":
        # Support batch demos in autonomous mode
        demo_list = [demo]
        if args.demos:
            demo_list = [DEMOS[d] for d in args.demos if d in DEMOS and "file" in DEMOS[d]]

        all_results = []
        for d in demo_list:
            trace = TraceLogger()
            prover = AutonomousProver(
                trace=trace, provider=args.tactic,
                thinking=not args.no_thinking,
            )
            result = prover.prove_sorry(
                demo=d,
                max_iterations=args.max_iterations,
                strategic_hints=args.hints,
            )
            trace.save(f"auto_{d['name']}")
            all_results.append((d['name'], result))
            print(f"\n{'='*60}")
            print(f"RESULT: {'SUCCESS' if result['success'] else 'FAILED'}")
            print(f"  Sorry evolution: {result['sorry_evolution']}")
            print(f"  Best sorry: {result['best_sorry']}")
            print(f"  Compiles: {result['compile_count']} ({result['compile_time_s']}s)")
            print(f"  Time: {result['total_s']:.1f}s, Iterations: {result['iterations']}")
            print(f"{'='*60}")

        if len(all_results) > 1:
            print(f"\n{'='*60}")
            print("BATCH SUMMARY:")
            for name, r in all_results:
                status = "OK" if r['success'] else "FAIL"
                print(f"  {name}: {status} ({r['sorry_evolution']}, {r['total_s']:.0f}s)")
            print(f"{'='*60}")
        return

    # ── Sorry-mode demos (6-8) ──
    if is_sorry_mode:
        mode = args.mode if args.mode != "both" else "multi"
        print(f"\n>>> SORRY-REPLACEMENT ({demo['name']})... [mode={mode}]")
        trace = TraceLogger()

        if mode == "multi":
            prover = MultiAgentSorryProver(
                trace=trace, provider=args.tactic,
                thinking=not args.no_thinking,
            )
        else:
            prover = SingleAgentProver(
                trace=trace, provider=args.tactic,
                thinking=not args.no_thinking,
            )

        if isinstance(prover, MultiAgentSorryProver):
            result = prover.prove_sorry(demo=demo, max_iterations=args.max_iterations)
        else:
            result = prover.prove_sorry(demo=demo, max_iterations=args.max_iterations)

        trace.save(f"sorry_{demo['name']}")
        print(f"\n{'='*60}")
        print(f"RESULT: {'SUCCESS' if result['success'] else 'FAILED'}")
        if result.get("proof"):
            print(f"  Proof: {result['proof'][:200]}")
        print(f"  Time: {result['total_s']:.1f}s, Iterations: {result['iterations']}")
        if result.get("sorry_evolution"):
            print(f"  Sorry evolution: {result['sorry_evolution']}")
        print(f"{'='*60}")
        return

    # ── Standard demos (1-5) ──
    if args.mode in ("multi", "both"):
        print("\n>>> MULTI-AGENT (SK function calling)...")
        orchestrator, state, trace = create_proof_session(
            theorem=demo["theorem"],
            imports=demo.get("imports"),
            project_dir=LEAN_PROJECT_DIR,
            provider=args.tactic,
            max_iterations=args.max_iterations,
            verbose=args.verbose,
        )
        orchestrator.run(f"Prove: {demo['theorem']}", verbose=True)
        trace.save(f"multi_{demo['name']}")
        multi_success = state.proof_complete
        multi_proof = state.final_proof

    if args.mode in ("single", "both"):
        print("\n>>> SINGLE-AGENT baseline...")
        trace2 = TraceLogger()
        prover = SingleAgentProver(trace=trace2, provider=args.tactic,
                                   thinking=not args.no_thinking)
        result = prover.prove(
            theorem=demo["theorem"],
            imports=demo.get("imports"),
            max_iterations=args.max_iterations,
        )
        trace2.save(f"single_{demo['name']}")

    if args.mode == "both":
        print(f"\n{'='*60}")
        print("COMPARISON")
        print(f"{'='*60}")
        print(f"  Multi:  {'OK' if multi_success else 'FAIL'} (proof: {multi_proof})")
        print(f"  Single: {'OK' if result['success'] else 'FAIL'} (proof: {result.get('proof')})")
    elif args.mode == "multi":
        print(f"\n{'='*60}")
        print(f"RESULT: {'SUCCESS' if multi_success else 'FAILED'}")
        if multi_proof:
            print(f"  Proof: {multi_proof}")
        print(f"{'='*60}")
    elif args.mode == "single":
        print(f"\n{'='*60}")
        print(f"RESULT: {'SUCCESS' if result['success'] else 'FAILED'}")
        if result.get("proof"):
            print(f"  Proof: {result['proof']}")
        print(f"{'='*60}")


if __name__ == "__main__":
    import sys
    sys.stdout.reconfigure(line_buffering=True)
    sys.stderr.reconfigure(line_buffering=True)
    main()
