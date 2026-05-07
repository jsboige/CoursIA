"""Per-agent tool classes for the multi-agent Lean 4 proof system.

Each agent gets ONLY the methods it needs — no single monolithic plugin.
Agent Framework auto-infers schemas from type hints + docstrings.
"""

import json
import re
import time
import uuid
from pathlib import Path
from typing import Optional, Dict, List

from .state import ProofState, TacticAttempt, SorryContext
from .trace import TraceLogger


# ══════════════════════════════════════════════════════════════════════════════
# SEARCH AGENT TOOLS — lemma discovery
# ══════════════════════════════════════════════════════════════════════════════

class SearchTools:
    """Tools for SearchAgent: lemma discovery and proof state reading."""

    def __init__(self, state: ProofState, filepath: str = "", trace: TraceLogger = None):
        self._state = state
        self._filepath = filepath
        self._trace = trace
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
            "Finset.sum_eq_single": ("sum s f = f b if b in s and others zero", "Finset"),
            "Finset.card_union_of_disjoint": ("card (s ∪ t) = card s + card t", "Finset"),
            "Finset.sum_add_distrib": ("sum s (f + g) = sum s f + sum s g", "Finset"),
            "Finset.sum_const": ("sum s (fun _ => c) = card s * c", "Finset"),
        }

    def search_mathlib_lemmas(self, goal: str, max_results: int = 10) -> str:
        """Search for Mathlib lemmas relevant to a proof goal."""
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
        found = results[:max_results]

        if self._trace:
            self._trace.log(
                agent="SearchAgent", role="tool", content=f"Found {len(found)} lemmas",
                duration_s=0.01, tool_name="search_mathlib_lemmas",
                tool_args={"goal": goal[:80]}, tool_result=f"{len(found)} results",
            )

        return json.dumps(found, indent=2, ensure_ascii=False)

    def search_local_lemmas(self) -> str:
        """Search for lemmas defined in the current .lean file (no sorry)."""
        from .lean_utils import extract_local_lemmas
        if not self._filepath:
            return json.dumps({"error": "No file configured"})

        content = Path(self._filepath).read_text(encoding="utf-8")
        sorry_lines = {i + 1 for i, l in enumerate(content.split("\n")) if "sorry" in l}
        lemmas = extract_local_lemmas(self._filepath, sorry_lines)

        # Update shared state
        self._state.local_lemmas = lemmas

        if self._trace:
            self._trace.log(
                agent="SearchAgent", role="tool",
                content=f"Found {len(lemmas)} local lemmas",
                duration_s=0.01, tool_name="search_local_lemmas",
                tool_result=", ".join(lemmas[:20]),
            )

        return json.dumps({
            "count": len(lemmas),
            "lemmas": lemmas,
        }, indent=2, ensure_ascii=False)

    def get_proof_state(self) -> str:
        """Get a rich summary of the current proof state."""
        return self._state.get_context_summary()

    def add_discovered_lemma(self, name: str, statement: str = "",
                             namespace: str = "", relevance: float = 0.5) -> str:
        """Add a discovered lemma to the shared state."""
        lemma_id = self._state.add_lemma(name, statement, namespace, relevance)
        return f"Added lemma: {lemma_id}"

    def file_read_lines(self, start: int, end: int) -> str:
        """Read a specific range of lines from the .lean file (1-based inclusive)."""
        if not self._filepath:
            return "No file configured"
        content = Path(self._filepath).read_text(encoding="utf-8")
        lines = content.split("\n")
        start = max(1, start)
        end = min(len(lines), end)
        selected = lines[start - 1:end]
        return "\n".join(f"{start + i}: {line}" for i, line in enumerate(selected))


# ══════════════════════════════════════════════════════════════════════════════
# TACTIC AGENT TOOLS — tactic generation and file editing
# ══════════════════════════════════════════════════════════════════════════════

class TacticTools:
    """Tools for TacticAgent: tactic generation, decomposition, and file editing."""

    def __init__(self, state: ProofState, filepath: str = "",
                 sorry_context: SorryContext = None,
                 imports: str = "", trace: TraceLogger = None):
        self._state = state
        self._filepath = filepath
        self._sorry_ctx = sorry_context
        self._imports = imports
        self._trace = trace
        self._best_content: Optional[str] = None
        self._best_sorry_count: int = 999
        self._original_sorry_count: int = 999
        self._original_file_size: int = 0
        self._lock_file = Path(filepath).with_suffix(".prover.lock") if filepath else None
        self._session_id = str(uuid.uuid4())[:8]
        if filepath and Path(filepath).exists():
            self._original_file_size = len(Path(filepath).read_text(encoding="utf-8"))

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

    def generate_tactics(self, goal: str, difficulty: str = "simple") -> str:
        """Generate tactic suggestions based on the goal pattern."""
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

    def submit_decomposition(self, have_name: str, have_type: str,
                             have_proof: str = "sorry",
                             main_tactic: str = "sorry") -> str:
        """Submit a decomposition: split the current goal into sub-goals using 'have'."""
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

    def submit_tactic(self, tactic: str, confidence: float = 0.5,
                      reasoning: str = "") -> str:
        """Submit a Lean 4 tactic to prove the theorem. Provide ONLY the tactic(s) after `by`."""
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

    def file_read_lines(self, start: int, end: int) -> str:
        """Read a specific range of lines from the .lean file (1-based inclusive)."""
        if not self._filepath:
            return "No file configured"
        content = Path(self._filepath).read_text(encoding="utf-8")
        lines = content.split("\n")
        start = max(1, start)
        end = min(len(lines), end)
        selected = lines[start - 1:end]
        return "\n".join(f"{start + i}: {line}" for i, line in enumerate(selected))

    def file_find_sorry_lines(self) -> str:
        """Find all sorry lines in the file with their line numbers and surrounding context."""
        if not self._filepath:
            return json.dumps({"error": "No file configured"})
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
                    "line": i + 1, "content": line.strip(), "context": ctx,
                })
        return json.dumps({
            "sorry_count": len(sorry_lines), "sorry_lines": sorry_lines,
        }, ensure_ascii=False)

    def get_proof_state(self) -> str:
        """Get a rich summary of the current proof state with hypotheses and lemma history."""
        return self._state.get_context_summary()

    def get_available_hypotheses(self) -> str:
        """Get hypotheses available in the current proof context (have, intro, case)."""
        if not self._filepath or not self._sorry_ctx:
            return json.dumps({"error": "No file/context configured"})
        from .lean_utils import extract_hypotheses
        sorry_line = self._sorry_ctx.sorry_line
        hyps = extract_hypotheses(self._filepath, sorry_line)
        self._state.available_hypotheses = hyps
        return json.dumps({
            "sorry_line": sorry_line,
            "hypotheses": hyps,
            "count": len(hyps),
        }, indent=2, ensure_ascii=False)

    def _check_file_size_guard(self, new_content: str, operation: str) -> Optional[str]:
        """Block writes that change file size by >50% (full-file rewrite detection)."""
        if self._original_file_size == 0:
            return None
        new_size = len(new_content)
        ratio = abs(new_size - self._original_file_size) / self._original_file_size
        if ratio > 0.5:
            if self._trace:
                self._trace.log(
                    agent="TacticTools", role="size_guard",
                    content=f"BLOCKED {operation}: new={new_size} vs original={self._original_file_size} "
                            f"(ratio={ratio:.0%}). Full-file rewrite suspected.",
                    duration_s=0.01,
                )
            return (f"BLOCKED by file size guard: your replacement would change the file by {ratio:.0%} "
                    f"(new={new_size} chars vs original={self._original_file_size} chars). "
                    f"Use TARGETED replacements: replace only the specific sorry line or a small range, "
                    f"NOT the entire file.")
        return None

    def file_replace_lines(self, start: int, end: int, new_content: str) -> str:
        """Replace a range of lines in the .lean file. Lines are 1-based, inclusive."""
        if not self._filepath:
            return json.dumps({"error": "No file configured"})
        try:
            content = Path(self._filepath).read_text(encoding="utf-8")
            lines = content.split("\n")
            old_lines = lines[start - 1:end] if end <= len(lines) else lines[start - 1:]
            old_text = "\n".join(old_lines)

            new_lines = new_content.split("\n")
            lines[start - 1:end if end <= len(lines) else len(lines)] = new_lines
            new_file_content = "\n".join(lines)

            # File size guard: block full-file rewrites
            size_error = self._check_file_size_guard(new_file_content, "file_replace_lines")
            if size_error:
                return json.dumps({"error": size_error}, ensure_ascii=False)

            sorry_count = new_file_content.count("sorry")

            # Sorry guard: block if net sorry increase beyond original
            if sorry_count > self._original_sorry_count:
                if self._trace:
                    self._trace.log(
                        agent="TacticTools", role="sorry_guard",
                        content=f"BLOCKED file_replace_lines: {sorry_count} > original {self._original_sorry_count}. REVERTING.",
                        duration_s=0.01,
                    )
                return json.dumps({
                    "error": f"BLOCKED by sorry guard: {sorry_count} sorry > original {self._original_sorry_count}. "
                             f"Do NOT introduce new sorry in replacements.",
                    "replaced_lines": f"{start}-{end}",
                    "sorry_count": sorry_count,
                }, ensure_ascii=False)

            Path(self._filepath).write_text(new_file_content, encoding="utf-8")

            if sorry_count < self._best_sorry_count:
                self._best_sorry_count = sorry_count
                self._best_content = new_file_content

            return json.dumps({
                "replaced_lines": f"{start}-{end}",
                "old_text_preview": old_text[:200],
                "new_sorry_count": sorry_count,
                "best_sorry_count": self._best_sorry_count,
            }, ensure_ascii=False)
        except Exception as e:
            return json.dumps({"error": str(e)})

    def file_replace_sorry(self, sorry_line: int, replacement: str) -> str:
        """Replace the sorry at a given line number with new tactic text. Auto-detects indentation."""
        if not self._filepath:
            return json.dumps({"error": "No file configured"})
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

            # File size guard: block full-file rewrites
            size_error = self._check_file_size_guard(new_content, "file_replace_sorry")
            if size_error:
                return json.dumps({"error": size_error}, ensure_ascii=False)

            sorry_count = new_content.count("sorry")

            # Sorry guard: block if net sorry increase beyond original (regression)
            if sorry_count > self._original_sorry_count:
                if self._trace:
                    self._trace.log(
                        agent="TacticTools", role="sorry_guard",
                        content=f"BLOCKED: {sorry_count} sorry > original {self._original_sorry_count}. "
                                f"Replacement introduces new sorry. REVERTING.",
                        duration_s=0.01,
                    )
                return json.dumps({
                    "error": f"BLOCKED by sorry guard: {sorry_count} sorry > original {self._original_sorry_count}. "
                             f"Your replacement introduces NEW sorry. Write the tactic WITHOUT sorry.",
                    "replaced": old_line.strip(),
                    "sorry_count": sorry_count,
                }, ensure_ascii=False)

            Path(self._filepath).write_text(new_content, encoding="utf-8")

            if sorry_count < self._best_sorry_count:
                self._best_sorry_count = sorry_count
                self._best_content = new_content

            return json.dumps({
                "replaced": old_line.strip(),
                "new_lines": len(replacement_lines),
                "new_sorry_count": sorry_count,
                "best_sorry_count": self._best_sorry_count,
            }, ensure_ascii=False)
        except Exception as e:
            return json.dumps({"error": str(e)})

    def compile_probe_goal(self, sorry_line: int) -> str:
        """Extract the Lean goal state at a specific sorry line by probing. Returns the goal text."""
        from .lean_utils import get_goal_state
        goal = get_goal_state(self._filepath, sorry_line)
        if goal:
            return json.dumps({"goal": goal, "line": sorry_line})
        return json.dumps({"goal": None, "line": sorry_line, "hint": "Could not extract goal"})

    def compile(self, check_axioms: bool = False) -> str:
        """3-level verification: build SUCCESS + sorry count delta + axiom whitelist.

        Level 1: lake build succeeds (no errors)
        Level 2: sorry count decreased or stable (no regression)
        Level 3 (optional): #print axioms reveals no unexpected axioms

        Args:
            check_axioms: If True, run Level 3 axiom check after successful build
        """
        from .verifier import get_verifier
        if not self._filepath:
            return json.dumps({"error": "No file configured"})

        project_dir = str(Path(self._filepath).parent.parent)
        start = time.time()

        verifier = get_verifier(project_dir)
        subdir = Path(self._filepath).parent.name
        filename = Path(self._filepath).name
        relative_path = f"{subdir}/{filename}"
        result = verifier.verify_project_file(relative_path)

        duration = time.time() - start
        raw_output = result.get("raw_output", "")
        success = result.get("success", False)
        cached = result.get("cached", False)

        errors = []
        for line in raw_output.split("\n"):
            m = re.match(r".*?(\d+):\d+: error: (.*)", line)
            if not m:
                m = re.match(r"error: .*?(\d+):\d+: (.*)", line)
            if m:
                errors.append({"line": int(m.group(1)), "message": m.group(2)})

        content = Path(self._filepath).read_text(encoding="utf-8")
        sorry_count = content.count("sorry")

        sorry_delta = self._original_sorry_count - sorry_count
        level_1 = success
        level_2 = sorry_delta >= 0
        level_3 = None

        if check_axioms and success:
            module_name = relative_path.replace("/", ".").replace("\\", ".")
            if module_name.endswith(".lean"):
                module_name = module_name[:-5]
            axiom_result = verifier.check_axioms(module_name)
            level_3 = axiom_result.get("success", False)
            if self._trace and axiom_result.get("forbidden"):
                self._trace.log(
                    agent="TacticAgent", role="axiom_check",
                    content=f"FORBIDDEN axioms: {axiom_result['forbidden']}",
                    duration_s=0, tool_name="compile",
                )

        overall = level_1 and level_2 and (level_3 if level_3 is not None else True)

        if self._trace:
            self._trace.log(
                agent="TacticAgent", role="compile",
                content=f"compile: L1={level_1} L2={level_2}(Δ{sorry_delta}) L3={level_3} "
                        f"| {sorry_count} sorry | {'CACHED' if cached else 'fresh'}",
                duration_s=duration, tool_name="compile",
                tool_result=raw_output[:500],
            )

        return json.dumps({
            "success": overall,
            "level_1_build": level_1,
            "level_2_sorry": level_2,
            "level_3_axioms": level_3,
            "sorry_count": sorry_count,
            "sorry_delta": sorry_delta,
            "original_sorry_count": self._original_sorry_count,
            "error_count": len(errors), "errors": errors[:10],
            "compile_time_s": round(duration, 1),
            "cached": cached,
            "raw_output_preview": raw_output[:500],
        }, ensure_ascii=False)

    def verify_sorry_replacement(self, tactic: str) -> str:
        """Verify a tactic as sorry replacement in the actual .lean file."""
        from .lean_utils import verify_sorry_replacement as _verify

        if not self._sorry_ctx:
            return json.dumps({"success": False, "errors": "No sorry context"})
        start = time.time()
        result = _verify(
            filepath=self._sorry_ctx.filepath,
            sorry_line=self._sorry_ctx.sorry_line,
            replacement=tactic,
        )
        duration = time.time() - start
        sorry_count = self._count_sorry_after_replacement(tactic)

        if self._trace:
            self._trace.log(
                agent="TacticAgent", role="sorry_verify",
                content=f"tactic={tactic[:80]} -> success={result['success']}",
                duration_s=duration, tool_name="verify_sorry_replacement",
                tool_result=f"success={result['success']}, sorry_count={sorry_count}",
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
        if not self._sorry_ctx:
            return -1
        content = self._sorry_ctx.full_file
        lines = content.split("\n")
        sorry_idx = self._sorry_ctx.sorry_line - 1
        indent = self._sorry_ctx.indentation
        indent_str = " " * indent
        replacement_lines = [indent_str + l.strip() for l in tactic.strip().split("\n") if l.strip()]
        new_lines = lines[:sorry_idx] + replacement_lines + lines[sorry_idx + 1:]
        return "\n".join(new_lines).count("sorry")

    @property
    def best_sorry_count(self) -> int:
        return self._best_sorry_count

    @property
    def best_content(self) -> Optional[str]:
        return self._best_content


# ══════════════════════════════════════════════════════════════════════════════
# CRITIC AGENT TOOLS — error analysis and routing
# ══════════════════════════════════════════════════════════════════════════════

class CriticTools:
    """Tools for CriticAgent: failure analysis and routing decisions."""

    def __init__(self, state: ProofState, trace: TraceLogger = None):
        self._state = state
        self._trace = trace

    def analyze_failure(self, tactic: str, error: str, goal: str = "") -> str:
        """Analyze a tactic failure and classify the error type."""
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
        elif "type mismatch" in error:
            hints.append("Type mismatch. Try norm_cast, push_cast, or cast lemmas.")
        elif "unsolved goals" in error:
            hints.append("Tactic left open goals. Add more tactics or decompose.")
        elif "sorry" in error.lower():
            hints.append("Decomposition with sorry detected — partial progress.")

        return json.dumps({
            "tactic": tactic,
            "error_type": "progress" if "progress" in error else "type_error",
            "hints": hints,
            "suggestion": hints[0] if hints else "Try a different tactic.",
        }, indent=2, ensure_ascii=False)

    def get_proof_state(self) -> str:
        """Get a summary of the current proof state."""
        return json.dumps(
            self._state.get_state_snapshot(summarize=True), indent=2, ensure_ascii=False
        )

    def designate_next_agent(self, agent_name: str, reason: str = "") -> str:
        """Designate which agent should act next. Use 'search', 'tactic', or 'coordinator'."""
        self._state.designate_next_agent(agent_name)
        return f"Next agent: {agent_name}. Reason: {reason}"


# ══════════════════════════════════════════════════════════════════════════════
# COORDINATOR AGENT TOOLS — strategic overview and escalation
# ══════════════════════════════════════════════════════════════════════════════

class CoordinatorTools:
    """Tools for CoordinatorAgent: strategic overview and file inspection."""

    def __init__(self, state: ProofState, filepath: str = "", trace: TraceLogger = None):
        self._state = state
        self._filepath = filepath
        self._trace = trace
        self._known_lemmas = {
            "Nat.add_zero": ("n + 0 = n", "Nat"),
            "Nat.zero_add": ("0 + n = n", "Nat"),
            "Nat.add_comm": ("n + m = m + n", "Nat"),
            "Nat.mul_comm": ("n * m = m * n", "Nat"),
            "Eq.refl": ("a = a", "Logic"),
            "Eq.symm": ("a = b -> b = a", "Logic"),
            "Finset.sum_erase_add": ("sum s f = sum (s.erase a) f + f a", "Finset"),
        }

    def get_proof_state(self) -> str:
        """Get a summary of the current proof state."""
        return json.dumps(
            self._state.get_state_snapshot(summarize=True), indent=2, ensure_ascii=False
        )

    def file_read_lines(self, start: int, end: int) -> str:
        """Read a specific range of lines from the .lean file (1-based inclusive)."""
        if not self._filepath:
            return "No file configured"
        content = Path(self._filepath).read_text(encoding="utf-8")
        lines = content.split("\n")
        start = max(1, start)
        end = min(len(lines), end)
        selected = lines[start - 1:end]
        return "\n".join(f"{start + i}: {line}" for i, line in enumerate(selected))

    def search_mathlib_lemmas(self, goal: str, max_results: int = 10) -> str:
        """Search for Mathlib lemmas relevant to a proof goal."""
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
            if score > 0:
                results.append({
                    "name": name, "statement": statement,
                    "namespace": namespace, "relevance": min(score, 1.0),
                })
        results.sort(key=lambda x: x["relevance"], reverse=True)
        return json.dumps(results[:max_results], indent=2, ensure_ascii=False)
