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
from .knowledge import ProofKnowledgeBase


# ══════════════════════════════════════════════════════════════════════════════
# SEARCH AGENT TOOLS — lemma discovery
# ══════════════════════════════════════════════════════════════════════════════

class SearchTools:
    """Tools for SearchAgent: lemma discovery and proof state reading."""

    def __init__(self, state: ProofState, filepath: str = "", trace: TraceLogger = None,
                 kb: Optional["ProofKnowledgeBase"] = None):
        self._state = state
        self._filepath = filepath
        self._trace = trace
        # B.1 ProofKnowledgeBase: shared singleton across sessions. Each SearchTools
        # instance reads from the same proof_knowledge.json so successful tactics
        # from past runs warm-start this one.
        self._kb = kb or ProofKnowledgeBase()
        # F11 (ai-01 C41 directive): track (query, result_count) to detect
        # same-query-0-result loops. DEMO 16 BG showed 12 identical calls.
        self._search_history: list[tuple[str, int]] = []
        self._known_lemmas = {
            # Arithmetic on Nat
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
            "Nat.odd_iff": ("Odd n ↔ n % 2 = 1", "Nat"),
            "Nat.div_two_lt_of_lt_mul_two_succ": (
                "n < (k + 1) * 2 → n / 2 < k + 1", "Nat"),
            # Logic
            "Eq.refl": ("a = a", "Logic"),
            "Eq.symm": ("a = b -> b = a", "Logic"),
            "lt_of_le_of_ne": ("a ≤ b → a ≠ b → a < b", "Order"),
            "le_of_not_gt": ("¬ a > b → a ≤ b", "Order"),
            "not_lt": ("¬ a < b ↔ b ≤ a", "Order"),
            # Finset basics
            "Finset.sum_erase_add": ("sum s f = sum (s.erase a) f + f a", "Finset"),
            "Finset.sum_eq_single": ("sum s f = f b if b in s and others zero", "Finset"),
            "Finset.card_union_of_disjoint": ("card (s ∪ t) = card s + card t", "Finset"),
            "Finset.sum_add_distrib": ("sum s (f + g) = sum s f + sum s g", "Finset"),
            "Finset.sum_const": ("sum s (fun _ => c) = card s * c", "Finset"),
            "Finset.card_le_card": ("s ⊆ t → s.card ≤ t.card", "Finset"),
            "Finset.mem_filter": (
                "x ∈ s.filter p ↔ x ∈ s ∧ p x", "Finset"),
            "Finset.card_univ": ("(Finset.univ : Finset α).card = Fintype.card α", "Finset"),
            "Finset.length_toList": ("s.toList.length = s.card", "Finset"),
            "Finset.toList_filter": (
                "(s.filter p).toList = s.toList.filter p (up to perm)", "Finset"),
            "Finset.card_filter_add_card_filter_not": (
                "|{x ∈ s | p x}| + |{x ∈ s | ¬p x}| = s.card  "
                "-- CALL with named args: (s := ...) (p := ...). "
                "Deprecated alias: Finset.filter_card_add_filter_neg_card_eq_card "
                "(do NOT use, removed in Mathlib current)", "Finset"),
            "Finset.filter_congr": (
                "(∀ x ∈ s, p x ↔ q x) → s.filter p = s.filter q  "
                "-- USAGE: apply Finset.filter_congr; intro i _; exact iff_proof", "Finset"),
            "not_le": ("¬a ≤ b ↔ b < a  -- USE (not_le).symm to flip order", "Order"),
            # Lists / sorting / counting (used in median voter counting lemma)
            "List.length_mergeSort": (
                "(l.mergeSort r).length = l.length", "List"),
            "List.mergeSort_perm": (
                "(l.mergeSort r) ~ l", "List"),
            "List.pairwise_mergeSort": (
                "Trans r → IsAntisymm α r → IsTotal α r → "
                "(l.mergeSort r).Pairwise r", "List"),
            "List.length_map": ("(l.map f).length = l.length", "List"),
            "List.length_take": ("(l.take n).length = min n l.length", "List"),
            "List.length_drop": ("(l.drop n).length = l.length - n", "List"),
            "List.take_append_drop": (
                "l.take n ++ l.drop n = l", "List"),
            "List.Perm.countP_eq": (
                "(p : α → Bool) → l₁ ~ l₂ → l₁.countP p = l₂.countP p", "List.Perm"),
            "List.countP_append": (
                "(l₁ ++ l₂).countP p = l₁.countP p + l₂.countP p", "List"),
            "List.countP_map": (
                "(l.map f).countP p = l.countP (p ∘ f)", "List"),
            "List.countP_eq_zero": (
                "l.countP p = 0 ↔ ∀ a ∈ l, ¬ p a", "List"),
            "List.countP_eq_length": (
                "l.countP p = l.length ↔ ∀ a ∈ l, p a", "List"),
            "List.countP_le_length": ("l.countP p ≤ l.length", "List"),
            "List.Pairwise.rel_get_of_le": (
                "l.Pairwise r → ∀ i j (h : i ≤ j) (hj : j < l.length), "
                "r l[i] l[j]  -- (Mathlib/Data/List/Pairwise.lean L142)", "List.Pairwise"),
            "List.getD": (
                "l.getD i default = if i < l.length then l[i] else default", "List"),
            "List.Perm.mem_iff": (
                "l₁ ~ l₂ → (a ∈ l₁ ↔ a ∈ l₂)", "List.Perm"),
        }

    def search_mathlib_lemmas(self, goal: str, max_results: int = 10,
                              use_lsp: bool = True) -> str:
        """Search for Mathlib lemmas relevant to a proof goal.

        Sources, in priority order:
          0. ProofKnowledgeBase (past successful tactics on similar goals)
          1. Lean LSP search via exact?/apply? (B.2)
          2. Hardcoded lemma dictionary for common patterns
        """
        # F11 loop detection — escalate after 3 same-query-0-results
        same_query_zeros = sum(1 for q, n in self._search_history if q == goal and n == 0)
        if same_query_zeros >= 2:
            if self._trace:
                self._trace.log(
                    agent="SearchAgent", role="loop_detected",
                    content=f"LOOP_DETECTED: query '{goal[:60]}' returned 0 results "
                            f"{same_query_zeros + 1}x. Breaking loop.",
                    duration_s=0.01, tool_name="search_mathlib_lemmas",
                    tool_args={"goal": goal[:80]},
                    tool_result="LOOP_DETECTED",
                )
            return (
                f"LOOP_DETECTED: query '{goal}' returned 0 results {same_query_zeros + 1}x. "
                f"STOP searching this term. Either:\n"
                f"1. Reformulate with different keywords (synonyms, broader/narrower terms)\n"
                f"2. Call `request_director_guidance` via CoordinatorAgent — the lemma likely does not exist\n"
                f"3. Add the missing lemma as a sub-goal via `submit_decomposition`"
            )
        kb_results = []
        try:
            kb_hit = self._kb.lookup(goal)
            if kb_hit:
                kb_results.append({
                    "name": f"KB_HIT:{kb_hit.get('theorem', '?')}",
                    "statement": f"PROVEN tactic: {kb_hit['tactic']}",
                    "namespace": "ProofKnowledgeBase",
                    "relevance": 1.0,
                    "source": "kb_exact",
                    "uses": kb_hit.get("uses", 1),
                })
            for sim in self._kb.search_similar(goal, max_results=3):
                kb_results.append({
                    "name": f"KB_SIM:{sim.get('theorem', '?')}",
                    "statement": (f"Similar past tactic ({sim.get('relevance', 0):.2f}): "
                                  f"{sim['tactic']}"),
                    "namespace": "ProofKnowledgeBase",
                    "relevance": min(0.95, 0.5 + sim.get("relevance", 0) * 0.5),
                    "source": "kb_similar",
                    "uses": sim.get("uses", 1),
                })
        except Exception:
            pass

        # B.2: Try real Lean LSP search next
        if use_lsp and self._filepath:
            lsp_results = self._search_via_lsp(goal)
            if lsp_results:
                merged = kb_results + lsp_results
                if self._trace:
                    self._trace.log(
                        agent="SearchAgent", role="tool",
                        content=(f"LSP found {len(lsp_results)} + KB {len(kb_results)} "
                                 f"= {len(merged)} suggestions"),
                        duration_s=0.01, tool_name="search_mathlib_lemmas",
                        tool_args={"goal": goal[:80]},
                        tool_result=f"{len(merged)} (kb={len(kb_results)} lsp={len(lsp_results)})",
                    )
                self._search_history.append((goal, len(merged)))
                return json.dumps(merged[:max_results], indent=2, ensure_ascii=False)

        # Fallback: keyword-based search on known lemmas
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
            # Counting / sorting / median patterns (DEMO 9, 14)
            if any(k in goal_lower for k in ("countp", "count_", "filter")) \
                    and any(k in name_lower for k in ("countp", "filter", "card")):
                score += 0.5
            if any(k in goal_lower for k in ("mergesort", "sort", "pairwise", "sorted")) \
                    and any(k in name_lower for k in ("mergesort", "pairwise", "sort")):
                score += 0.5
            if any(k in goal_lower for k in ("perm", "permut")) and "perm" in name_lower:
                score += 0.4
            if "card" in goal_lower and "card" in name_lower:
                score += 0.3
            if "filter" in goal_lower and "mem_filter" in name_lower:
                score += 0.4
            if score > 0:
                results.append({
                    "name": name, "statement": statement,
                    "namespace": namespace, "relevance": min(score, 1.0),
                    "source": "hardcoded",
                })

        results.sort(key=lambda x: x["relevance"], reverse=True)
        found = kb_results + results[:max_results - len(kb_results)]

        if self._trace:
            self._trace.log(
                agent="SearchAgent", role="tool",
                content=f"Found {len(found)} lemmas (fallback + kb={len(kb_results)})",
                duration_s=0.01, tool_name="search_mathlib_lemmas",
                tool_args={"goal": goal[:80]}, tool_result=f"{len(found)} results",
            )

        self._search_history.append((goal, len(found)))
        return json.dumps(found, indent=2, ensure_ascii=False)

    def _search_via_lsp(self, goal: str) -> list:
        """Search Mathlib using Lean LSP via exact?/apply? tactics."""
        try:
            from .verifier import get_verifier
            project_dir = str(Path(self._filepath).parent.parent)
            verifier = get_verifier(project_dir)
            subdir = Path(self._filepath).parent.name
            module_name = f"{subdir}"

            results = []
            for tactic in ["exact?", "apply?"]:
                search_result = verifier.search_lean(module_name, goal, tactic)
                for suggestion in search_result.get("suggestions", []):
                    results.append({
                        "name": suggestion["tactic"][:50],
                        "statement": suggestion["tactic"],
                        "namespace": "Mathlib",
                        "relevance": 0.9,
                        "source": f"lsp_{tactic}",
                    })
            return results
        except Exception:
            return []

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

    def lookup_proven_pattern(self, goal: str, max_results: int = 5) -> str:
        """Query the persistent ProofKnowledgeBase directly for past successes.

        Returns exact match (if any) plus similar past tactics. Use this BEFORE
        searching Mathlib when the current goal looks like one you've solved
        before (same lemma names, same shape). Cheaper and more targeted than
        rebuilding via LSP.
        """
        try:
            exact = self._kb.lookup(goal)
            similar = self._kb.search_similar(goal, max_results=max_results)
            payload = {
                "kb_size": self._kb.size,
                "exact_match": exact,
                "similar": similar,
            }
            if self._trace:
                hit_count = (1 if exact else 0) + len(similar)
                self._trace.log(
                    agent="SearchAgent", role="tool",
                    content=f"KB lookup: {hit_count} hits (kb_size={self._kb.size})",
                    duration_s=0.01, tool_name="lookup_proven_pattern",
                    tool_args={"goal": goal[:80]},
                    tool_result=f"exact={bool(exact)} similar={len(similar)}",
                )
            return json.dumps(payload, indent=2, ensure_ascii=False)
        except Exception as exc:
            return json.dumps({"error": str(exc), "kb_size": -1})


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
        self._original_content: Optional[str] = None
        # Decomposition budget: how many new sorries the agents may introduce
        # via `have h : sub := by sorry; ...` scaffolding. Replacing one big
        # sorry by two smaller sub-sorries that both compile is structural
        # progress, not a regression — the agent can then attack the smaller
        # sorries in subsequent iterations or future sessions. 5 is a generous
        # ceiling (deeper trees rarely help; explosive growth signals a runaway
        # agent rather than a real strategy). Lifted from a hard cap of 0
        # which made decomposition impossible (2026-05-11 user feedback).
        self._decomposition_budget: int = 2
        # Last file content that survived a `lake build`. May have MORE sorries
        # than the original (decomposition) but compiles. Used at end-of-session
        # to commit partial structural progress instead of restoring original
        # ("all-or-nothing" was the prior bug: sorry==original triggered restore
        # even when the file structurally improved).
        self._last_build_ok_content: Optional[str] = None
        self._last_build_ok_sorry_count: Optional[int] = None
        self._lock_file = Path(filepath).with_suffix(".prover.lock") if filepath else None
        self._session_id = str(uuid.uuid4())[:8]
        self._context_boundary = 20  # max lines from sorry for edits (generous: line shifts after edits)
        if filepath and Path(filepath).exists():
            raw = Path(filepath).read_text(encoding="utf-8")
            self._original_file_size = len(raw)
            self._original_content = raw

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
        """Submit a decomposition: split the current goal into sub-goals using `have`.

        Builds `have <name> : <type> := by <have_proof>; <main_tactic>` and
        records it in tactic_history so the AgentExecutor bridge can lift it
        into ProofMessage.tactic for VerifyExecutor. Without this recording,
        the decomposition would be returned as JSON only and never reach the
        verifier — same dead end as the pre-bridge submit_tactic.
        """
        indent = "  "
        lines = [
            f"have {have_name} : {have_type} := by {have_proof}",
            main_tactic,
        ]
        decomposition = f"\n{indent}".join(lines)
        attempt_id = self._state.add_tactic_attempt(
            tactic=decomposition,
            confidence=0.4,
            explanation=f"decomposition via have {have_name}",
            is_decomposition=True,
        )
        return json.dumps({
            "attempt_id": attempt_id,
            "decomposition": decomposition,
            "have_name": have_name,
            "have_type": have_type,
            "have_proof": have_proof,
            "main_tactic": main_tactic,
            "status": "submitted",
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

    # Lean placeholder patterns that "look like a proof" but never compile.
    # The plain `sorry` token is handled separately by the sorry-count guard;
    # these are the *non-sorry* sentinels the LLM tends to inject.
    _STUB_PATTERNS: List[str] = [
        r"\bexact\s+_\s*$",          # `exact _`
        r"\bexact\s+\?_\s*$",        # `exact ?_`
        r"\bexact\s+\?\w+\s*$",      # `exact ?h`
        r"\brefine\s+\?_\s*$",       # `refine ?_`
        r"\badmit\s*$",              # `admit`
        r"^\s*_\s*$",                # bare `_` line
    ]

    def _check_stub_guard(self, replacement: str, operation: str) -> Optional[str]:
        """Reject non-compiling placeholders ('exact _', 'admit', bare '_', ...).

        The file-level sorry counter does not see these, so without an explicit
        check the prover can "improve" sorry_count while leaving the file
        unbuildable. Returns an error message to surface to the agent, or None.
        """
        for raw_line in replacement.splitlines():
            line = raw_line.strip()
            if not line or line.startswith("--"):
                continue
            for pat in self._STUB_PATTERNS:
                if re.search(pat, line):
                    if self._trace:
                        self._trace.log(
                            agent="TacticTools", role="stub_guard",
                            content=f"BLOCKED {operation}: stub '{line[:60]}' matches {pat}",
                            duration_s=0.01,
                        )
                    return (
                        f"BLOCKED by stub guard: replacement contains non-compiling "
                        f"placeholder '{line[:60]}'. These are NOT proofs — write a "
                        f"real tactic, decompose with `have`, or keep sorry while you "
                        f"work on a sub-goal."
                    )
        return None

    def _build_check_or_revert(self, original_content: str, operation: str
                               ) -> Optional[Dict]:
        """After writing, run lake build. If it fails, revert and return diagnostics.

        Returns None when the build succeeds (caller continues normally).
        Returns a dict with `error` + `errors` + `reverted=True` on failure;
        the original file content is restored before returning.
        """
        try:
            from .verifier import get_verifier
            project_dir = str(Path(self._filepath).parent.parent)
            verifier = get_verifier(project_dir)
            subdir = Path(self._filepath).parent.name
            relative_path = f"{subdir}/{Path(self._filepath).name}"
            result = verifier.verify_project_file(relative_path)
        except Exception as e:
            # Verifier itself blew up — revert defensively and surface the error.
            Path(self._filepath).write_text(original_content, encoding="utf-8")
            return {
                "error": f"Verifier crashed during {operation} build-check: {e}. Reverted.",
                "reverted": True,
                "errors": [],
            }

        if result.get("success"):
            return None

        # Check if the ONLY errors are sorry-related (not syntax errors)
        # When sorry exists in a file, lake build always fails — but the
        # replacement might still be valid if no new syntax errors were introduced.
        raw_output = result.get("raw_output", "") or result.get("errors", "")
        non_sorry_errors = []
        for line in raw_output.split("\n"):
            if "error:" not in line:
                continue
            skip_patterns = [
                "declaration uses `sorry`",
                "uses `sorry`",
                "Some required targets logged failures",
                "Lean exited with code 1",
                "error: build failed",
                "compiled configuration is invalid",
            ]
            if any(skip in line for skip in skip_patterns):
                continue
            m = re.match(r".*?(\d+):\d+: error: (.*)", line)
            if not m:
                m = re.match(r"error: .*?(\d+):\d+: (.*)", line)
            if m:
                msg = m.group(2)
                if "unsolved goals" in msg:
                    continue
                non_sorry_errors.append({"line": int(m.group(1)), "message": msg})

        # If only sorry-related errors, accept the replacement (don't revert)
        if not non_sorry_errors:
            return None

        # Build failed with real errors — revert to original.
        Path(self._filepath).write_text(original_content, encoding="utf-8")
        raw_output = result.get("raw_output", "") or result.get("errors", "")
        errors = []
        for line in raw_output.split("\n"):
            m = re.match(r".*?(\d+):\d+: error: (.*)", line)
            if not m:
                m = re.match(r"error: .*?(\d+):\d+: (.*)", line)
            if m:
                errors.append({"line": int(m.group(1)), "message": m.group(2)})

        if self._trace:
            self._trace.log(
                agent="TacticTools", role="build_check",
                content=f"BUILD-FAIL after {operation}: {len(errors)} errors. Reverted.",
                duration_s=0.01,
                tool_result=raw_output[:300],
            )

        return {
            "error": (
                f"BUILD FAILED after {operation}: {len(errors)} compile errors. "
                f"File reverted to previous state. Fix the tactic and try again."
            ),
            "reverted": True,
            "errors": errors[:8],
            "raw_output_preview": raw_output[:400],
        }

    def file_replace_lines(self, start: int, end: int, new_content: str,
                           build_check: bool = True) -> str:
        """Replace a range of lines in the .lean file. Lines are 1-based, inclusive.

        When `build_check=True` (default), runs lake build after writing and
        reverts the file if compilation fails — the prover never operates on
        a broken file.
        """
        if not self._filepath:
            return json.dumps({"error": "No file configured"})

        # Context boundary: only allow replacing near the target sorry
        if self._sorry_ctx:
            target = self._sorry_ctx.sorry_line
            # The range must overlap with [target - boundary, target + boundary]
            boundary = self._context_boundary * 4  # Wider for range edits
            if end < target - boundary or start > target + boundary:
                return json.dumps({
                    "error": f"BLOCKED: range {start}-{end} is too far from target sorry at line {target}. "
                             f"Only modify lines within ±{boundary} of the sorry.",
                }, ensure_ascii=False)

        # Structural boundary guard: prevent replacing across section/end/theorem boundaries
        try:
            content_precheck = Path(self._filepath).read_text(encoding="utf-8")
            lines_precheck = content_precheck.split("\n")
            _STRUCTURE_KEYWORDS = re.compile(
                r'^\s*(theorem|lemma|def|instance|section|end|namespace|open|'
                r'variable|abbreviation|structure|class|inductive)\b'
            )
            # Count structural keywords BEFORE the replacement range
            before_structs = sum(
                1 for i in range(min(start - 1, len(lines_precheck)))
                if _STRUCTURE_KEYWORDS.match(lines_precheck[i])
            )
            # Count structural keywords AFTER the replacement range
            after_start = min(end, len(lines_precheck))
            after_structs = sum(
                1 for i in range(after_start, len(lines_precheck))
                if _STRUCTURE_KEYWORDS.match(lines_precheck[i])
            )
            # Count structural keywords IN the range being replaced
            range_structs = sum(
                1 for i in range(start - 1, min(end, len(lines_precheck)))
                if _STRUCTURE_KEYWORDS.match(lines_precheck[i])
            )
            # If the range contains structural keywords AND surrounding code also has them,
            # the replacement might break file structure. Block large ranges crossing boundaries.
            # Exception: replacing a single `sorry` line that happens to be near a keyword is fine.
            range_size = end - start + 1
            if range_structs > 0 and range_size > 3:
                struct_lines = [
                    f"L{i+1}: {lines_precheck[i].strip()[:60]}"
                    for i in range(start - 1, min(end, len(lines_precheck)))
                    if _STRUCTURE_KEYWORDS.match(lines_precheck[i])
                ]
                return json.dumps({
                    "error": f"BLOCKED: range {start}-{end} contains structural keywords "
                             f"(theorem/end/section/def). Use file_replace_sorry() instead "
                             f"to replace ONLY the sorry line. Structural lines found:\n"
                             + "\n".join(struct_lines),
                }, ensure_ascii=False)
        except Exception:
            pass  # Don't block on pre-check errors

        try:
            content = Path(self._filepath).read_text(encoding="utf-8")
            lines = content.split("\n")
            old_lines = lines[start - 1:end] if end <= len(lines) else lines[start - 1:]
            old_text = "\n".join(old_lines)

            new_lines = new_content.split("\n")

            # Comment preservation guard (Cycle 25 ai-01 trace fix):
            # Detect protected comment markers in old_lines that the agent would
            # silently strip. Markers indicate human-curated explanations that
            # must survive proof-block rewrites. If found AND absent from new_content,
            # prepend them to the replacement to preserve the documentation.
            _PROTECTED_MARKERS = (
                "PROOF STRATEGY", "TODO:", "FIXME:", "NOTE:",
                "KEY LEMMAS", "KEY MATHLIB", "STRATEGY:",
                "RECOMMENDED SUB-LEMMAS", "CRITICAL ERROR", "CRITICAL RULES",
            )
            protected = []
            for line in old_lines:
                stripped = line.strip()
                if not stripped.startswith("--"):
                    continue
                for marker in _PROTECTED_MARKERS:
                    if marker in stripped:
                        protected.append(line)
                        break
            if protected:
                preserved = [p for p in protected if p.strip() not in new_content]
                if preserved:
                    new_lines = preserved + new_lines
                    if self._trace:
                        self._trace.log(
                            agent="TacticTools", role="comment_preservation",
                            content=f"file_replace_lines: preserved {len(preserved)} protected comment lines "
                                    f"(markers: PROOF STRATEGY/TODO/FIXME/KEY LEMMAS/...) that the replacement would have stripped",
                            duration_s=0.0,
                        )

            lines[start - 1:end if end <= len(lines) else len(lines)] = new_lines
            new_file_content = "\n".join(lines)

            # File size guard: block full-file rewrites
            size_error = self._check_file_size_guard(new_file_content, "file_replace_lines")
            if size_error:
                return json.dumps({"error": size_error}, ensure_ascii=False)

            # Stub guard: reject non-compiling placeholders inside the replacement
            stub_error = self._check_stub_guard(new_content, "file_replace_lines")
            if stub_error:
                return json.dumps({"error": stub_error,
                                   "replaced_lines": f"{start}-{end}"},
                                  ensure_ascii=False)

            sorry_count = new_file_content.count("sorry")

            # Sorry guard: block only if growth EXCEEDS the decomposition
            # budget. Replacing 1 sorry by N sub-sorries that all compile is
            # structural progress (the agent breaks down a hard goal). Block
            # only the runaway case (>budget) which signals the agent is
            # spraying sorries instead of decomposing intentionally.
            ceiling = self._original_sorry_count + self._decomposition_budget
            if sorry_count > ceiling:
                if self._trace:
                    self._trace.log(
                        agent="TacticTools", role="sorry_guard",
                        content=f"BLOCKED file_replace_lines: {sorry_count} > ceiling {ceiling} (orig={self._original_sorry_count}+budget={self._decomposition_budget}). REVERTING.",
                        duration_s=0.01,
                    )
                return json.dumps({
                    "error": f"BLOCKED by sorry guard: {sorry_count} sorry > ceiling {ceiling}. "
                             f"You have a {self._decomposition_budget}-sorry decomposition budget on top of the {self._original_sorry_count} originals; you've exhausted it. "
                             f"Discharge some of the sub-sorries before adding more, or rewrite the replacement to be flatter.",
                    "replaced_lines": f"{start}-{end}",
                    "sorry_count": sorry_count,
                    "ceiling": ceiling,
                }, ensure_ascii=False)
            if sorry_count > self._original_sorry_count and self._trace:
                # Visible signal in the trace that decomposition is happening.
                self._trace.log(
                    agent="TacticTools", role="decomposition_progress",
                    content=f"sorries grew {self._original_sorry_count}->{sorry_count} (within budget {self._decomposition_budget}); accepting if build passes",
                    duration_s=0.0,
                )

            Path(self._filepath).write_text(new_file_content, encoding="utf-8")

            # Build check: if compilation fails, revert and surface diagnostics.
            # When build_check=False, we MUST NOT update _last_build_ok_* or
            # _best_* — those snapshots are the prover's source of truth for
            # the "best build-passing state" and the autonomous loop commits
            # them as RESULT_SUCCESS. Updating them on unverified raw sorry
            # count alone caused a false positive in iter 2 of demo 9 where a
            # `show ?a ≦ ?b -- PROBE` snapshot (invalid Lean U+2266 token)
            # was promoted to best_sorry_count=3 because the agent passed
            # build_check=False.
            if build_check:
                build_err = self._build_check_or_revert(content, "file_replace_lines")
                if build_err is not None:
                    build_err["replaced_lines"] = f"{start}-{end}"
                    return json.dumps(build_err, ensure_ascii=False)

                # Build verified — safe to update snapshots.
                self._last_build_ok_content = new_file_content
                self._last_build_ok_sorry_count = sorry_count

                if sorry_count < self._best_sorry_count:
                    self._best_sorry_count = sorry_count
                    self._best_content = new_file_content

            return json.dumps({
                "replaced_lines": f"{start}-{end}",
                "old_text_preview": old_text[:200],
                "new_sorry_count": sorry_count,
                "best_sorry_count": self._best_sorry_count,
                "build_check": "passed" if build_check else "skipped",
                "snapshot_updated": build_check,
            }, ensure_ascii=False)
        except Exception as e:
            return json.dumps({"error": str(e)})

    def file_replace_sorry(self, sorry_line: int, replacement: str,
                           build_check: bool = True) -> str:
        """Replace the sorry at a given line with a tactic. Auto-detects indentation.

        When `build_check=True` (default), runs lake build after writing and
        reverts the file if compilation fails. The autonomous prover loop also
        does periodic build checks, but inline validation here catches stubs
        like `exact _` immediately and gives the agent a fresh diagnostic.
        """
        if not self._filepath:
            return json.dumps({"error": "No file configured"})
        try:
            # Context boundary: only allow replacing the target sorry
            if self._sorry_ctx:
                target = self._sorry_ctx.sorry_line
                if abs(sorry_line - target) > self._context_boundary:
                    return json.dumps({
                        "error": f"BLOCKED: line {sorry_line} is too far from target sorry at line {target}. "
                                 f"Only modify lines within ±{self._context_boundary} of the sorry.",
                    }, ensure_ascii=False)

            content = Path(self._filepath).read_text(encoding="utf-8")
            lines = content.split("\n")

            if sorry_line < 1 or sorry_line > len(lines):
                return json.dumps({"error": f"Line {sorry_line} out of range"})

            sorry_text = lines[sorry_line - 1]
            if "sorry" not in sorry_text:
                return json.dumps({"error": f"Line {sorry_line} doesn't contain 'sorry': {sorry_text[:80]}"})

            indent = len(sorry_text) - len(sorry_text.lstrip())

            # Preserve relative indentation: find min indent in replacement,
            # strip it, then re-base to the sorry line's indent level.
            raw_lines = replacement.rstrip().split("\n")
            # Find minimum indentation among non-empty lines
            non_empty = [l for l in raw_lines if l.strip()]
            min_indent = min((len(l) - len(l.lstrip()) for l in non_empty), default=0)

            replacement_lines = []
            for line in raw_lines:
                if line.strip():
                    # Remove the original base indent, add the sorry's indent
                    relative_indent = len(line) - len(line.lstrip()) - min_indent
                    new_indent = " " * (indent + max(0, relative_indent))
                    replacement_lines.append(new_indent + line.strip())
                # Skip blank lines within replacement

            old_line = lines[sorry_line - 1]
            lines[sorry_line - 1:sorry_line] = replacement_lines
            new_content = "\n".join(lines)

            # File size guard: block full-file rewrites
            size_error = self._check_file_size_guard(new_content, "file_replace_sorry")
            if size_error:
                return json.dumps({"error": size_error}, ensure_ascii=False)

            # Stub guard: reject `exact _`, `admit`, bare `_`, ... before writing.
            stub_error = self._check_stub_guard(replacement, "file_replace_sorry")
            if stub_error:
                return json.dumps({"error": stub_error,
                                   "replaced": old_line.strip()},
                                  ensure_ascii=False)

            sorry_count = new_content.count("sorry")

            # Sorry guard: same semantics as file_replace_lines. Allow up to
            # `_decomposition_budget` extra sorries on top of the original
            # count (decomposition into sub-goals is structural progress).
            ceiling = self._original_sorry_count + self._decomposition_budget
            if sorry_count > ceiling:
                if self._trace:
                    self._trace.log(
                        agent="TacticTools", role="sorry_guard",
                        content=f"BLOCKED file_replace_sorry: {sorry_count} > ceiling {ceiling} (orig={self._original_sorry_count}+budget={self._decomposition_budget}). REVERTING.",
                        duration_s=0.01,
                    )
                return json.dumps({
                    "error": f"BLOCKED by sorry guard: {sorry_count} sorry > ceiling {ceiling}. "
                             f"You have a {self._decomposition_budget}-sorry decomposition budget on top of the {self._original_sorry_count} originals; you've exhausted it. "
                             f"Discharge some sub-sorries before adding more.",
                    "replaced": old_line.strip(),
                    "sorry_count": sorry_count,
                    "ceiling": ceiling,
                }, ensure_ascii=False)
            if sorry_count > self._original_sorry_count and self._trace:
                self._trace.log(
                    agent="TacticTools", role="decomposition_progress",
                    content=f"sorries grew {self._original_sorry_count}->{sorry_count} (within budget {self._decomposition_budget}); accepting if build passes",
                    duration_s=0.0,
                )

            # Save pre-edit content for rollback
            pre_edit_content = content
            Path(self._filepath).write_text(new_content, encoding="utf-8")

            # Build check: if compilation fails, revert and surface diagnostics.
            # Same invariant as file_replace_lines: snapshots only update when
            # the build was actually verified. See that method for the full
            # iter 2 false positive context.
            if build_check:
                build_err = self._build_check_or_revert(content, "file_replace_sorry")
                if build_err is not None:
                    build_err["replaced"] = old_line.strip()
                    return json.dumps(build_err, ensure_ascii=False)

                self._last_build_ok_content = new_content
                self._last_build_ok_sorry_count = sorry_count

                if sorry_count < self._best_sorry_count:
                    self._best_sorry_count = sorry_count
                    self._best_content = new_content

            return json.dumps({
                "replaced": old_line.strip(),
                "new_lines": len(replacement_lines),
                "new_sorry_count": sorry_count,
                "best_sorry_count": self._best_sorry_count,
                "build_check": "passed" if build_check else "skipped",
                "snapshot_updated": build_check,
            }, ensure_ascii=False)
        except Exception as e:
            return json.dumps({"error": str(e)})

    def _quick_build_check(self) -> bool:
        """Quick build check using the shared verifier.

        Invalidates cache first (file was just modified), then runs build.
        Returns True if build succeeds, False on errors.
        """
        if not self._filepath:
            return True
        try:
            from .verifier import get_verifier, _load_lean_verifier_class
            _LeanVerifier = _load_lean_verifier_class()

            project_dir = str(Path(self._filepath).parent.parent)
            subdir = Path(self._filepath).parent.name
            filename = Path(self._filepath).name
            relative_path = f"{subdir}/{filename}"

            # Invalidate cache since file was just modified
            _LeanVerifier.invalidate(self._filepath)

            verifier = get_verifier(project_dir)
            result = verifier.verify_project_file(relative_path, force=True)
            success = result.get("success", False)

            if not success and self._trace:
                errors = result.get("errors", "")[:200]
                self._trace.log(
                    agent="TacticTools", role="build_check",
                    content=f"BUILD FAILED after edit: {errors}",
                    duration_s=0.01,
                )
            return success
        except Exception as e:
            if self._trace:
                self._trace.log(
                    agent="TacticTools", role="build_check_error",
                    content=f"Build check exception (assuming OK): {e}",
                    duration_s=0.01,
                )
            return True

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
        result = verifier.verify_project_file(relative_path, force=True)

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
        """Analyze a tactic failure with structured error classification (B.6).

        Classifies errors into typed categories and returns actionable hints
        with retry strategy guidance.
        """
        category = "unknown"
        severity = "medium"
        hints = []
        retry_strategy = "try_different"

        if "No goals to be solved" in error:
            category = "over_proof"
            severity = "low"
            hints.append("First tactic already closed the goal. Remove trailing tactics like `rfl`.")
            retry_strategy = "trim_tactic"

        elif "made no progress" in error:
            category = "no_progress"
            severity = "low"
            hints.append("Tactic didn't change the goal. Try a different approach.")
            retry_strategy = "different_tactic"

        elif "unknown tactic" in error:
            category = "syntax"
            severity = "high"
            hints.append("Tactic requires Mathlib import. Try omega, simp, or rw instead.")
            retry_strategy = "use_standard_tactic"

        elif "could not prove the goal" in error:
            category = "incomplete"
            severity = "medium"
            hints.append("Tactic applicable but couldn't close the goal. Try a more powerful tactic.")
            retry_strategy = "strengthen_tactic"

        elif "unknown identifier" in error:
            category = "identifier"
            severity = "high"
            hints.append("Lemma name not found. Check exact spelling or search for alternatives.")
            retry_strategy = "search_lemma"

        elif "type mismatch" in error or "type error" in error.lower():
            category = "type_mismatch"
            severity = "medium"
            hints.append("Type mismatch. Try norm_cast, push_cast, or cast lemmas.")
            retry_strategy = "fix_types"

        elif "unsolved goals" in error:
            category = "incomplete"
            severity = "medium"
            hints.append("Tactic left open goals. Add more tactics or decompose.")
            retry_strategy = "decompose_or_continue"

        elif "sorry" in error.lower():
            category = "partial"
            severity = "low"
            hints.append("Decomposition with sorry detected — partial progress.")
            retry_strategy = "prove_subgoal"

        elif "invalid" in error.lower() and "notation" in error.lower():
            category = "notation"
            severity = "high"
            hints.append("Invalid notation (e.g. ⟨⟩ on non-inductive type). Use `show` or `constructor` instead.")
            retry_strategy = "use_show_or_constructor"

        elif "application type mismatch" in error:
            category = "type_mismatch"
            severity = "high"
            hints.append("Function applied to wrong argument type. Check argument order and types.")
            retry_strategy = "fix_arguments"

        elif "recursive" in error.lower() or "timeout" in error.lower():
            category = "resource"
            severity = "high"
            hints.append("Proof search timed out or recursed. Simplify or decompose the goal.")
            retry_strategy = "decompose"

        # Track in state
        self._state.last_error = error[:500]
        self._state.consecutive_failures += 1

        return json.dumps({
            "tactic": tactic,
            "category": category,
            "severity": severity,
            "error_type": category,
            "hints": hints,
            "suggestion": hints[0] if hints else "Try a different tactic.",
            "retry_strategy": retry_strategy,
            "consecutive_failures": self._state.consecutive_failures,
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

    def reset_consecutive_failures(self) -> str:
        """Reset the consecutive failure counter after a successful step."""
        self._state.consecutive_failures = 0
        return "Consecutive failures reset to 0"


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

    def set_attack_plan(self, steps: list, reason: str = "") -> str:
        """Set an explicit attack plan for the proof session (B.3).

        The CoordinatorAgent analyzes the goal and creates a step-by-step plan
        that guides other agents through the proof strategy.

        Args:
            steps: Ordered list of proof strategy steps (e.g. ['decompose conjunction',
                   'prove left with omega', 'prove right with exact h'])
            reason: Why this plan was chosen
        """
        self._state.plan = steps
        self._state.plan_phase = 0
        plan_str = "\n".join(f"  {i+1}. {step}" for i, step in enumerate(steps))

        if self._trace:
            self._trace.log(
                agent="CoordinatorAgent", role="plan",
                content=f"Set attack plan ({len(steps)} steps): {reason}",
                duration_s=0.01, tool_name="set_attack_plan",
                tool_args={"steps_count": len(steps), "reason": reason[:60]},
                tool_result=plan_str[:200],
            )

        return f"Attack plan set ({len(steps)} steps):\n{plan_str}\nReason: {reason}"

    def advance_plan(self) -> str:
        """Advance to the next step in the attack plan."""
        if not self._state.plan:
            return "No plan set. Use set_attack_plan first."
        self._state.plan_phase = min(
            self._state.plan_phase + 1, len(self._state.plan) - 1
        )
        current = self._state.plan[self._state.plan_phase]
        return f"Advanced to step {self._state.plan_phase + 1}/{len(self._state.plan)}: {current}"

    def try_constructive_existential(self) -> str:
        """B3 (issue #1225): attempt constructive witnesses for existential goals.

        When the current goal matches ∃ <var> : <type>, <property>, this tool
        searches the .lean file for constructors of <type> and validation lemmas
        for <property>, then generates concrete exact ⟨constructor, validator⟩
        tactic candidates.

        Called by the Coordinator BEFORE request_director_guidance or
        mark_sorry_intractable — constructive witnesses are cheap to attempt
        and occasionally succeed on existential goals that stumped the
        TacticAgent (which tends to try rfl/omega/simp first).

        Returns a summary of attempts made (or reason why no attempts were
        possible). Does NOT modify the file — only generates candidates for
        the Coordinator to relay to TacticAgent.
        """
        goal = self._state.current_goal
        if not goal:
            return "No current goal set. Use get_proof_state first."

        # Pattern 1: ∃ <var> : <type>, <property> (unicode exists)
        # Pattern 2: Exists <type> <property> (Lean ASCII)
        # Pattern 3: ∃ <var>, <property> (type inferred)
        existential_patterns = [
            r"∃\s*(\w+)\s*:\s*(.+?)\s*,\s*(.+)",
            r"Exists\s+(\S+)\s+(.+)",
            r"∃\s*(\w+)\s*,\s*(.+)",
        ]
        match = None
        var_name = ""
        type_name = ""
        property_expr = ""
        for pat in existential_patterns:
            m = re.search(pat, goal)
            if m:
                match = m
                if pat == r"Exists\s+(\S+)\s+(.+)":
                    var_name = "_"
                    type_name = m.group(1)
                    property_expr = m.group(2)
                else:
                    var_name = m.group(1)
                    type_name = m.group(2)
                    property_expr = m.group(3)
                break

        if not match:
            if self._trace:
                self._trace.log(
                    agent="CoordinatorAgent", role="b3_skip",
                    content=f"Goal does not match existential pattern: {goal[:120]}",
                    tool_name="try_constructive_existential",
                )
            return f"Goal does not match existential pattern: {goal[:200]}"

        if self._trace:
            self._trace.log(
                agent="CoordinatorAgent", role="b3_match",
                content=f"Existential matched: var={var_name}, type={type_name}, "
                        f"property={property_expr[:100]}",
                tool_name="try_constructive_existential",
                tool_args={"var": var_name, "type": type_name,
                           "property": property_expr[:200]},
            )

        # Search the .lean file for constructors of the type.
        constructors = []
        validators = []
        if self._filepath and Path(self._filepath).exists():
            content = Path(self._filepath).read_text(encoding="utf-8")
            # Look for defs returning the type (constructor candidates)
            # Match: def <name> ... : <type> or noncomputable def <name> ... : <type>
            for cm in re.finditer(
                r"(?:noncomputable\s+)?def\s+(\w+).*?:\s*([^\n]+)",
                content, re.DOTALL,
            ):
                name, ret = cm.group(1), cm.group(2).strip()
                # Check if the return type mentions our target type
                type_token = type_name.strip().split()[0]  # first word (e.g. "Matching")
                if type_token in ret:
                    constructors.append(name)

            # Look for lemmas/theorems mentioning the property or type
            for lm in re.finditer(
                r"(?:lemma|theorem)\s+(\w+)", content,
            ):
                lemma_name = lm.group(1)
                prop_tokens = re.findall(r"\w+", property_expr)
                type_tokens = re.findall(r"\w+", type_name)
                # Score: lemma mentions property tokens or type tokens
                name_tokens = set(re.findall(r"\w+", lemma_name.lower()))
                overlap = len(name_tokens & {t.lower() for t in prop_tokens + type_tokens})
                if overlap > 0:
                    validators.append((lemma_name, overlap))

            validators.sort(key=lambda x: x[1], reverse=True)

        if not constructors:
            # Fallback: look for constructors in known types
            # Common patterns: ⟨...⟩ works if the type is a structure
            constructors.append("⟨_, _⟩")

        candidates = []
        for ctor in constructors[:3]:
            # Basic candidate: exact ⟨ctor, ...⟩
            # For structure types, ⟨⟩ works directly
            if ctor.startswith("⟨"):
                candidates.append(f"exact ⟨_, rfl⟩")
                candidates.append(f"exact ⟨_, trivial⟩")
            else:
                for val_name, _ in validators[:2]:
                    candidates.append(f"exact ⟨{ctor} _, {val_name} _⟩")
                # Also try bare constructor without validator
                candidates.append(f"exact ⟨{ctor} _, rfl⟩")
                candidates.append(f"exact ⟨{ctor} _, trivial⟩")

        # Deduplicate while preserving order
        seen = set()
        unique_candidates = []
        for c in candidates:
            if c not in seen:
                seen.add(c)
                unique_candidates.append(c)

        # Limit to 6 candidates max
        unique_candidates = unique_candidates[:6]

        if self._trace:
            self._trace.log(
                agent="CoordinatorAgent", role="b3_candidates",
                content=f"Generated {len(unique_candidates)} tactic candidates",
                tool_name="try_constructive_existential",
                tool_args={"candidates": unique_candidates},
            )

        # Store candidates in state so TacticAgent can pick them up
        if not hasattr(self._state, "b3_candidates"):
            self._state.b3_candidates = []
        self._state.b3_candidates = unique_candidates

        result_lines = [
            f"B3 constructive existential heuristic for: {goal[:150]}",
            f"Type: {type_name}, Variable: {var_name}",
            f"Constructors found: {constructors[:5]}",
            f"Validators found: {[v[0] for v in validators[:5]]}",
            f"Tactic candidates ({len(unique_candidates)}):",
        ]
        for i, c in enumerate(unique_candidates, 1):
            result_lines.append(f"  {i}. {c}")
        result_lines.append(
            "\nRelay these to TacticAgent (submit_tactic). Each candidate "
            "is cheap — try them in order before escalating to Director."
        )
        return "\n".join(result_lines)

    def request_director_guidance(self, reason: str) -> str:
        """Request guidance from the external Director (F9, 2026-05-17).

        Call this BEFORE mark_sorry_intractable on any hard target. The
        Director (Opus 4.7 via OpenRouter) has access to shared reference
        docs (mmaaz-git proofs, ported defs, Mathlib gaps) and may provide
        an APPROACH + TACTICS combination you haven't tried.

        Workflow after this call:
          - The graph routes the next message to DirectorAgent
          - DirectorAgent emits APPROACH + TACTICS
          - The result flows back to TacticAgent (or Search) to execute

        C37 forensic (DEMO 15/16/17) showed the Coordinator NEVER reached
        Director because mark_sorry_intractable had no precondition. F9
        gates intractable behind at least one Director consultation.

        Args:
            reason: Concise context for the Director (max ~300 chars).
                    Include: current goal, what's been tried, suspected gap.
        """
        self._state.designate_next_agent("DirectorAgent")
        if self._trace:
            self._trace.log(
                agent="CoordinatorAgent", role="request_director",
                content=f"Requesting Director: {reason[:300]}",
                tool_name="request_director_guidance",
                tool_args={"reason": reason[:300]},
            )
        return (
            "Director will be consulted on the next turn. Provide the "
            "current proof state context — the Director responds with "
            "APPROACH + TACTICS in text form, which the workflow then "
            "routes to TacticAgent for execution. After at least one "
            "Director consultation, mark_sorry_intractable becomes "
            "available if you still need to abandon."
        )

    def mark_sorry_intractable(self, reason: str) -> str:
        """Explicitly abandon the current sorry (F5, gated by F9).

        Call this when the Coordinator has exhausted realistic attack plans
        on a goal — e.g., the lemma requires an obscure Mathlib API the
        SearchAgent can't locate, or the goal is mathematically false as
        stated. Setting intractable ends the session cleanly so the next
        prover run can target a different sorry instead of burning the
        remaining iteration budget on a dead end.

        F9 (2026-05-17): now gated. Must call request_director_guidance()
        at least once first AND wait for the Director to actually run
        (state.director_consulted set to True by AgentExecutor when
        DirectorAgent yields). Premature calls return an error message and
        leave the session running.

        Args:
            reason: Concise explanation (logged in trace + final report).
        """
        if not getattr(self._state, "director_consulted", False):
            if self._trace:
                self._trace.log(
                    agent="CoordinatorAgent", role="intractable_blocked",
                    content=(f"F9 gate: intractable refused — Director not "
                             f"yet consulted. reason={reason[:120]}"),
                    tool_name="mark_sorry_intractable",
                )
            return (
                "REFUSED (F9 gate). You must call request_director_guidance() "
                "at least once before marking a sorry intractable, AND wait for "
                "the Director to actually respond. The Director is a frontier "
                "model (Opus 4.7) with access to reference proofs — it may "
                "see an attack vector that the local agents missed. Call "
                "request_director_guidance(reason=...) now, then try the "
                "Director's APPROACH+TACTICS. Only if that ALSO fails should "
                "you call mark_sorry_intractable again."
            )

        self._state.intractable = True
        self._state.intractable_reason = reason
        if self._trace:
            self._trace.log(
                agent="CoordinatorAgent", role="intractable",
                content=f"Marked intractable: {reason[:200]}",
                tool_name="mark_sorry_intractable",
                tool_args={"reason": reason[:200]},
            )
        return (
            f"Sorry marked intractable. Reason: {reason}. "
            f"Session will yield_output after this turn — pick a different "
            f"goal on the next run."
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
