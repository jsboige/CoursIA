"""Configuration, providers, and demo theorems."""

import os
from pathlib import Path
from dotenv import load_dotenv
from agent_framework_openai import OpenAIChatCompletionClient

_parent = Path(__file__).resolve().parent.parent
_lean_dir = _parent.parent
load_dotenv(_lean_dir / ".env")
load_dotenv(_parent / ".env")

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

SOCIAL_CHOICE_DIR = Path(r"C:\dev\CoursIA\MyIA.AI.Notebooks\GameTheory\social_choice_lean")
VOTING_FILE = SOCIAL_CHOICE_DIR / "SocialChoice" / "Voting.lean" if SOCIAL_CHOICE_DIR.exists() else None
VOTING_IMPORTS = """import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Sort
import SocialChoice.Definitions
"""


def create_client(provider: str = "zai", model_key: str = "reasoning") -> OpenAIChatCompletionClient:
    """Create a ChatCompletionClient for the given provider."""
    cfg = PROVIDERS[provider]
    return OpenAIChatCompletionClient(
        model=cfg["models"][model_key],
        api_key=cfg["api_key"],
        base_url=cfg["base_url"],
    )


# ── Demo Theorems ──

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
    10: {
        "name": "VOTING_BANKS_SET_NONEMPTY",
        "file": str(VOTING_FILE),
        "line": 448,
        "sorry_type": "full_proof",
        "theorem_name": "banks_set_nonempty_of_tournament",
        "theorem": "banks_set_nonempty_of_tournament",
        "imports": VOTING_IMPORTS,
        "description": (
            "Prove banks_set_nonempty_of_tournament: when a tournament exists on S,\n"
            "the Banks set is nonempty.\n"
            "Goal: (banks_set prof S).Nonempty\n"
            "The Banks set collects endpoints of maximal chains in the tournament.\n"
            "Key: any maximal chain ending at the tournament winner gives a Banks winner.\n"
            "Available: is_tournament, banks_set, maximal_chain."
        ),
        "difficulty": "hard",
    },
    13: {
        "name": "VOTING_BANKS_SET_CONDORCET",
        "file": str(VOTING_FILE),
        "line": 437,
        "sorry_type": "full_proof",
        "theorem_name": "banks_set_condorcet",
        "theorem": "banks_set_condorcet",
        "imports": VOTING_IMPORTS,
        "description": (
            "Prove banks_set_condorcet: if x is a Condorcet winner in S,\n"
            "then x belongs to the Banks set.\n"
            "Goal: x ∈ banks_set prof S\n"
            "Strategy: unfold banks_set, show ∃ C, banks_chain prof S C ∧ C.Max x.\n"
            "The singleton chain {x} is a banks_chain when x is Condorcet winner\n"
            "(tournament means x beats everyone, so total order trivially satisfied).\n"
            "Then x is maximal in {x} trivially.\n"
            "Available: condorcet_winner, banks_set, banks_chain, is_tournament."
        ),
        "difficulty": "hard",
    },
    11: {
        "name": "VOTING_STV_NOT_MONOTONE",
        "file": str(VOTING_FILE),
        "line": 525,
        "sorry_type": "full_proof",
        "theorem_name": "stv_monotonicity_violation",
        "theorem": "stv_monotonicity_violation",
        "imports": VOTING_IMPORTS,
        "description": (
            "Prove STV fails monotonicity (Doron 1979): improving a candidate's\n"
            "position can paradoxically cause their elimination.\n"
            "Goal: ¬ @monotonicity ι σ _ _ (stv_scc n_seats)\n\n"
            "STRATEGY: negative result — construct explicit counterexample.\n"
            "Since ι and σ are variables, use `intro h_mono` then derive contradiction\n"
            "by constructing a specific Fin profile.\n\n"
            "CLASSIC COUNTEREXAMPLE (3 candidates, 1 seat):\n"
            "Candidates: {A, B, C}. Voters: 9 total.\n"
            "Profile P1: 4×[A>B>C], 3×[B>C>A], 2×[C>A>B]\n"
            "  - First prefs: A=4, B=3, C=2. Quota = 9/2+1 = 5\n"
            "  - Nobody reaches quota. Eliminate C (2 votes).\n"
            "  - C's votes transfer to A: A=6, B=3. A reaches quota. A wins.\n\n"
            "Profile P2 (A improved from C>A>B to A>C>B in last 2 ballots):\n"
            "  4×[A>B>C], 3×[B>C>A], 2×[A>C>B]\n"
            "  - First prefs: A=6, B=3, C=0. Quota = 5.\n"
            "  - A reaches quota immediately! A wins... BUT\n"
            "  Wait — this shows A still wins. Need different profile.\n\n"
            "ACTUAL DORON EXAMPLE needs careful surplus transfer:\n"
            "Use classical/decide tactics with Fin types.\n"
            "Approach: `intro h; exfalso; exact h <profile> <witness_pair>`\n"
            "The key insight: raising A gives A MORE first-preference votes,\n"
            "but the SURPLUS TRANSFER from A changes which candidate gets eliminated next.\n\n"
            "Available definitions: stv_scc, stv_step, droop_quota, first_preferences,\n"
            "stv_round_result, monotonicity (from Definitions.lean).\n"
            "NOTE: may need to unfold monotonicity to see exact goal structure."
        ),
        "difficulty": "very_hard",
    },
    12: {
        "name": "VOTING_STV_NOT_CLONE_INDEP",
        "file": str(VOTING_FILE),
        "line": 532,
        "sorry_type": "full_proof",
        "theorem_name": "stv_not_clone_independent",
        "theorem": "stv_not_clone_independent",
        "imports": VOTING_IMPORTS,
        "description": (
            "Prove STV does not satisfy clone independence:\n"
            "adding a clone of a candidate can change the outcome.\n"
            "Goal: ¬ @clone_independence ι σ _ _ _ (stv_scc n_seats)\n\n"
            "STRATEGY: negative result — construct explicit counterexample.\n"
            "clone_independence requires that adding a clone (candidate with identical\n"
            "preferences to existing one) doesn't change the relative ranking of\n"
            "non-cloned candidates in the outcome.\n\n"
            "COUNTEREXAMPLE IDEA (4 candidates, 1 seat):\n"
            "Original: {A, B, C}. Adding clone A' creates {A, A', B, C}.\n"
            "Without clone: B wins. With clone: A/A' votes split, changing elimination order.\n\n"
            "Approach: `intro h; exfalso; exact h <profile> <clone> <witness>`\n"
            "Need to compute stv_scc with and without the clone candidate.\n\n"
            "Available definitions: stv_scc, stv_step, droop_quota, first_preferences,\n"
            "clone_independence (from Definitions.lean).\n"
            "NOTE: may need to unfold clone_independence to see exact goal structure."
        ),
        "difficulty": "very_hard",
    },
}
