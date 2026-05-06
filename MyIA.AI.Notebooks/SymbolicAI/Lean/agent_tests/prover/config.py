"""Configuration, providers, and demo theorems."""

import os
from pathlib import Path
from dotenv import load_dotenv
from agent_framework_openai import OpenAIChatClient

_parent = Path(__file__).resolve().parent.parent
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


def create_client(provider: str = "zai", model_key: str = "reasoning") -> OpenAIChatClient:
    """Create an OpenAIChatClient for the given provider."""
    cfg = PROVIDERS[provider]
    return OpenAIChatClient(
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
}
