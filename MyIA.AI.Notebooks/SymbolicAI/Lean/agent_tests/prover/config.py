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
    "openrouter": {
        "base_url": os.getenv("OPENROUTER_BASE_URL", "https://openrouter.ai/api/v1"),
        "api_key": os.getenv("OPENROUTER_API_KEY", ""),
        "models": {
            "reasoning": os.getenv("OPENROUTER_CHAT_MODEL_ID",
                                   os.getenv("OPENAI_CHAT_MODEL_ID", "gpt-4o-mini")),
            "fast": os.getenv("OPENROUTER_FAST_MODEL_ID", "gpt-4o-mini"),
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
        "line": 251,
        "sorry_type": "sorry_replacement",
        "theorem_name": "median_voter_theorem",
        "theorem": "median_voter_theorem",
        "imports": VOTING_IMPORTS,
        "goal": "margin_pos prof (median_peak peaks) y",
        "description": "Prove the median peak beats all others. See DEMO 20 for strategy.",
        "proof_scaffolding": "intro y hy hne_y\nunfold margin_pos margin\nby_cases hlt : y < median_peak peaks\n",
        "difficulty": "very_hard",
    },
    10: {
        "name": "VOTING_BANKS_SET_NONEMPTY",
        "file": str(VOTING_FILE),
        "line": 455,
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
        "line": 445,
        "sorry_type": "full_proof",
        "theorem_name": "banks_set_condorcet",
        "theorem": "banks_set_condorcet",
        "imports": VOTING_IMPORTS,
        "goal": "∃ C, banks_chain prof S C ∧ x ∈ C ∧ ∀ y ∈ C, y ≠ x → margin_pos prof x y",
        "description": (
            "Prove banks_set_condorcet: if x is a Condorcet winner in S,\n"
            "then x belongs to the Banks set.\n"
            "The sorry is at L445 (single line). Replace it with a proof.\n"
            "\n"
            "STRATEGY: Pick a maximal pre-chain using Finset.exists_mem_eq_sup.\n"
            "1. Define isPC (pre-chain): subset of S with x, total+transitive, x beats all.\n"
            "2. Prove {x} isPC (vacuously true for total/trans on singleton).\n"
            "3. Use Finset.exists_mem_eq_sup on (S.powerset.filter isPC) with Finset.card\n"
            "   to get a maximum-cardinality pre-chain C.\n"
            "4. Prove C is a banks_chain (5 fields).\n"
            "5. Maximality: if y ∈ S\\C could be added, then insert y gives larger pre-chain.\n"
            "\n"
            "hw : condorcet_winner prof S x = ⟨x ∈ S, ∀ y ∈ S, y ≠ x → margin_pos prof x y⟩\n"
            "banks_chain prof S C = ⟨C ⊆ S, C.Nonempty, total_on C, trans_on C, maximal C⟩\n"
            "Finset.exists_mem_eq_sup : s.Nonempty → ∃ i ∈ s, s.sup f = f i\n"
            "Use `import Mathlib.Data.Finset.Powerset` for Finset.mem_powerset.\n"
            "\n"
            "IMPORTANT: Use file_replace_sorry(445, code) to replace ONLY the sorry line.\n"
            "The sorry is a SINGLE LINE at L445. Replace it with the full proof.\n"
            "DO NOT use file_replace_lines for the proof — it can corrupt surrounding code.\n"
            "Import Mathlib.Data.Finset.Powerset is already added.\n"
            "\n"
            "TACTICAL WARNINGS for maximality proof (field 5 of banks_chain):\n"
            "  The maximality goal is: ∀ y ∈ S, y ∉ C → ¬((tot_y) ∧ (trans_like_y))\n"
            "  After `intro y hyS hyC`, goal becomes ¬(A ∧ B).\n"
            "  Use `intro h` then `obtain ⟨hTot, hTrans⟩ := h` to get both hypotheses.\n"
            "  DO NOT use `push_neg` — it gives `A → ¬B`, not `A ∧ B`.\n"
            "  hTot : ∀ b ∈ C, margin_pos prof y b ∨ margin_pos prof b y\n"
            "  hTrans : ∀ b ∈ C, ∀ c ∈ C, margin_pos prof b c →\n"
            "    (margin_pos prof y b → margin_pos prof y c) ∧ (margin_pos prof c y → margin_pos prof b y)\n"
            "  When case-splitting on Finset.mem_insert: use `obtain h:y=a | h := h`\n"
            "  then `subst y` or `have : y = a := h_eq; subst y` — NOT rcases with rfl.\n"
        ),
        "proof_scaffolding": (
            "  -- Strategy: Good predicate + maximal chain + card contradiction\n"
            "  haveI : DecidableEq σ := Classical.decEq _\n"
            "  let isPC (C : Finset σ) : Prop :=\n"
            "    C ⊆ S ∧ x ∈ C ∧\n"
            "    (∀ a ∈ C, ∀ b ∈ C, a ≠ b → margin_pos prof a b ∨ margin_pos prof b a) ∧\n"
            "    (∀ a ∈ C, ∀ b ∈ C, ∀ c ∈ C,\n"
            "      margin_pos prof a b → margin_pos prof b c → margin_pos prof a c) ∧\n"
            "    ∀ y ∈ C, y ≠ x → margin_pos prof x y\n"
            "  have hPCx : isPC {x} := by\n"
            "    unfold isPC; refine ⟨Finset.singleton_subset_iff.mpr hw.1,\n"
            "      Finset.mem_singleton.mpr rfl, ?_, ?_, ?_⟩\n"
            "    · intro a ha b hb hab\n"
            "      rw [Finset.mem_singleton] at ha hb; subst a b; exact absurd rfl hab\n"
            "    · intro a ha b hb c hc hab hbc\n"
            "      rw [Finset.mem_singleton] at ha hb hc; subst a b c; exact hab\n"
            "    · intro y hy hne\n"
            "      rw [Finset.mem_singleton] at hy; subst y; exact (hne rfl).elim\n"
            "  have hNE : (S.powerset.filter isPC).Nonempty :=\n"
            "    ⟨{x}, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr\n"
            "      (Finset.singleton_subset_iff.mpr hw.1), hPCx⟩⟩\n"
            "  obtain ⟨C, hCmem, hCcard⟩ := Finset.exists_mem_eq_sup\n"
            "    (S.powerset.filter isPC) hNE Finset.card\n"
            "  simp only [Finset.mem_filter, Finset.mem_powerset] at hCmem\n"
            "  obtain ⟨hCsub, hCpc⟩ := hCmem\n"
            "  unfold isPC at hCpc\n"
            "  obtain ⟨_, hCx, hCtot, hCtrans, hCdom⟩ := hCpc\n"
            "  use C\n"
            "  refine ⟨⟨hCsub, ⟨x, hCx⟩, hCtot, hCtrans, ?_⟩, hCx, ?_⟩\n"
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
    20: {
        "name": "VOTING_MEDIAN_BEATS_ALL",
        "file": str(VOTING_FILE),
        "line": 251,
        "sorry_type": "sorry_replacement",
        "theorem_name": "median_voter_theorem",
        "theorem": "median_voter_theorem",
        "goal": "margin_pos prof (median_peak peaks) y",
        "imports": VOTING_IMPORTS,
        "description": (
            "Prove that the median peak beats every other alternative.\n"
            "The sorry is in the second branch of a constructor at line 251.\n"
            "\n"
            "!! CRITICAL: margin_pos_of_unanimous CANNOT be used here !!\n"
            "  That lemma requires ALL voters to prefer x to y.\n"
            "  The median voter theorem only guarantees a MAJORITY.\n"
            "  You MUST count voters using Finset.card and show > n/2.\n"
            "\n"
            "GOAL at sorry (after intro y hy hne_y):\n"
            "  margin_pos prof (median_peak peaks) y\n"
            "\n"
            "CONTEXT (all in scope):\n"
            "  prof : iota -> PrefOrder sigma, peaks : iota -> sigma\n"
            "  hsp : single_peaked_profile prof peaks\n"
            "  hodd : Odd (Fintype.card iota)\n"
            "  hcard_pos : 0 < Fintype.card iota\n"
            "  hne : Nonempty iota\n"
            "  [Inhabited sigma]\n"
            "  l : List sigma = sorted_peaks_list peaks\n"
            "  hl : l.length = Fintype.card iota\n"
            "  median_peak peaks = l.getD (l.length / 2) default\n"
            "\n"
            "single_peaked (prof i).rel (peaks i) has 3 components:\n"
            "  .1 (is_peak): forall x, x != peaks i -> P (prof i).rel (peaks i) x\n"
            "  .2.1 (left of peak): forall a b, a <= b -> b <= peaks i -> (prof i).rel b a\n"
            "  .2.2 (right of peak): forall a b, peaks i <= a -> a <= b -> (prof i).rel a b\n"
            "\n"
            "P R x y := R x y and not R y x (strict pref)\n"
            "margin prof x y = |{i : P (prof i).rel x y}| - |{i : P (prof i).rel y x}|\n"
            "margin_pos prof x y := 0 < margin prof x y\n"
            "\n"
            "PROOF STRATEGY (majority counting):\n"
            "  intro y hy hne_y\n"
            "  unfold margin_pos margin\n"
            "  by_cases hlt : y < median_peak peaks\n"
            "\n"
            "  Case 1 (y < median_peak):\n"
            "    For each voter i with peaks i >= median_peak:\n"
            "    - If peaks i = median_peak: (hsp i).1 gives is_peak, apply to y\n"
            "    - If peaks i > median_peak: y < median_peak < peaks i\n"
            "      Use (hsp i).2.1 y (median_peak peaks) (le_of_lt hlt)\n"
            "      This gives R (prof i) (median_peak) y (weak preference)\n"
            "      Also need NOT R (prof i) y (median_peak) for strict P.\n"
            "      By is_peak: P (prof i).rel (peaks i) (median_peak)\n"
            "      If R y median, then by transitivity R y (peaks i), contradiction.\n"
            "    Count: at least (n+1)/2 voters have peaks >= median\n"
            "    Since n is odd: (n+1)/2 > n/2\n"
            "\n"
            "  Case 2 (y > median_peak): symmetric\n"
            "    Voters with peaks i <= median_peak prefer median to y\n"
            "    using (hsp i).2.2 + is_peak\n"
            "\n"
            "CRITICAL RULES:\n"
            "  - ZERO sorry. Any sorry = FAILURE.\n"
            "  - DO NOT use margin_pos_of_unanimous (needs ALL voters).\n"
            "  - DO NOT use omega for counting Finset.card of filter.\n"
            "  - DO NOT call median_voter_theorem recursively.\n"
            "  - DO NOT use trace_state/show_plan/pretty (Lean 3 only).\n"
            "  - ALWAYS simp only [Finset.mem_filter, Finset.mem_univ, true_and]\n"
            "\n"
            "AVAILABLE:\n"
            "  Finset.filter, Finset.card, Finset.mem_filter, Finset.mem_univ\n"
            "  Finset.card_le_card, Finset.filter_subset, Finset.card_univ\n"
            "  Finset.card_filter_add_card_filter_eq_card\n"
            "  Nat.odd_iff, omega, classical, List.mergeSort, List.Perm\n"
        ),
        "proof_scaffolding": (
            "intro y hy hne_y\n"
            "unfold margin_pos margin\n"
            "by_cases hlt : y < median_peak peaks\n"
        ),
        "difficulty": "very_hard",
    },
    21: {
        "name": "VOTING_BANKS_SET_CONDORCET",
        "file": str(VOTING_FILE),
        "line": 445,
        "sorry_type": "sorry_replacement",
        "theorem_name": "banks_set_condorcet",
        "theorem": "banks_set_condorcet",
        "goal": "∃ C, banks_chain prof S C ∧ x ∈ C ∧ ∀ y ∈ C, y ≠ x → margin_pos prof x y",
        "imports": VOTING_IMPORTS,
        "description": (
            "Prove banks_set_condorcet: a Condorcet winner x is always in the Banks set.\n"
            "After `unfold banks_set banks_winner` and `simp only [Finset.mem_filter, hw.1, true_and]`,\n"
            "the sorry must show: ∃ C, banks_chain prof S C ∧ x ∈ C ∧ ∀ y ∈ C, y ≠ x → margin_pos prof x y\n"
            "\n"
            "CONTEXT at sorry:\n"
            "  prof : ι → PrefOrder σ\n"
            "  S : Finset σ\n"
            "  x : σ\n"
            "  hw : condorcet_winner prof S x\n"
            "  hw.1 : x ∈ S\n"
            "  hw.2 : ∀ y ∈ S, y ≠ x → margin_pos prof x y\n"
            "\n"
            "banks_chain prof S C expands to 5 conjunctions:\n"
            "  1) C ⊆ S\n"
            "  2) C.Nonempty\n"
            "  3) ∀ x ∈ C, ∀ y ∈ C, x ≠ y → margin_pos prof x y ∨ margin_pos prof y x\n"
            "  4) ∀ x ∈ C, ∀ y ∈ C, ∀ z ∈ C, margin_pos prof x y → margin_pos prof y z → margin_pos prof x z\n"
            "  5) ∀ a ∈ S, a ∉ C → ¬((∀ y ∈ C, margin_pos prof a y ∨ margin_pos prof y a) ∧\n"
            "       (∀ y ∈ C, ∀ z ∈ C, margin_pos prof y z →\n"
            "         (margin_pos prof a y → margin_pos prof a z) ∧ (margin_pos prof z a → margin_pos prof y a)))\n"
            "\n"
            "PROOF STRATEGY (Good predicate + maximal chain + card contradiction):\n"
            "  1) Define Good C := C ⊆ S ∧ x ∈ C ∧ (∀ y ∈ C, y ≠ x → margin_pos prof x y) ∧\n"
            "     (∀ y z ∈ C, y ≠ z → margin_pos prof y z ∨ margin_pos prof z y) ∧\n"
            "     (∀ y z w ∈ C, margin_pos prof y z → margin_pos prof z w → margin_pos prof y w)\n"
            "  2) Let Chains := S.powerset.filter Good. Prove {x} is Good (singleton).\n"
            "  3) Obtain maximal C ∈ Chains via Finset.exists_max_image.\n"
            "  4) Destructure Good C into hCS, hxC, htopC, htourC, htransC.\n"
            "  5) Provide C as witness. Prove banks_chain prof S C (5 fields).\n"
            "     For maximality (field 5): use contradiction.\n"
            "     Introduce a, haS, haNotC, hAdd (the negated conjunction).\n"
            "     Prove Good (insert a C) → insert a C ∈ Chains → card contradiction via omega.\n"
            "\n"
            "CRITICAL TACTICAL WARNINGS (from failed attempt):\n"
            "  - DO NOT use `rcases h with rfl | h2` on Finset.mem_insert hypotheses.\n"
            "    The rfl substitution shadows variables from outer scope, causing 'Unknown identifier'.\n"
            "    INSTEAD: use `obtain h:y | h := h_mem` then `· subst y; ... | · ...`\n"
            "    Or use `cases h_mem with | inl h => ... | inr h => ...` explicitly.\n"
            "  - DO NOT use `Finset.card_insert_of_not_mem` — may not exist in this Mathlib version.\n"
            "    INSTEAD: use `have : (insert a C).card = C.card + 1 := by\n"
            "      rw [Finset.card_insert_of_not_mem haNotC]` — if that fails, use\n"
            "      `Nat.add_left_cancel (Finset.card_insert_of_not_mem haNotC).symm` or\n"
            "      just `exact Finset.card_insert_of_not_mem haNotC` with omega.\n"
            "  - When proving Good (insert a C) fields, avoid deeply nested rcases.\n"
            "    Use `Finset.mem_insert` for case analysis: `obtain rfl | h := h_mem`.\n"
            "    But DO NOT use `rfl` pattern — use `obtain h_eq : _ | h := h_mem` then\n"
            "    `· have : y = a := h_eq; subst y; exact ...\n"
            "     · exact ...`\n"
            "  - Use `margin_self` for ∀ a, ¬margin_pos prof a a.\n"
            "  - Use `margin_antisymm` for ∀ a b, ¬(margin_pos prof a b ∧ margin_pos prof b a).\n"
            "\n"
            "AVAILABLE LEMMAS (from Voting.lean):\n"
            "  margin_self : ∀ prof x, ¬margin_pos prof x x\n"
            "  margin_antisymm : ∀ prof x y, margin prof x y + margin prof y x = 0\n"
            "  condorcet_winner : x ∈ S ∧ ∀ y ∈ S, y ≠ x → margin_pos prof x y\n"
            "\n"
            "DO NOT USE:\n"
            "  isPC (does NOT exist in codebase)\n"
            "  rcases h with rfl (causes variable shadowing in nested proofs)\n"
            "  Finset.card_insert_of_not_mem as a direct term (may not compile)\n"
            "  List.Sorted, List.mergeSort\n"
        ),
        "proof_scaffolding": (
            "-- Strategy: Good predicate + maximal chain via Finset.exists_max_image + card contradiction\n"
            "--\n"
            "-- Outline:\n"
            "-- 1. let Good := fun C => C ⊆ S ∧ x ∈ C ∧ (∀ y ∈ C, y ≠ x → margin_pos prof x y) ∧\n"
            "--      (∀ y z ∈ C, y ≠ z → margin_pos prof y z ∨ margin_pos prof z y) ∧\n"
            "--      (∀ y z w ∈ C, margin_pos prof y z → margin_pos prof z w → margin_pos prof y w)\n"
            "-- 2. let Chains := S.powerset.filter Good\n"
            "-- 3. have hsingleton : Good {x} (prove singleton is Good)\n"
            "-- 4. obtain ⟨C, hCmem, hCmax⟩ := Finset.exists_max_image Chains Finset.card ⟨{x}, by simp [Chains, hsingleton, hw.1]⟩\n"
            "-- 5. rcases Good_C into hCS, hxC, htopC, htourC, htransC\n"
            "-- 6. refine ⟨C, ?banks_chain, hxC, htopC⟩\n"
            "-- 7. Prove banks_chain: constructor for each field (subset, nonempty, total, trans, maximal)\n"
            "-- 8. For maximality: intro a haS haNotC hAdd, prove Good(insert a C), card contradiction\n"
            "--\n"
            "-- KEY: inside the maximality proof, when case-splitting on mem_insert,\n"
            "-- use `obtain h:y | h := h_mem` NOT `rcases h with rfl | h`\n"
            "-- Then use `subst y` or `have : y = a := h; subst y` to avoid variable shadowing\n"
        ),
        "difficulty": "hard",
    },
}
