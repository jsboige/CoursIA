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
        "line": 254,
        "sorry_type": "sorry_replacement",
        "theorem_name": "median_voter_theorem",
        "theorem": "median_voter_theorem",
        "imports": VOTING_IMPORTS,
        "goal": "0 < ({i | P (prof i).rel (median_peak peaks) (peaks j)}.card : Int) - ({i | P (prof i).rel (peaks j) (median_peak peaks)}.card : Int)",
        "description": (
            "Prove the margin is positive for median_peak vs peaks j.\n"
            "\n"
            "GOAL at sorry (EXACT):\n"
            "  0 < ({i | P (prof i).rel (median_peak peaks) (peaks j)}.card : Int)\n"
            "       - ({i | P (prof i).rel (peaks j) (median_peak peaks)}.card : Int)\n"
            "\n"
            "VARIABLES IN SCOPE:\n"
            "  prof : ι → PrefOrder σ, peaks : ι → σ\n"
            "  hsp : single_peaked_profile prof peaks\n"
            "  hstrict : ∀ i a b, a < b → b ≤ peaks i → P (prof i).rel b a\n"
            "    (voters with peak ≥ b prefer b over a when a < b)\n"
            "  hstrict' : ∀ i a b, peaks i ≤ a → a < b → P (prof i).rel a b\n"
            "    (voters with peak ≤ a prefer a over b when a < b)\n"
            "  hodd : Odd (Fintype.card ι)\n"
            "  hcard_pos : 0 < Fintype.card ι\n"
            "  j : ι\n"
            "  hny : ¬peaks j = median_peak peaks\n"
            "\n"
            "DEFINITIONS:\n"
            "  sorted_peaks_list peaks = (Finset.univ.toList.map peaks).mergeSort (· ≤ ·)\n"
            "  median_peak peaks = (sorted_peaks_list peaks).getD (s.length / 2) default\n"
            "  P R x y := R x y ∧ ¬R y x (strict preference from PrefOrder.rel)\n"
            "\n"
            "PROOF STRATEGY:\n"
            "  by_cases hlt : peaks j < median_peak peaks\n"
            "\n"
            "Case 1 (peaks j < median_peak peaks):\n"
            "  1. Have hgt_peaks : ∀ i, median_peak peaks ≤ peaks i → P (prof i).rel (median_peak peaks) (peaks j)\n"
            "     Proof: intro i hi; exact hstrict i (peaks j) (median_peak peaks) hlt hi\n"
            "  2. Define S_ge := Finset.filter (fun i => median_peak peaks ≤ peaks i) Finset.univ\n"
            "  3. Show S_ge ⊆ for_set: Finset.card_le_card (subset proof)\n"
            "  4. Show against_set ⊆ S_geᶜ: by contradiction using .2 of P\n"
            "  5. COUNTING: show Fintype.card ι / 2 < S_ge.card\n"
            "  6. Final arithmetic with omega\n"
            "\n"
            "Case 2 (peaks j > median_peak peaks): symmetric with hstrict'\n"
            "\n"
            "CRITICAL ERROR PATTERNS TO AVOID (from previous failed attempt):\n"
            "  1. When i ∈ Finset.filter (fun i => median_peak peaks ≤ peaks i) Finset.univ,\n"
            "     you CANNOT pass `hi` directly to hstrict. You MUST first:\n"
            "     simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi\n"
            "     to extract `hi : median_peak peaks ≤ peaks i` from the Finset membership.\n"
            "  2. omega CANNOT prove counting bounds over Finset.card of a filter.\n"
            "     After unfold, omega sees the filter as an opaque expression and CANNOT\n"
            "     determine its cardinality. omega counterexample: 'c ≥ 0, b - c ≥ 0, a ≥ 1, 0 ≤ a - 2*b ≤ 1'.\n"
            "     The counting bound `n/2 < |S_ge|` MUST be proved by:\n"
            "     a) Using Finset.card_filter_add_card_filter_eq_card to split into ≥ and <\n"
            "     b) Using the fact that Finset.card ι is odd: n = 2*(n/2) + 1\n"
            "     c) Combining with omega for the final Nat arithmetic\n"
            "  3. For the complement bound, use:\n"
            "     have : against_set.card ≤ (Finset.filter (fun i => peaks i < median_peak peaks) Finset.univ).card\n"
            "     Then use Finset.card_filter_add_card_filter_eq_card with le/lt split.\n"
            "     Do NOT use `Finset.card_compl` directly on a let-bound Finset.\n"
            "\n"
            "CRITICAL RULES:\n"
            "  - ZERO sorry. Any sorry = FAILURE.\n"
            "  - DO NOT use aesop. It cannot do set cardinality.\n"
            "  - DO NOT use omega/nlinarith for counting bounds after unfold. They CANNOT prove them.\n"
            "  - The P type has .1 (rel) and .2 (not reverse). Use .1 and .2 projections.\n"
            "  - ALWAYS simp Finset.mem_filter to extract predicates from Finset membership.\n"
            "\n"
            "AVAILABLE APIs:\n"
            "  Finset.filter, Finset.card, Finset.card_le_card, Finset.mem_filter\n"
            "  Finset.filter_subset, Finset.card_univ\n"
            "  Finset.card_filter_add_card_filter_eq_card : |{x ∈ s | p x}| + |{x ∈ s | ¬p x}| = |s|\n"
            "  List.mergeSort, List.length_mergeSort, List.length_map\n"
            "  List.mergeSort_perm, List.Perm, List.getD\n"
            "  List.length_toList, Finset.length_toList\n"
            "  mod_cast, omega, classical, Nat.odd_iff\n"
            "  lt_of_le_of_ne, le_of_not_gt, Ne.symm\n"
            "\n"
            "DO NOT USE (do NOT exist in Lean 4 v4.29.1):\n"
            "  List.Sorted, List.Sorted.rel_get_of_le_get, List.getD_eq_get,\n"
            "  List.length_filter, List.Sublist, List.mem_filter (List version)\n"
            "  aesop, nlinarith for counting\n"
        ),
        "proof_scaffolding": "",
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
        "line": 446,
        "sorry_type": "full_proof",
        "theorem_name": "banks_set_condorcet",
        "theorem": "banks_set_condorcet",
        "imports": VOTING_IMPORTS,
        "goal": "∃ C, banks_chain prof S C ∧ x ∈ C ∧ ∀ y ∈ C, y ≠ x → margin_pos prof x y",
        "description": (
            "Prove banks_set_condorcet: if x is a Condorcet winner in S,\n"
            "then x belongs to the Banks set.\n"
            "The sorry is at L446 (single line). Replace it with a proof.\n"
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
            "IMPORTANT: Use file_replace_sorry(446, code) to replace ONLY the sorry line.\n"
            "The sorry is a SINGLE LINE at L446. Replace it with the full proof.\n"
            "DO NOT use file_replace_lines for the proof — it can corrupt surrounding code.\n"
            "Import Mathlib.Data.Finset.Powerset is already added."
        ),
        "proof_scaffolding": (
            "  -- Import Mathlib.Data.Finset.Powerset already added\n"
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
            "  · -- maximality: prove no element from S\\C can be added\n"
            "    intro y hyS hyC\n"
            "    push_neg\n"
            "    intro hTot hTrans\n"
            "    have hInsertPC : isPC (insert y C) := by\n"
            "      unfold isPC\n"
            "      refine ⟨Finset.insert_subset_iff.mpr ⟨hyS, hCsub⟩,\n"
            "        Finset.mem_insert_of_mem hCx, ?_, ?_, ?_⟩\n"
            "      · -- total on insert y C\n"
            "        intro a ha b hb hab\n"
            "        rw [Finset.mem_insert] at ha hb\n"
            "        rcases ha with rfl | haC\n"
            "        · rcases hb with rfl | hbC\n"
            "          · exact absurd rfl hab\n"
            "          · exact hTot.1 b hbC hab\n"
            "        · rcases hb with rfl | hbC\n"
            "          · exact Or.inr (hTot.2 a haC hab)\n"
            "          · exact hCtot a haC b hbC hab\n"
            "      · -- transitive on insert y C\n"
            "        intro a ha b hb c hc hab hbc\n"
            "        rw [Finset.mem_insert] at ha hb hc\n"
            "        rcases ha with rfl | haC; rcases hb with rfl | hbC; rcases hc with rfl | hcC\n"
            "        · exact hab\n"
            "        · exact hTrans b hbC c hcC hab hbc\n"
            "        · exact (hTot.1 c hcC hab).elim\n"
            "        · exact hTrans a haC c hcC (hTot.2 a haC hab) hbc\n"
            "        · exact (hTot.2 b hbC hab).elim\n"
            "        · exact hCtrans a haC b hbC c hcC hab hbc\n"
            "        · exact hTrans a haC c hcC hab (hTot.1 c hcC hbc)\n"
            "        · exact hCtrans a haC b hbC c hcC hab hbc\n"
            "      · -- x dominates all in insert y C\n"
            "        intro b hb hbx\n"
            "        rw [Finset.mem_insert] at hb\n"
            "        rcases hb with rfl | hbC\n"
            "        · exact hw.2 y hyS hbx\n"
            "        · exact hCdom b hbC hbx\n"
            "    have hInsertMem : insert y C ∈ S.powerset.filter isPC :=\n"
            "      Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr\n"
            "        (Finset.insert_subset_iff.mpr ⟨hyS, hCsub⟩), hInsertPC⟩\n"
            "    have hle : (insert y C).card ≤ C.card := by\n"
            "      have hsup := Finset.le_sup (s := S.powerset.filter isPC)\n"
            "        (f := Finset.card) hInsertMem\n"
            "      simpa [hCcard] using hsup\n"
            "    have hlt : C.card < (insert y C).card :=\n"
            "      Finset.card_lt_card (Finset.ssubset_insert hyC)\n"
            "    exact (not_lt_of_ge hle hlt)\n"
            "  · exact fun y hy hne => hCdom y hy hne"
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
        "goal": "∀ y ∈ Finset.univ.image peaks, y ≠ median_peak peaks → margin_pos prof (median_peak peaks) y",
        "imports": VOTING_IMPORTS,
        "description": (
            "Prove that the median peak beats every other alternative in median_voter_theorem.\n"
            "The sorry is in the second branch of a constructor (after proving median ∈ image peaks).\n"
            "\n"
            "!! CRITICAL WARNINGS !!\n"
            "  1. Do NOT call median_voter_theorem — the sorry IS INSIDE this theorem.\n"
            "     Calling it recursively is a CIRCULAR REFERENCE and will never compile.\n"
            "  2. Do NOT use trace_state, show_plan, pretty — these are Lean 3 tactics.\n"
            "     Lean 4 uses different introspection.\n"
            "  3. Do NOT use aesop, simp alone — they cannot handle single-peaked counting.\n"
            "  4. Start with: intro y hy hne_y\n"
            "     Then use by_cases hlt : y < median_peak peaks or lt_or_gt_of_ne.\n"
            "\n"
            "GOAL at sorry:\n"
            "  ∀ y ∈ Finset.univ.image peaks, y ≠ median_peak peaks →\n"
            "    margin_pos prof (median_peak peaks) y\n"
            "\n"
            "CONTEXT (all available in scope):\n"
            "  prof : ι → PrefOrder σ, peaks : ι → σ\n"
            "  hsp : single_peaked_profile prof peaks\n"
            "  hodd : Odd (Fintype.card ι)\n"
            "  hcard_pos : 0 < Fintype.card ι\n"
            "  hne : Nonempty ι\n"
            "  [Inhabited σ]\n"
            "  l : List σ := sorted_peaks_list peaks = (Finset.univ.toList.map peaks).mergeSort (· ≤ ·)\n"
            "  hl : l.length = Fintype.card ι\n"
            "  hperm : l ≈ Finset.univ.toList.map peaks\n"
            "  median_peak peaks = l.getD (l.length / 2) default\n"
            "\n"
            "PROOF STRATEGY (follow step by step):\n"
            "  After intro y hy hne_y:\n"
            "  1. Use by_cases hlt : y < median_peak peaks\n"
            "  2. Case hlt : y < median_peak:\n"
            "     a. Unfold margin_pos, margin to get arithmetic goal about Finset.card\n"
            "     b. Set sL = Finset.filter (fun i => peaks i < median_peak peaks) Finset.univ\n"
            "     c. Set sR = Finset.filter (fun i => median_peak peaks ≤ peaks i) Finset.univ\n"
            "     d. For each i ∈ sR with peaks i ≥ median_peak:\n"
            "        single_peaked below-peak: y ≤ median_peak ≤ peaks i ⟹ (prof i).rel median_peak y\n"
            "        is_peak (if peaks i = median_peak): P (prof i).rel (median_peak peaks) y\n"
            "     e. Show card(sR) ≥ (n+1)/2 using hl + hodd + sorted list properties\n"
            "     f. Conclude: margin > 0 by omega\n"
            "  3. Case ¬hlt : use ¬(y < median_peak) + hne_y → y > median_peak, symmetric\n"
            "\n"
            "KEY DEFINITIONS:\n"
            "  margin_pos prof x y := 0 < margin prof x y\n"
            "  margin prof x y := (card(filter (fun i => P (prof i).rel x y) univ) : ℤ)\n"
            "                     - (card(filter (fun i => P (prof i).rel y x) univ) : ℤ)\n"
            "  P R x y := R x y ∧ ¬ R y x  (strict preference from Basic.lean)\n"
            "  single_peaked R p := is_peak R p ∧ (∀ a b, a ≤ b → b ≤ p → R b a)\n"
            "                                    ∧ (∀ a b, p ≤ a → a ≤ b → R a b)\n"
            "  single_peaked_profile prof peaks := ∀ i, single_peaked (prof i).rel (peaks i)\n"
            "  is_peak R p := ∀ x, x ≠ p → P R p x\n"
            "\n"
            "AVAILABLE LEMMAS:\n"
            "  List.mergeSort_perm, List.length_mergeSort, List.length_map\n"
            "  Finset.mem_image, Finset.mem_univ, Finset.mem_filter\n"
            "  Finset.card_filter, Finset.card_univ, Fintype.card\n"
            "  Nat.odd_iff : Odd n ↔ ∃ k, n = 2*k + 1\n"
            "  lt_or_ge : ∀ a b, a < b ∨ a ≥ b\n"
            "  lt_or_gt_of_ne : a ≠ b → a < b ∨ b < a\n"
            "\n"
            "DO NOT USE (do NOT exist in Lean 4 v4.29.1 Mathlib):\n"
            "  median_voter_theorem (RECURSIVE! sorry is inside it)\n"
            "  trace_state, show_plan, pretty (Lean 3 only)\n"
            "  List.Sorted, List.mergeSort_sorted, List.Sorted.*\n"
            "  Finset.card_filter_add_card_filter_neg\n"
            "  aesop (too weak for this proof)\n"
        ),
        "proof_scaffolding": (
            "intro y hy hne_y\n"
            "-- Unfold the target\n"
            "unfold margin_pos margin\n"
            "-- Split into two cases based on position relative to median\n"
            "by_cases hlt : y < median_peak peaks\n"
            "· -- Case: y < median_peak\n"
            "  -- Show majority of voters prefer median_peak to y\n"
            "  -- Voters with peak >= median_peak prefer median to y (single-peaked below-peak)\n"
            "  sorry -- TODO: counting argument for y < median\n"
            "· -- Case: y >= median_peak, but y ≠ median_peak, so y > median_peak\n"
            "  -- Symmetric: voters with peak <= median_peak prefer median to y\n"
            "  -- Use above-peak property: median_peak <= y, peaks i <= median_peak => (prof i).rel median_peak y\n"
            "  sorry -- TODO: counting argument for y > median\n"
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
            "the sorry must show there exists a maximal chain where x beats everyone.\n"
            "\n"
            "CONTEXT at sorry:\n"
            "  prof : ι → PrefOrder σ\n"
            "  S : Finset σ\n"
            "  x : σ\n"
            "  hw : condorcet_winner prof S x\n"
            "  hw.1 : x ∈ S\n"
            "  hw.2 : ∀ y ∈ S, y ≠ x → margin_pos prof x y\n"
            "\n"
            "GOAL: ∃ chain, IsChain (fun y z => margin_pos prof y z) chain\n"
            "       ∧ x ∈ chain ∧ chain.card = ... (maximal chain)\n"
            "\n"
            "CRITICAL WARNING:\n"
            "  This proof was previously solved by GPT-5.5 (DEMO 13) using:\n"
            "  - isPC helper for IsChain from pairwise comparisons\n"
            "  - Finset.exists_mem_eq_sup for maximal chain existence\n"
            "  - Cardinality contradiction argument\n"
            "  The singleton chain {x} approach may work as a starting point.\n"
            "\n"
            "AVAILABLE DEFINITIONS (in Voting.lean / Basic.lean):\n"
            "  margin_pos, condorcet_winner, banks_winner, banks_set\n"
            "  PrefOrder (structure with rel, refl, total fields)\n"
            "  List.IsChain (from Mathlib), isChain_append_last (private helper, line 302)\n"
            "  chain_head_relates_to_all (line 337)\n"
            "\n"
            "NOTE: isPC does NOT exist — do NOT use it.\n"
            "  Finset.exists_mem_eq_sup may or may not exist in Mathlib.\n"
            "  Use Finset.subset_of_mem_filter, Finset.mem_singleton,\n"
            "  Finset.singleton_subset_iff as alternatives.\n"
            "\n"
            "DO NOT USE:\n"
            "  List.Sorted, List.mergeSort, List.mergeSort_sorted\n"
            "  isPC (does NOT exist in codebase)\n"
        ),
        "proof_scaffolding": (
            "-- Strategy: use singleton chain {x}, show it's a valid chain\n"
            "-- and use Finset.exists_mem_eq_sup for maximality\n"
            "--\n"
            "-- Step 1: Construct chain = {x} (singleton)\n"
            "-- Step 2: Show IsChain for singleton (trivially ordered)\n"
            "-- Step 3: Show x ∈ chain\n"
            "-- Step 4: Show maximality via condorcet_winner property\n"
        ),
        "difficulty": "hard",
    },
}
