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

_COOPERATIVE_GAMES_CANDIDATES = [
    Path(r"C:\dev\CoursIA\MyIA.AI.Notebooks\GameTheory\cooperative_games_lean"),
    Path(r"D:\CoursIA\MyIA.AI.Notebooks\GameTheory\cooperative_games_lean"),
    Path(r"d:\CoursIA\MyIA.AI.Notebooks\GameTheory\cooperative_games_lean"),
]
COOPERATIVE_GAMES_DIR = next(
    (p for p in _COOPERATIVE_GAMES_CANDIDATES if p.exists()),
    Path(LEAN_PROJECT_DIR) if LEAN_PROJECT_DIR else _COOPERATIVE_GAMES_CANDIDATES[0],
)
SHAPLEY_FILE = COOPERATIVE_GAMES_DIR / "CooperativeGames" / "Shapley.lean" if COOPERATIVE_GAMES_DIR.exists() else None
BASIC_FILE = COOPERATIVE_GAMES_DIR / "CooperativeGames" / "Basic.lean" if COOPERATIVE_GAMES_DIR.exists() else None

_SOCIAL_CHOICE_CANDIDATES = [
    Path(r"C:\dev\CoursIA\MyIA.AI.Notebooks\GameTheory\social_choice_lean"),
    Path(r"D:\CoursIA\MyIA.AI.Notebooks\GameTheory\social_choice_lean"),
    Path(r"d:\CoursIA\MyIA.AI.Notebooks\GameTheory\social_choice_lean"),
]
SOCIAL_CHOICE_DIR = next(
    (p for p in _SOCIAL_CHOICE_CANDIDATES if p.exists()),
    _SOCIAL_CHOICE_CANDIDATES[0],
)
VOTING_FILE = SOCIAL_CHOICE_DIR / "SocialChoice" / "Voting.lean" if SOCIAL_CHOICE_DIR.exists() else None
SMOKE_TEST_FILE = SOCIAL_CHOICE_DIR / "SocialChoice" / "_SmokeTest.lean" if SOCIAL_CHOICE_DIR.exists() else None
VOTING_IMPORTS = """import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Sort
import SocialChoice.Definitions
"""

# ── HONEST sorrys registry (DO NOT TOUCH) ──
# Some sorrys document genuine theoretical impossibility — they are NOT bugs to
# fix. Attacking them wastes compute and produces fake "PROVED" reports. Each
# entry is keyed by the absolute filepath (as string) and lists `sorry_line`
# numbers that the prover MUST refuse to target.
#
# Pattern: an honest sorry has FIXME/cannot/unprovable/counter-example comments
# immediately above it. The detector in `lean_utils.is_honest_sorry()` confirms
# this dynamically; this registry is the static fallback.
HONEST_SORRIES = {
    str(VOTING_FILE) if VOTING_FILE else "": {
        # Line of the actual `sorry` keyword; FIXME marker is in comment block
        # immediately above (L253-261). Realigned 2026-05-12 (ai-01 iter 2)
        # after PR #952 shifted line numbers when L338+L361 were proven.
        262: (
            "median_voter_theorem WEAK version is UNPROVABLE with single_peaked "
            "(weak preference). Counter-example: σ={1,2,3}, 3 voters, peaks "
            "[1,2,3], median=2. If voter 3 is indifferent between 1 and 2, "
            "margin(2,1) = 0, not > 0. Use median_voter_theorem_strict instead "
            "(L271 with hstrict_left/hstrict_right hypotheses)."
        ),
    },
}


def create_client(provider: str = "zai", model_key: str = "reasoning",
                  request_timeout_s: float = 240.0,
                  max_retries: int = 1) -> OpenAIChatCompletionClient:
    """Create a ChatCompletionClient for the given provider.

    request_timeout_s caps a single chat completion call. Reasoning models
    can legitimately take 30-90s to think; cap at 4min to detect hangs while
    leaving room for genuinely deep reasoning. BG iter 2 had a TacticAgent
    chat hang for 16+ min with no completion — that's a hang, not slow
    reasoning, and we should fail-fast so the workflow can recover instead
    of burning the wall-clock cap.
    """
    from openai import AsyncOpenAI
    cfg = PROVIDERS[provider]
    async_client = AsyncOpenAI(
        api_key=cfg["api_key"],
        base_url=cfg["base_url"],
        timeout=request_timeout_s,
        max_retries=max_retries,
    )
    return OpenAIChatCompletionClient(
        model=cfg["models"][model_key],
        async_client=async_client,
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
        "line": 566,
        "sorry_type": "full_proof",
        "theorem_name": "shapley_uniqueness",
        "theorem": "shapley_uniqueness",
        "imports": SHAPLEY_IMPORTS,
        "description": (
            "Replace sorry at line 566 of Shapley.lean (theorem starts L556). Prove shapley_uniqueness:\n"
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
    # DEMO 7 (SHAPLEY_EFFICIENT_COEFF, was line=292) removed: theorem shapley_efficient
    # is now fully proved on main (Shapley.lean L243-L329). Single remaining sorry in
    # this file is L566 (shapley_uniqueness), already covered by DEMOS 6 + 8.
    8: {
        "name": "SHAPLEY_UNIQUENESS_ALT",
        "file": str(SHAPLEY_FILE),
        "line": 566,
        "sorry_type": "full_proof",
        "theorem_name": "shapley_uniqueness (alternative entry)",
        "theorem": "shapley_uniqueness",
        "imports": SHAPLEY_IMPORTS,
        "description": (
            "Same target as Demo 6 (line 566). Alias for batch/testing.\n"
            "Prove shapley_uniqueness: any solution satisfying all 4 axioms equals Shapley value.\n"
            "Uses Mobius decomposition of games into unanimity games.\n"
            "All helper theorems proved."
        ),
        "difficulty": "very_hard",
    },
    9: {
        "name": "VOTING_MEDIAN_COUNTING_LT",
        "file": str(VOTING_FILE),
        "line": 355,
        "sorry_type": "sorry_replacement",
        "theorem_name": "median_voter_theorem_strict (case peaks_j < median)",
        "theorem": "median_voter_theorem_strict",
        "imports": VOTING_IMPORTS,
        "goal": (
            "(Finset.filter (fun i => peaks i < median_peak peaks) Finset.univ).card "
            "< (Finset.filter (fun i => median_peak peaks ≤ peaks i) Finset.univ).card"
        ),
        "description": (
            "REPLACES the sorry at L325 (case `peaks_j < median_peak peaks`)\n"
            "in `median_voter_theorem_strict`.\n"
            "\n"
            "DO NOT touch L261 (that's the WEAK version sorry — registered as\n"
            "honest/unprovable in HONEST_SORRIES). The prover will refuse it.\n"
            "\n"
            "GOAL at sorry (EXACT):\n"
            "  (Finset.filter (fun i => peaks i < median_peak peaks) Finset.univ).card\n"
            "  < (Finset.filter (fun i => median_peak peaks ≤ peaks i) Finset.univ).card\n"
            "\n"
            "HYPOTHESES IN SCOPE:\n"
            "  ι : Type, [Fintype ι], σ : Type, [LinearOrder σ], [Inhabited σ]\n"
            "  prof : ι → PrefOrder σ, peaks : ι → σ\n"
            "  hsp : single_peaked_profile prof peaks\n"
            "  hodd : Odd (Fintype.card ι)\n"
            "  hcard_pos : 0 < Fintype.card ι\n"
            "  j : ι, hlt : peaks j < median_peak peaks\n"
            "  hgt_peaks, hfor_card, hag_card  (already established above — NOT needed for sorry)\n"
            "\n"
            "PROOF STRATEGY (combinatorial counting via sorted list):\n"
            "  Let n = Fintype.card ι (odd, n = 2k+1).\n"
            "  Let l = sorted_peaks_list peaks = (univ.toList.map peaks).mergeSort (· ≤ ·).\n"
            "  Then l.length = n and median_peak = l.getD (n/2) default.\n"
            "  Since l is sorted (Pairwise (· ≤ ·)):\n"
            "    - At most n/2 entries are STRICTLY less than l[n/2] (positions 0..n/2-1)\n"
            "    - At least n/2 + 1 = (n+1)/2 entries satisfy l[n/2] ≤ entry (positions n/2..n-1)\n"
            "  Transfer counts via List.Perm.countP_eq from sorted list to univ via mergeSort_perm.\n"
            "\n"
            "KEY LEMMAS (verified Lean 4.29.1 + Mathlib current):\n"
            "  List.mergeSort_perm : (l.mergeSort r) ~ l\n"
            "  List.pairwise_mergeSort : (l.mergeSort r).Pairwise r  -- if r is total/transitive\n"
            "  List.Perm.countP_eq (p : α → Bool) : l₁ ~ l₂ → l₁.countP p = l₂.countP p\n"
            "  List.countP_append, List.countP_eq_zero, List.countP_eq_length\n"
            "  List.take_append_drop, List.length_take, List.length_drop\n"
            "  List.Pairwise.rel_get_of_le (Mathlib/Data/List/Pairwise.lean L142) :\n"
            "    l.Pairwise r → ∀ i j (h : i ≤ j) (hj : j < l.length), r l[i] l[j]\n"
            "  Finset.toList_filter, Finset.length_toList\n"
            "\n"
            "CRITICAL ERROR PATTERNS TO AVOID:\n"
            "  1. `List.Sorted` does NOT exist as a top-level abbrev in 4.29.1.\n"
            "     Use `Pairwise (· ≤ ·)` directly. Sorted aliases were deprecated 2025-10-11.\n"
            "  2. `omega` CANNOT prove counting bounds over Finset.card of an opaque filter.\n"
            "     You MUST reduce to concrete arithmetic AFTER establishing list-level\n"
            "     count bounds.\n"
            "  3. When using `List.Perm.countP_eq`, the predicate must be `α → Bool`.\n"
            "     Use `decide` or explicit `decidable` to coerce a `Prop` predicate.\n"
            "  4. To transfer between `Finset.filter ... |>.card` and `List.countP`:\n"
            "     `Finset.toList_filter` then `Finset.length_toList`.\n"
            "\n"
            "RECOMMENDED SUB-LEMMAS (extract via `have` to keep main proof small):\n"
            "  have hperm : sorted_peaks_list peaks ~ Finset.univ.toList.map peaks := \n"
            "    List.mergeSort_perm _ _\n"
            "  have hsort : (sorted_peaks_list peaks).Pairwise (· ≤ ·) := by\n"
            "    apply List.pairwise_mergeSort  -- may need transitivity hypothesis\n"
            "  -- Then split sorted list at index n/2 = (sorted_peaks_list peaks).length / 2\n"
            "  -- and use Pairwise to bound countP on each half\n"
            "\n"
            "CRITICAL RULES:\n"
            "  - ZERO sorry remaining. Any sorry on this lemma = FAILURE.\n"
            "  - DO NOT use aesop on counting bounds.\n"
            "  - DO NOT use omega/nlinarith on opaque Finset.card terms.\n"
            "  - DO NOT touch lines 252-261 (HONEST sorry, weak version, unprovable).\n"
            "  - Build must SUCCEED (use compile() to verify).\n"
            "  - sorry count must DECREASE by at least 1 (originally 3 sorrys in Voting.lean).\n"
            "\n"
            "RELATED: DEMO 14 (VOTING_MEDIAN_COUNTING_GT) targets L348 with the\n"
            "symmetric statement. Once L325 is solved, the same proof technique\n"
            "applies (just swap < and ≤). Consider extracting a shared helper\n"
            "lemma `countP_lt_kth_le_of_sorted` in a new file.\n"
        ),
        "proof_scaffolding": (
            "  -- STEP 1 (VERIFIED COMPILES — keep as-is): A.card + B.card = n via complementarity\n"
            "  have hcomp : (Finset.filter (fun i => peaks i < median_peak peaks) Finset.univ).card +\n"
            "      (Finset.filter (fun i => median_peak peaks ≤ peaks i) Finset.univ).card =\n"
            "      Fintype.card ι := by\n"
            "    have hflip : (Finset.filter (fun i => peaks i < median_peak peaks) Finset.univ) =\n"
            "        (Finset.filter (fun i => ¬ median_peak peaks ≤ peaks i) Finset.univ) := by\n"
            "      apply Finset.filter_congr\n"
            "      intro i _\n"
            "      exact (not_le).symm\n"
            "    rw [hflip, add_comm,\n"
            "        Finset.card_filter_add_card_filter_not\n"
            "          (s := Finset.univ) (p := fun i => median_peak peaks ≤ peaks i),\n"
            "        Finset.card_univ]\n"
            "  -- STEP 2 (TODO — your job): A.card ≤ Fintype.card ι / 2\n"
            "  --   Strategy: unfold median_peak to L.getD k default where L = sorted peaks list\n"
            "  --   and k = L.length / 2. Sortedness (L.Pairwise (· ≤ ·)) implies values\n"
            "  --   strictly less than L[k] occur only at positions < k, so countP < L[k] ≤ k.\n"
            "  --   Transfer card → countP via Finset.toList + List.countP_map + Perm.countP_eq.\n"
            "  --   Key lemmas: List.mergeSort_perm, List.pairwise_mergeSort,\n"
            "  --               List.Pairwise.rel_get_of_le, List.countP_le_length,\n"
            "  --               Finset.length_toList.\n"
            "  -- STEP 3 (closes goal once Step 2 done): combine hcomp + Step 2 + hodd via omega\n"
            "  --   2*A.card ≤ 2k = n-1 < n = A.card + B.card  →  A.card < B.card.\n"
            "  sorry\n"
        ),
        "difficulty": "very_hard",
    },
    14: {
        "name": "VOTING_MEDIAN_COUNTING_GT",
        "file": str(VOTING_FILE),
        "line": 385,
        "sorry_type": "sorry_replacement",
        "theorem_name": "median_voter_theorem_strict (case peaks_j > median)",
        "theorem": "median_voter_theorem_strict",
        "imports": VOTING_IMPORTS,
        "goal": (
            "(Finset.filter (fun i => median_peak peaks < peaks i) Finset.univ).card "
            "< (Finset.filter (fun i => peaks i ≤ median_peak peaks) Finset.univ).card"
        ),
        "description": (
            "REPLACES the sorry at L348 (case `peaks_j > median_peak peaks`).\n"
            "Symmetric to DEMO 9 (L325). Same proof technique, swap `<` and `≤`.\n"
            "\n"
            "GOAL at sorry (EXACT):\n"
            "  (Finset.filter (fun i => median_peak peaks < peaks i) Finset.univ).card\n"
            "  < (Finset.filter (fun i => peaks i ≤ median_peak peaks) Finset.univ).card\n"
            "\n"
            "STRATEGY: identical to DEMO 9 but reversed inequality.\n"
            "Use `not_lt.mpr` / `lt_of_le_of_ne` / mirror sorting arguments.\n"
            "If a `countP_lt_kth_le_of_sorted` helper was extracted for L325,\n"
            "apply it here with the reversed predicate.\n"
            "\n"
            "Same DO-NOT-USE / HONEST_SORRIES restrictions as DEMO 9.\n"
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
    15: {
        "name": "SMOKE_TEST_ZERO_ADD",
        "file": str(SMOKE_TEST_FILE) if SMOKE_TEST_FILE else "",
        "line": 6,
        "sorry_type": "sorry_replacement",
        "theorem_name": "zero_add_smoke",
        "theorem": "zero_add_smoke",
        "imports": "import Mathlib.Data.Nat.Basic\n",
        "goal": "0 + n = n",
        "description": (
            "Smoke test trivial: prove 0 + n = n for Nat.\n"
            "Single one-line proof. Use one of:\n"
            "  exact Nat.zero_add n\n"
            "  omega\n"
            "  simp\n"
            "Replace the sorry at L6 of _SmokeTest.lean."
        ),
        "difficulty": "trivial",
    },
}
