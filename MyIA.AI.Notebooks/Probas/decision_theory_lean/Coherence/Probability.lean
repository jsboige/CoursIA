import Mathlib
import Coherence.Basic
import Coherence.DutchBook

/-!
# Coherence.Probability — cohérence (Dutch Book mono-livret) ⟺ axiomes de probabilité

Issue #4050 — jalon-clé `coherent_iff_probability` (cas fini). Le module `DutchBook.lean`
prouve la direction constructive « violation de l'inclusion–exclusion sur deux événements
⟹ Dutch Book à quatre tickets ». On établit ici la **correspondance pour le cadre fini
mono-livret** : une fonction de prix `q` est exploitable par un Dutch Book (à un seul
ticket) si et seulement si elle viole une borne de probabilité — non-négativité `q A ≥ 0`,
majoration `q A ≤ 1`, ou normalisation `q ∅ = 0`, `q univ = 1`.

**Pourquoi c'est élémentaire (et non Hahn–Banach).** L'évaluation « MOYENNE / séparation
d'hyperplans » de l'issue #4050 visait une formulation générale (livrets de taille
arbitraire sur un nombre quelconque d'événements, dont la réciproque passe par l'argument
d'espérance `E_q[gain] = 0`). Pour la **caractérisation mono-livret**, chaque axiome violé
admet un Dutch Book EXPLICITE à un seul ticket, et la réciproque se déduit par disjonction
sur le signe de la mise `s` :
- `q A < 0` : vendre (`s = −1`), gain agent `= q A − 𝟙_A ≤ q A < 0`.
- `q A > 1` : acheter (`s = +1`), gain agent `= 𝟙_A − q A < 0` (car `𝟙_A ≤ 1`).
- `q univ ≠ 1` : un ticket sur l'univers (`s = ±1`) donne un gain de signe constant `< 0`.
- `q ∅ > 0` : un ticket sur le vide (`s = +1`) donne `−q ∅ < 0` (car `𝟙_∅ = 0`).

Réciproquement, sous les bornes de probabilité, aucune mise `s` ne rend `s (𝟙_A − q A) < 0`
en tout état (disjonction `s < 0` / `s = 0` / `s > 0`).

**Cadrage honnête (G.3/G.9).** Le `coherent_iff_probability` COMPLET (livrets de taille
arbitraire, via la reconstruction de la mesure `q A = Σ_{ω ∈ A} q {ω}` puis l'argument
d'espérance) reste un jalon suivant ; on livre ici la caractérisation mono-livret et son
identité avec les bornes de probabilité, 0 `sorry`. Voir de Finetti (1937), *La prévision :
ses lois logiques, ses sources subjectives*.
-/

namespace Coherence

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-! ## Gain d'un ticket unique et Dutch Book mono-livret -/

/-- Le gain net à l'état `ω` d'un ticket unique sur l'événement `A` avec mise `s` (mise
    positive = achat, négative = vente). Comme pour `ieGain`, le ticket paie `𝟙_A ω` et
    coûte `q A` : gain `= s (𝟙_A ω − q A)`. -/
def ticketGain (q : Price Ω) (A : Event Ω) (s : ℝ) (ω : Ω) : ℝ := s * (ind A ω - q A)

/-- Un **Dutch Book mono-livret** sur `A` : une mise `s` dont le gain est strictement
    négatif en tout état — une perte sûre pour l'agent. -/
def IsSingleDutchBook (q : Price Ω) (A : Event Ω) (s : ℝ) : Prop :=
  ∀ ω : Ω, ticketGain q A s ω < 0

/-- `q` est **cohérente au sens mono-livret** si aucun événement n'admet de Dutch Book à
    un seul ticket. -/
def SingleCoherent (q : Price Ω) : Prop := ∀ A s, ¬ IsSingleDutchBook q A s

/-- `q` satisfait les **bornes de probabilité** (cas fini) : non-négativité, majoration
    par 1, et normalisation `q ∅ = 0`, `q univ = 1`. -/
def ProbBounds (q : Price Ω) : Prop :=
  (∀ A, (0:ℝ) ≤ q A) ∧ (∀ A, q A ≤ 1) ∧ q ∅ = 0 ∧ q (Finset.univ : Event Ω) = 1

/-! ## Lemmes : chaque axiome violé admet un Dutch Book mono-livret (witness explicite) -/

private lemma ind_nonneg (A : Event Ω) (ω : Ω) : (0:ℝ) ≤ ind A ω := by
  unfold ind; split <;> simp

private lemma ind_le_one (A : Event Ω) (ω : Ω) : ind A ω ≤ (1:ℝ) := by
  unfold ind; split <;> simp

/-- `q A < 0` ⟹ Dutch Book : vendre un ticket `A` (`s = −1`), gain `= q A − 𝟙_A < 0`. -/
theorem single_dutch_book_of_neg (q : Price Ω) (A : Event Ω) (h : q A < 0) :
    ∃ s, IsSingleDutchBook q A s := by
  refine ⟨-1, fun ω => ?_⟩
  show (-1:ℝ) * (ind A ω - q A) < 0
  have heq : (-1:ℝ) * (ind A ω - q A) = q A - ind A ω := by ring
  rw [heq]
  linarith [ind_nonneg A ω]

/-- `q A > 1` ⟹ Dutch Book : acheter (`s = +1`), gain `= 𝟙_A − q A < 0` (car `𝟙_A ≤ 1`). -/
theorem single_dutch_book_of_high (q : Price Ω) (A : Event Ω) (h : (1:ℝ) < q A) :
    ∃ s, IsSingleDutchBook q A s := by
  refine ⟨1, fun ω => ?_⟩
  show (1:ℝ) * (ind A ω - q A) < 0
  have heq : (1:ℝ) * (ind A ω - q A) = ind A ω - q A := by ring
  rw [heq]
  linarith [ind_le_one A ω]

/-- `q ∅ > 0` ⟹ Dutch Book sur l'événement vide (`s = +1`), gain `= −q ∅ < 0` (car
    `𝟙_∅ = 0` en tout état). -/
theorem single_dutch_book_of_pos_empty (q : Price Ω) (h : (0:ℝ) < q (∅ : Event Ω)) :
    ∃ s, IsSingleDutchBook q (∅ : Event Ω) s := by
  refine ⟨1, fun ω => ?_⟩
  show (1:ℝ) * (ind (∅ : Event Ω) ω - q ∅) < 0
  have hind : ind (∅ : Event Ω) ω = 0 := by unfold ind; simp
  have heq : (1:ℝ) * (ind (∅ : Event Ω) ω - q ∅) = ind (∅ : Event Ω) ω - q ∅ := by ring
  rw [heq, hind]; linarith

/-- `q univ < 1` ⟹ Dutch Book sur l'univers (`s = −1`), gain `= q univ − 1 < 0`
    (car `𝟙_univ = 1` en tout état). -/
theorem single_dutch_book_of_univ_lt (q : Price Ω) (h : q (Finset.univ : Event Ω) < 1) :
    ∃ s, IsSingleDutchBook q (Finset.univ : Event Ω) s := by
  refine ⟨-1, fun ω => ?_⟩
  show (-1:ℝ) * (ind (Finset.univ : Event Ω) ω - q Finset.univ) < 0
  have hind : ind (Finset.univ : Event Ω) ω = 1 := by
    unfold ind; rw [if_pos (Finset.mem_univ ω)]
  have heq : (-1:ℝ) * (ind (Finset.univ : Event Ω) ω - q Finset.univ) =
      q Finset.univ - ind (Finset.univ : Event Ω) ω := by ring
  rw [heq, hind]; linarith

/-! ## Théorème-clé : cohérence mono-livret ⟺ bornes de probabilité (de Finetti, cas fini) -/

/-- **de Finetti (cas fini, mono-livret).** Une fonction de prix `q` est cohérente au sens
    mono-livret (aucun Dutch Book à un seul ticket) **si et seulement si** elle satisfait
    les bornes de probabilité `0 ≤ q A ≤ 1`, `q ∅ = 0`, `q univ = 1`. L'hypothèse
    `[Nonempty Ω]` est la supposition physique naturelle (au moins un état du monde).

    **Preuve** (0 `sorry`) :
    - *⟹* (contraposée) : chaque borne violée admet un Dutch Book explicite
      (`single_dutch_book_of_neg/high/pos_empty/univ_lt`), contredisant `SingleCoherent`.
    - *⟸* : par trichotomie du signe de la mise `s`. Si `s < 0`, un gain `< 0` partout
      impose `𝟙_A > q A` partout ; pour un `ω ∉ A` (`A ≠ univ`) ceci force `0 > q A` (nie
      `q A ≥ 0`), et pour `A = univ` ceci force `1 > q univ` (nie `q univ = 1`). Si `s = 0`,
      le gain est nul (pas `< 0`). Si `s > 0`, un gain `< 0` partout impose `𝟙_A < q A`
      partout ; pour un `ω ∈ A` (`A` non vide) ceci force `1 < q A` (nie `q A ≤ 1`), et pour
      `A = ∅` ceci force `0 < q ∅` (nie `q ∅ = 0`). -/
theorem single_coherent_iff_prob_bounds (q : Price Ω) [Nonempty Ω] :
    SingleCoherent q ↔ ProbBounds q := by
  refine ⟨fun hsc => ?_, fun hb => ?_⟩
  · -- SingleCoherent ⟹ ProbBounds
    refine ⟨fun A => by_contra fun hn => ?_, fun A => by_contra fun hn => ?_, ?_, ?_⟩
    · -- 0 ≤ q A : hn : ¬(0 ≤ q A) ⟹ q A < 0
      obtain ⟨s, hdb⟩ := single_dutch_book_of_neg q A (not_le.mp hn)
      exact absurd hdb (hsc A s)
    · -- q A ≤ 1 : hn : ¬(q A ≤ 1) ⟹ 1 < q A
      obtain ⟨s, hdb⟩ := single_dutch_book_of_high q A (not_le.mp hn)
      exact absurd hdb (hsc A s)
    · -- q ∅ = 0
      by_contra hn
      rcases lt_or_gt_of_ne hn with hn0 | h0
      · obtain ⟨s, hdb⟩ := single_dutch_book_of_neg q (∅ : Event Ω) hn0
        exact absurd hdb (hsc _ s)
      · obtain ⟨s, hdb⟩ := single_dutch_book_of_pos_empty q h0
        exact absurd hdb (hsc _ s)
    · -- q univ = 1
      by_contra hn
      rcases lt_or_gt_of_ne hn with hlt | hgt
      · obtain ⟨s, hdb⟩ := single_dutch_book_of_univ_lt q hlt
        exact absurd hdb (hsc _ s)
      · obtain ⟨s, hdb⟩ := single_dutch_book_of_high q (Finset.univ : Event Ω) hgt
        exact absurd hdb (hsc _ s)
  · -- ProbBounds ⟹ SingleCoherent
    obtain ⟨hnn, hn1, h0, hu⟩ := hb
    intro A s hdb
    obtain ⟨w⟩ := ‹Nonempty Ω›
    rcases lt_trichotomy s 0 with hslt | hs0 | hsgt
    · -- s < 0 : 𝟙_A(ω) > q A pour tout ω
      have hind : ∀ ω, q A < ind A ω := fun ω => by
        have h := hdb ω
        unfold ticketGain at h
        nlinarith [hslt]
      by_cases hU : A = (Finset.univ : Event Ω)
      · -- A = univ : 𝟙_A(w) = 1, q A = 1 ⟹ 1 < 1, absurde
        have hiv : ind A w = 1 := by rw [hU]; unfold ind; simp
        have hqv : q A = 1 := by rw [hU]; exact hu
        linarith [hind w]
      · -- A ≠ univ : ∃ ω ∉ A, 𝟙_A = 0 ⟹ q A < 0, nie q A ≥ 0
        obtain ⟨ω, hω⟩ : ∃ ω, ω ∉ A := by
          by_contra hnex
          simp only [not_exists, Classical.not_not] at hnex
          exact absurd ((Finset.eq_univ_iff_forall).mpr hnex) hU
        have hiv : ind A ω = 0 := by unfold ind; rw [if_neg hω]
        linarith [hind ω, hnn A]
    · -- s = 0 : ticketGain = 0, jamais < 0
      have h0gain : ticketGain q A 0 w = 0 := by simp [ticketGain]
      have h := hdb w
      rw [hs0] at h
      rw [h0gain] at h
      linarith
    · -- s > 0 : 𝟙_A(ω) < q A pour tout ω
      have hind : ∀ ω, ind A ω < q A := fun ω => by
        have h := hdb ω
        unfold ticketGain at h
        nlinarith [hsgt]
      by_cases hA : A.Nonempty
      · -- A non vide : ∃ ω ∈ A, 𝟙_A = 1 ⟹ 1 < q A, nie q A ≤ 1
        obtain ⟨ω, hω⟩ := hA
        have hiv : ind A ω = 1 := by unfold ind; rw [if_pos hω]
        have h1lt : (1:ℝ) < q A := by rw [← hiv]; exact hind ω
        linarith [hn1 A]
      · -- A = ∅ : 𝟙_A(w) = 0, q A = q ∅ = 0 ⟹ 0 < 0, absurde
        rw [Finset.not_nonempty_iff_eq_empty] at hA
        have hiv : ind A w = 0 := by rw [hA]; unfold ind; simp
        have hqv : q A = 0 := by rw [hA]; exact h0
        linarith [hind w]

end Coherence
