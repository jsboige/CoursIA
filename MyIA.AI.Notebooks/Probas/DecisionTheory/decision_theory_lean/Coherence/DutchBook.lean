import Mathlib
import Coherence.Basic

/-!
# Coherence.DutchBook — incohérence ⟹ Dutch Book (de Finetti, direction constructive)

Issue #4050. Le théorème de cohérence de de Finetti (cas fini) établit la
correspondance entre **cohérence** (absence de pari à perte sûre) et **additivité**
(la fonction de prix satisfait l'inclusion–exclusion, donc est une mesure de
probabilité). On prouve ici la **direction constructive**, mécaniquement centrale :
si les prix violent l'inclusion–exclusion sur deux événements, un *Dutch Book*
explicite existe (mises concrètes sur les quatre tickets `A, B, A∩B, A∪B` donnant
une perte sûre). La contraposée donne « cohérence ⟹ additivité ».

La clé mathématique est l'identité d'inclusion–exclusion des indicatrices
(`ind_inclusion_exclusion` dans `Basic.lean`) : `𝟙_A + 𝟙_B − 𝟙_{A∩B} − 𝟙_{A∪B} = 0`
en tout état, donc le gain des quatre tickets avec mises `(1, 1, −1, −1)` est
exactement `δ := q(A∪B) + q(A∩B) − q(A) − q(B)`, **indépendant de l'état**. Si
`δ ≠ 0`, on choisit le signe des mises pour garantir une perte sûre = un Dutch Book.

**Cadrage honnête (G.3/G.9).** On prouve la direction « incohérence ⟹ Dutch Book »
(constructive, witness explicite, 0 `sorry`) et sa contraposée « cohérence ⟹
additivité sur deux événements ». La réciproque « additivité ⟹ cohérence » (et le
`coherent_iff_probability` complet : additivité générale + normalisation `q ∅ = 0`,
`q univ = 1`) nécessite la **séparation d'hyperplans / dualité LP** en dimension finie
(faisabilité Lean évaluée « MOYENNE » dans #4050) et est laissée **ouverte** comme
jalon suivant — non `sorry`-backed. Cette structure (une direction prouvée + la
réciproque ouverte documentée) est cohérente avec le module `Utility` du même lake
(direction sound prouvée, existence Herstein–Milnor ouverte). Voir de Finetti (1937).
-/

namespace Coherence

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-! ## Gain d'un livret de quatre tickets et Dutch Book -/

/-- Le gain net à l'état `ω` d'un livret de quatre tickets sur `(A, B, A∩B, A∪B)` avec
    mises `(sA, sB, sAB, sAU)` (mise positive = achat, négative = vente). Chaque ticket
    paie l'indicatrice de son événement et coûte `q(événement)` : le gain net d'un
    ticket est `mise × (indicatrice − prix)`. -/
def ieGain (q : Price Ω) (A B : Event Ω) (sA sB sAB sAU : ℝ) (ω : Ω) : ℝ :=
  sA * (ind A ω - q A) + sB * (ind B ω - q B)
    + sAB * (ind (A ∩ B) ω - q (A ∩ B)) + sAU * (ind (A ∪ B) ω - q (A ∪ B))

/-- Un **Dutch Book** par inclusion–exclusion : des mises sur `(A, B, A∩B, A∪B)` dont
    le gain net est **strictement négatif en tout état** — une perte sûre pour l'agent
    (et un profit sûr pour l'arbitragiste). -/
def IsIEArbitrage (q : Price Ω) (A B : Event Ω) (sA sB sAB sAU : ℝ) : Prop :=
  ∀ ω : Ω, ieGain q A B sA sB sAB sAU ω < 0

/-! ## Théorèmes cibles (direction constructive) -/

/-- **de Finetti (cas fini, ⟸, constructif).** Si le prix `q` viole l'inclusion–
    exclusion sur les événements `A, B` (`q(A∪B) + q(A∩B) ≠ q A + q B`), alors un
    Dutch Book existe : mises explicites sur `(A, B, A∩B, A∪B)` donnant une perte sûre.

    **Preuve** (0 `sorry`) : posons `δ := q(A∪B) + q(A∩B) − q A − q B ≠ 0`. Par
    l'identité d'inclusion–exclusion (`ind_inclusion_exclusion`), le gain du livret
    avec mises `(1, 1, −1,−1)` vaut exactement `δ` en tout état (la combinaison
    d'indicatrices s'annule). Si `δ < 0`, ces mises sont le Dutch Book. Si `δ > 0`, on
    inverse les signes `(−1, −1, 1, 1)` et le gain devient `−δ < 0`. Dans les deux cas,
    `linarith` conclut à partir de l'identité des indicatrices. -/
theorem non_additive_implies_dutch_book (q : Price Ω) (A B : Event Ω)
    (h : q (A ∪ B) + q (A ∩ B) ≠ q A + q B) :
    ∃ sA sB sAB sAU : ℝ, IsIEArbitrage q A B sA sB sAB sAU := by
  set δ := q (A ∪ B) + q (A ∩ B) - q A - q B
  have hδ : δ ≠ 0 := fun heq => h (by linarith)
  by_cases hδn : δ < 0
  · -- δ < 0 : mises (1, 1, −1, −1) → gain = δ < 0 en tout état.
    refine ⟨1, 1, -1, -1, ?_⟩
    intro ω
    simp only [ieGain]
    have hie := ind_inclusion_exclusion A B ω
    linarith
  · -- δ ≥ 0 ; avec δ ≠ 0 ⟹ δ > 0 : mises (−1, −1, 1, 1) → gain = −δ < 0.
    have hδge : 0 ≤ δ := not_lt.mp hδn
    have hδp : 0 < δ := lt_of_le_of_ne hδge (Ne.symm hδ)
    refine ⟨-1, -1, 1, 1, ?_⟩
    intro ω
    simp only [ieGain]
    have hie := ind_inclusion_exclusion A B ω
    linarith

/-- Les prix sont **cohérents** sur `(A, B)` si aucun Dutch Book n'existe sur les quatre
    événements `(A, B, A∩B, A∪B)`. -/
def CoherentOn (q : Price Ω) (A B : Event Ω) : Prop :=
  ∀ sA sB sAB sAU : ℝ, ¬ IsIEArbitrage q A B sA sB sAB sAU

/-- **Cohérence ⟹ inclusion–exclusion (de Finetti, contraposée).** Si aucun Dutch Book
    n'existe sur `(A, B, A∩B, A∪B)`, alors `q` est additif sur `A, B` : la fonction de
    prix satisfait l'inclusion–exclusion `q(A∪B) + q(A∩B) = q A + q B`. C'est la
    contraposée immédiate de `non_additive_implies_dutch_book`. -/
theorem coherent_on_implies_additive (q : Price Ω) (A B : Event Ω)
    (hc : CoherentOn q A B) :
    q (A ∪ B) + q (A ∩ B) = q A + q B := by
  by_contra h
  obtain ⟨sA, sB, sAB, sAU, harb⟩ := non_additive_implies_dutch_book q A B h
  exact hc sA sB sAB sAU harb

end Coherence
