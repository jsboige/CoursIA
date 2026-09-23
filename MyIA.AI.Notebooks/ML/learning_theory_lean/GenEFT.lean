import Mathlib
import EffectiveTheory.Repons

/-!
# GenEFT — description length, clustering, compétition A vs r

Tranche **R06** du corpus Tegmark (EPIC #16741, claim #16752) :
*GenEFT: A Generative Physics Framework for Automating Emergent Function
Tracking in Learning Machines* (Baek, Liu, Tegmark, arXiv:2402.05916v2).

Ce module formalise les trois morceaux quantitatifs du papier qui se prêtent
à une preuve courte et complète :

1. **Statics — description length par orbite** (Section III). Le re-labellage
   des `n` noeuds d'un graphe `G` est l'action naturelle de `Equiv.Perm (Fin n)`
   sur `SimpleGraph (Fin n)` ; les graphes « de même structure que `G` » sont
   exactement son orbite, et **orbit-stabilizer** donne
   `|orbit| · |Aut G| = n!` : encoder `G` revient à choisir un point dans une
   orbite de taille `n! / |Aut G|`, d'où la longueur de description
   `b = log₂ (n! / |Aut G|)`. Le pont `mem_aut_iff` identifie le stabilisateur
   à la définition usuelle d'automorphisme de graphe (préservation de
   l'adjacence dans les deux sens).

2. **Theorem 1 — clustering par décodeur injectif** (Section IV). Un
   autoencoder de classification (entrée : deux noeuds, sortie : `1` si même
   classe, `0` sinon) à perte d'entraînement **nulle** et décodeur
   **injectif** sépare exactement les classes : deux noeuds ont le même
   embedding **ssi** ils ont la même étiquette. La direction « perturbation »
   n'utilise même pas l'injectivité ; la direction « regroupement » l'utilise
   avec le témoin `k := i` (aucune hypothèse d'existence d'un tiers).

3. **Dynamics — éq. 16 et invariant de compétition** (Appendice C, éq. 10).
   Pour la perte quadratique localisée du papier, le forçage externe du
   gradient flow est **common-mode** : il s'annule dans la différence des
   trajectoires, dont la séparation `r = x₁ − x₂` évolue de façon autonome
   (`rel_eqn_autonomous`). Sur le système réduit `a₂, c`, la quantité
   `η_x a₂² − 2 η_A c²` est **conservée** (`competition_invariant`) : c'est le
   cœur quantitatif du Theorem 3 (taux d'apprentissage critiques), la
   compétition entre la croissance du canal `a₂` et la séparation `c` étant
   arbitrée par cet invariant.

Hors scope V1 (cité pour honnêteté, cf. lignes du papier) : le calcul concret
de `|Aut|` pour le tournoi de l'ordre total (`|Aut| = 1`, b = log₂ n!) et le
graphe biparti complet `K_{a,c}` (`|Aut| = a!·c!`, b ≈ k·n) — chaque borne
demande un argument de degré dédié ; le Theorem 2 (convergence, asymptotique) ;
la dérivation stochastique balls-in-buckets (éq. 8). -/

namespace GenEFT

/-! ## Section 1 — Statics : description length par orbite-stabilizer -/

section Statics

variable {n : ℕ}

/-- Le **re-labellage** d'un graphe par une permutation `σ` des sommets :
l'arête `i—j` existe dans `σ • G` ssi `σ⁻¹ i — σ⁻¹ j` existe dans `G`.
C'est l'action naturelle du groupe symétrique sur les structures de graphe. -/
instance permSmul : SMul (Equiv.Perm (Fin n)) (SimpleGraph (Fin n)) where
  smul σ G :=
    { Adj := fun i j => G.Adj (σ.symm i) (σ.symm j)
      symm := by
        apply Std.Symm.mk
        intro i j h
        exact G.symm.symm (σ.symm i) (σ.symm j) h
      loopless := by
        apply Std.Irrefl.mk
        intro i h
        exact G.loopless.irrefl (σ.symm i) h }

/-- `Equiv.Perm (Fin n)` agit sur les graphes sur `Fin n` par re-labellage :
le groupe symétrique effectue les renommages de sommets. -/
instance : MulAction (Equiv.Perm (Fin n)) (SimpleGraph (Fin n)) where
  one_smul G := by
    ext i j
    have hone : ∀ x, (1 : Equiv.Perm (Fin n)).symm x = x := by
      intro x
      rw [show ((1 : Equiv.Perm (Fin n)).symm) = 1 from inv_one]
      exact Equiv.Perm.one_apply x
    show G.Adj ((1 : Equiv.Perm (Fin n)).symm i) ((1 : Equiv.Perm (Fin n)).symm j) ↔ G.Adj i j
    rw [hone i, hone j]
  mul_smul σ τ G := by
    ext i j
    have hst : ∀ x, (σ * τ).symm x = τ.symm (σ.symm x) := by
      intro x
      rw [show (σ * τ).symm = τ.symm * σ.symm from mul_inv_rev σ τ]
      simp [Equiv.Perm.mul_apply]
    show G.Adj ((σ * τ).symm i) ((σ * τ).symm j) ↔
      G.Adj (τ.symm (σ.symm i)) (τ.symm (σ.symm j))
    rw [hst i, hst j]

/-- **Pont avec la définition usuelle** : une permutation est dans le
stabilisateur (l'« automate » du graphe, `Aut G`) **ssi** elle préserve
l'adjacence dans les deux sens — le stabilisateur du re-labellage EST le
groupe d'automorphismes du graphe. -/
theorem mem_aut_iff {G : SimpleGraph (Fin n)} (σ : Equiv.Perm (Fin n)) :
    σ ∈ MulAction.stabilizer (Equiv.Perm (Fin n)) G ↔
      ∀ i j, G.Adj i j ↔ G.Adj (σ i) (σ j) := by
  constructor
  · intro h i j
    have hsmul : σ • G = G := h
    constructor
    · intro hij
      have h3 : (σ • G).Adj (σ i) (σ j) := by
        show G.Adj (σ.symm (σ i)) (σ.symm (σ j))
        simpa using hij
      rw [hsmul] at h3
      exact h3
    · intro hij
      -- l'égalité de graphes σ • G = G transportée au couple (σ i, σ j)
      have hAdjeq : (σ • G).Adj = G.Adj := SimpleGraph.ext_iff.mp hsmul
      have h4 : (σ • G).Adj (σ i) (σ j) := by rw [hAdjeq]; exact hij
      have h5 : (σ • G).Adj (σ i) (σ j) ↔ G.Adj i j := by
        show G.Adj (σ.symm (σ i)) (σ.symm (σ j)) ↔ G.Adj i j
        simp
      exact h5.mp h4
  · intro h
    show σ • G = G
    ext i j
    show G.Adj (σ.symm i) (σ.symm j) ↔ G.Adj i j
    simpa using h (σ.symm i) (σ.symm j)

/-- **Orbit-stabilizer pour les graphes** (Section III du papier) : le nombre
de graphes de même structure que `G` (son orbite sous re-labellage) fois le
nombre d'automorphismes de `G` (son stabilisateur) égale `n!`. Encoder la
structure, c'est choisir un point de l'orbite. -/
theorem card_orbit_mul_card_aut (G : SimpleGraph (Fin n))
    [Fintype (MulAction.orbit (Equiv.Perm (Fin n)) G)]
    [Fintype ↥(MulAction.stabilizer (Equiv.Perm (Fin n)) G)] :
    Fintype.card (MulAction.orbit (Equiv.Perm (Fin n)) G) *
      Fintype.card (MulAction.stabilizer (Equiv.Perm (Fin n)) G) =
        Fintype.card (Equiv.Perm (Fin n)) := by
  exact MulAction.card_orbit_mul_card_stabilizer_eq_card_group
    (G := Equiv.Perm (Fin n)) G

/-- La **longueur de description** du graphe `G` (éq. 4 du papier) : le log
en base 2 de la taille de l'orbite de re-labellage, `b = log₂ (n! / |Aut G|)`.
C'est le nombre de bits du « plus court programme » qui produit `G` à
structure près. -/
noncomputable def descLength (G : SimpleGraph (Fin n))
    [Fintype (MulAction.orbit (Equiv.Perm (Fin n)) G)] : ℝ :=
  Real.logb 2 (Fintype.card (MulAction.orbit (Equiv.Perm (Fin n)) G))

/-- `descLength` sous forme de quotient : `b = log₂ (n! / |Aut G|)` — la
forme utilisée dans le papier (Section III). -/
theorem descLength_eq (G : SimpleGraph (Fin n))
    [Fintype (MulAction.orbit (Equiv.Perm (Fin n)) G)]
    [Fintype ↥(MulAction.stabilizer (Equiv.Perm (Fin n)) G)] :
    descLength G =
      Real.logb 2 (Fintype.card (Equiv.Perm (Fin n)) /
        Fintype.card (MulAction.stabilizer (Equiv.Perm (Fin n)) G)) := by
  have h := card_orbit_mul_card_aut G
  -- le stabilisateur contient l'identité, donc est non vide et de cardinal > 0
  have hcardpos : 0 < Fintype.card (MulAction.stabilizer (Equiv.Perm (Fin n)) G) :=
    Fintype.card_pos_iff.2 ⟨⟨1, one_smul _ G⟩⟩
  have haut : (Fintype.card (MulAction.stabilizer (Equiv.Perm (Fin n)) G) : ℝ) ≠ 0 :=
    ne_of_gt (by exact_mod_cast hcardpos)
  unfold descLength
  congr 1
  rw [eq_div_iff haut]
  exact_mod_cast h

end Statics

/-! ## Section 2 — Theorem 1 : clustering par décodeur injectif -/

section Clustering

variable {ι V : Type*}

/-- **Theorem 1 du papier (cœur quantitatif)** : un autoencoder de
classification — entrée `(E i, E k)` (les embeddings de deux noeuds), sortie
`dec` valant `1` si même classe et `0` sinon — dont la perte d'entraînement
est **nulle** (chaque paire est correctement classée, hypothèse `hLoss`) et
dont le décodeur est **injectif** (`hInj`) **clusterise exactement les
classes** : deux noeuds ont le même embedding **si et seulement si** ils ont
la même étiquette.

La direction `←` (même classe ⟹ même embedding) est celle qui demande
l'injectivité, avec le témoin `k := i` — aucune existence de tiers n'est
requise. La direction `→` (embeddings égaux, classes différentes ⟹
contradiction) n'utilise que la correction des labels sur la paire `(i, i)`. -/
theorem clustering (label : ι → Bool) (E : ι → V) (dec : V × V → ℝ)
    (hInj : Function.Injective dec)
    (hLoss : ∀ i k, dec (E i, E k) = if label i = label k then 1 else 0) :
    ∀ i j, E i = E j ↔ label i = label j := by
  have h0 : ∀ i k, dec (E i, E k)
      = if (label i).toNat = (label k).toNat then 1 else 0 := by
    intro i k
    cases li : label i <;> cases lk : label k <;>
      rw [hLoss i k] <;> simp [li, lk]
  have htoNat_inj : ∀ a b : Bool, a.toNat = b.toNat → a = b := by
    intro a b hab
    cases a <;> cases b <;> simp_all [Bool.toNat]
  have key := LearningTheory.EffectiveTheory.clustering_iff_injective_decoder
    E dec (fun i => (label i).toNat) hInj h0
  intro i j
  constructor
  · intro hE
    exact htoNat_inj (label i) (label j) ((key i j).mpr hE)
  · intro hlab
    exact (key i j).mp (congrArg Bool.toNat hlab)

end Clustering

/-! ## Section 3 — Dynamics : éq. 16 (autonomie) et éq. 10 (invariant) -/

section Dynamics

/-- **Éq. 10 — l'invariant de la compétition.** Sur le système réduit du
papier (Appendice C), le canal `a₂` et la séparation `c` évoluent par
`da₂/dt = -2 η_A c² a₂` et `dc/dt = -η_x a₂² c` : chacun inhibe la croissance
de l'autre. La quantité `η_x a₂² - 2 η_A c²` est **constante le long des
trajectoires** — c'est cet invariant qui arbitre la compétition et produit
les taux d'apprentissage critiques du Theorem 3. -/
theorem competition_invariant (ηx ηA : ℝ) (a₂ c : ℝ → ℝ)
    (ha : ∀ t, HasDerivAt a₂ (-(2 * ηA) * (c t ^ 2) * a₂ t) t)
    (hc : ∀ t, HasDerivAt c (-(ηx) * (a₂ t ^ 2) * c t) t) (t : ℝ) :
    HasDerivAt (fun t => ηx * a₂ t ^ 2 - 2 * ηA * c t ^ 2) 0 t := by
  rcases eq_or_ne ηx 0 with rfl | hηx
  · -- ηx = 0 : dc/dt = 0, la quantité se réduit à -2 ηA c², dérivée nulle
    -- (rfl a substitué ηx := 0 partout : les types ci-dessous s'écrivent avec le littéral)
    have hfun : (fun t => (0:ℝ) * a₂ t ^ 2 - 2 * ηA * c t ^ 2)
        = fun t => -(2 * ηA) * c t ^ 2 := by
      funext s; simp
    rw [hfun]
    have hc' : ∀ s, HasDerivAt c 0 s := by
      intro s; simpa using hc s
    refine (((hc' t).pow 2).const_mul (-(2 * ηA))).congr_deriv ?_
    simp
  rcases eq_or_ne ηA 0 with rfl | hηA
  · -- ηA = 0 : da₂/dt = 0, la quantité se réduit à ηx a₂², dérivée nulle
    have hfun : (fun t => ηx * a₂ t ^ 2 - 2 * (0:ℝ) * c t ^ 2)
        = fun t => ηx * a₂ t ^ 2 := by
      funext s; simp
    rw [hfun]
    have ha' : ∀ s, HasDerivAt a₂ 0 s := by
      intro s; simpa using ha s
    refine (((ha' t).pow 2).const_mul ηx).congr_deriv ?_
    simp
  -- cas générique (ηx ≠ 0, ηA ≠ 0) : délégation à l'organe — l'invariant
  -- normalisé C = a₂²/(2ηA) − c²/ηx vit dans EffectiveTheory.Repons ;
  -- notre forme n'en est que le multiple 2 ηA ηx · C.
  -- l'organe attend la forme -2 * ηA * ..., la nôtre est -(2 * ηA) * ... (même terme à ring près)
  have ha' : ∀ t, HasDerivAt a₂ (-2 * ηA * (c t) ^ 2 * a₂ t) t :=
    fun t => (ha t).congr_deriv (by ring)
  have hC := LearningTheory.EffectiveTheory.conservedHyperbola_deriv_zero
    (ηA := ηA) (ηx := ηx) hηA hηx ha' hc t
  have hfun : (fun s => ηx * a₂ s ^ 2 - 2 * ηA * c s ^ 2)
      = fun y => 2 * ηA * ηx * (a₂ y ^ 2 / (2 * ηA) - c y ^ 2 / ηx) := by
    funext s; field_simp
  rw [hfun]
  exact ((hC.const_mul (2 * ηA * ηx)).congr_deriv (by simp))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Éq. 16 de l'Appendice C — autonomie de la séparation.** Dans le
gradient flow du papier, chaque trajectoire subit le même forçage externe
`g` (le terme de rappel vers la cible, porté par `Aᵀ y`) en plus du flux
linéaire `F` (le terme `-η_x AᵀA`). Ce forçage est **common-mode** : dans la
différence `x₁ - x₂`, il s'annule exactement, et la séparation évolue de
façon autonome — ressort de Hooke `d(x₁ - x₂)/dt = F (x₁ - x₂)` avec
`F = -η_x AᵀA` affaiblissant. -/
theorem rel_eqn_autonomous (x₁ x₂ : ℝ → E) (F : E →L[ℝ] E) (g : ℝ → E)
    (h₁ : ∀ t, HasDerivAt x₁ (F (x₁ t) + g t) t)
    (h₂ : ∀ t, HasDerivAt x₂ (F (x₂ t) + g t) t) (t : ℝ) :
    HasDerivAt (fun t => x₁ t - x₂ t) (F (x₁ t - x₂ t)) t := by
  have hd : HasDerivAt (fun t => x₁ t - x₂ t)
      ((F (x₁ t) + g t) - (F (x₂ t) + g t)) t :=
    (h₁ t).sub (h₂ t)
  convert hd using 2
  simp only [ContinuousLinearMap.map_sub]
  abel

end Dynamics

end GenEFT
