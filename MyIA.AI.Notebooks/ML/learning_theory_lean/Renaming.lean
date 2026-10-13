import MathUniverse

/-!
# Renaming — l'équivalence de structures sous renommage (R16 §III « baggage »)

Suite du module `MathUniverse` sur l'issue **#16753** (Annexe A de R16 —
*The Mathematical Universe*, Tegmark). `MathUniverse` a défini la structure
relationnelle finie (`FinRelStruct`), le groupe `aut` et la décidabilité de
l'équivalence `EquivStruct` par énumération des tableaux. Cette tranche
formalise ce que le §III du papier appelle le **baggage** : les noms des
éléments ne font pas partie de la structure — renommer les entités d'une
définition donne *la même* structure, et c'est précisément cette équivalence
sous renommage que l'algorithme haltant de l'Annexe A décide.

Contenu distillé :

1. **`EquivStruct` est une équivalence** (`equivStruct_refl`, `equivStruct_symm`,
   `equivStruct_trans`) — réflexive, symétrique, transitive à travers les types
   porteurs : la relation d'« être deux définitions de la même structure ».
2. **Invariants de cardinalité** : l'équivalence exige des porteurs équipotents
   (`equivStruct_card_eq` — C₂ et C₃ ne sont PAS équivalents : 2 ≠ 3, théorème
   et confirmation par le noyau) et préserve la taille de chaque tableau de
   relation (`equivStruct_rel_card` via `relFinset`) — deux structures
   équipotentes de même signature peuvent néanmoins être distinguées : `c3`
   (table d'addition de Z/3) contre `point3` (structure pointée), `c2` contre
   `diag2` (diagonale). Le discrimination est visible dans la sortie :
   `decide` rend `false` sans témoin fourni.
3. **Le renommage est une énumération de permutations**
   (`equivStruct_iff_perm`) : sur un même porteur, décider l'équivalence
   revient à parcourir les `m!` permutations et non les `m^m` applications —
   l'écart entre la formulation générale (bijection entre porteurs distincts)
   et le cas concret du renommage d'un même ensemble d'entités.
4. **Le torseur des renommages sous Aut(S)** : deux isomorphismes diffèrent
   d'un automorphisme (`iso_symm_mul_aut`), Aut(S) agit à droite sur les
   isomorphismes (`iso_mul_aut`), et l'appartenance à Aut se transporte par
   conjugaison (`mem_aut_conj_iff`) — corollaire : toute structure équivalente
   à l'algèbre de Boole à deux éléments a un groupe d'automorphismes trivial
   (`aut_trivial_of_equiv_bool8`). C'est le pont vers
   `EffectiveTheory.InfoBits` (`b = log₂(n!/|Aut G|)`) : le contenu
   informationnel est un invariant du renommage.

Source PDF (GDrive, sha8) : R16 `85712871`. Twin anglais `Renaming_en`
(Epic #4980).
-/

namespace MathUniverse.Renaming

open MathUniverse (FinRelStruct EquivStruct aut Preserves mem_aut_iff)
open MathUniverse.Examples (c2 c3 bool8 bool8Sig c2Sig c3Sig aut_bool8_trivial)

section
variable {α : Type*} {β : Type*} {γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  {n : ℕ} {σ : Fin n → ℕ}

/-! ## 1. `EquivStruct` est une équivalence à travers les types -/

/-- Réflexivité : toute structure est équivalente à elle-même — l'identité
est le témoin. -/
theorem equivStruct_refl (S : FinRelStruct α σ) : EquivStruct S S :=
  ⟨Equiv.refl α, fun _ _ => Iff.rfl⟩

/-- Symétrie : si `f` transporte les relations de `S` sur celles de `T`,
alors `f.symm` transporte celles de `T` sur celles de `S`. -/
theorem equivStruct_symm {S : FinRelStruct α σ} {T : FinRelStruct β σ}
    (h : EquivStruct S T) : EquivStruct T S := by
  obtain ⟨f, hrel⟩ := h
  refine ⟨f.symm, fun i t => ?_⟩
  have key := hrel i (f.symm ∘ t)
  rw [show ⇑f ∘ (⇑f.symm ∘ t) = t from
    funext fun x => f.apply_symm_apply (t x)] at key
  exact key.symm

/-- Transitivité : composer les témoins compose les équivalences. -/
theorem equivStruct_trans {S : FinRelStruct α σ} {T : FinRelStruct β σ}
    {U : FinRelStruct γ σ} (h₁ : EquivStruct S T) (h₂ : EquivStruct T U) :
    EquivStruct S U := by
  obtain ⟨f, hf⟩ := h₁
  obtain ⟨g, hg⟩ := h₂
  exact ⟨f.trans g, fun i t => (hf i t).trans (hg i (f ∘ t))⟩

/-! ## 2. Invariants : cardinalités et taille des tableaux -/

/-- L'équivalence exige des porteurs équipotents : le témoin EST un
equipotent. Première barrière à croiser avant toute comparaison de
tableaux. -/
theorem equivStruct_card_eq {S : FinRelStruct α σ} {T : FinRelStruct β σ}
    (h : EquivStruct S T) : Fintype.card α = Fintype.card β := by
  obtain ⟨f, _⟩ := h
  exact Fintype.card_congr f

/-- Le tableau d'une relation, comme ensemble fini de uplets : la donnée
effective que le §A.2 du papier appelle « spécifier la structure par ses
tableaux ». La décidabilité vient du champ `rel_dec` (passé explicitement :
un champ de structure n'est pas une instance). -/
def relFinset (S : FinRelStruct α σ) (i : Fin n) [DecidableEq α]
    (d : ∀ t : Fin (σ i) → α, Decidable (S.rel i t)) :
    Finset (Fin (σ i) → α) :=
  @Finset.filter _ (fun t => S.rel i t) d Finset.univ

/-- **La taille d'un tableau est un invariant du renommage** : si `S` et `T`
sont équivalentes, chaque relation occupe le même nombre de lignes dans son
tableau — le témoin transporte les uplets un à un. -/
theorem equivStruct_rel_card {S : FinRelStruct α σ} {T : FinRelStruct β σ}
    (h : EquivStruct S T) (i : Fin n) [DecidableEq α] [DecidableEq β]
    (dS : ∀ t : Fin (σ i) → α, Decidable (S.rel i t))
    (dT : ∀ t : Fin (σ i) → β, Decidable (T.rel i t)) :
    (relFinset S i dS).card = (relFinset T i dT).card := by
  obtain ⟨f, hrel⟩ := h
  have hinjF : Function.Injective (fun t : Fin (σ i) → α => f ∘ t) :=
    fun t₁ t₂ ht => funext fun j => f.injective (congrFun ht j)
  have hinjS : Function.Injective (fun u : Fin (σ i) → β => f.symm ∘ u) :=
    fun u₁ u₂ ht => funext fun j => f.symm.injective (congrFun ht j)
  have hST : (relFinset S i dS).image (fun t => f ∘ t) ⊆ relFinset T i dT := by
    intro u hu
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hu
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hrel i t).mp (Finset.mem_filter.mp ht).2⟩
  have hTS : (relFinset T i dT).image (fun u => f.symm ∘ u) ⊆ relFinset S i dS := by
    intro t ht
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have hiff := hrel i (f.symm ∘ u)
    rw [show ⇑f ∘ (⇑f.symm ∘ u) = u from
      funext fun x => f.apply_symm_apply (u x)] at hiff
    exact hiff.mpr (Finset.mem_filter.mp hu).2
  refine le_antisymm ?_ ?_
  · calc (relFinset S i dS).card
        = ((relFinset S i dS).image (fun t => f ∘ t)).card :=
          (Finset.card_image_of_injOn fun a _ b _ hab => hinjF hab).symm
    _ ≤ (relFinset T i dT).card := Finset.card_le_card hST
  · calc (relFinset T i dT).card
        = ((relFinset T i dT).image (fun u => f.symm ∘ u)).card :=
          (Finset.card_image_of_injOn fun a _ b _ hab => hinjS hab).symm
    _ ≤ (relFinset S i dS).card := Finset.card_le_card hTS

/-! ## 3. Le renommage est une énumération de permutations -/

/-- Sur un même porteur, l'équivalence se décide en parcourant les
**permutations** (`m!` candidats) et non les applications (`m^m`) : le
renommage d'un ensemble d'entités fixé est exactement le conjugué
opérationnel de « deux définitions décrivent la même structure ». -/
theorem equivStruct_iff_perm (S T : FinRelStruct α σ) [DecidableEq α] :
    EquivStruct S T ↔
      ∃ p : Equiv.Perm α, ∀ i (t : Fin (σ i) → α), S.rel i t ↔ T.rel i (p ∘ t) := by
  constructor
  · exact fun ⟨f, h⟩ => ⟨f, h⟩
  · exact fun ⟨p, h⟩ => ⟨p, h⟩

/-! ## 4. Le torseur des renommages sous Aut(S) -/

/-- Le témoin déplié d'un isomorphisme de `S` sur `T` porté par la
permutation `p` : chaque relation de `S` se lit comme celle de `T` après
renommage par `p`. -/
def IsoWit (S T : FinRelStruct α σ) (p : Equiv.Perm α) : Prop :=
  ∀ i (t : Fin (σ i) → α), S.rel i t ↔ T.rel i (p ∘ t)

/-- **Aut(S) agit à droite sur les isomorphismes** : composer un isomorphisme
avec un automorphisme (côté source) donne un isomorphisme. -/
theorem iso_mul_aut {S T : FinRelStruct α σ} {p : Equiv.Perm α}
    (hp : IsoWit S T p) {g : Equiv.Perm α} (hg : g ∈ aut S) :
    IsoWit S T (p * g) := by
  intro i t
  have h1 : S.rel i t ↔ S.rel i (g ∘ t) := (mem_aut_iff S g).mp hg i t
  have h2 : S.rel i (g ∘ t) ↔ T.rel i (p ∘ (g ∘ t)) := hp i (g ∘ t)
  rw [show ⇑(p * g) ∘ t = p ∘ (g ∘ t) from funext fun j => rfl]
  exact h1.trans h2

/-- **Deux isomorphismes diffèrent d'un automorphisme** : le quotient
`p₁⁻¹ * p₂` préserve `S`. C'est le torseur — l'ensemble des renommages qui
identifient `S` à `T` est un torseur principal sous `Aut(S)`, dont la
cardinalité (l'invariant `|Aut S|` de `EffectiveTheory.InfoBits`) ne dépend
pas du témoin choisi. -/
theorem iso_symm_mul_aut {S T : FinRelStruct α σ} {p₁ p₂ : Equiv.Perm α}
    (h₁ : IsoWit S T p₁) (h₂ : IsoWit S T p₂) : p₁⁻¹ * p₂ ∈ aut S := by
  rw [mem_aut_iff]
  intro i t
  have hA : S.rel i t ↔ T.rel i (p₂ ∘ t) := h₂ i t
  have hB := h₁ i (⇑(p₁⁻¹) ∘ ⇑p₂ ∘ t)
  rw [show ⇑p₁ ∘ (⇑(p₁⁻¹) ∘ ⇑p₂ ∘ t) = ⇑p₂ ∘ t from
    funext fun j => p₁.apply_symm_apply (p₂ (t j))] at hB
  rw [show ⇑(p₁⁻¹ * p₂) ∘ t = ⇑(p₁⁻¹) ∘ ⇑p₂ ∘ t from funext fun j => rfl]
  exact hA.trans hB.symm

omit [Fintype α] in
/-- La conjugaison d'une permutation par une autre, point par point :
`(e * p * e⁻¹) x = e (p (e.symm x))` — lemme technique pour le transport
de `aut` par renommage. -/
private theorem coe_conj_apply (e p : Equiv.Perm α) (x : α) :
    (e * p * e⁻¹) x = e (p (e.symm x)) := by
  simp only [Equiv.Perm.inv_def, Equiv.Perm.mul_apply]

/-- **L'appartenance à Aut se transporte par conjugaison** : conjuguer un
automorphisme de `S` par un isomorphisme `S → T` donne un automorphisme de
`T`, et réciproquement. Le groupe d'automorphismes est un invariant du
renommage — pas un artefact de la définition. -/
theorem mem_aut_conj_iff {S T : FinRelStruct α σ} {e : Equiv.Perm α}
    (he : IsoWit S T e) (p : Equiv.Perm α) :
    p ∈ aut S ↔ e * p * e⁻¹ ∈ aut T := by
  constructor
  · intro hp
    rw [mem_aut_iff]
    intro i t
    have hE := he i (fun j => e.symm (t j))
    rw [show ⇑e ∘ (fun j => e.symm (t j)) = t from
      funext fun j => e.apply_symm_apply (t j)] at hE
    have hP := (mem_aut_iff S p).mp hp i (fun j => e.symm (t j))
    have hE' := he i (fun j => p (e.symm (t j)))
    rw [show ⇑(e * p * e⁻¹) ∘ t = fun j => e (p (e.symm (t j))) from
      funext fun j => coe_conj_apply e p (t j)]
    exact (hE.symm.trans hP).trans hE'
  · intro hq
    rw [mem_aut_iff]
    intro i t
    have hE : S.rel i t ↔ T.rel i (e ∘ t) := he i t
    have hQ := (mem_aut_iff T (e * p * e⁻¹)).mp hq i (e ∘ t)
    rw [show ⇑(e * p * e⁻¹) ∘ (⇑e ∘ t) = ⇑e ∘ (⇑p ∘ t) from
      funext fun j => by
        simp only [Function.comp_apply, coe_conj_apply, e.symm_apply_apply]] at hQ
    have hE' := he i (p ∘ t)
    exact (hE.trans hQ).trans hE'.symm

/-- **Corollaire (le pont InfoBits)** : toute structure équivalente à
l'algèbre de Boole à deux éléments a un groupe d'automorphismes trivial.
Le « 1 bit » de `b = log₂(n!/|Aut G|)` se transporte par renommage :
l'information est dans la structure, pas dans les noms. -/
theorem aut_trivial_of_equiv_bool8 {T : FinRelStruct Bool bool8Sig}
    (h : EquivStruct bool8 T) {q : Equiv.Perm Bool} (hq : q ∈ aut T) : q = 1 := by
  obtain ⟨f, hrel⟩ := h
  have hqP : Preserves T q := (mem_aut_iff T q).mp hq
  -- le conjugué x ↦ f.symm (q (f x)) préserve bool8
  have key : ∀ i (t : Fin (bool8Sig i) → Bool),
      bool8.rel i t ↔ bool8.rel i (fun j => f.symm (q (f (t j)))) := by
    intro i t
    have h1 : bool8.rel i t ↔ T.rel i (f ∘ t) := hrel i t
    have h2 : T.rel i (f ∘ t) ↔ T.rel i (q ∘ (f ∘ t)) := hqP i (f ∘ t)
    have h3 := hrel i (fun j => f.symm (q (f (t j))))
    rw [show ⇑f ∘ (fun j => f.symm (q (f (t j)))) = q ∘ f ∘ t from
      funext fun j => f.apply_symm_apply (q (f (t j)))] at h3
    exact h1.trans (h2.trans h3.symm)
  have hconj : (f.trans (q.trans f.symm) : Equiv.Perm Bool) ∈ aut bool8 := by
    rw [mem_aut_iff]
    intro i t
    rw [show ⇑(f.trans (q.trans f.symm) : Equiv.Perm Bool) ∘ t
          = fun j => f.symm (q (f (t j))) from
      funext fun j => by simp]
    exact key i t
  have h1 : (f.trans (q.trans f.symm) : Equiv.Perm Bool) = 1 :=
    aut_bool8_trivial _ hconj
  have hcoe : ∀ x : Bool, f.symm (q (f x)) = x := by
    intro x
    have hx := congrArg (fun w : Equiv.Perm Bool => w x) h1
    simpa [Equiv.Perm.coe_one] using hx
  ext z
  obtain ⟨y, hy⟩ := f.surjective z
  have hz1 : f.symm (q z) = y := by rw [← hy, hcoe y]
  have hz2 : f.symm z = y := by rw [← hy, f.symm_apply_apply]
  have hz : q z = z := f.symm.injective (by rw [hz1, hz2])
  simpa [Equiv.Perm.coe_one] using hz

end

/-! ## 5. Exemples : le discrimination par invariants et par le noyau -/

namespace Examples

/-- **C₂ ≇ C₃** : l'invariant de cardinalité suffit — 2 ≠ 3, il n'existe
pas d'equipotent `Bool ≃ Fin 3`. -/
theorem not_equivStruct_c2_c3 : ¬ EquivStruct c2 c3 := by
  intro h
  have hc := equivStruct_card_eq h
  rw [show Fintype.card Bool = 2 from by decide, Fintype.card_fin] at hc
  exact absurd hc (by decide)

/-- Le noyau le retrouve : l'énumération des tableaux de l'Annexe A rend
`false` sans témoin fourni. -/
example : ¬ EquivStruct c2 c3 := by decide +kernel

/-- Structure **pointée** sur `Fin 3` : une seule relation ternaire ne
contenant que le triplet `(0, 0, 0)` — même cardinal que `c3`, même
signature, table de taille différente. -/
def point3 : FinRelStruct (Fin 3) c3Sig where
  rel := fun _ t => t 0 = 0 ∧ t 1 = 0 ∧ t 2 = 0
  rel_dec := fun i _ =>
    match i with
    | 0 => inferInstance

/-- Structure **diagonale** sur `Bool` : la relation ne retient que les
triplets `(b, b, b)` — même cardinal (2) et même signature que `c2`, table
de taille différente. -/
def diag2 : FinRelStruct Bool c2Sig where
  rel := fun _ t => t 0 = t 1 ∧ t 1 = t 2
  rel_dec := fun i _ =>
    match i with
    | 0 => inferInstance

/-- La table d'addition de Z/3 compte neuf triplets (un résultat par
couple d'opérandes). -/
theorem card_rel_c3 : (relFinset c3 (0 : Fin 1) (c3.rel_dec 0)).card = 9 := by decide

/-- La structure pointée ne compte qu'un triplet. -/
theorem card_rel_point3 : (relFinset point3 (0 : Fin 1) (point3.rel_dec 0)).card = 1 := by
  decide

/-- La table d'addition de Z/2 compte quatre triplets. -/
theorem card_rel_c2 : (relFinset c2 (0 : Fin 1) (c2.rel_dec 0)).card = 4 := by decide

/-- La diagonale de `Bool` ne compte que deux triplets. -/
theorem card_rel_diag2 : (relFinset diag2 (0 : Fin 1) (diag2.rel_dec 0)).card = 2 := by
  decide

/-- **C₃ ≇ point3** : équipotents, même signature — distingués par la
taille du tableau (l'invariant `equivStruct_rel_card`). -/
theorem not_equivStruct_c3_point3 : ¬ EquivStruct c3 point3 := by
  intro h
  have hc := equivStruct_rel_card h (0 : Fin 1) (c3.rel_dec 0) (point3.rel_dec 0)
  rw [card_rel_c3, card_rel_point3] at hc
  exact absurd hc (by decide)

/-- **C₂ ≇ diag2** : même porteur, même signature — distingués par la
taille du tableau (quatre contre deux). -/
theorem not_equivStruct_c2_diag2 : ¬ EquivStruct c2 diag2 := by
  intro h
  have hc := equivStruct_rel_card h (0 : Fin 1) (c2.rel_dec 0) (diag2.rel_dec 0)
  rw [card_rel_c2, card_rel_diag2] at hc
  exact absurd hc (by decide)

/-- Le noyau confirme les deux discriminations sans témoin fourni. -/
example : ¬ EquivStruct c3 point3 := by decide +kernel

example : ¬ EquivStruct c2 diag2 := by decide +kernel

end Examples

end MathUniverse.Renaming
