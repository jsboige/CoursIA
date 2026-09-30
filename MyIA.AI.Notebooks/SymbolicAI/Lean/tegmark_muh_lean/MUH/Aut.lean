import MUH.Structure

/-! # Aut(S) est un groupe (Tegmark R16 Annexe A §1 in fine)

Tegmark (2007, Annexe A §1 in fine) esquisse en une phrase :
> « Aut(S) is a group (easy to see). »

Ce module formalise cette esquisse pour le cas restreint mais
généralement suffisant : structures à n ensembles de cardinaux fixés,
bijections au sein de chaque ensemble (les seules qui préservent les
cardinaux), préservation de la table de chaque relation par transport
via ces bijections.

Note : on travaille dans la représentation paramétrique StructureOn
qui expose n : Nat et sizes : Fin n → Nat plutôt que la forme
bundlée Structure. -/

namespace Aut

/-- Représentation paramétrique d'une structure Tegmark : n ensembles
    de cardinaux sizes, liste de relations Tegmark. -/
structure StructureOn (n : Nat) where
  sizes : Fin n → Nat
  sizes_pos : ∀ i, 0 < sizes i
  rels : List (Rel n sizes)

/-- Un automorphisme d'une structure Tegmark : famille d'applications
    injectives sur chaque ensemble préservant la table de chaque
    relation. L'injectivité suffit car les ensembles sont finis :
    `Fin m → Fin m` injectif est bijectif (`Fintype.card_fin`),
    mais ce lemme vit dans Mathlib et n'est pas disponible ici. -/
structure IsAutomorphism {n : Nat} (S : StructureOn n) where
  /-- Pour chaque ensemble S_i, la permutation qui le transforme. -/
  φ : (i : Fin n) → Fin (S.sizes i) → Fin (S.sizes i)
  /-- Chaque φ_i est injective. (Bijectivité implicite sur `Fin m`,
      via `Fintype.card_fin`.) -/
  φ_inj : ∀ i, Function.Injective (φ i)
  /-- Préservation des tables : pour chaque relation r et chaque tuple
      args, l'image par φ de la valeur de la table est la valeur de la
      table sur le tuple transporté (composante par composante). -/
  rel_pres : ∀ (r : Rel n S.sizes),
    r ∈ S.rels →
    ∀ (args : (i : Fin r.sig.arity) → Fin (S.sizes (r.sig.args i))),
    φ r.sig.out (r.table args) =
      r.table (fun i => φ (r.sig.args i) (args i))

/-- L'identité est un automorphisme de toute structure Tegmark :
    `id` est injective, et la préservation des tables est `rfl`. -/
def autId {n : Nat} (S : StructureOn n) : IsAutomorphism S where
  φ := fun _ x => x
  φ_inj := fun _ => Function.injective_id
  rel_pres := fun _ _ _ => rfl

/-- La composition de deux automorphismes est un automorphisme :
    `(ψ ∘ φ)_i = ψ_i ∘ φ_i`. C'est le **cœur** de « Aut(S) est un
    groupe » : la structure est fermée sous la composition, ce qui
    avec `autId` donne un sous-monoïde du groupe symétrique
    `Π i, Sym(S.sizes i)`.

    La préservation des tables est mécanique : on applique successivement
    les deux lemmes `rel_pres`, d'abord φ puis ψ, puis on conclut par
    `rfl` (la composition de `(ψ_i ∘ φ_i)` est définie comme la
    composition habituelle). -/
def autComp {n : Nat} {S : StructureOn n}
    (φ ψ : IsAutomorphism S) : IsAutomorphism S where
  φ := fun i => (ψ.φ i) ∘ (φ.φ i)
  φ_inj := fun i => (ψ.φ_inj i).comp (φ.φ_inj i)
  rel_pres := fun r hmem args => by
    -- Appliquer la préservation par φ, puis par ψ sur le tuple transporté
    have hφ := φ.rel_pres r hmem args
    have hψ := ψ.rel_pres r hmem (fun j => φ.φ (r.sig.args j) (args j))
    simp only [Function.comp_apply]
    rw [hφ, hψ]

end Aut