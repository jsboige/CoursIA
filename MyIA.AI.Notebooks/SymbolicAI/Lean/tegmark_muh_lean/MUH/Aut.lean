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

/-- La composition est associative : `(χ ∘ ψ) ∘ φ = χ ∘ (ψ ∘ φ)`.
    C'est l'associativité de `Function.comp`, par `rfl`. -/
theorem autComp_assoc {n : Nat} {S : StructureOn n}
    (φ ψ χ : IsAutomorphism S) :
    autComp (autComp φ ψ) χ = autComp φ (autComp ψ χ) := by
  cases φ; cases ψ; cases χ; rfl

/-- Neutre à gauche : `autId ∘ φ = φ` (car `id ∘ f = f` par `rfl`). -/
theorem autId_comp {n : Nat} {S : StructureOn n} (φ : IsAutomorphism S) :
    autComp (autId S) φ = φ := by
  cases φ; rfl

/-- Neutre à droite : `φ ∘ autId = φ` (car `f ∘ id = f` par `rfl`). -/
theorem comp_autId {n : Nat} {S : StructureOn n} (φ : IsAutomorphism S) :
    autComp φ (autId S) = φ := by
  cases φ; rfl

/-- Deux automorphismes de même composante `φ` sont égaux : les champs de
    preuve (`φ_inj`, `rel_pres`) suivent par `subst` puis irrélevance des
    preuves. C'est l'outil clé des théorèmes d'unicité (voir MUH.Examples). -/
theorem isAuto_eq {n : Nat} {S : StructureOn n} {φ ψ : IsAutomorphism S}
    (h : φ.φ = ψ.φ) : φ = ψ := by
  cases φ; cases ψ
  cases h
  rfl

end Aut

/-! ## Le groupe Aut(S) (Tegmark R16 Annexe A §1 in fine)

Tegmark : « Aut(S) is a group (easy to see). » La preuve : chaque φ_i est
une permutation d'un ensemble fini (injective sur `Fin m`), donc Aut(S) est
un sous-monoïde du produit de groupes symétriques `Π i, Sym(S.sizes i)`
contenant les inverses de ses éléments — un sous-groupe.

Formalisation sans Mathlib : l'inverse est **porté** par l'élément
(structure `Aut` ci-dessous), ce qui évite le principe des tiroirs
(injectif ⇒ bijectif sur `Fin m`, hors core) ; chaque exemple (C₃, Sheffer)
fournit son inverse explicitement. Les cinq axiomes de groupe sont
démontrés — `aut_isGroup` est l'énoncé complet de « easy to see ». -/

/-- Un automorphisme **muni de son inverse** : l'élément du groupe Aut(S). -/
structure Aut {n : Nat} (S : Aut.StructureOn n) where
  /-- L'automorphisme lui-même. -/
  toAuto : Aut.IsAutomorphism S
  /-- Son inverse (lui-même un automorphisme). -/
  inv : Aut.IsAutomorphism S
  /-- Inverse à droite : `φ ∘ φ⁻¹ = id`. -/
  rinv : Aut.autComp toAuto inv = Aut.autId S
  /-- Inverse à gauche : `φ⁻¹ ∘ φ = id`. -/
  linv : Aut.autComp inv toAuto = Aut.autId S

namespace Aut

variable {n : Nat} {S : StructureOn n}

/-- Le neutre du groupe : l'identité, inverse d'elle-même. -/
def gid (S : StructureOn n) : Aut S :=
  ⟨autId S, autId S, comp_autId _, comp_autId _⟩

/-- L'inverse d'un élément du groupe : l'échange des deux composantes. -/
def gsymm (a : Aut S) : Aut S := ⟨a.inv, a.toAuto, a.linv, a.rinv⟩

/-- La loi du groupe : composer les automorphismes ; l'inverse de
    `ψ ∘ φ` est `φ⁻¹ ∘ ψ⁻¹`. -/
def gcomp (a b : Aut S) : Aut S where
  toAuto := autComp a.toAuto b.toAuto
  inv := autComp b.inv a.inv
  rinv := by
    rw [autComp_assoc, ← autComp_assoc (S := S) b.toAuto b.inv a.inv]
    rw [b.rinv, autId_comp, a.rinv]
  linv := by
    rw [autComp_assoc, ← autComp_assoc (S := S) a.inv a.toAuto b.toAuto]
    rw [a.linv, autId_comp, b.linv]

/-- Neutre à gauche du groupe : `gid ∘ a = a`. -/
theorem gid_gcomp (a : Aut S) : gcomp (gid S) a = a := by
  cases a; rfl

/-- Neutre à droite du groupe : `a ∘ gid = a`. -/
theorem gcomp_gid (a : Aut S) : gcomp a (gid S) = a := by
  cases a; rfl

/-- Deux éléments du groupe dont l'automorphisme et l'inverse coïncident
    sont égaux : les champs de preuve suivent par `subst` puis irrélevance
    des preuves. -/
theorem eq_of_toAuto_inv {a b : Aut S}
    (h₁ : a.toAuto = b.toAuto) (h₂ : a.inv = b.inv) : a = b := by
  cases a; cases b
  cases h₁; cases h₂
  rfl

/-- Inverse à gauche du groupe : `a⁻¹ ∘ a = gid`. Les deux champs se
    réduisent au même composite `autComp a.inv a.toAuto`. -/
theorem gsymm_gcomp (a : Aut S) : gcomp (gsymm a) a = gid S :=
  eq_of_toAuto_inv a.linv a.linv

/-- Inverse à droite du groupe : `a ∘ a⁻¹ = gid`. Les deux champs se
    réduisent au même composite `autComp a.toAuto a.inv`. -/
theorem gcomp_gsymm (a : Aut S) : gcomp a (gsymm a) = gid S :=
  eq_of_toAuto_inv a.rinv a.rinv

/-- Associativité de la loi du groupe : `(a ∘ b) ∘ c = a ∘ (b ∘ c)` —
    les deux champs (automorphisme et inverse) sont associatifs, chacun
    pour son instance de `autComp_assoc` ; les champs de preuve suivent
    par irrélevance des preuves. -/
theorem gcomp_assoc (a b c : Aut S) :
    gcomp (gcomp a b) c = gcomp a (gcomp b c) :=
  eq_of_toAuto_inv
    (autComp_assoc a.toAuto b.toAuto c.toAuto)
    (autComp_assoc c.inv b.inv a.inv).symm

/-- Les axiomes d'un groupe, énoncés sans Mathlib (la hiérarchie
    algébrique vit dans Mathlib). -/
structure GroupAxioms (G : Type) (op : G → G → G) (e : G) (i : G → G) where
  assoc : ∀ a b c, op (op a b) c = op a (op b c)
  left_neutral : ∀ a, op e a = a
  right_neutral : ∀ a, op a e = a
  left_inv : ∀ a, op (i a) a = e
  right_inv : ∀ a, op a (i a) = e

/-- **« Aut(S) is a group (easy to see) »** — formalisé : `Aut S`, muni de
    `gcomp`, `gid` et `gsymm`, satisfait les cinq axiomes de groupe. -/
theorem aut_isGroup (S : StructureOn n) :
    GroupAxioms (Aut S) gcomp (gid S) gsymm where
  assoc := gcomp_assoc
  left_neutral := gid_gcomp
  right_neutral := gcomp_gid
  left_inv := gsymm_gcomp
  right_inv := gcomp_gsymm

end Aut
