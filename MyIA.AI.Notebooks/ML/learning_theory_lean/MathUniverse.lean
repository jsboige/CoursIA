import Mathlib

/-!
# MathUniverse — structures mathématiques finies (Annexe A, R16 Tegmark)

Formalisation Lean de l'**Annexe A** de R16 — *The Mathematical Universe*
(Tegmark, [arXiv:0704.0646](https://arxiv.org/abs/0704.0646), §A.1-A.2) —
la définition opérationnelle d'une structure mathématique sur laquelle repose
l'hypothèse de l'univers mathématique (MUH) : « une structure mathématique est
un ensemble d'entités abstraites et de relations entre elles ».

Tranche formalisation de l'arc « ouvert, responsable, prouvable, explicable »
de l'EPIC **#16741** (issue **#16753**). Contenu distillé :

1. **Définition** (`FinRelStruct`) : entités = un type fini `α` (l'union
   `S₁ ∪ … ∪ Sₙ` du papier, ici mono-sortée), et une **signature** `σ : Fin n → ℕ`
   donnant l'arité de chacune des `n` relations. Chaque relation est un
   prédicat **décidable** sur les uplets d'arité `σ i`. Séparer la signature de
   sa réalisation est exactement ce que fait la théorie des modèles — et c'est
   ce qui rend l'équivalence de deux définitions de la *même* structure
   énonçable sans transport d'arité. Les fonctions non booléennes se codent en
   relations par leur graphe — « la relation R(a₁,…,aₙ₋₁) = aₙ holds »
   (note 20 du papier).
2. **Aut(S) est un groupe** (`aut`) : les bijections préservant chaque
   relation forment un sous-groupe de `Equiv.Perm` — le « easy to see » de
   l'Annexe A, exercice idéal selon le papier. Témoin concret : le groupe
   d'automorphismes de l'algèbre de Boole à deux éléments est **trivial**
   (`aut_bool8_trivial`), ancre déjà utilisée par `EffectiveTheory.InfoBits`
   (`b = log₂(n!/|Aut G|)` : 1 bit pour le groupe à deux éléments).
3. **Décidabilité de l'équivalence** (`EquivStruct`, `EquivStruct.decidable`) :
   il existe « un simple algorithme haltant » pour décider si deux définitions
   de structures finies sont équivalentes — rendu ici comme instance
   `Decidable` par énumération exhaustive des fonctions entre types finis
   (« l'énumération des tableaux » du papier). `decide` EST l'algorithme.
4. **Exemples** (§A.2 du papier) : le groupe cyclique **C₂** (table
   d'addition de Z/2), le groupe cyclique **C₃** (Z/3), et l'**algèbre de
   Boole à deux éléments** — les huit relations F, T, ¬, ∧, ∨, ⇒, ⇔, | de
   l'équation (A1) — générée par **NAND seul** (équation A2) : les huit
   formules de composition du papier (`nand_false`, `nand_true`, `nand_not`,
   `nand_and`, `nand_or`, `nand_implies`, `nand_iff`) et la confirmation
   structurelle par l'algorithme de décision lui-même
   (`decide` sur `EquivStruct bool8 nand8`).

Source PDF (GDrive, sha8) : R16 `85712871`
(`G:\Mon Drive\MyIA\IA\Bibliographie IA\Consciousness\
2007 - Tegmark - The Mathematical Universe.pdf`).

Frère de `Perceptron` (Novikoff), `PacLearning` (Valiant), `GradientFlow`
(vanishing/survie résiduelle) et `EffectiveTheory` (arc B, #16752) dans le
lake généraliste ML. Twin anglais `MathUniverse_en` (#4980).
-/

namespace MathUniverse

variable {α : Type*} {β : Type*} [Fintype α] [Fintype β] {n : ℕ} {σ : Fin n → ℕ}

/-! ## 1. La définition (Annexe A.1) -/

/-- Une **structure relationnelle finie** de signature `σ` : un type porteur
`α` fini (les entités — l'union `S₁ ∪ … ∪ Sₙ` du papier, ici mono-sortée), et
pour chaque `i : Fin n` une relation d'arité `σ i` — un prédicat sur les
uplets d'éléments. La décidabilité exigée par le champ `rel_dec` est celle que
réclame le §A.2 du papier : « all these functions must be computable » — une
structure finie se spécifie par ses tableaux, et un tableau fini se parcourt
entièrement. -/
structure FinRelStruct (α : Type*) [Fintype α] {n : ℕ} (σ : Fin n → ℕ) where
  /- chaque relation : prédicat sur les uplets d'arité `σ i` -/
  rel : (i : Fin n) → ((Fin (σ i) → α) → Prop)
  /- la relation est décidable : le tableau est effectivement donnable -/
  rel_dec : (i : Fin n) → (t : Fin (σ i) → α) → Decidable (rel i t)

/-! ## 2. Aut(S) est un groupe -/

/-- Une application préserve la structure quand chaque relation est
invariante par relabellisation de ses uplets. Pour une bijection, préserver
« à l'aller » suffit : l'iff est alors automatiquement symétrique. -/
def Preserves (S : FinRelStruct α σ) (f : α → α) : Prop :=
  ∀ i (t : Fin (σ i) → α), S.rel i t ↔ S.rel i (f ∘ t)

/-- **Aut(S)**, le groupe d'automorphismes de la structure : les bijections
préservant chaque relation. C'est un sous-groupe de `Equiv.Perm α` — le
« easy to see » de l'Annexe A : l'identité préserve, la composée de deux
préservations préserve, et le symétrique d'une préservation préserve. La
structure de groupe est ensuite celle que Mathlib donne à tout sous-groupe. -/
def aut (S : FinRelStruct α σ) : Subgroup (Equiv.Perm α) where
  carrier := {f | Preserves S f}
  one_mem' := by
    intro i t
    simp
  mul_mem' := by
    intro f g hf hg i t
    rw [Equiv.Perm.coe_mul, Function.comp_assoc]
    exact (hg i t).trans (hf i (⇑g ∘ t))
  inv_mem' := by
    intro f hf i t
    have key : S.rel i (⇑f⁻¹ ∘ t) ↔ S.rel i (⇑(f * f⁻¹) ∘ t) := by
      have h := hf i (⇑f⁻¹ ∘ t)
      rwa [show ⇑f ∘ (⇑f⁻¹ ∘ t) = ⇑(f * f⁻¹) ∘ t by
        simp only [Equiv.Perm.coe_mul, Function.comp_assoc]] at h
    rw [mul_inv_cancel, Equiv.Perm.coe_one, Function.id_comp] at key
    exact key.symm

/-- La relation d'appartenance à Aut(S) se déplie en la préservation. -/
theorem mem_aut_iff (S : FinRelStruct α σ) (f : Equiv.Perm α) :
    f ∈ aut S ↔ Preserves S f := Iff.rfl

/-! ## 3. Décidabilité de l'équivalence (énumération haltante) -/

/-- **Équivalence de structures** (même signature `σ`) : il existe une
bijection `f` telle que chaque relation de `S` corresponde exactement à la
relation de même indice de `T` via `f`. C'est l'isomorphisme relationnel —
le papier : « two structure definitions are equivalent if they generate
each other » ; pour des structures finies données par leurs tableaux,
génératrices comprises, l'équivalence passe par cette correspondance. -/
def EquivStruct (S : FinRelStruct α σ) (T : FinRelStruct β σ) : Prop :=
  ∃ f : α ≃ β, ∀ i (t : Fin (σ i) → α), S.rel i t ↔ T.rel i (f ∘ t)

/-- La version déployée sur les fonctions : même énoncé, mais quantifié sur
`α → β` — le type énumérable par excellence (`Fintype.pi`), ce qui porte la
décidabilité. -/
theorem equivStruct_iff_functions (S : FinRelStruct α σ) (T : FinRelStruct β σ) :
    EquivStruct S T ↔
      ∃ f : α → β, Function.Bijective f ∧
        ∀ i (t : Fin (σ i) → α), S.rel i t ↔ T.rel i (f ∘ t) := by
  constructor
  · rintro ⟨f, hrel⟩
    exact ⟨f, f.bijective, hrel⟩
  · rintro ⟨f, hf, hrel⟩
    exact ⟨Equiv.ofBijective f hf, hrel⟩

/-- **L'algorithme haltant de l'Annexe A** : l'équivalence de deux
structures finies est **décidable** — on énumère toutes les applications
`α → β` (tous les tableaux), chacune testée par des prédicats décidables,
et l'énumération d'un produit fini de types finis termine. Rendu comme
instance `Decidable`, `decide` est littéralement l'énumération des
tableaux du papier.

Les deux `letI` locaux exposent les champs `rel_dec` comme instances : sans
eux, la résolution d'instances ne saurait pas remonter de `Decidable (S.rel i t)`
au champ qui l'atteste. -/
instance EquivStruct.decidable (S : FinRelStruct α σ) (T : FinRelStruct β σ)
    [DecidableEq α] [DecidableEq β] : Decidable (EquivStruct S T) :=
  letI : ∀ i (t : Fin (σ i) → α), Decidable (S.rel i t) := S.rel_dec
  letI : ∀ i (t : Fin (σ i) → β), Decidable (T.rel i t) := T.rel_dec
  decidable_of_iff (∃ f : α → β, Function.Bijective f ∧
    ∀ i (t : Fin (σ i) → α), S.rel i t ↔ T.rel i (f ∘ t))
    (equivStruct_iff_functions S T).symm

/-! ## 4. Exemples (Annexe A.2) -/

namespace Examples

/-! ### L'opérateur de Sheffer `|` (nand) -/

/-- NAND sur `Bool` (symbole de Sheffer `|`) — la relation R₈ de l'équation
(A1), et l'unique génératrice de l'équation (A2). -/
def nand (x y : Bool) : Bool := !(x && y)

/-! ### C₂ : le groupe cyclique Z/2 -/

/-- Signature de `c2` : une relation ternaire. -/
@[reducible]
def c2Sig : Fin 1 → ℕ := fun _ => 3

/-- Le groupe cyclique **C₂** comme structure relationnelle : une seule
relation ternaire, la table d'addition de Z/2 (« generalized multiplication
table », §A.2 du papier) — le graphe de `(x, y) ↦ x XOR y` sur `Bool`,
codé en relation par la note 20 : R(x, y, z) ↔ x + y = z. -/
def c2 : FinRelStruct Bool c2Sig where
  rel := fun _ t => (t 0 ^^ t 1) = t 2
  rel_dec := fun i _ =>
    match i with
    | 0 => inferInstance

/-! ### C₃ : le groupe cyclique Z/3 -/

/-- Signature de `c3` : une relation ternaire. -/
@[reducible]
def c3Sig : Fin 1 → ℕ := fun _ => 3

/-- Le groupe cyclique **C₃** : table d'addition de Z/3 sur `Fin 3`
(l'addition de `Fin n` est déjà modulaire). -/
def c3 : FinRelStruct (Fin 3) c3Sig where
  rel := fun _ t => (t 0 + t 1) = t 2
  rel_dec := fun i _ =>
    match i with
    | 0 => inferInstance

/-! ### L'algèbre de Boole à deux éléments (équation A1) -/

/-- Signature de `bool8` : les arités des huit relations de l'équation
(A1) — deux constantes (arité 1, codant « x = F » et « x = T »), une
fonction unaire (¬) et cinq binaires (∧, ∨, ⇒, ⇔, |). -/
@[reducible]
def bool8Sig : Fin 8 → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 3
  | 5 => 3
  | 6 => 3
  | 7 => 3

/-- Les huit relations de l'équation **(A1)** : F, T, ¬, ∧, ∨, ⇒, ⇔, |
(nand), chacune codée par son graphe (note 20). Les constantes F et T sont
des fonctions d'arité nulle, donc des relations unaires « x = F » et
« x = T » ; les opérateurs unaires et binaires deviennent relations d'arité
2 et 3. -/
def bool8 : FinRelStruct Bool bool8Sig where
  rel := fun i t =>
    match i with
    | 0 => t 0 = false                    -- R₁ = F  (constante fausse)
    | 1 => t 0 = true                     -- R₂ = T  (constante vraie)
    | 2 => (!t 0) = t 1                   -- R₃ = ¬
    | 3 => (t 0 && t 1) = t 2             -- R₄ = ∧
    | 4 => (t 0 || t 1) = t 2             -- R₅ = ∨
    | 5 => (!t 0 || t 1) = t 2            -- R₆ = ⇒
    | 6 => (t 0 == t 1) = t 2             -- R₇ = ⇔
    | 7 => nand (t 0) (t 1) = t 2         -- R₈ = | (nand)
  rel_dec := fun i _ =>
    match i with
    | 0 => inferInstance
    | 1 => inferInstance
    | 2 => inferInstance
    | 3 => inferInstance
    | 4 => inferInstance
    | 5 => inferInstance
    | 6 => inferInstance
    | 7 => inferInstance

/-- **Le groupe d'automorphismes de l'algèbre de Boole est trivial** :
préserver la relation R₁ (« x = F ») épingle la constante fausse, et une
bijection de `Bool` qui fixe `false` fixe `true`. Ancre concrète déjà
mobilisée par `EffectiveTheory.InfoBits` (`b = log₂(n!/|Aut G|)` :
2!/1 = 2, soit 1 bit). -/
theorem aut_bool8_trivial (f : Equiv.Perm Bool) (hf : f ∈ aut bool8) :
    f = 1 := by
  have hnot : Preserves bool8 ⇑f := hf
  have h0 : f false = false := by
    simpa [bool8] using (hnot 0 (fun _ => false)).mp rfl
  have h1 : f true = true := by
    obtain ⟨a, ha⟩ := f.surjective true
    cases a with
    | false => exact absurd (h0 ▸ ha) (by simp)
    | true => exact ha
  ext x
  cases x with
  | false => simpa [Equiv.coe_refl] using h0
  | true => simpa [Equiv.coe_refl] using h1

/-! ### Générée par NAND seul (équation A2) -/

/-- **R₁ = F** par composition de NAND : la formule
`R(R(X, R(X, X)), R(X, R(X, X)))` du papier rend la constante fausse. -/
theorem nand_false (x : Bool) :
    nand (nand x (nand x x)) (nand x (nand x x)) = false := by
  cases x <;> decide

/-- **R₂ = T** : `R(X, R(X, X))` rend la constante vraie. -/
theorem nand_true (x : Bool) : nand x (nand x x) = true := by
  cases x <;> decide

/-- **R₃ = ¬** : `R(X, X)` rend la négation. -/
theorem nand_not (x : Bool) : nand x x = !x := by
  cases x <;> decide

/-- **R₄ = ∧** : `R(R(X, Y), R(X, Y))` rend la conjonction. -/
theorem nand_and (x y : Bool) :
    nand (nand x y) (nand x y) = (x && y) := by
  cases x <;> cases y <;> decide

/-- **R₅ = ∨** : `R(R(X, X), R(Y, Y))` rend la disjonction. -/
theorem nand_or (x y : Bool) :
    nand (nand x x) (nand y y) = (x || y) := by
  cases x <;> cases y <;> decide

/-- **R₆ = ⇒** : `R(X, R(Y, Y))` rend l'implication. -/
theorem nand_implies (x y : Bool) :
    nand x (nand y y) = (!x || y) := by
  cases x <;> cases y <;> decide

/-- **R₇ = ⇔** : `R(R(X, Y), R(R(X, X), R(Y, Y)))` rend l'équivalence
(la table `[[1,0],[0,1]]` du papier). -/
theorem nand_iff (x y : Bool) :
    nand (nand x y) (nand (nand x x) (nand y y)) = (x == y) := by
  cases x <;> cases y <;> decide

/-- La structure **(A2)** : la même signature que (A1) — huit relations —
mais chaque table est dorénavant **définie par composition de NAND seul**,
en suivant exactement les formules de l'équation (A2) du papier. Les deux
constantes restent des relations unaires « x = F » et « x = T » — donc
`x = <formule>`, et non `<formule> = false` : la formule rend la constante,
elle ne l'affirme pas. -/
def nand8 : FinRelStruct Bool bool8Sig where
  rel := fun i t =>
    match i with
    | 0 => t 0 = nand (nand (t 0) (nand (t 0) (t 0))) (nand (t 0) (nand (t 0) (t 0)))
    | 1 => t 0 = nand (t 0) (nand (t 0) (t 0))
    | 2 => nand (t 0) (t 0) = t 1
    | 3 => nand (nand (t 0) (t 1)) (nand (t 0) (t 1)) = t 2
    | 4 => nand (nand (t 0) (t 0)) (nand (t 1) (t 1)) = t 2
    | 5 => nand (t 0) (nand (t 1) (t 1)) = t 2
    | 6 => nand (nand (t 0) (t 1)) (nand (nand (t 0) (t 0)) (nand (t 1) (t 1))) = t 2
    | 7 => nand (t 0) (t 1) = t 2
  rel_dec := fun i _ =>
    match i with
    | 0 => inferInstance
    | 1 => inferInstance
    | 2 => inferInstance
    | 3 => inferInstance
    | 4 => inferInstance
    | 5 => inferInstance
    | 6 => inferInstance
    | 7 => inferInstance

/-- **L'équivalence des définitions (A1) et (A2)** : les huit relations
définies par composition de NAND coïncident exactement avec les huit
relations primitives — l'identité en est le témoin. La preuve est
littéralement le catalogue des formules de composition : chaque lemme
`nand_*` ci-dessus réécrit une ligne de (A2) en la ligne correspondante
de (A1). -/
theorem equivStruct_bool8_nand8 : EquivStruct bool8 nand8 := by
  refine ⟨Equiv.refl Bool, ?_⟩
  intro i t
  fin_cases i
  · simp [bool8, nand8, Equiv.coe_refl, nand_false]
  · simp [bool8, nand8, Equiv.coe_refl, nand_true]
  · simp [bool8, nand8, Equiv.coe_refl, nand_not]
  · simp [bool8, nand8, Equiv.coe_refl, nand_and]
  · simp [bool8, nand8, Equiv.coe_refl, nand_or]
  · simp [bool8, nand8, Equiv.coe_refl, nand_implies]
  · simp [bool8, nand8, Equiv.coe_refl, nand_iff]
  · simp [bool8, nand8, Equiv.coe_refl]

/-- **L'algorithme haltant confirme le papier** : `decide` — l'énumération
des tableaux de l'Annexe A — retrouve que (A1) et (A2) définissent la même
structure, sans qu'on lui donne le témoin. -/
example : decide (EquivStruct bool8 nand8) = true := by
  decide +kernel

end Examples

end MathUniverse
