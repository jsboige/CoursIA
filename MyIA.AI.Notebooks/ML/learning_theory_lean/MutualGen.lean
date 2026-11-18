import MathUniverse

/-!
# Génération mutuelle générale — l'arité quelconque (Annexe A de R16, tranche 4)

Suite de `MathUniverse` (structures finies, décidabilité de l'équivalence) et de
`Generators` (terme binaire sur générateur unique, instance NAND de l'équation (A2)).
Cette tranche généralise les deux résiduels nommés au fil de #16753 :

1. **Le tuple d'arité quelconque** : `TermSig` est un terme sur une signature
   `σ : Fin n → ℕ` quelconque — `n` symboles, chacun d'arité `σ i`, multi-générateurs
   là où `Generators.Term` portait un unique générateur binaire.
2. **La génération mutuelle générale** : le « two structure definitions are
   equivalent if they generate each other » du §A.2, rendu comme théorème général —
   si chaque générateur de `g₁` est défini par un terme sur `g₂` et réciproquement,
   alors `g₁` et `g₂` engendrent **exactement les mêmes fonctions**
   (`mutual_gen_iff`), par double substitution de termes (`translate`).

Le lemme moteur est la compatibilité de l'évaluation avec la substitution
(`eval_subst`, `eval_translate`) — l'argument « easy to see » du papier : remplacer
un symbole par sa définition dans un terme ne change pas la fonction calculée.
Les exemples referment sur l'ancre `nand` de `MathUniverse` : une fonction d'arité 3
engendrée par le générateur binaire seul, et une signature à deux symboles (¬, ∧)
engendrant ∨ par De Morgan — chacun confirmé par le noyau (`decide`), sans témoin
fourni.

Paper source : R16 — M. Tegmark, *The Mathematical Universe*, arXiv:0704.0646,
Annexe A §A.2. Issue : #16753 (tranche 4).
-/

namespace MathUniverse.MutualGen

/-! ## 1. Termes sur une signature quelconque

La signature `σ : Fin n → ℕ` donne l'arité de chacun des `n` symboles. Un terme
est soit une variable, soit un symbole `i` appliqué à `σ i` sous-termes — le
tuple d'arité quelconque du résiduel #16753. -/

/-- Un **terme** sur la signature `σ` à coefficients dans les variables `ν` :
soit une variable, soit le symbole `i` appliqué à `σ i` sous-termes. -/

inductive TermSig {n : ℕ} (σ : Fin n → ℕ) (ν : Type) where
  /-- une variable -/
  | var : ν → TermSig σ ν
  /-- le symbole `i` appliqué à `σ i` sous-termes -/
  | node : (i : Fin n) → (Fin (σ i) → TermSig σ ν) → TermSig σ ν

/-- L'**évaluation** d'un terme : une valuation des variables et une famille
de générateurs concrets — pour chaque symbole `i`, une fonction d'arité `σ i`
sur `α`. -/
def TermSig.eval {n : ℕ} {σ : Fin n → ℕ} {ν α : Type}
    (t : TermSig σ ν)
    (g : (i : Fin n) → ((Fin (σ i) → α) → α)) (env : ν → α) : α :=
  match t with
  | .var x => env x
  | .node i args => g i (fun k => (args k).eval g env)

/-- La **fonction d'arité `ν` définie par un terme** : le terme évalué comme
fonction des variables. -/
def TermSig.funOf {n : ℕ} {σ : Fin n → ℕ} {ν α : Type}
    (t : TermSig σ ν) (g : (i : Fin n) → ((Fin (σ i) → α) → α)) :
    (ν → α) → α :=
  fun env => t.eval g env

/-- La famille de générateurs `g` **engendre** la fonction `f` quand un terme
la définit — la généralisation multi-symboles, arités quelconques, du
`Generates` binaire. -/
def GeneratesSig {n : ℕ} {σ : Fin n → ℕ} {ν α : Type}
    (g : (i : Fin n) → ((Fin (σ i) → α) → α)) (f : (ν → α) → α) : Prop :=
  ∃ t : TermSig σ ν, t.funOf g = f

/-! ## 2. Substitution — le lemme moteur

Substituer un terme à chaque variable d'un autre revient à composer les
évaluations. C'est le seul calcul dont la génération mutuelle a besoin. -/

/-- La **substitution** `t[s]` : chaque variable `x` de `t` remplacée par le
terme `s x`. -/
def TermSig.subst {n : ℕ} {σ : Fin n → ℕ} {ν μ : Type}
    (t : TermSig σ ν) (s : ν → TermSig σ μ) : TermSig σ μ :=
  match t with
  | .var x => s x
  | .node i args => .node i (fun k => (args k).subst s)

/-- **L'évaluation est compatible avec la substitution** : évaluer `t[s]` dans
`env`, c'est évaluer `t` dans les valeurs de `s` dans `env`. -/
theorem TermSig.eval_subst {n : ℕ} {σ : Fin n → ℕ} {ν μ α : Type}
    (t : TermSig σ ν) (s : ν → TermSig σ μ)
    (g : (i : Fin n) → ((Fin (σ i) → α) → α)) (env : μ → α) :
    (t.subst s).eval g env = t.eval g (fun x => (s x).eval g env) := by
  induction t with
  | var x => rfl
  | node i args ih =>
      simp only [TermSig.subst, TermSig.eval]
      exact congrArg (g i) (funext ih)

/-- **La traduction d'un terme sur `g₁` en terme sur `g₂`** : chaque symbole
`i` de la signature de `g₁` est remplacé par son terme définitionnel `d i`
sur `g₂` — la substitution appliquée symbole par symbole. -/
def translate {n₁ n₂ : ℕ} {σ₁ : Fin n₁ → ℕ} {σ₂ : Fin n₂ → ℕ} {ν : Type}
    (d : (i : Fin n₁) → TermSig σ₂ (Fin (σ₁ i))) (t : TermSig σ₁ ν) :
    TermSig σ₂ ν :=
  match t with
  | .var x => .var x
  | .node i args => (d i).subst (fun k => translate d (args k))

/-- **La traduction préserve l'évaluation** : si chaque `d i` définit `g₁ i`
sur `g₂`, alors le terme traduit calcule la même fonction — remplacer un
symbole par sa définition ne change pas la valeur. C'est l'« easy to see »
du §A.2, rendu. -/
theorem eval_translate {n₁ n₂ : ℕ} {σ₁ : Fin n₁ → ℕ} {σ₂ : Fin n₂ → ℕ} {ν α : Type}
    (g₁ : (i : Fin n₁) → ((Fin (σ₁ i) → α) → α))
    (g₂ : (i : Fin n₂) → ((Fin (σ₂ i) → α) → α))
    (d : (i : Fin n₁) → TermSig σ₂ (Fin (σ₁ i)))
    (hd : ∀ (i : Fin n₁) (t : Fin (σ₁ i) → α), (d i).eval g₂ t = g₁ i t)
    (t : TermSig σ₁ ν) (env : ν → α) :
    (translate d t).eval g₂ env = t.eval g₁ env := by
  induction t with
  | var x => rfl
  | node i args ih =>
      simp only [translate, TermSig.eval_subst]
      have e : (fun k => (translate d (args k)).eval g₂ env)
          = (fun k => (args k).eval g₁ env) := funext ih
      simp only [TermSig.eval]
      rw [e, hd i]

/-! ## 3. Génération mutuelle générale

Le théorème du papier : deux définitions qui se génèrent l'une l'autre sont
équivalentes — ici, au niveau des fonctions engendrées : les deux familles de
générateurs définissent exactement les mêmes fonctions, toutes arités
confondues. -/

/-- **Génération mutuelle générale** (§A.2) : si chaque générateur de `g₁`
est engendré par `g₂` et chaque générateur de `g₂` par `g₁`, alors `g₁` et
`g₂` engendrent exactement les mêmes fonctions — de toute arité `ν`. -/
theorem mutual_gen_iff {n₁ n₂ : ℕ} {σ₁ : Fin n₁ → ℕ} {σ₂ : Fin n₂ → ℕ} {α ν : Type}
    (g₁ : (i : Fin n₁) → ((Fin (σ₁ i) → α) → α))
    (g₂ : (i : Fin n₂) → ((Fin (σ₂ i) → α) → α))
    (h₁ : ∀ i : Fin n₁, GeneratesSig g₂ (g₁ i))
    (h₂ : ∀ i : Fin n₂, GeneratesSig g₁ (g₂ i))
    (f : (ν → α) → α) :
    GeneratesSig g₁ f ↔ GeneratesSig g₂ f := by
  constructor
  · rintro ⟨t, ht⟩
    choose d hd using h₁
    have hd' : ∀ (i : Fin n₁) (u : Fin (σ₁ i) → α), (d i).eval g₂ u = g₁ i u :=
      fun i u => congrFun (hd i) u
    refine ⟨translate d t, funext fun env => ?_⟩
    show (translate d t).eval g₂ env = f env
    rw [eval_translate g₁ g₂ d hd' t env]
    exact congrFun ht env
  · rintro ⟨t, ht⟩
    choose d hd using h₂
    have hd' : ∀ (i : Fin n₂) (u : Fin (σ₂ i) → α), (d i).eval g₁ u = g₂ i u :=
      fun i u => congrFun (hd i) u
    refine ⟨translate d t, funext fun env => ?_⟩
    show (translate d t).eval g₁ env = f env
    rw [eval_translate g₂ g₁ d hd' t env]
    exact congrFun ht env

/-! ## 4. Exemples — l'ancre `nand`

Deux témoins confirmés par le noyau, portés par la preuve et non par l'énoncé :
une fonction d'**arité 3** engendrée par le seul générateur binaire NAND, et
une signature à **deux symboles** (¬ unaire, ∧ binaire) engendrant ∨ par De
Morgan. -/

/-- La signature à un symbole binaire : NAND seul (l'équation (A2)). -/
def nandSig : Fin 1 → ℕ := fun _ => 2

/-- Le générateur concret : NAND sur `Bool`, lu comme fonction d'arité 2.
Le type porte l'arité **littérale** `Fin 2` : `σ := fun _ => 2` se rétablit
par unification de motif, et `t 0` / `t 1` synthétisent `OfNat (Fin 2)`
directement — passer par `Fin (nandSig i)` exigerait de déplier `nandSig`
à la volée, ce que la recherche d'instances ne fait pas. -/
def nandG : (i : Fin 1) → ((Fin 2 → Bool) → Bool) :=
  fun _ t => MathUniverse.Examples.nand (t 0) (t 1)

/-- La conjonction d'arité 2 : la cible du premier témoin. -/
def and2 : (Fin 2 → Bool) → Bool := fun t => t 0 && t 1

/-- La conjonction d'arité 3 : `x ∧ y ∧ z` — le tuple d'arité quelconque,
engendré par le binaire seul. -/
def and3 : (Fin 3 → Bool) → Bool := fun t => t 0 && t 1 && t 2

/-- Un terme-brique : `a ∧ b` vu comme double NAND — `R(R(a, b), R(a, b))`,
réutilisable. -/
def tAnd {ν : Type} (a b : TermSig nandSig ν) : TermSig nandSig ν :=
  .node 0 (fun _ => .node 0 ![a, b])

/-- **NAND engendre ∧** (R₄ du §A.2) : `x ∧ y = R(R(x, y), R(x, y))`. Le
noyau confirme l'égalité fonctionnelle par évaluation exhaustive des
environnements (`decide` via `Pi.instDecidableEqFintype`). -/
theorem nand_generates_and2 : GeneratesSig nandG and2 :=
  ⟨tAnd (.var 0) (.var 1), by decide⟩

/-- **NAND engendre une fonction d'arité 3** : `x ∧ y ∧ z` par composition —
l'arité du tuple n'est pas un plafond du générateur binaire. -/
theorem nand_generates_and3 : GeneratesSig nandG and3 :=
  ⟨tAnd (tAnd (.var 0) (.var 1)) (.var 2), by decide⟩

/-- La signature à deux symboles : ¬ (unaire) et ∧ (binaire). Le filtrage
structurel sur `0` / `⟨j + 1, _⟩` (idiome `Fin.cons`) fait que l'arité se
réduit par iota aussi bien sur l'indice littéral que sur le successeur. -/
def notAndSig : Fin 2 → ℕ
  | 0 => 1
  | ⟨j + 1, _⟩ => 2

/-- Les générateurs concrets : négation et conjonction sur `Bool`,
distingués par le même filtrage structurel. Chaque branche **annonce son
arité littérale** (`Fin 1` / `Fin 2`) — l'unification définitionnelle
déplie `notAndSig` sur le motif, et `u 0` / `u 1` synthétisent `OfNat` sur
un littéral, jamais sur un `Fin (notAndSig i)` opaque. La réduction par
iota sur les indices concrets du témoin porte la preuve par `decide`. -/
def notAndG : (i : Fin 2) → ((Fin (notAndSig i) → Bool) → Bool)
  | 0 => fun (u : Fin 1 → Bool) => !(u 0)
  | ⟨j + 1, _⟩ => fun (u : Fin 2 → Bool) => u 0 && u 1

/-- La disjonction : la cible du témoin De Morgan. -/
def or2 : (Fin 2 → Bool) → Bool := fun t => t 0 || t 1

/-- **¬ et ∧ engendrent ∨ par De Morgan** : `x ∨ y = ¬(¬x ∧ ¬y)` — un
multi-générateur, deux arités distinctes dans la même signature. -/
theorem notAnd_generates_or2 :
    GeneratesSig notAndG or2 :=
  ⟨.node 0 (fun _ => .node 1 (fun k => .node 0 (fun _ => .var k))), by decide⟩

end MathUniverse.MutualGen
