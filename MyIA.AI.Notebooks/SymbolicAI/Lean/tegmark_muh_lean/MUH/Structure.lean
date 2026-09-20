/-! # Signature d'une structure mathématique finie (Tegmark R16 Annexe A §1)

Une **structure mathématique finie** au sens de Tegmark (2007, Annexe A §1) est
un triplet
```
  (n : Nat,            -- nombre d'ensembles S₁,...,Sₙ
   sizes : Fin n → Nat,-- cardinal de chaque ensemble
   relations : List RelSpec)  -- relations génératrices finies
```
où chaque `RelSpec` porte :
  - une arité `k : Nat`,
  - les types des arguments `args : Fin k → Fin n`,
  - le type de la sortie `out : Fin n`,
  - la **table** des valeurs : `Fin (Π i, sizes (args i)) → Fin (sizes out)`
    (pour les relations Booléennes : `Fin (sizes out) = Fin 2`, donc la table
    rend `Bool`).

La *composition* de deux relations R₁ : S_{a₁}×...×S_{aₖ} → S_{b} et
R₂ : S_{c₁}×...×S_{cₗ} → S_{d} en génère une troisième dès que les types des
sorties paramétriques s'alignent — c'est la règle (3) du §1.

L'**équivalence** de deux structures est définie par génération mutuelle : R₂ est
*générée* par R₁ si chaque relation de R₂ est la composition de relations de R₁.
Une structure est dite *engendrée* par une autre si chacune de ses relations est
produite par compositions finies. -/

/-- Type d'un index dans la famille d'ensembles S₁...Sₙ. -/
abbrev SetIdx (n : Nat) := Fin n

/-- Cardinal d'un ensemble Sᵢ. Pour une structure finie, chaque `sizes i` est
    un entier naturel strictement positif (sinon l'ensemble est vide et la
    relation ne peut être définie). -/
abbrev Sizes (n : Nat) := Fin n → Nat

/-- Signature d'une relation Tegmark : arité, types d'arguments, type de sortie.
    La table de valeurs est tenue à part (voir `Rel`). -/
structure RelSig (n : Nat) where
  arity : Nat
  args  : Fin arity → Fin n
  out   : Fin n

/-- Une relation Tegmark : la signature, plus la table de valeurs.
    Pour une relation Booléenne, `sizes out = 2` (toujours), donc la table
    rend `Bool`. Pour une relation générale, la table rend `Fin (sizes out)`. -/
structure Rel (n : Nat) (sizes : Sizes n) where
  sig : RelSig n
  -- Table des valeurs : `Fin (Π i, sizes (sig.args i)) → Fin (sizes sig.out)`.
  -- Pour Tegmark Annexe A §c, c'est exactement le `value array`.
  table : (i : Fin sig.arity) → (Fin (sizes (sig.args i))) → Fin (sizes sig.out)

/-- Structure mathématique finie : ensembles (par leurs cardinaux) et relations
    génératrices (finies). -/
structure Structure where
  nSets   : Nat
  sizes   : Fin nSets → Nat
  rels    : List (Rel nSets sizes)
  -- Invariant de cardinalité positive : Tegmark Annexe A §1 suppose chaque
    -- ensemble non-vide pour que les relations soient définies. Encodé ici
    -- par une preuve de `∀ i, 0 < sizes i`.
  sizes_pos : ∀ i, 0 < sizes i

namespace Structure

variable {n : Nat} {sizes : Sizes n}

/-- Récupère l'arité d'une relation Tegmark. -/
def arity (r : Rel n sizes) : Nat := r.sig.arity

/-- Récupère le type de sortie d'une relation. -/
def out (r : Rel n sizes) : Fin n := r.sig.out

/-- Récupère le type du i-ème argument (0-indexed). -/
def argType (r : Rel n sizes) (i : Fin r.sig.arity) : Fin n :=
  r.sig.args i

end Structure