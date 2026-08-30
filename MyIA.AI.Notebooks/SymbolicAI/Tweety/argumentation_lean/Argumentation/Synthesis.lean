import Mathlib
import Argumentation.Extensions

/-!
# Synthèse certifiée d'extensions stables — témoins Z3 (Loi II, variante `-c`)

Quatrième substrat indépendant pour le Chantier 2 (#12205, §4) : la chaîne
**spécification → générateur ≠ vérificateur → témoin → certificat** transférée
à l'argumentation abstraite de Dung.

```
spécification (AF-A, sémantique Stable)  →  Z3 4.16.0  →  S = {1, 2, 5}  →  afA_stable_SA : afA.Stable SA := by decide
spécification (AF-B, 3-cycle)            →  Z3 (UNSAT)  →  —            →  afB_no_stable : ∀ p, ¬ afB.Stable {a | p a} := by decide
```

La Loi II (« passer du vérificateur au constructeur », #12204) était déjà
franchie sur Life (#12286), Robinson-Goforth (#12364) et AMD (#12648) ; ce
module teste si elle **transfère** sur un substrat fini où la sémantique est
une contrainte combinatoire (sans conflat + dominance).

**Dette assumée (comme en B1)** : le chercheur — Z3, hors Lean — n'est pas
certifié. Ce qui est certifié est le **témoin**, par évaluation du noyau Lean
(`decide`, aucun axiome). Personne n'a écrit `{1, 2, 5}` à la main : c'est le
modèle rendu par Z3 sur la spécification (script `synth_stable.py`, #13597).

## Le cas sans solution est un livrable

L'AF-B (3-cycle) n'admet **aucune** extension stable : un ensemble sans conflat
qui domine tout l'extérieur n'existe pas — les trois arguments s'excluent
mutuellement en cascade et aucun singleton n'attaque les deux autres. Z3 rend
UNSAT ; `afB_no_stable` le certifie par énumération décisive des 8 fonctions
caractéristiques `Fin 3 → Bool` : c'est une **dissociation enregistrée à la
borne n = 3**, pas un échec d'expérience.
-/

namespace Argumentation.Synthesis

/-- Décidabilité de l'implication — le composant absent de la chaîne de
synthèse `decide` pour les sémantiques de Dung sur un cadre fini : les gardes
`a ∈ S → φ` de `conflictFree` et `Stable` en ont besoin. `private` : portée
limitée à ce fichier, aucun export. -/
private instance impDec (p q : Prop) [Decidable p] [Decidable q] :
    Decidable (p → q) :=
  match inferInstanceAs (Decidable p), inferInstanceAs (Decidable q) with
  | isFalse hp, _ => isTrue fun h => absurd h hp
  | isTrue _, isTrue hq => isTrue fun _ => hq
  | isTrue hp, isFalse hq => isFalse fun h => hq (h hp)

/-! ## AF-A : 6 arguments, spécification à table d'attaque décidable -/

/-- Table d'attaque de l'AF-A — ceci est la **spécification** (aucun témoin ici) :
0 ↔ 1 mutuelle, 2 → 3, 4 ↔ 5 mutuelle, 1 → 3, 3 → 4, 0 → 5. -/
def afA_edges : List (Nat × Nat) :=
  [(0, 1), (1, 0), (2, 3), (4, 5), (5, 4), (1, 3), (3, 4), (0, 5)]

/-- L'AF-A concret sur `Fin 6` : la relation d'attaque est l'appartenance
décidable à la table. -/
def afA : AF (Fin 6) where
  attacks a b := afA_edges.contains (a.val, b.val) = true

/-- Témoin rendu par Z3 4.16.0 (modèle du solveur, transcrit tel quel) :
l'ensemble `{1, 2, 5}`. -/
def SA : Set (Fin 6) := {a | a.val ∈ [1, 2, 5]}

instance (a b : Fin 6) : Decidable (afA.attacks a b) :=
  instDecidableEqBool (afA_edges.contains (a.val, b.val)) true

-- `def SA` (et `def afA`) ne se deplient pas a la transparence `instances` :
-- l'appartenance doit etre declaree explicitement pour que la synthese la trouve.
instance : DecidablePred (· ∈ SA) := fun a =>
  if h : a.val ∈ [1, 2, 5] then isTrue h else isFalse h

/-- **Certificat** : le témoin Z3 `{1, 2, 5}` est une extension stable de
l'AF-A, évalué par le noyau Lean — le cran « vérificateur → constructeur »
est franchi sur ce substrat. -/
theorem afA_stable_SA : afA.Stable SA := by
  unfold AF.Stable AF.conflictFree
  decide

/-! ## AF-B : le 3-cycle, cas sans solution -/

/-- Table d'attaque de l'AF-B : le cycle 0 → 1 → 2 → 0. -/
def afB_edges : List (Nat × Nat) := [(0, 1), (1, 2), (2, 0)]

/-- L'AF-B concret sur `Fin 3`. -/
def afB : AF (Fin 3) where
  attacks a b := afB_edges.contains (a.val, b.val) = true

instance (a b : Fin 3) : Decidable (afB.attacks a b) :=
  instDecidableEqBool (afB_edges.contains (a.val, b.val)) true

instance {p : Fin 3 → Bool} : DecidablePred (· ∈ {a | p a}) := fun a =>
  if h : p a = true then isTrue h else isFalse h

/-- **Dissociation certifiée à la borne n = 3** : le 3-cycle n'admet aucune
extension stable. Z3 rend UNSAT sur la même spécification ; Lean certifie
l'impossibilité en énumérant les 8 fonctions caractéristiques `Fin 3 → Bool`
(chaque sous-ensemble de `{0, 1, 2}` est `{a | p a}` pour un `p`). Un
générateur qui rend « aucune solution » avec ce certificat ne contourne pas
le cran : il franchit le point 4 du critère de #12205. -/
theorem afB_no_stable : ∀ p : Fin 3 → Bool, ¬ afB.Stable {a | p a} := by
  intro p
  unfold AF.Stable AF.conflictFree
  decide +revert

end Argumentation.Synthesis
