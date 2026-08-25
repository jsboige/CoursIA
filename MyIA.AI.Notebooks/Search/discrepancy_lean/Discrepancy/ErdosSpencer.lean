import Mathlib
import Discrepancy.Basic
import PacLearning.Hoeffding

/-!
# Boute P2 — borne inférieure d'Erdős–Spencer `√k/2` (méthode probabiliste)

Palier P2 de l'issue #12823 (voir `FORMAL_STATUS.md`) : la contrepartie
optimale du théorème de Beck–Fiala `disc ≤ 2k − 1` — il existe des familles
de degré au plus `k` dont AUCUNE coloration `±1` n'abaisse la discrépance
sous `√k / 2`, justifiant que la borne `O(√k)` ne peut pas être améliorée
en `o(√k)` en général.

La preuve cible réutilise le kernel `PacLearning.Hoeffding` du lake frère
`learning_theory_lean` (import, pas duplication — mandat FORMAL_STATUS) :

1. **Anti-concentration** (boute `p1`) : pour une coloration fixée `c` et un
   ensemble `S` tiré au hasard (Bernoulli indépendant), la somme colorée
   `∑_{i∈S} c i` s'écarte de `√k/2` avec probabilité minorée — via la
   concentration du kernel (`PacLearning.hoeffding_concentration`).
2. **Familles aléatoires** (boute `p2`) : `m` tirages indépendants → pour une
   coloration fixée, la probabilité que TOUS les ensembles restent sous
   `√k/2` décroît exponentiellement en `m`.
3. **Union bound sur les colorations** (boute `p3`) : `2^n · p^m < 1` pour
   `m` assez grand — il existe une réalisation dont toute coloration laisse
   au moins un ensemble à somme `≥ √k/2`.
4. **Contrôle du degré** (boute `p4`) : élagage/conditionnement du tirage
   pour `maxDegree ≤ k` en régime `k ≤ n / C`.

Tant que la preuve n'est pas assemblée, l'énoncé vit comme `Prop` nommée
(convention du lake : conjecture = `def ... : Prop`, zéro `sorry`).
-/

namespace Discrepancy

/-- **Borne inférieure d'Erdős–Spencer (1972)** : pour tout `k ≥ 1` et `n`
assez grand devant `k`, il existe une famille de parties de `Fin n`, de degré
maximal au plus `k`, dont toute coloration `±1` laisse une somme colorée de
valeur absolue au moins `√k / 2` — écrit sans division :
`Nat.sqrt k ≤ 2 * discrepancy F c`. -/
def ErdosSpencerLB : Prop :=
  ∀ (n k : ℕ), 1 ≤ k → k ≤ n →
    ∃ F : Finset (Finset (Fin n)),
      maxDegree F ≤ k ∧
        ∀ c : Fin n → ℤ, IsColoring c → Nat.sqrt k ≤ 2 * discrepancy F c

end Discrepancy
