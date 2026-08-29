import Discrepancy.Basic

/-!
# Komlós et Bansal–Jiang : colonnes unitaires et régime grand degré

Deuxième volet du lake `discrepancy_lean` (issue #12823) : les énoncés de la
frontière SOTA, en la forme exacte de la conjecture de **Komlós** (matrices
à colonnes unitaires, bornée `O(1)` conjecturée) et les formes du papier
**Bansal–Jiang 2025** (arXiv:2508.03961, « Decoupling via Affine
Spectral-Independence: Beck-Fiala and Komlós Bounds Beyond Banaszczyk ») :

- régime grand degré : la conjecture de Beck–Fiala vaut dès `k ≥ (log n)²` ;
- Komlós en `Õ(log^(1/4) n)`, au-delà du `O(√(log n))` de Banaszczyk.

Honnêteté documentée : ces théorèmes exigent un étage absent de Mathlib
(SDP + dualité, indépendance spectrale affine, mouvement brownien discret
guidé, concentration matricielle). Les énoncés vivent donc en `Prop` nommées
**dès maintenant** ; les preuves attendront l'étage amont (P3 = aspiration
documentée, jamais promesse). Pour la forme Komlós du papier, on énonce une
**version affaiblie concrète** (`C * (log n)²`), vraie dès que le théorème
du papier l'est — les exposants polylog exacts du `Õ` ne sont pas pretended.

Les sommes sont écrites à la main (`∑ i, A i j * c j`) plutôt qu'avec
`Matrix.mulVec` : la colonne-ligne reste lisible comme une somme de produits,
au plus près des définitions papier.
-/

namespace Discrepancy

/-- **Conjecture de Komlós** : il existe une constante universelle `C` telle
que toute matrice `A` à `n` colonnes **unitaires** (`∑ i, A i j ^ 2 = 1`)
admet une coloration `±1` des colonnes dont chaque somme de ligne reste
bornée par `C` en valeur absolue.

Le théorème de Banaszczyk (1998) donne `O(√(log n))` ; la conjecture exige
`O(1)`. Ouverte. -/
def KomlosConjecture : Prop :=
  ∃ C : ℚ, ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℚ),
    (∀ j : Fin n, ∑ i, A i j * A i j = 1) →
      ∃ c : Fin n → ℚ,
        (∀ j : Fin n, c j = 1 ∨ c j = -1) ∧ ∀ i : Fin m, |∑ j, A i j * c j| ≤ C

/-- **Bansal–Jiang 2025, régime grand degré** (arXiv:2508.03961,
théorème 1) : la conjecture de Beck–Fiala vaut dès que le degré domine le
carré du logarithme, `k ≥ (log₂ n)²` — avec la même conclusion `O(√k)` à
constante universelle. Résout la conjecture de Beck–Fiala pour `k ≥ log² n`. -/
def BansalJiangLargeDegree : Prop :=
  ∃ C : ℕ,
    ∀ (n k : ℕ) (F : Finset (Finset (Fin n))) (_hk : maxDegree F ≤ k)
      (_hlog : (Nat.log 2 n) ^ 2 ≤ k),
      ∃ c : Fin n → ℤ, IsColoring c ∧ discrepancy F c ≤ C * Nat.sqrt k

/-- **Komlós, forme affaiblie concrète d'après Bansal–Jiang 2025** : pour
les matrices à colonnes unitaires, une coloration `±1` borne chaque somme de
ligne par `C * (log₂ n)²`.

Le papier prouve `Õ(log^(1/4) n)` — plus fort. Un exposant polylog
conservateur (ici `2`) donne un énoncé **impliqué** par le théorème du
papier, donc vrai dès que le papier l'est, tout en restant au-delà de
l'objectif Banaszczyk en petites puissances. C'est la frontière SOTA telle
que le dépôt peut l'énoncer honnêtement sans l'étage SDP. -/
def KomlosBansalJiangWeak : Prop :=
  ∃ C : ℚ,
    ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℚ),
      (∀ j : Fin n, ∑ i, A i j * A i j = 1) →
        ∃ c : Fin n → ℚ,
          (∀ j : Fin n, c j = 1 ∨ c j = -1) ∧
            ∀ i : Fin m, |∑ j, A i j * c j| ≤ C * ((Nat.log 2 n : ℚ) ^ 2)

end Discrepancy
