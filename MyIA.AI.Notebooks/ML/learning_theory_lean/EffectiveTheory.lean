import Mathlib
import EffectiveTheory.Grokking
import EffectiveTheory.Repons
import EffectiveTheory.InfoBits
import EffectiveTheory.CircleOfDays

/-!
# EffectiveTheory — théorie effective de la représentation (Tegmark & co)

Tranche formalisation de l'arc « théorie effective » **#16741** (issue
**#16752**, arc B — « ouverte, responsable, prouvable, explicable ») :
distiller en Lean les énoncés mathématiquement propres du corpus
R02 / R06 / R10.

1. **`EffectiveTheory.Grokking`** (R02, *Towards Understanding Grokking*,
   arXiv:2205.10343) : parallélogrammes — Définition 1 (δ-parallélogramme),
   Proposition 1 (perte nulle ⟹ `i + j = m + n`), Proposition 2 (décodeur
   injectif ⟹ formation des parallélogrammes) — et les deux identités de
   l'appendice F qui portent les lois de conservation `C = Σ E k` (somme des
   composantes du gradient nulle) et `Z₀ = Σ E k²` (identité d'Euler
   `Σ ∂ℓ₀/∂E_k · E k = 2 ℓ₀`).
2. **`EffectiveTheory.Repons`** (R06, *GenEFT*, arXiv:2402.05916) :
   Théorème 1 (décodeur injectif ⟹ clustering par classe, preuve
   constructive par contradiction), la quantité conservée hyperbolique
   `C = a₂²/(2η_A) − c²/η_x` du système de repons (appendice C,
   `dC/dt = 0`, preuve calculatoire) et l'**autonomie de la séparation**
   (Eq. 16 : le forçage externe common-mode s'annule dans `x₁ − x₂`).
3. **`EffectiveTheory.InfoBits`** (R06) : contenu informationnel
   `b = log₂(n!/|Aut G|)` et ses ancres concrètes — groupe trivial
   (`b = 0`), groupe à deux éléments (`b = 1`, automorphismes triviaux) —
   et les **Statics sur graphes** (Section III) : action de re-labellage de
   `Equiv.Perm (Fin n)` sur `SimpleGraph (Fin n)`, pont `mem_aut_iff`
   (stabilisateur = automorphismes), orbit-stabilizer
   `card_orbit_mul_card_aut` (`|orbite| · |Aut G| = n!`) et longueur de
   description `descLength` / `descLength_eq` (`b = log₂ (n!/|Aut G|)`).
   Migration du module dissous `GenEFT.lean` (#17480).
4. **`EffectiveTheory.CircleOfDays`** (R10, *Not All Language Model Features
   Are One-Dimensionally Linear*, arXiv:2405.14860) : le cercle des jours
   comme représentation de `C₇ = ZMod 7` (`rotation_cyclicSeven`) et son
   **irréductibilité** (`circleOfDays_irreducible`) — le « LLM a ré-appris
   la théorie des représentations ».

Sources PDF (GDrive, sha8) : R02 `88CE88DB` · R06 `B589C4EF` · R10
`7DEAC929`. Frère de `Perceptron` (Novikoff), `PacLearning` (Valiant) et
`GradientFlow` (vanishing/survie résiduelle) dans le lake généraliste ML.
-/
