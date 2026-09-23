import Mathlib
import EffectiveTheory.Grokking
import EffectiveTheory.GrokkingLemmas
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
2. **`EffectiveTheory.GrokkingLemmas`** (R02, recadrage #16752) : module
   frère du précédent — conservation de `C = Σ E k` le long du flot de `ℓ₀`
   **sans hypothèse** (`C_conserved_l0`), invariance de l'hyperplan centré
   `C = 0` le long du flot effectif par facteur intégrant
   (`meanZero_invariant`), et lemmes génériques de calcul différentiel
   (`hasDerivAt_line`, `euler_zero_homogeneous`,
   `fderiv_of_translateInvariant`, `eq_of_hasDerivAt_zero`,
   `Z0_conserved` en cadre préhilbertien quelconque). Twin anglais
   `GrokkingLemmas_en` (#4980).
3. **`EffectiveTheory.Repons`** (R06, *GenEFT*, arXiv:2402.05916) :
   Théorème 1 (décodeur injectif ⟹ clustering par classe, preuve
   constructive par contradiction) et la quantité conservée hyperbolique
   `C = a₂²/(2η_A) − c²/η_x` du système de repons (appendice C,
   `dC/dt = 0`, preuve calculatoire).
4. **`EffectiveTheory.InfoBits`** (R06) : contenu informationnel
   `b = log₂(n!/|Aut G|)` et ses ancres concrètes — groupe trivial
   (`b = 0`), groupe à deux éléments (`b = 1`, automorphismes triviaux).
5. **`EffectiveTheory.CircleOfDays`** (R10, *Not All Language Model Features
   Are One-Dimensionally Linear*, arXiv:2405.14860) : le cercle des jours
   comme représentation de `C₇ = ZMod 7` (`rotation_cyclicSeven`) et son
   **irréductibilité** (`circleOfDays_irreducible`) — le « LLM a ré-appris
   la théorie des représentations ».

Sources PDF (GDrive, sha8) : R02 `88CE88DB` · R06 `B589C4EF` · R10
`7DEAC929`. Frère de `Perceptron` (Novikoff), `PacLearning` (Valiant) et
`GradientFlow` (vanishing/survie résiduelle) dans le lake généraliste ML.
-/
