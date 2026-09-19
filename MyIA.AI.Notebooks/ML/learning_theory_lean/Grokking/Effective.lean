/-
Grokking — théorie effective de l'apprentissage des représentations (tranche 1 : R02).

Ce module formalise les énoncés courts de la partie 3 du papier
« Towards Understanding Grokking — An Effective Theory of Representation Learning »
(Liu, Michaud, Tegmark ; arXiv:2205.10343), issue #16752, arc « ouverte, responsable,
prouvable, explicable » du corpus Tegmark (#16741).

Cadre : addition modulaire jouet sur `Fin p`. Le modèle `M = (Dec, R)` associe à chaque
entier `k` un plongement `E k` dans un groupe abélien `V` (l'espace des représentations) ;
le décodeur `Dec : V → W` lit une paire plongée `E i + E j` et doit produire l'étiquette
`Y (i + j)` de la somme. L'entraînement est à perte nulle lorsque
`Dec (E i + E j) = Y (i + j)` pour toutes les paires.

Contenu :
* `Grokking.IsParallelogram` — Définition 1 du papier (cas exact δ = 0) :
  `(i, j, m, n)` forme un parallélogramme dans la représentation si `E i + E j = E m + E n`.
* `Grokking.prop1_zeroLoss` — Proposition 1 : à perte d'entraînement nulle, tout
  parallélogramme de la représentation provient d'une égalité d'indices `i + j = m + n`
  (les étiquettes étant deux à deux distinctes). Contrepositif : une représentation qui
  « triche » en formant un parallélogramme entre sommes différentes est impossible sans
  perte — c'est la mémoire, pas la structure.
* `Grokking.prop2_injectiveDecoder` — Proposition 2 : réciproquement, si le décodeur d'un
  modèle idéal (perte nulle + décodeur injectif) est injectif, alors toute paire de paires
  d'entraînement `(i, j)`, `(m, n)` avec `i + j = m + n` FORCE un parallélogramme dans la
  représentation. C'est le mécanisme de formation des parallélogrammes : l'injectivité du
  décodeur interdit à deux sommes égales d'avoir des plongements différents.

Les deux propositions sont duales : la 1 échange injectivité du décodeur contre
injectivité des étiquettes, la 2 la rétablit. Aucune structure topologique n'est
nécessaire — un groupe abélien pour `V` suffit (le papier travaille dans `ℝ^d`, mais les
énoncés sont purement algébriques).

Le volet dynamique (lois de conservation de l'Appendice F) est dans
`Grokking.Conservation`.
-/
import Mathlib

namespace Grokking

section Definitions

variable {V : Type*} [AddCommGroup V] {W : Type*} {p : ℕ} [NeZero p]

/-- Définition 1 (R02, cas δ = 0) : `(i, j, m, n)` forme un **parallélogramme** dans la
représentation `E` si les sommes de plongements coïncident exactement. Dans le papier la
définition tolère un seuil `δ` pour les erreurs numériques ; nous prenons `δ = 0`,
le cas limite où tous les énoncés sont exacts. -/
def IsParallelogram (E : Fin p → V) (i j m n : Fin p) : Prop :=
  E i + E j = E m + E n

/-- Perte d'entraînement nulle : le décodeur restitue l'étiquette de la somme pour
chaque paire d'indices. (Le papier limite ceci au jeu d'entraînement `D` ; nous prenons
toutes les paires, ce qui ne fait que renforcer les hypothèses.) -/
def ZeroTrainingLoss (E : Fin p → V) (Dec : V → W) (Y : Fin p → W) : Prop :=
  ∀ i j, Dec (E i + E j) = Y (i + j)

end Definitions

section Proposition1

variable {V : Type*} [AddCommGroup V] {W : Type*} {p : ℕ} [NeZero p]

/-- **Proposition 1 (R02).** À perte d'entraînement nulle et étiquettes deux à deux
distinctes, tout parallélogramme de la représentation est « permis » : `i + j = m + n`.

Preuve (par contradiction, comme dans le papier) : le parallélogramme donne
`Dec (E i + E j) = Dec (E m + E n)`, la perte nulle identifie les deux côtés à
`Y (i + j)` et `Y (m + n)`, et l'injectivité des étiquettes conclut. La version
formalisée est directe plutôt que par l'absurde — même contenu, moins d'étapes. -/
theorem prop1_zeroLoss {E : Fin p → V} {Dec : V → W} {Y : Fin p → W}
    (hloss : ZeroTrainingLoss E Dec Y) (hY : Function.Injective Y) {i j m n : Fin p}
    (hpara : IsParallelogram E i j m n) : i + j = m + n := by
  have h1 : Y (i + j) = Y (m + n) := by
    rw [(hloss i j).symm, (hloss m n).symm, hpara]
  exact hY h1

end Proposition1

section Proposition2

variable {V : Type*} [AddCommGroup V] {W : Type*} {p : ℕ} [NeZero p]

/-- **Proposition 2 (R02).** Dans un modèle idéal (perte nulle + décodeur injectif),
toute égalité d'indices `i + j = m + n` force un parallélogramme de la représentation.

C'est le mécanisme de **formation** des parallélogrammes : la perte nulle donne
`Dec (E i + E j) = Y (i + j) = Y (m + n) = Dec (E m + E n)`, et l'injectivité du
décodeur transforme l'égalité des sorties en égalité des entrées. Combinée à la
Proposition 1, une représentation apprise par un modèle idéal a exactement les
parallélogrammes permis — la structure linéaire observée après le grokking. -/
theorem prop2_injectiveDecoder {E : Fin p → V} {Dec : V → W} {Y : Fin p → W}
    (hloss : ZeroTrainingLoss E Dec Y) (hDec : Function.Injective Dec) {i j m n : Fin p}
    (hsum : i + j = m + n) : IsParallelogram E i j m n := by
  have h1 : Dec (E i + E j) = Dec (E m + E n) := by
    rw [hloss, hloss, hsum]
  exact hDec h1

end Proposition2

section Permissible

variable {p : ℕ} [NeZero p]

/-- Ensemble des parallélogrammes **permis** `P₀` (Éq. 1 du papier) : quadruples
d'indices cohérents avec l'addition. Servira de support à la perte effective `ℓ₀`
du module `Grokking.Conservation`. -/
def permissible : Finset (Fin p × Fin p × Fin p × Fin p) :=
  Finset.univ.filter fun q => q.1 + q.2.1 = q.2.2.1 + q.2.2.2

end Permissible

end Grokking
