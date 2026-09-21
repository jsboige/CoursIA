import Mathlib

/-!
# Repons — théorie effective R06 : clustering par classe et quantité conservée

Tranche **R06** de l'arc « théorie effective » (#16741, issue #16752) :
*Baek, Liu & Tegmark, GenEFT — Understanding Statics and Dynamics of Model
Generalization via Effective Theory* (arXiv:2402.05916, 2024 ; PDF GDrive
sha8 `B589C4EF`).

Contenu formalisé :

1. **Théorème 1 (GenEFT)** — `clustering_iff_injective_decoder` : pour un
   autoencodeur de classification (sortie 1 si les deux entrées sont de même
   classe, 0 sinon) entraîné à perte nulle, un décodeur injectif force le
   **clustering par classe** : deux nœuds ont même représentation si et
   seulement s'ils appartiennent à la même classe. La preuve est la
   contradiction constructive du papier : si `E i = E j` pour des classes
   distinctes, alors `Dec (E i ∥ E k) = Dec (E j ∥ E k)` donne `1 = 0` ;
   réciproquement, même classe ⟹ les sorties valent 1 pour le témoin `k = i`
   et l'injectivité donne `E i = E j`.
2. **Appendice C, Eq. (11)** — `conservedHyperbola_deriv_zero` : le système
   d'interactions de deux repons de même classe (Eq. 8-10 : décideur
   `a₂` et demi-séparation `c` soumis à `da₂/dt = −2 η_A c² a₂` et
   `dc/dt = −η_x a₂² c`) conserve la quantité hyperbolique
   `C = a₂² / (2 η_A) − c² / η_x` : sa dérivée est identiquement nulle le
   long de toute solution. C'est la « preuve calculatoire type Mathlib »
   demandée par l'issue : substitution des dérivées + anéantissement
   mutuel `−2 a₂² c² + 2 a₂² c² = 0`. La quantité sépare les trajectoires :
   `C > 0` ⟹ collision des repons (généralisation), `C < 0` ⟹ pas de
   collision (mémorisation) — l'hyperbole de l'oscillateur harmonique du
   papier.

Dépendances : Mathlib uniquement (`hasDerivAt_pow`, `HasDerivAt.comp`,
`HasDerivAt.div_const`, `HasDerivAt.sub`, `field_simp`, `ring`).
-/

namespace LearningTheory.EffectiveTheory

section Clustering

variable {V : Type*} {ι : Type*}

/-- **Théorème 1 (R06)** : classification à perte nulle avec décodeur injectif
⟹ les représentations se groupent exactement par classe.

Le décodeur `dec : V × V → ℝ` opère sur la concaténation des embeddings
(`Dec (E x ∥ E y)` dans le papier) ; l'hypothèse de perte nulle dit que sa
sortie est l'indicateur d'égalité de classe (1 si même classe, 0 sinon).
La preuve est la contradiction constructive du papier, avec le témoin
`k = i` (pas besoin d'un tiers : le papier utilise un `k` de la classe de
`i`, et `i` lui-même convient). -/
theorem clustering_iff_injective_decoder
    (E : ι → V) (dec : V × V → ℝ) (cls : ι → ℕ)
    (hDec : Function.Injective dec)
    (hZeroLoss : ∀ x y, dec (E x, E y) = if cls x = cls y then 1 else 0) :
    ∀ i j, cls i = cls j ↔ E i = E j := by
  intro i j
  constructor
  · -- Même classe ⟹ mêmes représentations : les sorties vers (E i) valent
    -- toutes deux 1, et l'injectivité du décodeur identifie les couples.
    intro hcls
    have h1 : dec (E i, E i) = 1 := by simp [hZeroLoss]
    have h2 : dec (E j, E i) = 1 := by simp [hZeroLoss, hcls]
    have hpair : (E i, E i) = (E j, E i) := hDec (by rw [h1, h2])
    exact congrArg Prod.fst hpair
  · -- Classes distinctes ⟹ représentations distinctes (contraposée par
    -- contradiction : si E i = E j, le même décodage vers le témoin i
    -- vaut à la fois 1 (i,i) et 0 (j,i)).
    intro hE
    by_contra hne
    have key : dec (E i, E i) = dec (E j, E i) := by rw [hE]
    have h1 : dec (E i, E i) = 1 := by simp [hZeroLoss]
    have h0 : dec (E j, E i) = 0 := by
      have hji := hZeroLoss j i
      simp [Ne.symm hne] at hji
      exact hji
    rw [h1, h0] at key
    norm_num at key

end Clustering

section ConservedHyperbola

variable {ηA ηx : ℝ}

/-- **Appendice C (R06), Eq. (11)** : quantité conservée du système de deux
repons de même classe. Si `a₂` et `c` suivent les équations effectives
`da₂/dt = −2 η_A c² a₂` et `dc/dt = −η_x a₂² c` (Eq. 10), alors
`t ↦ (a₂ t)² / (2 η_A) − (c t)² / ηx` a une dérivée identiquement nulle.

Preuve calculatoire : la dérivée vaut
`2 a₂ · (−2 η_A c² a₂) / (2 η_A) − 2 c · (−η_x a₂² c) / ηx = −2 a₂² c² +
2 a₂² c² = 0` — anéantissement mutuel exact, structure d'énergie de
l'oscillateur harmonique signalée par le papier. -/
theorem conservedHyperbola_deriv_zero {a₂ c : ℝ → ℝ}
    (hηA : ηA ≠ 0) (hηx : ηx ≠ 0)
    (ha : ∀ t, HasDerivAt a₂ (-2 * ηA * (c t) ^ 2 * a₂ t) t)
    (hc : ∀ t, HasDerivAt c (-ηx * (a₂ t) ^ 2 * c t) t) :
    ∀ t, HasDerivAt (fun t => (a₂ t) ^ 2 / (2 * ηA) - (c t) ^ 2 / ηx) 0 t := by
  intro t
  have h1 := (hasDerivAt_pow 2 (a₂ t)).comp t (ha t)
  have h2 := (hasDerivAt_pow 2 (c t)).comp t (hc t)
  have H := (h1.div_const (2 * ηA)).sub (h2.div_const ηx)
  refine H.congr_deriv ?_
  field_simp
  ring

end ConservedHyperbola

end LearningTheory.EffectiveTheory
