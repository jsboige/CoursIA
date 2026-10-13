/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
Adapté à `discrepancy_lean` (issue #17845, distillation Karingula–Lovett
arXiv:2609.20979) : toolchain v4.33.0, Mathlib `db584cd6`, convention i18n #4980.

Le source Dahia original vit dans le dépôt `gdahia/Komlos` (toolchain
v4.34.0, cadre `Finsupp` sur `E →₀ ℝ`). Ce module n'a **pas de contrepartie
oracle nom pour nom** : l'oracle n'a pas besoin de pont de niveau, et cette
absence est précisément ce que cette brique documente.

**Design-gate de l'assemblage k2.6 (consigné ici, décision arbitrée).**
L'oracle démontre le Lemme 1.4 (`Komlos/SignedSums.lean` l.37-64) par
induction sur `n` avec l'énoncé **universellement quantifié sur `E`** —
l'hypothèse d'induction s'applique donc, au cran successeur, à la
distribution scindée dans l'espace **agrandi** `E × ℝ` (l.52), avec les
vecteurs embarqués à hauteur nulle `(v i.castSucc, 0)` (l.47, l.53). La
base du lake `Fin d → ℤ` est fixe, et aucune des briques k1.x/k2.x ne
s'appliquerait à une distribution sur un type réellement différent. Les
options mesurées :

- (a) généraliser `split`/`pullback` sur un espace abstrait `X × Bool` —
  une seconde formalisation de toute la chaîne ;
- (b) espace produit itéré `(Fin d → ℤ) × (Fin n → Bool)` — même coût de
  généralisation, notation plus lourde ;
- **(c) retenue : l'espace qui grandit est `Fin (d + k) → ℤ`.** La hauteur
  `Bool` s'embarque comme l'entier `{0, 1}` à la position `snoc` :
  l'embedding `liftUp : ((Fin d → ℤ) × Bool) → (Fin (d+1) → ℤ)` réalise
  le `incl b : E ↪ E × ℝ` de l'oracle (`Komlos/Split.lean` l.31) côté
  discret, et `toReal` (k2.3) transporte vers `Fin (d+1) → ℝ`, qui est le
  `E × ℝ` de l'oracle lu coordonnée par coordonnée. Chaque brique du lake
  étant générique en `d`, elles s'appliquent **toutes telles quelles à la
  dimension suivante** : le miroir d'induction de l'oracle est
  `induction n generalizing d`.

**Portée de ce commit** (brique k2.6a, `lake build SUCCESS` requis, 0
`sorry`) — le pont de niveau, mécanique de bout en bout :

- `liftUp` + injectivité — l'embedding produit vers `snoc` ;
- `liftUp_add_snoc` — les translations de hauteur nulle commutent avec
  l'embedding : `liftUp y + snoc u 0 = liftUp (y.1 + u, y.2)` (l'équation
  qui fait marcher le pont de `shiftDistance`) ;
- `pushUp` — la poussée le long de `liftUp`, le **même pattern
  `Function.extend` que l'organe `push` de k2.3** (le `Finsupp.embDomain`
  du lake), avec sa lecture `apply`/`eq_zero`/`nonneg`/`mass` ; ce n'est
  pas le `push` de k2.3 lui-même car celui-ci est typé sur le transport de
  dimension `(Fin d → ℤ) →+ (Fin d → ℝ)`, alors que le côté produit ne
  porte aucune structure additive (`Bool`) ;
- les **ponts de moment** : le moment coordonné de la poussée, lu sur une
  coordonnée `castSucc`, est le moment produit de la source ; sur la
  coordonnée `last`, c'est le moment de hauteur — les deux composantes de
  `mean_split` (k2.0) lues à travers l'embedding ;
- le **pont de distance de translation** :
  `Δ(pushUp Q, snoc u 0) = Δprod(Q, u)` — le Claim 3.2 de k1.5 se
  transporte tel quel vers l'espace agrandi ;
- `sum_smul_snoc` — la forme lake du `sum_smul_inl` de l'oracle
  (`Komlos/Split.lean` l.50-53) : une somme de vecteurs mis à l'échelle,
  chacun embarqué à hauteur nulle, reste embarquée à hauteur nulle. Son
  consommateur est mesuré : `Komlos/SignedSums.lean` l.54
  (`rw [mean_split, sum_smul_inl, ...]`) ;
- `toReal_liftUp` — la commutation `toReal ∘ liftUp = snoc ∘ (toReal ×
  hauteur)` : le carré de diagramme avec le `toRealProd` de k2.4 se
  referme, et c'est ainsi que l'assemblage k2.6 nourrira `pullback`
  (k2.4) depuis l'hypothèse d'induction énoncée à la dimension agrandie.

**Différé avec consommateur mesuré** : la conservation des moments sous
contenance (`prodMoment_split_of_support`, le pendant `_of_support` des
composantes de `mean_split` de k2.0) et le transfert de contenance à
travers la scission (k2.6b) ; l'induction elle-même (`SignedSums.lean`
nom pour nom, k2.6c). L'état détaillé vit dans `FORMAL_STATUS.md`.
-/

import Discrepancy.Komlos.MeanSplit
import Discrepancy.Komlos.SplitDistance
import Discrepancy.Komlos.Transport

/-!
# Pont de niveau : espace produit vers dimension agrandie (k2.6a)

`Discrepancy.Komlos.liftUp` embarque `(Fin d → ℤ) × Bool` dans
`Fin (d+1) → ℤ` — la partie spatiale par `Fin.snoc`, la hauteur `Bool`
comme l'entier `{0, 1}` à la dernière coordonnée. `pushUp` pousse une
distribution le long de cet embedding (le pattern `Function.extend` de
l'organe `push` de k2.3), et les ponts de ce module énoncent que **toute**
la structure que l'assemblage consomme — masse, moments coordonnés,
moment de hauteur, distance de translation, support — se lit à travers
l'embedding sans perte.

C'est la réalisation discrète de l'espace croissant de l'oracle : son
induction sur le nombre de vecteurs applique l'hypothèse dans `E × ℝ` à
chaque scission (`Komlos/SignedSums.lean` l.44-53) ; la nôtre l'applique
dans `Fin (d+1) → ℤ`, où chaque brique du lake (toutes génériques en
`d`) vit déjà.
-/

namespace Discrepancy.Komlos

/-- **Embedding de niveau** : la grille produit `(Fin d → ℤ) × Bool` se
plonge dans la grille de dimension supérieure `Fin (d+1) → ℤ` — la partie
spatiale par `Fin.snoc`, la hauteur `Bool` comme l'entier `{0, 1}` à la
dernière coordonnée.

C'est la contrepartie discrète du `incl b : E ↪ E × ℝ` de l'oracle
(`Komlos/Split.lean` l.31) : là où l'oracle embarque `E` comme tranche de
hauteur `b` de `E × ℝ`, le lake embarque la paire `(x, b)` comme vecteur
de dimension `d+1` — la hauteur devenant une coordonnée entière valant
`0` ou `1`. Le transport `toReal` (k2.3) la relit alors comme coordonnée
réelle, refermant le carré avec `toRealProd` (k2.4, cf `toReal_liftUp`). -/
def liftUp {d : ℕ} : ((Fin d → ℤ) × Bool) → (Fin (d + 1) → ℤ) :=
  fun y => Fin.snoc y.1 (if y.2 then 1 else 0)

/-- Lecture de l'embedding sur une coordonnée héritée : la partie
spatiale se lit inchangée. -/
@[simp] lemma liftUp_apply_castSucc {d : ℕ} (y : (Fin d → ℤ) × Bool)
    (i : Fin d) : liftUp y i.castSucc = y.1 i := by simp [liftUp]

/-- Lecture de l'embedding sur la coordonnée de hauteur : le `Bool`
devient l'entier `{0, 1}`. -/
@[simp] lemma liftUp_apply_last {d : ℕ} (y : (Fin d → ℤ) × Bool) :
    liftUp y (Fin.last d) = if y.2 then 1 else 0 := by simp [liftUp]

/-- L'embedding de niveau est **injectif** : la partie spatiale se relit
par `Fin.init`-quement (deux `snoc` égaux ont des queues égales et des
corps égaux), et la coordonnée de hauteur sépare `false` de `true` par
`0 ≠ 1`. C'est le papier des `Finset.map` des supports transportés. -/
lemma liftUp_injective {d : ℕ} : Function.Injective (liftUp (d := d)) := by
  rintro ⟨x₁, b₁⟩ ⟨x₂, b₂⟩ h
  simp only [liftUp, Fin.snoc_inj] at h
  obtain ⟨hxe, hqe⟩ := h
  cases b₁ <;> cases b₂ <;> simp_all

/-- La version `Finset.Embedding` de `liftUp`, pour les `Finset.map` des
supports poussés. -/
def liftUpEmb {d : ℕ} : ((Fin d → ℤ) × Bool) ↪ (Fin (d + 1) → ℤ) :=
  ⟨liftUp, liftUp_injective⟩

/-- Lecture de l'embedding wrapper : `liftUpEmb` applique `liftUp`. C'est
le pont syntaxique que consomment les re-écritures `pushUp_apply` /
`liftUp_apply_*` sur les images `Finset.map`. -/
lemma liftUpEmb_apply {d : ℕ} (y : (Fin d → ℤ) × Bool) :
    liftUpEmb y = liftUp y := rfl

/-- **Les translations de hauteur nulle commutent avec l'embedding** :
`liftUp y + snoc u 0 = liftUp (y.1 + u, y.2)`. C'est l'équation qui fait
marcher le pont de distance de translation (`shiftDistance_pushUp`) : la
translation `u` de la base, embarquée à hauteur nulle dans la dimension
supérieure, agit sur l'image exactement comme la translation `(u, 0)` de
l'espace produit. -/
lemma liftUp_add_snoc {d : ℕ} (y : (Fin d → ℤ) × Bool) (u : Fin d → ℤ) :
    liftUp y + Fin.snoc u 0 = liftUp (y.1 + u, y.2) := by
  funext j
  induction j using Fin.lastCases with
  | last => simp [liftUp]
  | cast i => simp [liftUp, Pi.add_apply]

/-- **Poussée d'une distribution le long de l'embedding de niveau** :
`pushUp Q (liftUp y) = Q y` (par `pushUp_apply`) et `pushUp Q z = 0`
hors de l'image (par `pushUp_eq_zero`).

C'est le **même pattern `Function.extend` que l'organe `push` de k2.3**
(le `Finsupp.embDomain` de l'oracle, `Komlos/Transport.lean` l.27-28) —
et non cet organe lui-même : `push` de k2.3 est typé sur le transport de
dimension `(Fin d → ℤ) →+ (Fin d → ℝ)`, un morphisme additif, alors que
la source produit `(Fin d → ℤ) × Bool` ne porte aucune structure
additive (le `Bool` n'a pas d'opposé). Le prolongement le long d'une
injection est l'organe Mathlib commun aux deux. -/
noncomputable def pushUp {d : ℕ} (Q : ((Fin d → ℤ) × Bool) → ℝ) :
    (Fin (d + 1) → ℤ) → ℝ :=
  Function.extend liftUp Q 0

/-- Sur l'image de l'embedding, la poussée relit la distribution source.
(Chez l'oracle, c'est le rôle de `Finsupp.embDomain_apply_self`.) -/
@[simp] lemma pushUp_apply {d : ℕ} (Q : ((Fin d → ℤ) × Bool) → ℝ)
    (y : (Fin d → ℤ) × Bool) : pushUp Q (liftUp y) = Q y :=
  Function.Injective.extend_apply liftUp_injective Q 0 y

/-- Hors de l'image de l'embedding, la poussée est nulle : les points de
la grille de dimension `d+1` sans antécédent produit ne portent aucune
masse. -/
lemma pushUp_eq_zero {d : ℕ} (Q : ((Fin d → ℤ) × Bool) → ℝ)
    {z : Fin (d + 1) → ℤ} (hz : ∀ y, liftUp y ≠ z) : pushUp Q z = 0 := by
  have hb : ¬∃ a, liftUp a = z := by
    rintro ⟨a, rfl⟩
    exact hz a rfl
  exact Function.extend_apply' Q (0 : (Fin (d + 1) → ℤ) → ℝ) z hb

/-- La poussée d'une fonction positive reste positive : chaque point est
soit une valeur de la source, soit zéro. -/
lemma pushUp_nonneg {d : ℕ} {Q : ((Fin d → ℤ) × Bool) → ℝ}
    (hQ : ∀ y, 0 ≤ Q y) (z : Fin (d + 1) → ℤ) : 0 ≤ pushUp Q z := by
  by_cases h : ∃ y, liftUp y = z
  · obtain ⟨y, rfl⟩ := h
    rw [pushUp_apply]
    exact hQ y
  · rw [pushUp_eq_zero Q (fun y hy => h ⟨y, hy⟩)]

/-- **La masse est conservée par la poussée** : sommer la poussée sur le
support transporté, c'est sommer la source — le pendant `pushUp` de
`push_mass` (k2.3). -/
lemma pushUp_mass {d : ℕ} (Q : ((Fin d → ℤ) × Bool) → ℝ)
    (SQ : Finset ((Fin d → ℤ) × Bool)) :
    ∑ z ∈ SQ.map liftUpEmb, pushUp Q z = ∑ y ∈ SQ, Q y := by
  simp only [Finset.sum_map, liftUpEmb_apply]
  exact Finset.sum_congr rfl fun y _ => pushUp_apply Q y

/-- **Exactitude du support poussé (sens direct)** : si chaque point de
`SQ` porte une masse non nulle, chaque point du support transporté porte
une masse non nulle. -/
lemma pushUp_ne_zero_of_mem {d : ℕ} {Q : ((Fin d → ℤ) × Bool) → ℝ}
    {SQ : Finset ((Fin d → ℤ) × Bool)} (hSQ : ∀ y ∈ SQ, Q y ≠ 0) :
    ∀ z ∈ SQ.map liftUpEmb, pushUp Q z ≠ 0 := by
  intro z hz
  rw [Finset.mem_map] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  simp only [liftUpEmb_apply]
  rw [pushUp_apply]
  exact hSQ y hy

/-- **Exactitude du support poussé (sens retour)** : si `SQ` contient le
support de `Q`, l'image transportée contient le support de la poussée. -/
lemma pushUp_mem_map_of_ne_zero {d : ℕ} {Q : ((Fin d → ℤ) × Bool) → ℝ}
    {SQ : Finset ((Fin d → ℤ) × Bool)} (hSQ : ∀ y, Q y ≠ 0 → y ∈ SQ) :
    ∀ z, pushUp Q z ≠ 0 → z ∈ SQ.map liftUpEmb := by
  intro z hz
  by_cases hex : ∃ y, liftUp y = z
  · obtain ⟨y, rfl⟩ := hex
    rw [pushUp_apply] at hz
    exact Finset.mem_map.mpr ⟨y, hSQ y hz, liftUpEmb_apply y⟩
  · rw [pushUp_eq_zero Q (fun y hy => absurd ⟨y, hy⟩ hex)] at hz
    exact (hz rfl).elim

/-- **Pont de moment, coordonnée héritée** : le moment coordonné de la
poussée, lu sur une coordonnée `castSucc`, est le moment de base de la
source — la composante spatiale du barycentre traverse l'embedding sans
changement. C'est la première composante de `mean_split` (k2.0) lue à
travers le pont de niveau. -/
lemma coordMoment_pushUp_castSucc {d : ℕ} (Q : ((Fin d → ℤ) × Bool) → ℝ)
    (SQ : Finset ((Fin d → ℤ) × Bool)) (i : Fin d) :
    coordMoment (pushUp Q) (SQ.map liftUpEmb) i.castSucc = prodMoment Q SQ i := by
  simp only [coordMoment, prodMoment, Finset.sum_map, liftUpEmb_apply]
  exact Finset.sum_congr rfl fun y _ => by rw [pushUp_apply, liftUp_apply_castSucc]

/-- **Pont de moment, coordonnée de hauteur** : le moment coordonné de la
poussée, lu sur la dernière coordonnée, est le moment de hauteur de la
source — le `Bool` `{false, true}` relu comme le réel `{0, 1}`. C'est la
seconde composante de `mean_split` (k2.0) : le bit de scission devient la
coordonnée de hauteur du barycentre poussé. -/
lemma coordMoment_pushUp_last {d : ℕ} (Q : ((Fin d → ℤ) × Bool) → ℝ)
    (SQ : Finset ((Fin d → ℤ) × Bool)) :
    coordMoment (pushUp Q) (SQ.map liftUpEmb) (Fin.last d)
      = heightMoment Q SQ := by
  simp only [coordMoment, heightMoment, Finset.sum_map, liftUpEmb_apply]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [pushUp_apply, liftUp_apply_last]
  cases y.2 <;> simp

/-- **Pont de distance de translation** : la distance de translation de
la poussée, dans une direction embarquée à hauteur nulle, est la distance
de translation produit de la source — `Δ(pushUp Q, snoc u 0) = Δprod(Q,
u)`. C'est ce qui permet au Claim 3.2 (k1.5, `shiftDistanceProd_split_le`)
de s'appliquer à la dimension supérieure : l'hypothèse d'induction sur
les distances se transporte sans perte. -/
lemma shiftDistance_pushUp {d : ℕ} (Q : ((Fin d → ℤ) × Bool) → ℝ)
    (SQ : Finset ((Fin d → ℤ) × Bool)) (u : Fin d → ℤ) :
    shiftDistance (SQ.map liftUpEmb) (pushUp Q) (Fin.snoc u 0)
      = shiftDistanceProd SQ Q u := by
  simp only [shiftDistance, shiftDistanceProd, Finset.sum_map, liftUpEmb_apply]
  refine congrArg _ (Finset.sum_congr rfl fun y _ => ?_)
  rw [liftUp_add_snoc, pushUp_apply, pushUp_apply]

/-- **Forme lake du `sum_smul_inl` de l'oracle** (`Komlos/Split.lean`
l.50-53) : une somme de vecteurs mis à l'échelle, chacun embarqué à
hauteur nulle par `snoc · 0`, est elle-même un vecteur embarqué à hauteur
nulle — la somme pondérée des parties spatiales, queue nulle.

Consommateur mesuré : `Komlos/SignedSums.lean` l.54, où cette identité
sépare la coordonnée de hauteur du point que l'hypothèse d'induction
produit (`rw [mean_split, sum_smul_inl, ...] at hmem`). -/
lemma sum_smul_snoc {d : ℕ} {ι : Type*} (s : Finset ι)
    (ε : ι → ℝ) (r : ι → (Fin d → ℝ)) :
    ∑ i ∈ s, ε i • Fin.snoc (r i) (0 : ℝ)
      = Fin.snoc (∑ i ∈ s, ε i • r i) (0 : ℝ) := by
  funext j
  induction j using Fin.lastCases with
  | last =>
      simp only [Finset.sum_apply, Pi.smul_apply, Fin.snoc_last, smul_eq_mul,
        mul_zero, Finset.sum_const_zero]
  | cast i =>
      simp only [Fin.snoc_castSucc, Finset.sum_apply, Pi.smul_apply]

/-- **Commutation du transport avec l'embedding** : `toReal ∘ liftUp =
snoc ∘ (toReal × hauteur)` — la partie spatiale est transportée par
`toReal` (k2.3), la hauteur `Bool` devient le réel `{0, 1}`.

C'est ce qui referme le carré avec `toRealProd` (k2.4) : l'image
transportée du support poussé dans `Fin (d+1) → ℝ` est la lecture
`(y.1, hauteur y.2)` de l'embedding produit — l'endroit exact où la
conclusion d'induction à la dimension `d+1` nourrit le `pullback` de
k2.4, énoncé dans `(Fin d → ℝ) × ℝ`. -/
lemma toReal_liftUp {d : ℕ} (y : (Fin d → ℤ) × Bool) :
    toReal (liftUp y)
      = Fin.snoc (toReal y.1) (if y.2 then (1 : ℝ) else 0) := by
  funext j
  obtain ⟨x, b⟩ := y
  cases b <;> induction j using Fin.lastCases <;> simp [liftUp]

end Discrepancy.Komlos
