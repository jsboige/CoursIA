/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
Adapté à `discrepancy_lean` (issue #17845, Karingula–Lovett distillation
arXiv:2609.20979) : toolchain v4.33.0, Mathlib `db584cd6`, convention i18n #4980.

Le source Dahia original vit dans le dépôt `gdahia/Komlos` (module
`Komlos/SignedSums.lean`, toolchain v4.34.0, cadre `Finsupp` sur `E →₀ ℝ`).
L'assemblage final — l'itération `induction n with` du Lemme 1.4 — s'y lit
l.37-58. Ce module du lake porte la distillation entière : la première brique
`sum_smul_inl` y est livrée générique (k2.6, la carte de consommation des
organes mesurée en tête de module, la décision de cadre — option (c) —
arbitrée en k2.6a), puis l'assemblage final lui-même (k2.6c) : le carré réel
`snocReal`, le transport d'enveloppe `mem_convexHull_map_snocReal`, la porte
inductive à deux ensembles `exists_colouring_aux` (fermeture `S` + support
exact `E` — le prix `Finset` du support canonique du `Finsupp` de l'oracle)
et l'énoncé public `exists_isColouring_mean_add_sum_mem_convexHull`.

Réserve de portée levée (mesure k5.2, chantier #21417 cran 2) : la forme
livrée le 10-06 n'était instanciable qu'à famille `v` identiquement nulle — ses
hypothèses de contention sur un `Finset` stable forçaient `v i = 0`
(`contention_stability_forces_zero`, plus bas dans ce fichier, avec l'argument
mesuré). L'énoncé public et la porte inductive portent désormais un jeu de
clauses `B` (sommes signées bornées des générateurs, satisfaisable par une
grande boîte, aucune stabilité requise) : le k2 est clos comme preuve **et**
comme énoncé instanciable. Voir les lignes k2.6c et k5.2 de `FORMAL_STATUS.md`.
-/

import Discrepancy.Basic
import Discrepancy.Komlos.Containment
import Discrepancy.Komlos.Distribution
import Discrepancy.Komlos.Lift
import Discrepancy.Komlos.LiftSplit
import Discrepancy.Komlos.Pullback
import Discrepancy.Komlos.Split

/-!
# Sommes signées — assemblage du Lemme 1.4 (brique k2.6)

L'objectif de ce module est l'assemblage final de la voie élémentaire
(Karingula–Lovett) : l'itération `induction n with` de l'oracle
`gdahia/Komlos` (`SignedSums.lean` l.37-58) qui consomme
`mean_mem_convexHull` en base (l.42), `mean_split` + `sum_smul_inl`
au pas (l.53) et `pullback` en clôture (l.55).

## Carte de généricité (mesurée au 2026-10-06, k2.5 tip 87b4f35871)

L'induction de l'oracle ré-instancie ses organes à chaque niveau sur un
ambiant croissant `E → E × ℝ → (E × ℝ) × ℝ → …` — c'est la généralité de
`E` qui absorbe la croissance. Les organes k2.0–k2.5 du lake sont
monomorphes (`Fin d → ℤ`, hauteur `Bool`) :

| Organe oracle | Notre lake | État |
|---|---|---|
| `split : (E →₀ ℝ) → (E × ℝ →₀ ℝ)` | `Split.split` (`Fin d → ℤ`, `× Bool`) | monomorphe |
| `mean_split` (barycentre conservé) | `MeanSplit.mean_split_of_support` | monomorphe |
| `shiftDist_split_le` | acquis k1.6 | monomorphe |
| `splitBit_eq` | `SplitBit` | monomorphe |
| `pullback` (générique) | `Pullback.pullback` (`toReal`/`toRealProd`) | monomorphe |
| `mean_mem_convexHull` | `Distribution.mean_mem_convexHull` (k2.5) | monomorphe |
| `sum_smul_inl` | **absent — livré ci-dessous, générique** | ✓ k2.6 |
| convexHull (`add_smul`/`sum_smul`/`mem_convexHull'`) | `Pullback` l.150/189/213 | ✓ génériques |

L'écart d'architecture est **arbitré en k2.6a** (option (c) : l'espace
qui grandit est réalisé `Fin (d + k) → ℤ` par l'embedding `liftUp`, sans
re-généralisation des organes — la voie α est écartée, la voie β
(ping-pong deux espaces) est close par la mesure). `sum_smul_inl` reste
l'organe générique ℝ-modulaire, **complémentaire de `sum_smul_snoc`**
(k2.6a, forme lake côté grille) : consommable côté transport/hull, où
les moments vivent dans `ℝ`.
-/

namespace Discrepancy.Komlos

/-- La composante gauche d'une somme de vecteurs `ε i • (v i, 0)` est la
somme des composantes gauches — le pendant `Finset` du `sum_smul_inl` de
l'oracle (`split.lean` l.50), utilisé par la réécriture `rw [mean_split,
sum_smul_inl, …]` du pas inductif. Générique en `E` : c'est le seul
organe du pas que le lake n'avait pas, et il ne dépend pas de la grille. -/
lemma sum_smul_inl {n : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
    (ε : Fin n → ℝ) (v : Fin n → E) :
    (∑ i, ε i • (v i, (0 : ℝ))) = (∑ i, ε i • v i, (0 : ℝ)) := by
  refine Prod.ext ?_ ?_ <;> simp [Prod.smul_mk, Prod.fst_sum, Prod.snd_sum]

/-! ### Brique k2.6c : l'assemblage final — l'induction du Lemme 1.4 -/

/-- **L'isomorphisme `snoc` côté réel** : `(Fin d → ℝ) × ℝ → (Fin (d+1) → ℝ)`,
`(z, t) ↦ snoc z t`. C'est la forme réelle du pont de niveau : le carré
`toReal ∘ liftUp = snoc ∘ toRealProd` (cf `toReal_liftUp`, k2.6a) dit que
transporter le support poussé dans la dimension agrandie revient à
`snoc`-er le support produit transporté — et c'est par là que la conclusion
d'induction à la dimension `d+1` nourrit le `pullback` de k2.4, énoncé dans
`(Fin d → ℝ) × ℝ`. -/
def snocReal {d : ℕ} : ((Fin d → ℝ) × ℝ) → (Fin (d + 1) → ℝ) :=
  fun p => Fin.snoc p.1 p.2

lemma snocReal_apply_castSucc {d : ℕ} (p : (Fin d → ℝ) × ℝ) (j : Fin d) :
    snocReal p j.castSucc = p.1 j := by simp [snocReal]

lemma snocReal_apply_last {d : ℕ} (p : (Fin d → ℝ) × ℝ) :
    snocReal p (Fin.last d) = p.2 := by simp [snocReal]

/-- **Le carré réel** : `snocReal (toRealProd y) = toReal (liftUp y)` —
la lecture combinée de `toReal_liftUp` (k2.6a) et de la définition
`toRealProd` (k2.4). C'est la seule équation qui manque au transport des
enveloppes entre les deux lectures de la dimension agrandie. -/
lemma snocReal_toRealProd {d : ℕ} (y : (Fin d → ℤ) × Bool) :
    snocReal (toRealProd y) = toReal (liftUp y) := by
  rw [toReal_liftUp]
  funext j
  simp [snocReal, toRealProd]

lemma snocReal_injective {d : ℕ} : Function.Injective (snocReal (d := d)) := by
  rintro ⟨z₁, t₁⟩ ⟨z₂, t₂⟩ h
  have h1 : z₁ = z₂ := by
    funext j
    have := congrFun h j.castSucc
    simpa [snocReal] using this
  have h2 : t₁ = t₂ := by
    have := congrFun h (Fin.last d)
    simpa [snocReal] using this
  exact Prod.ext h1 h2

/-- La version `Finset.Embedding` de `snocReal`, pour les `Finset.map` des
supports transportés. -/
def snocRealEmb {d : ℕ} : ((Fin d → ℝ) × ℝ) ↪ (Fin (d + 1) → ℝ) :=
  ⟨snocReal, snocReal_injective⟩

lemma snocRealEmb_apply {d : ℕ} (p : (Fin d → ℝ) × ℝ) : snocRealEmb p = snocReal p := rfl

/-- `snocReal` comme application `ℝ`-linéaire. C'est la structure qui
transporte les enveloppes convexes : `LinearMap.image_convexHull` identifie
l'enveloppe de l'image à l'image de l'enveloppe, et l'injectivité restitue
le point — le lemme de transport ci-dessous en découle immédiatement. -/
def snocLM {d : ℕ} : ((Fin d → ℝ) × ℝ) →ₗ[ℝ] (Fin (d + 1) → ℝ) where
  toFun p := snocReal p
  map_add' p q := by
    funext j
    induction j using Fin.lastCases with
    | last => simp [snocReal, Fin.snoc_last, Pi.add_apply]
    | cast i => simp [snocReal, Fin.snoc_castSucc, Pi.add_apply]
  map_smul' c p := by
    funext j
    induction j using Fin.lastCases with
    | last => simp [snocReal, Fin.snoc_last, Pi.smul_apply, smul_eq_mul]
    | cast i => simp [snocReal, Fin.snoc_castSucc, Pi.smul_apply, smul_eq_mul]

/-- **Transport d'enveloppe à travers `snoc`** : appartenir à l'enveloppe
d'un ensemble fini `snoc`-é, c'est appartenir à l'enveloppe de l'ensemble
source.

C'est l'organe qui referme le carré de diagramme pour l'assemblage k2.6c :
l'hypothèse d'induction conclut dans `Fin (d+1) → ℝ` (enveloppe du support
poussé transporté), le `pullback` de k2.4 consomme `(Fin d → ℝ) × ℝ`
(enveloppe du support produit transporté) — la correspondance est exactement
ce transport. Preuve : `snocReal` est linéaire (`snocLM`) et injective, et
`LinearMap.image_convexHull` commute l'enveloppe et l'image. -/
lemma mem_convexHull_map_snocReal {d : ℕ} {E : Finset ((Fin d → ℝ) × ℝ)}
    {p : (Fin d → ℝ) × ℝ} :
    snocReal p ∈ convexHull ℝ
      (↑(E.map snocRealEmb) : Set ((Fin (d + 1) → ℝ))) ↔
      p ∈ convexHull ℝ (↑E : Set ((Fin d → ℝ) × ℝ)) := by
  have hset : (↑(E.map snocRealEmb) : Set ((Fin (d + 1) → ℝ)))
      = (⇑snocLM) '' (↑E : Set ((Fin d → ℝ) × ℝ)) := by
    rw [Finset.coe_map]
    rfl
  rw [hset, ← LinearMap.image_convexHull]
  constructor
  · rintro ⟨q, hq, hfq⟩
    rwa [snocReal_injective hfq] at hq
  · exact fun h => ⟨p, h, rfl⟩

/-! ### La porte inductive : deux ensembles, `S` la fermeture et `E` le support -/

/-- **Lemme 1.4 (Karingula–Lovett), forme lake — la porte inductive**.

Chez l'oracle (`gdahia/Komlos`, `SignedSums.lean` l.37-58), l'induction vit
sur les `Finsupp` : le support exact est canonique à chaque niveau, et la
conclusion d'hypothèse d'induction se consomme telle quelle par `pullback`.
Le cadre `Finset` explicite du lake doit payer ce transport : la contenance
`SupportContained` (k1.7) exige un support **fermé par décalages de `A`**
(les points de masse déplacés y atterrissent), tandis que le `pullback`
(k2.4) exige une enveloppe portée par le **support exact** de la scission
(`hSQ : ∀ y ∈ SQ, split v P y ≠ 0`). Ces deux rôles sont incompatibles sur
un seul `Finset` : la porte en porte donc deux — `S` (fermeture : masse,
moments, contenance) et `E` (support exact : enveloppe de la conclusion,
`E ⊆ S`).

Au niveau suivant, `S'` est l'image liftée du produit plein (la contenance
y est transférée par `supportContained_pushUp_split_enlarged`, l'organe de
transmission du chantier #21417) et `E'` le support exact poussé (`SQ.map
liftUpEmb`, `SQ` le filtre des scissions non nulles). Le pont entre les deux
lectures est le carré `snocReal ∘ toRealProd = toReal ∘ liftUp` plus le
transport d'enveloppe `mem_convexHull_map_snocReal` (ci-dessus).

**Chantier #21417 (correction du défaut k5.2)** : la porte ne porte plus
d'ensemble `A` stable par `± 3 • v i` — une classe d'orbite, insatisfaisable
sur un `Finset` pour `v ≠ 0` (le témoin `contention_stability_forces_zero`
ci-dessous démontre que ces hypothèses forcent `v = 0`). Elle porte un **jeu
de clauses** : un `Finset B` contenant les sommes signées à coefficients
bornés par 2 en les générateurs `3 • v i` (5ⁿ points, satisfaisable par une
grande boîte — aucune stabilité n'est exigée de `B`), avec la contenance
`SupportContained S P B`. L'équation de transmission se vérifie niveau par
niveau : chaque clause du niveau `d + 1` (somme bornée des `n` premiers
générateurs, snocquée à hauteur nulle) vit dans l'ombre
`(B + w) ∩ (B − w)` car sa base `z` vérifie `z ± w ∈ B` — le coefficient du
générateur dernier passe de `0` à `± 1`, borné par 2. -/
theorem exists_colouring_aux (n : ℕ) :
    ∀ (d : ℕ) (S E : Finset (Fin d → ℤ)) (P : (Fin d → ℤ) → ℝ),
      (∀ x, 0 ≤ P x) → (∑ x ∈ S, P x = 1) →
      (∀ x, P x ≠ 0 → x ∈ E) → E ⊆ S →
      ∀ B : Finset (Fin d → ℤ),
      ∀ v : Fin n → (Fin d → ℤ),
      (∀ f : Fin n → ℤ, (∀ i, |f i| ≤ 2) → ∑ i, f i • (3 • v i) ∈ B) →
      SupportContained S P B →
      (∀ i, shiftDistance S P (6 • v i) ≤ 3⁻¹) →
      ∃ ε : Fin n → ℤ, (∀ i, ε i = 1 ∨ ε i = -1) ∧
        (fun j => coordMoment P S j + ∑ i, (ε i : ℝ) * (v i j : ℝ)) ∈
          convexHull ℝ
            ↑(E.map (⟨⇑toReal, toReal_injective⟩ : (Fin d → ℤ) ↪ (Fin d → ℝ))) := by
  induction n with
  | zero =>
      intro d S E P hP0 hmass hE hES B v hclauses hC hv
      have hzero : ∀ x ∈ S, x ∉ E → P x = 0 := by
        intro x _ hx
        by_contra hp
        exact hx (hE x hp)
      have hmassE : ∑ x ∈ E, P x = 1 := by
        rw [← hmass]
        exact Finset.sum_subset hES hzero
      have hmean := mean_mem_convexHull hP0 hmassE
      refine ⟨fun _ => 1, fun i => i.elim0, ?_⟩
      have hfun : (fun j => coordMoment P S j
          + ∑ i : Fin 0, ((fun _ => 1 : Fin 0 → ℤ) i : ℝ) * (v i j : ℝ))
          = (fun j => coordMoment P E j) := by
        funext j
        have hvan : ∀ x ∈ S, x ∉ E → P x * (x j : ℝ) = 0 := by
          intro x _ hxE
          by_contra hp
          exact hxE (hE x (fun h0 => hp (by rw [h0]; ring)))
        simp only [coordMoment]
        rw [Finset.sum_subset hES hvan]
        simp
      rw [hfun]
      exact hmean
  | succ n ih =>
      intro d S E P hP0 hmass hE hES B v hclauses hC hv
      classical
      -- Le vecteur de scission
      set w : Fin d → ℤ := 3 • v (Fin.last n) with hw
      -- Évaluation des sommes signées de la famille de clauses
      have hsum1 : ∀ (a : Fin (n + 1)) (x : ℤ),
          ∑ i, (if i = a then x else 0) • (3 • v i) = x • (3 • v a) := by
        intro a x
        rw [Finset.sum_eq_single a]
        · simp
        · intro b _ hb; simp [hb]
        · simp
      have hsum2 : ∀ (a b : Fin (n + 1)) (hab : a ≠ b) (x y : ℤ),
          ∑ i, (if i = a then x else if i = b then y else 0) • (3 • v i)
            = x • (3 • v a) + y • (3 • v b) := by
        intro a b hab x y
        have hsplit : ∀ i ∈ (Finset.univ : Finset (Fin (n + 1))),
            (if i = a then x else if i = b then y else 0) • (3 • v i)
              = (if i = a then x • (3 • v i) else 0)
                + (if i = b then y • (3 • v i) else 0) := by
          intro i _
          by_cases h1 : i = a
          · subst h1
            simp [hab]
          · by_cases h2 : i = b
            · subst h2
              simp [h1]
            · simp [h1, h2]
        rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib,
          Finset.sum_ite_eq' Finset.univ a (fun i => x • (3 • v i)),
          Finset.sum_ite_eq' Finset.univ b (fun i => y • (3 • v i))]
        simp
      -- Appartenances de base par la famille de clauses (aucune stabilité)
      have hm0 : (0 : Fin d → ℤ) ∈ B := by
        have h := hclauses (fun _ => 0) (by intro i; simp)
        simpa using h
      have hmw : w ∈ B := by
        have h := hclauses (fun i => if i = Fin.last n then (1 : ℤ) else 0)
          (by intro i; by_cases h : i = Fin.last n <;> simp [h])
        rw [hsum1 (Fin.last n) 1] at h
        simpa [hw] using h
      have hmnw : -w ∈ B := by
        have h := hclauses (fun i => if i = Fin.last n then (-1 : ℤ) else 0)
          (by intro i; by_cases h : i = Fin.last n <;> simp [h, abs_neg])
        rw [hsum1 (Fin.last n) (-1)] at h
        simpa [hw] using h
      have mono3 : SupportContained S P ({0, w, -w} : Finset (Fin d → ℤ)) :=
        hC.mono (by
          intro t ht
          simp only [Finset.mem_insert, Finset.mem_singleton] at ht ⊢
          rcases ht with rfl | rfl | rfl
          · exact hm0
          · exact hmw
          · exact hmnw)
      -- Les données de niveau d + 1
      set SQ : Finset ((Fin d → ℤ) × Bool) :=
        (S ×ˢ (Finset.univ : Finset Bool)).filter (fun y => split w P y ≠ 0)
        with hSQ
      set S' : Finset (Fin (d + 1) → ℤ) :=
        (S ×ˢ (Finset.univ : Finset Bool)).map liftUpEmb with hS'
      set E' : Finset (Fin (d + 1) → ℤ) := SQ.map liftUpEmb with hE'
      set B' : Finset (Fin (d + 1) → ℤ) :=
        (B.image (fun b => b + w) ∩ B.image (fun b => b - w)).image
          (fun a => Fin.snoc a 0) with hB'
      -- Les arguments du niveau suivant
      have hP0' : ∀ z, 0 ≤ pushUp (split w P) z :=
        fun z => pushUp_nonneg (split_nonneg hP0 w) z
      have hmass' : ∑ z ∈ S', pushUp (split w P) z = 1 := by
        rw [hS', pushUp_mass, split_mass_of_support w mono3]
        exact hmass
      have hsupp' : ∀ z, pushUp (split w P) z ≠ 0 → z ∈ E' := by
        intro z hz
        by_cases hy : ∃ y : (Fin d → ℤ) × Bool, liftUp y = z
        · obtain ⟨y, rfl⟩ := hy
          have hy' : split w P y ≠ 0 := by
            rw [← pushUp_apply (split w P) y]
            exact hz
          -- l'antécédent vit dans S ×ˢ univ
          have hy1 : y.1 ∈ S := by
            obtain ⟨x, b⟩ := y
            have hne : P (x + w) ≠ 0 ∨ P (x - w) ≠ 0 := by
              cases b with
              | false =>
                  rw [split_apply_zero] at hy'
                  rcases le_total (P (x + w)) (P (x - w)) with h | h
                  · rw [max_eq_right h] at hy'
                    exact Or.inr (by intro h0; rw [h0, mul_zero] at hy'; exact hy' rfl)
                  · rw [max_eq_left h] at hy'
                    exact Or.inl (by intro h0; rw [h0, mul_zero] at hy'; exact hy' rfl)
              | true =>
                  rw [split_apply_one] at hy'
                  rcases le_total (P (x + w)) (P (x - w)) with h | h
                  · rw [min_eq_left h] at hy'
                    exact Or.inl (by intro h0; rw [h0, mul_zero] at hy'; exact hy' rfl)
                  · rw [min_eq_right h] at hy'
                    exact Or.inr (by intro h0; rw [h0, mul_zero] at hy'; exact hy' rfl)
            rcases hne with h | h
            · have hx := hC (x + w) h (-w) hmnw
              simpa using hx
            · have hx := hC (x - w) h w hmw
              simpa using hx
          refine Finset.mem_map.2 ⟨y, Finset.mem_filter.2 ⟨?_, hy'⟩, rfl⟩
          exact Finset.mem_product.2 ⟨hy1, Finset.mem_univ _⟩
        · exact absurd (pushUp_eq_zero (split w P)
            (fun y hy' => hy ⟨y, hy'⟩)) hz
      have hES' : E' ⊆ S' := by
        intro z hz
        obtain ⟨y, hy, rfl⟩ := Finset.mem_map.1 hz
        exact Finset.mem_map.2 ⟨y, Finset.filter_subset _ _ hy, rfl⟩
      -- La contenance du niveau suivant : l'organe de transmission (#21417)
      have hC' : SupportContained S' (pushUp (split w P)) B' :=
        supportContained_pushUp_split_enlarged w hC
      -- Les clauses du niveau suivant : chaque somme bornée snocquée vit
      -- dans l'ombre (B + w) ∩ (B − w), car sa base z vérifie z ± w ∈ B
      have hclauses' : ∀ g : Fin n → ℤ, (∀ i, |g i| ≤ 2) →
          ∑ i, g i • (3 • (liftUp (v i.castSucc, false) : Fin (d + 1) → ℤ)) ∈ B' := by
        intro g hg
        have hlift : ∀ i : Fin n,
            3 • (liftUp (v i.castSucc, false) : Fin (d + 1) → ℤ)
              = Fin.snoc (3 • v i.castSucc) 0 := by
          intro i
          funext j
          induction j using Fin.lastCases with
          | last => simp [liftUp]
          | cast k => simp [liftUp, Pi.smul_apply]
        set z : Fin d → ℤ := ∑ i, g i • (3 • v i.castSucc) with hzdef
        have hsum' : ∑ i, g i • (3 • (liftUp (v i.castSucc, false) : Fin (d + 1) → ℤ))
            = Fin.snoc z 0 := by
          funext j
          induction j using Fin.lastCases with
          | last => simp
          | cast k =>
              rw [Finset.sum_apply]
              simp only [hlift, Fin.snoc_castSucc, Pi.smul_apply, smul_eq_mul,
                hzdef]
              rw [Finset.sum_apply]
              simp
        have hzw : z - w ∈ B := by
          have h := hclauses (Fin.snoc g (-1 : ℤ))
            (by
              intro i
              induction i using Fin.lastCases with
              | last => simp [abs_neg]
              | cast k => simpa using hg k)
          rw [Fin.sum_univ_castSucc] at h
          simp only [Fin.snoc_castSucc, Fin.snoc_last, neg_one_smul] at h
          rw [← hzdef] at h
          rw [sub_eq_add_neg, hw]
          exact h
        have hzpw : z + w ∈ B := by
          have h := hclauses (Fin.snoc g (1 : ℤ))
            (by
              intro i
              induction i using Fin.lastCases with
              | last => simp
              | cast k => simpa using hg k)
          rw [Fin.sum_univ_castSucc] at h
          simp only [Fin.snoc_castSucc, Fin.snoc_last, one_smul] at h
          rw [← hzdef] at h
          rw [hw]
          exact h
        rw [hsum']
        refine Finset.mem_image.mpr ⟨z, ?_, rfl⟩
        simp only [Finset.mem_inter, Finset.mem_image]
        refine ⟨⟨z - w, hzw, ?_⟩, z + w, hzpw, ?_⟩
        · funext j; simp only [Pi.add_apply, Pi.sub_apply]; omega
        · funext j; simp only [Pi.add_apply, Pi.sub_apply]; omega
      have hv' : ∀ i : Fin n,
          shiftDistance S' (pushUp (split w P)) (6 • liftUp (v i.castSucc, false))
            ≤ 3⁻¹ := by
        intro i
        have h6 : 6 • liftUp (v i.castSucc, false)
            = Fin.snoc (6 • v i.castSucc) 0 := by
          funext j
          induction j using Fin.lastCases with
          | last => simp [liftUp]
          | cast k => simp [liftUp, Pi.smul_apply]
        -- la contention à six décalages, par la famille de clauses
        have hmn6 : -(6 • v i.castSucc) ∈ B := by
          have h := hclauses (fun j => if j = i.castSucc then (-2 : ℤ) else 0)
            (by intro j; by_cases h : j = i.castSucc <;> simp [h, abs_neg])
          have hid : ((-2 : ℤ) • (3 • v i.castSucc) : Fin d → ℤ)
              = -(6 • v i.castSucc) := by
            funext j
            simp only [Pi.smul_apply, Pi.neg_apply]
            ring
          rw [hsum1 i.castSucc (-2), hid] at h
          exact h
        have hwu : w - 6 • v i.castSucc ∈ B := by
          have h := hclauses
            (fun j => if j = Fin.last n then (1 : ℤ) else
              if j = i.castSucc then (-2 : ℤ) else 0)
            (by intro j
                by_cases h1 : j = Fin.last n
                · simp [h1]
                · by_cases h2 : j = i.castSucc <;> simp [h1, h2, abs_neg])
          have hid : (((1 : ℤ) • (3 • v (Fin.last n))
              + (-2 : ℤ) • (3 • v i.castSucc) : Fin d → ℤ))
              = w - 6 • v i.castSucc := by
            funext j
            simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, hw]
            ring
          rw [hsum2 (Fin.last n) i.castSucc
            (by
              intro h
              have h2 := congrArg Fin.val h
              simp only [Fin.val_last, Fin.val_castSucc] at h2
              omega) 1 (-2), hid] at h
          exact h
        have hnwu : -w - 6 • v i.castSucc ∈ B := by
          have h := hclauses
            (fun j => if j = Fin.last n then (-1 : ℤ) else
              if j = i.castSucc then (-2 : ℤ) else 0)
            (by intro j
                by_cases h1 : j = Fin.last n
                · simp [h1, abs_neg]
                · by_cases h2 : j = i.castSucc <;> simp [h1, h2, abs_neg])
          have hid : (((-1 : ℤ) • (3 • v (Fin.last n))
              + (-2 : ℤ) • (3 • v i.castSucc) : Fin d → ℤ))
              = -w - 6 • v i.castSucc := by
            funext j
            simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.neg_apply, hw]
            ring
          rw [hsum2 (Fin.last n) i.castSucc
            (by
              intro h
              have h2 := congrArg Fin.val h
              simp only [Fin.val_last, Fin.val_castSucc] at h2
              omega) (-1) (-2), hid] at h
          exact h
        have h6set : SupportContained S P
            ({0, w, -w, -(6 • v i.castSucc), w - 6 • v i.castSucc,
              -w - 6 • v i.castSucc} : Finset (Fin d → ℤ)) :=
          hC.mono (by
            intro t ht
            simp only [Finset.mem_insert, Finset.mem_singleton] at ht ⊢
            rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
            · exact hm0
            · exact hmw
            · exact hmnw
            · exact hmn6
            · exact hwu
            · exact hnwu)
        rw [h6, hS', shiftDistance_pushUp]
        exact (shiftDistanceProd_split_le_of_support w (6 • v i.castSucc)
          hP0 hmass h6set).trans (hv i.castSucc)
      obtain ⟨ε', hε', hmem'⟩ := ih (d + 1) S' E' (pushUp (split w P))
        hP0' hmass' hsupp' hES' B' (fun i => liftUp (v i.castSucc, false))
        hclauses' hC' hv'
      -- Le point de niveau d + 1, lu coordonnée par coordonnée
      set z : Fin d → ℝ := fun k =>
        coordMoment P S k + ∑ i : Fin n, (ε' i : ℝ) * (v i.castSucc k : ℝ)
        with hz
      set β : ℝ := splitBit w P S with hb
      have hpt : (fun j => coordMoment (pushUp (split w P)) S' j
            + ∑ i : Fin n, (ε' i : ℝ) * ((liftUp (v i.castSucc, false)) j : ℝ))
          = Fin.snoc z β := by
        funext j
        induction j using Fin.lastCases with
        | last =>
            show coordMoment (pushUp (split w P)) S' (Fin.last d)
              + ∑ i : Fin n, (ε' i : ℝ)
                  * ((liftUp (v i.castSucc, false)) (Fin.last d) : ℝ)
              = (Fin.snoc z β : Fin (d + 1) → ℝ) (Fin.last d)
            rw [hS', coordMoment_pushUp_split_last w P S, hb]
            simp
        | cast k =>
            show coordMoment (pushUp (split w P)) S' k.castSucc
              + ∑ i : Fin n, (ε' i : ℝ)
                  * ((liftUp (v i.castSucc, false)) k.castSucc : ℝ)
              = (Fin.snoc z β : Fin (d + 1) → ℝ) k.castSucc
            rw [hS', coordMoment_pushUp_split_of_support w mono3 k, hz]
            simp
      have hmem2 : (fun j => coordMoment (pushUp (split w P)) S' j
            + ∑ i : Fin n, (ε' i : ℝ) * ((liftUp (v i.castSucc, false)) j : ℝ))
          ∈ convexHull ℝ
            ↑(E'.map (⟨⇑toReal, toReal_injective⟩ :
              (Fin (d + 1) → ℤ) ↪ (Fin (d + 1) → ℝ))) := hmem'
      rw [hpt] at hmem2
      -- le carré : le support poussé transporté est l'image snocReal
      have hmapE : E'.map
            (⟨⇑toReal, toReal_injective⟩ : (Fin (d + 1) → ℤ) ↪ (Fin (d + 1) → ℝ))
          = (SQ.map toRealProdEmb).map snocRealEmb := by
        apply Finset.ext
        intro t
        simp only [Finset.mem_map]
        constructor
        · rintro ⟨q, hq, rfl⟩
          obtain ⟨y, hy, rfl⟩ := Finset.mem_map.1 hq
          exact ⟨toRealProd y, ⟨y, hy, rfl⟩, snocReal_toRealProd y⟩
        · rintro ⟨r, hr, rfl⟩
          obtain ⟨y, hy, rfl⟩ := hr
          exact ⟨liftUp y, Finset.mem_map.2 ⟨y, hy, rfl⟩,
            (snocReal_toRealProd y).symm⟩
      rw [hmapE] at hmem2
      have h1 : Fin.snoc z β = snocReal (z, β) := rfl
      rw [h1] at hmem2
      obtain hmempb := (mem_convexHull_map_snocReal
        (E := SQ.map toRealProdEmb) (p := (z, β))).mp hmem2
      -- la clé de hauteur : splitBit ≥ 1/3
      have hw2 : w + w = 6 • v (Fin.last n) := by
        funext j
        simp only [Pi.add_apply, Pi.smul_apply, hw]
        ring
      have hidww : -(w + w) = -w - w := by
        funext j
        simp only [Pi.add_apply, Pi.neg_apply, Pi.sub_apply, hw]
        ring
      have hmww : -w - w ∈ B := by
        have h := hclauses (fun j => if j = Fin.last n then (-2 : ℤ) else 0)
          (by intro j; by_cases h : j = Fin.last n <;> simp [h, abs_neg])
        have hid : (-2 : ℤ) • (3 • v (Fin.last n)) = -w - w := by
          funext j
          simp only [Pi.smul_apply, Pi.sub_apply, Pi.neg_apply, smul_eq_mul, hw]
          ring
        rw [hsum1 (Fin.last n) (-2), hid] at h
        exact h
      have hP5 : SupportContained S P
          ({0, w, -w, -w - w, -(w + w)} : Finset (Fin d → ℤ)) :=
        hC.mono (by
          intro t ht
          simp only [Finset.mem_insert, Finset.mem_singleton] at ht ⊢
          rcases ht with rfl | rfl | rfl | rfl | rfl
          · exact hm0
          · exact hmw
          · exact hmnw
          · exact hmww
          · rw [hidww]
            exact hmww)
      have hβ : 3⁻¹ ≤ β := by
        rw [hb, splitBit_eq_of_support w hP0 hmass hP5, hw2]
        linarith [hv (Fin.last n)]
      -- le rappel : z + e • toReal (v dernier) ∈ enveloppe du support de P
      obtain ⟨e, he, hfin⟩ := pullback (v := w) (w := v (Fin.last n)) hP0 hE
        (fun i => by rw [hw]; simp)
        (fun y hy => (Finset.mem_filter.1 hy).2)
        hβ hmempb
      -- l'assemblage final
      have hēe : ((if e = 1 then 1 else -1 : ℤ) : ℝ) = e := by
        rcases he with h | h
        · rw [if_pos h, h]
          norm_num
        · rw [if_neg (by rw [h]; norm_num), h]
          norm_num
      refine ⟨Fin.snoc ε' (if e = 1 then 1 else -1), ?_, ?_⟩
      · intro i
        induction i using Fin.lastCases with
        | last =>
            simp only [Fin.snoc_last]
            rcases he with h | h
            · exact Or.inl (by rw [if_pos h])
            · exact Or.inr (by rw [if_neg (by rw [h]; norm_num)])
        | cast j => simpa using hε' j
      · have hfe : (fun j => coordMoment P S j
            + ∑ i : Fin (n + 1),
                ((Fin.snoc ε' (if e = 1 then 1 else -1) : Fin (n + 1) → ℤ) i : ℝ)
                  * (v i j : ℝ))
          = z + e • toReal (v (Fin.last n)) := by
          funext j
          rw [Fin.sum_univ_castSucc, Fin.snoc_last, hēe]
          simp only [Fin.snoc_castSucc, Pi.add_apply, Pi.smul_apply, toReal_apply, hz]
          ring
        rw [hfe]
        exact hfin

/-- **Lemme 1.4 (Karingula–Lovett) — énoncé public** : si `S` contient le
support de `P` décalé par chaque somme signée à coefficients bornés par 2
en les générateurs `3 • v i`, et si chaque `6 • v i` a une distance de
décalage `≤ 1/3`, il existe une coloration `ε` telle que le barycentre de
`P` augmenté des sommes signées appartienne à l'enveloppe convexe du
support transporté de `P`.

Le jeu de clauses `B` est fourni par l'appelant — typiquement l'image des
coefficients bornés (5ⁿ points, une « grande boîte » satisfaisable,
**aucune stabilité requise**) : c'est la correction du chantier #21417 du
défaut k2.6c (l'ancienne forme portait un `A` stable par `± 3 • v i`, une
classe d'orbite qui force `v = 0` — le témoin
`contention_stability_forces_zero` ci-dessous). Exiger `B` explicite
garde l'hypothèse vérifiable par l'appelant sans enfermer la porte
inductive dans une instanciation figée.

La forme porte (`exists_colouring_aux`) conclut sur le support exact `E` ;
l'énoncé public le consomme avec `E := S.filter (P · ≠ 0)` et remonte à
l'enveloppe de `S` par monotonie — c'est la lecture lake de l'oracle
`gdahia/Komlos` (`SignedSums.lean` l.32-36), où le `Finsupp` porte son
support canonique. -/
theorem exists_isColouring_mean_add_sum_mem_convexHull (n d : ℕ)
    (S B : Finset (Fin d → ℤ)) (P : (Fin d → ℤ) → ℝ) (hP0 : ∀ x, 0 ≤ P x)
    (hmass : ∑ x ∈ S, P x = 1) (hPsupp : ∀ x, P x ≠ 0 → x ∈ S)
    (v : Fin n → (Fin d → ℤ))
    (hclauses : ∀ f : Fin n → ℤ, (∀ i, |f i| ≤ 2) → ∑ i, f i • (3 • v i) ∈ B)
    (hB : SupportContained S P B)
    (hv : ∀ i, shiftDistance S P (6 • v i) ≤ 3⁻¹) :
    ∃ ε : Fin n → ℤ, (∀ i, ε i = 1 ∨ ε i = -1) ∧
      (fun j => coordMoment P S j + ∑ i, (ε i : ℝ) * (v i j : ℝ)) ∈
        convexHull ℝ
          ↑(S.map (⟨⇑toReal, toReal_injective⟩ : (Fin d → ℤ) ↪ (Fin d → ℝ))) := by
  obtain ⟨ε, hε, hmem⟩ := exists_colouring_aux n d S (S.filter (fun x => P x ≠ 0)) P
    hP0 hmass (fun x hx => Finset.mem_filter.2 ⟨hPsupp x hx, hx⟩)
    (Finset.filter_subset _ _) B v hclauses hB hv
  refine ⟨ε, hε, ?_⟩
  have hsub : (S.filter (fun x => P x ≠ 0)).map
      (⟨⇑toReal, toReal_injective⟩ : (Fin d → ℤ) ↪ (Fin d → ℝ))
    ⊆ S.map (⟨⇑toReal, toReal_injective⟩ : (Fin d → ℤ) ↪ (Fin d → ℝ)) :=
    Finset.map_subset_map.mpr (Finset.filter_subset _ _)
  exact convexHull_mono (Finset.coe_subset.2 hsub) hmem

/-- **Le défaut de l'énoncé public du Lemme 1.4, démontré** (mesure k5.2) :
les hypothèses de contention `hA0 : 0 ∈ A` et
`hAstab : ∀ a ∈ A, ∀ i, a + 3 • v i ∈ A ∧ a - 3 • v i ∈ A` d'un `Finset`
forcent `v i = 0` pour tout `i`. L'argument est l'orbite de
`eq_zero_of_image_add_eq_self` (k1.7) transposée de `S` à `A` : la stabilité
de `A` par `+ 3 • v i` dit que `A.image (fun x => x + 3 • v i) ⊆ A`, l'image
d'une translation a même cardinal, donc l'égalité, et l'invariance d'image
d'un ensemble non vide force le décalage nul dans le groupe sans torsion
`ℤ^d`.

Conséquence mesurée : `exists_isColouring_mean_add_sum_mem_convexHull`
n'est instanciable qu'à famille `v` identiquement nulle — le régime où
`shiftDistance S P (6 • v i) ≤ 3⁻¹` est trivial et la conclusion ne porte
aucune somme. C'est la même classe de défaut que celle mesurée en k1.7 sur
l'invariance de `S` (hypothèse de stabilité par translation non nulle sur un
ensemble fini), réintroduite au sommet k2.6 sur `A`. **Correctif livré
(chantier #21417)** : la porte inductive ne porte plus d'ensemble stable —
la contention est réifiée sur un jeu de clauses `B` (sommes signées à
coefficients bornés par 2 en les `3 • v i`, satisfaisable par grande boîte),
transmise par `supportContained_pushUp_split_enlarged` (intersection des
translatés) ; `shiftDistance` garde sa forme k1.1, la passerelle
`shiftDistance_eq_shiftDistanceTV` (k4.2c) reste disponible comme lecture
alternative. L'assemblage k5.2 (GridCase) en dépend. -/
theorem contention_stability_forces_zero {d n : ℕ} (v : Fin n → (Fin d → ℤ))
    {A : Finset (Fin d → ℤ)} (hA0 : 0 ∈ A)
    (hAstab : ∀ a ∈ A, ∀ i, a + 3 • v i ∈ A ∧ a - 3 • v i ∈ A) :
    ∀ i, v i = 0 := by
  intro i
  have hsub : A.image (fun x => x + 3 • v i) ⊆ A := by
    intro y hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy
    exact (hAstab a ha i).1
  have hcard : (A.image (fun x => x + 3 • v i)).card = A.card :=
    Finset.card_image_of_injective _ (fun x y h => add_right_cancel h)
  have hEq : A.image (fun x => x + 3 • v i) = A :=
    Finset.eq_of_subset_of_card_le hsub (hcard ▸ Nat.le_refl _)
  have h3 : 3 • v i = 0 :=
    eq_zero_of_image_add_eq_self hEq ⟨0, hA0⟩
  funext j
  have hcoord : (3 • v i) j = 0 := congrFun h3 j
  simpa [Pi.smul_apply] using hcoord

end Discrepancy.Komlos
