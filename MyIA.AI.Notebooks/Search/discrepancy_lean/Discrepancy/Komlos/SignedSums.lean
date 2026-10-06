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
y est transférée par `supportContained_pushUp_split`, k2.6b) et `E'` le
support exact poussé (`SQ.map liftUpEmb`, `SQ` le filtre des scissions non
nulles). Le pont entre les deux lectures est le carré
`snocReal ∘ toRealProd = toReal ∘ liftUp` plus le transport d'enveloppe
`mem_convexHull_map_snocReal` (ci-dessus). -/
theorem exists_colouring_aux (n : ℕ) :
    ∀ (d : ℕ) (S E : Finset (Fin d → ℤ)) (P : (Fin d → ℤ) → ℝ),
      (∀ x, 0 ≤ P x) → (∑ x ∈ S, P x = 1) →
      (∀ x, P x ≠ 0 → x ∈ E) → E ⊆ S →
      ∀ A : Finset (Fin d → ℤ), 0 ∈ A → SupportContained S P A →
      ∀ v : Fin n → (Fin d → ℤ),
      (∀ i, v i ∈ A ∧ -v i ∈ A) →
      (∀ a ∈ A, ∀ i, a + 3 • v i ∈ A ∧ a - 3 • v i ∈ A) →
      (∀ i, shiftDistance S P (6 • v i) ≤ 3⁻¹) →
      ∃ ε : Fin n → ℤ, (∀ i, ε i = 1 ∨ ε i = -1) ∧
        (fun j => coordMoment P S j + ∑ i, (ε i : ℝ) * (v i j : ℝ)) ∈
          convexHull ℝ
            ↑(E.map (⟨⇑toReal, toReal_injective⟩ : (Fin d → ℤ) ↪ (Fin d → ℝ))) := by
  induction n with
  | zero =>
      intro d S E P hP0 hmass hE hES A hA0 hC v hAv hAstab hv
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
      intro d S E P hP0 hmass hE hES A hA0 hC v hAv hAstab hv
      classical
      -- Le vecteur de scission
      set w : Fin d → ℤ := 3 • v (Fin.last n) with hw
      -- Appartenances à A (chaînes de stabilité depuis 0)
      have hm0 : (0 : Fin d → ℤ) ∈ A := hA0
      have hmw : 3 • v (Fin.last n) ∈ A := by
        simpa using (hAstab 0 hA0 (Fin.last n)).1
      have hmnw : -(3 • v (Fin.last n)) ∈ A := by
        simpa using (hAstab 0 hA0 (Fin.last n)).2
      have hmn3 : ∀ i : Fin (n + 1), -(3 • v i) ∈ A := by
        intro i
        simpa using (hAstab 0 hA0 i).2
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
      set A' : Finset (Fin (d + 1) → ℤ) :=
        A.image (fun a => Fin.snoc a 0) with hA'
      -- Petites équations de snoc
      have hadd_snoc : ∀ x y : Fin d → ℤ,
          (Fin.snoc x 0 : Fin (d + 1) → ℤ) + Fin.snoc y 0
            = Fin.snoc (x + y) 0 := by
        intro x y
        funext j
        induction j using Fin.lastCases with
        | last => simp
        | cast i => simp
      have hsub_snoc : ∀ x y : Fin d → ℤ,
          (Fin.snoc x 0 : Fin (d + 1) → ℤ) - Fin.snoc y 0
            = Fin.snoc (x - y) 0 := by
        intro x y
        funext j
        induction j using Fin.lastCases with
        | last => simp
        | cast i => simp
      have hneg_snoc : ∀ x : Fin d → ℤ,
          -(Fin.snoc x 0 : Fin (d + 1) → ℤ) = Fin.snoc (-x) 0 := by
        intro x
        funext j
        induction j using Fin.lastCases with
        | last => simp
        | cast i => simp
      -- Les vecteurs embarqués se lisent comme des snoc à hauteur nulle
      have hv'snoc : ∀ i : Fin n,
          (liftUp (v i.castSucc, false) : Fin (d + 1) → ℤ)
            = Fin.snoc (v i.castSucc) 0 := fun _ => rfl
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
      have hA0' : 0 ∈ A' := Finset.mem_image.2 ⟨0, hA0, by
        funext j
        induction j using Fin.lastCases with
        | last => simp
        | cast i => simp⟩
      have hC' : SupportContained S' (pushUp (split w P)) A' :=
        supportContained_pushUp_split w hC
          (fun a ha => ⟨(hAstab a ha (Fin.last n)).1, (hAstab a ha (Fin.last n)).2⟩)
      have hAv' : ∀ i : Fin n,
          liftUp (v i.castSucc, false) ∈ A' ∧ -liftUp (v i.castSucc, false) ∈ A' := by
        intro i
        constructor
        · refine Finset.mem_image.2 ⟨v i.castSucc, (hAv i.castSucc).1, ?_⟩
          rw [hv'snoc i]
        · refine Finset.mem_image.2 ⟨-v i.castSucc, (hAv i.castSucc).2, ?_⟩
          rw [hv'snoc i, hneg_snoc]
      have hAstab' : ∀ a ∈ A', ∀ i : Fin n,
          a + 3 • liftUp (v i.castSucc, false) ∈ A'
            ∧ a - 3 • liftUp (v i.castSucc, false) ∈ A' := by
        intro a' ha' i
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 ha'
        rw [hA']
        have h1 : 3 • liftUp (v i.castSucc, false)
            = Fin.snoc (3 • v i.castSucc) 0 := by
          funext j
          induction j using Fin.lastCases with
          | last => simp [liftUp]
          | cast k => simp [liftUp, Pi.smul_apply, smul_eq_mul]
        constructor
        · refine Finset.mem_image.2 ⟨a + 3 • v i.castSucc,
            (hAstab a ha i.castSucc).1, ?_⟩
          rw [h1, hadd_snoc]
        · refine Finset.mem_image.2 ⟨a - 3 • v i.castSucc,
            (hAstab a ha i.castSucc).2, ?_⟩
          rw [h1, hsub_snoc]
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
        -- la contention à six décalages
        have hmn6 : -(3 • v i.castSucc) - 3 • v i.castSucc ∈ A :=
          (hAstab _ (hmn3 i.castSucc) i.castSucc).2
        have hwu : 3 • v (Fin.last n) - 3 • v i.castSucc ∈ A :=
          (hAstab _ hmw i.castSucc).2
        have hnwu : -(3 • v (Fin.last n)) - 3 • v i.castSucc ∈ A :=
          (hAstab _ hmnw i.castSucc).2
        have hid1 : (-(3 • v i.castSucc) - 3 • v i.castSucc : Fin d → ℤ)
            = -(6 • v i.castSucc) := by
          funext j
          simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
          ring
        have hid2 : 3 • v (Fin.last n) - 3 • v i.castSucc - 3 • v i.castSucc
            = w - 6 • v i.castSucc := by
          funext j
          simp only [Pi.sub_apply, Pi.smul_apply, hw]
          ring
        have hid3 : -(3 • v (Fin.last n)) - 3 • v i.castSucc - 3 • v i.castSucc
            = -w - 6 • v i.castSucc := by
          funext j
          simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply, hw]
          ring
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
            · rw [← hid1]
              exact hmn6
            · rw [← hid2]
              exact (hAstab _ hwu i.castSucc).2
            · rw [← hid3]
              exact (hAstab _ hnwu i.castSucc).2)
        rw [h6, hS', shiftDistance_pushUp]
        exact (shiftDistanceProd_split_le_of_support w (6 • v i.castSucc)
          hP0 hmass h6set).trans (hv i.castSucc)
      obtain ⟨ε', hε', hmem'⟩ := ih (d + 1) S' E' (pushUp (split w P))
        hP0' hmass' hsupp' hES' A' hA0' hC'
        (fun i => liftUp (v i.castSucc, false)) hAv' hAstab' hv'
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
            simp [hv'snoc]
        | cast k =>
            show coordMoment (pushUp (split w P)) S' k.castSucc
              + ∑ i : Fin n, (ε' i : ℝ)
                  * ((liftUp (v i.castSucc, false)) k.castSucc : ℝ)
              = (Fin.snoc z β : Fin (d + 1) → ℝ) k.castSucc
            rw [hS', coordMoment_pushUp_split_of_support w mono3 k, hz]
            simp [hv'snoc]
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
      have hP5 : SupportContained S P
          ({0, w, -w, -w - w, -(w + w)} : Finset (Fin d → ℤ)) :=
        hC.mono (by
          intro t ht
          simp only [Finset.mem_insert, Finset.mem_singleton] at ht ⊢
          rcases ht with rfl | rfl | rfl | rfl | rfl
          · exact hm0
          · exact hmw
          · exact hmnw
          · exact (hAstab _ hmnw (Fin.last n)).2
          · rw [hidww]
            exact (hAstab _ hmnw (Fin.last n)).2)
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

/-- **Lemme 1.4 (Karingula–Lovett) — énoncé public** : si chaque `v i`
d'un ensemble `A` contenant `0` et stable par `± 3 • v j` a une distance de
décalage `≤ 1/3` pour `6 • v i`, il existe une coloration `ε` telle que le
barycentre de `P` augmenté des sommes signées appartienne à l'enveloppe
convexe du support transporté de `P`.

La forme porte (`exists_colouring_aux`) conclut sur le support exact `E` ;
l'énoncé public le consomme avec `E := S.filter (P · ≠ 0)` et remonte à
l'enveloppe de `S` par monotonie — c'est la lecture lake de l'oracle
`gdahia/Komlos` (`SignedSums.lean` l.32-36), où le `Finsupp` porte son
support canonique. -/
theorem exists_isColouring_mean_add_sum_mem_convexHull (n d : ℕ)
    (S : Finset (Fin d → ℤ)) (P : (Fin d → ℤ) → ℝ) (hP0 : ∀ x, 0 ≤ P x)
    (hmass : ∑ x ∈ S, P x = 1) (hPsupp : ∀ x, P x ≠ 0 → x ∈ S)
    (A : Finset (Fin d → ℤ)) (hA0 : 0 ∈ A) (hC : SupportContained S P A)
    (v : Fin n → (Fin d → ℤ)) (hAv : ∀ i, v i ∈ A ∧ -v i ∈ A)
    (hAstab : ∀ a ∈ A, ∀ i, a + 3 • v i ∈ A ∧ a - 3 • v i ∈ A)
    (hv : ∀ i, shiftDistance S P (6 • v i) ≤ 3⁻¹) :
    ∃ ε : Fin n → ℤ, (∀ i, ε i = 1 ∨ ε i = -1) ∧
      (fun j => coordMoment P S j + ∑ i, (ε i : ℝ) * (v i j : ℝ)) ∈
        convexHull ℝ
          ↑(S.map (⟨⇑toReal, toReal_injective⟩ : (Fin d → ℤ) ↪ (Fin d → ℝ))) := by
  obtain ⟨ε, hε, hmem⟩ := exists_colouring_aux n d S (S.filter (fun x => P x ≠ 0)) P
    hP0 hmass (fun x hx => Finset.mem_filter.2 ⟨hPsupp x hx, hx⟩)
    (Finset.filter_subset _ _) A hA0 hC v hAv hAstab hv
  refine ⟨ε, hε, ?_⟩
  have hsub : (S.filter (fun x => P x ≠ 0)).map
      (⟨⇑toReal, toReal_injective⟩ : (Fin d → ℤ) ↪ (Fin d → ℝ))
    ⊆ S.map (⟨⇑toReal, toReal_injective⟩ : (Fin d → ℤ) ↪ (Fin d → ℝ)) :=
    Finset.map_subset_map.mpr (Finset.filter_subset _ _)
  exact convexHull_mono (Finset.coe_subset.2 hsub) hmem

end Discrepancy.Komlos
