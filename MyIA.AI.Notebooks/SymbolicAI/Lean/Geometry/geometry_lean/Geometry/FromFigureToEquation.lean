/-
  FromFigureToEquation — companion Lean du notebook Geometry-01
  ==============================================================

  Troisième module du lac `geometry_lean` (EPIC #18601 volet B, tranche 4 :
  « Companions 03 (Wu) puis 01 (figure vers équation) »). Il double
  `Geometry-01-From-Figure-To-Equation.ipynb` en formalisant l'étape que le
  notebook exécute numériquement : **la traduction d'une figure en équations
  polynomiales, et ce que le test numérique peut et ne peut pas prouver**.

  Le notebook mesure ; ce module démontre :

  * l'encodage (§2) — orthogonalité en `A` et milieu de `[BC]` substitué,
    sur `MvPolynomial (Fin 6) ℚ` — et son premier fait surprenant : la
    composante `MB² − MC²` est **identiquement nulle** (symétrie du milieu,
    sans aucune hypothèse), seule `MA² − MB²` porte l'information ;
  * la famille paramétrique des triangles rectangles (§3, §6 étape 1) —
    `A = (0,0)`, `B = (u₁,u₂)`, `C = (−k·u₂, k·u₁)` (rotation) : `H` et
    `C₁` s'y annulent **identiquement** — l'écho formel exact du protocole
    de tirage correct du notebook ;
  * le témoin négatif (§4) avec son **identité exacte**
    `C′ + AC² − H = 0` : sous l'hypothèse `H = 0` et `AC ≠ 0`, l'énoncé
    piège « M′A² = M′C² » est réfuté — l'outil sait dire non ;
  * le tirage biaisé (§5) : le polynôme du cercle s'annule aux points de
    Pythagore et pas ailleurs — témoins numériques exacts ;
  * le moteur de Schwartz–Zippel (§6) sur le polynôme témoin
    `P(u,v) = u·v + u²` : caractérisation exacte de son lieu de zéros, compte
    exact `4s+1` sur la grille `[−s,s]²`, et la borne `d/|S|` vérifiée —
    la mesure du notebook devient une inégalité prouvée.

  Non-but assumé (non-buts de l'EPIC) : la borne de Schwartz–Zippel générale
  (probabiliste) n'est pas démontrée ici — le module en formalise l'instance
  mesurée par le notebook. L'appartenance idéale (le test de Wu) vit dans
  `Geometry.WuMethod` ; la preuve géométrique abstraite du fil rouge dans
  `Geometry.MidpointHypotenuse`.
-/

import Mathlib

open MvPolynomial Finset

/-! ## L'encodage (notebook §2)

Six coordonnées `X 0 = x_A`, `X 1 = y_A`, `X 2 = x_B`, `X 3 = y_B`,
`X 4 = x_C`, `X 5 = y_C`. L'hypothèse `H` : orthogonalité en `A` (produit
scalaire nul). Le milieu `M` de `[BC]` est **substitué** (cellule 8 du
notebook) : `x_M = (x_B + x_C)/2`, `y_M = (y_B + y_C)/2`. Les conclusions
sont `C₁ = MA² − MB²` et `C₂ = MB² − MC²`. -/

/-- Hypothèse `H` : orthogonalité en `A` — produit scalaire `(B−A)·(C−A)`
nul (notebook Geometry-01, cellule 8). -/
noncomputable def H : MvPolynomial (Fin 6) ℚ :=
  (X 2 - X 0) * (X 4 - X 0) + (X 3 - X 1) * (X 5 - X 1)

/-- Conclusion `C₁ = MA² − MB²` avec `M` milieu substitué de `[BC]`
(le `(1/2)` du milieu vit dans le coefficient constant `C (1/2)`). -/
noncomputable def C1 : MvPolynomial (Fin 6) ℚ :=
  (C (1/2 : ℚ) * (X 2 + X 4) - X 0)^2 + (C (1/2 : ℚ) * (X 3 + X 5) - X 1)^2
    - ((C (1/2 : ℚ) * (X 2 + X 4) - X 2)^2
        + (C (1/2 : ℚ) * (X 3 + X 5) - X 3)^2)

/-- Conclusion `C₂ = MB² − MC²` avec `M` milieu substitué de `[BC]`. -/
noncomputable def C2 : MvPolynomial (Fin 6) ℚ :=
  (C (1/2 : ℚ) * (X 2 + X 4) - X 2)^2 + (C (1/2 : ℚ) * (X 3 + X 5) - X 3)^2
    - ((C (1/2 : ℚ) * (X 2 + X 4) - X 4)^2
        + (C (1/2 : ℚ) * (X 3 + X 5) - X 5)^2)

/-- **Première surprise du notebook (§2, cellule 8)** : `C₂` est
identiquement nul — la symétrie `B ↔ C` du milieu rend `MB² = MC²` **sans
aucune hypothèse**, ni orthogonalité ni même non-dégénérescence. Seule `C₁`
porte une information géométrique. -/
theorem C2_identically_zero (z : Fin 6 → ℚ) : eval z C2 = 0 := by
  simp [C2, eval_sub, eval_add, eval_mul, eval_pow, eval_X, eval_C]; ring

/-- La forme développée de `C₁` à coefficients entiers (le `(1/2)` du milieu
disparaît au développement) — la version affichée par `sp.expand` à la
cellule 8 du notebook. -/
theorem C1_expanded (z : Fin 6 → ℚ) :
    eval z C1 = (z 0)^2 - z 0 * z 2 - z 0 * z 4 + z 2 * z 4
      + (z 1)^2 - z 1 * z 3 - z 1 * z 5 + z 3 * z 5 := by
  simp [C1, eval_sub, eval_add, eval_mul, eval_pow, eval_X, eval_C]; ring

/-! ## La famille paramétrique des triangles rectangles (§3, §6 étape 1)

Le protocole correct du notebook (cellule 22) : au lieu de tirer six
coordonnées puis filtrer `H = 0` (taux de rencontre `~10⁻⁵`, étape 0), on
**construit** la famille — `A = (0,0)`, `B = (u₁,u₂)`, `C = (−k·u₂, k·u₁)`,
la rotation d'un quart de tour de `B` mise à l'échelle — et l'on teste la
conclusion dessus. Ce module prouve que le test ne peut qu'y réussir :
`H` et `C₁` s'y annulent identiquement. -/

/-- Le point de la famille paramétrique : `A = (0,0)`, `B = (u₁,u₂)`,
`C = (−k·u₂, k·u₁)` — la substitution exacte de la cellule 22. -/
def fam (u1 u2 k : ℚ) : Fin 6 → ℚ :=
  ![0, 0, u1, u2, -k * u2, k * u1]

/-- L'hypothèse `H` s'annule sur toute la famille — par construction de la
rotation, pour toute valeur des paramètres. -/
theorem H_zero_on_family (u1 u2 k : ℚ) : eval (fam u1 u2 k) H = 0 := by
  simp [H, fam, eval_add, eval_mul, eval_sub, eval_X]; ring

/-- **Le cœur du protocole numérique (§6 étape 1)** : la conclusion `C₁`
s'annule identiquement sur la famille des triangles rectangles. La
substitution `sp.expand(C1.subs(...)) = 0` du notebook devient une identité
prouvée : aucun tirage ne peut la contredire. -/
theorem C1_zero_on_family (u1 u2 k : ℚ) : eval (fam u1 u2 k) C1 = 0 := by
  simp [C1, fam, eval_sub, eval_add, eval_mul, eval_pow, eval_X, eval_C]; ring

/-! ## Le témoin négatif (§4) : la machinerie sait dire non

Le notebook échange le milieu de `[BC]` contre celui `M′` de `[AB]` et
constate que l'énoncé piège est réfuté par toute figure non dégénérée
(cellule 14 : « figures qui le REFUTENT : 10 000 / 10 000 »). La clé est
une **identité exacte** : `C′ + AC² − H = 0`. -/

/-- Conclusion piège `C′ = M′A² − M′C²` avec `M′` milieu de `[AB]`
(cellule 14). -/
noncomputable def Cp : MvPolynomial (Fin 6) ℚ :=
  (C (1/2 : ℚ) * (X 0 + X 2) - X 0)^2 + (C (1/2 : ℚ) * (X 1 + X 3) - X 1)^2
    - ((C (1/2 : ℚ) * (X 0 + X 2) - X 4)^2
        + (C (1/2 : ℚ) * (X 1 + X 3) - X 5)^2)

/-- Le carré `AC²` — la non-dégénérescence du côté `[AC]`. -/
noncomputable def AC2 : MvPolynomial (Fin 6) ℚ :=
  (X 4 - X 0)^2 + (X 5 - X 1)^2

/-- **L'identité exacte du piège (§4, cellule 14)** :
`C′ + AC² − H = 0` — donc `C′ = H − AC²`. L'énoncé « M′A² = M′C² » n'est
vrai que là où `H = AC²`, et sous l'hypothèse `H = 0` il exige `AC² = 0`. -/
theorem Cp_plus_AC2_minus_H (z : Fin 6 → ℚ) :
    eval z Cp + eval z AC2 - eval z H = 0 := by
  simp [Cp, AC2, H, eval_sub, eval_add, eval_mul, eval_pow, eval_X, eval_C]; ring

/-- **Le témoin négatif réfuté (§4)** : sous l'hypothèse d'orthogonalité
`H = 0` et de non-dégénérescence `AC ≠ 0`, l'énoncé piège est FAUX. -/
theorem trap_refuted (z : Fin 6 → ℚ) (hH : eval z H = 0)
    (hAC : eval z AC2 ≠ 0) : eval z Cp ≠ 0 := by
  intro hcp
  have h := Cp_plus_AC2_minus_H z
  rw [hcp, hH] at h
  simp at h
  exact hAC h

/-! ## Le tirage biaisé (§5) : le même polynôme, deux réponses

Cellule 17 : `q(x,y) = x² + y² − 25` testé **sur** le cercle de rayon 5
(points pythagoriciens) semble identiquement nul ; testé ailleurs, il ne
l'est pas. La validité d'un test numérique dépend entièrement du mode de
tirage. -/

/-- `q` s'annule au point pythagoricien `(3,4)` du cercle de rayon 5. -/
theorem q_zero_on_circle : (3 : ℚ)^2 + (4 : ℚ)^2 - 25 = 0 := by norm_num

/-- Le **même** `q`, évalué hors du cercle, n'est plus nul : le tirage
biaisé faisait croire à `q ≡ 0`. -/
theorem q_nonzero_elsewhere : (1 : ℚ)^2 + (1 : ℚ)^2 - 25 ≠ 0 := by norm_num

/-! ## Le moteur de Schwartz–Zippel (§6) : de la mesure à la borne

Cellule 20 : le polynôme témoin `P(u,v) = u·v + u²` (non nul, degré total
`d = 2`) a un taux d'annulation mesuré sur la grille `[−s,s]²` qui reste
sous la borne `d/|S| = 2/(2s+1)`. Ce module remplace la mesure par un
**compte exact** : le lieu des zéros est l'union de la droite `u = 0` et de
l'antidiagonale `v = −u`, donc exactement `4s+1` points sur la grille, et
`(4s+1)/(2s+1)² ≤ 2/(2s+1)` — l'inégalité de Schwartz–Zippel pour cette
instance, prouvée et non plus mesurée. -/

/-- **Caractérisation exacte du lieu de zéros** du polynôme témoin :
`u·v + u² = 0` si et seulement si `u = 0` ou `v = −u` (l'anneau `ℤ` est
intègre : `u·(v+u) = 0`). -/
theorem zeros_char (u v : ℤ) : u * v + u ^ 2 = 0 ↔ u = 0 ∨ v = -u := by
  constructor
  · intro h
    have h' : u * (v + u) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h' with rfl | h2
    · exact Or.inl rfl
    · exact Or.inr (by linarith)
  · rintro (rfl | rfl) <;> ring

/-- Le compte exact des zéros sur la grille `[−s,s]²` (avec
`S = Finset.Icc (−s) s` sur `ℤ`) : la droite `u = 0` et l'antidiagonale
`v = −u`, d'intersection le seul point origine, totalisent
`2·(2s+1) − 1 = 4s+1` points. C'est la version prouvée du tableau de la
cellule 20 — 9, 21, 41 puis 201 points mesurés pour `s = 2, 5, 10, 50`. -/
theorem zeros_grid_count (s : ℕ) :
    (((Finset.Icc (-(s : ℤ)) s) ×ˢ (Finset.Icc (-(s : ℤ)) s)).filter
        (fun p : ℤ × ℤ => p.1 * p.2 + p.1 ^ 2 = 0)).card = 4 * s + 1 := by
  have hcard : #(Finset.Icc (-(s : ℤ)) s) = 2 * s + 1 := by
    rw [Int.card_Icc]
    norm_num
    omega
  have hzero : (0 : ℤ) ∈ Finset.Icc (-(s : ℤ)) s := by
    simp only [Finset.mem_Icc]
    omega
  have hneg : ∀ u ∈ Finset.Icc (-(s : ℤ)) s,
      -u ∈ Finset.Icc (-(s : ℤ)) s := by
    intro u hu
    simp only [Finset.mem_Icc] at hu ⊢
    omega
  have hinj : Function.Injective (fun u : ℤ => (u, -u)) := fun a b hab =>
    congrArg Prod.fst hab
  have hcount : ((({0} ×ˢ Finset.Icc (-(s : ℤ)) s) ∪
      (Finset.Icc (-(s : ℤ)) s).image (fun u : ℤ => (u, -u)))).card
      = 4 * s + 1 := by
    let A : Finset (ℤ × ℤ) := {0} ×ˢ Finset.Icc (-(s : ℤ)) s
    let B : Finset (ℤ × ℤ) := (Finset.Icc (-(s : ℤ)) s).image (fun u : ℤ => (u, -u))
    change (A ∪ B).card = 4 * s + 1
    have hA : #A = 2 * s + 1 := by
      change #({0} ×ˢ Finset.Icc (-(s : ℤ)) s) = 2 * s + 1
      rw [Finset.card_product, Finset.card_singleton, hcard, one_mul]
    have hB : #B = 2 * s + 1 := by
      change #((Finset.Icc (-(s : ℤ)) s).image (fun u : ℤ => (u, -u)))
        = 2 * s + 1
      rw [Finset.card_image_of_injective _ hinj, hcard]
    have hAB : A ∩ B = {(0, 0)} := by
      change ({0} ×ˢ Finset.Icc (-(s : ℤ)) s) ∩
          (Finset.Icc (-(s : ℤ)) s).image (fun u : ℤ => (u, -u)) = {(0, 0)}
      ext p
      simp only [Finset.mem_inter, Finset.mem_product, Finset.mem_image,
        Finset.mem_singleton]
      constructor
      · rintro ⟨⟨hp1, -⟩, ⟨u, hu, hp⟩⟩
        have hfst : u = p.1 := congrArg Prod.fst hp
        have hsnd : -u = p.2 := congrArg Prod.snd hp
        have hu0 : u = 0 := by rw [hfst, hp1]
        have hp2 : p.2 = 0 := by
          rw [← hsnd, hu0]
          norm_num
        have hp00 : p = (0, 0) := by
          rw [Prod.ext_iff]
          exact ⟨hp1, hp2⟩
        exact hp00
      · intro hp
        rw [hp]
        exact ⟨⟨rfl, hzero⟩, 0, hzero, by simp⟩
    have hABc : #(A ∩ B) = 1 := by rw [hAB, Finset.card_singleton]
    have h := Finset.card_union_add_card_inter A B
    rw [hABc, hA, hB] at h
    omega
  have hset : ((Finset.Icc (-(s : ℤ)) s) ×ˢ (Finset.Icc (-(s : ℤ)) s)).filter
      (fun p : ℤ × ℤ => p.1 * p.2 + p.1 ^ 2 = 0)
      = (({0} ×ˢ Finset.Icc (-(s : ℤ)) s) ∪
          (Finset.Icc (-(s : ℤ)) s).image (fun u : ℤ => (u, -u))) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_union,
      Finset.mem_image, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨h1, h2⟩, hz⟩
      rcases (zeros_char p.1 p.2).mp hz with hp1 | hp2
      · exact Or.inl ⟨hp1, h2⟩
      · exact Or.inr ⟨p.1, h1, by
          rw [Prod.ext_iff]
          exact ⟨rfl, hp2.symm⟩⟩
    · rintro (⟨hp1, h2⟩ | ⟨u, hu, rfl⟩)
      · exact ⟨⟨by rw [hp1]; exact hzero, h2⟩, by rw [hp1]; norm_num⟩
      · exact ⟨⟨hu, hneg u hu⟩, by ring⟩
  rw [hset]
  exact hcount

/-- **La borne de Schwartz–Zippel pour l'instance (§6)** : le taux exact de
zéros `(4s+1)/(2s+1)²` du polynôme témoin de degré `d = 2` reste sous la
borne `d/|S| = 2/(2s+1)`. L'inégalité que le notebook mesurait à chaque
taille de grille est prouvée une fois pour toutes. -/
theorem sz_bound_instance (s : ℕ) :
    ((4 * s + 1 : ℚ) / ((2 * s + 1 : ℚ))^2) ≤ 2 / ((2 * s + 1 : ℚ)) := by
  have hpos : (0 : ℚ) < 2 * s + 1 := by positivity
  have hne : (2 * s + 1 : ℚ) ≠ 0 := ne_of_gt hpos
  have hne2 : ((2 * s + 1 : ℚ))^2 ≠ 0 := pow_ne_zero 2 hne
  have hkey : 2 / (2 * s + 1 : ℚ) - (4 * s + 1 : ℚ) / ((2 * s + 1 : ℚ))^2
      = 1 / ((2 * s + 1 : ℚ))^2 := by
    field_simp [hne, hne2]
    ring
  have hnn : (0 : ℚ) ≤ 2 / (2 * s + 1 : ℚ)
      - (4 * s + 1 : ℚ) / ((2 * s + 1 : ℚ))^2 := by
    rw [hkey]
    positivity
  linarith
