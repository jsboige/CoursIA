/-
  WuMethod — companion Lean du notebook Geometry-03 (méthode de Wu)
  ================================================================

  Deuxième module du lac `geometry_lean` (EPIC #18601 volet B, tranche 4 :
  « Companions 03 (Wu) puis 01 »). Il double
  `Geometry-03-Wu-Method-Python.ipynb` en formalisant **ce que le test de Wu
  garantit** — la question pédagogique de la position 05 du programme gradué
  #17544 (« que garantit "prouvé par Gröbner" ? »).

  Ce que le notebook calcule avec sympy (pseudo-restes, chaînes ascendantes,
  initiales), ce module le prouve : pour chaque théorème, un **certificat
  polynomial explicite** — une identité de la forme
  `J • g = Σ aᵢ • hᵢ` — dont Lean vérifie la validité par `ring`. C'est
  exactement la substance du pseudo-reste nul : la conclusion `g` appartient
  à l'idéal des hypothèses `hᵢ` à un facteur de non-dégénérescence `J` près,
  donc s'annule partout où les hypothèses s'annulent et `J` ne s'annule pas.

  Deux familles d'énoncés, calquées sur les sections du notebook :

  * **T1, le fil rouge** (milieu de l'hypoténuse) : encodage polynomial en
    quatre variables, certificat d'appartenance idéale `g = u₁ • h₁` sans
    aucune condition de non-dégénérescence, et lue sémantique sur
    `MvPolynomial (Fin 4) ℚ` — l'appartenance à l'idéal implique
    l'annulation universelle. S'y ajoute le **témoin négatif** (§9 du
    notebook) : la conclusion fausse « MA² = 4·MB² » est réfutée par un
    contre-exemple explicite — un outil de preuve doit aussi savoir dire non.

  * **T3, le théorème de Ceva** (§8 du notebook) : encodage barycentrique
    exact du notebook — `A = (0,0)`, `B = (1,0)`, `C = (p,q)`, points de côté
    paramétrés par `t₁ t₂ t₃`, point de concours `O = (o₁,o₂)`, hypothèses
    d'alignement par déterminants 2×2. L'identité maîtresse ci-dessous joue
    le rôle du pseudo-reste nul ; la direction « concurrence ⇒ produit des
    rapports dirigés » n'exige que `q ≠ 0` (triangle non plat), la réciproque
    construit explicitement le point de concours par Cramer. Le **piège des
    rapports dirigés** du notebook (inverser `CE/EA`) est lui aussi réfuté
    par un contre-exemple numérique exact.

  Non-but assumé (non-buts de l'EPIC) : ce module ne migre pas les
  algorithmes de Wu ou de Ritt en Lean exécutable — il formalise les
  théorèmes qu'ils établissent. Le demi-tour « preuve géométrique abstraite »
  du fil rouge vit dans `Geometry.MidpointHypotenuse`.
-/

import Mathlib

open MvPolynomial

/-! ## T1 — le fil rouge : milieu de l'hypoténuse (notebook §2)

Encodage du notebook, cellule « Encodage de T1 » : `A = (0,0)`, `B = (u₁,0)`,
`C = (0,u₂)` — l'angle droit en `A` porte les côtés sur les axes — et
`M = (xₘ,yₘ)` le milieu de l'hypoténuse `[BC]`. Les hypothèses disent que
`M` est le milieu : `h₁ : 2xₘ − u₁ = 0` (abscisse) et `h₂ : 2yₘ − u₂ = 0`
(ordonnée). Les variables sont indicées `X 0 = u₁`, `X 1 = u₂`, `X 2 = xₘ`,
`X 3 = yₘ`. -/

/-- Hypothèse `h₁ : 2·xₘ − u₁` — l'abscisse du milieu de `[BC]` vaut
`u₁/2` (notebook Geometry-03, cellule 4). -/
noncomputable def t1H1 : MvPolynomial (Fin 4) ℚ := 2 * X 2 - X 0

/-- Hypothèse `h₂ : 2·yₘ − u₂` — l'ordonnée du milieu de `[BC]` vaut
`u₂/2`. -/
noncomputable def t1H2 : MvPolynomial (Fin 4) ℚ := 2 * X 3 - X 1

/-- Conclusion `g_{MB} : MA² − MB²` — le milieu est à égale distance de `A`
et de `B`. -/
noncomputable def t1GMB : MvPolynomial (Fin 4) ℚ :=
  (X 2)^2 + (X 3)^2 - ((X 2 - X 0)^2 + (X 3)^2)

/-- Conclusion `g_{MC} : MA² − MC²` — le milieu est à égale distance de `A`
et de `C` (composante symétrique, échangée par `u₁ ↔ u₂`, `xₘ ↔ yₘ`). -/
noncomputable def t1GMC : MvPolynomial (Fin 4) ℚ :=
  (X 2)^2 + (X 3)^2 - ((X 2)^2 + (X 3 - X 1)^2)

/-- **Certificat T1 côté `B`.** La conclusion `g_{MB}` est égale au produit
`u₁ • h₁` : elle appartient à l'idéal engendré par la seule hypothèse
d'abscisse — c'est le contenu du pseudo-reste nul du notebook pour T1, sans
aucune condition de non-dégénérescence. La composante ordonnée `h₂` n'intervient
pas : `MB` ne mobilise que l'abscisse de `B`. -/
theorem t1_certificate_mb (z : Fin 4 → ℚ) :
    eval z t1GMB = z 0 * eval z t1H1 := by
  simp [t1GMB, t1H1, eval_sub, eval_mul, eval_pow, eval_X] <;> ring

/-- **Certificat T1 côté `C`.** Symétrique du précédent : `g_{MC} = u₂ • h₂`.
Avec le certificat côté `B`, l'équidistance complète
`MA = MB = MC` du `Geometry.MidpointHypotenuse` abstrait se lit ici en
coordonnées, une hypothèse par composante. -/
theorem t1_certificate_mc (z : Fin 4 → ℚ) :
    eval z t1GMC = z 1 * eval z t1H2 := by
  simp [t1GMC, t1H2, eval_sub, eval_mul, eval_pow, eval_X] <;> ring

/-- **La garantie sémantique du test de Wu (T1).** Partout où l'hypothèse
d'abscisse s'annule, la conclusion `MA² = MB²` s'annule : l'appartenance à
l'idéal implique l'annulation universelle. C'est la réponse formelle à
« que garantit "prouvé" ? » pour le fil rouge. -/
theorem t1_soundness_mb (z : Fin 4 → ℚ) (h1 : eval z t1H1 = 0) :
    eval z t1GMB = 0 := by
  rw [t1_certificate_mb, h1, mul_zero]

/-- Garantie sémantique, composante `C`. -/
theorem t1_soundness_mc (z : Fin 4 → ℚ) (h2 : eval z t1H2 = 0) :
    eval z t1GMC = 0 := by
  rw [t1_certificate_mc, h2, mul_zero]

/-- Équidistance complète en coordonnées : si `M` est le milieu (les deux
hypothèses), alors `MA² = MB²` et `MA² = MC²`. -/
theorem t1_equidistant (z : Fin 4 → ℚ) (h1 : eval z t1H1 = 0)
    (h2 : eval z t1H2 = 0) :
    eval z t1GMB = 0 ∧ eval z t1GMC = 0 :=
  ⟨t1_soundness_mb z h1, t1_soundness_mc z h2⟩

/-- Conclusion **fausse** du témoin négatif (§9 du notebook) :
`MA² − 4·MB²`, vraie seulement pour des triangles très particuliers. -/
noncomputable def t1GFaux : MvPolynomial (Fin 4) ℚ :=
  (X 2)^2 + (X 3)^2 - 4 * ((X 2 - X 0)^2 + (X 3)^2)

/-- **Témoin négatif : l'outil de preuve sait dire non.** L'énoncé faux
« MA² = 4·MB² sous les hypothèses du milieu » n'est PAS prouvable : au point
concret du notebook `u₁ = 4`, `u₂ = 3`, `M = (2, 3/2)` (triangle rectangle
3-4-5), les deux hypothèses s'annulent mais la conclusion fausse vaut
`−75/4 ≠ 0`. Là où le test de Wu rend un reste non nul, Lean exhibe le
contre-exemple — la dissymétrie saine entre outil de recherche et outil de
preuve. -/
theorem t1_false_conclusion_unprovable :
    ¬ (∀ z : Fin 4 → ℚ, eval z t1H1 = 0 → eval z t1H2 = 0 →
        eval z t1GFaux = 0) := by
  intro h
  have hw := h ![4, 3, 2, (3 / 2 : ℚ)]
    (by simp [t1H1, eval_sub, eval_mul, eval_X] <;> norm_num)
    (by simp [t1H2, eval_sub, eval_mul, eval_X] <;> norm_num)
  simp [t1GFaux, eval_sub, eval_add, eval_mul, eval_pow, eval_X] at hw
  norm_num at hw

/-! ## T3 — le théorème de Ceva (notebook §8)

Encodage barycentrique exact du notebook : `A = (0,0)`, `B = (1,0)`,
`C = (p,q)` ; les points de côté `D ∈ (BC)`, `E ∈ (CA)`, `F ∈ (AB)` par leurs
paramètres `t₁ t₂ t₃` — `D = B + t₁(C−B)`, `E = A + t₂(C−A)`, `F = A + t₃(B−A)`
— et `O = (o₁,o₂)` le point de concours. Les trois hypothèses d'alignement
sont des déterminants 2×2 nuls. La conclusion (rapports **dirigés**) :
`t₁(1−t₂)t₃ − (1−t₁)t₂(1−t₃) = 0`. -/

/-- **Identité maîtresse de T3** — le pseudo-reste nul du notebook, rendu
explicite : `q² • g₃ = D • h_{CF} − q(t₂t₃−1) • h_{AD} + q(t₁t₃−t₁+1) • h_{BE}`
avec `D = (t₁t₂−t₁−t₂)·(−q)` le déterminant 2×2 des céviennes `(AD)` et
`(BE)`. Chaque coefficient est polynomial ; Lean vérifie l'identité par
`ring`. C'est elle qui joue, côté preuve vérifiée, le rôle du calcul
`prem(g₃, CS(T3)) = 0` du notebook. -/
theorem ceva_master_identity (p q t1 t2 t3 o1 o2 : ℚ) :
    q * q * (t1 * (1 - t2) * t3 - (1 - t1) * t2 * (1 - t3))
      = (t1 * t2 - t1 - t2) * (-q) * ((o1 - p) * (-q) - (o2 - q) * (t3 - p))
        - q * (t2 * t3 - 1) * (o1 * (t1 * q) - o2 * ((1 - t1) + t1 * p))
        + q * (t1 * t3 - t1 + 1) * ((o1 - 1) * (t2 * q) - o2 * (t2 * p - 1)) := by
  ring

/-- **Ceva, direction « concurrence ⇒ produit ».** Si les trois cévianes
`(AD)`, `(BE)`, `(CF)` sont concourantes en `O` et si le triangle n'est pas
plat (`q ≠ 0`), alors le produit des rapports dirigés vaut 1. Remarque de
structure : le certificat porte `D • h_{CF}` — l'hypothèse d'alignement déjà
nulle annule le terme en `D`, donc **cette direction n'exige que `q ≠ 0`**,
pas la non-parallélisme des céviannes ; les initiales plus riches du
notebook servent à sa chaîne algorithmique et à la réciproque. -/
theorem ceva_product_of_concurrent {p q t1 t2 t3 o1 o2 : ℚ} (hq : q ≠ 0)
    (hAD : o1 * (t1 * q) - o2 * ((1 - t1) + t1 * p) = 0)
    (hBE : (o1 - 1) * (t2 * q) - o2 * (t2 * p - 1) = 0)
    (hCF : (o1 - p) * (-q) - (o2 - q) * (t3 - p) = 0) :
    t1 * (1 - t2) * t3 - (1 - t1) * t2 * (1 - t3) = 0 := by
  have key := ceva_master_identity p q t1 t2 t3 o1 o2
  rw [hCF, hAD, hBE] at key
  simp only [mul_zero, add_zero, sub_zero] at key
  exact (mul_eq_zero.mp key).resolve_left (mul_ne_zero hq hq)

/-- **Ceva, direction « produit ⇒ concurrence ».** Si le produit des rapports
dirigés vaut 1, le triangle n'est pas plat (`q ≠ 0`) et les céviannes `(AD)`
et `(BE)` sont sécantes (`t₁t₂ − t₁ − t₂ ≠ 0`, leur déterminant), alors les
trois céviannes sont concourantes : le point de concours est construit
explicitement par Cramer — c'est l'intersection de `(AD)` et `(BE)`, et
l'identité maîtresse garantit qu'il est sur `(CF)`. Les conditions
`q ≠ 0` et `t₁t₂ − t₁ − t₂ ≠ 0` sont les initiales du notebook (§6) :
triangle non plat, céviannes bien définies et sécantes. -/
theorem ceva_concurrent_of_product {p q t1 t2 t3 : ℚ} (hq : q ≠ 0)
    (hden : t1 * t2 - t1 - t2 ≠ 0)
    (hg : t1 * (1 - t2) * t3 - (1 - t1) * t2 * (1 - t3) = 0) :
    ∃ o1 o2 : ℚ,
      o1 * (t1 * q) - o2 * ((1 - t1) + t1 * p) = 0 ∧
      (o1 - 1) * (t2 * q) - o2 * (t2 * p - 1) = 0 ∧
      (o1 - p) * (-q) - (o2 - q) * (t3 - p) = 0 := by
  set O1 : ℚ :=
    -(((1 - t1) + t1 * p) * (t2 * q)) / (q * (t1 * t2 - t1 - t2)) with hO1
  set O2 : ℚ :=
    -((t1 * q) * (t2 * q)) / (q * (t1 * t2 - t1 - t2)) with hO2
  have hdn : (q * (t1 * t2 - t1 - t2) : ℚ) ≠ 0 := mul_ne_zero hq hden
  have h1 : O1 * (t1 * q) - O2 * ((1 - t1) + t1 * p) = 0 := by
    rw [hO1, hO2]
    set d : ℚ := q * (t1 * t2 - t1 - t2) with hd_def
    have hd_ne : d ≠ 0 := mul_ne_zero hq hden
    field_simp [hd_ne]
    ring
  have h2 : (O1 - 1) * (t2 * q) - O2 * (t2 * p - 1) = 0 := by
    rw [hO1, hO2]
    set d : ℚ := q * (t1 * t2 - t1 - t2) with hd_def
    have hd_ne : d ≠ 0 := mul_ne_zero hq hden
    field_simp [hd_ne]
    ring
  have key := ceva_master_identity p q t1 t2 t3 O1 O2
  rw [h1, h2] at key
  simp only [hg, mul_zero, add_zero, sub_zero] at key
  refine ⟨O1, O2, h1, h2, ?_⟩
  exact (mul_eq_zero.mp key.symm).resolve_left
    (mul_ne_zero hden (neg_ne_zero.mpr hq))

/-- **Le piège des rapports dirigés, réfuté formellement** (§8 du notebook).
L'encodage naïf qui inverserait le rapport `CE/EA` conclurait à
`t₁t₂(1−t₃) − (1−t₁)(1−t₂)t₃ = 0`. Sur le triangle concret du notebook
(`p = 2`, `q = 3`, `t₁ = 3/10`, `t₂ = 2/5`, `t₃ = 14/23` dérivé de la vraie
relation de Ceva), le point `O = (26/29, 18/29)` réalise exactement les trois
alignements — et la conclusion inversée vaut `−24/115 ≠ 0`. Un énoncé faux
ne devient pas théorème : la vérification numérique du notebook a son
contrepartie exacte en Lean. -/
theorem ceva_directed_ratio_trap_witness :
    (26:ℚ) / 29 * ((3 / 10) * 3) - (18 / 29) * ((1 - 3 / 10) + (3 / 10) * 2) = 0 ∧
    ((26:ℚ) / 29 - 1) * ((2 / 5) * 3) - (18 / 29) * ((2 / 5) * 2 - 1) = 0 ∧
    ((26:ℚ) / 29 - 2) * (-(3:ℚ)) - (18 / 29 - 3) * (14 / 23 - 2) = 0 ∧
    ((3:ℚ) / 10) * (2 / 5) * (1 - 14 / 23) - (1 - 3 / 10) * (1 - 2 / 5) * (14 / 23) ≠ 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · norm_num
  · intro hcon
    norm_num at hcon
