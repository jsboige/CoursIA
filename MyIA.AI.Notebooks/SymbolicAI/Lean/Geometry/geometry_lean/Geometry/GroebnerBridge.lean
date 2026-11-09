/-
  GroebnerBridge — companion Lean du notebook Geometry-02 (pont Gröbner)
  ====================================================================

  Troisième module du lac `geometry_lean` (EPIC #18601 volet B, position 05 du
  programme gradué #17544). Il double
  `Geometry-02-From-Equation-To-Proof.ipynb` en formalisant **ce que « prouvé
  par Gröbner » garantit** : une conclusion `g` dont la réduction modulo les
  hypothèses `hᵢ` donne un reste nul est un élément de l'idéal engendré par
  les `hᵢ` — elle s'annule donc partout où les hypothèses s'annulent. Le
  notebook le décide par le calcul sympy (`groebner`, `reduce`, quotients et
  restes) ; ce module le **certifie** : chaque appartenance est portée par un
  certificat polynomial explicite que Lean vérifie par `ring`, et chaque
  « reste non nul » du notebook devient un contre-exemple concret — l'outil de
  preuve sait aussi dire non.

  Trois familles d'énoncés, calquées sur les sections du notebook :

  * **Le fil rouge en six variables** (§1-§4) : angle droit en `A` et milieu
    `M` de `[BC]` quelconques. La conclusion `MA² − MB²` est **égale** à
    l'hypothèse d'orthogonalité `H` (quotient 1, reste 0 — la cellule
    « réduire C1 par H » du notebook) : l'équidistance `MA = MB = MC` du
    `Geometry.MidpointHypotenuse` abstrait se lit ici comme trois éléments de
    l'idéal `⟨H⟩`, dont deux égaux à `H` lui-même et un identiquement nul.
    L'isocélité `AB = AC`, elle, n'est **pas** dans l'idéal : le triangle
    rectangle 3-4-5 du notebook la réfute (§5).

  * **Le théorème faux et le vrai besoin** (§6) : `AB ⊥ AC`, `AB ⊥ AD`
    « donc » `A, C, D` alignés. L'encodage polynomial dit non : le reste de la
    conclusion n'est pas nul, et le point `B = A` du notebook (hypothèses
    nulles, conclusion valant 1) prouve que **l'énoncé est faux** — pas
    seulement hors de portée de l'outil.

  * **L'astuce de Ritt / Rabinowitsch** (§7) : en saturant l'idéal par la
    condition de non-dégénérescence `B ≠ A`, le reste devient nul. Les deux
    faces du geste sont formalisées : l'identité maîtresse
    `g • concl = u • h_a + v • h_b` (appartenance à l'idéal **saturé**,
    exposant 1) et l'encodage Rabinowitsch en sept variables, où l'inverse
    virtuel `z` adjoint `z • g − 1` aux hypothèses et fait revenir la
    conclusion dans l'idéal augmenté.

  Non-but assumé : ce module ne calcule pas de base de Gröbner — Mathlib n'en
  fournit pas d'algorithme exécutable — il certifie les appartenances que le
  notebook décide. Le coût expérimental de la certitude (§8 du notebook) est
  une mesure d'implémentation, hors du périmètre formel.
-/

import Mathlib

open MvPolynomial

/-! ## Le fil rouge en six variables (notebook §1-§4)

Encodage du notebook, cellule « Encodage » : `A`, `B`, `C` libres,
`X 0 = x_A`, `X 1 = y_A`, `X 2 = x_B`, `X 3 = y_B`, `X 4 = x_C`, `X 5 = y_C`.
Hypothèse `H` : l'angle en `A` est droit (produit scalaire nul des vecteurs
`AB` et `AC`). Conclusion `C1 = MA² − MB²` où `M` est le milieu de `[BC]` ;
`C'` la conclusion symétrique `MA² − MC²` ; `C3 = MB² − MC²` ; `C_iso =
AB² − AC²`. -/

/-- Hypothèse `H` : `(x_B − x_A)(x_C − x_A) + (y_B − y_A)(y_C − y_A)` —
l'angle en `A` est droit (notebook Geometry-02, §1). -/
noncomputable def FilH : MvPolynomial (Fin 6) ℚ :=
  (X 2 - X 0) * (X 4 - X 0) + (X 3 - X 1) * (X 5 - X 1)

/-- Conclusion `C1 : MA² − MB²` — le milieu `M` de `[BC]` est à égale
distance de `A` et de `B` (§2). Le milieu est substitué coordonnée par
coordonnée : `x_M = (x_B + x_C)/2`, `y_M = (y_B + y_C)/2`. -/
noncomputable def FilC1 : MvPolynomial (Fin 6) ℚ :=
  (C (1 / 2 : ℚ) * (X 2 + X 4) - X 0)^2 + (C (1 / 2 : ℚ) * (X 3 + X 5) - X 1)^2
    - ((C (1 / 2 : ℚ) * (X 4 - X 2))^2 + (C (1 / 2 : ℚ) * (X 5 - X 3))^2)

/-- Conclusion symétrique `C' : MA² − MC²` (§4, la cellule « coefficients »
du notebook la rend par la liste `[1]`). -/
noncomputable def FilCp : MvPolynomial (Fin 6) ℚ :=
  (C (1 / 2 : ℚ) * (X 2 + X 4) - X 0)^2 + (C (1 / 2 : ℚ) * (X 3 + X 5) - X 1)^2
    - ((C (1 / 2 : ℚ) * (X 2 - X 4))^2 + (C (1 / 2 : ℚ) * (X 3 - X 5))^2)

/-- Composante transverse `C3 : MB² − MC²` — les deux demi-diagonales de
`[BC]` ont même longueur (§4 : le notebook la rend nulle par réduction). -/
noncomputable def FilC3 : MvPolynomial (Fin 6) ℚ :=
  (C (1 / 2 : ℚ) * (X 4 - X 2))^2 + (C (1 / 2 : ℚ) * (X 5 - X 3))^2
    - ((C (1 / 2 : ℚ) * (X 2 - X 4))^2 + (C (1 / 2 : ℚ) * (X 3 - X 5))^2)

/-- Conclusion **non prouvable** `C_iso : AB² − AC²` — le triangle est
isocèle en `A` (§5). -/
noncomputable def FilCiso : MvPolynomial (Fin 6) ℚ :=
  (X 2 - X 0)^2 + (X 3 - X 1)^2 - ((X 4 - X 0)^2 + (X 5 - X 1)^2)

/-- **Le certificat du quotient 1** (§2, cellule « réduire `C1` par `H` ») :
la conclusion `C1` est **égale** à l'hypothèse `H` — quotient exactement 1,
reste exactement 0, comme le rend la sortie sympy du notebook. L'équidistance
n'est pas une conséquence profonde : c'est l'orthogonalité **réécrite**. -/
theorem fil_c1_eq_h : FilC1 = FilH :=
  MvPolynomial.funext fun z =>
    by simp [FilC1, FilH, eval_sub, eval_add, eval_mul, eval_pow, eval_X, eval_C] <;> ring

/-- **L'appartenance à l'idéal, côté Mathlib** (§3) : `C1 ∈ ⟨H⟩` — lu par
`Ideal.mem_span_singleton'`, avec le quotient 1 du certificat précédent pour
unique témoin. C'est la lecture formelle de « reste nul » : la conclusion vit
dans l'idéal engendré par l'hypothèse. -/
theorem fil_c1_mem_ideal : FilC1 ∈ Ideal.span {FilH} := by
  rw [Ideal.mem_span_singleton']
  exact ⟨1, by rw [one_mul]; exact fil_c1_eq_h.symm⟩

/-- La composante symétrique aussi : `C' = H` (§4, liste de coefficients
`[1]`) — le quotient est encore exactement 1. -/
theorem fil_cp_eq_h : FilCp = FilH :=
  MvPolynomial.funext fun z =>
    by simp [FilCp, FilH, eval_sub, eval_add, eval_mul, eval_pow, eval_X, eval_C] <;> ring

/-- La composante transverse est **identiquement nulle** : `C3 = 0` — les
vecteurs `M − B` et `M − C` sont opposés (une seule demi-diagonale, deux
signes), donc leurs carrés sont égaux (§4). -/
theorem fil_c3_eq_zero : FilC3 = 0 :=
  MvPolynomial.funext fun z =>
    by simp [FilC3, eval_sub, eval_add, eval_mul, eval_pow, eval_X, eval_C] <;> ring

/-- **Ce que « prouvé » garantit, pour le fil rouge** : partout où `H`
s'annule, les trois conclusions d'équidistance s'annulent — `M` est le centre
du cercle circonscrit (le `Geometry.MidpointHypotenuse` abstrait, lu en
coordonnées). C'est l'annulation universelle que la seule appartenance à
l'idéal suffit à établir. -/
theorem fil_soundness (z : Fin 6 → ℚ) (h : eval z FilH = 0) :
    eval z FilC1 = 0 ∧ eval z FilCp = 0 ∧ eval z FilC3 = 0 := by
  constructor
  · rw [fil_c1_eq_h]; exact h
  constructor
  · rw [fil_cp_eq_h]; exact h
  · rw [fil_c3_eq_zero]; simp

/-- **Lecture générale : l'idéal entier s'annule, chaque membre suit.** Pour
tout idéal de `ℚ[x₀,…,x₅]` et tout point qui l'annule, l'appartenance à
l'idéal entraîne l'annulation — c'est le pont entre l'algèbre de Mathlib
(`Ideal.span`, `Ideal.mem_span_singleton'`) et la lecture géométrique
(variété des hypothèses). -/
theorem mem_ideal_vanishes (I : Ideal (MvPolynomial (Fin 6) ℚ))
    {f : MvPolynomial (Fin 6) ℚ} (hf : f ∈ I) (z : Fin 6 → ℚ)
    (hz : ∀ g ∈ I, eval z g = 0) : eval z f = 0 :=
  hz f hf

/-- **Témoin négatif : l'isocélité n'est pas dans l'idéal** (§5). L'énoncé
« angle droit en `A` donc `AB = AC` » est faux : au triangle 3-4-5 du
notebook (`A = (0,0)`, `B = (3,0)`, `C = (0,4)` — angle droit en `A`),
l'hypothèse s'annule et `C_iso` vaut `−7 ≠ 0`. Le reste non nul du notebook
et le contre-exemple formel disent la même chose : pas de théorème sans
appartenance. -/
theorem fil_iso_unprovable :
    ¬ (∀ z : Fin 6 → ℚ, eval z FilH = 0 → eval z FilCiso = 0) := by
  intro h
  have hw := h ![0, 0, 3, 0, 0, 4]
    (by simp [FilH, eval_sub, eval_add, eval_mul, eval_X])
  simp [FilCiso, eval_sub, eval_add, eval_pow, eval_X] at hw
  norm_num at hw

/-! ## Le théorème faux et le vrai besoin (notebook §6)

Encodage du notebook, `A` fixé à l'origine : `X 0 = x_B`, `X 1 = y_B`,
`X 2 = x_C`, `X 3 = y_C`, `X 4 = x_D`, `X 5 = y_D`. Hypothèses `h_a :
AB ⊥ AC` et `h_b : AB ⊥ AD` ; conclusion `concl = det(C, D)` (le
déterminant 2×2 des vecteurs `AC` et `AD`, nul ssi `A, C, D` sont alignés).
La réduction du notebook rend un reste **non nul** : la conclusion n'est pas
dans l'idéal `⟨h_a, h_b⟩` — et pour cause. -/

/-- Hypothèse `h_a : AB ⊥ AC` — produit scalaire nul (notebook §6). -/
noncomputable def NdHA : MvPolynomial (Fin 6) ℚ := X 0 * X 2 + X 1 * X 3

/-- Hypothèse `h_b : AB ⊥ AD` (notebook §6). -/
noncomputable def NdHB : MvPolynomial (Fin 6) ℚ := X 0 * X 4 + X 1 * X 5

/-- Conclusion `concl : x_C · y_D − x_D · y_C` — `A, C, D` alignés
(déterminant 2×2 nul). -/
noncomputable def NdConcl : MvPolynomial (Fin 6) ℚ := X 2 * X 5 - X 4 * X 3

/-- Condition de non-dégénérescence `g : B ≠ A` — `AB² = x_B² + y_B²`
(notebook §7). -/
noncomputable def NdG : MvPolynomial (Fin 6) ℚ := (X 0)^2 + (X 1)^2

/-- Coefficient `u` du certificat de Ritt : `x_B y_D − y_B x_D`
(composante du produit vectoriel `AB × AD`). -/
noncomputable def NdU : MvPolynomial (Fin 6) ℚ := X 0 * X 5 - X 1 * X 4

/-- Coefficient `v` du certificat de Ritt : `x_B y_C − y_B x_C`
(composante du produit vectoriel `AB × AC`). -/
noncomputable def NdV : MvPolynomial (Fin 6) ℚ := X 0 * X 3 - X 1 * X 2

/-- **Le théorème est faux, pas seulement hors de portée** (§6). Au point
`B = A = (0,0)`, `C = (1,0)`, `D = (0,1)` du notebook, les deux hypothèses
d'orthogonalité s'annulent (le vecteur nul est orthogonal à tout) et la
conclusion vaut `1 ≠ 0` : `A, C, D` ne sont pas alignés. Le reste non nul de
la réduction signale ici un énoncé **réfutable** — la leçon du notebook :
avant de chercher une preuve, demander ce que dit l'idéal. -/
theorem nd_false_unprovable :
    ¬ (∀ z : Fin 6 → ℚ, eval z NdHA = 0 → eval z NdHB = 0 →
        eval z NdConcl = 0) := by
  intro h
  have hw := h ![0, 0, 1, 0, 0, 1]
    (by simp [NdHA, eval_add, eval_mul, eval_X])
    (by simp [NdHB, eval_add, eval_mul, eval_X])
  simp [NdConcl, eval_sub, eval_mul, eval_X] at hw

/-! ## L'astuce de Ritt — saturation par `B ≠ A` (notebook §7)

Le notebook adjoint à l'idéal la condition de non-dégénérescence `g =
AB²` (via l'inverse virtuel de Rabinowitsch) et obtient un reste nul. Ce
module rend les deux faces du geste : l'identité maîtresse ci-dessous dit que
`g • concl` est dans l'idéal `⟨h_a, h_b⟩` **sans** condition — c'est
l'appartenance à l'idéal saturé, exposant 1 — et la section suivante encode
l'inverse virtuel en sept variables. -/

/-- **Identité maîtresse de Ritt** — le reste nul du notebook rendu explicite :
`g • concl = u • h_a − v • h_b`, une identité de `ℚ[x_B,…,y_D]` vérifiée par
`ring`. Le membre de gauche porte la conclusion **multipliée par** la
non-dégénérescence : c'est exactement ce que la saturation mesure. -/
theorem ritt_identity : NdG * NdConcl = NdU * NdHA - NdV * NdHB :=
  MvPolynomial.funext fun z =>
    by simp [NdG, NdConcl, NdU, NdV, NdHA, NdHB, eval_sub, eval_add, eval_mul,
        eval_pow, eval_X] <;> ring

/-- **Appartenance à l'idéal saturé, exposant 1** (§7) : `g • concl ∈
⟨h_a, h_b⟩`, lu par `Ideal.mem_span_pair` avec les coefficients `u` et `−v`
de l'identité maîtresse. En langage des idéaux : la conclusion appartient à
l'idéal `⟨h_a, h_b⟩` saturé par `g` dès l'exposant un. -/
theorem ritt_mem_ideal : NdG * NdConcl ∈ Ideal.span {NdHA, NdHB} := by
  rw [Ideal.mem_span_pair]
  refine ⟨NdU, -NdV, ?_⟩
  rw [neg_mul, ← sub_eq_add_neg]
  exact ritt_identity.symm

/-- Version évaluée de l'identité maîtresse — le pont vers la lecture
géométrique. -/
theorem ritt_eval_identity (z : Fin 6 → ℚ) :
    (z 0^2 + z 1^2) * eval z NdConcl
      = (z 0 * z 5 - z 1 * z 4) * eval z NdHA
        - (z 0 * z 3 - z 1 * z 2) * eval z NdHB := by
  have h := congrArg (eval z) ritt_identity
  simpa [NdG, NdConcl, NdU, NdV, NdHA, NdHB, eval_sub, eval_add, eval_mul,
    eval_pow, eval_X] using h

/-- **Le théorème prouvé sous `B ≠ A`** (§7) : partout où `h_a` et `h_b`
s'annulent et où `g` ne s'annule **pas**, la conclusion s'annule. C'est la
réponse au « vrai besoin » du §6 : l'énoncé faux devient théorème dès que la
non-dégénérescence exclut le point singulier `B = A`. -/
theorem ritt_soundness (z : Fin 6 → ℚ) (ha : eval z NdHA = 0)
    (hb : eval z NdHB = 0) (hg : eval z NdG ≠ 0) : eval z NdConcl = 0 := by
  have h := ritt_eval_identity z
  rw [ha, hb] at h
  simp only [mul_zero, sub_zero] at h
  have hg' : (z 0 ^ 2 + z 1 ^ 2) ≠ 0 := by simpa [NdG] using hg
  exact (mul_eq_zero.mp h).resolve_left hg'

/-! ## L'inverse virtuel — l'encodage Rabinowitsch en sept variables
(notebook §7)

Le geste algorithmique du notebook : ajouter une variable `z` (ici `X 6`)
et l'hypothèse `z • g − 1`, qui force `g` inversible donc `B ≠ A` **dans
l'anneau quotient**. La conclusion revient alors dans l'idéal augmenté —
l'identité ci-dessous en est le certificat explicite, la où le notebook
observe un reste nul. -/

/-- Hypothèse `h_a`, copie en sept variables (`X 6` = inverse virtuel). -/
noncomputable def rabHA : MvPolynomial (Fin 7) ℚ := X 0 * X 2 + X 1 * X 3

/-- Hypothèse `h_b`, copie en sept variables. -/
noncomputable def rabHB : MvPolynomial (Fin 7) ℚ := X 0 * X 4 + X 1 * X 5

/-- Conclusion `concl`, copie en sept variables. -/
noncomputable def rabConcl : MvPolynomial (Fin 7) ℚ := X 2 * X 5 - X 4 * X 3

/-- Coefficient `u`, copie en sept variables. -/
noncomputable def rabU : MvPolynomial (Fin 7) ℚ := X 0 * X 5 - X 1 * X 4

/-- Coefficient `v`, copie en sept variables. -/
noncomputable def rabV : MvPolynomial (Fin 7) ℚ := X 0 * X 3 - X 1 * X 2

/-- Hypothèse de Rabinowitsch `z • g − 1` avec `g = x_B² + y_B²` : `z`
est l'inverse virtuel de la non-dégénérescence. -/
noncomputable def rabZ : MvPolynomial (Fin 7) ℚ :=
  X 6 * ((X 0)^2 + (X 1)^2) - 1

/-- **Certificat Rabinowitsch** : la conclusion est combinaison explicite des
trois hypothèses — `(z • u) • h_a − (z • v) • h_b − concl • (z • g − 1) =
concl`. Vérifiée par `ring` ; chaque coefficient est polynomial. C'est le
contenu exact du « reste nul après saturation » du notebook. -/
theorem rab_identity :
    (X 6 * rabU) * rabHA + -(X 6 * rabV) * rabHB + -rabConcl * rabZ
      = rabConcl :=
  MvPolynomial.funext fun z =>
    by simp [rabU, rabV, rabHA, rabHB, rabConcl, rabZ, eval_sub, eval_add,
        eval_mul, eval_pow, eval_X] <;> ring

/-- **L'appartenance à l'idéal augmenté** : `concl ∈ ⟨h_a, h_b, z • g − 1⟩`,
lue par `Submodule.mem_span_triple` avec les coefficients du certificat. En
saturant par `B ≠ A`, la conclusion interdite du §6 redevient élément de
l'idéal — la frontière entre « faux » et « vrai sous condition » est
exactement la saturation. -/
theorem rab_mem_ideal : rabConcl ∈ Ideal.span {rabHA, rabHB, rabZ} := by
  rw [Submodule.mem_span_triple]
  refine ⟨X 6 * rabU, -(X 6 * rabV), -rabConcl, ?_⟩
  simp only [smul_eq_mul]
  exact rab_identity

/-- **Soundness de l'idéal augmenté** : partout où les trois hypothèses
s'annulent, la conclusion s'annule — la lecture géométrique du certificat
Rabinowitsch, même théorème que `ritt_soundness` vu depuis l'anneau quotient
par l'inverse virtuel. -/
theorem rab_soundness (z : Fin 7 → ℚ) (ha : eval z rabHA = 0)
    (hb : eval z rabHB = 0) (hz : eval z rabZ = 0) : eval z rabConcl = 0 := by
  have h := congrArg (eval z) rab_identity
  simp only [eval_add, eval_mul, ha, hb, hz, mul_zero, add_zero] at h
  simpa using h.symm
