/-
  Ritt — companion Lean du notebook Geometry-03b (décomposition de Ritt)
  ====================================================================

  Quatrième module du lac `geometry_lean` (EPIC #18601 volet B, « la suite
  vit côté #17544 »). Il double
  `Geometry-03b-Ritt-Decomposition-Python.ipynb` en formalisant **ce que la
  décomposition de Ritt garantit** quand le test de Wu global rend un verdict
  NON CONCLUANT.

  Le fil rouge du notebook est le théorème T2 du papillon : deux cordes
  `(AB)` et `(CD)` d'un cercle coupent l'axe `(PQ)` en `X` et `Y`, et le
  milieu de `[XY]` est un point fixe. Le test de Wu sur l'encodage global
  rend `prem(g₂, CS) ≠ 0` — NON CONCLUANT. Le notebook explique pourquoi :
  l'énoncé parlant de `x_X` et `y_Y` ne vit que là où les dénominateurs
  `(d₂ − a₂)` et `(b₂ − c₂)` ne s'annulent pas ; la variété porte donc des
  strates muettes, et la décomposition de Ritt — scinder sur les facteurs
  du dénominateur, tester composante par composante — remplace le verdict
  unique par un verdict par strate.

  Ce que le notebook calcule avec sympy (chaînes ascendantes, pseudo-restes,
  `ritt_split_one`), ce module le prouve, en quatre familles d'énoncés
  calquées sur les sections du notebook :

  * **§2 — l'identité dénominateur** : `g₂ = (x_X + y_Y) · den`, donc sur
    le lieu non dégénéré (`den ≠ 0`) l'équivalence `g₂ = 0 ↔ x_X + y_Y = 0` :
    la conclusion algébrique et la conclusion géométrique disent la même
    chose exactement là où l'énoncé a un sens.

  * **§4 — les strates** : sur la strate doublement dégénérée
    (`d₂ = a₂` et `b₂ = c₂`), `g₂` s'annule **identiquement** — un zéro
    trivial, structurel, qui n'est pas un certificat de théorème. Et le
    **témoin du bord** du notebook (cercle `c = 2`, corde `AD` horizontale,
    point rationnel) : un point de `V(H₂)` sur le bord `d₂ = a₂` où
    `g₂ = 24/5 ≠ 0` — preuve que l'énoncé global « `g₂ = 0` sur `V(H₂)` »
    est **faux**, et que le NON CONCLUANT du pseudo-reste était le verdict
    juste.

  * **§3 — les branches vides de la scission** : sur l'exemple jouet
    `Hs = [(x² − 1)y − 2, xz − y]`, la scission sur l'initiale `(x−1)(x+1)`
    produit des branches **sans points** — tester composante par composante
    exige de détecter le vide, pas seulement d'exécuter le test par branche.

  * **§5–6 — le lieu non dégénéré** : un point témoin **rationnel et
    générique** (les deux cordes hors axe, `X = (3/7, 0)`, `Y = (−3/7, 0)`,
    milieu exactement `P`) où les six hypothèses tiennent, `den ≠ 0`, la
    conclusion vraie `g₂ = 0` tient — et la conclusion délibérément fausse
    `g₂^×` (second terme doublé) vaut `−189/85 ≠ 0` : la décomposition doit
    aussi savoir dire non.

  Non-but assumé (non-buts de l'EPIC) : ce module ne migre pas
  `char_set`, `wu_prem` ni `ritt_split_one` en Lean exécutable — il
  formalise les garanties sémantiques qu'ils établissent. L'astuce de
  Ritt/Rabinowitsch (saturation par non-annulation) vit dans
  `Geometry.GroebnerBridge` ; la décomposition-ci est l'autre volet du
  même nom.
-/

import Mathlib

/-! ## T2 le papillon — encodage (notebook §1-2)

Encodage du notebook, cellule 4 : le cercle `x² + y² − 2c·y − 1 = 0`
(paramètre `cc`), les cordes `(AB)` (pente `m₁`) et `(CD)` (pente `m₂`)
passant par l'origine `P = (0,0)`, l'axe `(PQ)` est `y = 0`. `X = (AD) ∩ (PQ)`
et `Y = (CB) ∩ (PQ)`. Les six hypothèses `H₂` : quatre appartiances au
cercle (`h_a`, `h_b`, `h_c`, `h_d`) et deux alignements avec `P` (`h_ab`,
`h_cd` par déterminants 2×2). La conclusion `g₂` encode « le milieu de
`[XY]` est sur l'axe en `P` » sans division : `x_X + y_Y = 0` après
multiplication par le dénominateur. -/

/-- Hypothèse `h_a` : `A = (a₁,a₂)` est sur le cercle `x² + y² − 2c·y − 1`. -/
def rittHA (cc a1 a2 : ℚ) : ℚ := a1^2 + a2^2 - 2*cc*a2 - 1

/-- Hypothèse `h_b` : `B = (b₁,b₂)` est sur le cercle. -/
def rittHB (cc b1 b2 : ℚ) : ℚ := b1^2 + b2^2 - 2*cc*b2 - 1

/-- Hypothèse `h_c` : `C = (c₁,c₂)` est sur le cercle. -/
def rittHC (cc c1 c2 : ℚ) : ℚ := c1^2 + c2^2 - 2*cc*c2 - 1

/-- Hypothèse `h_d` : `D = (d₁,d₂)` est sur le cercle. -/
def rittHD (cc d1 d2 : ℚ) : ℚ := d1^2 + d2^2 - 2*cc*d2 - 1

/-- Hypothèse `h_ab` : `A` et `B` alignés avec `P = (0,0)`
(déterminant 2×2 nul). -/
def rittHAB (a1 a2 b1 b2 : ℚ) : ℚ := a1*b2 - a2*b1

/-- Hypothèse `h_cd` : `C` et `D` alignés avec `P` (déterminant 2×2 nul). -/
def rittHCD (c1 c2 d1 d2 : ℚ) : ℚ := c1*d2 - c2*d1

/-- Conclusion `g₂` du papillon, cellule 4 du notebook :
« `x_X + y_Y = 0` » multipliée par le dénominateur
`(d₂ − a₂)(b₂ − c₂)` — l'énoncé algébrique du théorème T2. -/
def rittG2 (a1 a2 b1 b2 c1 c2 d1 d2 : ℚ) : ℚ :=
  (a1*d2 - a2*d1)*(b2 - c2) + (c1*b2 - c2*b1)*(d2 - a2)

/-- Conclusion **fausse** du témoin négatif (§6 du notebook) : la même que
`g₂` avec le second terme doublé — elle affirme « `x_X + 2·y_Y = 0` »,
qu'aucune figure générique ne vérifie. -/
def rittGFaux (a1 a2 b1 b2 c1 c2 d1 d2 : ℚ) : ℚ :=
  (a1*d2 - a2*d1)*(b2 - c2) + 2*(c1*b2 - c2*b1)*(d2 - a2)

/-! ## §2 — l'identité dénominateur et l'équivalence -/

/-- **Identité dénominateur (§2, cellule 10 du notebook).** La conclusion
`g₂` est exactement `(x_X + y_Y) · den` avec
`den = (d₂ − a₂)(b₂ − c₂)` — l'identité vérifiée par sympy dans le
notebook, ici par `ring` après nettoyage des fractions. C'est elle qui
dit ce que l'énoncé algébrique affirme **vraiment** : pas « le milieu est
en `P` », mais « le milieu est en `P`, **ou** l'un des dénominateurs est
nul ». -/
theorem ritt_denominator_identity (a1 a2 b1 b2 c1 c2 d1 d2 : ℚ)
    (h1 : d2 - a2 ≠ 0) (h2 : b2 - c2 ≠ 0) :
    rittG2 a1 a2 b1 b2 c1 c2 d1 d2
      = ((a1*d2 - a2*d1)/(d2 - a2) + (c1*b2 - c2*b1)/(b2 - c2))
          * ((d2 - a2)*(b2 - c2)) := by
  simp only [rittG2]
  field_simp

/-- **Sur le lieu non dégénéré, les deux lectures coïncident.** Là où
`den ≠ 0`, `g₂ = 0` **équivaut** à `x_X + y_Y = 0` : multiplier par le
dénominateur n'ajoute aucune solution parasite sur l'ouvert où l'énoncé
géométrique a un sens. C'est la moitié positive de la restriction implicite
que la décomposition rend visible. -/
theorem ritt_conclusion_iff (a1 a2 b1 b2 c1 c2 d1 d2 : ℚ)
    (h1 : d2 - a2 ≠ 0) (h2 : b2 - c2 ≠ 0) :
    rittG2 a1 a2 b1 b2 c1 c2 d1 d2 = 0 ↔
      (a1*d2 - a2*d1)/(d2 - a2) + (c1*b2 - c2*b1)/(b2 - c2) = 0 := by
  have hden : (d2 - a2) * (b2 - c2) ≠ 0 := mul_ne_zero h1 h2
  rw [ritt_denominator_identity a1 a2 b1 b2 c1 c2 d1 d2 h1 h2]
  constructor
  · intro h
    exact mul_right_cancel₀ hden (h.trans (zero_mul _).symm)
  · intro h
    rw [h, zero_mul]

/-! ## §4 — les strates : le zéro trivial et le témoin du bord -/

/-- **La strate doublement dégénérée annule `g₂` identiquement (§4, cellule
19).** Si `d₂ = a₂` **et** `b₂ = c₂`, chaque terme de `g₂` porte l'un des
deux facteurs : le premier `(a₁d₂ − a₂d₁)(b₂ − c₂)` meurt par `b₂ = c₂`, le
second `(c₁b₂ − c₂b₁)(d₂ − a₂)` par `d₂ = a₂`. Ce zéro est **trivial** —
structurel, vrai sans aucune hypothèse — et le notebook est explicite : ce
n'est **pas** un certificat de théorème, seulement l'aveu que le test ne
peut plus rien y contredire. -/
theorem ritt_double_degenerate (a1 a2 b1 b2 c1 c2 d1 d2 : ℚ)
    (e1 : d2 = a2) (e2 : b2 = c2) :
    rittG2 a1 a2 b1 b2 c1 c2 d1 d2 = 0 := by
  subst e1
  subst e2
  simp only [rittG2]
  ring

/-- **Le témoin du bord (§4, cellule 18 du notebook).** Il existe un point
**rationnel** de `V(H₂)` — le cercle `c = 2`, la corde `(AD)` horizontale
`A = (−2,1)`, `D = (2,1)`, `C = (2,1)`, `B = (2/5, −1/5)` — sur le bord
`d₂ = a₂` (corde `(AD)` parallèle à `(PQ)`, `X` à l'infini), avec `b₂ ≠ c₂`
et **`g₂ = 24/5 ≠ 0`**. Géométriquement : `X` n'existe pas, l'énoncé est
muet — rien à réfuter ; algébriquement : `g₂` ne s'y annule pas. -/
theorem ritt_border_point_exists :
    ∃ (cc a1 a2 b1 b2 c1 c2 d1 d2 : ℚ),
      rittHA cc a1 a2 = 0 ∧ rittHB cc b1 b2 = 0 ∧ rittHAB a1 a2 b1 b2 = 0 ∧
      rittHC cc c1 c2 = 0 ∧ rittHD cc d1 d2 = 0 ∧ rittHCD c1 c2 d1 d2 = 0 ∧
      d2 = a2 ∧ b2 ≠ c2 ∧ rittG2 a1 a2 b1 b2 c1 c2 d1 d2 ≠ 0 := by
  refine ⟨2, -2, 1, 2/5, -1/5, 2, 1, 2, 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [rittHA, rittHB, rittHC, rittHD, rittHAB, rittHCD, rittG2]

/-- **Pourquoi le test de Wu dit NON — et pourquoi il a raison (§1-§2).**
L'énoncé global « `g₂ = 0` partout sur `V(H₂)` » est **faux** : le témoin
du bord le réfute. Le pseudo-reste non nul `prem(g₂, CS) ≠ 0` du notebook
n'est donc pas un échec de l'outil mais le verdict correct sur un énoncé
trop gros — la décomposition de Ritt est ce qui découpe l'énoncé en strates
où chacune a un verdict honnête. -/
theorem ritt_naive_statement_refuted :
    ¬ (∀ (cc a1 a2 b1 b2 c1 c2 d1 d2 : ℚ),
        rittHA cc a1 a2 = 0 → rittHB cc b1 b2 = 0 → rittHAB a1 a2 b1 b2 = 0 →
        rittHC cc c1 c2 = 0 → rittHD cc d1 d2 = 0 → rittHCD c1 c2 d1 d2 = 0 →
        rittG2 a1 a2 b1 b2 c1 c2 d1 d2 = 0) := by
  intro h
  obtain ⟨cc, a1, a2, b1, b2, c1, c2, d1, d2,
    hA, hB, hAB, hC, hD, hCD, -, -, hg⟩ := ritt_border_point_exists
  exact hg (h cc a1 a2 b1 b2 c1 c2 d1 d2 hA hB hAB hC hD hCD)

/-! ## §3 — les branches vides de la scission (exemple jouet) -/

/-- **Une branche de la scission de Ritt peut être vide (§3, cellule 13).**
Sur l'exemple jouet du notebook `Hs = [(x² − 1)y − 2, xz − y]`,
l'initiale du premier polynôme se factorise en `(x − 1)(x + 1)` : la
scission ouvre les branches `x = 1` et `x = −1`. Or **aucun point** de
`V(Hs)` n'y vit : à `x = 1`, le polynôme vaut `−2 ≠ 0` quel que soit `y`.
Tester composante par composante exige de détecter le vide — exécuter le
test dans une branche sans points ne prouve rien. -/
theorem ritt_split_branch_empty_one (x y : ℚ)
    (h : (x^2 - 1)*y - 2 = 0) : x ≠ 1 := by
  intro hx
  rw [hx] at h
  norm_num at h

/-- Seconde branche vide du même exemple jouet : à `x = −1`, le polynôme
vaut `−2 ≠ 0` quel que soit `y`. -/
theorem ritt_split_branch_empty_minus (x y : ℚ)
    (h : (x^2 - 1)*y - 2 = 0) : x ≠ -1 := by
  intro hx
  rw [hx] at h
  norm_num at h

/-! ## §5–6 — le lieu non dégénéré : témoin positif et négatif -/

/-- **Témoin non dégénéré rationnel (§5-§6).** Un point **générique** —
cercle `c = 2`, corde `(AB)` de pente `4` (`A = (1,4)`,
`B = (−1/17, −4/17)`), corde `(CD)` de pente `−1/2` (`C = (−2,1)`,
`D = (2/5, −1/5)`), les deux cordes hors axe — où les six hypothèses
tiennent, les deux facteurs du dénominateur sont non nuls, la conclusion
**vraie** `g₂ = 0` tient, et la conclusion **fausse** `g₂^×` vaut
`−189/85 ≠ 0`. La vérification numérique sur 400 figures du notebook a sa
contrepartie exacte en rationnels. -/
theorem ritt_nondegenerate_point_exists :
    ∃ (cc a1 a2 b1 b2 c1 c2 d1 d2 : ℚ),
      rittHA cc a1 a2 = 0 ∧ rittHB cc b1 b2 = 0 ∧ rittHAB a1 a2 b1 b2 = 0 ∧
      rittHC cc c1 c2 = 0 ∧ rittHD cc d1 d2 = 0 ∧ rittHCD c1 c2 d1 d2 = 0 ∧
      d2 - a2 ≠ 0 ∧ b2 - c2 ≠ 0 ∧
      rittG2 a1 a2 b1 b2 c1 c2 d1 d2 = 0 ∧
      rittGFaux a1 a2 b1 b2 c1 c2 d1 d2 ≠ 0 := by
  refine ⟨2, 1, 4, -1/17, -4/17, -2, 1, 2/5, -1/5, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [rittHA, rittHB, rittHC, rittHD, rittHAB, rittHCD, rittG2, rittGFaux]

/-- **Au point témoin, la conclusion lue géométriquement tient (§5).** Par
l'équivalence de §2, `g₂ = 0` et `den ≠ 0` donnent `x_X + y_Y = 0` : le
milieu de `[XY]` est sur l'axe en `P`. Au point témoin, `X = (3/7, 0)` et
`Y = (−3/7, 0)` — le milieu tombe exactement sur `P`, en rationnels. -/
theorem ritt_nondegenerate_conclusion_geometric :
    ∃ (cc a1 a2 b1 b2 c1 c2 d1 d2 : ℚ),
      rittHA cc a1 a2 = 0 ∧ rittHB cc b1 b2 = 0 ∧ rittHAB a1 a2 b1 b2 = 0 ∧
      rittHC cc c1 c2 = 0 ∧ rittHD cc d1 d2 = 0 ∧ rittHCD c1 c2 d1 d2 = 0 ∧
      d2 - a2 ≠ 0 ∧ b2 - c2 ≠ 0 ∧
      (a1*d2 - a2*d1)/(d2 - a2) + (c1*b2 - c2*b1)/(b2 - c2) = 0 := by
  obtain ⟨cc, a1, a2, b1, b2, c1, c2, d1, d2,
    hA, hB, hAB, hC, hD, hCD, h1, h2, hg2, -⟩ := ritt_nondegenerate_point_exists
  exact ⟨cc, a1, a2, b1, b2, c1, c2, d1, d2,
    hA, hB, hAB, hC, hD, hCD, h1, h2,
    (ritt_conclusion_iff a1 a2 b1 b2 c1 c2 d1 d2 h1 h2).mp hg2⟩
