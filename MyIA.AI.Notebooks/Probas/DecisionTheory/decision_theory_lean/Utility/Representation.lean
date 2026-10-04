import Mathlib
import Utility.Basic
import Utility.Axioms

/-!
# Représentation en utilité espérée

Le théorème de représentation de von Neumann–Morgenstern (vNM) relie les
préférences axiomatiques sur les loteries à la maximisation de l'utilité
espérée :

> Une préférence `P` sur les loteries satisfait (complétude, transitivité,
> indépendance, continuité) **si et seulement si** il existe une fonction
> d'utilité `u : α → ℝ` telle que `P p q ↔ E_p[u] ≥ E_q[u]`, unique à
> transformation affine positive près.

Ce fichier prouve le **sens direct** (représentation ⟹ rationalité) et les
lemmes de **stabilité affine** (cardinalité / unicité à transformation affine
positive près) intégralement, sans aucun `sorry`. Le **sens d'existence**
(rationalité ⟹ existence d'une utilité représentante) est la moitié
substantielle du théorème (Herstein–Milnor 1953) ; il est documenté plus bas
comme un jalon ouvert et n'est pas énoncé comme un résultat adossé à `sorry`.

Références croisées :
- Infer-14 (Infer.NET) : les utilités d'espérance postérieure calculées là sont
  une instance de `expectation` sur une postérieure bayésienne ; la
  représentation ici est la justification en théorie de la décision du
  classement par utilité espérée.
- PyMC-1 (PyMC) : les estimations d'utilité espérée postérieure par
  échantillonnage approchent le même opérateur `expectation` ; l'unicité
  affine justifie pourquoi seules les *différences* d'utilité (et non les
  niveaux) sont identifiées par les données de choix.

Convention i18n (EPIC #4980) : FR-first appliqué sur les en-têtes et docstrings
publics. Le code tactique et les commentaires intra-preuve restent en anglais
(références Mathlib, notation formelle).
-/

namespace Utility

variable {α : Type*} [Fintype α]

/-- `IsExpectedUtilityRep u P` affirme que la fonction d'utilité `u` représente
la préférence `P` : `p` est faiblement préférée à `q` exactement quand
l'utilité espérée sous `p` est au moins celle sous `q`. -/
def IsExpectedUtilityRep (u : α → ℝ) (P : Pref α) : Prop :=
  ∀ p q : Lottery α, P p q ↔ expectation p u ≥ expectation q u

section EasyDirection

/-!
## Représentation ⟹ Rationalité (sens direct, sans sorry)

Si une fonction d'utilité représente `P`, alors `P` satisfait les quatre
axiomes vNM. Les axiomes se ramènent à des faits élémentaires sur l'ordre et
la structure affine de `ℝ`.
-/

/-- Une préférence représentée est complète : deux espérances quelconques sont
des nombres réels et donc comparables. -/
theorem rep_complete (u : α → ℝ) (P : Pref α) (h : IsExpectedUtilityRep u P) :
    IsComplete P := by
  intro p q
  by_cases he : expectation p u ≥ expectation q u
  · exact Or.inl ((h p q).mpr he)
  · simp only [not_le] at he
    exact Or.inr ((h q p).mpr (le_of_lt he))

/-- Une préférence représentée est transitive : l'inégalité large sur `ℝ` est
transitive. -/
theorem rep_transitive (u : α → ℝ) (P : Pref α) (h : IsExpectedUtilityRep u P) :
    IsTransitive P := by
  intro p q r hpq hqr
  refine (h p r).mpr ?_
  have h1 := (h p q).mp hpq
  have h2 := (h q r).mp hqr
  linarith

/-- Une préférence représentée satisfait l'indépendance : mélanger avec une
loterie commune préserve l'ordre des utilités espérées, car l'espérance est
affine. -/
theorem rep_independent (u : α → ℝ) (P : Pref α) (h : IsExpectedUtilityRep u P) :
    IsIndependent P := by
  intro p q r t ht0 ht1 hpq
  apply (h _ _).mpr
  rw [expectation_mix t p r u ht0 ht1, expectation_mix t q r u ht0 ht1]
  have hpq' : expectation p u ≥ expectation q u := (h p q).mp hpq
  nlinarith [hpq', ht0, ht1, sub_nonneg.mpr ht1]

/-- Une préférence représentée satisfait la continuité : étant donné
`p ≽ q ≽ r`, les utilités espérées vérifient `E_p ≥ E_q ≥ E_r`, donc
l'interpolation affine `g(t) = t·E_p + (1-t)·E_r` sur `t ∈ [0,1]` croise
`E_q`, rendant le mélange correspondant indifférent à `q`. -/
theorem rep_continuous (u : α → ℝ) (P : Pref α) (h : IsExpectedUtilityRep u P) :
    IsContinuous P := by
  intro p q r hpq hqr
  have hEpq : expectation p u ≥ expectation q u := (h p q).mp hpq
  have hEqr : expectation q u ≥ expectation r u := (h q r).mp hqr
  by_cases hne : expectation p u = expectation r u
  · -- Degenerate case: all three expectations coincide; any mixture is indifferent.
    refine ⟨(1 : ℝ) / 2, by norm_num, by norm_num, ?_, ?_⟩
    · have he : expectation (mix ((1:ℝ)/2) p r (by norm_num) (by norm_num)) u
          = expectation q u := by
        rw [expectation_mix, hne]; linarith
      exact (h _ _).mpr (by linarith [he])
    · have he : expectation (mix ((1:ℝ)/2) p r (by norm_num) (by norm_num)) u
          = expectation q u := by
        rw [expectation_mix, hne]; linarith
      exact (h _ _).mpr (by linarith [he])
  · -- Non-degenerate case: E_p > E_r; cross at t = (E_q − E_r)/(E_p − E_r) ∈ [0,1].
    have hlt : expectation p u > expectation r u := by
      refine lt_of_le_of_ne ?_ (Ne.symm hne)
      linarith
    have hdenom : 0 < expectation p u - expectation r u := sub_pos.mpr hlt
    set t : ℝ := (expectation q u - expectation r u) / (expectation p u - expectation r u) with htdef
    have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hEqr) (le_of_lt hdenom)
    have ht1 : t ≤ 1 := (div_le_one hdenom).mpr (by linarith)
    refine ⟨t, ht0, ht1, ?_, ?_⟩
    · have he : expectation (mix t p r ht0 ht1) u = expectation q u := by
        rw [expectation_mix, htdef]
        have hne0 : expectation p u - expectation r u ≠ 0 := ne_of_gt hdenom
        field_simp [hne0]
        ring
      exact (h _ _).mpr (by linarith [he])
    · have he : expectation (mix t p r ht0 ht1) u = expectation q u := by
        rw [expectation_mix, htdef]
        have hne0 : expectation p u - expectation r u ≠ 0 := ne_of_gt hdenom
        field_simp [hne0]
        ring
      exact (h _ _).mpr (by linarith [he])

/-- **Sens direct du théorème vNM** : si une fonction d'utilité représente une
préférence, alors cette préférence est rationnelle (satisfait les quatre
axiomes). C'est la moitié sans sorry du théorème de représentation. -/
theorem expected_utility_rep_is_rational (u : α → ℝ) (P : Pref α)
    (h : IsExpectedUtilityRep u P) : IsRational P where
  complete := rep_complete u P h
  transitive := rep_transitive u P h
  independent := rep_independent u P h
  continuous := rep_continuous u P h

end EasyDirection

section AffineStability

/-!
## Stabilité affine (unicité à transformation affine positive près)

Si `u` représente `P`, toute transformation affine positive `a • u + b` avec
`a > 0` représente aussi `P`. C'est la moitié facile du résultat de
cardinalité vNM : seule la forme affine de l'utilité est fixée par les données
de choix.
-/

/-- Une transformation affine positive d'une utilité représentante est à
nouveau une utilité représentante : l'utilité espérée se transforme comme
`E_p[a·u + b] = a·E_p[u] + b`, donc l'ordre est préservé par la mise à
l'échelle positive `a` et est invariant sous le décalage commun `b`. -/
theorem affine_rep_is_rep (u : α → ℝ) (P : Pref α) (h : IsExpectedUtilityRep u P)
    (a : ℝ) (ha : 0 < a) (b : ℝ) :
    IsExpectedUtilityRep (fun x => a * u x + b) P := by
  intro p q
  rw [expectation_affine p a b u, expectation_affine q a b u]
  refine ⟨fun hpq => ?_, fun hge => ?_⟩
  · have hpq' : expectation p u ≥ expectation q u := (h p q).mp hpq
    nlinarith [hpq', ha]
  · apply (h p q).mpr
    nlinarith [hge, ha]

end AffineStability

section StrictAndIndifference

/-!
## Préférence stricte et indifférence sous une représentation

La représentation faible `IsExpectedUtilityRep u P` fixe
`p ≽ q ↔ E_p[u] ≥ E_q[u]`. Deux caractérisations compagnons suivent par
raisonnement élémentaire sur l'ordre de `ℝ`, complétant la trichotomie
faible / stricte / indifférente d'une préférence représentée — l'analogue vNM
de la dichotomie mono-livre / poids-probabilités de `Coherence`.
-/

/-- Sous une représentation, la **préférence stricte** `p ≻ q` (faiblement
    préférée dans un sens, pas dans l'autre) vaut exactement quand l'utilité
    espérée sous `p` *excède strictement* celle sous `q`. C'est la compagnonne
    stricte de `IsExpectedUtilityRep`. -/
theorem rep_strict_iff (u : α → ℝ) (P : Pref α) (h : IsExpectedUtilityRep u P)
    (p q : Lottery α) :
    StrictPref P p q ↔ expectation p u > expectation q u := by
  show P p q ∧ ¬ P q p ↔ expectation p u > expectation q u
  refine ⟨fun ⟨hpp, hnqp⟩ => ?_, fun hgt => ⟨?_, ?_⟩⟩
  · -- P p q ∧ ¬ P q p  ⟹ E_p > E_q
    have hge : expectation p u ≥ expectation q u := (h p q).mp hpp
    by_contra hneg
    -- hneg : ¬ E_p > E_q  ⟹  E_p ≤ E_q  ⟹  P q p, contradicting hnqp
    exact hnqp ((h q p).mpr (not_lt.mp hneg))
  · -- E_p > E_q  ⟹  P p q
    exact (h p q).mpr (le_of_lt hgt)
  · -- E_p > E_q  ⟹  ¬ P q p
    intro hqp
    have hle := (h q p).mp hqp
    linarith

/-- Sous une représentation, l'**indifférence** `p ~ q` (chacune faiblement
    préférée à l'autre) vaut exactement quand les deux utilités espérées
    coïncident. Avec `rep_strict_iff`, cela partitionne une préférence représentée
    en les trois cas exhaustifs (strict-p / strict-q / indifférente) via la
    trichotomie de `ℝ`. -/
theorem rep_indifference_iff (u : α → ℝ) (P : Pref α) (h : IsExpectedUtilityRep u P)
    (p q : Lottery α) :
    (P p q ∧ P q p) ↔ expectation p u = expectation q u := by
  refine ⟨fun ⟨hpp, hqp⟩ => ?_, fun heq => ?_⟩
  · -- P p q ∧ P q p  ⟹  E_p = E_q  (squeeze the two inequalities)
    have hge := (h p q).mp hpp
    have hle := (h q p).mp hqp
    linarith
  · -- E_p = E_q  ⟹  P p q ∧ P q p
    exact ⟨(h p q).mpr (by linarith), (h q p).mpr (by linarith)⟩

/-- **Irréflexivité de la préférence stricte** sous une représentation : aucune
    loterie n'est strictement préférée à elle-même. Corollaire immédiat de
    `rep_strict_iff` (`E_p > E_p` est absurde). -/
theorem strict_irrefl (u : α → ℝ) (P : Pref α) (h : IsExpectedUtilityRep u P)
    (p : Lottery α) : ¬ StrictPref P p p := by
  rw [rep_strict_iff u P h]
  exact lt_irrefl _

end StrictAndIndifference

section OrderAlgebra

/-!
## L'algèbre ordre-théorique d'une préférence représentée

`rep_strict_iff` et `rep_indifference_iff` transportent une préférence
représentée sur l'ordre de `ℝ`. Par conséquent, la partie stricte `≻` hérite
de la structure d'un ordre strict (irréflexive — déjà montrée dans
`StrictAndIndifference` —, asymétrique, transitive), la partie indifférence
`~` hérite de celle d'une relation d'équivalence, et les deux s'entrelacent :
un pas strict absorbe un pas indifférent adjacent. Chaque preuve ci-dessous
est le fait élémentaire correspondant sur `<` / `=` sur `ℝ`, remonté à travers
la représentation. Ensemble, elles referment la trichotomie qu'ouvre
`StrictAndIndifference`. -/

/-- **L'indifférence correspond à l'égalité des utilités espérées.**
Reformulation de `rep_indifference_iff` via la relation nommée `Indiff` ; les
deux sont la même conjonction définitionnellement, donc la preuve est
l'équivalence antérieure verbatim. -/
theorem rep_indiff_iff (u : α → ℝ) (P : Pref α) (h : IsExpectedUtilityRep u P)
    (p q : Lottery α) :
    Indiff P p q ↔ expectation p u = expectation q u :=
  rep_indifference_iff u P h p q

/-- **La préférence stricte est asymétrique** : `p ≻ q` interdit `q ≻ p`, car
`E_p > E_q` exclut `E_q > E_p`. -/
theorem strict_asymm (u : α → ℝ) (P : Pref α) (h : IsExpectedUtilityRep u P)
    {p q : Lottery α} (hpq : StrictPref P p q) : ¬ StrictPref P q p := by
  rw [rep_strict_iff u P h] at hpq ⊢
  intro hqp
  linarith

/-- **La préférence stricte est transitive** : `p ≻ q` et `q ≻ r` donnent
`p ≻ r`, en enchaînant `E_p > E_q > E_r`. Avec `strict_irrefl` et
`strict_asymm`, `≻` est un ordre strict. -/
theorem strict_trans (u : α → ℝ) (P : Pref α) (h : IsExpectedUtilityRep u P)
    {p q r : Lottery α} (hpq : StrictPref P p q) (hqr : StrictPref P q r) :
    StrictPref P p r := by
  rw [rep_strict_iff u P h] at hpq hqr ⊢
  linarith

/-- **L'indifférence est réflexive** : toute loterie est indifférente à
elle-même (`E_p = E_p`). -/
theorem indiff_refl (u : α → ℝ) (P : Pref α) (h : IsExpectedUtilityRep u P)
    (p : Lottery α) : Indiff P p p := by
  rw [rep_indiff_iff u P h]

/-- **L'indifférence est symétrique** : `p ~ q` donne `q ~ p` (l'égalité est
symétrique). -/
theorem indiff_symm (u : α → ℝ) (P : Pref α) (h : IsExpectedUtilityRep u P)
    {p q : Lottery α} (hpq : Indiff P p q) : Indiff P q p := by
  rw [rep_indiff_iff u P h] at hpq ⊢
  linarith

/-- **L'indifférence est transitive** : `p ~ q` et `q ~ r` donnent `p ~ r`
(`E_p = E_q = E_r`). Avec la réflexivité et la symétrie, `~` est une relation
d'équivalence sur les loteries. -/
theorem indiff_trans (u : α → ℝ) (P : Pref α) (h : IsExpectedUtilityRep u P)
    {p q r : Lottery α} (hpq : Indiff P p q) (hqr : Indiff P q r) :
    Indiff P p r := by
  rw [rep_indiff_iff u P h] at hpq hqr ⊢
  linarith

/-- **Un pas strict absorbe un pas indifférent suivant** : `p ≻ q` et `q ~ r`
donnent `p ≻ r` (`E_p > E_q = E_r`). -/
theorem strict_indiff_trans (u : α → ℝ) (P : Pref α) (h : IsExpectedUtilityRep u P)
    {p q r : Lottery α} (hpq : StrictPref P p q) (hqr : Indiff P q r) :
    StrictPref P p r := by
  rw [rep_strict_iff u P h] at hpq ⊢
  rw [rep_indiff_iff u P h] at hqr
  linarith

/-- **Un pas indifférent absorbe un pas strict suivant** : `p ~ q` et `q ≻ r`
donnent `p ≻ r` (`E_p = E_q > E_r`). -/
theorem indiff_strict_trans (u : α → ℝ) (P : Pref α) (h : IsExpectedUtilityRep u P)
    {p q r : Lottery α} (hpq : Indiff P p q) (hqr : StrictPref P q r) :
    StrictPref P p r := by
  rw [rep_indiff_iff u P h] at hpq
  rw [rep_strict_iff u P h] at hqr ⊢
  linarith

/-- **Trichotomie** : sous une représentation, deux loteries quelconques
tombent dans au moins l'un des cas `p ≻ q`, `q ≻ p`, `p ~ q`. L'exhaustivité
est la trichotomie de `<` sur `E_p, E_q` ; les trois cas sont de plus
mutuellement exclusifs (`strict_asymm` écarte la stricte inverse, et une
préférence stricte force `E_p ≠ E_q`). -/
theorem rep_trichotomy (u : α → ℝ) (P : Pref α) (h : IsExpectedUtilityRep u P)
    (p q : Lottery α) :
    StrictPref P p q ∨ StrictPref P q p ∨ Indiff P p q := by
  rcases lt_trichotomy (expectation p u) (expectation q u) with hlt | heq | hgt
  · exact Or.inr (Or.inl ((rep_strict_iff u P h q p).mpr hlt))
  · exact Or.inr (Or.inr ((rep_indiff_iff u P h p q).mpr heq))
  · exact Or.inl ((rep_strict_iff u P h p q).mpr hgt)

end OrderAlgebra

/-!
## Sens d'existence — JALON OUVERT

La réciproque — **toute préférence rationnelle admet une représentation en
utilité espérée** — est la moitié substantielle du théorème de von
Neumann–Morgenstern (Herstein & Milnor, 1953). Sa preuve procède par :

1. Établir que la préférence est représentée par une fonctionnelle linéaire
   sur le simplexe des loteries (l'indépendance donne la linéarité le long
   des lignes de mélange, la continuité l'étend à l'intérieur).
2. Montrer que cette fonctionnelle linéaire est une espérance `E_p[u]` pour
   un certain `u : α → ℝ`, récupéré des valeurs de la fonctionnelle sur les
   masses de Dirac.

Cela requiert un argument non trivial de séparation / d'algèbre linéaire et
est laissé comme prochain jalon naturel. Il est délibérément **non** énoncé
comme un théorème adossé à `sorry` : la bibliothèque présente est entièrement
sans `sorry`, livrant la réciproque saine, les quatre axiomes sous une
représentation, et l'unicité affine.
-/

end Utility
