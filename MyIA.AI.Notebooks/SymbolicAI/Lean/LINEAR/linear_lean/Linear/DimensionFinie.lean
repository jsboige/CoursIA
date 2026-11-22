/-
  Linear.DimensionFinie — marche 1 (chapitre 2 d'Axler)
  ============================================

  Source : Sheldon Axler, *Linear Algebra Done Right*, 4e éd., Springer 2024,
  licence CC BY-NC 4.0, version du 30 octobre 2026. Copie archivée au gisement
  partagé (chemin dans `Linear/EspacesVectoriels.lean`). L'ordre suit le
  chapitre 2 : 2.A (envergement, familles libres, lemme de dépendance),
  2.B (bases, critère 2.28, supplémentaire 2.33), 2.C (dimension finie :
  2.35, 2.37-2.43). Les déterminants d'Axler arrivent en chapitre 9 — ce
  choix d'ordre, propre au livre, est repris tel quel par la marche.

  Même discipline qu'`EspacesVectoriels.lean` : les définitions d'Axler sont
  portées par Mathlib, énoncées ici sous leur numéro et déléguées —
  - envergement (Axler 2.4, plus petit sous-espace contenant) → `span` ;
  - famille libre (Axler 2.15) → `LinearIndependent` ;
  - base (Axler 2.26) → `Basis` ;
  - dimension (Axler 2.35) → `finrank`.

  La dimension finie (2.C) suppose `[Module.Finite K V]` — la traduction de
  « finite-dimensional vector space » (Axler 2.23).
-/
import Mathlib

namespace Linear

-- Les organes Mathlib cités dans ce fichier vivent sous `Submodule` (`span`, `mem_sup`) et
-- `Module` (`Basis`, `finrank`) : les ouvrir évite de qualifier chaque énoncé et rend les
-- docstrings ci-dessous lisibles telles quelles.
open Submodule Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-! ### 2.A — Familles libres et lemme de dépendance (Axler 2.15, 2.19, 2.22)

Le cœur de 2.A est le lemme de dépendance linéaire 2.19 : une famille
finie dépendante admet une combinaison non triviale égale à zéro (Axler en
tire l'indice minimal ; la marche énonce l'existence, que Mathlib porte via
`Fintype.linearIndependent_iff`). -/

/-- **Axler 2.19** (lemme de dépendance, forme existence) : une famille finie
dépendante admet une combinaison linéaire **non triviale** égale à zéro. La
forme indice-minimal d'Axler est la technique de preuve ; l'organe Mathlib est
`Fintype.linearIndependent_iff`. -/
theorem combinaison_non_triviale {n : ℕ} (v : Fin n → V)
    (h : ¬ LinearIndependent K v) :
    ∃ g : Fin n → K, ∑ i, g i • v i = 0 ∧ ∃ i, g i ≠ 0 := by
  rw [Fintype.linearIndependent_iff] at h
  push Not at h
  obtain ⟨g, hg, i, hi⟩ := h
  exact ⟨g, hg, i, hi⟩

/-- **Axler 2.22** : la longueur d'une famille libre est au plus celle d'une
famille couvrante du même espace. Preuve par la dimension : l'envergement
d'une famille libre de `m` vecteurs a pour dimension `m`
(`finrank_span_eq_card`), l'envergement d'une famille
couvrante est l'espace entier. -/
theorem longueur_libre_le_couverte [Module.Finite K V] {m n : ℕ}
    (v : Fin m → V) (hv : LinearIndependent K v)
    (w : Fin n → V) (hw : span K (Set.range w) = ⊤) :
    m ≤ n := by
  have h1 : finrank K ↥(span K (Set.range v)) = m := by
    rw [finrank_span_eq_card hv, Fintype.card_fin]
  have h2 : finrank K ↥(span K (Set.range v)) ≤ finrank K V :=
    Submodule.finrank_le _
  have h3 : finrank K V ≤ n := by
    simpa using finrank_le_of_span_eq_top hw
  omega

/-! ### 2.B — Bases et supplémentaires (Axler 2.28, 2.33)

Axler définit une base (2.26) comme famille libre ET couvrante ; le critère
2.28 en donne la lecture combinatoire : chaque vecteur est combinaison des
autres. Le théorème 2.32 (toute famille libre s'étend en une base) est porté
par Mathlib (`exists_linearIndependent_extension`) et cité sans re-preuve ;
le complément 2.33 est énoncé sous sa forme déléguée. -/

/-- **Axler 2.28** (critère de base) : `x` appartient à l'envergement de la
famille `v` si et seulement si `x` est combinaison linéaire des `v i` — c'est
la lecture « coefficients » de la définition 2.26. Organe Mathlib :
`mem_span_range_iff_exists_fun`. -/
theorem critere_base {ι : Type*} [Fintype ι] (v : ι → V) (x : V) :
    x ∈ span K (Set.range v) ↔ ∃ c : ι → K, ∑ i, c i • v i = x :=
  mem_span_range_iff_exists_fun K

/-- **Axler 2.33** : tout sous-espace d'un espace vectoriel admet un
supplémentaire (chaque sous-espace de dimension finie a une base qu'on
prolonge, cf. 2.32 ci-dessus). Organe Mathlib : `Submodule.exists_isCompl`. -/
theorem complement_existe (U : Submodule K V) : ∃ W : Submodule K V, IsCompl U W :=
  Submodule.exists_isCompl U

/-! ### 2.C — Dimension finie (Axler 2.35-2.43)

La dimension d'un espace de dimension finie (2.35) est la longueur commune
de toutes ses bases ; les conséquences 2.37-2.43 suivent l'ordre du livre :
sous-espace (2.37), famille libre de la bonne taille (2.38), sous-espace de
pleine dimension (2.39), famille couvrante de la bonne taille (2.42),
formule de Grassmann (2.43). -/

/-- **Axler 2.35** : la dimension d'un espace vectoriel de dimension finie
est la longueur de chacune de ses bases. Organe Mathlib :
`Module.finrank_eq_card_basis` (toutes les bases ont même longueur, cf. 2.36). -/
theorem dimension_base {ι : Type*} [Fintype ι] (b : Basis ι K V) :
    finrank K V = Fintype.card ι :=
  Module.finrank_eq_card_basis b

/-- **Axler 2.37** : si `V` est de dimension finie, tout sous-espace `U` de
`V` est de dimension finie et `dim U ≤ dim V`. Organes Mathlib :
`Submodule.finrank_le` (via `finrank_top`). -/
theorem dim_sous_espace_le [Module.Finite K V] (U : Submodule K V) :
    finrank K ↥U ≤ finrank K V :=
  Submodule.finrank_le U

/-- **Axler 2.38** : dans un espace de dimension `n`, une famille libre de
`n` vecteurs est une base (couvre l'espace). Organe Mathlib :
`Submodule.eq_top_of_finrank_eq` sur l'envergement. -/
theorem famille_libre_bonne_taille_est_base [Module.Finite K V] {n : ℕ}
    (v : Fin n → V) (hv : LinearIndependent K v) (hcard : finrank K V = n) :
    span K (Set.range v) = ⊤ := by
  have h : finrank K ↥(span K (Set.range v)) = finrank K V := by
    rw [finrank_span_eq_card hv, Fintype.card_fin, hcard]
  exact Submodule.eq_top_of_finrank_eq h

/-- **Axler 2.39** : si `V` est de dimension finie, tout sous-espace de `V`
de même dimension que `V` est égal à `V`. Organe Mathlib :
`Submodule.eq_top_of_finrank_eq`. -/
theorem sous_espace_pleine_dimension [Module.Finite K V] (U : Submodule K V)
    (h : finrank K ↥U = finrank K V) : U = ⊤ :=
  Submodule.eq_top_of_finrank_eq h

/-- **Axler 2.42** : dans un espace de dimension `n`, une famille couvrante
de `n` vecteurs est une base (libre). La carte `c ↦ ∑ i, c i • v i` est
linéaire et surjective (critère 2.28), d'une source de dimension `n` vers un
espace de dimension `n` : le rang + noyau force le noyau nul. (Axler le
prouve par 2.19 et minimalité ; l'argument par application linéaire annonce
le chapitre 3, que la marche emprunte ici.) -/
theorem famille_couvante_bonne_taille_est_base [Module.Finite K V] {n : ℕ}
    (v : Fin n → V) (hspan : span K (Set.range v) = ⊤) (hcard : finrank K V = n) :
    LinearIndependent K v := by
  rw [linearIndependent_iff_injective_fintypeLinearCombination]
  set f : (Fin n → K) →ₗ[K] V := Fintype.linearCombination K v with hf
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp
      (show x ∈ span K (Set.range v) by rw [hspan]; trivial)
    exact ⟨c, by rw [hf, Fintype.linearCombination_apply]; exact hc⟩
  have hrange : LinearMap.range f = ⊤ := LinearMap.range_eq_top.2 hsurj
  have hrank : finrank K ↥(LinearMap.range f) + finrank K ↥(LinearMap.ker f)
      = finrank K (Fin n → K) := LinearMap.finrank_range_add_finrank_ker f
  have hdim : finrank K (Fin n → K) = n := Module.finrank_fin_fun K
  rw [hrange, finrank_top, hcard, hdim] at hrank
  have hker : finrank K ↥(LinearMap.ker f) = 0 := by omega
  have hkerbot : LinearMap.ker f = ⊥ := Submodule.finrank_eq_zero.mp hker
  simpa [hf] using (LinearMap.ker_eq_bot).mp hkerbot

/-- **Axler 2.43** (formule de la dimension d'une somme) : pour tous
sous-espaces `U`, `W` d'un espace de dimension finie,
`dim (U + W) = dim U + dim W − dim (U ∩ W)`. Organe Mathlib :
`Submodule.finrank_sup_add_finrank_inf_eq` (forme additive). -/
theorem grassmann [Module.Finite K V] (U W : Submodule K V) :
    finrank K ↥(U ⊔ W) + finrank K ↥(U ⊓ W)
      = finrank K ↥U + finrank K ↥W := by
  exact Submodule.finrank_sup_add_finrank_inf_eq U W

/-! ### Exercices du chapitre 2 (Axler, « Exercises 2A / 2C »)

Trois sorry-cibles documentées (mandat user 2026-11-03) : énoncés seulement,
comptées dans le sorry-baseline du lake (`README.md §sorry`). -/

/-- Exercice **Axler 2A.13** (sorry-cible) : si `v` est libre et que la
famille `i ↦ v i + w` est dépendante, alors `w` est dans l'envergement de
`v`.

Cible prover : medium — par contraposée sur une relation de dépendance
`∑ g i • (v i + w) = 0` non triviale, distinguer `∑ g i = 0` (donne une
dépendance sur `v`, contradiction) de `∑ g i ≠ 0` (isole `w`). Tenté : le
squelette par cas ; la réécriture de `w` comme combinaison reste à écrire. -/
theorem exercice_2A_13 {n : ℕ} (v : Fin n → V) (w : V)
    (hv : LinearIndependent K v)
    (h : ¬ LinearIndependent K (fun i => v i + w)) :
    w ∈ span K (Set.range v) := by
  sorry

/-- Exercice **Axler 2C.12** (sorry-cible) : dans un espace de dimension 8,
des sous-espaces `U` de dimension 3 et `W` de dimension 5 dont la somme est
l'espace entier sont supplémentaires (`U ⊕ W = V`).

Cible prover : easy-medium — par la formule 2.43 (`grassmann`),
`finrank (U ⊓ W) = 3 + 5 − 8 = 0`, donc `U ⊓ W = ⊥`, et `IsCompl` s'ensuit
avec `U ⊔ W = ⊤`. Tenté : le canal 2.43 seul ; la conclusion `IsCompl`
reste à écrire. -/
theorem exercice_2C_12 [Module.Finite K V] (U W : Submodule K V)
    (hdim : finrank K V = 8) (hU : finrank K ↥U = 3) (hW : finrank K ↥W = 5)
    (hsup : U ⊔ W = ⊤) : IsCompl U W := by
  sorry

/-- Exercice **Axler 2C.13** (sorry-cible) : dans un espace de dimension 9,
deux sous-espaces de dimension 5 chacun ont une intersection non nulle.

Cible prover : easy-medium — par contraposée de 2.43 : si `U ⊓ W = ⊥`,
alors `finrank (U ⊔ W) = 10 > 9 = finrank V`, contredisant 2.37. Tenté : le
canal par l'absurde ; l'inégalité finale reste à écrire. -/
theorem exercice_2C_13 [Module.Finite K V] (U W : Submodule K V)
    (hdim : finrank K V = 9) (hU : finrank K ↥U = 5) (hW : finrank K ↥W = 5) :
    U ⊓ W ≠ ⊥ := by
  sorry

end Linear
