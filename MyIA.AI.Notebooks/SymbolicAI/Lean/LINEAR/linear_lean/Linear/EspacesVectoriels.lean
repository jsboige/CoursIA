/-
  Linear.EspacesVectoriels — marche 1 (chapitre 1 d'Axler)
  ============================================

  Source : Sheldon Axler, *Linear Algebra Done Right*, 4e éd., Springer 2024,
  licence CC BY-NC 4.0, version du 30 octobre 2026. Copie archivée au gisement
  partagé : `G:\Mon Drive\MyIA\IA\Bibliographie IA\Pedagogie-Proves\2024 -
  Axler - Linear Algebra Done Right (Springer, 4e edition, CC BY-NC 4.0,
  version 30 oct 2026).pdf`. Chaque énoncé ci-dessous cite son numéro dans le
  livre ; l'ordre des sections suit l'ordre du chapitre 1 (1.A R^n et C^n,
  1.B définition, 1.C sous-espaces et sommes directes).

  Ce fichier distille l'ORDRE d'Axler, pas son texte : les définitions
  d'Axler sont portées par les organes natifs de Mathlib, que la marche
  déclare et cite, jamais redéfinies. Aucune ligne n'est recopiée des
  compagnons (rkirov/linear-algebra-done-right-lean, Apache-2.0 déclaré
  dans son README amont ; blanketism/Axler-Solutions, sans licence
  déclarée), consultés seulement pour comparer les progressions.

  Correspondance Axler → Mathlib :
  - 𝔽 = ℝ ou ℂ (Axler 1.6) → `K` corps quelconque ; les énoncés d'Axler qui
    exigent ℝ ou ℂ (produits scalaires, chapitres 6-7) le diront quand leurs
    marches arriveront ;
  - espace vectoriel (Axler 1.20) → `AddCommGroup V` + `Module K V` ;
  - sous-espace (Axler 1.33) → `Submodule K V` ;
  - somme de sous-espaces (Axler 1.36) → `U ⊔ W`, cf. `Submodule.mem_sup` ;
  - somme directe (Axler 1.41) → `IsCompl U W` (supplémentaires).
-/
import Mathlib

namespace Linear

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-! ### 1.B — Scalaires et vecteur nul (Axler 1.31, 1.32)

Axler établit d'abord les deux identités que la définition 1.20 ne donne pas
immédiatement : un scalaire fois le vecteur nul, et moins un fois un vecteur.
Mathlib les nomme `smul_zero` et `neg_one_smul` : la marche les énonce sous
le numéro d'Axler et délègue. -/

/-- **Axler 1.31** (« a number times the vector 0 ») : `a • 0 = 0` pour tout
scalaire `a`. Organe Mathlib : `smul_zero`. -/
theorem scalaire_fois_zero (a : K) : a • (0 : V) = 0 :=
  smul_zero a

/-- **Axler 1.32** (« the number −1 times a vector ») : `(−1) • v = -v` pour
tout vecteur `v`. Organe Mathlib : `neg_one_smul`. -/
theorem moins_un_fois_vecteur (v : V) : (-1 : K) • v = -v :=
  neg_one_smul K v

/-! ### 1.C — Sommes et sommes directes (Axler 1.36, 1.41, 1.45)

La somme `U + W` des sous-espaces (Axler 1.36) est le plus petit sous-espace
les contenant : c'est `U ⊔ W` dans le treillis des sous-modules. La somme est
directe (Axler 1.41) quand chaque vecteur de la somme s'écrit de façon unique
— critère 1.45 : `U ⊓ W = {0}`. Mathlib capture la paire de conditions sous
`IsCompl U W` (`U ⊓ W = ⊥` et `U ⊔ W = ⊤`). -/

/-- **Axler 1.44** (adapté aux familles) : caractérisation de l'appartenance
à une somme de sous-espaces. Organe Mathlib : `Submodule.mem_sup`. -/
theorem mem_somme (U W : Submodule K V) (x : V) :
    x ∈ U ⊔ W ↔ ∃ u ∈ U, ∃ w ∈ W, x = u + w :=
  Submodule.mem_sup.trans
    ⟨fun ⟨u, hu, w, hw, huw⟩ => ⟨u, hu, w, hw, huw.symm⟩,
     fun ⟨u, hu, w, hw, huw⟩ => ⟨u, hu, w, hw, huw.symm⟩⟩

/-- **Axler 1.45** : si `V = U ⊕ W` (somme directe), chaque vecteur de `V`
s'écrit de manière **unique** comme somme d'un vecteur de `U` et d'un vecteur
de `W`. C'est le critère qui fonde la définition 1.41 de la somme directe ;
Mathlib le porte via `IsCompl`. -/
theorem decomposition_unique_somme_directe {U W : Submodule K V}
    (h : IsCompl U W) (v : V) :
    ∃! p : U × W, (p.1 : V) + (p.2 : V) = v := by
  obtain ⟨u, hu, w, hw, hvw⟩ :=
    Submodule.mem_sup.mp (show v ∈ U ⊔ W by rw [h.sup_eq_top]; exact Submodule.mem_top)
  refine ⟨(⟨u, hu⟩, ⟨w, hw⟩), by simp [hvw], ?_⟩
  rintro ⟨⟨p₁, hp₁⟩, ⟨p₂, hp₂⟩⟩ hp
  have key : p₁ + p₂ = u + w := by rw [hp, hvw]
  have h₁ : p₁ - u = w - p₂ := by
    rw [sub_eq_sub_iff_add_eq_add]
    exact key.trans (add_comm u w)
  have h₂ : p₁ - u ∈ U ⊓ W :=
    Submodule.mem_inf.mpr
      ⟨Submodule.sub_mem U hp₁ hu, h₁ ▸ Submodule.sub_mem W hw hp₂⟩
  rw [h.inf_eq_bot, Submodule.mem_bot] at h₂
  have hp₁' : p₁ = u := by
    have := sub_eq_zero.mp h₂
    exact this
  have hp₂' : p₂ = w := by
    have : w - p₂ = 0 := by rw [← h₁, h₂]
    exact (sub_eq_zero.mp this).symm
  exact Prod.ext (Subtype.ext hp₁') (Subtype.ext hp₂')

/-! ### Exercices du chapitre 1 (Axler, « Exercises 1B »)

Les exercices 1B.1 et 1B.2 sont des échauffements que l'organe disperse en
une ligne : la marche les montre résolus pour exhiber le geste. Les exercices
marqués `Cible prover` sont des **sorry-cibles** documentées (mandat user
2026-11-03) : laissées à l'étudiant/au prouveur, comptées dans le
sorry-baseline du lake (voir `README.md §sorry`). -/

/-- Exercice **Axler 1B.1** (échauffement résolu) : `−(−v) = v` pour tout
`v`. Organe Mathlib : `neg_neg`. -/
theorem exercice_1B_1 (v : V) : -(-v) = v :=
  neg_neg v

/-- Exercice **Axler 1B.2** (échauffement résolu) : si `a • v = 0` alors
`a = 0` ou `v = 0`. Organe Mathlib : `smul_eq_zero`. -/
theorem exercice_1B_2 (a : K) (v : V) (h : a • v = 0) : a = 0 ∨ v = 0 :=
  smul_eq_zero.mp h

/-- Exercice **Axler 1B.3** (sorry-cible) : pour `v w : V`, il existe un
**unique** `x` tel que `v + 3 • x = w`.

Cible prover : easy — construire `x = (3 : K)⁻¹ • (w - v)` (existence par
calcul, `smul_sub`/`add_smul`), puis unicité par `smul_right_injective`
(ou `inject_smul`) avec `(3 : K) ≠ 0`. Tenté : la construction seule ; la
composante `∃!` reste à écrire. -/
-- Hypothese de caracteristique (correctif #26894, nit coordinateur) : sans
-- `[CharZero K]`, en caracteristique 3 on a `(3 : K) = 0`, donc `v + 3 • x = v`
-- independamment de `x` — l'existence exigerait `v = w` et l'unicite est fausse.
-- `CharZero` rend `(3 : K)` non nul et inversible, ce qui valide la construction
-- ci-dessus. Axler travaille sur R ou C (caracteristique 0) : l'hypothese est
-- fidele a la source. Le `sorry` (cible etudiant) est conserve (anti-regression).
theorem exercice_1B_3 [CharZero K] (v w : V) : ∃! x : V, v + (3 : K) • x = w := by
  sorry

end Linear
