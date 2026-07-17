/-
  Équilibre de Nash bayésien (formulation interimaire)
  ====================================================

  - `isBNE` : un profil de stratégies est un BNE quand aucun type de
    l'un ou l'autre joueur n'a de déviation unilatérale d'action
    profitable, en utilité espérée interimaire. Les quantificateurs
    portent uniquement sur les types et actions `Fin`, donc la propriété
    est décidable (`decide` fonctionne sur des jeux concrets).
  - `exAnteU1_le_of_interim_best` : le principe de déviation unique dans
    ce cadre fini — l'optimalité interimaire implique l'optimalité ex-ante
    vis-à-vis de déviations contingentes au type arbitraires.
  - `isBNE_scaleW` : le BNE est invariant par remise à l'échelle des poids
    du prior par une constante positive (indépendance de normalisation :
    les poids `Nat` représentent toute mesure de probabilité qui leur est
    proportionnelle).

  Voir #2610 (formalisation GT-Lean, phase bayésienne 1).
-/

import Bayesian.Types

/-- Équilibre de Nash bayésien, formulation interimaire : pour chaque type de
    chaque joueur, l'action prescrite maximise l'utilité espérée interimaire
    face à la stratégie de l'adversaire.

    Réductible pour que l'instance `Decidable` soit trouvée par dépliage
    (conjonction de `∀` sur `Fin` de comparaisons `Int` décidables). -/
@[reducible] def isBNE (g : BayesGame2) (s1 : Strategy1 g) (s2 : Strategy2 g) : Prop :=
  (∀ t1 : Fin g.nT1, ∀ a : Fin g.nA1,
      interimU1 g t1 a s2 ≤ interimU1 g t1 (s1 t1) s2) ∧
  (∀ t2 : Fin g.nT2, ∀ a : Fin g.nA2,
      interimU2 g t2 a s1 ≤ interimU2 g t2 (s2 t2) s1)

/-- Principe de déviation unique, côté joueur 1 : si chaque type du
    joueur 1 joue une meilleure réponse interimaire, alors aucune déviation
    contingente au type `s1'` n'améliore l'utilité espérée ex-ante du joueur 1. -/
theorem exAnteU1_le_of_interim_best (g : BayesGame2)
    {s1 : Strategy1 g} {s2 : Strategy2 g}
    (h : ∀ t1 a, interimU1 g t1 a s2 ≤ interimU1 g t1 (s1 t1) s2)
    (s1' : Strategy1 g) :
    exAnteU1 g s1' s2 ≤ exAnteU1 g s1 s2 :=
  sumFin_mono (fun t1 => h t1 (s1' t1))

/-- Principe de déviation unique, côté joueur 2. -/
theorem exAnteU2_le_of_interim_best (g : BayesGame2)
    {s1 : Strategy1 g} {s2 : Strategy2 g}
    (h : ∀ t2 a, interimU2 g t2 a s1 ≤ interimU2 g t2 (s2 t2) s1)
    (s2' : Strategy2 g) :
    exAnteU2 g s1 s2' ≤ exAnteU2 g s1 s2 :=
  sumFin_mono (fun t2 => h t2 (s2' t2))

/-- Un BNE est aussi un équilibre de Nash ex-ante : aucun joueur ne gagne
    à dévier unilatéralement de façon contingente au type. -/
theorem bne_exAnte (g : BayesGame2) {s1 : Strategy1 g} {s2 : Strategy2 g}
    (h : isBNE g s1 s2) :
    (∀ s1', exAnteU1 g s1' s2 ≤ exAnteU1 g s1 s2) ∧
    (∀ s2', exAnteU2 g s1 s2' ≤ exAnteU2 g s1 s2) :=
  ⟨exAnteU1_le_of_interim_best g h.1, exAnteU2_le_of_interim_best g h.2⟩

/-- Le même jeu avec tous les poids du prior multipliés par `c`. -/
@[reducible] def scaleW (g : BayesGame2) (c : Nat) : BayesGame2 :=
  { g with w := fun t1 t2 => c * g.w t1 t2 }

theorem interimU1_scaleW (g : BayesGame2) (c : Nat)
    (t1 : Fin g.nT1) (a : Fin g.nA1) (s2 : Strategy2 g) :
    interimU1 (scaleW g c) t1 a s2 = (c : Int) * interimU1 g t1 a s2 := by
  unfold interimU1
  rw [← sumFin_mul_left]
  apply sumFin_congr
  intro t2
  rw [Int.natCast_mul, Int.mul_assoc]

theorem interimU2_scaleW (g : BayesGame2) (c : Nat)
    (t2 : Fin g.nT2) (a : Fin g.nA2) (s1 : Strategy1 g) :
    interimU2 (scaleW g c) t2 a s1 = (c : Int) * interimU2 g t2 a s1 := by
  unfold interimU2
  rw [← sumFin_mul_left]
  apply sumFin_congr
  intro t1
  rw [Int.natCast_mul, Int.mul_assoc]

/-- Le BNE est invariant par remise à l'échelle positive des poids du prior.
    C'est ce qui fait des poids `Nat` non normalisés un encodage fidèle
    d'un prior commun : seuls les rapports des poids importent. -/
theorem isBNE_scaleW (g : BayesGame2) (c : Nat) (hc : 0 < c)
    (s1 : Strategy1 g) (s2 : Strategy2 g) :
    isBNE (scaleW g c) s1 s2 ↔ isBNE g s1 s2 := by
  have hc' : (0 : Int) < (c : Int) := by omega
  constructor
  · intro ⟨h1, h2⟩
    refine ⟨fun t1 a => ?_, fun t2 a => ?_⟩
    · have := h1 t1 a
      rw [interimU1_scaleW, interimU1_scaleW] at this
      exact Int.le_of_mul_le_mul_left this hc'
    · have := h2 t2 a
      rw [interimU2_scaleW, interimU2_scaleW] at this
      exact Int.le_of_mul_le_mul_left this hc'
  · intro ⟨h1, h2⟩
    refine ⟨fun t1 a => ?_, fun t2 a => ?_⟩
    · rw [interimU1_scaleW, interimU1_scaleW]
      exact Int.mul_le_mul_of_nonneg_left (h1 t1 a) (Int.le_of_lt hc')
    · rw [interimU2_scaleW, interimU2_scaleW]
      exact Int.mul_le_mul_of_nonneg_left (h2 t2 a) (Int.le_of_lt hc')
