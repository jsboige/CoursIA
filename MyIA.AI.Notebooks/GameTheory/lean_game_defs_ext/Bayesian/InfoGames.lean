/-
  L'information peut nuire dans les jeux (contre-exemple, vérifié au noyau)
  ==============================================================

  `Information.lean` prouve qu'un décideur *seul* ne perd jamais à
  observer un signal (monotonie de Blackwell). Ce fichier montre que le
  résultat est authentiquement à un joueur : dans un jeu, donner à un
  joueur strictement plus d'information peut strictement *réduire* son
  paiement d'équilibre.

  L'exemple (construction classique à deux états, 2x2) : un état
  θ ∈ {0, 1} est tiré avec poids égaux. Le joueur 1 (lignes, actions T/B)
  n'observe jamais θ. On compare deux scénarios pour le joueur 2
  (colonnes, actions l/r) :

  - `gNoInfo` : le joueur 2 n'observe pas θ non plus. Les paiements sont
    le plongement des tables dépendant de l'état sur θ (réduction ex-ante :
    un type par joueur, paiements sommés sur les états — voir
    `infoHurts_reduction`).
  - `gInfo` : le joueur 2 observe privément θ (deux types).

  Voir `Information.lean` et le fichier original pour les tables de
  paiement dépendant de l'état et l'argument d'équilibre. Les deux jeux
  portent la même échelle de poids de prior totale, donc les paiements 3
  et 5 sont directement comparables.

  L'unicité de l'équilibre est établie pour *tous* les profils de
  stratégies en réduisant une stratégie arbitraire à un constructeur
  canonique (`mkS1g`/`mkS2g`, une éta-expansion sur les littéraux `Fin`)
  puis en décidant l'énoncé fini par calcul au noyau.

  Voir #2610 (formalisation GT-Lean, phase bayésienne 4).
-/

import Bayesian.BNE

/-- Le jeu informé : le joueur 2 observe privément l'état θ (son type), -/
def gInfo : BayesGame2 where
  nT1 := 1
  nT2 := 2
  nA1 := 2
  nA2 := 2
  w := fun _ _ => 1
  u1 := fun _ t2 a1 a2 =>
    if t2.val = 0 then
      (if a1.val = 0 then (if a2.val = 0 then 2 else 0) else 0)
    else
      (if a1.val = 0 then (if a2.val = 0 then 2 else 0)
       else (if a2.val = 0 then 0 else 4))
  u2 := fun _ t2 a1 a2 =>
    if t2.val = 0 then
      (if a1.val = 0 then (if a2.val = 0 then 3 else 0)
       else (if a2.val = 0 then 2 else 0))
    else
      (if a1.val = 0 then (if a2.val = 0 then 2 else 3)
       else (if a2.val = 0 then 0 else 1))

/-- Le benchmark non informé : personne n'observe θ, donc les deux joueurs -/
def gNoInfo : BayesGame2 where
  nT1 := 1
  nT2 := 1
  nA1 := 2
  nA2 := 2
  w := fun _ _ => 1
  u1 := fun _ _ a1 a2 =>
    if a1.val = 0 then (if a2.val = 0 then 4 else 0)
    else (if a2.val = 0 then 0 else 4)
  u2 := fun _ _ a1 a2 =>
    if a1.val = 0 then (if a2.val = 0 then 5 else 3)
    else (if a2.val = 0 then 2 else 1)

/-- Vérification : les paiements de `gNoInfo` sont exactement ceux de -/
theorem infoHurts_reduction :
    ∀ a1 a2 : Fin 2,
      gNoInfo.u1 ⟨0, by decide⟩ ⟨0, by decide⟩ a1 a2 =
        gInfo.u1 ⟨0, by decide⟩ ⟨0, by decide⟩ a1 a2 +
        gInfo.u1 ⟨0, by decide⟩ ⟨1, by decide⟩ a1 a2 ∧
      gNoInfo.u2 ⟨0, by decide⟩ ⟨0, by decide⟩ a1 a2 =
        gInfo.u2 ⟨0, by decide⟩ ⟨0, by decide⟩ a1 a2 +
        gInfo.u2 ⟨0, by decide⟩ ⟨1, by decide⟩ a1 a2 := by
  decide

/-! ### Canonical strategy constructors (informed game) -/

/-- Les stratégies du joueur 1 dans `gInfo` sont constantes (un seul type). -/
def mkS1g (x : Fin 2) : Strategy1 gInfo := fun _ => x

/-- Les stratégies du joueur 2 dans `gInfo`, depuis les deux actions -/
def mkS2g (y z : Fin 2) : Strategy2 gInfo :=
  fun t2 => if t2.val = 0 then y else z

/-- Toute stratégie du joueur 1 est une constante canonique. -/
theorem s1g_eta (s1 : Strategy1 gInfo) : s1 = mkS1g (s1 ⟨0, by decide⟩) := by
  funext t1
  cases t1 using Fin.cases with
  | zero => rfl
  | succ j => exact j.elim0

/-- Toute stratégie du joueur 2 est déterminée par ses deux valeurs. -/
theorem s2g_eta (s2 : Strategy2 gInfo) :
    s2 = mkS2g (s2 ⟨0, by decide⟩) (s2 ⟨1, by decide⟩) := by
  funext t2
  cases t2 using Fin.cases with
  | zero => rfl
  | succ j =>
    cases j using Fin.cases with
    | zero => rfl
    | succ j' => exact j'.elim0

/-! ### Equilibrium analysis of the informed game -/

/-- (B, suivre-l'état) est un BNE du jeu informé. -/
theorem gInfo_bne :
    isBNE gInfo (mkS1g ⟨1, by decide⟩) (mkS2g ⟨0, by decide⟩ ⟨1, by decide⟩) := by
  decide

/-- Sur les stratégies canoniques, le BNE de `gInfo` est unique : le -/
theorem gInfo_unique_aux :
    ∀ x y z : Fin 2,
      isBNE gInfo (mkS1g x) (mkS2g y z) →
        x = ⟨1, by decide⟩ ∧ y = ⟨0, by decide⟩ ∧ z = ⟨1, by decide⟩ := by
  decide

/-- Sur les stratégies canoniques, tout BNE de `gInfo` paie le joueur 2
    exactement 3. -/
theorem gInfo_exAnteU2_aux :
    ∀ x y z : Fin 2,
      isBNE gInfo (mkS1g x) (mkS2g y z) →
        exAnteU2 gInfo (mkS1g x) (mkS2g y z) = 3 := by
  decide

/-- Le jeu informé a un BNE essentiellement unique. -/
theorem gInfo_unique (s1 : Strategy1 gInfo) (s2 : Strategy2 gInfo)
    (h : isBNE gInfo s1 s2) :
    s1 = mkS1g ⟨1, by decide⟩ ∧ s2 = mkS2g ⟨0, by decide⟩ ⟨1, by decide⟩ := by
  rw [s1g_eta s1, s2g_eta s2] at h
  have hu := gInfo_unique_aux _ _ _ h
  exact ⟨by rw [s1g_eta s1, hu.1], by rw [s2g_eta s2, hu.2.1, hu.2.2]⟩

/-- Dans tout BNE du jeu informé, le joueur 2 gagne 3. -/
theorem gInfo_bne_payoff (s1 : Strategy1 gInfo) (s2 : Strategy2 gInfo)
    (h : isBNE gInfo s1 s2) : exAnteU2 gInfo s1 s2 = 3 := by
  rw [s1g_eta s1, s2g_eta s2] at h ⊢
  exact gInfo_exAnteU2_aux _ _ _ h

/-! ### Equilibrium analysis of the uninformed game -/

/-- Les stratégies du joueur 1 dans `gNoInfo` sont constantes. -/
def mkS1n (x : Fin 2) : Strategy1 gNoInfo := fun _ => x

/-- Les stratégies du joueur 2 dans `gNoInfo` sont constantes. -/
def mkS2n (y : Fin 2) : Strategy2 gNoInfo := fun _ => y

theorem s1n_eta (s1 : Strategy1 gNoInfo) : s1 = mkS1n (s1 ⟨0, by decide⟩) := by
  funext t1
  cases t1 using Fin.cases with
  | zero => rfl
  | succ j => exact j.elim0

theorem s2n_eta (s2 : Strategy2 gNoInfo) : s2 = mkS2n (s2 ⟨0, by decide⟩) := by
  funext t2
  cases t2 using Fin.cases with
  | zero => rfl
  | succ j => exact j.elim0

/-- (T, l) est un BNE du jeu non informé. -/
theorem gNoInfo_bne :
    isBNE gNoInfo (mkS1n ⟨0, by decide⟩) (mkS2n ⟨0, by decide⟩) := by
  decide

/-- Sur les stratégies canoniques, tout BNE de `gNoInfo` paie le joueur 2
    exactement 5 (le BNE (T, l) est en fait unique, par dominance stricte
    de l). -/
theorem gNoInfo_exAnteU2_aux :
    ∀ x y : Fin 2,
      isBNE gNoInfo (mkS1n x) (mkS2n y) →
        exAnteU2 gNoInfo (mkS1n x) (mkS2n y) = 5 := by
  decide

/-- Dans tout BNE du jeu non informé, le joueur 2 gagne 5. -/
theorem gNoInfo_bne_payoff (s1 : Strategy1 gNoInfo) (s2 : Strategy2 gNoInfo)
    (h : isBNE gNoInfo s1 s2) : exAnteU2 gNoInfo s1 s2 = 5 := by
  rw [s1n_eta s1, s2n_eta s2] at h ⊢
  exact gNoInfo_exAnteU2_aux _ _ h

/-! ### Punchline -/

/-- **L'information peut nuire dans les jeux.** Dans tout équilibre, le -/
theorem information_hurts
    (s1 : Strategy1 gInfo) (s2 : Strategy2 gInfo)
    (t1 : Strategy1 gNoInfo) (t2 : Strategy2 gNoInfo)
    (hI : isBNE gInfo s1 s2) (hN : isBNE gNoInfo t1 t2) :
    exAnteU2 gInfo s1 s2 < exAnteU2 gNoInfo t1 t2 := by
  rw [gInfo_bne_payoff s1 s2 hI, gNoInfo_bne_payoff t1 t2 hN]
  decide
