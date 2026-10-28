/-
  Théorie du choix social en Lean 4
  =================================

  Formalise les notions clés de la théorie du choix social :
  - Préférences et ordres
  - Fonctions de bien-être social
  - Axiomes d'Arrow (Pareto, IIA, Non-dictature)
  - Théorème d'impossibilité d'Arrow (énoncé)

  Basé sur GameTheory-19-Lean-SocialChoice.ipynb
  Inspiré de asouther4/lean-social-choice (Lean 3)

  ---
  Jumelage i18n : ce module est le FR canonique (sibling pair Pattern A,
  ratifié par user 2026-07-04 sur EPIC #4980). Le miroir anglais vit dans
  `SocialChoice_en.lean` (variante reuse-FR-names : contrairement à `Nash.lean`
  qui dépend du module de base partagé `Basic`, `SocialChoice.lean` est
  autonome — aucun import, Lean core uniquement — donc le miroir EN l'est
  aussi et re-déclare ses types dans `namespace SocialChoiceEn`). Le corps des
  définitions, signatures, tactiques et de l'axiome `arrow_impossibility` est
  byte-identique entre les deux fichiers ; seules les docstrings `/-! ... -/`
  (titres de section) et `/-- ... -/` (docstrings de déclarations) diffèrent,
  FR dans ce fichier, EN dans `SocialChoice_en.lean`.
-/

/-!
## Préférences
-/

/-- Une relation de préférence est une relation binaire sur les alternatives. -/
structure Preference (A : Type) where
  /-- `R x y` signifie « x est au moins aussi bon que y ». -/
  R : A → A → Prop
  /-- Complétude : pour tout x, y, soit R x y soit R y x. -/
  complete : ∀ x y, R x y ∨ R y x
  /-- Transitivité. -/
  trans : ∀ x y z, R x y → R y z → R x z

/-- Préférence stricte : x est strictement préféré à y. -/
def StrictPref {A : Type} (p : Preference A) (x y : A) : Prop :=
  p.R x y ∧ ¬p.R y x

/-- Indifférence : x et y sont également bons. -/
def Indifferent {A : Type} (p : Preference A) (x y : A) : Prop :=
  p.R x y ∧ p.R y x

/-!
## Fonctions de bien-être social
-/

/-- Une fonction de bien-être social agrège les préférences individuelles en une préférence sociale. -/
structure SocialWelfareFunction (I A : Type) where
  /-- La fonction d'agrégation. -/
  aggregate : (I → Preference A) → Preference A

/-!
## Axiomes d'Arrow
-/

/-- Pareto faible : si tout le monde préfère strictement x à y, la société préfère x à y. -/
def WeakPareto {I A : Type} (swf : SocialWelfareFunction I A) : Prop :=
  ∀ prefs : I → Preference A, ∀ x y,
    (∀ i, StrictPref (prefs i) x y) → StrictPref (swf.aggregate prefs) x y

/-- Indépendance des alternatives non pertinentes (IIA). -/
def IIA {I A : Type} (swf : SocialWelfareFunction I A) : Prop :=
  ∀ prefs prefs' : I → Preference A, ∀ x y,
    -- Si les préférences x vs y sont identiques dans les deux profils
    (∀ i, (prefs i).R x y ↔ (prefs' i).R x y) →
    (∀ i, (prefs i).R y x ↔ (prefs' i).R y x) →
    -- Alors la préférence sociale sur x, y est identique
    ((swf.aggregate prefs).R x y ↔ (swf.aggregate prefs').R x y)

/-- Non-dictature : aucun individu unique ne détermine la préférence sociale. -/
def NonDictatorial {I A : Type} (swf : SocialWelfareFunction I A) : Prop :=
  ¬∃ d : I, ∀ prefs : I → Preference A, ∀ x y,
    StrictPref (prefs d) x y → StrictPref (swf.aggregate prefs) x y

/-!
## Théorème d'impossibilité d'Arrow
-/

/--
Théorème d'impossibilité d'Arrow (énoncé) :
il n'existe pas de fonction de bien-être social avec ≥ 3 alternatives qui satisfasse :
1. Pareto faible
2. Indépendance des alternatives non pertinentes
3. Non-dictature

Note : énoncé avec des types `Fin n` explicites plutôt qu'un `Fintype` générique
pour éviter la dépendance Mathlib. Le contenu mathématique du théorème est identique.
-/
-- Port en cours (#23022) : les briques de la preuve vivent dans la section
-- « Coalitions décisives » plus bas ; le théorème reste énoncé comme axiome
-- tant que la réduction n'est pas achevée.
axiom arrow_impossibility {nI nA : Nat}
    (hI : nI ≥ 2)
    (hA : nA ≥ 3)
    (swf : SocialWelfareFunction (Fin nI) (Fin nA))
    (h_pareto : WeakPareto swf)
    (h_iia : IIA swf) :
    ¬NonDictatorial swf

/-!
## Exemples
-/

/-- SWF dictatorial : la préférence de l'individu d devient la préférence sociale. -/
def dictatorship {I A : Type} (d : I) : SocialWelfareFunction I A := {
  aggregate := fun prefs => prefs d
}

/-- Théorème : une dictature satisfait Pareto et IIA. -/
theorem dictatorship_satisfies_pareto {I A : Type} (d : I) :
    WeakPareto (dictatorship (I := I) (A := A) d) := by
  intro prefs x y h_all
  exact h_all d

theorem dictatorship_satisfies_iia {I A : Type} (d : I) :
    IIA (dictatorship (I := I) (A := A) d) := by
  intro prefs prefs' x y h1 h2
  exact h1 d

/-!
## Impossibilité de Sen
-/

/-- Libéralisme minimal : un individu est décisif sur au moins une paire. -/
def MinimalLiberalism {I A : Type} (swf : SocialWelfareFunction I A) : Prop :=
  ∃ i : I, ∃ x y : A,
    ∀ prefs : I → Preference A,
      StrictPref (prefs i) x y → StrictPref (swf.aggregate prefs) x y

/- Théorème d'impossibilité de Sen (énoncé) :
   aucune SWF ne peut satisfaire à la fois Pareto faible et Libéralisme minimal
   sous certaines configurations de préférences.
   (Énoncé plus faible — le théorème complet nécessite de construire
   des profils de préférences spécifiques.) -/

/-!
## Représentations par utilité
-/

/-- Une fonction d'utilité représente une préférence si `u(x) ≥ u(y)` ssi `R x y`. -/
def represents {A : Type} (u : A → Int) (p : Preference A) : Prop :=
  ∀ x y, p.R x y ↔ u x >= u y

/-- Construit une préférence à partir d'une fonction d'utilité. -/
def prefFromUtility {A : Type} (u : A → Int)
    (h_finite : ∀ x y, u x >= u y ∨ u y >= u x := by decide) : Preference A := {
  R := fun x y => u x >= u y
  complete := h_finite
  trans := fun x y z hxy hyz => by omega
}

/-!
## Coalitions décisives

Étage 1 du port de la preuve du théorème d'Arrow (#23022), qui doit remplacer
progressivement l'axiome `arrow_impossibility` déclaré plus haut. La notion est
celle d'Arrow : une coalition `D` est décisive sur la paire `(x, y)` si, chaque
fois que ses membres préfèrent unanimement `x` à `y` et que tous les autres
préfèrent unanimement `y` à `x`, la préférence sociale va dans le sens de `D`.

Ces lemmes restent en Lean core pur : les profils auxiliaires sont construits
par des fonctions d'utilité entières (`rank3`) plutôt que par des ordres
combinatoires, ce qui évite `Finset`/`Fintype` et préserve le lake sans
dépendance. Toute fonction `A → Int` définit une préférence valide
(`prefOfUtility`), et c'est ce qui rend les constructions disponibles sans
bibliothèque.
-/

/-- Rang d'une alternative dans un profil à trois alternatives distinguées :
`a` reçoit `va`, `b` reçoit `vb`, `c` reçoit `vc`, toute autre alternative
reçoit `0`. Suffit à construire les profils auxiliaires de la preuve d'Arrow. -/
def rank3 {A : Type} [DecidableEq A] (a b c : A) (va vb vc : Int) : A → Int :=
  fun z => if z = a then va else if z = b then vb else if z = c then vc else 0

/-- Préférence induite par une fonction d'utilité entière : `x` est au moins
aussi bon que `y` si et seulement si son utilité est supérieure ou égale. -/
def prefOfUtility {A : Type} (u : A → Int) : Preference A where
  R := fun x y => u x ≥ u y
  complete := fun x y => by
    by_cases h : u x ≥ u y
    · exact Or.inl h
    · exact Or.inr (by omega)
  trans := fun x y z hxy hyz => by omega

/-- `D` est décisive sur la paire `(x, y)` : dès que tous les membres de `D`
préfèrent strictement `x` à `y` et tous les non-membres préfèrent strictement
`y` à `x`, la société préfère strictement `x` à `y`. -/
def Decisive {I A : Type} (swf : SocialWelfareFunction I A) (D : I → Prop)
    (x y : A) : Prop :=
  ∀ prefs : I → Preference A,
    (∀ i, D i → StrictPref (prefs i) x y) →
    (∀ i, ¬ D i → StrictPref (prefs i) y x) →
    StrictPref (swf.aggregate prefs) x y

/-- Pareto faible fait de la coalition de tous les agents une coalition
décisive sur toute paire. -/
theorem decisive_unanimous {I A : Type} (swf : SocialWelfareFunction I A)
    (h : WeakPareto swf) {x y : A} : Decisive swf (fun _ => True) x y := by
  intro prefs hD _
  exact h prefs x y (fun i => hD i trivial)

/-- Expansion du champ, axe des alternatives : si `D` est décisive sur `(x, y)`,
elle l'est sur `(x, z)` pour tout `z` distinct de `x` et de `y`.

Preuve (argument d'Arrow) : sur le profil auxiliaire où `D` a `x ≻ y ≻ z` et
où les autres ont `y ≻ z ≻ x`, la décision sur `(x, y)` donne `x ≻s y` et
Pareto donne `y ≻s z`, donc `x ≻s z` par transitivité ; les comparaisons
`x` contre `z` y sont celles du profil visé, donc IIA transporte le résultat. -/
theorem decisive_expand_right {I A : Type} [DecidableEq A]
    (swf : SocialWelfareFunction I A)
    (D : I → Prop) [DecidablePred D] (h_iia : IIA swf) (h_pareto : WeakPareto swf)
    {x y z : A} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h : Decisive swf D x y) : Decisive swf D x z := by
  intro prefs hzD hzND
  let P : I → Preference A :=
    fun i => if D i then prefOfUtility (rank3 x y z 3 2 1)
             else prefOfUtility (rank3 x y z 1 3 2)
  have hPmem : ∀ i, D i → P i = prefOfUtility (rank3 x y z 3 2 1) := by
    intro i hi; simp [P, hi]
  have hPout : ∀ i, ¬ D i → P i = prefOfUtility (rank3 x y z 1 3 2) := by
    intro i hi; simp [P, hi]
  have hdec : StrictPref (swf.aggregate P) x y := by
    apply h P
    · intro i hi
      rw [hPmem i hi]
      exact ⟨by simp [prefOfUtility, rank3, hxy.symm] <;> decide,
        by simp [prefOfUtility, rank3, hxy.symm] <;> decide⟩
    · intro i hi
      rw [hPout i hi]
      exact ⟨by simp [prefOfUtility, rank3, hxy.symm] <;> decide,
        by simp [prefOfUtility, rank3, hxy.symm] <;> decide⟩
  have hpareto : StrictPref (swf.aggregate P) y z :=
    h_pareto P y z (fun i => by
      by_cases hi : D i
      · rw [hPmem i hi]
        exact ⟨by simp [prefOfUtility, rank3, hxy.symm, hxz.symm, hyz.symm] <;> decide,
          by simp [prefOfUtility, rank3, hxy.symm, hxz.symm, hyz.symm] <;> decide⟩
      · rw [hPout i hi]
        exact ⟨by simp [prefOfUtility, rank3, hxy.symm, hxz.symm, hyz.symm] <;> decide,
          by simp [prefOfUtility, rank3, hxy.symm, hxz.symm, hyz.symm] <;> decide⟩)
  have hxzP : StrictPref (swf.aggregate P) x z :=
    ⟨(swf.aggregate P).trans x y z hdec.1 hpareto.1,
     fun hzx => hpareto.2 ((swf.aggregate P).trans z x y hzx hdec.1)⟩
  have h₁ : ∀ i, (P i).R x z ↔ (prefs i).R x z := by
    intro i
    by_cases hi : D i
    · rw [hPmem i hi]
      have hPtrue : (prefOfUtility (rank3 x y z 3 2 1)).R x z := by
        simp [prefOfUtility, rank3, hxz.symm, hyz.symm]
      have hT : (prefs i).R x z := (hzD i hi).1
      exact ⟨fun _ => hT, fun _ => hPtrue⟩
    · rw [hPout i hi]
      have hPfalse : ¬ (prefOfUtility (rank3 x y z 1 3 2)).R x z := by
        simp [prefOfUtility, rank3, hxz.symm, hyz.symm]
      have hT : ¬ (prefs i).R x z := (hzND i hi).2
      exact ⟨fun hc => absurd hc hPfalse, fun hc => absurd hc hT⟩
  have h₂ : ∀ i, (P i).R z x ↔ (prefs i).R z x := by
    intro i
    by_cases hi : D i
    · rw [hPmem i hi]
      have hPfalse : ¬ (prefOfUtility (rank3 x y z 3 2 1)).R z x := by
        simp [prefOfUtility, rank3, hxz.symm, hyz.symm]
      have hT : ¬ (prefs i).R z x := (hzD i hi).2
      exact ⟨fun hc => absurd hc hPfalse, fun hc => absurd hc hT⟩
    · rw [hPout i hi]
      have hPtrue : (prefOfUtility (rank3 x y z 1 3 2)).R z x := by
        simp [prefOfUtility, rank3, hxz.symm, hyz.symm]
      have hT : (prefs i).R z x := (hzND i hi).1
      exact ⟨fun _ => hT, fun _ => hPtrue⟩
  -- IIA est énoncée pour la paire ordonnée `(x, y)` : la comparaison inverse
  -- s'obtient en l'invoquant sur `(z, x)` avec les deux motifs échangés.
  have hiff₁ : (swf.aggregate P).R x z ↔ (swf.aggregate prefs).R x z :=
    h_iia P prefs x z h₁ h₂
  have hiff₂ : (swf.aggregate P).R z x ↔ (swf.aggregate prefs).R z x :=
    h_iia P prefs z x h₂ h₁
  exact ⟨hiff₁.mp hxzP.1, fun hzx => hxzP.2 (hiff₂.mpr hzx)⟩

/-- Expansion du champ, axe des agents : si `D` est décisive sur `(x, y)`, elle
l'est sur `(z, y)` pour tout `z` distinct de `x` et de `y`.

Preuve : sur le profil auxiliaire où `D` a `z ≻ x ≻ y` et où les autres ont
`y ≻ z ≻ x`, Pareto donne `z ≻s x`, la décision sur `(x, y)` donne `x ≻s y`,
donc `z ≻s y` ; les comparaisons `z` contre `y` y sont celles du profil visé,
donc IIA transporte le résultat. -/
theorem decisive_expand_left {I A : Type} [DecidableEq A]
    (swf : SocialWelfareFunction I A)
    (D : I → Prop) [DecidablePred D] (h_iia : IIA swf) (h_pareto : WeakPareto swf)
    {x y z : A} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h : Decisive swf D x y) : Decisive swf D z y := by
  intro prefs hzD hzND
  let P : I → Preference A :=
    fun i => if D i then prefOfUtility (rank3 z x y 3 2 1)
             else prefOfUtility (rank3 y z x 3 2 1)
  have hPmem : ∀ i, D i → P i = prefOfUtility (rank3 z x y 3 2 1) := by
    intro i hi; simp [P, hi]
  have hPout : ∀ i, ¬ D i → P i = prefOfUtility (rank3 y z x 3 2 1) := by
    intro i hi; simp [P, hi]
  have hdec : StrictPref (swf.aggregate P) x y := by
    apply h P
    · intro i hi
      rw [hPmem i hi]
      exact ⟨by simp [prefOfUtility, rank3, hxz, hyz, hxy.symm] <;> decide,
        by simp [prefOfUtility, rank3, hxz, hyz, hxy.symm] <;> decide⟩
    · intro i hi
      rw [hPout i hi]
      exact ⟨by simp [prefOfUtility, rank3, hxy, hxz] <;> decide,
        by simp [prefOfUtility, rank3, hxy, hxz] <;> decide⟩
  have hzxP : StrictPref (swf.aggregate P) z x :=
    h_pareto P z x (fun i => by
      by_cases hi : D i
      · rw [hPmem i hi]
        exact ⟨by simp [prefOfUtility, rank3, hxz] <;> decide,
          by simp [prefOfUtility, rank3, hxz] <;> decide⟩
      · rw [hPout i hi]
        exact ⟨by simp [prefOfUtility, rank3, hxy, hxz, hyz.symm] <;> decide,
          by simp [prefOfUtility, rank3, hxy, hxz, hyz.symm] <;> decide⟩)
  have hzyP : StrictPref (swf.aggregate P) z y :=
    ⟨(swf.aggregate P).trans z x y hzxP.1 hdec.1,
     fun hyz' => hdec.2 ((swf.aggregate P).trans y z x hyz' hzxP.1)⟩
  have h₁ : ∀ i, (P i).R z y ↔ (prefs i).R z y := by
    intro i
    by_cases hi : D i
    · rw [hPmem i hi]
      have hPtrue : (prefOfUtility (rank3 z x y 3 2 1)).R z y := by
        simp [prefOfUtility, rank3, hyz, hxy.symm]
      have hT : (prefs i).R z y := (hzD i hi).1
      exact ⟨fun _ => hT, fun _ => hPtrue⟩
    · rw [hPout i hi]
      have hPfalse : ¬ (prefOfUtility (rank3 y z x 3 2 1)).R z y := by
        simp [prefOfUtility, rank3, hyz.symm]
      have hT : ¬ (prefs i).R z y := (hzND i hi).2
      exact ⟨fun hc => absurd hc hPfalse, fun hc => absurd hc hT⟩
  have h₂ : ∀ i, (P i).R y z ↔ (prefs i).R y z := by
    intro i
    by_cases hi : D i
    · rw [hPmem i hi]
      have hPfalse : ¬ (prefOfUtility (rank3 z x y 3 2 1)).R y z := by
        simp [prefOfUtility, rank3, hyz, hxy.symm]
      have hT : ¬ (prefs i).R y z := (hzD i hi).2
      exact ⟨fun hc => absurd hc hPfalse, fun hc => absurd hc hT⟩
    · rw [hPout i hi]
      have hPtrue : (prefOfUtility (rank3 y z x 3 2 1)).R y z := by
        simp [prefOfUtility, rank3, hyz.symm]
      have hT : (prefs i).R y z := (hzND i hi).1
      exact ⟨fun _ => hT, fun _ => hPtrue⟩
  have hiff₁ : (swf.aggregate P).R z y ↔ (swf.aggregate prefs).R z y :=
    h_iia P prefs z y h₁ h₂
  have hiff₂ : (swf.aggregate P).R y z ↔ (swf.aggregate prefs).R y z :=
    h_iia P prefs y z h₂ h₁
  exact ⟨hiff₁.mp hzyP.1, fun hyz' => hzyP.2 (hiff₂.mpr hyz')⟩

/-- Symétrie du champ : si `D` est décisive sur `(x, y)`, elle l'est sur la
paire renversée `(y, x)`.

C'est le pas que l'étage 1 ne franchissait pas, et il n'est pas gratuit : `IIA`
est énoncée pour la **paire ordonnée**, donc le renversement ne se transporte
pas par une simple réécriture. La preuve traverse trois paires distinctes sur
un vivier de trois alternatives — `(x, y) → (x, z) → (y, z) → (y, x)` — chaque
étape étant une expansion du champ déjà établie. -/
theorem decisive_swap {I A : Type} [DecidableEq A]
    (swf : SocialWelfareFunction I A)
    (D : I → Prop) [DecidablePred D] (h_iia : IIA swf) (h_pareto : WeakPareto swf)
    {x y z : A} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h : Decisive swf D x y) : Decisive swf D y x := by
  have h1 : Decisive swf D x z :=
    decisive_expand_right swf D h_iia h_pareto hxy hxz hyz h
  have h2 : Decisive swf D y z :=
    decisive_expand_left swf D h_iia h_pareto hxz hxy hyz.symm h1
  exact decisive_expand_right swf D h_iia h_pareto hyz hxy.symm hxz.symm h2

/-- Fermeture du champ : sur trois alternatives deux à deux distinctes, une
coalition décisive sur une seule paire l'est sur les six paires ordonnées.

Les deux expansions de l'étage 1 ne couvrent que les paires qui gardent un
côté ; `decisive_swap` fournit les paires renversées, et la clôture en découle.
C'est l'hypothèse exacte dont la suite du port a besoin : pour réduire la
coalition décisive, il faut pouvoir lire une décision sur n'importe quelle
paire, pas seulement sur celle qui a servi à l'établir. -/
theorem decisive_field {I A : Type} [DecidableEq A]
    (swf : SocialWelfareFunction I A)
    (D : I → Prop) [DecidablePred D] (h_iia : IIA swf) (h_pareto : WeakPareto swf)
    {x y z : A} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h : Decisive swf D x y) :
    Decisive swf D x y ∧ Decisive swf D y x ∧ Decisive swf D x z ∧
    Decisive swf D z x ∧ Decisive swf D y z ∧ Decisive swf D z y := by
  have h1 : Decisive swf D x z :=
    decisive_expand_right swf D h_iia h_pareto hxy hxz hyz h
  have h2 : Decisive swf D z y :=
    decisive_expand_left swf D h_iia h_pareto hxy hxz hyz h
  have h3 : Decisive swf D z x :=
    decisive_expand_right swf D h_iia h_pareto hyz.symm hxz.symm hxy.symm h2
  have h4 : Decisive swf D y x :=
    decisive_swap swf D h_iia h_pareto hxy hxz hyz h
  have h5 : Decisive swf D y z :=
    decisive_expand_right swf D h_iia h_pareto hxy.symm hyz hxz h4
  exact ⟨h, h4, h1, h3, h5, h2⟩

/-- Contraction : une coalition décisive se scinde. Si `D` est décisive sur
`(x, y)` et se partage en deux parties disjointes `D₁` et `D₂` qui la
couvrent, alors l'une des deux est décisive — `D₁` sur `(x, z)`, `D₂` sur
`(z, y)`.

C'est la brique qui fait **décroître** les coalitions décisives : combinée à
la fermeture du champ (`decisive_field`), elle produit, sur un ensemble fini
d'agents, une coalition décisive minimale — et la minimalité en fera un
dictateur. Preuve (argument d'Arrow) : sur le profil où `D₁` a `x ≻ y ≻ z`,
`D₂` a `z ≻ x ≻ y` et les autres ont `y ≻ z ≻ x`, tous les membres de `D`
préfèrent `x` à `y`, donc la décision de `D` donne `x ≻s y`. Si `z ≳s x`,
alors `z ≳s y` par transitivité, et `z ≻s y` strictement (sinon
`y ≳s z ≳s x ≳s y` contredirait `x ≻s y`) ; seuls les membres de `D₂`
préfèrent `z` à `y` dans ce profil, donc IIA transporte la décision. Sinon
`x ≻s z` par complétude, et seuls les membres de `D₁` préfèrent `x` à `z` :
IIA transporte. Pareto n'intervient pas — la décision initiale vient de la
décisivité de `D` elle-même. -/
theorem decisive_split {I A : Type} [DecidableEq A]
    (swf : SocialWelfareFunction I A)
    (D D1 D2 : I → Prop) [DecidablePred D1] [DecidablePred D2]
    (h_iia : IIA swf)
    (h1in : ∀ i, D1 i → D i) (h2in : ∀ i, D2 i → D i)
    (hcover : ∀ i, D i → D1 i ∨ D2 i) (hdisj : ∀ i, ¬ (D1 i ∧ D2 i))
    {x y z : A} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h : Decisive swf D x y) :
    Decisive swf D1 x z ∨ Decisive swf D2 z y := by
  -- Profil auxiliaire : D₁ a x ≻ y ≻ z, D₂ a z ≻ x ≻ y, les autres y ≻ z ≻ x.
  let P : I → Preference A :=
    fun i => if D1 i then prefOfUtility (rank3 x y z 3 2 1)
             else if D2 i then prefOfUtility (rank3 z x y 3 2 1)
             else prefOfUtility (rank3 y z x 3 2 1)
  have hP1 : ∀ i, D1 i → P i = prefOfUtility (rank3 x y z 3 2 1) := by
    intro i hi; simp [P, hi]
  have hP2 : ∀ i, D2 i → P i = prefOfUtility (rank3 z x y 3 2 1) := by
    intro i hi
    have hnd1 : ¬ D1 i := fun hc => hdisj i ⟨hc, hi⟩
    simp [P, hnd1, hi]
  have hPout : ∀ i, ¬ D1 i → ¬ D2 i → P i = prefOfUtility (rank3 y z x 3 2 1) := by
    intro i h1 h2; simp [P, h1, h2]
  -- Tous les membres de D préfèrent x à y, tous les non-membres y à x :
  -- la décisivité de D sur (x, y) s'applique telle quelle au profil P.
  have hdec : StrictPref (swf.aggregate P) x y := by
    apply h P
    · intro i hi
      by_cases h1 : D1 i
      · rw [hP1 i h1]
        exact ⟨by simp [prefOfUtility, rank3, hxy.symm] <;> decide,
          by simp [prefOfUtility, rank3, hxy.symm] <;> decide⟩
      · have h2 : D2 i := ((hcover i hi).resolve_left h1)
        rw [hP2 i h2]
        exact ⟨by simp [prefOfUtility, rank3, hxz, hyz, hxy.symm] <;> decide,
          by simp [prefOfUtility, rank3, hxz, hyz, hxy.symm] <;> decide⟩
    · intro i hi
      have h1 : ¬ D1 i := fun hc => hi (h1in i hc)
      have h2 : ¬ D2 i := fun hc => hi (h2in i hc)
      rw [hPout i h1 h2]
      exact ⟨by simp [prefOfUtility, rank3, hxy, hxz] <;> decide,
        by simp [prefOfUtility, rank3, hxy, hxz] <;> decide⟩
  -- Le sens social sur (z, x) tranche laquelle des deux moitiés est décisive.
  by_cases hzx : (swf.aggregate P).R z x
  · right
    have hzy : StrictPref (swf.aggregate P) z y :=
      ⟨(swf.aggregate P).trans z x y hzx hdec.1,
       fun hyz' => hdec.2 ((swf.aggregate P).trans y z x hyz' hzx)⟩
    intro prefs hD2 hND2
    have h₁ : ∀ i, (P i).R z y ↔ (prefs i).R z y := by
      intro i
      by_cases hi : D2 i
      · rw [hP2 i hi]
        have hPtrue : (prefOfUtility (rank3 z x y 3 2 1)).R z y := by
          simp [prefOfUtility, rank3, hyz, hxy.symm]
        have hT : (prefs i).R z y := (hD2 i hi).1
        exact ⟨fun _ => hT, fun _ => hPtrue⟩
      · have hPfalse : ¬ (P i).R z y := by
          by_cases h1 : D1 i
          · rw [hP1 i h1]
            simp [prefOfUtility, rank3, hxy.symm, hxz.symm, hyz.symm]
          · rw [hPout i h1 hi]
            simp [prefOfUtility, rank3, hyz.symm]
        have hT : ¬ (prefs i).R z y := (hND2 i hi).2
        exact ⟨fun hc => absurd hc hPfalse, fun hc => absurd hc hT⟩
    have h₂ : ∀ i, (P i).R y z ↔ (prefs i).R y z := by
      intro i
      by_cases hi : D2 i
      · rw [hP2 i hi]
        have hPfalse : ¬ (prefOfUtility (rank3 z x y 3 2 1)).R y z := by
          simp [prefOfUtility, rank3, hyz, hxy.symm]
        have hT : ¬ (prefs i).R y z := (hD2 i hi).2
        exact ⟨fun hc => absurd hc hPfalse, fun hc => absurd hc hT⟩
      · have hPtrue : (P i).R y z := by
          by_cases h1 : D1 i
          · rw [hP1 i h1]
            simp [prefOfUtility, rank3, hxy.symm, hxz.symm, hyz.symm]
          · rw [hPout i h1 hi]
            simp [prefOfUtility, rank3, hyz.symm]
        have hT : (prefs i).R y z := (hND2 i hi).1
        exact ⟨fun _ => hT, fun _ => hPtrue⟩
    have hiff₁ : (swf.aggregate P).R z y ↔ (swf.aggregate prefs).R z y :=
      h_iia P prefs z y h₁ h₂
    have hiff₂ : (swf.aggregate P).R y z ↔ (swf.aggregate prefs).R y z :=
      h_iia P prefs y z h₂ h₁
    exact ⟨hiff₁.mp hzy.1, fun hyz' => hzy.2 (hiff₂.mpr hyz')⟩
  · left
    have hxzS : StrictPref (swf.aggregate P) x z :=
      ⟨((swf.aggregate P).complete x z).resolve_right hzx, hzx⟩
    intro prefs hD1 hND1
    have h₁ : ∀ i, (P i).R x z ↔ (prefs i).R x z := by
      intro i
      by_cases hi : D1 i
      · rw [hP1 i hi]
        have hPtrue : (prefOfUtility (rank3 x y z 3 2 1)).R x z := by
          simp [prefOfUtility, rank3, hxz.symm, hyz.symm]
        have hT : (prefs i).R x z := (hD1 i hi).1
        exact ⟨fun _ => hT, fun _ => hPtrue⟩
      · have hPfalse : ¬ (P i).R x z := by
          by_cases h2 : D2 i
          · rw [hP2 i h2]
            simp [prefOfUtility, rank3, hxz]
          · rw [hPout i hi h2]
            simp [prefOfUtility, rank3, hxy, hxz, hyz.symm]
        have hT : ¬ (prefs i).R x z := (hND1 i hi).2
        exact ⟨fun hc => absurd hc hPfalse, fun hc => absurd hc hT⟩
    have h₂ : ∀ i, (P i).R z x ↔ (prefs i).R z x := by
      intro i
      by_cases hi : D1 i
      · rw [hP1 i hi]
        have hPfalse : ¬ (prefOfUtility (rank3 x y z 3 2 1)).R z x := by
          simp [prefOfUtility, rank3, hxz.symm, hyz.symm]
        have hT : ¬ (prefs i).R z x := (hD1 i hi).2
        exact ⟨fun hc => absurd hc hPfalse, fun hc => absurd hc hT⟩
      · have hPtrue : (P i).R z x := by
          by_cases h2 : D2 i
          · rw [hP2 i h2]
            simp [prefOfUtility, rank3, hxz]
          · rw [hPout i hi h2]
            simp [prefOfUtility, rank3, hxy, hxz, hyz.symm]
        have hT : (prefs i).R z x := (hND1 i hi).1
        exact ⟨fun _ => hT, fun _ => hPtrue⟩
    have hiff₁ : (swf.aggregate P).R x z ↔ (swf.aggregate prefs).R x z :=
      h_iia P prefs x z h₁ h₂
    have hiff₂ : (swf.aggregate P).R z x ↔ (swf.aggregate prefs).R z x :=
      h_iia P prefs z x h₂ h₁
    exact ⟨hiff₁.mp hxzS.1, fun hzx' => hxzS.2 (hiff₂.mpr hzx')⟩
