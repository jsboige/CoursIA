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

/-!
**Énoncé.** Il n'existe pas de fonction de bien-être social sur au moins trois
alternatives qui satisfasse simultanément :

1. Pareto faible ;
2. Indépendance des alternatives non pertinentes (IIA) ;
3. non-dictature.

Énoncé avec des types `Fin n` explicites plutôt qu'un `Fintype` générique pour
éviter la dépendance Mathlib : le contenu mathématique du théorème est identique.

La preuve est donnée en fin de fichier (section « Étape 4b ») ; la déclaration
`axiom arrow_impossibility` qui portait cet énoncé sans preuve a été retirée
(#23022).
-/

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

/-!
## Étape 4a : champ global et dictateur

Avant-dernier étage de la réduction de l'axiome `arrow_impossibility` (#23022).
Il reste, après lui, à extraire un singleton décisif par contraction itérée
(l'étape 4b, qui demande une mesure de cardinalité sur `Fin nI`).

- `decisive_global` : une coalition décisive sur une seule paire d'alternatives
  distinctes l'est sur toute paire. Les deux lemmes d'expansion déplacent chaque
  coordonnée indépendamment ; seul le rabattement de la première coordonnée sur
  `y` exige une troisième alternative hors de `{x, y}` (hypothèse `hcard`,
  satisfaite dès que l'ensemble compte au moins trois éléments).
- `empty_not_decisive` : aucune coalition vide n'est décisive sous Pareto — le
  profil unanime `y ≻ x` met la conclusion en contradiction directe avec
  Pareto. C'est l'ancre qui interdira à la contraction d'aboutir à l'ensemble
  vide.
- `decisive_singleton_dictator` : un singleton décisif sur toute paire est un
  dictateur au sens exact de `NonDictatorial`. Sur le profil auxiliaire où `d`
  place `z` strictement entre `x` et `y` et où chaque autre agent garde ses
  rapports `x`/`y` exacts avec `z` envoyé en dernière position (`zLast`), Pareto
  donne `x ≻ₛ z` (unanimité) et la décisivité donne `z ≻ₛ y` ; la transitivité
  produit `x ≻ₛ y`, que l'IIA transporte vers le profil d'origine, accord
  individuel par individu. La construction `zLast` préserve les deux sens de la
  relation `x`/`y` sans aucun raisonnement par cas sur les préférences d'autrui,
  d'où aucun recours à `Classical` et donc aucun axiome au-delà de `propext` et
  `Quot.sound`.
-/

/-- Préférence où `z` passe strictement en dernière position : les rapports
entre alternatives distinctes de `z` sont exactement ceux de `p`, et toute
alternative distincte de `z` est strictement préférée à `z`. -/
def zLast {A : Type} (p : Preference A) (z : A) : Preference A where
  R := fun a b => (a = z ∧ b = z) ∨ (b = z ∧ a ≠ z) ∨ (a ≠ z ∧ b ≠ z ∧ p.R a b)
  complete := by
    intro a b
    by_cases haz : a = z
    · by_cases hbz : b = z
      · exact Or.inl (Or.inl ⟨haz, hbz⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨haz, hbz⟩))
    · by_cases hbz : b = z
      · exact Or.inl (Or.inr (Or.inl ⟨hbz, haz⟩))
      · rcases p.complete a b with h | h
        · exact Or.inl (Or.inr (Or.inr ⟨haz, hbz, h⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨hbz, haz, h⟩))
  trans := by
    intro a b c hab hbc
    rcases hab with ⟨haz, hbz⟩ | ⟨hbz, haz⟩ | ⟨haz, hbz, hpab⟩
    · rcases hbc with ⟨_, hcz⟩ | ⟨hcz, _⟩ | ⟨hnb, _, _⟩
      · exact Or.inl ⟨haz, hcz⟩
      · exact Or.inl ⟨haz, hcz⟩
      · exact absurd hbz hnb
    · rcases hbc with ⟨_, hcz⟩ | ⟨hcz, _⟩ | ⟨hnb, _, _⟩
      · exact Or.inr (Or.inl ⟨hcz, haz⟩)
      · exact Or.inr (Or.inl ⟨hcz, haz⟩)
      · exact absurd hbz hnb
    · rcases hbc with ⟨hbz', _⟩ | ⟨hcz, _⟩ | ⟨_, hcz, hpbc⟩
      · exact absurd hbz' hbz
      · exact Or.inr (Or.inl ⟨hcz, haz⟩)
      · exact Or.inr (Or.inr ⟨haz, hcz, p.trans a b c hpab hpbc⟩)

/-- Aucune coalition vide n'est décisive dès que Pareto tient : sur le profil
unanime `y ≻ x`, la prémisse « membres » est vide et la prémisse « non-membres »
est satisfaite par tout le monde, donc la conclusion imposerait `x ≻ₛ y`
contre le verdict unanime de Pareto. -/
theorem empty_not_decisive {I A : Type} [DecidableEq A]
    (swf : SocialWelfareFunction I A) (h_pareto : WeakPareto swf)
    {x y : A} (hxy : x ≠ y)
    (h : Decisive swf (fun _ => False) x y) : False := by
  let P : I → Preference A := fun _ => prefOfUtility (rank3 y x y 2 1 0)
  have hyx : ∀ i, StrictPref (P i) y x := fun i =>
    ⟨by simp [P, prefOfUtility, rank3, hxy],
     by simp [P, prefOfUtility, rank3, hxy]⟩
  have hsoc : StrictPref (swf.aggregate P) x y :=
    h P (fun i hi => False.elim hi) (fun i _ => hyx i)
  have hpar : StrictPref (swf.aggregate P) y x :=
    h_pareto P y x hyx
  exact hsoc.2 hpar.1

/-- Une coalition décisive sur une seule paire d'alternatives distinctes l'est
sur toute paire : les lemmes d'expansion déplacent chaque coordonnée
indépendamment, et le seul cas qui résiste (rabattre la première coordonnée sur
`y`) se traite via une troisième alternative `w` hors de `{x, y}`. -/
theorem decisive_global {I A : Type} [DecidableEq A]
    (swf : SocialWelfareFunction I A)
    (D : I → Prop) [DecidablePred D]
    (h_iia : IIA swf) (h_pareto : WeakPareto swf)
    {x y : A} (hxy : x ≠ y)
    (hcard : ∃ w : A, w ≠ x ∧ w ≠ y)
    (h : Decisive swf D x y) :
    ∀ a b : A, a ≠ b → Decisive swf D a b := by
  intro a b hab
  by_cases hax : a = x
  · by_cases hby : b = y
    · rw [hax, hby]; exact h
    · rw [hax]
      exact decisive_expand_right swf D h_iia h_pareto hxy
        (fun hc => hab (hax.trans hc)) (fun hc => hby hc.symm) h
  · by_cases hay : a = y
    · obtain ⟨w, hwx, hwy⟩ := hcard
      have hxw : Decisive swf D x w :=
        decisive_expand_right swf D h_iia h_pareto hxy
          (fun hc => hwx hc.symm) (fun hc => hwy hc.symm) h
      have hyw : Decisive swf D y w :=
        decisive_expand_left swf D h_iia h_pareto
          (fun hc => hwx hc.symm) hxy hwy hxw
      by_cases hbw : b = w
      · rw [hay, hbw]; exact hyw
      · rw [hay]
        exact decisive_expand_right swf D h_iia h_pareto
          (fun hc => hwy hc.symm) (fun hc => hab (hay.trans hc))
          (fun hc => hbw hc.symm) hyw
    · have hay' : Decisive swf D a y :=
        decisive_expand_left swf D h_iia h_pareto hxy
          (fun hc => hax hc.symm) (fun hc => hay hc.symm) h
      by_cases hby : b = y
      · rw [hby]; exact hay'
      · exact decisive_expand_right swf D h_iia h_pareto hay hab
          (fun hc => hby hc.symm) hay'

/-- Un singleton décisif sur toute paire est un dictateur au sens de
`NonDictatorial` : chaque préférence stricte du dictateur devient la préférence
stricte de la société, sur tout profil. -/
theorem decisive_singleton_dictator {I A : Type} [DecidableEq I] [DecidableEq A]
    (swf : SocialWelfareFunction I A)
    (h_iia : IIA swf) (h_pareto : WeakPareto swf)
    (d : I) (hdec : ∀ x y : A, x ≠ y → Decisive swf (fun i => i = d) x y)
    (prefs : I → Preference A) {x y z : A}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hd : StrictPref (prefs d) x y) :
    StrictPref (swf.aggregate prefs) x y := by
  let P : I → Preference A :=
    fun i => if i = d then prefOfUtility (rank3 x z y 3 2 1) else zLast (prefs i) z
  have hPd : ∀ i, i = d → P i = prefOfUtility (rank3 x z y 3 2 1) := by
    intro i hi; simp [P, hi]
  have hPo : ∀ i, i ≠ d → P i = zLast (prefs i) z := by
    intro i hi; simp [P, hi]
  -- Jambe Pareto : unanimité stricte `x ≻ z` sur le profil auxiliaire.
  have hPxz : StrictPref (swf.aggregate P) x z :=
    h_pareto P x z (fun i => by
      by_cases hid : i = d
      · rw [hPd i hid]
        exact ⟨by simp [prefOfUtility, rank3, hxz.symm],
               by simp [prefOfUtility, rank3, hxz.symm]⟩
      · rw [hPo i hid]
        exact ⟨Or.inr (Or.inl ⟨rfl, hxz⟩), by simp [zLast, hxz]⟩)
  -- Jambe décisivité : `z ≻ y` -- le dictateur a `z ≻ y`, tous les autres ont
  -- `y ≻ z` strictement puisque `z` est leur dernier choix.
  have hPzy : StrictPref (swf.aggregate P) z y :=
    hdec z y (fun hc => hyz hc.symm) P
      (fun i hid => by
        rw [hPd i hid]
        exact ⟨by simp [prefOfUtility, rank3, hyz, hxy.symm, hxz.symm],
               by simp [prefOfUtility, rank3, hyz, hxy.symm, hxz.symm]⟩)
      (fun i hid => by
        rw [hPo i hid]
        exact ⟨Or.inr (Or.inl ⟨rfl, hyz⟩), by simp [zLast, hyz]⟩)
  -- Accord individuel sur les rapports `x`/`y` : construction `zLast`.
  have h₁ : ∀ i, (P i).R x y ↔ (prefs i).R x y := by
    intro i
    by_cases hid : i = d
    · rw [hPd i hid, hid]
      exact ⟨fun _ => hd.1,
             fun _ => by simp [prefOfUtility, rank3, hyz, hxy.symm]⟩
    · rw [hPo i hid]
      constructor
      · intro hc
        rcases hc with ⟨_, hyz1⟩ | ⟨hyz1, _⟩ | ⟨_, _, hp⟩
        · exact absurd hyz1 hyz
        · exact absurd hyz1 hyz
        · exact hp
      · intro hp
        exact Or.inr (Or.inr ⟨hxz, hyz, hp⟩)
  have h₂ : ∀ i, (P i).R y x ↔ (prefs i).R y x := by
    intro i
    by_cases hid : i = d
    · rw [hPd i hid, hid]
      have hPF : ¬ (prefOfUtility (rank3 x z y 3 2 1)).R y x := by
        simp [prefOfUtility, rank3, hyz, hxy.symm]
      exact ⟨fun hc => absurd hc hPF, fun hc => absurd hc hd.2⟩
    · rw [hPo i hid]
      constructor
      · intro hc
        rcases hc with ⟨_, hxz1⟩ | ⟨hxz1, _⟩ | ⟨_, _, hp⟩
        · exact absurd hxz1 hxz
        · exact absurd hxz1 hxz
        · exact hp
      · intro hp
        exact Or.inr (Or.inr ⟨hyz, hxz, hp⟩)
  -- Transitivité sociale puis transport IIA vers le profil d'origine.
  have hPxy : StrictPref (swf.aggregate P) x y :=
    ⟨(swf.aggregate P).trans x z y hPxz.1 hPzy.1,
     fun hyx => hPzy.2 ((swf.aggregate P).trans y x z hyx hPxz.1)⟩
  have hiff₁ : (swf.aggregate P).R x y ↔ (swf.aggregate prefs).R x y :=
    h_iia P prefs x y h₁ h₂
  have hiff₂ : (swf.aggregate P).R y x ↔ (swf.aggregate prefs).R y x :=
    h_iia P prefs y x h₂ h₁
  exact ⟨hiff₁.mp hPxy.1, fun hyx => hPxy.2 (hiff₂.mpr hyx)⟩

/-!
## Étape 4b : extraction du dictateur

Dernier étage du port direct (#23022) : il extrait un dictateur d'une coalition
décisive, ce qui permet de **prouver** `arrow_impossibility` au lieu de
l'énoncer.

La machinerie de l'étage 4a suffit, **sans aucune mesure de cardinalité** — donc
sans `Finset`, et sans quitter le Lean core. Plutôt que de chercher un minimum
parmi toutes les coalitions décisives (ce qui demanderait de les compter), la
preuve scinde une famille **explicite** de coalitions : la suite des « queues »
`{i | m ≤ i}`.

- La queue vide n'est jamais décisive (`empty_not_decisive`), donc la descente ne
  peut pas s'éteindre sans avoir trouvé de dictateur.
- `decisive_split` sur la queue `m` offre deux issues. Soit le singleton `{m}`
  est décisif sur la paire `(x₀, w)`, et `decisive_global` en fait un dictateur
  (`decisive_singleton_dictator`). Soit la queue `m + 1` est décisive sur
  `(w, y₀)`, et la descente continue d'un cran.

L'induction porte sur `nI - m`, qui décroît strictement à chaque cran : aucune
mesure de cardinalité n'est nécessaire, et `Finset` reste hors du lake.

Clôture axiomatique mesurée (`#print axioms`) : `propext`, `Quot.sound`, et
`Classical.choice` **hérité** de `decisive_split`. Ce lemme tranche la
préférence sociale sur une paire par `by_cases`, ce qui tire
`Classical.propDecidable` sur une proposition arbitraire — il ne reçoit aucune
instance de décidabilité sur la relation sociale. Cet étage-ci n'introduit donc
aucun axiome nouveau ; il n'en supprime pas non plus.
-/

/-- L'individu `d` est un dictateur : chacune de ses préférences strictes devient
la préférence stricte de la société, sur tout profil et toute paire. C'est
exactement le prédicat dont `NonDictatorial` nie l'existence. -/
def Dictator {I A : Type} (swf : SocialWelfareFunction I A) (d : I) : Prop :=
  ∀ prefs : I → Preference A, ∀ x y : A,
    StrictPref (prefs d) x y → StrictPref (swf.aggregate prefs) x y

/-- Deux coalitions extensionnellement égales ont la même décisivité. -/
theorem decisive_congr {I A : Type} (swf : SocialWelfareFunction I A)
    {D D' : I → Prop} {x y : A} (h : ∀ i, D i ↔ D' i)
    (hdec : Decisive swf D x y) : Decisive swf D' x y := by
  intro prefs hD hND
  exact hdec prefs (fun i hi => hD i ((h i).mp hi))
    (fun i hi => hND i (fun hc => hi ((h i).mpr hc)))

/-- La coalition des agents dont l'indice vaut au moins `m`. -/
def tailCoal {n : Nat} (m : Nat) : Fin n → Prop := fun i => m ≤ i.val

/-- Dès que l'ensemble compte au moins trois alternatives, tout couple
d'alternatives laisse une alternative distincte des deux. Le témoin est cherché
parmi `0`, `1` et `2` : deux valeurs y suffisent au plus. -/
theorem exists_third {n : Nat} (h : n ≥ 3) (x y : Fin n) :
    ∃ z : Fin n, z ≠ x ∧ z ≠ y := by
  by_cases h0 : (0 : Nat) = x.val ∨ 0 = y.val
  · by_cases h1 : (1 : Nat) = x.val ∨ 1 = y.val
    · refine ⟨⟨2, by omega⟩, ?_, ?_⟩
      · intro hc
        have hv : (2 : Nat) = x.val := congrArg Fin.val hc
        rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> omega
      · intro hc
        have hv : (2 : Nat) = y.val := congrArg Fin.val hc
        rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> omega
    · have h1x : (1 : Nat) ≠ x.val := fun e => h1 (Or.inl e)
      have h1y : (1 : Nat) ≠ y.val := fun e => h1 (Or.inr e)
      exact ⟨⟨1, by omega⟩, fun hc => h1x (congrArg Fin.val hc),
        fun hc => h1y (congrArg Fin.val hc)⟩
  · have h0x : (0 : Nat) ≠ x.val := fun e => h0 (Or.inl e)
    have h0y : (0 : Nat) ≠ y.val := fun e => h0 (Or.inr e)
    exact ⟨⟨0, by omega⟩, fun hc => h0x (congrArg Fin.val hc),
      fun hc => h0y (congrArg Fin.val hc)⟩

/-- Sous Pareto et IIA, une coalition décisive sur une paire d'alternatives
distinctes contient un dictateur.

La descente porte sur `nI - m` : à chaque cran, `decisive_split` détache l'agent
`m` de la queue, et la queue vide est exclue par `empty_not_decisive`. -/
theorem exists_dictator_of_decisive {nI nA : Nat} (hA : nA ≥ 3)
    (swf : SocialWelfareFunction (Fin nI) (Fin nA))
    (h_iia : IIA swf) (h_pareto : WeakPareto swf)
    {x0 y0 w : Fin nA} (hx0y0 : x0 ≠ y0) (hx0w : x0 ≠ w) (hy0w : y0 ≠ w) :
    ∀ (k : Nat) (m : Nat), m + k = nI →
      Decisive swf (tailCoal m) x0 y0 → ∃ d : Fin nI, Dictator swf d := by
  intro k
  induction k with
  | zero =>
      intro m hm hdec
      have hemp : Decisive swf (fun _ => False) x0 y0 :=
        decisive_congr swf (D := tailCoal m) (D' := fun _ => False)
          (fun i => ⟨fun hi => by
            have hi' : m ≤ i.val := hi
            omega, fun hf => False.elim hf⟩) hdec
      exact False.elim (empty_not_decisive swf h_pareto hx0y0 hemp)
  | succ k ih =>
      intro m hm hdec
      have hmn : m < nI := by omega
      have hsplit :
          Decisive swf (fun i : Fin nI => i = ⟨m, hmn⟩) x0 w ∨
            Decisive swf (fun i : Fin nI => m + 1 ≤ i.val) w y0 :=
        decisive_split swf (tailCoal m) (fun i : Fin nI => i = ⟨m, hmn⟩)
          (fun i : Fin nI => m + 1 ≤ i.val) h_iia
          (fun i hi => by rw [hi]; exact Nat.le_refl m)
          (fun i hi => Nat.le_of_succ_le hi)
          (fun i hi => by
            have hi' : m ≤ i.val := hi
            by_cases hc : i.val = m
            · exact Or.inl (Fin.ext hc)
            · exact Or.inr (by omega))
          (fun i => by
            rintro ⟨h1, h2⟩
            have h2' : m + 1 ≤ i.val := h2
            have h1' : i.val = m := by rw [h1]
            omega)
          hx0y0 hx0w hy0w hdec
      rcases hsplit with hsingle | htail
      · have hall : ∀ a b : Fin nA, a ≠ b →
            Decisive swf (fun i : Fin nI => i = ⟨m, hmn⟩) a b :=
          decisive_global (x := x0) (y := w) swf
            (fun i : Fin nI => i = ⟨m, hmn⟩) h_iia h_pareto
            hx0w ⟨y0, hx0y0.symm, hy0w⟩ hsingle
        refine ⟨⟨m, hmn⟩, ?_⟩
        intro prefs a b hab
        have hne : a ≠ b := by
          intro heq
          subst heq
          exact hab.2 hab.1
        obtain ⟨z, hzx, hzy⟩ := exists_third hA a b
        exact decisive_singleton_dictator swf h_iia h_pareto ⟨m, hmn⟩ hall prefs
          hne hzx.symm hzy.symm hab
      · have hall : ∀ a b : Fin nA, a ≠ b →
            Decisive swf (fun i : Fin nI => m + 1 ≤ i.val) a b :=
          decisive_global (x := w) (y := y0) swf
            (fun i : Fin nI => m + 1 ≤ i.val) h_iia h_pareto
            hy0w.symm ⟨x0, hx0w, hx0y0⟩ htail
        exact ih (m + 1) (by omega) (hall x0 y0 hx0y0)

/-- **Théorème d'impossibilité d'Arrow.** Il n'existe pas de fonction de
bien-être social sur au moins trois alternatives qui satisfasse simultanément
Pareto faible, indépendance des alternatives non pertinentes et non-dictature.

Le théorème est ici **prouvé** : le profil unanime rend la coalition totale
décisive, et `exists_dictator_of_decisive` en extrait un dictateur dès que
l'ensemble des alternatives compte trois éléments.

L'hypothèse `nI ≥ 2` est celle de l'énoncé historique, conservée pour la
fidélité à la littérature ; la preuve ci-dessous vaut pour tout `nI`, d'où le
nom `_hI` du paramètre. -/
theorem arrow_impossibility {nI nA : Nat}
    (_hI : nI ≥ 2)
    (hA : nA ≥ 3)
    (swf : SocialWelfareFunction (Fin nI) (Fin nA))
    (h_pareto : WeakPareto swf)
    (h_iia : IIA swf) :
    ¬NonDictatorial swf := by
  intro hnd
  let x0 : Fin nA := ⟨0, by omega⟩
  let y0 : Fin nA := ⟨1, by omega⟩
  let w : Fin nA := ⟨2, by omega⟩
  have hx0y0 : x0 ≠ y0 := by
    intro h
    have hv : x0.val = y0.val := congrArg Fin.val h
    have h0v : x0.val = 0 := rfl
    have h1v : y0.val = 1 := rfl
    omega
  have hx0w : x0 ≠ w := by
    intro h
    have hv : x0.val = w.val := congrArg Fin.val h
    have h0v : x0.val = 0 := rfl
    have hwv : w.val = 2 := rfl
    omega
  have hy0w : y0 ≠ w := by
    intro h
    have hv : y0.val = w.val := congrArg Fin.val h
    have h1v : y0.val = 1 := rfl
    have hwv : w.val = 2 := rfl
    omega
  have hunan : Decisive swf (fun _ => True) x0 y0 := decisive_unanimous swf h_pareto
  have h0 : Decisive swf (tailCoal 0) x0 y0 :=
    decisive_congr swf (D := fun _ => True) (D' := tailCoal 0)
      (fun i => ⟨fun _ => Nat.zero_le i.val, fun _ => trivial⟩) hunan
  obtain ⟨d, hd⟩ := exists_dictator_of_decisive hA swf h_iia h_pareto
    hx0y0 hx0w hy0w nI 0 (by omega) h0
  exact hnd ⟨d, hd⟩
