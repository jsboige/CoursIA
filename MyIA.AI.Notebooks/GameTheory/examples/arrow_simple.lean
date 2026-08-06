/-
  Théorème d'impossibilité d'Arrow — Exemple simple
  =================================================

  Une démonstration simplifiée des concepts du théorème d'Arrow.
  En lien avec GameTheory-19-Lean-SocialChoice.ipynb

  Ce fichier présente la structure de base sans les preuves complètes.
  Pour la formalisation complète, voir lean_game_defs/SocialChoice.lean
-/

-- Définitions de base pour un cadre à 3 alternatives et 2 électeurs

-- Alternatives
inductive Alt where
  | a : Alt
  | b : Alt
  | c : Alt
deriving DecidableEq, Repr

-- Électeurs
inductive Voter where
  | v1 : Voter
  | v2 : Voter
deriving DecidableEq, Repr

-- Un ordre de préférence stricte (simplifié sous forme de fonction)
-- pref v x y signifie « l'électeur v préfère strictement x à y »
def StrictPref := Voter → Alt → Alt → Bool

-- Exemple : profil du paradoxe de Condorcet
-- Électeur 1 : a > b > c
-- Électeur 2 : b > c > a
def condorcetProfile : StrictPref := fun v x y =>
  match v, x, y with
  | Voter.v1, Alt.a, Alt.b => true
  | Voter.v1, Alt.b, Alt.c => true
  | Voter.v1, Alt.a, Alt.c => true
  | Voter.v2, Alt.b, Alt.c => true
  | Voter.v2, Alt.c, Alt.a => true
  | Voter.v2, Alt.b, Alt.a => true
  | _, _, _ => false

-- Règle de majorité (par paires)
def majorityPrefers (prefs : StrictPref) (x y : Alt) : Bool :=
  let v1_prefers := prefs Voter.v1 x y
  let v2_prefers := prefs Voter.v2 x y
  v1_prefers || v2_prefers  -- Au moins un préfère (départage simplifié)

-- Vérifier la présence de cycles dans les préférences de majorité
def hasCycle (prefs : StrictPref) : Bool :=
  majorityPrefers prefs Alt.a Alt.b &&
  majorityPrefers prefs Alt.b Alt.c &&
  majorityPrefers prefs Alt.c Alt.a

-- Vérifier le paradoxe de Condorcet
#eval hasCycle condorcetProfile  -- Doit valoir true !

-- Ceci illustre pourquoi le théorème d'Arrow importe :
-- même avec seulement 2 électeurs et 3 alternatives,
-- la règle de majorité peut produire des cycles (préférence sociale intransitive)

-- Une fonction de bien-être social (SWF)
structure SWF where
  -- Associe les préférences individuelles à une préférence sociale
  aggregate : StrictPref → (Alt → Alt → Bool)

-- Dictature : la préférence de l'électeur 1 devient la préférence sociale
def dictatorshipV1 : SWF := {
  aggregate := fun prefs x y => prefs Voter.v1 x y
}

-- Vérifier si une SWF satisfait le critère de Pareto
def satisfiesPareto (swf : SWF) (prefs : StrictPref) : Prop :=
  ∀ x y, (prefs Voter.v1 x y ∧ prefs Voter.v2 x y) →
         swf.aggregate prefs x y = true

-- Une dictature satisfait trivialement Pareto lorsque le dictateur est d'accord,
-- mais viole la non-dictature par définition

-- Théorème d'Arrow (énoncé informel) :
-- il n'existe pas de SWF avec ≥3 alternatives qui satisfait à la fois :
-- 1. Domaine non restreint (fonctionne pour tous les profils de préférence)
-- 2. Efficacité au sens de Pareto
-- 3. Indépendance des alternatives non pertinentes (IANP)
-- 4. Non-dictature

-- La preuve est complexe et exige un traitement soigneux de tous les cas.
-- Voir SocialChoice.lean pour le cadre formel.

#check dictatorshipV1
#check condorcetProfile
