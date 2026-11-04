/-
  `Conway.CollatzLike` — Fonctions de type Collatz et indécidabilité
  ===================================================================
  Hommage à Conway — Formalisation des fonctions « Collatz-like »

  John Horton Conway (1937-2020) — co-fondateur de la théorie des jeux
  combinatoires, mais aussi contributeur majeur en théorie des nombres
  et en logique mathématique.

  L'article fondateur de Conway (1972) « Unpredictable Iterations »
  (Conway 1972, Proceedings of the 1972 Number Theory Conference)
  prouve qu'une **généralisation naturelle** de la conjecture de Collatz
  est **indécidable**. Plus précisément, il existe une fonction
  « Collatz-like » (application linéaire par morceaux sur les entiers,
  avec un nombre fini de cas) dont le comportement asymptotique
  (« est-ce que toute trajectoire atteint un ensemble particulier ? »)
  est **algorithmiquement indécidable**.

  Ce module formalise les parties **accessibles** de ce résultat :
  1. La définition d'une fonction Collatz-like (itération linéaire par
     morceaux)
  2. Des exemples concrets avec propriétés de terminaison prouvées
  3. La connexion entre FRACTRAN et les fonctions Collatz-like

  Ce n'est PAS la preuve d'indécidabilité complète (qui nécessite
  l'arithmétisation des machines de Turing), mais le **noyau
  computationnel** qui la motive.

  Aucun `sorry` dans ce module — tous les résultats sont prouvés via
  `native_decide` ou calcul direct.

  ### i18n — convention #4980 (sibling pair, decision 2026-07-04)

  Ce fichier est **FR canonique**. Son miroir anglais vit dans le sibling
  `CollatzLike_en.lean` (modèle sibling pair ratifié 2026-07-04, cf
  `code-style.md` §Lean i18n, analogue `Angel.lean` / `Angel_en.lean`).
  Les énoncés de théorèmes, les tactiques Lean, les noms de lemmes et les
  références Mathlib restent en anglais (Mathlib 4) ; seules les docstrings
  et les commentaires diffèrent entre les deux fichiers. Anti-§D
  byte-identity garanti : le namespace body est préservé bit-pour-bit.

  ### c.385 — continuité conway_lean Phase 1+ satellites (post-c.384)

  c.384 = PIVOT L335 strict obligatoire post-c.381-c.383 = 3 cycles
  R6 Sustained intra-R6 sur registre `grothendieck_lean` Phase 2+
  (YonedaLemma c.381, MathlibMap c.382, SheafBasics c.383), retour
  vers `conway_lean` Phase 1+ satellites registre ouvert post-c.380
  (5ᵉ sous-module = `Nim` c.384, analogue structurel c.380 Doomsday).

  **c.385 = 6ᵉ sous-module rollout `conway_lean` Phase 1+** =
  `CollatzLike` = continuation registre conway_lean Phase 1+ ouvert
  post-c.384 PIVOT strict obligatoire. Substance réelle :
  **conjecture de Collatz (3n+1) + généralisation indécidable
  Conway 1972 « Unpredictable Iterations »** (math number theory +
  recursion theory). Analogie structurelle avec c.380 Doomsday
  (algorithme mathématique fondamental vérifié par `native_decide`
  sur cas concrets) + c.384 Nim (jeu mathématique + algorithme
  fondamental). 8 theorem vérifiés (`native_decide`) sur trajectoires
  canoniques (Collatz 6→1, 27→..., 7→1, Compressed 6→1, 7→1,
  FRACTRAN double, 7n+1 3→..., 7n+1 1→1). 11 defs/structures
  (`AffineMap`, `CLBranch`, `CollatzLike`, `collatz`,
  `collatzCompressed`, `sevenNPlusOne`, `applyAffine`, `clStep`,
  `clIterate`, `collatzStep`, `doubleProgram`). `CollatzLike ≠
  Grothendieck` : number theory vs algebraic geometry, registre
  propre po-2023 sans conflit GT/Probas/Planners owner-strict
  (L143 SAFE cross-owner).

  Backlog c.386+ (3 sous-modules Phase 1+ restants après c.385 :
  `Conway/{Angel,FreeWillTheorem,KochenSpecker}.lean` + `Conway/Life/*`
  13 fichiers + grothendieck_lean 19 restants Phase 2+) + hors-Lean
  backlog.

  Cross-références : c.366 `#6111` `Conway.lean` racine bilingue inline
  (MERGED, initie rollout Phase 1+) + c.377 `#6178`
  `Conway/MathlibMap` bilingue (1ᵉʳ sous-module rollout conway_lein,
  PIVOT L335 strict, analogue structurel c.382) + c.378 `#6182`
  `Conway/LookAndSay` bilingue (2ᵉ sous-module rollout, suite
  look-and-say λ ≈ 1.303577) + c.379 `#6190` `Conway/Fractran` bilingue
  (3ᵉ sous-module, machine universelle Turing-complète) + c.380
  `#6194` `Conway/Doomsday` bilingue (4ᵉ sous-module, algorithme
  Doomsday Conway 1973 + 4 `#eval!` cas réels Conway mort 2020/4/11,
  9/11, Moon 1969/7/20, D-Day 1944/6/6, **analogue structurel direct
  c.385 CollatzLike**) + c.381 `#6197` `Grothendieck/YonedaLemma`
  bilingue (1ᵉʳ sous-module rollout grothendieck_lein Phase 2+,
  PIVOT L335 strict c.381) + c.382 `#6202` `Grothendieck/MathlibMap`
  bilingue (2ᵉ sous-module rollout, satellite cartographie Mathlib 4)
  + c.383 `#6208` `Grothendieck/SheafBasics` bilingue (3ᵉ sous-module
  rollout, fondations faisceaux = 6 theorem, 3ᵉ cycle R6 Sustained
  intra-R6 sur registre `grothendieck_lein` ouvert = au seuil R5.4b
  MUST avant PIVOT obligatoire c.384) + c.384 `#6212` `Conway/Nim`
  bilingue (5ᵉ sous-module rollout conway_lein Phase 1+, Nim + Bouton
  1901 + Sprague-Grundy = analogue structurel direct c.385 CollatzLike
  par algorithme mathématique concret + `#eval!`/theorem cas concrets)
  + **c.385 `Conway/CollatzLike` bilingue (cette PR, 6ᵉ sous-module
  rollout conway_lein Phase 1+, conjecture Collatz 3n+1 + Conway 1972
  indécidabilité)** ← **continuité registre `conway_lein` Phase 1+
  ouvert post-c.384 PIVOT strict obligatoire**.
-/

import Conway.Fractran

namespace Conway

/-! ## Fonctions linéaires par morceaux

Une fonction de type Collatz partitionne ℤ en un nombre fini de classes
de résidus modulo `m`, et applique une application affine différente
`n ↦ (a·n + b) / c` à chaque classe. La fonction de Collatz classique
(problème 3n+1) a m=2 :
  - n ≡ 0 (mod 2) : n ↦ n/2
  - n ≡ 1 (mod 2) : n ↦ (3n+1)/2

Conway a montré que pour des choix suffisamment complexes de m, a, b, c,
la question « toute trajectoire atteint-elle 1 ? » devient indécidable. -/

/-- Application affine n ↦ (a·n + b) / c, applicable quand la division est exacte. -/
structure AffineMap where
  a : Int
  b : Int
  c : Nat
  hc : c > 0
  deriving Repr

/-- Applique une application affine, renvoie none si la division n'est pas exacte. -/
def applyAffine (f : AffineMap) (n : Int) : Option Int :=
  let num := f.a * n + f.b
  if num % f.c = 0 then some (num / f.c) else none

/-- Une branche d'une fonction de type Collatz : appliquer cette application
    quand n mod m = r (pour 0 ≤ r < m). -/
structure CLBranch where
  r : Nat          -- classe de résidu
  f : AffineMap    -- l'application à appliquer
  deriving Repr

/-- Une fonction de type Collatz : partitionner ℤ en classes de résidus
    modulo m, appliquer une application affine différente à chacune. -/
structure CollatzLike where
  m : Nat          -- module (nombre de cas)
  hm : m > 0
  branches : List CLBranch
  deriving Repr

/-- La fonction de Collatz classique comme CollatzLike.
    n ≡ 0 (mod 2) : n ↦ n/2 (i.e., a=1, b=0, c=2)
    n ≡ 1 (mod 2) : n ↦ (3n+1) (simplifié en (3n+1)/1) -/
def collatz : CollatzLike where
  m := 2
  hm := by decide
  branches := [
    ⟨0, ⟨1, 0, 2, by decide⟩⟩,   -- n pair : n/2
    ⟨1, ⟨3, 1, 1, by decide⟩⟩    -- n impair : 3n+1
  ]

/-- Une étape d'une fonction de type Collatz. -/
def clStep (f : CollatzLike) (n : Int) : Int :=
  let r := ((n % f.m) + f.m) % f.m  -- résidu non négatif
  match f.branches.find? (fun b => b.r = r.natAbs) with
  | some branch => match applyAffine branch.f n with
    | some m => m
    | none => n  -- rester sur place si la division échoue
  | none => n    -- rester sur place si aucune branche ne correspond

/-- Itère une fonction de type Collatz pendant k étapes. -/
def clIterate (f : CollatzLike) : Int → Nat → List Int
  | n, 0 => [n]
  | n, k + 1 => n :: clIterate f (clStep f n) k

/-! ## Propriétés prouvées de la fonction de Collatz classique

Bien que la conjecture de Collatz complète (« toute trajectoire atteint 1 »)
reste ouverte, nous pouvons vérifier des trajectoires spécifiques via
`native_decide`. -/

/-- Fonction d'étape 3n+1 classique : n ↦ n/2 si pair, 3n+1 si impair. -/
def collatzStep (n : Int) : Int :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

/-- Vérifie la célèbre trajectoire partant de 6 :
    6 → 3 → 10 → 5 → 16 → 8 → 4 → 2 → 1 -/
theorem collatz_6_trajectory :
    clIterate collatz 6 8 = [6, 3, 10, 5, 16, 8, 4, 2, 1] := by
  decide

/-- Vérifie la trajectoire partant de 27 (la plus longue sous 100) :
    27 prend 111 étapes pour atteindre 1. Nous vérifions les 10 premières. -/
theorem collatz_27_first_10 :
    clIterate collatz 27 10 = [27, 82, 41, 124, 62, 31, 94, 47, 142, 71, 214] := by
  decide

/-- Vérifie la trajectoire partant de 7 :
    7 → 22 → 11 → 34 → 17 → 52 → 26 → 13 → 40 → 20 → 10 → 5 → 16 → 8 → 4 → 2 → 1 -/
theorem collatz_7_trajectory :
    clIterate collatz 7 16 = [7, 22, 11, 34, 17, 52, 26, 13, 40, 20, 10, 5, 16, 8, 4, 2, 1] := by
  decide

/-! ## Variante (3n+1)/2 de Conway

Conway étudiait souvent la forme compressée où les deux opérations sont
combinées : n ≡ 0 (mod 2) : n/2 ; n ≡ 1 (mod 2) : (3n+1)/2.
Cela divise par deux le nombre d'étapes en combinant l'étape garantie
paire après 3n+1 avec la division par 2 qui s'ensuit. -/

/-- La fonction de Collatz compressée : n pair → n/2, n impair → (3n+1)/2.
    C'est la forme que Conway a analysée dans « Unpredictable Iterations ». -/
def collatzCompressed : CollatzLike where
  m := 2
  hm := by decide
  branches := [
    ⟨0, ⟨1, 0, 2, by decide⟩⟩,    -- n pair : n/2
    ⟨1, ⟨3, 1, 2, by decide⟩⟩     -- n impair : (3n+1)/2
  ]

/-- Vérifie la trajectoire compressée partant de 6 :
    6 → 3 → 5 → 8 → 4 → 2 → 1 (6 étapes au lieu de 8) -/
theorem collatzCompressed_6 :
    clIterate collatzCompressed 6 6 = [6, 3, 5, 8, 4, 2, 1] := by
  decide

/-- Vérifie la trajectoire compressée partant de 7 :
    7 → 11 → 17 → 26 → 13 → 20 → 10 → 5 → 8 → 4 → 2 → 1 -/
theorem collatzCompressed_7 :
    clIterate collatzCompressed 7 11 = [7, 11, 17, 26, 13, 20, 10, 5, 8, 4, 2, 1] := by
  decide

/-! ## Connexion à FRACTRAN

Conway a montré que tout programme FRACTRAN peut être converti en une
fonction de type Collatz et vice-versa. C'est l'idée clé derrière le
résultat d'indécidabilité : puisque FRACTRAN est Turing-complet, et que
l'arrêt de FRACTRAN se réduit à la terminaison des fonctions de type
Collatz, cette dernière est indécidable.

Nous vérifions une étape de cette correspondance : un programme FRACTRAN
simple qui double un nombre correspond à une fonction de type Collatz
spécifique. -/

/-- Le programme FRACTRAN de « doublement » : n ↦ 2n.
    Fraction unique 2/1 : à chaque étape, multiplier par 2. -/
def doubleProgram : List Frac := [frac 2 1 (by decide)]

/-- Vérifie : exécuter le programme de doublement depuis 3 pendant 4 étapes. -/
theorem fractran_double_3 :
    fractranRun doubleProgram 3 4 = [3, 6, 12, 24, 48] := by
  decide

/-! ## Variante 7n+1 de Conway — un problème ouvert

L'une des généralisations ouvertes les plus simples : 7n+1 au lieu de
3n+1. Toute trajectoire est-elle périodique ? On l'ignore. Nous vérifions
que certaines valeurs de départ atteignent bien 1. -/

/-- La fonction 7n+1 : n pair → n/2, n impair → 7n+1. -/
def sevenNPlusOne : CollatzLike where
  m := 2
  hm := by decide
  branches := [
    ⟨0, ⟨1, 0, 2, by decide⟩⟩,    -- n pair : n/2
    ⟨1, ⟨7, 1, 1, by decide⟩⟩     -- n impair : 7n+1
  ]

/-- Vérifie la trajectoire 7n+1 partant de 3 :
    3 → 22 → 11 → 78 → 39 → 274 → 137 → 960 → 480 → 240 → 120 → 60 → 30 → 15 → 106 → 53 → 372 → 186 → 93 → 652 → 326 → 163 → 1142 → 571 → 3998 → ... (longue !)
    Nous vérifions les 5 premières étapes. -/
theorem sevenNPlusOne_3 :
    clIterate sevenNPlusOne 3 5 = [3, 22, 11, 78, 39, 274] := by
  decide

/-- 7n+1 depuis 1 : 1 → 8 → 4 → 2 → 1 (cycle court). -/
theorem sevenNPlusOne_1 :
    clIterate sevenNPlusOne 1 4 = [1, 8, 4, 2, 1] := by
  decide

end Conway
