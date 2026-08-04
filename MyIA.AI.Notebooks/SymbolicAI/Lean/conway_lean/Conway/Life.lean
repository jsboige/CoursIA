/-
Copyright (c) 2026 CoursIA. Tous droits reserves.
Distribue sous licence Apache 2.0 comme decrit dans le fichier LICENSE.

## Jeu de la Vie de Conway — Fondations Phase 1

John Horton Conway (1937-2020) a invente le Jeu de la Vie en 1970 en
collaboration avec les etudiants gradues de Cambridge Michael Guy et autres.
Un automate cellulaire sur le plan entier avec la celebre regle B3/S23.
Malgre son extreme simplicite, la regle supporte le calcul universel
(Conway 1982 ; Rendell 2000) et l'auto-replication (Wade 2010 — Gemini).

Ce fichier est le module **FONDATIONS** de l'hommage Phase 2 (Epic #1647) :
- Etat du jeu encode comme `List (Int x Int)` de cellules vivantes (tri, unique)
- Fonction `step` implementant la regle B3/S23 via operations sur listes
- Iterateur `evolve`
- Predicats `IsStillLife`, `IsOscillator`, `IsSpaceship`
- Temoins pour les patterns canoniques petits
  (block, beehive, blinker, toad, beacon, glider)
- Micro-preuves verifiables par `native_decide` sur egalite de liste

La representation par liste evite le goulot d'etranglement `Quot.lift` /
`Eq.rec` qui survient quand le noyau Lean essaie de decider l'egalite de
`Finset` construite via `image`/`biUnion`/`filter` sur `Int x Int`. L'egalite
de liste se reduit a une comparaison structurelle cons-par-cons, que le
noyau et le generateur de code natif traitent efficacement.

L'optimisation hashlife (Gosper 1984), le parser RLE et les trois piliers
communautaires (Gemini, OTCA Metapixel, ordinateur 8 bits de Carlini) sont
differes aux Phases 2 a 9 de l'Epic #1647.

Ce module est entierement prouve (aucun gap).
-/

import Mathlib.Tactic

/-
  Convention i18n (EPIC #4980, decision user 2026-07-04) : ce fichier est **FR canonique**,
  avec son miroir anglais dans le fichier sibling `Life_en.lean` (modele sibling pair
  ratifie 2026-07-04, cf `code-style.md` §Lean i18n). Les enonces de theoremes,
  les tactiques Lean, les noms de lemmes et les references Mathlib restent en anglais
  (compat Mathlib 4) ; seules les docstrings de module et ce bloc d'en-tete different
  entre les deux fichiers.
-/

namespace Conway
namespace Life

/-! ## Types de base

Nous modelisons les cellules vivantes par une liste triee et dedupliquee de
coordonnees entieres. Les cellules mortes sont celles qui ne sont pas dans
la liste.
-/

/-- Ordre lexicographique sur `Int × Int` pour le tri. -/
def lexLt (a b : Int × Int) : Bool :=
  if a.1 < b.1 then true
  else if a.1 > b.1 then false
  else a.2 < b.2

/-- Une grille du Jeu de la Vie de Conway : liste triee et dedupliquee de
    cellules vivantes. Nous utilisons `List` plutot que `Finset` car
    l'egalite de liste est decidee par comparaison structurelle (pas de
    `Quot.lift`), ce que `native_decide` sait traiter. -/
abbrev Grid := List (Int × Int)

/-! ## Voisinage

Le voisinage de Moore (coup du roi) : les 8 cellules entourant une
cellule donnee. Nous les renvoyons sous forme de liste simple (l'ordre
ne compte pas pour le denombrement).
-/

/-- Les 8 voisins de Moore d'une cellule `p`. -/
def mooreNeighbors (p : Int × Int) : List (Int × Int) :=
  [(p.1 - 1, p.2 - 1), (p.1 - 1, p.2), (p.1 - 1, p.2 + 1),
   (p.1, p.2 - 1),                 (p.1, p.2 + 1),
   (p.1 + 1, p.2 - 1), (p.1 + 1, p.2), (p.1 + 1, p.2 + 1)]

/-! ## La regle B3/S23

Pour chaque cellule, on compte ses voisins de Moore vivants :
- Une cellule morte avec exactement 3 voisins vivants devient vivante (Naissance = B3)
- Une cellule vivante avec 2 ou 3 voisins vivants reste vivante (Survie = S23)
- Sinon la cellule est morte
-/

/-- Verifie si une cellule est vivante dans une grille (test d'appartenance). -/
def isAlive (g : Grid) (p : Int × Int) : Bool :=
  g.elem p

/-- Compte les voisins de Moore vivants de `p` dans la grille `g`. -/
def liveNeighborCount (g : Grid) (p : Int × Int) : Nat :=
  (mooreNeighbors p).countP (isAlive g)

/-- La regle B3/S23 : `p` doit-elle etre vivante a la generation suivante ? -/
def aliveNext (g : Grid) (p : Int × Int) : Bool :=
  let n := liveNeighborCount g p
  if isAlive g p then
    n == 2 || n == 3   -- S23
  else
    n == 3             -- B3

/-- Cellules candidates pour l'etape suivante : cellules vivantes et leurs voisins. -/
def candidates (g : Grid) : List (Int × Int) :=
  g ++ g.flatMap mooreNeighbors

/-- Fermeture reflexive de `lexLt` : un comparateur **total** pour
    `insertionSort`. Sur des paires distinctes il decide exactement comme
    `lexLt` ; sur des paires egales il renvoie `true`. La totalite est ce
    dont `List.pairwise_insertionSort` a besoin pour certifier que la
    sortie est triee (voir `Conway.Life.GridCanonical`). -/
def lexLe (a b : Int × Int) : Bool :=
  lexLt a b || a == b

/-- Trie une liste lexicographiquement et supprime les doublons.

    Le comparateur est le `lexLe` total et la deduplication utilise
    `List.dedup` de Mathlib, donc les lemmes de forme canonique (tri,
    `Nodup`, appartenance, extensionalite) sont tous derivables — voir
    `Conway.Life.GridCanonical`.

    Nous utilisons `insertionSort` (plutot que `mergeSort`) car le
    reducteur du noyau — utilise par `decide` sur les theoremes de
    `Computation` — peut evaluer completement `List.insertionSort`, alors
    que `List.mergeSort` reste *bloque* (son `merge` imbrique est opaque
    a `decide`). Mesure po-2026 c.786 (probe `decide` isole par cible) :
    `mergeSort` bloque pour les types d'elements `Nat` ET `Int` — le
    blocage vient de l'algorithme de tri, pas du type de coordonnees.
    `insertionSort` reduit sous `decide` (POC verifie sur le pattern
    `eater1` a 7 cellules, cas #8749 INTRINSIC). Ce swap preserve les
    coordonnees `Int × Int` (aucun enonce de glider ou d'origine altere)
    et produit une liste canonique byte-identique — les comparateurs
    concordent sur toutes les paires distinctes et les egalites sont
    des *valeurs egales*. -/
def sortDedup (l : List (Int × Int)) : List (Int × Int) :=
  -- `insertionSort` (Mathlib) prend un comparateur en `Prop` ; le
  -- `mergeSort` du noyau Lean prend un comparateur en `Bool`. Nous
  -- remontons `lexLe : → Bool` vers `→ Prop` via `= true` pour que les
  -- deux comparateurs decidendent de maniere identique.
  (List.insertionSort (fun a b => lexLe a b = true) l).dedup

/-- `sortDedup` preserve l'appartenance. -/
theorem mem_sortDedup {p : Int × Int} {l : List (Int × Int)} :
    p ∈ sortDedup l ↔ p ∈ l := by
  unfold sortDedup
  rw [List.mem_dedup, List.mem_insertionSort]

/-- Une etape du Jeu de la Vie de Conway (regle B3/S23). -/
def step (g : Grid) : Grid :=
  sortDedup ((candidates g).filter (fun p => aliveNext g p))

/-- Etape iteree : `evolve n g` applique `step` `n` fois a `g`. -/
def evolve (n : Nat) (g : Grid) : Grid :=
  step^[n] g

@[simp] theorem evolve_zero (g : Grid) : evolve 0 g = g := rfl

@[simp] theorem evolve_succ (n : Nat) (g : Grid) :
    evolve (n + 1) g = step (evolve n g) := by
  simp [evolve, Function.iterate_succ_apply']

/-! ## Predicats de patterns

Nous definissons des predicats a valeur booleenne (renvoyant `Bool`) pour
que `native_decide` puisse les evaluer en compilant vers le code natif et
en comparant l'egalite de `Bool`. Pas de synthese de `Decidable` ni de
`Quot.lift` necessaire — juste une reduction de `Bool`.
-/

/-- Une vie immobile : une grille inchangee par une etape d'evolution. -/
def isStillLife (g : Grid) : Bool := step g == g

/-- Un oscillateur pur de periode `n` : revient a lui-meme en exactement `n` etapes. -/
def isOscillator (g : Grid) (n : Nat) : Bool := evolve n g == g

/-- Translate chaque cellule d'une grille d'un deplacement fixe `v`. -/
def shift (v : Int × Int) (g : Grid) : Grid :=
  sortDedup (g.map (fun p => (p.1 + v.1, p.2 + v.2)))

/-- Un vaisseau de periode `n` et de deplacement `v` : apres `n` etapes, le
    pattern reapparait, translate de `v`. -/
def isSpaceship (g : Grid) (n : Nat) (v : Int × Int) : Bool :=
  evolve n g == shift v g

/-! ## Patterns canoniques

Voici les plus celebres petits patterns du Jeu de la Vie de Conway,
decouverts au debut des annees 1970 par le groupe de Conway a Cambridge et
par les joueurs de la communaute M.I.T. PDP-6/PDP-10.

Chaque pattern est donne dans l'ordre lexicographique trie de sorte que
`step` produise une liste dans le meme ordre, ce qui permet a
`native_decide` de verifier l'egalite par comparaison structurelle.
-/

/-- Le **Block** : un carre 2x2. La plus petite vie immobile. -/
def block : Grid := [(0, 0), (0, 1), (1, 0), (1, 1)]

/-- Le **Beehive** : une vie immobile hexagonale a 6 cellules. -/
def beehive : Grid := [(0, 1), (1, 0), (1, 2), (2, 0), (2, 2), (3, 1)]

/-- Le **Blinker** (horizontal) : trois cellules en ligne. Oscillateur de periode 2. -/
def blinker_h : Grid := [(0, 0), (1, 0), (2, 0)]

/-- Le **Blinker** (vertical) : trois cellules en colonne. -/
def blinker_v : Grid := [(1, -1), (1, 0), (1, 1)]

/-- Le **Toad** (phase 1) : un oscillateur de periode 2. -/
def toad : Grid := [(0, 1), (1, 0), (1, 1), (2, 0), (2, 1), (3, 0)]

/-- Le **Beacon** (phase 1) : deux blocks se touchant en diagonale. Periode 2. -/
def beacon : Grid :=
  [(0, 0), (0, 1), (1, 0), (1, 1), (2, 2), (2, 3), (3, 2), (3, 3)]

/-- Le **Glider** (phase 1, direction sud-est) : le plus petit vaisseau.
    Apres 4 generations il reapparait, translate de (1, -1). -/
def glider : Grid := [(0, 0), (1, 0), (1, 2), (2, 0), (2, 1)]

/-! ## Micro-preuves

Voici les premiers resultats formels de la Phase 1 : verifications simples
de patterns classiques par `native_decide`. Les predicats renvoient `Bool`,
donc `native_decide` compile la fonction d'etape en code natif, evalue
l'expression booleenne et verifie qu'elle egale `true`. Pas de synthese de
`Decidable` ni de `Quot.lift` implique.
-/

/-- Le Block est une vie immobile : `isStillLife block = true`. -/
theorem block_still_life : isStillLife block = true := by decide

/-- Le Beehive est une vie immobile. -/
theorem beehive_still_life : isStillLife beehive = true := by decide

/-- Le Blinker horizontal oscille avec la periode 2. -/
theorem blinker_period_two : isOscillator blinker_h 2 = true := by decide

/-- Une etape transforme le Blinker horizontal en Blinker vertical. -/
theorem blinker_step : (step blinker_h == blinker_v) = true := by decide

/-- Le Toad oscille avec la periode 2. -/
theorem toad_period_two : isOscillator toad 2 = true := by decide

/-- Le Beacon oscille avec la periode 2. -/
theorem beacon_period_two : isOscillator beacon 2 = true := by decide

/-- Le Glider est un vaisseau de periode 4, deplacement `(1, -1)`. -/
theorem glider_spaceship : isSpaceship glider 4 (1, -1) = true := by decide

end Life
end Conway
