/-
Copyright (c) 2026 CoursIA. Tous droits réservés.
Distribué sous licence Apache 2.0 comme décrit dans le fichier LICENSE.

## Jeu de la Vie de Conway — moteur torique (la lecture pavée)

`Conway.Life` simule Life sur une grille creuse **sans bord** : une cellule
isolée évolue comme sur le plan infini, et rien ne revient par le bord.

Or les motifs « piliers » de `Conway.Life.Pillars` ne sont pas tous lus ainsi.
La période de l'UnitCell (`p5760unitlifecell.rle`) est réelle, mais elle
appartient à la lecture **pavée** : mesurée sur un **tore** 500 x 500, la
première répétition tombe aux générations 11 324 et 5 564, soit une période de
**5 760**. La formaliser demandait un moteur torique — absent du lac jusqu'à
ce module, et que le docstring de `Pillars.lean` désignait comme la suite de
cette tranche.

Ce module fournit ce moteur, et le fait qui le rend utile : le **modèle de
bord change le destin du motif**.

| Motif                             | Plan (`Conway.Life.evolve`) | Tore 3 x 3                |
|-----------------------------------|-----------------------------|---------------------------|
| blinker `[(0,0),(1,0),(2,0)]`     | période **2**               | sature, puis **meurt**    |

Le même jeu de trois cellules vivantes est un oscillateur éternel sur le plan
et une configuration éteinte en deux générations sur le tore 3 x 3 : la
couture fait rencontrer des voisins que le plan n'a pas. C'est exactement ce
qui rendait la période de l'UnitCell inexprimable sans pavage.

### Pourquoi des coordonnées `Nat` ici

Le moteur torique énumère les `h x w` cellules de la boîte, donc ses
coordonnées sont **bornées**. On les garde en `Nat` pour une raison de noyau :
`decide` évalue la preuve dans le réducteur du noyau, qui ne réduit pas
`List.range` (récursion bien fondée) ni `Int.emod` de façon fiable — les deux
pièges sont déjà documentés dans ce lac (`List.mergeSort` « reste bloqué »,
cf. `Conway.Life.sortDedup`). L'énumération ci-dessous est donc **structurale**
(`rangeUp`), et le pli torique se fait par `tpred`/`tsucc` plutôt que par un
modulo.

### Convention i18n (EPIC #4980, décision user 2026-07-04)

Ce fichier est le **FR canonique** ; son jumeau `Torus_en.lean` porte les
mêmes énoncés et les mêmes preuves avec des docstrings anglaises (namespace
suffixe `_en`). Les énoncés mathématiques et les tactiques sont identiques
de part et d'autre.
-/

import Conway.Life

namespace Conway
namespace Life
namespace Torus

/-! ## Pli torique d'une coordonnée

Le pli se fait par un pas conditionnel, pas par un modulo : `tpred` et `tsucc`
sont des `if` sur des entiers naturels, donc le noyau les réduit sans effort.
-/

/-- Prédécesseur torique dans `[0, n)` : `0` a pour prédécesseur `n - 1`. -/
def tpred (n : Nat) (i : Nat) : Nat := if i = 0 then n - 1 else i - 1

/-- Successeur torique dans `[0, n)` : `n - 1` a pour successeur `0`. -/
def tsucc (n : Nat) (i : Nat) : Nat := if i + 1 = n then 0 else i + 1

/-- `[0, n)` en ordre croissant, par récursion **structurelle** sur `n`.

    `List.range` construit la même liste par récursion bien fondée, que le
    réducteur du noyau ne déplie pas ; `rangeUp` est la version que `decide`
    peut évaluer. -/
def rangeUp : Nat → List Nat
  | 0 => []
  | n + 1 => rangeUp n ++ [n]

/-- Les `h x w` cellules du tore, en ordre croissant (ligne puis colonne).

    L'ordre croissant est ce qui rend les témoins lisibles : `torusStep`
    filtre cette liste sans la réordonner, donc ses sorties sont canoniques
    comme celles de `Conway.Life.step` (qui, lui, trie et déduplique). -/
def torusCells (h w : Nat) : List (Nat × Nat) :=
  (rangeUp h).flatMap (fun r => (rangeUp w).map (fun c => (r, c)))

/-- Les huit voisins de Moore d'une cellule sur le tore `h x w`, chaque
    coordonnée repliée indépendamment, la cellule elle-même retirée. -/
def torusNeighbors (h w : Nat) (p : Nat × Nat) : List (Nat × Nat) :=
  let rs := [tpred h p.1, p.1, tsucc h p.1]
  let cs := [tpred w p.2, p.2, tsucc w p.2]
  ((rs.flatMap (fun r => cs.map (fun c => (r, c)))).filter (fun q => q != p))

/-- Une cellule est vivante dans une grille torique si elle y figure. -/
def torusLive (g : List (Nat × Nat)) (p : Nat × Nat) : Bool :=
  g.elem p

/-- Nombre de voisins vivants de `p` sur le tore. -/
def torusCount (h w : Nat) (g : List (Nat × Nat)) (p : Nat × Nat) : Nat :=
  (torusNeighbors h w p).countP (torusLive g)

/-- La règle B3/S23 sur le tore : identique au plan, seul le voisinage change. -/
def torusAliveNext (h w : Nat) (g : List (Nat × Nat)) (p : Nat × Nat) : Bool :=
  let n := torusCount h w g p
  if torusLive g p then
    n == 2 || n == 3
  else
    n == 3

/-- Une génération sur le tore `h x w`. -/
def torusStep (h w : Nat) (g : List (Nat × Nat)) : List (Nat × Nat) :=
  (torusCells h w).filter (fun p => torusAliveNext h w g p)

/-- `n` générations sur le tore `h x w`. -/
def torusEvolve (h w : Nat) (n : Nat) (g : List (Nat × Nat)) : List (Nat × Nat) :=
  -- Parenthèses obligatoires : `^[` lie plus fort que l'application, donc
  -- `torusStep h w ^[n]` se lirait `torusStep h (w ^[n])`. `Conway.Life.evolve`
  -- n'a pas ce piège parce qu'il itère un identifiant nu (`step^[n]`).
  (torusStep h w)^[n] g

/-- Traduction d'une grille torique : sans repli, donc injective — l'ordre
    de la liste est préservé et aucun doublon n'apparaît. -/
def torusShift (dr dc : Nat) (g : List (Nat × Nat)) : List (Nat × Nat) :=
  g.map (fun p => (p.1 + dr, p.2 + dc))

/-! ## Le tore est clos

Une génération ne fait pas sortir de la boîte : chaque cellule candidate vient
de `torusCells h w`. C'est la propriété qui distingue le tore du plan, où les
cellules s'échappent indéfiniment (le fait mesuré sur l'UnitCell).
-/

/-- Toute cellule d'une génération appartient à la boîte `h x w`. -/
theorem torusStep_subset (h w : Nat) (g : List (Nat × Nat)) :
    ∀ p ∈ torusStep h w g, p ∈ torusCells h w := by
  intro p hp
  -- `List.mem_filter` rend `(a ∈ l) ∧ (p a = true)` : l'appartenance est le
  -- premier membre.
  exact (List.mem_filter.mp hp).1

/-- `torusEvolve` n'ajoute aucune cellule hors boîte non plus — **à condition
    de partir d'une grille dans la boîte**. La partie « à condition » n'est pas
    cosmétique : à `n = 0` le moteur rend la grille telle quelle, donc une
    grille d'entrée hors boîte y resterait hors boîte. C'est le prix de la
    lecture pavée : le tore est clos à partir de la première génération. -/
theorem torusEvolve_subset (h w : Nat) {g : List (Nat × Nat)}
    (hg : ∀ p ∈ g, p ∈ torusCells h w) (n : Nat) :
    ∀ p ∈ torusEvolve h w n g, p ∈ torusCells h w := by
  induction n with
  | zero => exact hg
  | succ k ih =>
      intro p hp
      simp only [torusEvolve, Function.iterate_succ_apply'] at hp
      exact torusStep_subset h w _ p hp

@[simp] theorem torusEvolve_zero (h w : Nat) (g : List (Nat × Nat)) :
    torusEvolve h w 0 g = g := rfl

@[simp] theorem torusEvolve_succ (h w : Nat) (n : Nat) (g : List (Nat × Nat)) :
    torusEvolve h w (n + 1) g = torusStep h w (torusEvolve h w n g) := by
  simp [torusEvolve, Function.iterate_succ_apply']

/-! ## Témoins

Tous sont prouvés par `decide` dans le noyau : **aucun `native_decide`**, donc
aucun axiome nouveau. Le gate `proof-integrity` du lac rougit sur tout
`native_decide` non listé ; ces énoncés n'en ajoutent aucun.
-/

/-- Le blinker horizontal du lac, rappelé pour la lisibilité des énoncés. -/
def blinkerT : List (Nat × Nat) := [(0, 0), (1, 0), (2, 0)]

/-- Le même blinker, translaté pour tenir entièrement loin des coutures d'un
    tore 5 x 5 (lignes 1..3, colonne 2 — aucune coordonnée au bord). -/
def blinkerT5 : List (Nat × Nat) := [(1, 2), (2, 2), (3, 2)]

/-- Le planeur standard, cinq cellules, en ordre croissant. -/
def gliderT : List (Nat × Nat) := [(0, 2), (1, 0), (1, 2), (2, 1), (2, 2)]

/-- **Le blinker est de période 2 sur le plan.** Énoncé absent du lac comme
    théorème : il n'y figurait qu'en `#eval` commenté (`Hashlife.lean`). -/
theorem blinker_plane_period_two : evolve 2 blinker_h = blinker_h := by decide

/-- **Témoin négatif apparié** : le blinker du plan n'est pas une vie immobile,
    donc la période vaut 2 et non 1. -/
theorem blinker_plane_not_still : evolve 1 blinker_h ≠ blinker_h := by decide

/-- **Accord tore / plan loin de la couture.** Sur un tore 5 x 5, un blinker
    qui ne touche aucune couture a la même période 2 que sur le plan : le
    moteur torique ne déforme pas ce qu'il n'a pas besoin de plier. -/
theorem blinker_torus5_period_two :
    torusEvolve 5 5 2 blinkerT5 = blinkerT5 := by decide

/-- **Témoin négatif apparié** : période 2, pas 1. -/
theorem blinker_torus5_not_still :
    torusEvolve 5 5 1 blinkerT5 ≠ blinkerT5 := by decide

/-- **La divergence des modèles de bord.** Le même jeu de trois cellules
    alignées, placé sur un tore 3 x 3, sature la boîte en une génération. -/
theorem blinker_torus3_saturates :
    torusEvolve 3 3 1 blinkerT = torusCells 3 3 := by decide

/-- **... puis meurt** : deux générations suffisent à éteindre la grille, alors
    que le même motif oscille indéfiniment sur le plan (`blinker_plane_period_two`).
    C'est le témoin qui explique pourquoi la période de l'UnitCell n'était pas
    exprimable sans pavage. -/
theorem blinker_torus3_dies :
    torusEvolve 3 3 2 blinkerT = [] := by decide

/-- **Témoin négatif apparié** : la grille n'est pas déjà éteinte après une
    seule génération — l'extinction est bien un effet de la deuxième. -/
theorem blinker_torus3_not_dead_at_one :
    torusEvolve 3 3 1 blinkerT ≠ [] := by decide

/-- **Un vaisseau sur le tore** : le planeur, après quatre générations sur un
    tore 20 x 20, est le translaté de `(1, 1)` de lui-même. Le repli ne gêne
    pas son vol tant qu'il ne touche pas la couture. -/
theorem glider_torus_spaceship :
    torusEvolve 20 20 4 gliderT = torusShift 1 1 gliderT := by decide

/-- **Témoin négatif apparié** : le planeur n'est pas immobile — sa période
    n'est donc pas 1. -/
theorem glider_torus_not_still :
    torusEvolve 20 20 1 gliderT ≠ gliderT := by decide

end Torus
end Life
end Conway
