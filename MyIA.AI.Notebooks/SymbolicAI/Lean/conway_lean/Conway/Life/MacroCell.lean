/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

## MacroCell — Representation par quadtree pour Hashlife

Une `MacroCell` represente une region carree de la grille du Jeu de la
Vie sous forme de quadtree. Les cellules de niveau 0 sont des cellules
booleennes individuelles. Une cellule de niveau (n+1) est un
arrangement 2x2 de cellules de niveau n (nommees `nw`, `ne`, `sw`, `se`
pour nord-ouest, nord-est, sud-ouest, sud-est).

L'idee clee de Hashlife (Gosper 1984) est que la fonction de pas sur
les MacroCell peut etre calculee recursivement et memoisee, donnant une
acceleration exponentielle sur les motifs a structure repetitive.

## Convention de disposition

Nous utilisons la meme convention de coordonnees que `Conway.Life` :
- Chaque cellule est `(row, col) : Int × Int`.
- Les lignes croissent vers le bas (nord -> sud).
- Les colonnes croissent vers la droite (ouest -> est).

Ainsi, au niveau le plus haut, un noeud `node nw ne sw se` de niveau
`n+1` couvre une region de taille `2^(n+1) x 2^(n+1)` partitionnee en :

```
nw | ne
---+---
sw | se
```

ou chaque quadrant est `2^n x 2^n`. Si la region entiere a son coin
haut-gauche en `(row0, col0)`, alors :

- `nw` couvre `[row0,            row0 + 2^n)         x [col0,           col0 + 2^n)`
- `ne` couvre `[row0,            row0 + 2^n)         x [col0 + 2^n,    col0 + 2^(n+1))`
- `sw` couvre `[row0 + 2^n,     row0 + 2^(n+1))      x [col0,           col0 + 2^n)`
- `se` couvre `[row0 + 2^n,     row0 + 2^(n+1))      x [col0 + 2^n,    col0 + 2^(n+1))`

Ce module est entierement prouve (aucun trou). Il fournit seulement la
structure de donnees et les conversions. L'algorithme Hashlife vit dans
`Conway.Life.Hashlife`.
-/

import Conway.Life


/-
  Convention i18n (EPIC #4980, décision user 2026-07-04) : ce fichier est **FR canonique**,
  avec son miroir anglais dans le fichier sibling `MacroCell_en.lean` (modèle sibling
  pair ratifié 2026-07-04, cf `code-style.md` paragraphe Lean i18n). Les énoncés de
  théorèmes, les tactiques Lean, les noms de lemmes et les références Mathlib restent en
  anglais (compatibilité Mathlib 4) ; seules les docstrings de module et ce bloc d'en-tête
  diffèrent entre les deux fichiers.
-/

namespace Conway

namespace Life

/-! ## La structure de donnees quadtree -/

/-- Une cellule de quadtree.
    - `leaf b` est une cellule unique qui est vivante (`b = true`) ou morte (`b = false`).
    - `node nw ne sw se` est un bloc 2x2 de sous-arbres, tous requis (par convention,
      mais non impose par le type) d'etre au meme niveau. -/
inductive MacroCell where
  | leaf (alive : Bool)
  | node (nw ne sw se : MacroCell)
  -- `DecidableEq` (plutot qu'un `BEq` derive) pour que l'instance `BEq`
  -- soit licite (`instLawfulBEq`), ce dont les preuves du cache de
  -- memoisation dans `Conway.Life.HashlifeMemo` dependent.
  deriving DecidableEq, Repr, Inhabited

namespace MacroCell

/-- Le niveau d'une `MacroCell` : 0 pour `leaf`, `1 + nw.level` pour `node`.
    Par construction, une `MacroCell` bien formee a ses quatre sous-arbres au
    meme niveau ; nous inspectons seulement `nw`. -/
def level : MacroCell -> Nat
  | leaf _      => 0
  | node nw _ _ _ => 1 + nw.level

/-- La longueur de cote de la region couverte par une `MacroCell` : `2 ^ level`. -/
def size (c : MacroCell) : Nat := 2 ^ c.level

/-- Une feuille contenant une cellule morte. -/
def deadLeaf : MacroCell := leaf false

/-- Une feuille contenant une cellule vivante. -/
def aliveLeaf : MacroCell := leaf true

/-- Construit une `MacroCell` "vide" (tout-morte) de niveau `n`. -/
def emptyOfLevel : Nat -> MacroCell
  | 0     => deadLeaf
  | n + 1 =>
    let sub := emptyOfLevel n
    node sub sub sub sub

/-- Teste si une `MacroCell` represente la region toute-morte. -/
def isEmpty : MacroCell -> Bool
  | leaf b      => !b
  | node a b c d => a.isEmpty && b.isEmpty && c.isEmpty && d.isEmpty

/-! ## Conversion : MacroCell -> Grid

Etant donnee une `MacroCell` et le decalage absolu `(row, col)` de son
coin haut-gauche, enumerer les cellules vivantes dans l'ordre
lexicographique `(row, col)`.

La recursion parcourt les quadrants dans l'ordre `nw, ne, sw, se`.
Traiter toutes les lignes de `nw` avant celles de `ne` n'est **pas**
correct dans l'ordre lex quand les lignes s'entrelacent ; cependant,
parce que `nw` et `ne` couvrent la meme plage de lignes et que `nw` a
des colonnes strictement plus petites, lister tout `nw` puis tout `ne`
produit l'ordre lex **seulement quand** la sortie de chaque quadrant est
elle-meme triee. L'implementation plus simple et evidemment correcte
consiste a concatener les quatre quadrants puis a `sortDedup` au niveau
du haut. -/

/-- Aide interne : enumerer les cellules vivantes de `c` dont le coin
    haut-gauche est au decalage `(r0, c0)`. La liste resultante n'est **pas**
    garantie triee dans l'ordre lex — l'appelant devrait `sortDedup` si besoin. -/
def toCellsAux (r0 c0 : Int) : MacroCell -> List (Int × Int)
  | leaf true   => [(r0, c0)]
  | leaf false  => []
  | node nw ne sw se =>
    let n := nw.level
    let half : Int := (2 ^ n : Nat)
    nw.toCellsAux r0 c0
      ++ ne.toCellsAux r0 (c0 + half)
      ++ sw.toCellsAux (r0 + half) c0
      ++ se.toCellsAux (r0 + half) (c0 + half)

/-- Convertit une `MacroCell` en `Grid`, etant donne le decalage `(r0, c0)` de
    son coin haut-gauche. La sortie est triee lexicographiquement et dedoublonnee. -/
def toGrid (offset : Int × Int) (c : MacroCell) : Grid :=
  sortDedup (c.toCellsAux offset.1 offset.2)

end MacroCell

/-! ## Conversion : Grid -> MacroCell

Etant donne un `Grid` (liste des coordonnees des cellules vivantes),
construire une `MacroCell` du plus petit niveau dont la region, placee a
un decalage choisi, contient toutes les cellules vivantes. Le decalage
est renvoye a cote pour que les appels ulterieurs a `toGrid` fassent un
aller-retour correct.

La construction est directe mais un peu fastidieuse :
1. Trouver la boite englobante `[rMin, rMax] x [cMin, cMax]` des cellules
   vivantes (en utilisant du rembourrage supplementaire de chaque cote
   pour permettre a `step` de s'etendre).
2. Calculer la longueur de cote necessaire : `max (rMax - rMin + 1) (cMax - cMin + 1)`,
   arrondie a la puissance de 2 superieure.
3. Construire recursivement le quadtree, en envoyant chaque cellule
   vivante vers le quadrant approprie.
-/

namespace MacroCell

/-- Plus petit `n` tel que `2 ^ n >= k`.

    Implementation note (#8869, c.847) : la recursion precedente
    `| k + 2 => 1 + ceilLog2 ((k + 2 + 1) / 2)` etait **WellFounded** (l'argument
    `(k+2+1)/2` n'est pas structurellement plus petit), donc **opaque au reducteur
    du noyau** — `decide` ne pouvait pas l'evaluer, bloquant `gridFrame lvl` puis
    toute la chaine `buildFromGrid`/`toGrid`/`evolveHashlife` (les 14 theoremes de
    coherence de `Computation.lean` etaient `native_decide` par symptome, pas par
    necessite intrinseque). Reformulee via `Nat.log 2` (recursion structurelle de
    Mathlib, noyau-reductible) : `ceilLog2 k = if k ≤ 1 then 0 else Nat.log 2 (k-1) + 1`.
    Meme fonction (valeurs invariantes, cf `ceilLog2_spec`), mais desormais
    decidable. Diagnostic firsthand : `ceilLog2 6 = 3` passe sous `decide` apres
    rewrite (echouait avant, meme avec `maxRecDepth 1000000`, meme sur 1 pas). -/
def ceilLog2 (k : Nat) : Nat :=
  if k ≤ 1 then 0 else Nat.log 2 (k - 1) + 1

/-- `ceilLog2 k` est assez grand pour que `2 ^ ceilLog2 k >= k`. C'est le
    coeur arithmetique du lemme de containment de `gridFrame`. -/
theorem ceilLog2_spec (k : Nat) : 2 ^ ceilLog2 k >= k := by
  by_cases hk : k ≤ 1
  · -- k = 0 ou 1 : ceilLog2 k = 0, et 2^0 = 1 ≥ k
    simp only [ceilLog2, hk, reduceIte]
    omega
  · -- k ≥ 2 : ceilLog2 k = Nat.log 2 (k-1) + 1, et k ≤ 2^((k-1).log+1) par la
    -- borne superieure de Nat.log (Mathlib : n < b^(log b n + 1)).
    simp only [ceilLog2, hk, reduceIte]
    have h := Nat.lt_pow_succ_log_self Nat.one_lt_two (k - 1)
    rw [Nat.succ_eq_add_one] at h
    omega

/-- Construit une `MacroCell` de niveau `n` couvrant le carre
    `[r0, r0 + 2^n) x [c0, c0 + 2^n)`, avec les cellules vivantes donnees par
    le test d'appartenance dans `g`. -/
def buildFromGrid (g : Grid) (r0 c0 : Int) : Nat -> MacroCell
  | 0     => leaf (g.elem (r0, c0))
  | n + 1 =>
    let half : Int := (2 ^ n : Nat)
    let nw := buildFromGrid g r0          c0          n
    let ne := buildFromGrid g r0          (c0 + half) n
    let sw := buildFromGrid g (r0 + half) c0          n
    let se := buildFromGrid g (r0 + half) (c0 + half) n
    node nw ne sw se

/-- Le niveau d'une `MacroCell` construite par `buildFromGrid g r0 c0 lvl` est `lvl`. -/
theorem level_buildFromGrid (g : Grid) (r0 c0 : Int) (lvl : Nat) :
    (buildFromGrid g r0 c0 lvl).level = lvl := by
  induction lvl with
  | zero => rfl
  | succ n ih =>
    simp only [buildFromGrid]
    rw [level, ih]
    omega

/-- Une cellule `p` se trouve dans le carre de niveau `lvl` ancre en `(r0, c0)` :
    `[r0, r0 + 2^lvl) x [c0, c0 + 2^lvl)`.

    NOTE : `cases`/`rcases`/`rintro` sur une disjonction dont les branches
    mentionnent `inRegion` (qui se deploie en `Int.le`/`Int.lt`) declenche un
    echec d'elimination dependante de Lean sur le match de soustraction Int. La
    preuve ci-dessous utilise `match` (qui s'elabore differemment et reussit)
    pour decomposer la disjonction a 4 quadrants. -/
def inRegion (p : Int × Int) (r0 c0 : Int) (lvl : Nat) : Prop :=
  r0 ≤ p.1 ∧ p.1 < r0 + (2 ^ lvl : Nat) ∧
    c0 ≤ p.2 ∧ p.2 < c0 + (2 ^ lvl : Nat)

/-- **Lemme central d'aller-retour** : une cellule `p` apparait dans
    l'enumeration `toCellsAux` de `buildFromGrid g r0 c0 lvl` ssi `p` se
    trouve dans le carre couvert ET `p ∈ g`. Prouve par induction sur `lvl`,
    en generalisant les decalages pour que l'IH s'applique aux origines
    decalees des quadrants. -/
theorem mem_toCellsAux_buildFromGrid (g : Grid) (lvl : Nat) (r0 c0 : Int)
    (p : Int × Int) :
    p ∈ (buildFromGrid g r0 c0 lvl).toCellsAux r0 c0 ↔
      inRegion p r0 c0 lvl ∧ p ∈ g := by
  induction lvl generalizing r0 c0 p with
  | zero =>
    cases h : g.elem (r0, c0) with
    | true =>
      unfold inRegion
      simp only [buildFromGrid, toCellsAux, h, pow_zero, Nat.cast_one,
                 List.mem_singleton]
      constructor
      · rintro rfl
        refine ⟨⟨rfl.le, by omega, rfl.le, by omega⟩, ?_⟩
        exact List.elem_iff.mp h
      · rintro ⟨⟨h1, h2, h3, h4⟩, _⟩
        ext <;> omega
    | false =>
      simp only [buildFromGrid, toCellsAux, h, List.not_mem_nil, false_iff]
      rintro ⟨hreg, hpg⟩
      unfold inRegion at hreg
      obtain ⟨h1, h2, h3, h4⟩ := hreg
      have hp : p = (r0, c0) := by ext <;> omega
      subst hp
      have hne : (r0, c0) ∉ g := by
        intro hm
        exact absurd (List.elem_iff.mpr hm) (Bool.eq_false_iff.mp h)
      exact absurd hpg hne
  | succ n ih =>
    simp only [buildFromGrid, toCellsAux, level_buildFromGrid] at *
    simp only [List.mem_append] at *
    have ihn := ih r0 c0 p
    have ihne := ih r0 (c0 + (2 ^ n : Nat)) p
    have ihsw := ih (r0 + (2 ^ n : Nat)) c0 p
    have ihse := ih (r0 + (2 ^ n : Nat)) (c0 + (2 ^ n : Nat)) p
    rw [ihn, ihne, ihsw, ihse]
    constructor
    · -- Direct : `match` (pas rcases) decompose le Or — rcases/rintro declenchent
      -- un echec d'elimination dependante de Lean sur les Int.le dans les types
      -- de branches. Imbriquee a gauche `((A ∨ B) ∨ C) ∨ D` :
      --   nw = inl (inl (inl _)), ne = inl (inl (inr _)),
      --   sw = inl (inr _),       se = inr _.
      intro h
      match h with
      | Or.inl (Or.inl (Or.inl ⟨hreg, hm⟩)) =>
        unfold inRegion at hreg
        refine ⟨?_, hm⟩
        unfold inRegion; simp only [Nat.pow_succ, Nat.cast_mul]; omega
      | Or.inl (Or.inl (Or.inr ⟨hreg, hm⟩)) =>
        unfold inRegion at hreg
        refine ⟨?_, hm⟩
        unfold inRegion; simp only [Nat.pow_succ, Nat.cast_mul]; omega
      | Or.inl (Or.inr ⟨hreg, hm⟩) =>
        unfold inRegion at hreg
        refine ⟨?_, hm⟩
        unfold inRegion; simp only [Nat.pow_succ, Nat.cast_mul]; omega
      | Or.inr ⟨hreg, hm⟩ =>
        unfold inRegion at hreg
        refine ⟨?_, hm⟩
        unfold inRegion; simp only [Nat.pow_succ, Nat.cast_mul]; omega
    · rintro ⟨hreg, hpg⟩
      unfold inRegion at hreg
      simp only [Nat.pow_succ, Nat.cast_mul] at hreg
      by_cases hr : p.1 < r0 + (2 ^ n : Nat)
      · by_cases hc : p.2 < c0 + (2 ^ n : Nat)
        · left; left; left; unfold inRegion; refine ⟨⟨?_, ?_, ?_, ?_⟩, hpg⟩ <;> omega
        · left; left; right; unfold inRegion; refine ⟨⟨?_, ?_, ?_, ?_⟩, hpg⟩ <;> omega
      · by_cases hc : p.2 < c0 + (2 ^ n : Nat)
        · left; right; unfold inRegion; refine ⟨⟨?_, ?_, ?_, ?_⟩, hpg⟩ <;> omega
        · right; unfold inRegion; refine ⟨⟨?_, ?_, ?_, ?_⟩, hpg⟩ <;> omega

/-- **Identite de decalage pour `toCellsAux`** : enumerer les cellules
    vivantes de `c` avec le coin haut-gauche ancre en `(r0, c0)` egale
    l'enumeration ancoree a l'origine `(c.toCellsAux 0 0)` translatee
    point par point par `(r0, c0)`. Induction structurelle pure sur
    `MacroCell` — pas de Hashlife, pas d'`evolve`, pas de cone de lumiere.
    C'est le pont de comptabilite qui alignera un objectif d'appartenance
    `toCellsAux` / `toGrid` a decalage `(r0, c0)` avec une hypothese
    d'induction ancoree a l'origine dans le futur assemblage P4 de
    correction centrale (`hashlifeResult_central_correct`). -/
theorem toCellsAux_shift (c : MacroCell) (r0 c0 : Int) :
    c.toCellsAux r0 c0 =
      (c.toCellsAux 0 0).map (fun p => (p.1 + r0, p.2 + c0)) := by
  induction c generalizing r0 c0 with
  | leaf b =>
    -- `toCellsAux r0 c0 (leaf b)` se reduit en `[(r0, c0)]` / `[]`, mais
    -- `List.map f [(0, 0)] = [(0 + r0, 0 + c0)]` n'est PAS defeq a `[(r0, c0)]`
    -- (`Int.add 0 _` ne se reduit pas definitionnellement), donc `rfl` echoue —
    -- fermer par `zero_add` a la place.
    cases b
    · simp only [toCellsAux, List.map_nil]
    · simp only [toCellsAux, List.map_singleton, zero_add]
  | node nw ne sw se ihw ine isw ise =>
    simp only [toCellsAux]
    -- Appliquer l'IH a chaque quadrant du membre gauche, en ancrant a l'origine :
    rw [ihw r0 c0, ine r0 (c0 + (2 ^ nw.level : Nat)),
        isw (r0 + (2 ^ nw.level : Nat)) c0,
        ise (r0 + (2 ^ nw.level : Nat)) (c0 + (2 ^ nw.level : Nat))]
    -- Distribuer le map du membre droit sur la concatenation, puis replier
    -- les quadrants ancores a l'origine a travers l'IH (en avant) pour que
    -- chaque segment du membre droit devienne une composition de deux
    -- decalages ; `map_map` l'aplatit.
    simp only [List.map_append, zero_add]
    rw [ine 0 (2 ^ nw.level : Nat), isw (2 ^ nw.level : Nat) 0,
        ise (2 ^ nw.level : Nat) (2 ^ nw.level : Nat)]
    simp only [List.map_map, zero_add]
    -- Les deux membres sont maintenant des concatenations de `map (shift_i) (toCellsAux 0 0 sub_i)`,
    -- ne differant que par des rearrangements AC de l'addition ; normaliser et fermer.
    simp only [add_zero, add_assoc, add_comm, add_left_comm]
    rfl

/-- **Forme d'appartenance de l'identite de decalage** : `p` se trouve dans
    l'enumeration a decalage `(r0, c0)` de `c` ssi `p` translatee vers
    l'origine `(p.1 - r0, p.2 - c0)` se trouve dans l'enumeration ancoree a
    l'origine. C'est la forme directement utilisable dans les
    biconditionnelles d'appartenance (ex. l'objectif P4 de correction
    centrale `p ∈ (hashlifeResultAux …).toGrid off ↔ …`), ou l'egalite de
    liste `toCellsAux_shift` est moins commode. -/
theorem mem_toCellsAux_shift {c : MacroCell} {r0 c0 : Int} {p : Int × Int} :
    p ∈ c.toCellsAux r0 c0 ↔ (p.1 - r0, p.2 - c0) ∈ c.toCellsAux 0 0 := by
  rw [toCellsAux_shift, List.mem_map]
  constructor
  · rintro ⟨q, hqmem, hpq⟩
    -- `q` est une variable libre, donc nous reecrivons l'appartenance pour
    -- parler de `q` directement (impossible de `subst` sur `q.1`/`q.2`, qui
    -- sont des acces a des champs).
    have hqeq : q = (p.1 - r0, p.2 - c0) := by
      rw [Prod.ext_iff] at hpq; ext <;> omega
    rw [hqeq] at hqmem
    exact hqmem
  · intro hq
    refine ⟨(p.1 - r0, p.2 - c0), hq, ?_⟩
    ext <;> omega

end MacroCell

/-! ## Grid -> MacroCell de haut niveau

Nous choisissons un decalage et un niveau assez grands pour contenir
`g`. Pour laisser de la place a un tour de `step` pour s'etendre, nous
ajoutons un rembourrage de 2 cellules de chaque cote de la boite
englobante. Les grilles vides donnent la feuille de niveau 0 toute-morte. -/

/-- La ligne minimum d'une grille non vide ; par defaut 0 sur la grille vide. -/
def gridRowMin (g : Grid) : Int :=
  match g with
  | []      => 0
  | p :: ps => ps.foldl (fun m q => min m q.1) p.1

/-- La ligne maximum d'une grille non vide ; par defaut 0 sur la grille vide. -/
def gridRowMax (g : Grid) : Int :=
  match g with
  | []      => 0
  | p :: ps => ps.foldl (fun m q => max m q.1) p.1

/-- La colonne minimum d'une grille non vide ; par defaut 0 sur la grille vide. -/
def gridColMin (g : Grid) : Int :=
  match g with
  | []      => 0
  | p :: ps => ps.foldl (fun m q => min m q.2) p.2

/-- La colonne maximum d'une grille non vide ; par defaut 0 sur la grille vide. -/
def gridColMax (g : Grid) : Int :=
  match g with
  | []      => 0
  | p :: ps => ps.foldl (fun m q => max m q.2) p.2

/-! ## Lemmes d'appartenance a la boite englobante

Ces lemmes relient `gridRowMin` / `gridRowMax` / `gridColMin` / `gridColMax`
a l'appartenance de liste : toute cellule vivante de `g` se trouve dans sa
boite englobante. Ils forment le pont arithmetique pour
`gridFrame_contains_g` (correction P5, issue #2162, Gap 2 — l'aller-retour
Grid↔MacroCell).

Les quatre aides a boite englobante sont des `foldl` sur une projection de
coordonnee, donc nous factorisons le raisonnement via des lemmes generiques
parametres par `proj` et nous les instancions pour les lignes (`(·.1)`) et
les colonnes (`(·.2)`). Nous decomposons `p ∈ head :: tail` via `by_cases`
plutot que `cases`/`subst` pour eviter la substitution dependante de la
direction (quel cote est elimine) quand les deux operandes sont des
variables locales. -/

/-- Aide generique : un `foldl` de `min` (via une projection `proj`) ne
    depasse jamais son accumulateur de depart. -/
theorem foldl_proj_min_le_seed (ps : Grid) (proj : Int × Int → Int) (acc : Int) :
    ps.foldl (fun m q => min m (proj q)) acc ≤ acc := by
  induction ps generalizing acc with
  | nil => simp
  | cons q qs ih =>
    simp only [List.foldl_cons]
    have h := ih (min acc (proj q))
    omega

/-- Aide generique : un `foldl` de `min` (via `proj`) ne depasse jamais la
    coordonnee projettee d'une cellule quelconque de la liste. -/
theorem foldl_proj_min_le_of_mem (ps : Grid) (proj : Int × Int → Int) (acc : Int)
    (p : Int × Int) (hp : p ∈ ps) :
    ps.foldl (fun m q => min m (proj q)) acc ≤ proj p := by
  induction ps generalizing acc p with
  | nil => simp at hp
  | cons q qs ih =>
    simp only [List.foldl_cons]
    by_cases heq : p = q
    · rw [heq]
      have h := foldl_proj_min_le_seed qs proj (min acc (proj q))
      omega
    · have hps : p ∈ qs := by
        rcases List.mem_cons.mp hp with hhead | hps
        · exact absurd hhead heq
        · exact hps
      exact ih (min acc (proj q)) p hps

/-- Aide generique : un `foldl` de `max` (via une projection `proj`) n'est
    jamais en dessous de son accumulateur de depart. -/
theorem le_foldl_proj_max_seed (ps : Grid) (proj : Int × Int → Int) (acc : Int) :
    acc ≤ ps.foldl (fun m q => max m (proj q)) acc := by
  induction ps generalizing acc with
  | nil => simp
  | cons q qs ih =>
    simp only [List.foldl_cons]
    have h := ih (max acc (proj q))
    omega

/-- Aide generique : un `foldl` de `max` (via `proj`) n'est jamais en dessous
    de la coordonnee projettee d'une cellule quelconque de la liste. -/
theorem le_foldl_proj_max_of_mem (ps : Grid) (proj : Int × Int → Int) (acc : Int)
    (p : Int × Int) (hp : p ∈ ps) :
    proj p ≤ ps.foldl (fun m q => max m (proj q)) acc := by
  induction ps generalizing acc p with
  | nil => simp at hp
  | cons q qs ih =>
    simp only [List.foldl_cons]
    by_cases heq : p = q
    · rw [heq]
      have h := le_foldl_proj_max_seed qs proj (max acc (proj q))
      omega
    · have hps : p ∈ qs := by
        rcases List.mem_cons.mp hp with hhead | hps
        · exact absurd hhead heq
        · exact hps
      exact ih (max acc (proj q)) p hps

/-- Toute cellule de `g` a une coordonnee de ligne au moins `gridRowMin g`. -/
theorem gridRowMin_le_of_mem (g : Grid) (p : Int × Int) (hp : p ∈ g) :
    gridRowMin g ≤ p.1 := by
  cases g with
  | nil => simp at hp
  | cons p₀ ps =>
    simp only [gridRowMin]
    by_cases heq : p = p₀
    · rw [heq]
      exact foldl_proj_min_le_seed ps (·.1) p₀.1
    · have hps : p ∈ ps := by
        rcases List.mem_cons.mp hp with hhead | hps
        · exact absurd hhead heq
        · exact hps
      exact foldl_proj_min_le_of_mem ps (·.1) p₀.1 p hps

/-- Toute cellule de `g` a une coordonnee de ligne au plus `gridRowMax g`. -/
theorem le_gridRowMax_of_mem (g : Grid) (p : Int × Int) (hp : p ∈ g) :
    p.1 ≤ gridRowMax g := by
  cases g with
  | nil => simp at hp
  | cons p₀ ps =>
    simp only [gridRowMax]
    by_cases heq : p = p₀
    · rw [heq]
      exact le_foldl_proj_max_seed ps (·.1) p₀.1
    · have hps : p ∈ ps := by
        rcases List.mem_cons.mp hp with hhead | hps
        · exact absurd hhead heq
        · exact hps
      exact le_foldl_proj_max_of_mem ps (·.1) p₀.1 p hps

/-- Toute cellule de `g` a une coordonnee de colonne au moins `gridColMin g`. -/
theorem gridColMin_le_of_mem (g : Grid) (p : Int × Int) (hp : p ∈ g) :
    gridColMin g ≤ p.2 := by
  cases g with
  | nil => simp at hp
  | cons p₀ ps =>
    simp only [gridColMin]
    by_cases heq : p = p₀
    · rw [heq]
      exact foldl_proj_min_le_seed ps (·.2) p₀.2
    · have hps : p ∈ ps := by
        rcases List.mem_cons.mp hp with hhead | hps
        · exact absurd hhead heq
        · exact hps
      exact foldl_proj_min_le_of_mem ps (·.2) p₀.2 p hps

/-- Toute cellule de `g` a une coordonnee de colonne au plus `gridColMax g`. -/
theorem le_gridColMax_of_mem (g : Grid) (p : Int × Int) (hp : p ∈ g) :
    p.2 ≤ gridColMax g := by
  cases g with
  | nil => simp at hp
  | cons p₀ ps =>
    simp only [gridColMax]
    by_cases heq : p = p₀
    · rw [heq]
      exact le_foldl_proj_max_seed ps (·.2) p₀.2
    · have hps : p ∈ ps := by
        rcases List.mem_cons.mp hp with hhead | hps
        · exact absurd hhead heq
        · exact hps
      exact le_foldl_proj_max_of_mem ps (·.2) p₀.2 p hps

/-- Pour toute grille non vide, la boite englobante des lignes est bien
    formee : `gridRowMin g ≤ gridRowMax g`. -/
theorem gridRowMin_le_gridRowMax (g : Grid) (hg : g ≠ []) :
    gridRowMin g ≤ gridRowMax g := by
  obtain ⟨p₀, ps, rfl⟩ : ∃ p₀ ps, g = p₀ :: ps := by
    cases g with
    | nil => exact absurd rfl hg
    | cons p₀ ps => exact ⟨p₀, ps, rfl⟩
  have hmin : gridRowMin (p₀ :: ps) ≤ p₀.1 :=
    gridRowMin_le_of_mem _ _ (by simp)
  have hmax : p₀.1 ≤ gridRowMax (p₀ :: ps) :=
    le_gridRowMax_of_mem _ _ (by simp)
  omega

/-- Pour toute grille non vide, la boite englobante des colonnes est bien
    formee : `gridColMin g ≤ gridColMax g`. -/
theorem gridColMin_le_gridColMax (g : Grid) (hg : g ≠ []) :
    gridColMin g ≤ gridColMax g := by
  obtain ⟨p₀, ps, rfl⟩ : ∃ p₀ ps, g = p₀ :: ps := by
    cases g with
    | nil => exact absurd rfl hg
    | cons p₀ ps => exact ⟨p₀, ps, rfl⟩
  have hmin : gridColMin (p₀ :: ps) ≤ p₀.2 :=
    gridColMin_le_of_mem _ _ (by simp)
  have hmax : p₀.2 ≤ gridColMax (p₀ :: ps) :=
    le_gridColMax_of_mem _ _ (by simp)
  omega

/-- Aide generique : un `foldl` de `min` (via `proj`) est *atteint* — le
    resultat est soit le depart `acc`, soit la projection d'un element de la
    liste. Compagnon de `foldl_proj_min_le_seed`/`foldl_proj_min_le_of_mem`
    (ceux-ci donnent les bornes `≤` ; celui-ci donne le temoin). -/
theorem foldl_proj_min_attained (ps : Grid) (proj : Int × Int → Int) (acc : Int) :
    ps.foldl (fun m q => min m (proj q)) acc = acc ∨
      ∃ p ∈ ps, ps.foldl (fun m q => min m (proj q)) acc = proj p := by
  induction ps generalizing acc with
  | nil => left; rfl
  | cons q qs ih =>
    simp only [List.foldl_cons]
    rcases ih (min acc (proj q)) with h | ⟨p, hp, hval⟩
    · rcases le_total acc (proj q) with hle | hle
      · left; rw [h]; omega
      · right; exact ⟨q, by simp, by rw [h]; omega⟩
    · right; exact ⟨p, by simp [hp], hval⟩

/-- Le minimum de ligne d'une grille non vide est *atteint* par une cellule
    vivante : il existe un `p ∈ g` avec `p.1 = gridRowMin g`. C'est la forme
    temoin de `gridRowMin_le_of_mem` (necessaire pour extraire la cellule
    vivante la plus haute, ex. pour la borne de satisfiabilite structurelle
    sur `box_assez_grand`). -/
theorem gridRowMin_mem (g : Grid) (hg : g ≠ []) :
    ∃ p ∈ g, p.1 = gridRowMin g := by
  cases g with
  | nil => exact absurd rfl hg
  | cons p₀ ps =>
    simp only [gridRowMin]
    rcases foldl_proj_min_attained ps (·.1) p₀.1 with h | ⟨p, hp, hval⟩
    · exact ⟨p₀, by simp, h.symm⟩
    · exact ⟨p, by simp [hp], hval.symm⟩

/-- Calcule un `(offset, level)` adapte pour que le carre de cote
    `2 ^ level` place en `offset` contienne strictement la boite englobante
    de `g` plus un rembourrage de 2 cellules de chaque cote. Renvoie
    `((0, 0), 0)` pour la grille vide. -/
def gridFrame (g : Grid) : (Int × Int) × Nat :=
  match g with
  | []      => ((0, 0), 0)
  | _ :: _ =>
    let rMin := gridRowMin g
    let rMax := gridRowMax g
    let cMin := gridColMin g
    let cMax := gridColMax g
    -- rembourrage de 2 cellules de chaque cote
    let r0 := rMin - 2
    let c0 := cMin - 2
    let height := (rMax - rMin + 5).toNat   -- +1 pour inclusif, +4 pour le rembourrage
    let width  := (cMax - cMin + 5).toNat
    let side   := max height width
    let lvl    := MacroCell.ceilLog2 side
    ((r0, c0), lvl)

/-- Pour toute cellule vivante `p ∈ g`, le cadre choisi par `gridFrame g`
    contient `p` : `inRegion p r0 c0 lvl` ou `((r0, c0), lvl) = gridFrame g`.
    C'est le pont de containment pour l'aller-retour Grid↔MacroCell
    (issue #2162, Gap 2). -/
theorem gridFrame_contains_g (g : Grid) (p : Int × Int) (hp : p ∈ g) :
    let ((r0, c0), lvl) := gridFrame g
    MacroCell.inRegion p r0 c0 lvl := by
  cases g with
  | nil => simp at hp
  | cons p₀ ps =>
    have hrMin : gridRowMin (p₀ :: ps) ≤ p.1 := gridRowMin_le_of_mem _ _ hp
    have hrMax : p.1 ≤ gridRowMax (p₀ :: ps) := le_gridRowMax_of_mem _ _ hp
    have hcMin : gridColMin (p₀ :: ps) ≤ p.2 := gridColMin_le_of_mem _ _ hp
    have hcMax : p.2 ≤ gridColMax (p₀ :: ps) := le_gridColMax_of_mem _ _ hp
    have hrnn : gridRowMin (p₀ :: ps) ≤ gridRowMax (p₀ :: ps) :=
      gridRowMin_le_gridRowMax _ (List.cons_ne_nil _ _)
    have hcnn : gridColMin (p₀ :: ps) ≤ gridColMax (p₀ :: ps) :=
      gridColMin_le_gridColMax _ (List.cons_ne_nil _ _)
    simp only [gridFrame]
    set rMin := gridRowMin (p₀ :: ps)
    set rMax := gridRowMax (p₀ :: ps)
    set cMin := gridColMin (p₀ :: ps)
    set cMax := gridColMax (p₀ :: ps)
    set height := (rMax - rMin + 5).toNat
    set width := (cMax - cMin + 5).toNat
    set side := max height width
    set lvl := MacroCell.ceilLog2 side
    have hspec : (2 ^ lvl : Nat) ≥ side := MacroCell.ceilLog2_spec side
    have hh : height ≤ side := Nat.le_max_left _ _
    have hw : width ≤ side := Nat.le_max_right _ _
    have hnn_r : 0 ≤ rMax - rMin + 5 := by omega
    have hnn_c : 0 ≤ cMax - cMin + 5 := by omega
    unfold MacroCell.inRegion
    refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-! ### Cadrage conscient de n (`gridFrameN`) — porte N1 de la refonte P5 (issue #3846)

Le rembourrage fixe a 2 de `gridFrame` plafonne la marge du cone de lumiere
a 2 (voir `boxAssezGrand_nonempty_le_two` dans `HashlifeCorrectness`) : avec
`r0 := rMin - 2`, la cellule vivante la plus haute a une marge d'exactement
2, donc `BoxAssezGrand g n` force `n ≤ 2` et est *insatisfiable* pour les
grands `n`. C'est la racine structurelle de l'obstruction P5 des grands `n`.

`gridFrameN n g` generalise le rembourrage en `max 2 n`, donc la marge du
cone de lumiere est au moins `max 2 n ≥ n` *par construction*. L'hypothese
de marge devient alors satisfiable pour tout `n` (pas seulement `n ≤ 2`) —
voir le temoin `box_assez_grandN_single_cell_3` dans
`HashlifeCorrectness`, le dual honnete du plafond insat
`boxAssezGrand_nonempty_le_two`. N1 garde `evolveHashlifeFast` inchange ;
N2 trame ce cadre a travers la boucle sans re-cadrer. -/

/-- Comme `gridFrame` mais avec un rembourrage `max 2 n` (au lieu du `2`
    fixe) de chaque cote, donc la marge du cone de lumiere est au moins
    `max 2 n ≥ n`. Renvoie `((0, 0), 0)` pour la grille vide. (Refonte P5,
    issue #3846, porte N1.) -/
def gridFrameN (n : Nat) (g : Grid) : (Int × Int) × Nat :=
  match g with
  | []      => ((0, 0), 0)
  | _ :: _ =>
    let rMin := gridRowMin g
    let rMax := gridRowMax g
    let cMin := gridColMin g
    let cMax := gridColMax g
    let pad  := max 2 n
    let r0 := rMin - pad
    let c0 := cMin - pad
    let height := (rMax - rMin + 1 + 2 * pad).toNat
    let width  := (cMax - cMin + 1 + 2 * pad).toNat
    let side   := max height width
    let lvl    := MacroCell.ceilLog2 side
    ((r0, c0), lvl)

/-- Pour toute cellule vivante `p ∈ g`, le cadre choisi par `gridFrameN n g`
    contient `p` (pont de containment, analogue conscient de n de
    `gridFrame_contains_g`). -/
theorem gridFrameN_contains_g (n : Nat) (g : Grid) (p : Int × Int) (hp : p ∈ g) :
    let ((r0, c0), lvl) := gridFrameN n g
    MacroCell.inRegion p r0 c0 lvl := by
  cases g with
  | nil => simp at hp
  | cons p₀ ps =>
    have hrMin : gridRowMin (p₀ :: ps) ≤ p.1 := gridRowMin_le_of_mem _ _ hp
    have hrMax : p.1 ≤ gridRowMax (p₀ :: ps) := le_gridRowMax_of_mem _ _ hp
    have hcMin : gridColMin (p₀ :: ps) ≤ p.2 := gridColMin_le_of_mem _ _ hp
    have hcMax : p.2 ≤ gridColMax (p₀ :: ps) := le_gridColMax_of_mem _ _ hp
    have hrnn : gridRowMin (p₀ :: ps) ≤ gridRowMax (p₀ :: ps) :=
      gridRowMin_le_gridRowMax _ (List.cons_ne_nil _ _)
    have hcnn : gridColMin (p₀ :: ps) ≤ gridColMax (p₀ :: ps) :=
      gridColMin_le_gridColMax _ (List.cons_ne_nil _ _)
    simp only [gridFrameN]
    set rMin := gridRowMin (p₀ :: ps)
    set rMax := gridRowMax (p₀ :: ps)
    set cMin := gridColMin (p₀ :: ps)
    set cMax := gridColMax (p₀ :: ps)
    set pad := max 2 n
    set height := (rMax - rMin + 1 + 2 * pad).toNat
    set width := (cMax - cMin + 1 + 2 * pad).toNat
    set side := max height width
    set lvl := MacroCell.ceilLog2 side
    have hspec : (2 ^ lvl : Nat) ≥ side := MacroCell.ceilLog2_spec side
    have hh : height ≤ side := Nat.le_max_left _ _
    have hw : width ≤ side := Nat.le_max_right _ _
    have hnn_r : 0 ≤ rMax - rMin + 1 + 2 * pad := by omega
    have hnn_c : 0 ≤ cMax - cMin + 1 + 2 * pad := by omega
    unfold MacroCell.inRegion
    refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-- `gridFrameN n g` se reduit en `gridFrame g` quand `n ≤ 2` : le
    rembourrage conscient de n `max 2 n` egale le rembourrage fixe `2`, donc
    les deux cadres coincident. C'est le pont de reduction montrant que
    `gridFrameN` generalise strictement `gridFrame` — il laisse les resultats
    existants bases sur `gridFrame` se transferer au cadre conscient de n pour
    les petits `n` (tramage N3, issue #3846). -/
theorem gridFrameN_le_two_eq_gridFrame (n : Nat) (g : Grid) (hn : n ≤ 2) :
    gridFrameN n g = gridFrame g := by
  have hpad : max 2 n = 2 := by omega
  cases g with
  | nil => rfl
  | cons p₀ ps =>
    -- Etablir la non-negativite des portees ligne/col directement (pas d'alias
    -- `set`, pour que `omega` relie ces faits aux termes du but `gridRowMin _` etc.).
    have hrnn : gridRowMin (p₀ :: ps) ≤ gridRowMax (p₀ :: ps) :=
      gridRowMin_le_gridRowMax _ (List.cons_ne_nil _ _)
    have hcnn : gridColMin (p₀ :: ps) ≤ gridColMax (p₀ :: ps) :=
      gridColMin_le_gridColMax _ (List.cons_ne_nil _ _)
    simp only [gridFrameN, gridFrame, hpad, Nat.cast_two]
    -- Les deux cadres ont maintenant un rembourrage de 2 ; la seule difference
    -- residuelle est `+ 1 + 2*2` (gridFrameN) contre `+ 5` (gridFrame) dans la
    -- hauteur/largeur, une identite arithmetique pure Int. La paire de decalage
    -- `(r0, c0)` coincide par `rfl`. Fermer la paire de decalage `(r0, c0)` par
    -- `Prod.ext` + `rfl` (pas de `congr` sur la soustraction, qui
    -- sur-decomposerait). L'egalite des niveaux se reduit aux identites
    -- `toNat` de hauteur/largeur `(x + 1 + 2*2).toNat = (x + 5).toNat`, que
    -- `omega` ferme en utilisant les faits de non-negativite ci-dessus.
    refine Prod.ext ?_ ?_
    · rfl
    · have hH : (gridRowMax (p₀ :: ps) - gridRowMin (p₀ :: ps) + 1 + 2 * 2).toNat
                  = (gridRowMax (p₀ :: ps) - gridRowMin (p₀ :: ps) + 5).toNat := by omega
      have hW : (gridColMax (p₀ :: ps) - gridColMin (p₀ :: ps) + 1 + 2 * 2).toNat
                  = (gridColMax (p₀ :: ps) - gridColMin (p₀ :: ps) + 5).toNat := by omega
      rw [hH, hW]

/-- Convertit un `Grid` en `MacroCell`, en renvoyant le decalage choisi pour
    que `MacroCell.toGrid offset (gridToMacroCell g) = g`. -/
def gridToMacroCellWithOffset (g : Grid) : (Int × Int) × MacroCell :=
  let (off, lvl) := gridFrame g
  (off, MacroCell.buildFromGrid g off.1 off.2 lvl)

/-- Variante consciente de n de `gridToMacroCellWithOffset` : construit la
    `MacroCell` a partir du cadre conscient de n `gridFrameN n g` (rembourrage
    `max 2 n`), plutot que le `gridFrame` a rembourrage fixe. C'est le
    constructeur d'offset/MacroCell que le tramage N3 de
    `evolveHashlifeFast` (issue #3846) substitue a `gridToMacroCellWithOffset`
    pour tramer le cadre conscient de n a travers la boucle de recursion. -/
def gridToMacroCellWithOffsetN (n : Nat) (g : Grid) : (Int × Int) × MacroCell :=
  let (off, lvl) := gridFrameN n g
  (off, MacroCell.buildFromGrid g off.1 off.2 lvl)

/-- `gridToMacroCellWithOffsetN n g` se reduit en
    `gridToMacroCellWithOffset g` quand `n ≤ 2` : comme
    `gridFrameN n g = gridFrame g` pour les petits `n`
    (`gridFrameN_le_two_eq_gridFrame`), les deux constructeurs fournissent le
    meme decalage et niveau a `buildFromGrid`. Cela fait le pont entre le
    constructeur a cadre fixe utilise par l'actuel `evolveHashlifeFast` et sa
    variante consciente de n, donc la substitution du tramage N3 est
    transparente comportementalement pour les petits `n` (issue #3846). -/
theorem gridToMacroCellWithOffsetN_le_two_eq (n : Nat) (g : Grid) (hn : n ≤ 2) :
    gridToMacroCellWithOffsetN n g = gridToMacroCellWithOffset g := by
  unfold gridToMacroCellWithOffsetN gridToMacroCellWithOffset
  rw [gridFrameN_le_two_eq_gridFrame n g hn]

/-- Convertit un `Grid` en `MacroCell`, en jetant le decalage (par defaut
    `(0, 0)` pour l'aller-retour). Pour les besoins d'aller-retour, preferer
    `gridToMacroCellWithOffset`. -/
def gridToMacroCell (g : Grid) : MacroCell :=
  (gridToMacroCellWithOffset g).2

/-- **Aller-retour Grid -> MacroCell -> Grid (appartenance)** : pour tout
    point `p`, `p` est vivant dans la grille reconstruite
    `(gridToMacroCellWithOffset g).2.toGrid (gridToMacroCellWithOffset g).1`
    ssi `p` est vivant dans `g`. C'est la forme generale du but annonce par
    le docstring de `gridToMacroCellWithOffset`, jusqu'ici verifie seulement
    par `#eval` sur les motifs canoniques (Tests de coherence ci-dessous).

    Assemble `mem_toCellsAux_buildFromGrid` (l'enumeration de
    `buildFromGrid` dans le carre couvert est exactement `inRegion /\ p ∈ g`)
    avec `gridFrame_contains_g` (toute cellule vivante de `g` est dans le
    carre du cadre). Direction -> : les membres de l'enumeration sont dans
    `g`. Direction <- : les membres de `g` sont dans le carre, donc dans
    l'enumeration.

    C'est la brique BR1 du pont de localite (a) de `p5_large_n_jumpN`
    (#6724) : elle identifie `mc.toGrid off` a `g` au niveau des membres,
    ce qui permet de transporter les evolutions de l'un a l'autre via
    `toGrid_shift_between` (Foundation) et `evolve_shift` (GridCanonical). -/
theorem mem_toGrid_gridToMacroCellWithOffset (g : Grid) (p : Int × Int) :
    p ∈ (gridToMacroCellWithOffset g).2.toGrid (gridToMacroCellWithOffset g).1 ↔ p ∈ g := by
  cases hF : gridFrame g with
  | mk off lvl =>
    simp only [gridToMacroCellWithOffset, hF, MacroCell.toGrid, mem_sortDedup]
    rw [MacroCell.mem_toCellsAux_buildFromGrid g lvl off.1 off.2 p]
    constructor
    · exact fun h => h.2
    · intro hp
      refine ⟨?_, hp⟩
      have hreg := gridFrame_contains_g g p hp
      rw [hF] at hreg
      exact hreg

/-! ## Tests de coherence

Nous verifions que l'aller-retour `Grid -> MacroCell -> Grid` preserve les
petits motifs canoniques de `Conway.Life`. -/

-- Aides de boite englobante
#eval gridRowMin block
#eval gridRowMax block
#eval gridFrame block

-- La grille vide devrait donner une feuille morte de niveau 0.
#eval gridToMacroCell ([] : Grid) |>.level
#eval gridToMacroCell ([] : Grid) |>.isEmpty

-- Aller-retour sur le block : la MacroCell, puis de retour vers une grille
-- au decalage choisi, devrait egaler `block`.
#eval
  let (off, mc) := gridToMacroCellWithOffset block
  (off, mc.level, mc.toGrid off == block)

#eval
  let (off, mc) := gridToMacroCellWithOffset blinker_h
  (off, mc.level, mc.toGrid off == blinker_h)

#eval
  let (off, mc) := gridToMacroCellWithOffset glider
  (off, mc.level, mc.toGrid off == glider)

#eval
  let (off, mc) := gridToMacroCellWithOffset beehive
  (off, mc.level, mc.toGrid off == beehive)

#eval
  let (off, mc) := gridToMacroCellWithOffset toad
  (off, mc.level, mc.toGrid off == toad)

end Life
end Conway
