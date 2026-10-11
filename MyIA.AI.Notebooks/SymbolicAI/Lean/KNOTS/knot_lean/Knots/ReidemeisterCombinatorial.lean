/-
Knots.ReidemeisterCombinatorial — Suite de mouvements de Reidemeister vérifiable
================================================================================

Issue d'infrastructure (Epic #1453, point 3) : organe manquant derrière les
`sorry` restants de `knot_lean` (Reidemeister.lean:1056, Lidman.lean:81) —
une **suite de mouvements de Reidemeister vérifiable par le noyau**.

Pourquoi ce module est séparé de `Knots.Reidemeister` : la machinerie RTC
(`ReidemeisterEquiv`) est déjà en place (inductifs `ReidemeisterStep` et
`ReidemeisterEquiv`, lemmes `*.symm`, `reidemeister_equiv_symm`,
`reidemeister_equiv_equivalence`). Ce qu'il manque, c'est la **colonne
vertébrale algorithmique** :

  1. un **inductif indexé** `MoveSequence` (`KnotDiagram → KnotDiagram → Type`)
     qui porte la cohérence structurelle des suites (le typeur refuse toute
     liste dont le dernier pas n'aboutit pas au `d₃` annoncé),
  2. un constructeur `movesConnects` qui scelle la RTC en un témoin compact,
  3. un vérificateur **décidable borné** `verifyMoves` qui, pour un budget `n`
     de mouvements autorisés, énumère toutes les suites de R1/R2/R3 et
     retourne `true` si l'une d'elles relie deux diagrammes. Borné pour rester
     décidable ; l'énumération complète est `O((crossings+1)^n)`,
  4. la **soundness** du vérificateur : si `verifyMoves n d₁ d₂ = true`, alors
     `ReidemeisterEquiv d₁ d₂`. C'est la cible des passes prouveur subséquentes.

Ce que ce module **ne fait pas** :
- il ne prouve pas le théorème de Reidemeister profond (`reidemeister_theorem`,
  Reidemeister.lean:1053) qui exige PL-manifolds/S³/abs.isotopie — la
  soundness du vérificateur donne seulement le côté **combinatoire** (« ⇐ »
  ReidemeisterEquiv → ambient_isotopic reste hors juridiction) ;
- il ne s'attaque pas aux `sorry` permanents de `Knots.Slice` (Conway,
  Piccirillo, Freedman), marqués explicitement « decades away from formalization »
  par les sections précédentes — ces énoncés vivent dans une théorie
  4-manifolds / Khovanov / Kirby que Mathlib n'a pas.

Cible Lidman:81 — `unknotting_11n102_upper` — **devient accessible** une fois
ce module en place : on exhibe une `MoveSequence` reliant
`(changeCrossingAt c₁ (changeCrossingAt c₂ knot_11n102)).diagram` au
`unknotDiagram`, et `verifyMoves_sound` (à prouver par passe prouveur sur ce
module) scelle l'implication.

Convention i18n (EPIC #4980, décision user 2026-07-04) : ce fichier est **FR
canonique**, avec son miroir anglais dans le sibling `ReidemeisterCombinatorial_en.lean`
(modèle sibling pair ratifié 2026-07-04). Les énoncés de théorèmes, les
tactiques Lean, les noms de lemmes et les références Mathlib restent en anglais
(compat Mathlib 4) ; seules les docstrings de module et ce bloc d'en-tête
diffèrent entre les deux fichiers.

Statut : l'énumération réelle des témoins à un mouvement est en place
(`#19890` — R1/R2 avant et arrière, R3 avant), `oneStepWitnesses_sound`
est prouvé par construction, et `verifyMoves_sound` est totale. Le témoin
concret `Lidman:81` (`unknotting_11n102_upper`) reste la cible des passes
suivantes, et l'inverse du move R3 est un travail futur documenté.
-/

import Knots.Reidemeister
import Knots.Invariant

namespace Knots

/-! ## 1. Suite de mouvements — inductive indexé

`MoveSequence` est un **inductif indexé** `KnotDiagram → KnotDiagram → Type`
(et non un alias `List ReidemeisterStep`) : un constructeur `nil` réflexif et
un constructeur `cons` qui chaîne un pas `ReidemeisterStep` avec la queue.

L'indexation par `KnotDiagram` aux deux bouts impose la cohérence structurelle
des suites : `cons` exige `step : ReidemeisterStep d₁ d₂` et
`tail : MoveSequence d₂ d₃`, donc le typeur refuse toute liste dont le dernier
pas n'aboutit pas au `d₃` annoncé.

Convention : l'ordre est « gauche → droite » — `cons step tail` signifie
« appliquer `step` d'abord, puis `tail` ».
-/

/-- Suite finie de mouvements de Reidemeister.

Inductif indexé sur deux `KnotDiagram` : le type porte la garantie que la
concaténation des pas relie bien `d₁` à `d₂`.
-/
inductive MoveSequence : KnotDiagram → KnotDiagram → Type where
  /-- Suite vide : un diagramme se relie trivialement à lui-même. -/
  | nil (d : KnotDiagram) : MoveSequence d d
  /-- Enchaîner un pas `ReidemeisterStep d₁ d₂` avec une suite `MoveSequence d₂ d₃`. -/
  | cons {d₁ d₂ d₃ : KnotDiagram}
      (step : ReidemeisterStep d₁ d₂)
      (tail : MoveSequence d₂ d₃) :
      MoveSequence d₁ d₃

/-! ## 2. Reconstruction RTC et soundness

`movesConnects` scelle une `MoveSequence` en une preuve de `ReidemeisterEquiv`
: c'est l'inverse du constructeur `ReidemeisterEquiv.step` rendu composable.
La récurrence structurelle sur l'inductif indexé force la cohérence des
diagrammes en bout de chaîne.
-/

/-- Une suite de mouvements connecte `d₁` à `d₂` au sens de `ReidemeisterEquiv`.

Reconstruction par récurrence sur la `MoveSequence` :
- `nil` (suite vide) → `ReidemeisterEquiv.refl d₁`,
- `cons step tail` → `ReidemeisterEquiv.trans (ReidemeisterEquiv.step step)
  (movesConnects d₂ d₃ tail)`.

La définition est **non-récursive à droite** : `movesConnects d₂ d₃ tail` est
calculé avant d'être consommé par le `trans`, ce qui rend l'évaluation
terminaison-safe sous `decreasing_by wf_tacs`.
-/
def movesConnects {d₁ d₂ : KnotDiagram} :
    MoveSequence d₁ d₂ → ReidemeisterEquiv d₁ d₂
  | .nil d => ReidemeisterEquiv.refl d
  | .cons step tail =>
    ReidemeisterEquiv.trans
      (ReidemeisterEquiv.step step)
      (movesConnects tail)

/-! ## 2.1. Soundness triviale de la RTC

`movesConnects` _construit_ la RTC, donc sa soundness est l'identité. C'est
l'API stable pour les consommateurs (cf. `Knots.Lidman`).
-/

/-- Soundness triviale par construction : `movesConnects` _est_ la RTC. -/
theorem movesConnects_sound {d₁ d₂ : KnotDiagram}
    (ms : MoveSequence d₁ d₂) : ReidemeisterEquiv d₁ d₂ :=
  movesConnects ms

/-! ## 3. Vérificateur décidable borné

`verifyMovesAux` énumère les suites de longueur au plus `n` et décide si
l'une d'elles relie `d₁` à `d₂`. La décision est **décidable** (retourne un
`Bool`) — c'est l'instrument des passes prouveur qui n'ont pas accès à
l'orchestration tactic `decide` sur l'espace des suites infinies.

L'algorithme est volontairement naïf (énumération exhaustive) : pour les
bornes utiles en pratique (n ≤ 4), le branching factor reste dominé par
`(crossings+1) × 3` (R1/R2/R3 × double-sens) et le coût reste en
`O((3(numCrossings+1))^n)`. Les passes prouveur ultérieures raffineront en
évitant les symétries triviales (`ReidemeisterEquiv.symm`, `trans`).
-/

/-- Vue d'un `ReidemeisterStep` sous forme de constructeur pur (sans `d₂`
existentiel). Utilisée par l'algorithme pour reconstruire le diagramme cible
à chaque pas. -/
def ReidemeisterStep.toWitness (d₁ : KnotDiagram) (d₂ : KnotDiagram)
    (h : (Reidemeister1Connected d₁ d₂ ∨ Reidemeister1Connected d₂ d₁
       ∨ Reidemeister2Connected d₁ d₂ ∨ Reidemeister2Connected d₂ d₁
       ∨ Reidemeister3Connected d₁ d₂ ∨ Reidemeister3Connected d₂ d₁)) :
    ReidemeisterStep d₁ d₂ :=
  -- Distributivité du `∨` : la conjonction est soit R1, R2, soit R3,
  -- et dans chaque cas la direction est forward ou backward.
  -- La reconstruction est partielle : on accepte n'importe quel témoin
  -- `h` et on pattern-match pour choisir le bon constructeur de
  -- `ReidemeisterStep`. Le `_` est explicite pour signaler que la
  -- reconstruction n'est pas toujours unique (forward/backward symétriques).
  by
    rcases h with h | h | h | h | h | h
    · exact ReidemeisterStep.r1 (Or.inl h)
    · exact ReidemeisterStep.r1 (Or.inr h)
    · exact ReidemeisterStep.r2 (Or.inl h)
    · exact ReidemeisterStep.r2 (Or.inr h)
    · exact ReidemeisterStep.r3 (Or.inl h)
    · exact ReidemeisterStep.r3 (Or.inr h)

/-! ## 3bis. Énumération réelle des témoins à un mouvement (`#19890`)

Le principe : chaque candidat est construit **avec sa preuve** (`StepWitness`),
si bien que la soundness de l'énumération est **par construction** — elle se
réduit à `List.mem_map` dans `oneStepWitnesses_sound`, jamais re-devinée
depuis le seul diagramme cible.

Portée de l'énumération :
- **R1** : torsions connectées AVANT (ajout d'un kink sur un arc propre) et
  ARRIÈRE (contraction d'un kink terminal) ;
- **R2** : bigons AVANT et ARRIÈRE (contraction d'une paire de kinks
  terminale) ;
- **R3** : moves triangulaires AVANT — la direction inverse est un travail
  futur documenté sur `Reidemeister3Connected` (le move n'est pas symétrique
  par construction : la bijection à Sat égal n'est pas involutive).

Chaque candidat est filtré par les gardes décidables exactes de la relation
(`wf` des deux côtés, `Nodup` des labels R3, forme kink pour les
contractions) : un candidat mal formé n'est tout simplement pas émis — la
liste ne contient QUE des successeurs authentiques.

Les générateurs de renommage (`renameOptsWith` & co.) sont eux-mêmes
porteurs de preuve : chaque option de slot est émise AVEC la disjonction qui
la justifie dans `isRenameOf` / `isDoubleRenameOf`, ce qui évite tout lemme
d'appartenance a posteriori.
-/

/-- Un témoin d'un mouvement : le diagramme cible et la preuve du
`ReidemeisterStep`, construits au même site d'énumération. -/
structure StepWitness (d : KnotDiagram) where
  /-- Diagramme accessible depuis `d` par un unique `ReidemeisterStep`. -/
  target : KnotDiagram
  /-- Preuve du step, fabriquée à l'énumération. -/
  proof : ReidemeisterStep d target

/-- Plongement canonique `Fin n ↪ Fin (n + m)` : les labels frais d'une
chirurgie prennent les rangées `n+1, …, n+m` (ρ de witnessing trivial,
toujours constructible). -/
def finEmbed (n m : Nat) : Fin n ↪ Fin (n + m) where
  toFun j := ⟨j.val, by omega⟩
  inj' x y h := by injection h with hv; exact Fin.ext hv

/-- Réécrire un slot à sa valeur courante ne change pas la liste. -/
theorem list_set_current {l : List PDCrossing} {i : Nat}
    (h : i < l.length) : l.set i (l.get ⟨i, h⟩) = l := by
  induction l generalizing i with
  | nil => simp at h
  | cons x xs ih =>
    match i with
    | 0 => rfl
    | i + 1 =>
      exact congrArg (List.cons x) (ih (by simp only [List.length_cons] at h; omega))

/-- Forme généralisée : réécrire le slot `i` en une valeur égale à la
courante ne change pas la liste. -/
theorem list_set_eq {l : List PDCrossing} {i : Nat} {x : PDCrossing}
    (h : i < l.length) (hx : l.get ⟨i, h⟩ = x) : l.set i x = l := by
  rw [← hx]; exact list_set_current h

/-- Lire le slot `i` juste après l'y avoir écrit rend la valeur écrite. -/
theorem list_get_set_self {l : List PDCrossing} {i : Nat} (a : PDCrossing)
    (h : i < (l.set i a).length) : (l.set i a).get ⟨i, h⟩ = a := by
  rw [List.get_eq_getElem, List.getElem_set_self]

/-- Options d'un slot pour `isRenameOf c a b` (R1 avant) : un slot valant
`a` peut se préserver ou devenir `b` ; tout autre slot se préserve. Chaque
option est émise avec sa preuve. -/
def renameOptsWith (x a b : Nat) : List { y : Nat // y = x ∨ (y = b ∧ x = a) } :=
  if hx : x = a then
    [⟨x, Or.inl rfl⟩, ⟨b, Or.inr ⟨rfl, hx⟩⟩]
  else
    [⟨x, Or.inl rfl⟩]

/-- Options d'un slot pour `isDoubleRenameOf c a o₁ o₂` (R2 avant) : un slot
valant `a` peut se préserver, devenir `o₁` ou `o₂`. -/
def rename2OptsWith (x a o₁ o₂ : Nat) :
    List { y : Nat // y = x ∨ (y = o₁ ∧ x = a) ∨ (y = o₂ ∧ x = a) } :=
  if hx : x = a then
    [⟨x, Or.inl rfl⟩, ⟨o₁, Or.inr (Or.inl ⟨rfl, hx⟩)⟩, ⟨o₂, Or.inr (Or.inr ⟨rfl, hx⟩)⟩]
  else
    [⟨x, Or.inl rfl⟩]

/-- Options inverses d'un slot (contraction R1) : pour `Y'` connu, les
valeurs source `x` telles que le slot renommé vaille `y`. -/
def unRenameOptsWith (y b a : Nat) : List { x : Nat // y = x ∨ (y = b ∧ x = a) } :=
  if hy : y = b then
    [⟨y, Or.inl rfl⟩, ⟨a, Or.inr ⟨hy, rfl⟩⟩]
  else
    [⟨y, Or.inl rfl⟩]

/-- Options inverses doubles d'un slot (contraction R2). -/
def unRename2Opts (y o₁ o₂ a : Nat) :
    List { x : Nat // y = x ∨ (y = o₁ ∧ x = a) ∨ (y = o₂ ∧ x = a) } :=
  if hy : y = o₁ then
    [⟨y, Or.inl rfl⟩, ⟨a, Or.inr (Or.inl ⟨hy, rfl⟩)⟩]
  else if hy2 : y = o₂ then
    [⟨y, Or.inl rfl⟩, ⟨a, Or.inr (Or.inr ⟨hy2, rfl⟩)⟩]
  else
    [⟨y, Or.inl rfl⟩]

/-- Tous les renommés R1 de `c`, preuve `isRenameOf` attachée. -/
def PDCrossing.allRenamesWith (c : PDCrossing) (a b : Nat) :
    List { Y : PDCrossing // Y.isRenameOf c a b } :=
  (renameOptsWith c.e1 a b).flatMap fun e1 =>
    (renameOptsWith c.e2 a b).flatMap fun e2 =>
      (renameOptsWith c.e3 a b).flatMap fun e3 =>
        (renameOptsWith c.e4 a b).map fun e4 =>
          ⟨⟨e1.1, e2.1, e3.1, e4.1⟩, ⟨e1.2, e2.2, e3.2, e4.2⟩⟩

/-- Tous les double-renommés R2 de `c`, preuve attachée. -/
def PDCrossing.allDoubleRenamesWith (c : PDCrossing) (a o₁ o₂ : Nat) :
    List { Y : PDCrossing // Y.isDoubleRenameOf c a o₁ o₂ } :=
  (rename2OptsWith c.e1 a o₁ o₂).flatMap fun e1 =>
    (rename2OptsWith c.e2 a o₁ o₂).flatMap fun e2 =>
      (rename2OptsWith c.e3 a o₁ o₂).flatMap fun e3 =>
        (rename2OptsWith c.e4 a o₁ o₂).map fun e4 =>
          ⟨⟨e1.1, e2.1, e3.1, e4.1⟩, ⟨e1.2, e2.2, e3.2, e4.2⟩⟩

/-- Toutes les sources `Y` dont `Y'` est le renommé R1 (contraction), preuve
attachée. -/
def PDCrossing.allUnRenamesWith (Y' : PDCrossing) (a b : Nat) :
    List { Y : PDCrossing // Y'.isRenameOf Y a b } :=
  (unRenameOptsWith Y'.e1 b a).flatMap fun e1 =>
    (unRenameOptsWith Y'.e2 b a).flatMap fun e2 =>
      (unRenameOptsWith Y'.e3 b a).flatMap fun e3 =>
        (unRenameOptsWith Y'.e4 b a).map fun e4 =>
          ⟨⟨e1.1, e2.1, e3.1, e4.1⟩, ⟨e1.2, e2.2, e3.2, e4.2⟩⟩

/-- Toutes les sources `Y` dont `Y'` est le double-renommé R2 (contraction). -/
def PDCrossing.allUnDoubleRenamesWith (Y' : PDCrossing) (a o₁ o₂ : Nat) :
    List { Y : PDCrossing // Y'.isDoubleRenameOf Y a o₁ o₂ } :=
  (unRename2Opts Y'.e1 o₁ o₂ a).flatMap fun e1 =>
    (unRename2Opts Y'.e2 o₁ o₂ a).flatMap fun e2 =>
      (unRename2Opts Y'.e3 o₁ o₂ a).flatMap fun e3 =>
        (unRename2Opts Y'.e4 o₁ o₂ a).map fun e4 =>
          ⟨⟨e1.1, e2.1, e3.1, e4.1⟩, ⟨e1.2, e2.2, e3.2, e4.2⟩⟩

/-- Arcs candidats de `d` (bornes et appartenance prouvées). -/
def arcCandidatesWith (d : KnotDiagram) :
    List { a : Nat // 1 ≤ a ∧ a ≤ d.numEdges ∧ a ∈ d.edges } :=
  d.edges.attach.flatMap fun a =>
    if h : 1 ≤ a.1 ∧ a.1 ≤ d.numEdges then [⟨a.1, h.1, h.2, a.2⟩] else []

/-- Témoins d'arc propre : indices `j ≠ i` dont le croisement porte l'arc
`a` (garde anti-monogone de `Reidemeister1Connected`). -/
def properArcWitnesses (d : KnotDiagram) (i : Fin d.crossings.length) (a : Nat) :
    List { j : Fin d.crossings.length // j ≠ i ∧ (d.crossings.get j).hasEdge a } :=
  (List.finRange d.crossings.length).filterMap fun j =>
    if hij : j = i then none
    else if hhas : (d.crossings.get j).e1 = a ∨ (d.crossings.get j).e2 = a
                ∨ (d.crossings.get j).e3 = a ∨ (d.crossings.get j).e4 = a
    then some ⟨j, hij, hhas⟩
    else none

/-- R1 AVANT : torsion connectée sur chaque arc propre de chaque croisement. -/
def r1ForwardWitnesses (d : KnotDiagram) : List (StepWitness d) :=
  (List.finRange d.crossings.length).flatMap fun i =>
    (arcCandidatesWith d).flatMap fun a =>
      (properArcWitnesses d i a.1).flatMap fun _j =>
        ((d.crossings.get i).allRenamesWith a.1 (d.numEdges + 1)).flatMap fun Y' =>
          let d₂ : KnotDiagram :=
            { crossings := d.crossings.set i.val Y'.1 ++
                [⟨a.1, d.numEdges + 1, d.numEdges + 2, d.numEdges + 2⟩]
            , numEdges := d.numEdges + 2 }
          if hwf : d.wf = true ∧ d₂.wf = true then
            [{ target := d₂
             , proof := ReidemeisterStep.r1 (Or.inl
                 ⟨hwf.1, hwf.2, i, a.1, Y'.1, finEmbed d.numEdges 2,
                   a.2.1, a.2.2.1, a.2.2.2, ⟨_j.1, _j.2.1, _j.2.2⟩,
                   Y'.2, rfl, rfl⟩) }]
          else []

/-- R1 ARRIÈRE : contraction d'un kink terminal `⟨a, n-1, n, n⟩` (n =
`d.numEdges`) — énumère les sources `Y₀` dont le croisement modifié `Y'` de
`d` est le renommé. -/
def r1BackwardWitnesses (d : KnotDiagram) : List (StepWitness d) :=
  match hlast : d.crossings.getLast? with
  | some kink =>
    if hk : kink.e2 = d.numEdges - 1 ∧ kink.e3 = d.numEdges ∧ kink.e4 = d.numEdges
        ∧ 2 ≤ d.numEdges then
      (List.finRange d.crossings.length).flatMap fun (i : Fin d.crossings.length) =>
        if hilt : i.val < d.crossings.length - 1 then
          have hdl : i.val < d.crossings.dropLast.length := by
            simp only [List.length_dropLast]; omega
          let Y' := d.crossings.dropLast.get ⟨i.val, hdl⟩
          (Y'.allUnRenamesWith kink.e1 (d.numEdges - 1)).flatMap fun Y₀ =>
            let d' : KnotDiagram :=
              { crossings := d.crossings.dropLast.set i.val Y₀.1
              , numEdges := d.numEdges - 2 }
            have hdlen : i.val < d'.crossings.length := by
              change i.val < (d.crossings.dropLast.set i.val Y₀.1).length
              rw [List.length_set]; exact hdl
            if ha : 1 ≤ kink.e1 ∧ kink.e1 ≤ d.numEdges - 2 ∧ kink.e1 ∈ d'.edges then
              (properArcWitnesses d' ⟨i.val, hdlen⟩ kink.e1).flatMap fun _j =>
                if hwf : d'.wf = true ∧ d.wf = true then
                  [{ target := d'
                   , proof := by
                       have hY'get : d'.crossings.get ⟨i.val, hdlen⟩ = Y₀.1 := by
                         change (d.crossings.dropLast.set i.val Y₀.1).get ⟨i.val, hdlen⟩
                           = Y₀.1
                         rw [List.get_eq_getElem, List.getElem_set_self]
                       have hkink : kink = ⟨kink.e1, d.numEdges - 1, d.numEdges, d.numEdges⟩ := by
                         rw [show kink = ⟨kink.e1, kink.e2, kink.e3, kink.e4⟩ from rfl,
                             hk.1, hk.2.1, hk.2.2.1]
                       refine ReidemeisterStep.r1 (Or.inr
                         ⟨hwf.1, hwf.2, ⟨i.val, hdlen⟩, kink.e1, Y', finEmbed _ 2,
                           ha.1, ha.2.1, ha.2.2, ⟨_j.1, _j.2.1, _j.2.2⟩, ?_, ?_, ?_⟩)
                       · rw [hY'get,
                           show d'.numEdges + 1 = d.numEdges - 1 by
                             show d.numEdges - 2 + 1 = d.numEdges - 1; omega]
                         exact Y₀.2
                       · show d.crossings =
                           d'.crossings.set i.val Y' ++
                             [⟨kink.e1, d'.numEdges + 1, d'.numEdges + 2, d'.numEdges + 2⟩]
                         rw [show d'.crossings = d.crossings.dropLast.set i.val Y₀.1 from rfl,
                           List.set_set Y₀.1,
                           list_set_eq (x := Y') hdl (by rfl),
                           show d'.numEdges + 1 = d.numEdges - 1 by
                             show d.numEdges - 2 + 1 = d.numEdges - 1; omega,
                           show d'.numEdges + 2 = d.numEdges by
                             show d.numEdges - 2 + 2 = d.numEdges; omega,
                           ← hkink]
                         have hmem : kink ∈ d.crossings.getLast? := by
                           rw [hlast]; exact Option.mem_some.mpr rfl
                         exact (List.dropLast_append_getLast? kink hmem).symm
                       · show d.numEdges = d'.numEdges + 2
                         show d.numEdges = d.numEdges - 2 + 2
                         omega }]
                else []
            else []
        else []
    else []
  | none => []

/-- R2 AVANT : bigon connecté sur chaque arc double de chaque croisement. -/
def r2ForwardWitnesses (d : KnotDiagram) : List (StepWitness d) :=
  (List.finRange d.crossings.length).flatMap fun i =>
    (arcCandidatesWith d).flatMap fun a =>
      ((d.crossings.get i).allDoubleRenamesWith a.1 (d.numEdges + 2) (d.numEdges + 4)).flatMap fun Y' =>
        let d₂ : KnotDiagram :=
          { crossings := d.crossings.set i.val Y'.1 ++
              [⟨a.1, d.numEdges + 1, d.numEdges + 1, d.numEdges + 2⟩,
               ⟨a.1, d.numEdges + 3, d.numEdges + 3, d.numEdges + 4⟩]
          , numEdges := d.numEdges + 4 }
        if hwf : d.wf = true ∧ d₂.wf = true then
          [{ target := d₂
           , proof := ReidemeisterStep.r2 (Or.inl
               ⟨hwf.1, hwf.2, i, a.1, Y'.1, finEmbed d.numEdges 4,
                 a.2.1, a.2.2.1, a.2.2.2, Y'.2, rfl, rfl⟩) }]
        else []

/-- R2 ARRIÈRE : contraction d'une paire de kinks terminaux
`⟨a, n-3, n-3, n-2⟩`, `⟨a, n-1, n-1, n⟩` (n = `d.numEdges`). -/
def r2BackwardWitnesses (d : KnotDiagram) : List (StepWitness d) :=
  match h2 : d.crossings.getLast? with
  | some k2 =>
    match h1 : d.crossings.dropLast.getLast? with
    | some k1 =>
      if hk : k1.e2 = d.numEdges - 3 ∧ k1.e3 = d.numEdges - 3 ∧ k1.e4 = d.numEdges - 2
          ∧ k2.e1 = k1.e1 ∧ k2.e2 = d.numEdges - 1 ∧ k2.e3 = d.numEdges - 1
          ∧ k2.e4 = d.numEdges ∧ 4 ≤ d.numEdges then
        (List.finRange d.crossings.length).flatMap fun (i : Fin d.crossings.length) =>
          if hilt : i.val < d.crossings.length - 2 then
            have hdl : i.val < d.crossings.dropLast.dropLast.length := by
              simp only [List.length_dropLast]; omega
            let Y' := d.crossings.dropLast.dropLast.get ⟨i.val, hdl⟩
            (Y'.allUnDoubleRenamesWith k1.e1 (d.numEdges - 2) d.numEdges).flatMap fun Y₀ =>
              let d' : KnotDiagram :=
                { crossings := d.crossings.dropLast.dropLast.set i.val Y₀.1
                , numEdges := d.numEdges - 4 }
              have hdlen : i.val < d'.crossings.length := by
                change i.val < (d.crossings.dropLast.dropLast.set i.val Y₀.1).length
                rw [List.length_set]; exact hdl
              if ha : 1 ≤ k1.e1 ∧ k1.e1 ≤ d.numEdges - 4 ∧ k1.e1 ∈ d'.edges then
                if hwf : d'.wf = true ∧ d.wf = true then
                  [{ target := d'
                   , proof := by
                       have hY'get : d'.crossings.get ⟨i.val, hdlen⟩ = Y₀.1 := by
                         change (d.crossings.dropLast.dropLast.set i.val Y₀.1).get
                           ⟨i.val, hdlen⟩ = Y₀.1
                         rw [List.get_eq_getElem, List.getElem_set_self]
                       have hk1 : k1 =
                           ⟨k1.e1, d.numEdges - 3, d.numEdges - 3, d.numEdges - 2⟩ := by
                         rw [show k1 = ⟨k1.e1, k1.e2, k1.e3, k1.e4⟩ from rfl,
                             hk.1, hk.2.1, hk.2.2.1]
                       have hk2 : k2 =
                           ⟨k1.e1, d.numEdges - 1, d.numEdges - 1, d.numEdges⟩ := by
                         rw [show k2 = ⟨k2.e1, k2.e2, k2.e3, k2.e4⟩ from rfl,
                             hk.2.2.2.1, hk.2.2.2.2.1, hk.2.2.2.2.2.1, hk.2.2.2.2.2.2.1]
                       refine ReidemeisterStep.r2 (Or.inr
                         ⟨hwf.1, hwf.2, ⟨i.val, hdlen⟩, k1.e1, Y', finEmbed _ 4,
                           ha.1, ha.2.1, ha.2.2, ?_, ?_, ?_⟩)
                       · rw [hY'get,
                           show d'.numEdges + 2 = d.numEdges - 2 by
                             show d.numEdges - 4 + 2 = d.numEdges - 2; omega,
                           show d'.numEdges + 4 = d.numEdges by
                             show d.numEdges - 4 + 4 = d.numEdges; omega]
                         exact Y₀.2
                       · show d.crossings =
                           d'.crossings.set i.val Y' ++
                             [⟨k1.e1, d'.numEdges + 1, d'.numEdges + 1, d'.numEdges + 2⟩,
                              ⟨k1.e1, d'.numEdges + 3, d'.numEdges + 3, d'.numEdges + 4⟩]
                         rw [show d'.crossings = d.crossings.dropLast.dropLast.set i.val Y₀.1
                             from rfl,
                           List.set_set Y₀.1,
                           list_set_eq (x := Y') hdl (by rfl),
                           show d'.numEdges + 1 = d.numEdges - 3 by
                             show d.numEdges - 4 + 1 = d.numEdges - 3; omega,
                           show d'.numEdges + 2 = d.numEdges - 2 by
                             show d.numEdges - 4 + 2 = d.numEdges - 2; omega,
                           show d'.numEdges + 3 = d.numEdges - 1 by
                             show d.numEdges - 4 + 3 = d.numEdges - 1; omega,
                           show d'.numEdges + 4 = d.numEdges by
                             show d.numEdges - 4 + 4 = d.numEdges; omega,
                           ← hk1, ← hk2]
                         have hmem2 : k2 ∈ d.crossings.getLast? := by
                           rw [h2]; exact Option.mem_some.mpr rfl
                         have hmem1 : k1 ∈ d.crossings.dropLast.getLast? := by
                           rw [h1]; exact Option.mem_some.mpr rfl
                         have e2 : d.crossings = d.crossings.dropLast ++ [k2] :=
                           (List.dropLast_append_getLast? k2 hmem2).symm
                         have e1 : d.crossings.dropLast =
                             d.crossings.dropLast.dropLast ++ [k1] :=
                           (List.dropLast_append_getLast? k1 hmem1).symm
                         exact e2.trans ((congrArg (fun x => x ++ [k2]) e1).trans
                           (by simp [List.append_assoc]))
                       · show d.numEdges = d'.numEdges + 4
                         show d.numEdges = d.numEdges - 4 + 4
                         omega }]
                else []
              else []
          else []
      else []
    | none => []
  | none => []

/-- R3 AVANT : move triangulaire — déterministe par fenêtre de 3 croisements
consécutifs, zéro label frais (redistribution des 9 labels existants). -/
def r3ForwardWitnesses (d : KnotDiagram) : List (StepWitness d) :=
  (List.range (d.crossings.length)).flatMap fun i =>
      if hi : i + 2 < d.crossings.length then
      let X₁ := d.crossings.get ⟨i, by omega⟩
      let X₂ := d.crossings.get ⟨i + 1, by omega⟩
      let X₃ := d.crossings.get ⟨i + 2, by omega⟩
      -- layout du triangle X : X₁ = ⟨a₂,a₁,g₁,g₂⟩, X₂ = ⟨a₃,g₁,g₃,b₃⟩,
      -- X₃ = ⟨g₃,g₂,b₂,b₁⟩ — les égalités de recouvrement rendent les trois
      -- `get` définitionnels après réécriture.
      if hlay : X₂.e2 = X₁.e3 ∧ X₃.e1 = X₂.e3 ∧ X₃.e2 = X₁.e4 then
        -- ordre Nodup de la def : [a₂, a₁, a₃, b₃, b₂, b₁, g₁, g₂, g₃]
        if hnd : List.Nodup
            [X₁.e1, X₁.e2, X₂.e1, X₂.e4, X₃.e3, X₃.e4, X₁.e3, X₁.e4, X₂.e3] then
          let d₂ : KnotDiagram :=
            { crossings := ((d.crossings.set i ⟨X₂.e1, X₂.e4, X₂.e3, X₁.e3⟩).set (i + 1)
                ⟨X₂.e3, X₁.e2, X₃.e3, X₁.e4⟩).set (i + 2) ⟨X₁.e3, X₁.e4, X₁.e1, X₃.e4⟩
            , numEdges := d.numEdges }
          if hwf : d.wf = true ∧ d₂.wf = true then
            if hlen : d.crossings.length = d₂.crossings.length then
              [{ target := d₂
               , proof := ReidemeisterStep.r3 (Or.inl
                   ⟨hwf.1, hwf.2, hlen, rfl, i, hi,
                     X₁.e2, X₁.e1, X₂.e1, X₃.e4, X₃.e3, X₂.e4, X₁.e3, X₁.e4, X₂.e3,
                     hnd,
                     by show X₁ = ⟨X₁.e1, X₁.e2, X₁.e3, X₁.e4⟩; rfl,
                     by show X₂ = ⟨X₂.e1, X₁.e3, X₂.e3, X₂.e4⟩; rw [← hlay.1],
                     by show X₃ = ⟨X₂.e3, X₁.e4, X₃.e3, X₃.e4⟩; rw [← hlay.2.1, ← hlay.2.2],
                     rfl⟩) }]
            else []
          else []
        else []
      else []
    else []

/-- L'énumération complète des témoins à un mouvement, preuves attachées. -/
def oneStepWitnessesWithProof (d : KnotDiagram) : List (StepWitness d) :=
  r1ForwardWitnesses d ++ r1BackwardWitnesses d
  ++ r2ForwardWitnesses d ++ r2BackwardWitnesses d ++ r3ForwardWitnesses d

/-- Témoin brut d'un mouvement applicable : un `KnotDiagram` accessible depuis
`d₁` par un seul `ReidemeisterStep` (sans témoin de la relation). C'est
l'API publique consommée par `verifyMovesAux`.
-/
def oneStepWitnesses (d₁ : KnotDiagram) : List KnotDiagram :=
  (oneStepWitnessesWithProof d₁).map StepWitness.target

/-- Vérificateur récursif borné.

`verifyMovesAux k d₁ d₂` retourne `true` ssi il existe une suite d'au plus
`k` `ReidemeisterStep` reliant `d₁` à `d₂`. Cas de base :
- `k = 0` → `d₁ = d₂` (RTC réflexive) ;
- `k ≥ 1` → il existe un successeur `d'` de `d₁` à 1 mouvement tel que
  `verifyMovesAux (k-1) d' d₂` est `true`.

**Statut** : énumération réelle branchée (`#19890`). `oneStepWitnesses d`
rend la liste des successeurs authentiques à un mouvement (R1/R2 dans les
deux sens, R3 avant), filtrés par les gardes décidables de chaque relation —
le retour `false` reste conservative (sound :
`verifyMovesAux = true → ReidemeisterEquiv`, prouvé par `verifyMoves_sound`
ci-dessous).
-/
def verifyMovesAux : Nat → KnotDiagram → KnotDiagram → Bool
  | 0, d, d' => decide (d = d')
  | k+1, d, d' =>
    -- Squelette : on décide l'égalité `d = d'` (clôture réflexive à 0 mouvement,
    -- via le `DecidableEq` dérivé — pas de `LawfulBEq` requis) et chaque
    -- successeur à 1 mouvement de `d`. Le retour `false` est
    -- conservative (sound : `verifyMovesAux = true → ReidemeisterEquiv`,
    -- l'inverse n'est pas demandée).
    decide (d = d') ||
    (oneStepWitnesses d).any fun d_next => verifyMovesAux k d_next d'

/-- Interface publique du vérificateur borné. -/
def verifyMoves (n : Nat) (d₁ d₂ : KnotDiagram) : Bool :=
  verifyMovesAux n d₁ d₂

/-! ## 4. Soundness

La soundness : « si `verifyMoves n d₁ d₂ = true`, alors
`ReidemeisterEquiv d₁ d₂ ». La réciproque (complétude) est hors scope —
l'algorithme est volontairement borné et perd des témoins au-delà du budget.

**Preuve** (le plan « visé » de la PR2+, tenu) : récurrence sur `n`.
- `n = 0` : `verifyMovesAux 0 d₁ d₂ = decide (d₁ = d₂) = true` → `d₁ = d₂`
  (par `of_decide_eq_true`, via le `DecidableEq` dérivé) → `ReidemeisterEquiv.refl d₁`.
- `n = k+1` : `verifyMovesAux (k+1) d₁ d₂ = true` →
  (`decide (d₁ = d₂) = true` ∧ réflexivité) ∨ (∃ d_next, `verifyMovesAux k d_next d₂ = true`
  ∧ `ReidemeisterStep d₁ d_next`). Cas par cas, le premier se ramène à
  `n = 0`, le second utilise l'hypothèse d'induction pour obtenir
  `ReidemeisterEquiv d_next d₂`, puis `ReidemeisterEquiv.step` + `trans`
  ferment le diagramme.

L'instrumentation concrète (`Bool.or_eq_true_iff` puis extraction du témoin
`d_next` depuis `(oneStepWitnesses d).any` par `List.any_eq_true`) est en
place ; le mur PR2+ restant — l'énumération réelle des témoins — est isolé
dans le lemme-pont `oneStepWitnesses_sound` ci-dessous.
-/
/-- Lemme-pont (pattern `named-hard-wall`, désormais tenu) : chaque témoin
rendu par `oneStepWitnesses d` est un successeur à un `ReidemeisterStep`
de `d`.

Depuis l'énumération réelle (`#19890`), la preuve est **par construction** :
chaque élément de `oneStepWitnessesWithProof d` porte sa preuve
(`StepWitness.proof`), et `oneStepWitnesses` n'est que le `map` des cibles —
l'appartenance se remonte par `List.mem_map`. Aucune soundness n'est
re-devinée depuis le diagramme cible. -/
theorem oneStepWitnesses_sound (d d' : KnotDiagram)
    (h : d' ∈ oneStepWitnesses d) : ReidemeisterStep d d' := by
  obtain ⟨w, _hw, heq⟩ := List.mem_map.mp h
  subst heq
  exact w.proof

/-- Acceptance `#19890` (3), témoin R1 : la paire concrète de
`reidemeister1Connected_satisfiable` est bien reliée par le vérificateur à
budget 1 — l'énumération R1 AVANT émet `d₂` comme successeur de `d₁`. -/
theorem verifyMoves_one_r1_witness :
    verifyMoves 1
      { crossings := [⟨1,2,3,4⟩, ⟨1,2,3,4⟩], numEdges := 4 }
      { crossings := [⟨1,2,3,4⟩, ⟨5,2,3,4⟩, ⟨1,5,6,6⟩], numEdges := 6 } = true := by
  decide

/-- Acceptance `#19890` (3), témoin R3 : la paire concrète de
`reidemeister3Connected_satisfiable` est bien reliée à budget 1 — le move
triangulaire est déterministe par fenêtre, l'énumération le retrouve. -/
theorem verifyMoves_one_r3_witness :
    verifyMoves 1
      { crossings := [⟨1,2,7,8⟩, ⟨3,7,9,4⟩, ⟨9,8,5,6⟩,
                       ⟨1,2,10,10⟩, ⟨3,4,5,6⟩], numEdges := 10 }
      { crossings := [⟨3,4,9,7⟩, ⟨9,2,5,8⟩, ⟨7,8,1,6⟩,
                       ⟨1,2,10,10⟩, ⟨3,4,5,6⟩], numEdges := 10 } = true := by
  decide

theorem verifyMoves_sound :
    ∀ (n : Nat) (d₁ d₂ : KnotDiagram),
      verifyMoves n d₁ d₂ = true → ReidemeisterEquiv d₁ d₂ := by
  intro n
  induction n with
  | zero =>
    intro d₁ d₂ h
    simp only [verifyMoves, verifyMovesAux] at h
    have hd : d₁ = d₂ := of_decide_eq_true h
    subst hd
    exact ReidemeisterEquiv.refl d₁
  | succ k ih =>
    intro d₁ d₂ h
    simp only [verifyMoves, verifyMovesAux] at h
    rcases Bool.or_eq_true_iff.mp h with heq | hany
    · have hd : d₁ = d₂ := of_decide_eq_true heq
      subst hd
      exact ReidemeisterEquiv.refl d₁
    · obtain ⟨d_next, hmem, hver⟩ := List.any_eq_true.mp hany
      exact ReidemeisterEquiv.trans
        (ReidemeisterEquiv.step (oneStepWitnesses_sound d₁ d_next hmem))
        (ih d_next d₂ hver)

/-! ## 5. Helpers pour `Lidman.lean` (cible indirecte)

`foldChangeCrossingsAt` applique séquentiellement une liste de changements de
croisement à un nœud (fold left). C'est le « témoin `indices` » de
`Knot.UnknottableIn` (Invariant.lean:2292) rendu opérationnel.

`unknottingWitness` scelle l'usage typique : « pour qu'un nœud ait un nombre
de dénouement ≤ n, exhiber une suite de changements de croisement de longueur
n et une suite de ReidemeisterEquiv entre l'image et `unknotDiagram` ».
C'est le contrat que `unknotting_11n102_upper` (Lidman:81) honorera une fois
ce module landed et `verifyMoves_sound` prouvé.
-/

/-- Applique séquentiellement une liste de changements de croisement. -/
def foldChangeCrossingsAt (k : Knot) (indices : List Nat) : Knot :=
  indices.foldl Knot.changeCrossingAt k

/-- Témoin de dénouement : liste de changements + suite de ReidemeisterEquiv
entre l'image et `unknotDiagram`. -/
structure UnknottingWitness (k : Knot) (n : Nat) where
  indices : List Nat
  length_eq : indices.length = n
  equiv :
    MoveSequence
      (foldChangeCrossingsAt k indices).diagram
      unknotDiagram

/-! ## 6. Compatibilité future

Le module ne dépend que de `Knots.Reidemeister` et `Knots.Invariant` — pas de
`Knots.ReidemeisterInvariance` (qui importerait `Knots.Conway` et ferait
tourner le lac inutilement pour les passes qui n'attaquent que la
combinatoire). Le sibling `_en` porte le miroir anglais des docstrings,
corps byte-identique (convention i18n EPIC #4980).

Le lakefile (`Knots.lean`, ligne d'import) devra ajouter
`import Knots.ReidemeisterCombinatorial` une fois ce module vérifié par CI —
PR3, après soundness et witness `Lidman:81`.
-/

end Knots
