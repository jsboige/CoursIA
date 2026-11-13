/-
Knots.BoundedEnumeration — Énumération canonique bornée + petit vérificateur
================================================================================

Étape 4 de l'issue #18611 (Epic #1453, point 3) : « Équivalence décidable
bornée — énumération des diagrammes à croisements bornés, et décision de
connectivité par mouvements — le « petit vérificateur » de l'arbitrage »,
côté combinatoire.

Ce module livre :

  1. `allDiagrams n` — l'**énumération canonique finie** des diagrammes de
     nœud à au plus `n` croisements : pour chaque `c ≤ n`, les listes de
     `c` croisements à étiquettes bornées par `labelBound c`, filtrées sur
     la bonne formation `KnotDiagram.wf` ; le cas `c = 0` ajoute les deux
     diagrammes dégénérés (`numEdges ∈ {0, 1}`) ;
  2. `allDiagrams_bounded` — tout diagramme de l'énumération a au plus `n`
     croisements : l'univers est **borné par construction** ;
  3. `allDiagrams_wf` — tout diagramme de l'énumération est en bonne
     formation : l'univers est **sain**, on n'y décide que des diagrammes
     légitimes ;
  4. `boundedClassConnects_sound` — la **soundness du petit vérificateur
     restreinte à la classe bornée** : si `verifyMoves` répond `true` pour
     deux diagrammes de l'énumération, ils sont `ReidemeisterEquiv` ;
  5. deux exemples exécutables : `demo_unknot_mem` (le nœud trivial
     appartient à l'énumération — décidé par calcul) et
     `demo_verifier_sound` (le témoin R1 du vérificateur scellé en preuve
     `ReidemeisterEquiv` authentique).

Portée et résidu (déclaré, non dissimulé) :
- la **complétude** de l'énumération — « tout diagramme bien formé à au
  plus `n` croisements appartient à `allDiagrams n` » — n'est **pas**
  prouvée ici ; c'est le résidu nommé de cette étape, porté par la PR ;
- l'énumération n'est **pas évaluée** pour de grandes bornes : c'est un
  objet fini de type `List`, et seuls les cas `c = 0` sont calculés par
  `decide` ;
- aucun théorème profond de la théorie des nœuds n'est prouvé (les `sorry`
  permanents restent ceux de `Knots.Lidman`, `Knots.Slice`).

Convention i18n (EPIC #4980, décision user 2026-07-04) : ce fichier est le
**FR canonique**, avec son miroir anglais dans le sibling
`BoundedEnumeration_en.lean` (modèle sibling pair). Les énoncés de
théorèmes, les tactiques Lean, les noms de lemmes et les références Mathlib
restent en anglais (compat Mathlib 4) ; seules les docstrings de module et
ce bloc d'en-tête diffèrent entre les deux fichiers.
-/

import Knots.Basic
import Knots.Reidemeister
import Knots.ReidemeisterCombinatorial

namespace Knots.Bounded

open Knots.Combinatorial

/-! ## 1. Borne d'étiquetage

`labelBound c = 2c` : un diagramme bien formé à `c` croisements a quatre
extrémités par croisement, soit `4c` occurrences d'arêtes. La borne est
donc une constante de construction, pas une propriété démontrée ici.
-/

/-- Borne d'étiquetage de l'énumération bornée. -/
def labelBound (c : Nat) : Nat := 2 * c

/-! ## 2. Univers fini et énumération

La construction est **déclarative** : on énumère d'abord les croisements
admissibles, puis les listes de `c` tels croisements, puis on filtre sur la
bonne formation.
-/

/-- Tous les croisements dont les quatre étiquettes sont dans `[1, alpha]`. -/
def allBoundedCrossings (alpha : Nat) : List PDCrossing :=
  (List.range alpha).flatMap fun a1 =>
    (List.range alpha).flatMap fun a2 =>
      (List.range alpha).flatMap fun a3 =>
        (List.range alpha).map fun a4 =>
          ⟨a1 + 1, a2 + 1, a3 + 1, a4 + 1⟩

/-- Toutes les listes de `c` croisements à étiquettes bornées par `alpha`. -/
def allCrossingLists (c alpha : Nat) : List (List PDCrossing) :=
  match c with
  | 0 => [[]]
  | c' + 1 =>
    (allCrossingLists c' alpha).flatMap fun xs =>
      (allBoundedCrossings alpha).map (fun x => x :: xs)

/-- Diagramme canonique construit sur `c` croisements : les croisements
    fournis, et `labelBound c` arêtes. -/
def mkDiag (c : Nat) (l : List PDCrossing) : KnotDiagram :=
  { crossings := l, numEdges := labelBound c }

/-- Énumération canonique finie des diagrammes de nœud à au plus `n`
    croisements.

    Cas `c = 0` : les deux diagrammes dégénérés. Cas `c > 0` : les listes de
    `c` croisements à étiquettes bornées, filtrées sur `wf`, puis
    transformées en diagrammes. -/
def allDiagrams (n : Nat) : List KnotDiagram :=
  (List.range (n + 1)).flatMap fun c =>
    if c = 0 then
      [ ⟨[], 0⟩, ⟨[], 1⟩ ]
    else
      ((allCrossingLists c (labelBound c)).filter
        (fun l => (mkDiag c l).wf)).map (mkDiag c)

/-! ## 3. Propriétés de l'énumération -/

/-- Les listes produites par `allCrossingLists c alpha` ont exactement `c`
    éléments : la longueur est portée par la construction. -/
theorem allCrossingLists_length (c alpha : Nat) :
    ∀ l ∈ allCrossingLists c alpha, l.length = c := by
  induction c with
  | zero =>
    intro l hl
    simp only [allCrossingLists, List.mem_singleton] at hl
    subst hl
    rfl
  | succ k ih =>
    intro l hl
    simp only [allCrossingLists, List.mem_flatMap, List.mem_map] at hl
    obtain ⟨xs, hxs, x, _, rfl⟩ := hl
    simp only [List.length_cons, ih xs hxs]

/-- Tout diagramme de l'énumération a au plus `n` croisements : l'univers
    est borné par construction. -/
theorem allDiagrams_bounded (n : Nat) (d : KnotDiagram)
    (h : d ∈ allDiagrams n) : d.numCrossings ≤ n := by
  simp only [allDiagrams, List.mem_flatMap] at h
  obtain ⟨c, hc, hd⟩ := h
  rw [List.mem_range] at hc
  by_cases hc0 : c = 0
  · subst hc0
    have hd' : d = ⟨[], 0⟩ ∨ d = ⟨[], 1⟩ := by simpa using hd
    rcases hd' with rfl | rfl <;>
      simp only [KnotDiagram.numCrossings, List.length_nil] <;> omega
  · simp only [if_neg hc0, List.mem_map] at hd
    obtain ⟨l, hl, rfl⟩ := hd
    simp only [List.mem_filter] at hl
    obtain ⟨hl', _⟩ := hl
    simp only [mkDiag, KnotDiagram.numCrossings]
    rw [allCrossingLists_length c (labelBound c) l hl']
    omega

/-- Tout diagramme de l'énumération est en bonne formation : on ne décide
    que sur des diagrammes légitimes. -/
theorem allDiagrams_wf (n : Nat) (d : KnotDiagram)
    (h : d ∈ allDiagrams n) : d.wf = true := by
  simp only [allDiagrams, List.mem_flatMap] at h
  obtain ⟨c, _, hd⟩ := h
  by_cases hc0 : c = 0
  · subst hc0
    have hd' : d = ⟨[], 0⟩ ∨ d = ⟨[], 1⟩ := by simpa using hd
    rcases hd' with rfl | rfl
    · decide
    · decide
  · simp only [if_neg hc0, List.mem_map, List.mem_filter] at hd
    obtain ⟨l, ⟨_, hwf⟩, rfl⟩ := hd
    exact hwf

/-! ## 4. Le petit vérificateur sur la classe bornée

`verifyMoves` (borné en budget) et sa soundness vers `ReidemeisterEquiv`
vivent dans `Knots.ReidemeisterCombinatorial`. Ce module en donne
l'**énoncé restreint à l'univers énuméré** : c'est la forme qu'utilise le
« petit vérificateur » de l'arbitrage.
-/

/-- Soundness du petit vérificateur sur la classe bornée : si
    `verifyMoves budget d₁ d₂ = true` pour deux diagrammes de l'énumération
    `allDiagrams n`, alors ils sont `ReidemeisterEquiv`. -/
theorem boundedClassConnects_sound (n budget : Nat)
    (d₁ d₂ : KnotDiagram)
    (_h₁ : d₁ ∈ allDiagrams n) (_h₂ : d₂ ∈ allDiagrams n)
    (hv : verifyMoves budget d₁ d₂ = true) :
    ReidemeisterEquiv d₁ d₂ :=
  verifyMoves_sound budget d₁ d₂ hv

/-! ## 5. Exemples exécutables -/

/-- Le nœud trivial appartient à l'énumération : décidé par calcul. -/
theorem demo_unknot_mem :
    ({ crossings := [], numEdges := 1 } : KnotDiagram) ∈ allDiagrams 0 := by
  simp [allDiagrams]

/-- Le verdict du vérificateur se scelle en une preuve authentique : la
    paire du témoin R1 de `Knots.ReidemeisterCombinatorial` est
    `ReidemeisterEquiv`. -/
theorem demo_verifier_sound :
    ReidemeisterEquiv
      { crossings := [⟨1, 2, 3, 4⟩, ⟨1, 2, 3, 4⟩], numEdges := 4 }
      { crossings := [⟨1, 2, 3, 4⟩, ⟨5, 2, 3, 4⟩, ⟨1, 5, 6, 6⟩],
        numEdges := 6 } :=
  verifyMoves_sound 1 _ _ verifyMoves_one_r1_witness

end Knots.Bounded
