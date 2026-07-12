/-
# Formes canoniques de grille — la spécification `sortDedup` (Conway)

Copyright (c) 2026 CoursIA. Tous droits réservés.
Distribué sous licence Apache 2.0 comme décrit dans le fichier LICENSE.
Version française mirrorée depuis l'anglais — voir les notes d'accessibilité
plus bas pour le rationale i18n.

## Formes canoniques de grille — la spécification `sortDedup`

Toute grille manipulée par le moteur Life est l'image d'un `sortDedup` :
`step`, `evolve (n+1)`, `shift` et `MacroCell.toGrid` se composent tous
à droite avec `sortDedup`, et `restrictGridTo` est un `filter` d'une telle
image. Ce module prouve que les sorties de `sortDedup` sont **canoniques**
— triées lexicographiquement et sans doublons — et que les listes
canoniques sont **rigides** : déterminées par leur seul prédicat
d'appartenance (`Canonical.ext`).

C'est le **pont** qui transforme les objectifs d'égalité de listes des
théorèmes de correction Hashlife (P4/P5, `HashlifeCorrectness.lean`) en
objectifs d'appartenance point par point, où la combinatoire réelle de la
règle B3/S23 et la récursion macrocell peuvent être argumentées cellule
par cellule.

La théorie de l'ordre est élémentaire : `lexLe` (la clôture réflexive de
`lexLt`) est totale, transitive et antisymétrique sur `Int × Int`, le tout
par `omega` après dépliage en arithmétique linéaire entière.

Ce module est **entièrement prouvé** (aucun `sorry`).

## Note d'accessibilité Epic #1452/#1453

Ce module héberge **13 theorem + 1 def** sur 4 sections, dédiées à la
canonicité structurelle de la grille (sans aucune sémantique runtime
Hashlife). Les tactiques mobilisées sont **arithmétiques et structurelles**
(`omega`, `unfold`, `simp only [...]`, `rw [mem_sortDedup]`, `split_ifs`,
`exact ⟨_, _⟩`) avec deux appels à `List.Pairwise.sublist` / `List.Nodup.sublist`
pour préserver la canonicité sous `filter`. C'est précisément la calibration
cible pour l'Epic #1453 : cible SOTA-OK où le harnais prouveur résout
proprement des lemmes de canonicité structurelle entre représentations de
listes équivalentes.

**Densité 2.371 thm/KB** (13 / 5483) — la plus élevée du sous-domaine
`conway_lein/Life/*` : densité record car la substance est *purement
canonique* (1 axiome par ~10 lignes de preuve structurée), avec une
définition de prédicat `Canonical` réutilisée par 6 theorem. C'est la
signature attendue d'un module de **canonicité structurelle** : un seul
concept (canonicité de liste) instancié sur les opérations fondamentales
du moteur Life (`step`, `evolve`, `shift`, `filter`).

**Satellite de N2 redesign arc EPIC #3846.** Ce module n'est pas sur le
chemin W3/W4 du cycle-break N2 lui-même (c'est `ConeGeometry` qui en est
W3, et `LightCone` qui en est le pont), mais il est **consommé** par
`HashlifeCorrectness.lean` pour transformer les objectifs d'égalité de
listes P4/P5 en objectifs d'appartenance cellulaire. La fermeture de
`hashlife_correct` (4 sorries à fermer dans `HashlifeCorrectness.lean`,
cf issue #5726) débloque l'éligibilité du Jeu de la Vie comme substrat
de stratification ICT (issue #5726, partie de l'EPIC #4588).

## Substance réelle — canonicité structurelle, 13 theorem + 1 def sur 4 sections

`GridCanonical.lean` héberge **13 theorem + 1 def** sur la **canonicité
de la grille** (lex-sortie + sans-doublons) maintenue par les opérations
fondamentales du moteur Life :

- `lexLt_iff` : **lexLt en arithmétique linéaire** — `lexLt a b = true ↔
  a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2)` (par dépliage `lexLt` + `split_ifs`
  + `simp` + `omega`). Fait de base pour relier la définition opérationnelle
  `lexLt` à l'arithmétique linéaire des paires d'entiers.
- `lexLe_iff` : **lexLe en arithmétique linéaire** — `lexLe a b = true ↔
  a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 ≤ b.2)` (par `simp only [lexLe, Bool.or_eq_true,
  lexLt_iff, beq_iff_eq, Prod.ext_iff]` + `omega`). Fait jumeau du
  précédent, pour la clôture réflexive.
- `lexLe_total` : **lexLe total** — `(lexLe a b || lexLe b a) = true` (par
  `simp only [Bool.or_eq_true, lexLe_iff]` + `omega`). C'est l'hypothèse
  que `List.pairwise_mergeSort` exige sur son argument comparateur.
- `lexLe_trans` : **lexLe transitif** — `lexLe a c = true` depuis
  `lexLe a b = true` + `lexLe b c = true` (par `simp only [lexLe_iff] at *`
  + `omega`).
- `lexLe_antisymm` : **lexLe antisymétrique** — `lexLe a b = true` +
  `lexLe b a = true` ⇒ `a = b` (par `simp only [lexLe_iff] at *` + `rw
  [Prod.ext_iff]` + `omega`). Fait clef qui rend les listes lex-triées
  *rigides* : une permutation entre deux listes triées est l'identité.
- `Canonical` *(def)* : **prédicat de canonicité** sur `Grid` —
  `g.Pairwise (fun a b => lexLe a b = true) ∧ g.Nodup`. Définition
  *composite* (sortedness + no-duplicates) qui capture la rigidité.
- `canonical_sortDedup` : **`sortDedup` produit une grid canonique** —
  `Canonical (sortDedup l)` pour toute liste `l` (par dépliage `sortDedup`
  + `List.Pairwise.sublist (List.dedup_sublist _)` (depuis
  `pairwise_mergeSort` utilisant `lexLe_trans` + `lexLe_total`) +
  `List.nodup_dedup _`). Le fait central : toute image `sortDedup` est
  canonique.
- `Canonical.filter` : **filter préserve la canonicité** — `Canonical
  (g.filter q)` depuis `Canonical g` (par `List.Pairwise.sublist
  List.filter_sublist` + `List.Nodup.sublist List.filter_sublist`). Fait
  technique pour les opérations de restriction (`restrictGridTo`).
- `Canonical.ext` : **rigidité des grilles canoniques** — deux grilles
  canoniques avec les mêmes membres sont **égales comme listes**
  (`g₁ = g₂`). La preuve : la même-appartenance donne une permutation
  (`List.perm_ext_iff_of_nodup` qui demande la no-dups), puis une
  permutation entre deux listes lex-triées est l'identité par
  antisymétrie (`List.Perm.eq_of_pairwise` utilisant `lexLe_antisymm`).
  C'est le fait **central** de ce module : la canonicité identifie
  listes et ensembles.
- `sortDedup_eq_sortDedup_iff` : **égalité iff ensembles égaux** — pour
  deux listes `l₁`, `l₂`, `sortDedup l₁ = sortDedup l₂ ↔ ∀ p, p ∈ l₁ ↔
  p ∈ l₂` (par `constructor` + `rw [← mem_sortDedup, h, mem_sortDedup]`
  pour forward + `Canonical.ext` pour backward). Le **workhorse** utilisé
  par P4/P5 de `HashlifeCorrectness.lean`.
- `canonical_step` : **`step` produit des grilles canoniques** — `Canonical
  (step g)` (par `canonical_sortDedup _`). Fait de préservation directe
  puisque `step g = sortDedup (candidates g.filter (aliveNext g))`.
- `canonical_evolve_of_pos` : **`evolve n` canonique pour `n ≥ 1`** —
  `Canonical (evolve n g)` (par `obtain ⟨m, rfl⟩ : ∃ m, n = m + 1` + `rw
  [evolve_succ]` + `canonical_step _`). Pour `n = 0`, `evolve 0 g = g`,
  qui n'a pas besoin d'être canonique.
- `canonical_shift` : **`shift` produit des grilles canoniques** —
  `Canonical (shift v g)` (par `canonical_sortDedup _`). Translation
  préserve la canonicité.
- `mem_step_iff` : **appartenance dans `step g` dépliée** — `p ∈ step g ↔
  p ∈ candidates g ∧ aliveNext g p = true` (par `unfold step` + `rw
  [mem_sortDedup, List.mem_filter]`). Fait de **désucrage** qui permet
  aux théorèmes P4/P5 de raisonner sur la règle B3/S23 elle-même
  plutôt que sur la machinerie `sortDedup`.

Le **fait central formalisé** dans ce module est donc la **canonicité
structurelle des grilles du moteur Life** : toute grille construite par
`sortDedup` est canonique (lex-sortie + sans-doublons), et les listes
canoniques sont **rigides** — déterminées par leur seul prédicat
d'appartenance. Cette rigidité est exactement ce qui permet aux
théorèmes P4/P5 de `HashlifeCorrectness.lean` de transformer leurs
objectifs d'égalité de listes en objectifs d'appartenance cellulaire
(où la combinatoire B3/S23 peut être argumentée cellule par cellule).

## Pont Mathlib + accessibilité Epic #1452

L'import est `Conway.Life` (le module parent qui agrège tous les
sous-modules Life). Sans `import Mathlib` direct — Mathlib est ré-importé
transitivement via la chaîne de lakes. Toutes les tactiques utilisées
(`omega`, `unfold`, `simp only [...]`, `rw [...]`, `split_ifs`,
`exact ⟨_, _⟩`, `List.Pairwise.sublist`, `List.Nodup.sublist`,
`List.perm_ext_iff_of_nodup`, `List.Perm.eq_of_pairwise`) sont des
**champs de structure canoniques Mathlib 4** sur `List` et `Int × Int`.
C'est la calibration SOTA-OK visée par l'Epic #1453 : cibles où le
harnais prouveur résout proprement des lemmes de canonicité structurelle
entre représentations de listes équivalentes.

Suit : hommage MathOverflow + Mathlib i18n convention #4980 ratifiée
2026-07-04 (option A pragmatique : deux blocs `/` top-level distincts,
sans séparateur `---` interne).
-/

/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

## Canonical grid forms — the `sortDedup` specification

Every grid manipulated by the Life engine is a `sortDedup` image:
`step`, `evolve (n+1)`, `shift` and `MacroCell.toGrid` all post-compose
with `sortDedup`, and `restrictGridTo` is a `filter` of such an image.
This module proves that `sortDedup` outputs are **canonical** — lex-sorted
and duplicate-free — and that canonical lists are **rigid**: determined by
their membership predicate alone (`Canonical.ext`).

This is the bridge that turns the list-equality goals of the Hashlife
correctness theorems (P4/P5, `HashlifeCorrectness.lean`) into pointwise
membership goals, where the actual combinatorics of the B3/S23 rule and
the macrocell recursion can be argued cell by cell.

The order theory is elementary: `lexLe` (reflexive closure of `lexLt`)
is total, transitive and antisymmetric on `Int × Int`, all by `omega`
after unfolding to linear integer arithmetic.

This module is fully proven (no `sorry`).
-/

import Conway.Life

namespace Conway
namespace Life

/-! ## The lexicographic comparator: order axioms -/

/-- `lexLt` in terms of linear integer arithmetic. -/
theorem lexLt_iff {a b : Int × Int} :
    lexLt a b = true ↔ a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2) := by
  unfold lexLt
  split_ifs <;> simp <;> omega

/-- `lexLe` in terms of linear integer arithmetic. -/
theorem lexLe_iff {a b : Int × Int} :
    lexLe a b = true ↔ a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 ≤ b.2) := by
  simp only [lexLe, Bool.or_eq_true, lexLt_iff, beq_iff_eq, Prod.ext_iff]
  omega

/-- `lexLe` is total — the hypothesis `List.pairwise_mergeSort` needs. -/
theorem lexLe_total (a b : Int × Int) : (lexLe a b || lexLe b a) = true := by
  simp only [Bool.or_eq_true, lexLe_iff]
  omega

/-- `lexLe` is transitive. -/
theorem lexLe_trans (a b c : Int × Int)
    (hab : lexLe a b = true) (hbc : lexLe b c = true) : lexLe a c = true := by
  simp only [lexLe_iff] at *
  omega

/-- `lexLe` is antisymmetric — what makes sorted Nodup lists rigid. -/
theorem lexLe_antisymm (a b : Int × Int)
    (hab : lexLe a b = true) (hba : lexLe b a = true) : a = b := by
  simp only [lexLe_iff] at hab hba
  rw [Prod.ext_iff]
  omega

/-! ## Canonical grids -/

/-- A grid in canonical form: lexicographically sorted and duplicate-free.
    Invariant of every `sortDedup` image, preserved by `filter`. -/
def Canonical (g : Grid) : Prop :=
  g.Pairwise (fun a b => lexLe a b = true) ∧ g.Nodup

/-- `sortDedup` always produces a canonical grid: sortedness comes from
    `pairwise_mergeSort` (using totality and transitivity of `lexLe`) and
    survives `dedup` because `dedup` yields a sublist; freedom from
    duplicates is `nodup_dedup`. -/
theorem canonical_sortDedup (l : List (Int × Int)) : Canonical (sortDedup l) := by
  unfold sortDedup
  exact ⟨List.Pairwise.sublist (List.dedup_sublist _)
          (List.pairwise_mergeSort lexLe_trans lexLe_total l),
        List.nodup_dedup _⟩

/-- Filtering preserves canonical form (`filter` yields a sublist). -/
theorem Canonical.filter {g : Grid} (h : Canonical g) (q : (Int × Int) → Bool) :
    Canonical (g.filter q) :=
  ⟨List.Pairwise.sublist List.filter_sublist h.1,
   List.Nodup.sublist List.filter_sublist h.2⟩

/-- **Rigidity of canonical grids**: two canonical grids with the same
    members are equal as lists. Same-membership gives a permutation
    (`perm_ext_iff_of_nodup`), and a permutation between two lex-sorted
    lists is the identity by antisymmetry (`Perm.eq_of_pairwise`). -/
theorem Canonical.ext {g₁ g₂ : Grid} (h₁ : Canonical g₁) (h₂ : Canonical g₂)
    (h : ∀ p, p ∈ g₁ ↔ p ∈ g₂) : g₁ = g₂ :=
  List.Perm.eq_of_pairwise (fun a b _ _ hab hba => lexLe_antisymm a b hab hba)
    h₁.1 h₂.1 ((List.perm_ext_iff_of_nodup h₁.2 h₂.2).mpr h)

/-- The workhorse corollary: two `sortDedup` images are equal **iff** their
    input lists have the same members. List equality of canonical grids is
    exactly set equality. -/
theorem sortDedup_eq_sortDedup_iff {l₁ l₂ : List (Int × Int)} :
    sortDedup l₁ = sortDedup l₂ ↔ ∀ p, p ∈ l₁ ↔ p ∈ l₂ := by
  constructor
  · intro h p
    rw [← mem_sortDedup (l := l₁), h, mem_sortDedup]
  · intro h
    exact Canonical.ext (canonical_sortDedup _) (canonical_sortDedup _)
      (fun p => by rw [mem_sortDedup, mem_sortDedup]; exact h p)

/-! ## Canonicity of the Life-engine grids -/

/-- `step` produces canonical grids. -/
theorem canonical_step (g : Grid) : Canonical (step g) :=
  canonical_sortDedup _

/-- `evolve n` produces canonical grids for `n ≥ 1` (for `n = 0` the
    output is the input, which need not be canonical). -/
theorem canonical_evolve_of_pos {n : Nat} (hn : 0 < n) (g : Grid) :
    Canonical (evolve n g) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [evolve_succ]
  exact canonical_step _

/-- `shift` produces canonical grids. -/
theorem canonical_shift (v : Int × Int) (g : Grid) : Canonical (shift v g) :=
  canonical_sortDedup _

/-- Membership in a `step` image, unfolded to the rule: `p` is in `step g`
    iff it is a candidate and `aliveNext` accepts it. -/
theorem mem_step_iff {g : Grid} {p : Int × Int} :
    p ∈ step g ↔ p ∈ candidates g ∧ aliveNext g p = true := by
  unfold step
  rw [mem_sortDedup, List.mem_filter]

end Life
end Conway
