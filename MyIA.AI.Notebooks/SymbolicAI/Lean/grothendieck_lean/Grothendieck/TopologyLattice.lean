/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Hommage Grothendieck — Partie 39 : lois de treillis des topologies

Alexandre Grothendieck (1928-2014).

Extension Phase 5 (#2159, EPIC #1646).

Les parties 1-38 ont etabli les fondamentaux : categories, cribles,
topologies, lois de treillis, identites de pullback, bases de faisceaux,
cloture couvrante, calibration, sous-canonicalite, topologies denses,
faisceaux, hom interne, cohomologie de Cech, limite de Mayer-Vietoris,
extensions de Kan, adjonctions, monades, equivalences, categories monoidales,
limites et colimites, couples comma, images directes, theoremes propres sur la
forme fleche (`J.Covers S f`), sur la couverture bundlee (`J.Cover X`), les
lois de coherence du pseudo-foncteur pullback (Partie 37) et les lois de
foncteur du pullback (Partie 38).

La Partie 39 etablit les **lois de treillis des topologies de Grothendieck** :
Mathlib fournit la structure de treillis complet sur `GrothendieckTopology C`
(instance `CompleteLattice`, construite depuis le `sInf` intersection
ponctuelle), mais **ne fournit pas** les caracterisations par recouvrement des
operations de treillis. Ce module les enonce et les prouve :

  - `le_covering` : l'ordre est ponctuel — `J₁ ≤ J₂` si et seulement si tout
    crible `S ∈ J₁ X` est aussi dans `J₂ X`.
  - `le_covers` : l'ordre est compatible avec la forme fleche —
    `J₁ ≤ J₂ → J₁.Covers S f → J₂.Covers S f`.
  - `inf_covering` / `inf_covers` : `S ∈ (J₁ ⊓ J₂) X` si et seulement si
    `S ∈ J₁ X` **et** `S ∈ J₂ X` — l'intersection des topologies est
    l'intersection ponctuelle des cribles couvrants.
  - `sup_covering` / `sup_covers` : la borne superieure est la **topologie
    engendree** — `S ∈ (J₁ ⊔ J₂) X` si et seulement si `S` est couvert par
    toute topologie `K` au-dessus de `J₁` et de `J₂` (caracterisation par
    bornes superieures ; l'union ponctuelle ne suffit pas, elle n'est pas
    stable par pullback).
  - `sSup_covering` : la version infinie — `S ∈ sSup s X` si et seulement si
    `S` est couvert par toute borne superieure du membre `s`.

Chaque preuve est une **preuve tactique reelle** (veine DEEP) : les axiomes
de treillis (`le_sInf`, `sInf_le`, `le_sSup`, `sSup_le`, `le_inf`,
`inf_le_left`/`inf_le_right`, `sup_le`, `le_sup_left`/`le_sup_right`) plus
`le_covering` ramenant la compatibilite ordre/recouvrement. Aucune preuve
n'est un re-export.

EPIC #1646, Phase 5 (#2159). Tous les `sorry`s elimines a la creation.

### Convention i18n (EPIC #4980 ratifiee par user 2026-07-04)

Ce module est apparie avec son jumeau anglais dans le fichier sibling
`TopologyLattice_en.lean` (modele sibling pair, voir PR #6154 pour le pilote
sur `Utility.lean`). Namespace suffix `_en` applique au fichier EN
(anti-collision, conforme code-style.md #4980). Les enonces de theoremes, les
noms de lemmes, les tactiques Lean et les references Mathlib restent en
anglais ; seules les docstrings `/-- ... -/` et les commentaires `-- ...`
different entre les deux fichiers (preservation byte-identity).
-/

import Mathlib.CategoryTheory.Sites.Grothendieck

namespace Grothendieck.TopologyLattice

open CategoryTheory

/-!
## Section 1 : ordre et forme fleche

L'ordre sur `GrothendieckTopology C` est l'ordre ponctuel sur les familles de
cribles (`le_def` de Mathlib). La forme fleche `J.Covers S f` est definie par
`S.pullback f ∈ J Y` (Mathlib, `covers_iff`). Cette section relie les deux.
-/

/-- L'ordre des topologies est ponctuel : `J₁ ≤ J₂` si et seulement si tout
    crible couvert par `J₁` est couvert par `J₂`.
    Preuve : `le_def` puis l'ordre ponctuel des fonctions (definitionnel),
    decompose en appartenances ponctuelles. -/
theorem le_covering {C : Type*} [Category C] {J₁ J₂ : GrothendieckTopology C} :
    J₁ ≤ J₂ ↔ ∀ ⦃X : C⦄ (S : Sieve X), S ∈ J₁ X → S ∈ J₂ X := by
  rw [GrothendieckTopology.le_def]
  constructor
  · intro h X S hS
    exact h X hS
  · intro h X S hS
    exact h S hS

/-- L'ordre est compatible avec la forme fleche : si `J₁ ≤ J₂`, tout crible
    que `J₁` couvre le long de `f`, `J₂` le couvre aussi.
    Preuve : `covers_iff` des deux cotes (les deux membres sont `∈ J₁ Y` /
    `∈ J₂ Y`) puis `le_covering`. -/
theorem le_covers {C : Type*} [Category C] {X Y : C} {J₁ J₂ : GrothendieckTopology C}
    (S : Sieve X) (f : Y ⟶ X) :
    J₁ ≤ J₂ → J₁.Covers S f → J₂.Covers S f := by
  intro h₁₂ hc
  rw [GrothendieckTopology.covers_iff] at hc ⊢
  exact le_covering.mp h₁₂ (S.pullback f) hc

/-!
## Section 2 : borne inferieure (inf)

La borne inferieure `J₁ ⊓ J₂` de deux topologies est le `sInf` de la paire
(infimum du treillis complet), et par `mem_sInf` de Mathlib sa
caracterisation ponctuelle est l'intersection des cribles couvrants. Cette
section prouve ces caracterisations et leur traduction a la forme fleche.
-/

/-- L'infimum d'une paire est le `sInf` de la paire : `J₁ ⊓ J₂ = sInf {J₁, J₂}`.
    Preuve : `le_antisymm` — d'un cote `le_sInf` avec `inf_le_left` /
    `inf_le_right`, de l'autre `le_inf` avec `sInf_le` deux fois. -/
lemma inf_eq_sInf {C : Type*} [Category C] {J₁ J₂ : GrothendieckTopology C} :
    J₁ ⊓ J₂ = sInf {J₁, J₂} := by
  apply le_antisymm
  · apply le_sInf
    intro J hJ
    simp at hJ
    rcases hJ with rfl | rfl
    · exact inf_le_left
    · exact inf_le_right
  · apply le_inf
    · apply sInf_le
      simp
    · apply sInf_le
      simp

/-- L'intersection de deux topologies est l'intersection ponctuelle :
    `S ∈ (J₁ ⊓ J₂) X` si et seulement si `S ∈ J₁ X` et `S ∈ J₂ X`.
    Preuve : `inf_eq_sInf` puis `mem_sInf` de Mathlib, et decomposer
    l'appartenance a la paire `{J₁, J₂}`. -/
theorem inf_covering {C : Type*} [Category C] {X : C} {J₁ J₂ : GrothendieckTopology C}
    (S : Sieve X) :
    S ∈ (J₁ ⊓ J₂) X ↔ S ∈ J₁ X ∧ S ∈ J₂ X := by
  rw [inf_eq_sInf]
  rw [GrothendieckTopology.mem_sInf]
  constructor
  · intro h
    exact ⟨h J₁ (by simp), h J₂ (by simp)⟩
  · intro h K hK
    simp at hK
    rcases hK with rfl | rfl
    · exact h.1
    · exact h.2

/-- Traduction de `inf_covering` a la forme fleche : couvrir par `J₁ ⊓ J₂`
    equivaut a couvrir par `J₁` et par `J₂`.
    Preuve : `covers_iff` trois fois (les trois membres sont des appartenances
    `∈ (J₁ ⊓ J₂) Y` / `∈ J₁ Y` / `∈ J₂ Y`) puis `inf_covering`. -/
theorem inf_covers {C : Type*} [Category C] {X Y : C} {J₁ J₂ : GrothendieckTopology C}
    (S : Sieve X) (f : Y ⟶ X) :
    (J₁ ⊓ J₂).Covers S f ↔ J₁.Covers S f ∧ J₂.Covers S f := by
  rw [GrothendieckTopology.covers_iff, GrothendieckTopology.covers_iff,
    GrothendieckTopology.covers_iff]
  exact inf_covering (S.pullback f)

/-!
## Section 3 : borne superieure (sup, sSup)

La borne superieure `J₁ ⊔ J₂` de deux topologies est la **topologie
engendree** par la reunion des cribles : la plus petite topologie au-dessus
des deux. La caracterisation correcte n'est donc pas l'union ponctuelle (qui
n'est pas stable par pullback) mais la caracterisation par bornes superieures :
`S ∈ (J₁ ⊔ J₂) X` si et seulement si `S` est couvert par **toute** topologie
au-dessus de `J₁` et de `J₂`. Cette section prouve ces caracterisations ainsi
que leur version infinie `sSup`.
-/

/-- Borne superieure d'une paire, caracterisation par recouvrement :
    `S ∈ (J₁ ⊔ J₂) X` si et seulement si `S ∈ K X` pour toute topologie `K`
    au-dessus de `J₁` et de `J₂` (la topologie engendree).
    Preuve : dans un sens `sup_le` puis `le_covering` ; dans l'autre, prendre
    `K = J₁ ⊔ J₂`, borne superieure des deux par `le_sup_left`/`le_sup_right`. -/
theorem sup_covering {C : Type*} [Category C] {X : C} {J₁ J₂ : GrothendieckTopology C}
    (S : Sieve X) :
    S ∈ (J₁ ⊔ J₂) X ↔
      ∀ K : GrothendieckTopology C, J₁ ≤ K → J₂ ≤ K → S ∈ K X := by
  constructor
  · intro hS K h₁K h₂K
    exact le_covering.mp (sup_le h₁K h₂K) S hS
  · intro h
    exact h (J₁ ⊔ J₂) le_sup_left le_sup_right

/-- Traduction de `sup_covering` a la forme fleche.
    Preuve : `covers_iff` deux fois puis `sup_covering`. -/
theorem sup_covers {C : Type*} [Category C] {X Y : C} {J₁ J₂ : GrothendieckTopology C}
    (S : Sieve X) (f : Y ⟶ X) :
    (J₁ ⊔ J₂).Covers S f ↔
      ∀ K : GrothendieckTopology C, J₁ ≤ K → J₂ ≤ K → K.Covers S f := by
  rw [GrothendieckTopology.covers_iff]
  constructor
  · intro hS K h₁K h₂K
    rw [GrothendieckTopology.covers_iff]
    exact le_covering.mp (sup_le h₁K h₂K) (S.pullback f) hS
  · intro h
    rw [← GrothendieckTopology.covers_iff]
    exact h (J₁ ⊔ J₂) le_sup_left le_sup_right

/-- Borne superieure d'une famille, caracterisation par recouvrement :
    `S ∈ sSup s X` si et seulement si `S ∈ K X` pour toute borne superieure
    `K` du membre `s`.
    Preuve : dans un sens `sSup_le` puis `le_covering` ; dans l'autre, prendre
    `K = sSup s`, borne superieure du membre par `le_sSup`. -/
theorem sSup_covering {C : Type*} [Category C] {X : C} (s : Set (GrothendieckTopology C))
    (S : Sieve X) :
    S ∈ sSup s X ↔ ∀ K : GrothendieckTopology C, (∀ J ∈ s, J ≤ K) → S ∈ K X := by
  constructor
  · intro hS K hK
    exact le_covering.mp (sSup_le hK) S hS
  · intro h
    exact h (sSup s) fun J hJ => le_sSup hJ

end Grothendieck.TopologyLattice
