/-
Grothendieck hommage — Partie 11 : Identités de génération des cribles

Alexandre Grothendieck (1928-2014).

Extension Phase 7 (#2159, Epic #1646).

La Partie 9 (CoverageGen.lean) a montré comment une couverture (donnée
plus simple qu'une topologie complète) engendre une topologie de
Grothendieck, en utilisant `Sieve.generate` pour transformer des
précaractères couvrants en cribles couvrants. Ce module étudie
l'opération `Sieve.generate` elle-même, et en consigne les identités
fondamentales :

  - Un préfaisceau s'injecte dans le crible qu'il engendre (`generate_extends`).
  - La connexion de Galois : `generate R ≤ S ↔ R ≤ S` (`generate_le_iff`).
  - Les cribles sont exactement les points fixes de la génération
    (`generate_sieve`) : générer le précaractère des flèches d'un
    crible redonne ce crible. C'est l'idempotence qui fait que « le
    crible engendré par un crible » est un no-op.
  - La génération est monotone dans le préfaisceau (`generate_monotone`).
  - La génération préserve les cribles maximal et minimal.
  - `generate R = ⊥` caractérise le préfaisceau vide
    (`generate_eq_bot_iff`).

Ces identités complètent le tableau ordinale de `Sieve.generate`, en
complément des identités de pullback de la Partie 6 (SieveLattice.lean)
et du récit « génération comme saturation » de la Partie 9
(CoverageGen.lean).

Mathlib 4 formalise déjà toute l'infrastructure `Sieve.generate` dans
`Mathlib.CategoryTheory.Sites.Grothendieck` :
  - `Sieve.generate : Presieve X → Sieve X` — la génération d'un crible
  - `Sieve.le_generate : R ≤ Sieve.generate R` — l'inclusion canonique
  - `Sieve.generate_le_iff : Sieve.generate R ≤ S ↔ R ≤ S` — la
    caractérisation de Galois
  - `Sieve.generate_sieve : Sieve.generate S = S` — l'idempotence sur
    les cribles (point fixe)
  - `Sieve.generate_mono : R₁ ≤ R₂ → Sieve.generate R₁ ≤ Sieve.generate R₂` —
    la monotonie
  - `Sieve.generate_top`, `Sieve.generate_bot` — préservation des bornes
  - `Sieve.generate_eq_bot_iff : Sieve.generate R = ⊥ ↔ R = ⊥` —
    caractérisation du vide

Ce module ré-expose ces faits dans le namespace `Grothendieck` comme un
parcours pédagogique structuré pour des apprenants découvrant
l'opération `Sieve.generate` :
  1. L'inclusion canonique (counit de la Galois insertion).
  2. La caractérisation de Galois (unit-counit).
  3. L'idempotence sur les cribles (points fixes).
  4. La monotonie.
  5. La préservation des bornes (⊤ et ⊥).
  6. La caractérisation du préfaisceau vide.

Epic #1646, Phase 7 (#2159). Aucun but non-résolu à la création.

### i18n — convention #4980 ratifiée 2026-07-04

Ce module est jumelé avec sa version anglaise canonique dans le fichier
sibling `SieveGenerate_en.lean` (modèle sibling pair, voir PR #6154
pour le pilote sur `Utility.lean`). Les énoncés de théorèmes, les noms
de lemmes, les tactiques Lean et les références Mathlib restent en
anglais (Mathlib 4, tactic DSL standard). Seules les **docstrings
`/-- ... -/`** et **commentaires `-- ...`** diffèrent entre les deux
fichiers. Anti-§D byte-identity garanti : le namespace body est préservé
bit-pour-bit (énoncés et preuves byte-identiques entre
`SieveGenerate.lean` et `SieveGenerate_en.lean`).
-/

import Mathlib.CategoryTheory.Sites.Grothendieck

namespace Grothendieck

open CategoryTheory

/-!
## Un préfaisceau s'injecte dans le crible qu'il engendre

`Sieve.generate R` est le plus petit crible contenant toutes les flèches
du préfaisceau `R`. En particulier `R` lui-même est contenu dans
`generate R`. C'est la counit de l'insertion de Galois `giGenerate`.
-/

/-- Tout préfaisceau est contenu dans le crible qu'il engendre. C'est
    `Sieve.le_generate` : `R ≤ Sieve.generate R`. -/
theorem generate_extends {C : Type*} [Category C] {X : C} (R : Presieve X) :
    R ≤ Sieve.generate R :=
  Sieve.le_generate R

/-!
## La connexion de Galois

La caractérisation fondamentale : `Sieve.generate R` est le plus petit
crible au-dessus de `R`. Équivalemment, `generate R ≤ S` vaut exactement
lorsque toute flèche de `R` appartient à `S`. C'est la relation
counit-unit de l'insertion de Galois entre préfaisceaux et cribles
(ordonnés par inclusion).
-/

/-- `Sieve.generate R ≤ S` ssi `R ≤ S` : le crible engendré est en
    dessous de `S` exactement quand le préfaisceau d'origine l'est.
    Restatement direct de `Sieve.generate_le_iff`. -/
theorem generate_le_iff {C : Type*} [Category C] {X : C}
    (R : Presieve X) (S : Sieve X) :
    Sieve.generate R ≤ S ↔ R ≤ S :=
  Sieve.generate_le_iff R S

/-!
## Les cribles sont les points fixes de la génération

Générer le crible associé à un préfaisceau qui est déjà *un* crible
redonne ce même crible. Cette idempotence exprime que les cribles sont
exactement les préfaisceaux saturés (downward-closed) : ce sont les
points fixes de `Sieve.generate`.
-/

/-- `Sieve.generate S = S` pour un crible `S` : les cribles sont les
    points fixes de la génération. Restatement de `Sieve.generate_sieve`. -/
theorem generate_sieve {C : Type*} [Category C] {X : C} (S : Sieve X) :
    Sieve.generate S = S :=
  Sieve.generate_sieve S

/-!
## La génération est monotone

Si `R₁ ≤ R₂` (comme préfaisceaux), alors le crible engendré par `R₁`
est contenu dans le crible engendré par `R₂`. C'est l'ombre
ordinale de `generate` étant adjoint à gauche (insertion de Galois).
-/

/-- `Sieve.generate` est monotone : `R₁ ≤ R₂` implique
    `Sieve.generate R₁ ≤ Sieve.generate R₂`. Utilise
    `Sieve.generate_mono`. -/
theorem generate_monotone {C : Type*} [Category C] {X : C}
    {R₁ R₂ : Presieve X} (h : R₁ ≤ R₂) :
    Sieve.generate R₁ ≤ Sieve.generate R₂ :=
  Sieve.generate_mono h

/-!
## La génération préserve les cribles maximal et minimal

Le crible maximal est engendré par le préfaisceau maximal, et le crible
vide par le préfaisceau vide. Ce sont les cas limites de la génération.
-/

/-- `Sieve.generate ⊤ = ⊤` : le préfaisceau maximal engendre le crible
    maximal. Restatement de `Sieve.generate_top`. -/
theorem generate_top {C : Type*} [Category C] (X : C) :
    Sieve.generate (⊤ : Presieve X) = ⊤ :=
  Sieve.generate_top

/-- `Sieve.generate ⊥ = ⊥` : le préfaisceau vide engendre le crible
    vide. Restatement de `Sieve.generate_bot`. -/
theorem generate_bot {C : Type*} [Category C] (X : C) :
    Sieve.generate (⊥ : Presieve X) = ⊥ :=
  Sieve.generate_bot

/-!
## Caractérisation du crible vide

Un préfaisceau engendre le crible vide exactement quand il est lui-même
vide. Cela suit de l'insertion de Galois (`generate` reflète l'élément
minimal). En combinant `generate_le_iff` avec le préfaisceau vide.
-/

/-- `Sieve.generate R = ⊥` ssi `R = ⊥` : seul le préfaisceau vide
    engendre le crible vide. Restatement de
    `Sieve.generate_eq_bot_iff`. -/
theorem generate_eq_bot_iff {C : Type*} [Category C] {X : C} (R : Presieve X) :
    Sieve.generate R = ⊥ ↔ R = ⊥ :=
  Sieve.generate_eq_bot_iff R

/-!
## Théorèmes propres (c.1301+129)

Les théorèmes ci-dessous *prouvent* des égalités définitionnelles et des
équivalences définitionnelles que les fields/lemmas de la structure
`Sieve X` exposent dans `Mathlib/CategoryTheory/Sites/Sieves.lean`.
Tous ces fields opèrent sur la structure résidente `Sieve X` non
polymorphe d'univers — donc **L902 ★★ SAFE** (cf c.1301+108-L1 ★★ :
les constructors polymorphes d'univers sont à proscrire, contrairement
aux fields résidents sur X).

1. `id_mem_iff_eq_top_field` : restatement de `Sieve.id_mem_iff_eq_top`
   (`S (𝟙 X) ↔ S = ⊤`, caractérise les cribles maximaux par l'identité).
2. `generate_of_contains_isSplitEpi_field` : restatement de
   `Sieve.generate_of_contains_isSplitEpi` (un préfaisceau qui contient
   un épimorphisme scindé engendre le crible maximal).
3. `generate_of_singleton_isSplitEpi_field` : restatement de
   `Sieve.generate_of_singleton_isSplitEpi` (cas particulier du précédent
   pour un préfaisceau singleton d'un épimorphisme scindé).
4. `arrows_eq_bot_iff_field` : restatement de `Sieve.arrows_eq_bot_iff`
   (`S.arrows = ⊥ ↔ S = ⊥`, caractérise le crible vide par ses arrows).
5. `comp_mem_iff_field` : restatement de `Sieve.comp_mem_iff` (pour un
   iso `i`, `S (i ≫ f) ↔ S f` : la composition avec un iso préserve
   l'appartenance à un crible).

Ce sont des théorèmes « vitrines » qui certifient que ces fields/lemmas
de la structure `Sieve X` sont effectivement calculables dans la même
exécution Lean.
-/

/-- Théorème : `S (𝟙 X) ↔ S = ⊤` — un crible contient l'identité ssi
    il est le crible maximal. β-équivalent au lemma
    `Sieve.id_mem_iff_eq_top`. -/
theorem id_mem_iff_eq_top_field {C : Type*} [Category C]
    {X : C} {S : Sieve X} :
    S (𝟙 X) ↔ S = ⊤ :=
  Sieve.id_mem_iff_eq_top

/-- Théorème : `Sieve.generate R = ⊤` dès que `R` contient un
    épimorphisme scindé. β-équivalent au lemma
    `Sieve.generate_of_contains_isSplitEpi`. -/
theorem generate_of_contains_isSplitEpi_field {C : Type*} [Category C]
    {X Y : C} {R : Presieve X} (f : Y ⟶ X) [IsSplitEpi f] (hf : R f) :
    Sieve.generate R = ⊤ :=
  Sieve.generate_of_contains_isSplitEpi f hf

/-- Théorème : `Sieve.generate (Presieve.singleton f) = ⊤` pour tout
    épimorphisme scindé `f`. Cas particulier du précédent. β-équivalent
    au lemma `Sieve.generate_of_singleton_isSplitEpi`. -/
theorem generate_of_singleton_isSplitEpi_field {C : Type*} [Category C]
    {X Y : C} (f : Y ⟶ X) [IsSplitEpi f] :
    Sieve.generate (Presieve.singleton f) = ⊤ :=
  Sieve.generate_of_singleton_isSplitEpi f

/-- Théorème : `S.arrows = ⊥ ↔ S = ⊥` — le crible a ses arrows vides
    ssi c'est le crible vide. β-équivalent au lemma
    `Sieve.arrows_eq_bot_iff`. -/
theorem arrows_eq_bot_iff_field {C : Type*} [Category C]
    {X : C} {S : Sieve X} :
    S.arrows = ⊥ ↔ S = ⊥ :=
  Sieve.arrows_eq_bot_iff

/-- Théorème : pour un iso `i`, `S (i ≫ f) ↔ S f`. La composition avec
    un iso préserve l'appartenance à un crible. β-équivalent au lemma
    `Sieve.comp_mem_iff`. -/
theorem comp_mem_iff_field {C : Type*} [Category C]
    {X Y Z : C} (i : X ⟶ Y) (f : Y ⟶ Z) [IsIso i] (S : Sieve Z) :
    S (i ≫ f) ↔ S f :=
  Sieve.comp_mem_iff i f S

end Grothendieck