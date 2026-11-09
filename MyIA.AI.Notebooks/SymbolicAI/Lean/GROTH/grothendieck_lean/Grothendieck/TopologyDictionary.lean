/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Hommage Grothendieck — Partie 60 : Le dictionnaire Grothendieck ↔ Lawvere–Tierney

Alexandre Grothendieck (1928-2014).

Extension de #2159 (EPIC #1646).

La Partie 58 a établi le **classifieur de sous-objets** Ω = le préfaisceau des
cribles ; la Partie 59 a posé la **topologie de Lawvere–Tierney** comme
opérateur de clôture `j` sur Ω. La Partie 59 s'arrêtait sur une frontière
explicite : « la correspondance topologie de Grothendieck ↔ topologie de
Lawvere–Tierney exige un opérateur `GrothendieckTopology.closure` absent de
Mathlib v4.32.1 ; elle reste hors de portée de cette partie ».

Cette partie ferme cette frontière : le dictionnaire est **complet et
bidirectionnel**. L'opérateur manquant n'a pas besoin d'exister dans Mathlib —
il se construit depuis les axiomes bruts :

  - **Sens J → j** : à toute topologie de Grothendieck `J`, la **clôture**
    `jClosure J S := {f | S.pullback f ∈ J}` est une topologie de Lawvere–Tierney
    (`grothendieckToLawvereTierney`). Les trois lois se déduisent des trois
    axiomes : extensivité par `mem_iff_pullback_eq_top` + `top_mem` ;
    idempotence par l'axiome de **transitivité** (qui est littéralement le
    miroir de la définition de la clôture) ; préservation des meets par
    `pullback_inter` + `cover_inf_iff`.
  - **Sens j → J** : à toute topologie de Lawvere–Tierney `j`, les cribles
    **denses** `S` tels que `j S = ⊤` forment une topologie de Grothendieck
    (`lawvereTierneyToGrothendieck`). La transitivité — le seul axiome non
    trivial — se déduit de la monotonie et de l'idempotence de la Partie 59 :
    `S ≤ j R` puis `⊤ = j S ≤ j (j R) = j R`.
  - **Round-trips** : les deux constructions sont inverses l'une de l'autre —
    `J` se retrouve à l'identique (membership des cribles couvrants), et `j`
    se retrouve à l'identique (clôture point par point).

Le théorème-pont : sur une catégorie `C`, **topologies de Grothendieck et
topologies de Lawvere–Tierney sont la même chose** — la vision « site »
(SGA 4) et la vision « topos élémentaire » (Lawvere–Tierney) coïncident au
niveau préfaisceau. C'est le pont que Mac Lane–Moerdijk appellent la
correspondance entre topologies sur un site et topologies sur son topos de
préfaisceaux.

Tous les `sorry`s éliminés à la création.

### Note d'accessibilité (Epics #1452/#1453)

Ce module expose **7 vérifications `#check`**, **3 constructions** (la clôture
`jClosure` et les deux transports du dictionnaire) et **10 théorèmes propres**,
dont les deux round-trips. Chaque preuve est calculatoire : extensionalité de
cribles + réécriture par les identités de la Partie 6 et les lois de la
Partie 59 — aucune tactique de haut niveau.

### Convention i18n (EPIC #4980 ratifiée par user 2026-07-04)

Ce module est jumelé avec sa version anglaise canonique dans le fichier sibling
`TopologyDictionary_en.lean` (modèle sibling pair, miroir auto-contenu).
Namespace suffixé `_en` (anti-collision). Les `#check`, signatures, variables
et univers sont byte-identiques entre les deux fichiers ; seules les docstrings
et commentaires diffèrent.
-/

import Mathlib.CategoryTheory.Sites.Grothendieck

import Grothendieck.LawvereTierney
import Grothendieck.SieveLattice
import Grothendieck.SieveOps

universe u v

namespace Grothendieck.TopologyDictionary

open CategoryTheory
open Grothendieck.LawvereTierney

variable {C : Type u} [Category.{v} C]

/-!
## Section 0 : Calibration

Le matériel Mathlib requis : les trois axiomes de `GrothendieckTopology`
(`top_mem`, `pullback_stable`, `transitive`), ses deux lemmes de clôture
(`superset_covering`, `intersection_covering`), le treillis des cribles et le
pullback. Rien au-delà de ce que les Parties 1, 6 et 8 ont déjà parcouru.
-/

-- CALIBRATION : les trois axiomes d'une topologie de Grothendieck.
#check @GrothendieckTopology.top_mem           -- ⊤ ∈ J.sieves X (axiome 1)
#check @GrothendieckTopology.pullback_stable   -- stabilité par pullback (axiome 2)
#check @GrothendieckTopology.transitive        -- caractère local (axiome 3)
-- CALIBRATION : les lemmes de clôture des cribles couvrants.
#check @GrothendieckTopology.superset_covering     -- sur-crible d'un couvrant
#check @GrothendieckTopology.intersection_covering -- intersection de couvrants
-- CALIBRATION : le treillis des cribles et le pullback (Parties 1 et 6).
#check @Sieve.pullback_top                     -- (⊤ : Sieve X).pullback f = ⊤
#check @Sieve.pullback_inter                   -- le pullback distribue sur ⊓

/-!
## Section 1 : Le pont d'appartenance

Une flèche `g` appartient au pullback `R.pullback f` exactement quand le
composé `g ≫ f` appartient à `R` ; et une flèche `f` appartient à `R`
exactement quand l'identité appartient au pullback `R.pullback f`. Ce second
pont est la clé du dictionnaire : il traduit « être couvrant » (membership en
`J`) en « être clos au sommet » (égalité à `⊤` en `j`).
-/

/-- PROPRE : `g` vit dans le pullback de `R` le long de `f` ssi le composé
    `g ≫ f` vit dans `R` — lecture directe de la définition Mathlib. -/
theorem mem_pullback_iff {X Y Z : C} (R : Sieve X) (f : Y ⟶ X) (g : Z ⟶ Y) :
    (R.pullback f) g ↔ R (g ≫ f) := by
  simp [Sieve.pullback]

/-- PROPRE : `f` appartient à un crible ssi l'identité appartient au pullback
    de ce crible le long de `f`. C'est le pont « membership ↔ pullback en le
    sommet » qui transporte la densité de `j` vers la couverture de `J`. -/
theorem mem_iff_id_mem_pullback {X Y : C} (R : Sieve X) (f : Y ⟶ X) :
    R f ↔ (R.pullback f) (𝟙 Y) := by
  rw [mem_pullback_iff, Category.id_comp]

/-!
## Section 2 : Sens J → j — la clôture d'une topologie de Grothendieck

La **clôture** d'un crible `S` pour une topologie `J` : l'ensemble des flèches
`f` telles que le pullback de `S` le long de `f` est couvrant. C'est
l'opérateur que Mathlib v4.32.1 ne fournit pas — il se construit depuis les
axiomes bruts, et sa descente par composition est exactement l'axiome 2.
-/

/-- La **clôture J** d'un crible `S` : les flèches `f : Y ⟶ X` telles que
    `S.pullback f` couvre `Y`. La fermeture vers le bas est l'axiome de
    stabilité par pullback ; l'extensionalité des cribles fait le reste. -/
def jClosure (J : GrothendieckTopology C) {X : C} (S : Sieve X) : Sieve X where
  arrows := fun Y f => S.pullback f ∈ J Y
  downward_closed := by
    intro Y Z f hf g
    show S.pullback (g ≫ f) ∈ J Z
    rw [← pullback_pullback]
    exact J.pullback_stable g hf

/-- PROPRE : appartenir à la clôture J, c'est couvrir après pullback —
    l'égalité définitionnelle, énoncée comme pont réutilisable. -/
theorem mem_jClosure_iff (J : GrothendieckTopology C) {X Y : C}
    (S : Sieve X) (f : Y ⟶ X) :
    (jClosure J S) f ↔ S.pullback f ∈ J Y :=
  Iff.rfl

/-- PROPRE : la clôture J est **naturelle** — le diagramme du pullback
    commute à la clôture. Preuve : extensionalité + l'identité d'associativité
    `pullback_pullback` de la Partie 6. -/
theorem jClosure_pullback (J : GrothendieckTopology C) {X Y : C}
    (f : Y ⟶ X) (S : Sieve X) :
    jClosure J (S.pullback f) = (jClosure J S).pullback f := by
  ext Z g
  rw [mem_jClosure_iff, mem_pullback_iff, mem_jClosure_iff, pullback_pullback]

/-- PROPRE : la clôture J d'un couvrant est couvrante. C'est le sens facile
    de la transitivité : le crible `S.pullback f` couvre pour toute flèche de
    la clôture, donc la clôture « contient assez » de flèches. -/
theorem jClosure_mem (J : GrothendieckTopology C) {X : C} {S : Sieve X}
    (h : S ∈ J X) : jClosure J S ∈ J X := by
  have htop : jClosure J S = ⊤ := by
    ext Y f
    exact ⟨fun _ => trivial, fun _ => J.pullback_stable f h⟩
  rw [htop]
  exact J.top_mem X

/-- PROPRE : un crible dont la clôture couvre est couvrant — le sens non
    trivial, qui EST l'axiome de transitivité : la clôture de `S` couvre et
    chacune de ses flèches pullback `S` en un couvrant, donc `S` couvre.
    La preuve est le miroir exact de la définition de `jClosure`. -/
theorem mem_of_mem_jClosure (J : GrothendieckTopology C) {X : C} {S : Sieve X}
    (h : jClosure J S ∈ J X) : S ∈ J X :=
  J.transitive h S (fun _ _ hf => hf)

/-- PROPRE : le pont central du sens J → j — la clôture d'un crible est
    couvrante si et seulement si le crible l'est. La clôture J ne crée pas de
    nouvelle couverture : elle dilate chaque crible en le plus grand crible
    de même couverture locale. -/
theorem covering_iff_jClosure (J : GrothendieckTopology C) {X : C}
    {S : Sieve X} :
    jClosure J S ∈ J X ↔ S ∈ J X :=
  ⟨mem_of_mem_jClosure J, jClosure_mem J⟩

/-- **Sens J → j du dictionnaire** : toute topologie de Grothendieck induit
    une topologie de Lawvere–Tierney — sa clôture. Extensivité : une flèche de
    `S` rend son pullback maximal (`mem_iff_pullback_eq_top`, Partie 6), donc
    couvrant (axiome 1). Idempotence : par le pont central. Meets : le pullback
    distribue sur ⊓ (Partie 6) et l'intersection de couvrants couvre
    (Partie 8). -/
def grothendieckToLawvereTierney (J : GrothendieckTopology C) :
    LawvereTierney C where
  closure := fun X => jClosure J
  maps_pullback := fun _ _ f S => jClosure_pullback J f S
  extensive := by
    intro X S Y f hf
    show S.pullback f ∈ J _
    rw [(mem_iff_pullback_eq_top S f).1 hf]
    exact J.top_mem _
  idempotent := by
    intro X S
    ext Z g
    rw [mem_jClosure_iff, ← jClosure_pullback, covering_iff_jClosure,
      mem_jClosure_iff]
  preserve_meet := by
    intro X S T
    ext Z g
    rw [mem_jClosure_iff, Sieve.inter_apply, mem_jClosure_iff, mem_jClosure_iff,
      Sieve.pullback_inter, cover_inf_iff]

/-!
## Section 3 : Sens j → J — les cribles denses d'une topologie de Lawvere–Tierney

Les cribles que `j` envoie sur le crible maximal sont les **denses**. Les trois
axiomes d'une topologie de Grothendieck tombent : le haut est dense (`j_top`,
Partie 59), la stabilité par pullback est la naturalité de `j`, et la
transitivité est la chaîne `S ≤ j R` puis `⊤ = j S ≤ j (j R) = j R` —
monotonie puis idempotence.
-/

/-- **Sens j → J du dictionnaire** : toute topologie de Lawvere–Tierney induit
    une topologie de Grothendieck — ses cribles denses `j S = ⊤`. La preuve de
    la transitivité est la chaîne centrale du dictionnaire : chaque flèche de
    `S` est dans `j R` (l'identité vit dans un pullback devenu maximal), puis
    la monotonie et l'idempotence de la Partie 59 hissent `j R` au-dessus de
    `⊤`. -/
def lawvereTierneyToGrothendieck (j : LawvereTierney C) :
    GrothendieckTopology C where
  sieves X := {S | j.closure X S = ⊤}
  top_mem' := by
    intro X
    exact j_top j X
  pullback_stable' := by
    intro X Y S f hS
    have hS' : j.closure X S = ⊤ := hS
    show j.closure Y (S.pullback f) = ⊤
    rw [j.maps_pullback, hS', Sieve.pullback_top]
  transitive' := by
    intro X S hS R hR
    have hS' : j.closure X S = ⊤ := hS
    have hsub : S ≤ j.closure X R := by
      intro Y f hf
      have hd : j.closure Y (R.pullback f) = ⊤ := hR hf
      rw [mem_iff_id_mem_pullback, ← j.maps_pullback, hd]
      trivial
    have hmono : j.closure X S ≤ j.closure X (j.closure X R) :=
      j_monotone j hsub
    rw [j.idempotent, hS'] at hmono
    show j.closure X R = ⊤
    exact le_antisymm le_top hmono

/-!
## Section 4 : Les round-trips — le dictionnaire est une bijection

Les deux transports sont inverses l'un de l'autre. Le premier round-trip se
lit sur les cribles couvrants : `S` est dense pour la clôture de `J` exactement
quand `S` couvre pour `J`. Le second se lit sur les opérateurs : la clôture
extraite des denses de `j` redonne `j` point par point.
-/

/-- PROPRE : premier round-trip, en membership — les cribles denses de la
    clôture de `J` sont exactement les cribles couvrants de `J`. Sens direct :
    l'identité vit dans une clôture maximale, et le pullback le long de
    l'identité est `S` lui-même (`pullback_id`, Partie 6). Sens retour :
    stabilité par pullback, flèche par flèche. -/
theorem mem_lawvereTierney_toGrothendieck_iff (J : GrothendieckTopology C)
    {X : C} {S : Sieve X} :
    S ∈ lawvereTierneyToGrothendieck
        (grothendieckToLawvereTierney J) X ↔ S ∈ J X := by
  constructor
  · intro h
    rw [← GrothendieckTopology.mem_sieves_iff_coe] at h
    simp only [lawvereTierneyToGrothendieck, grothendieckToLawvereTierney,
      Set.mem_setOf_eq] at h
    have h1 : (jClosure J S) (𝟙 X) := by
      rw [h]
      trivial
    rw [mem_jClosure_iff] at h1
    rwa [pullback_id] at h1
  · intro h
    rw [← GrothendieckTopology.mem_sieves_iff_coe]
    simp only [lawvereTierneyToGrothendieck, grothendieckToLawvereTierney,
      Set.mem_setOf_eq]
    ext Y f
    exact ⟨fun _ => trivial, fun _ => J.pullback_stable f h⟩

/-- PROPRE : premier round-trip, en égalité de topologies — repartir de `J`,
    passer en Lawvere–Tierney puis revenir, redonne `J` à l'identifique. -/
theorem lawvereTierneyToGrothendieck_comp_grothendieckToLawvereTierney
    (J : GrothendieckTopology C) :
    lawvereTierneyToGrothendieck (grothendieckToLawvereTierney J) = J := by
  apply le_antisymm
  · rw [GrothendieckTopology.le_def]
    intro X S hS
    exact (mem_lawvereTierney_toGrothendieck_iff J).1 hS
  · rw [GrothendieckTopology.le_def]
    intro X S hS
    exact (mem_lawvereTierney_toGrothendieck_iff J).2 hS

/-- PROPRE : second round-trip — la clôture extraite des denses de `j` redonne
    `j` en chaque crible. Une flèche `f` est dans la clôture extraite ssi le
    pullback de `S` le long de `f` est dense, ssi `(j S).pullback f` est
    maximal (naturalité), ssi enfin `f` vit dans `j S` (pont de la Section 1). -/
theorem grothendieckToLawvereTierney_comp_lawvereTierneyToGrothendieck_closure
    (j : LawvereTierney C) :
    (grothendieckToLawvereTierney (lawvereTierneyToGrothendieck j)).closure
      = j.closure := by
  funext X S
  simp only [grothendieckToLawvereTierney]
  ext Y f
  rw [mem_jClosure_iff, ← GrothendieckTopology.mem_sieves_iff_coe]
  simp only [lawvereTierneyToGrothendieck, Set.mem_setOf_eq]
  rw [j.maps_pullback, ← mem_iff_pullback_eq_top]

/-!
## Section 5 : Récapitulatif du dictionnaire

La vue « site » de SGA 4 — une topologie de Grothendieck, trois axiomes sur
des cribles couvrants — et la vue « topos élémentaire » de Lawvere–Tierney —
un opérateur de clôture sur le classifieur Ω — décrivent **la même donnée** :

  J ↦ jClosure J          (sens J → j, Section 2)
  j ↦ {S | j S = ⊤}        (sens j → J, Section 3)
  round-trips              (Section 4 : bijection)

Les Parties 58 (Ω), 59 (j) et 60 (le dictionnaire) bouclent ainsi la moitié
élémentaire de la théorie : le préfaisceau des cribles d'un site est un topos
élémentaire dont les topologies de Lawvere–Tierney sont exactement les
topologies du site.
-/

end Grothendieck.TopologyDictionary
