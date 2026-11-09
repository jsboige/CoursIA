/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Hommage Grothendieck — Partie 59 : La topologie de Lawvere–Tierney — l'opérateur de clôture sur Ω

Alexandre Grothendieck (1928-2014).

Extension de #2159 (EPIC #1646).

Les parties 1-44 ont établi le socle : catégories, cribles, topologies, lois
de treillis (`SieveLattice`), faisceaux, faisceautisation. Les parties 45-57
ont systématisé la forme flèche de la couverture. La Partie 58 a franchi un
seuil en exhibant le **classifieur de sous-objets** Ω = `Functor.sieves`, le
préfaisceau des cribles.

Cette partie pose l'autre moitié de la structure de topos élémentaire : la
**topologie de Lawvere–Tierney**. Une topologie de Lawvere–Tierney est un
opérateur de clôture `j` sur Ω — en chaque objet `X`, une application
`Sieve X → Sieve X` — qui satisfait trois lois :

  - **extensivité** : `S ≤ j S` (tout crible est contenu dans sa clôture) ;
  - **idempotence** : `j (j S) = j S` (la clôture d'une clôture est close) ;
  - **préservation des meets** : `j (S ⊓ T) = j S ⊓ j T` (la clôture commute
    à l'intersection finie).

avec en sus une **naturalité** par rapport au pullback : `j (S.pullback f) =
(j S).pullback f`. La naturalité est ce qui fait de `j` un opérateur **global**
sur le préfaisceau Ω plutôt qu'une famille d'opérateurs locaux sans lien.

C'est aussi l'opérateur de clôture que la Partie 6 a parcouru pour les cribles
sous un autre nom : `pullback_imap`, `pullback_iinf` sont des morceaux de la
structure de treillis de Ω ; la Partie 59 montre que la clôture de Lawvere–
Tierney est le geste dual qui, sur ce treillis, découpe les cribles **clos**.

Deux topologies canoniques la réalisent, aux deux extrémités du spectre :

  - **discrète** (`j S = S`) : la clôture est l'identité, tout crible est clos ;
  - **indiscrete** (`j S = ⊤`) : la clôture est maximale, seuls `⊤` est clos.

Toutes deux vérifient les trois lois — la première trivialement, la seconde par
les lois de `Sieve` (`pullback_top`, `le_top`, `inf_idem`). La **frontière
honnête** de cette partie : la correspondance « topologie de Grothendieck
↔ topologie de Lawvere–Tierney » (le `j` induit par la clôture `J`-closure)
exige un opérateur `GrothendieckTopology.closure` absent de Mathlib v4.32.1 ;
elle reste hors de portée de cette partie, comme l'instance `ElementaryTopos`
l'était pour la Partie 58.

Tous les `sorry`s éliminés à la création.

### Note d'accessibilité (Epics #1452/#1453)

Ce module expose **6 vérifications `#check`**, **1 structure**, **2 topologies
canoniques** et **4 théorèmes propres** : (1) la structure `LawvereTierney` ;
(2) la topologie discrète ; (3) la topologie indiscrete ; (4) la loi du haut,
la monotonie et la fermeture de la clôture ; (5) les cribles clos de la
topologie indiscrete.

### Convention i18n (EPIC #4980 ratifiée par user 2026-07-04)

Ce module est jumelé avec sa version anglaise canonique dans le fichier sibling
`LawvereTierney_en.lean` (modèle sibling pair). Namespace suffixé `_en` (anti-
collision). Les `#check`, signatures, variables et univers sont byte-identiques
entre les deux fichiers ; seules les docstrings et commentaires diffèrent.
-/

import Mathlib.CategoryTheory.Topos.Sheaf

universe u v

namespace Grothendieck.LawvereTierney

open CategoryTheory

variable {C : Type u} [Category.{v} C]

/-!
## Section 1 : La structure

Une **topologie de Lawvere–Tierney** sur Ω est un opérateur de clôture
`closure : ∀ X, Sieve X → Sieve X` naturel en `X` (compatible avec le pullback)
et vérifiant les trois lois : extensivité, idempotence, préservation des meets.
Matériel Mathlib nécessaire : le treillis complet des cribles (`CompleteLattice
(Sieve X)`, donc `≤`, `⊓`, `⊤`, `le_inf`, `le_top`), le pullback `Sieve.pullback`
et ses lois (`pullback_top`, `pullback_inter`, `pullback_id`, `pullback_comp`).
-/

-- CALIBRATION : le treillis des cribles et son pullback.
#check @Sieve.ext               -- extensionalité : R = S ssi ∀ Y f, R f ↔ S f
#check @Sieve.top_apply         -- (⊤ : Sieve X) f : tout crible maximal contient f
#check @Sieve.pullback          -- pullback d'un crible le long d'une flèche
#check @Sieve.pullback_top      -- (⊤ : Sieve X).pullback f = ⊤
#check @Sieve.pullback_inter    -- (S ⊓ R).pullback f = S.pullback f ⊓ R.pullback f
#check @Sieve.pullback_id       -- S.pullback (𝟙 _) = S

/-- Une **topologie de Lawvere–Tierney** sur le topos des préfaisceaux de `C`.

    Elle est donnée par un opérateur `closure` sur les cribles, naturel en `X`
    (compatible au pullback), extensif (`S ≤ closure S`), idempotent
    (`closure (closure S) = closure S`) et préservant les meets finis
    (`closure (S ⊓ T) = closure S ⊓ closure T`). C'est exactement l'opérateur
    de clôture dont les points fixes sont les cribles **clos** — la structure
    déduale du sous-objet que la Partie 58 a classifié. -/
structure LawvereTierney (C : Type u) [Category.{v} C] where
  /-- L'opérateur de clôture : en chaque objet `X`, un endomorphisme de `Sieve X`. -/
  closure : ∀ X : C, Sieve X → Sieve X
  /-- Naturalité : la clôture commute au pullback — `j` est un opérateur global
      sur Ω, pas une famille locale sans lien. -/
  maps_pullback : ∀ ⦃X Y : C⦄ (f : Y ⟶ X) (S : Sieve X),
    closure Y (S.pullback f) = (closure X S).pullback f
  /-- Extensivité : tout crible est contenu dans sa clôture. -/
  extensive : ∀ X (S : Sieve X), S ≤ closure X S
  /-- Idempotence : la clôture d'un crible est close. -/
  idempotent : ∀ X (S : Sieve X), closure X (closure X S) = closure X S
  /-- Préservation des meets : la clôture commute à l'intersection finie. -/
  preserve_meet : ∀ X (S T : Sieve X), closure X (S ⊓ T) = closure X S ⊓ closure X T

/-- Un crible `S` est **clos** pour la topologie `j` s'il est un point fixe de
    la clôture : `closure S = S`. Les cribles clos sont précisément ceux qui
    sont stables sous `j` — le sous-objet que la Partie 58 appelle clos. -/
def IsClosed (j : LawvereTierney C) {X : C} (S : Sieve X) : Prop :=
  j.closure X S = S

/-!
## Section 2 : La topologie discrète

La clôture identité `j S = S` est une topologie de Lawvere–Tierney : la
**topologie discrète**. Tout crible est clos — la clôture ne sépare rien. Les
trois lois sont triviales (`S ≤ S`, `S = S`, `S ⊓ T = S ⊓ T`).
-/

/-- La topologie **discrète** : `j S = S`. La clôture est l'identité ; tout
    crible est clos. Extensivité par `le_refl`, idempotence et préservation des
    meets par réflexivité. -/
def lawvereTierneyDiscrete : LawvereTierney C where
  closure := fun X S => S
  maps_pullback := by
    intro X Y f S
    rfl
  extensive := by
    intro X S
    exact le_refl S
  idempotent := by
    intro X S
    rfl
  preserve_meet := by
    intro X S T
    rfl

/-!
## Section 3 : La topologie indiscrete

La clôture constante `j S = ⊤` est une topologie de Lawvere–Tierney : la
**topologie indiscrete** (grosse). Seul le crible maximal `⊤` est clos ; tout
autre crible est « fermé » de force en `⊤`. Les lois tiennent par les lois de
`Sieve` : pullback du haut (`pullback_top`), majorant (`le_top`), idempotence
et `inf_idem` pour le meet.
-/

/-- La topologie **indiscrete** : `j S = ⊤`. La clôture est constante maximale ;
    seul le crible maximal est clos. Extensivité par `le_top`, naturalité par
    `Sieve.pullback_top`, meet par `inf_idem`. -/
def lawvereTierneyIndiscrete : LawvereTierney C where
  closure := fun X S => ⊤
  maps_pullback := by
    intro X Y f S
    simp
  extensive := by
    intro X S
    exact le_top
  idempotent := by
    intro X S
    rfl
  preserve_meet := by
    intro X S T
    simp

/-!
## Section 4 : Les lois propres d'une topologie de Lawvere–Tierney

Les théorèmes qui font de `closure` un opérateur de clôture digne de ce nom :
la clôture du crible maximal est maximale, la clôture est **monotone** (préserve
l'ordre — dérivée de la préservation des meets), et la clôture de n'importe
quel crible est **close**.
-/

/-- LA LOI DU HAUT : la clôture du crible maximal est le crible maximal.
    Déduite de l'extensivité (`⊤ ≤ j ⊤`) et du fait que `j ⊤ ≤ ⊤` puisque
    `⊤` est l'élément maximum. -/
theorem j_top (j : LawvereTierney C) (X : C) :
    j.closure X (⊤ : Sieve X) = ⊤ :=
  le_antisymm le_top (j.extensive X (⊤ : Sieve X))

/-- PROPRE : la clôture est **monotone** — `S ≤ T` implique `j S ≤ j T`.
    La preuve est une conséquence de la préservation des meets : `S ≤ T` donne
    `S ⊓ T = S`, donc `j S = j (S ⊓ T) = j S ⊓ j T`, et l'intersection est
    majorée par chaque facteur. C'est ce qui fait de `closure` un opérateur de
    clôture (une clôture préserve l'ordre), pas une simple involution. -/
theorem j_monotone (j : LawvereTierney C) {X : C} {S T : Sieve X} (h : S ≤ T) :
    j.closure X S ≤ j.closure X T := by
  have h_eq_inf : S ⊓ T = S := le_antisymm inf_le_left (le_inf le_rfl h)
  have h_meet : j.closure X (S ⊓ T) = j.closure X S ⊓ j.closure X T :=
    j.preserve_meet X S T
  rw [h_eq_inf] at h_meet
  calc
    j.closure X S = j.closure X S ⊓ j.closure X T := h_meet
    _ ≤ j.closure X T := inf_le_right

/-- PROPRE : la clôture de n'importe quel crible est **close** — c'est
    l'idempotence, relue comme une propriété de `IsClosed`. La clôture d'une
    clôture ne bouge plus : les clôtures sont exactement les points fixes. -/
theorem closure_isClosed (j : LawvereTierney C) {X : C} (S : Sieve X) :
    IsClosed j (j.closure X S) := j.idempotent X S

/-!
## Section 5 : Les cribles clos de la topologie indiscrete

Pour la topologie discrète, `IsClosed` est trivialement vrai pour tout crible.
Pour la topologie indiscrete, la caractérisation est informative : un crible est
clos exactement quand il est le crible maximal — la clôture ne laisse qu'un
point fixe, le haut du treillis.
-/

/-- PROPRE : pour la topologie indiscrete, un crible est clos ssi c'est le
    crible maximal `⊤`. La clôture constante en `⊤` n'a qu'un point fixe. -/
theorem indiscrete_closed_iff_top {X : C} (S : Sieve X) :
    IsClosed lawvereTierneyIndiscrete S ↔ S = ⊤ :=
  Iff.intro (fun h => h.symm) (fun h => h.symm)

/-!
## Section 6 : Récapitulatif de la structure

La Partie 58 a exhibé le classifieur de sous-objets `Ω` ; cette partie installe
l'opérateur de clôture qui le découpe. La structure `LawvereTierney` est ce qui
manquait à `Ω` pour être un topos élémentaire : classifieur (58) + clôtures
de Lawvere–Tierney (59). Les deux réalisations canoniques (discrète et
indiscrete) sont les extrémités du spectre ; la monotonie relie la clôture à
l'ordre du treillis des cribles.
-/

end Grothendieck.LawvereTierney
