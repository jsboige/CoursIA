/-
Grothendieck hommage — Partie 61 : foncteurs continus et lemme de comparaison.

Alexandre Grothendieck (1928-2014).

Extension Phase 2 (#2159, Epic #1646).

Un morphisme de sites ne se contente pas de transporter des cribles : il
transporte des **faisceaux**. La Partie 60 (`TopologyDictionary.lean`) a fermé
la frontière Grothendieck ↔ Lawvere–Tierney côté topologies ; celle-ci la
ferme côté faisceaux. Le pont central est le foncteur continu :

  - `Functor.IsContinuous F J K` : `F : C ⥤ D` est continu lorsque la
    précomposition par `F.op` préserve la condition de faisceau — c'est la
    donnée `op_comp_isSheaf_of_types`. C'est l'exact analogue, niveau
    faisceaux, de ce que `pullback_monotone` (`SieveLattice.lean`) établit
    niveau cribles : tirer en arrière respecte la structure.

  - `Functor.sheafPushforwardContinuous` : le foncteur induit
    `Sheaf K A ⥤ Sheaf J A`. Au niveau préfaisceau, pousser en avant n'est
    qu'une précomposition (`whiskeringLeft`) ; niveau faisceaux, il faut et
    il suffit que `F` soit continu pour que l'image d'un faisceau reste un
    faisceau — le carré `sheafPushforwardContinuousCompSheafToPresheafIso`
    exprime cette compatibilité.

Ce module enregistre les identités fondamentales du pushforward continu :

  - `sheafPushforwardContinuous_comp_sheafToPresheaf` : le carré commute —
    oublier le faisceau après pushforward continu égale précomposer d'abord
  - `sheafPushforwardContinuous_id` : pushforward le long de l'identité
  - `sheafPushforwardContinuous_comp` : les pushforwards composent
    (contravariance en les foncteurs)
  - `adjunction_sheafPushforwardContinuous` : **le lemme de comparaison** —
    si `F ⊣ G` avec `F` et `G` continus, les pushforwards continus sur les
    catégories de faisceaux sont eux-mêmes adjoints (SGA 4 III.1.6). C'est
    l'ingrédient opérationnel du théorème de comparaison : il permet de
    transporter les adjonctions de préfaisceaux vers les faisceaux sans
    jamais invoquer la sheafification à la main.

Ces identités complètent le tableau commencé par les Parties 8-9
(`SieveOps.lean`, `SieveLattice.lean` : le pullback niveau cribles) et
`DirectImage.lean` (l'adjonction `f^* ⊣ f_*` niveau schémas) : elles en
fournissent la généralisation niveau **sites arbitraires**.

Epic #1646, Phase 2 (#2159). Tous les `sorry`s éliminés à la création.

### i18n — convention #4980 ratifiée 2026-07-04

Ce module est jumelé avec sa version anglaise canonique dans le fichier
sibling `SitesComparison_en.lean` (modèle sibling pair, voir PR #6154 pour le
pilote sur `Utility.lean`). Les énoncés de théorèmes, les noms de lemmes,
les tactiques Lean (`:= by`, `rfl`, `exact`, etc.) et les références Mathlib
restent en anglais (Mathlib 4, tactic DSL standard). Seules les **docstrings
`/-- ... -/`** et **commentaires `-- ...`** diffèrent entre les deux fichiers.
Anti-§D byte-identity garanti : le namespace body est préservé bit-à-bit
(énoncés et preuves byte-identiques entre `SitesComparison.lean` et
`SitesComparison_en.lean`).
-/

import Mathlib.CategoryTheory.Sites.Continuous

namespace Grothendieck

open CategoryTheory

/-!
## Le carré commute : pushforward continu et oubli des faisceaux

Pousser en avant un faisceau puis oublier qu'il est un faisceau égale
précomposer le préfaisceau sous-jacent par `F.op`. C'est la définition-même
du foncteur `sheafPushforwardContinuous` (construit par `ObjectProperty.lift`)
: le diagramme

    Sheaf K A --sheafPushforwardContinuous--> Sheaf J A
       |                                      |
       sheafToPresheaf                        sheafToPresheaf
       v                                      v
    Cᵒᵖ ⥤ A ---(whiskeringLeft).obj F.op---> Dᵒᵖ ⥤ A

commute strictement (l'iso est `Iso.refl`).
-/

/-- COMPARAISON (Iso.refl) : le carré pushforward continu / oubli des
    faisceaux commute — implémentation via
    `Functor.sheafPushforwardContinuousCompSheafToPresheafIso`. (Un `def` :
    un `Iso` est une structure data-carrying, non une `Prop`.) -/
def sheafPushforwardContinuous_comp_sheafToPresheaf
    {C D : Type*} [Category C] [Category D] {A : Type*} [Category A]
    (F : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [Functor.IsContinuous F J K] :
    F.sheafPushforwardContinuous A J K ⋙ sheafToPresheaf J A ≅
      sheafToPresheaf K A ⋙ (Functor.whiskeringLeft _ _ _).obj F.op :=
  Functor.sheafPushforwardContinuousCompSheafToPresheafIso F A J K

/-!
## Pushforward continu le long de l'identité

Le foncteur identité est continu (`Functor.isContinuous_id`), et pousser en
avant le long de l'identité est l'identité sur les faisceaux.
-/

/-- COMPARAISON (Iso.refl) : pushforward continu le long du foncteur
    identité = identité sur les faisceaux. (Un `def` : un `Iso` est une
    structure data-carrying, non une `Prop`.) -/
def sheafPushforwardContinuous_id
    {C : Type*} [Category C] {A : Type*} [Category A]
    (J : GrothendieckTopology C) :
    Functor.sheafPushforwardContinuous (𝟭 C) A J J ≅ 𝟭 (Sheaf J A) :=
  Functor.sheafPushforwardContinuousId A J

/-!
## Les pushforwards continus composent

Si `F : C ⥤ D` et `G : D ⥤ E` sont continus, pousser en avant le long de `G`
puis le long de `F` égale pousser en avant le long de `F ⋙ G` — la
contravariance en les foncteurs, miroir de `pullback_pullback`
(`SieveLattice.lean`) niveau cribles. La continuité du composé est fournie
par `Functor.isContinuous_comp`.
-/

/-- COMPARAISON (Iso.refl) : les pushforwards continus composent —
    contravariance en les foncteurs, miroir faisceau de `pullback_pullback`.
    (Un `def` : un `Iso` est une structure data-carrying, non une `Prop` ;
    l'instance de continuité du composé est dérivée par `letI`, comme dans
    `Functor.sheafPushforwardContinuousComp`.) -/
def sheafPushforwardContinuous_comp
    {C D E : Type*} [Category C] [Category D] [Category E]
    {A : Type*} [Category A] (F : C ⥤ D) (G : D ⥤ E)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (L : GrothendieckTopology E)
    [Functor.IsContinuous F J K] [Functor.IsContinuous G K L] :
    letI := Functor.isContinuous_comp F G J K L
    G.sheafPushforwardContinuous A K L ⋙ F.sheafPushforwardContinuous A J K ≅
      (F ⋙ G).sheafPushforwardContinuous A J L :=
  Functor.sheafPushforwardContinuousComp F G A J K L

/-!
## Le lemme de comparaison : l'adjonction passe aux faisceaux

Si `F ⊣ G` est une adjonction entre foncteurs tous deux continus, les
pushforwards continus induits sur les catégories de faisceaux sont eux-mêmes
adjoints. C'est le **lemme de comparaison** de SGA 4 (exposé III, 1.6) sous
sa forme opérationnelle : toute adjonction de préfaisceaux compatible aux
topologies descend aux faisceaux **sans sheafification explicite** — les
unités et co-unités sont héritées composante par composante de l'adjonction
opposée `(adj.op.whiskerLeft _)`.

C'est la généralisation sites-arbitraires de l'adjonction
`pullbackPushforwardAdjunction` (`DirectImage.lean`, niveau schémas) : ici
aucune géométrie n'est requise, seulement la continuité.
-/

/-- COMPARAISON (SGA 4 III.1.6) : si `F ⊣ G` avec `F` et `G` continus, les
    pushforwards continus sur les catégories de faisceaux sont adjoints —
    le lemme de comparaison, forme opérationnelle. (Un `def`, pas un
    `theorem` : une `Adjunction` est une structure data-carrying, non une
    `Prop` — miroir exact de `Adjunction.sheafPushforwardContinuous`.) -/
def adjunction_sheafPushforwardContinuous
    {C D : Type*} [Category C] [Category D] {A : Type*} [Category A]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [Functor.IsContinuous F J K] [Functor.IsContinuous G K J] :
    F.sheafPushforwardContinuous A J K ⊣ G.sheafPushforwardContinuous A K J :=
  Adjunction.sheafPushforwardContinuous (E := A) adj J K

end Grothendieck
