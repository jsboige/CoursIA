/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grothendieck.GodementMono

/-!
# La suite des unités itérées `F → C⁰F → C⁰²F → ⋯` — et pourquoi ce n'est pas
la résolution canonique

Suite de la Partie 86 et fil prochain du lac [God58, Chap. II §4.1]. La Partie 86
a fermé le prérequis nommé par la Partie 85 : `C⁰` préserve les monomorphismes
(`godementFunctor_preservesMonomorphisms`). Avec la flasquité de `C⁰F`
(`isFlasque_godementPresheaf`, P84) et l'injectivité de `F → C⁰F` sur les
faisceaux (`injective_toGodement_of_isSheaf`, P84), ce module pose la **suite
des unités itérées** d'un préfaisceau `F` de groupes abéliens sur `X` :

```
  F --μ--> C⁰F --μ(C⁰F)--> C⁰²F --μ(C⁰²F)--> C⁰³F → ⋯
```

où chaque flèche est l'unité `toGodement` évaluée au préfaisceau source : la
seconde flèche, `godementUnitIter`, est exactement `toGodement (F := C⁰F)`,
l'unité réappliquée.

## Ce que cette suite n'est pas

Cette suite de morphismes n'est **pas** un complexe, donc pas la résolution
canonique de Godement. Le théorème `godementUnit_comp_injective` ci-dessous le
montre : sur un faisceau `F`, le composé `μ ≫ μ(C⁰F)` est **injectif** sur
chaque ouvert — composé de l'unité (injective sur les faisceaux, P84) et de
l'unité réappliquée (injective sans hypothèse, car `C⁰F` est toujours un
faisceau, P84). Sur une section non nulle, le composé reste non nul (témoin
élémentaire : un point, le faisceau constant `ℤ`, la section `1`). L'égalité
`μ ≫ d⁰ = 0` qu'exigerait une différentielle n'est donc pas un énoncé ouvert
ni une preuve reportée : elle est **fausse** pour ce morphisme.

La construction canonique de [God58, Chap. II §4.1] passe à chaque étape par
le **conoyau de l'unité** et son plongement dans le terme de Godement suivant ;
réappliquer l'unité sans ce conoyau ne la remplace pas. Construire la vraie
différentielle de la résolution canonique (via `coker μ`) est la **frontière
nommée** traitée en Partie 89.

## Ce que ce module pose, honnêtement

1. `godementUnitIter` : la seconde flèche `C⁰F ⟶ C⁰²F`, définie comme
   `toGodement (F := C⁰F)` — l'unité réappliquée, désignée pour ce qu'elle
   est. (L'alias `godementDZero` des premières versions de cette PR, qui la
   nommait « différentielle degré 0 », est retiré : le nom était mathématique-
   ment infidèle, et aucune preuve ne dépendait de lui.)
2. `godementUnit_comp_injective` : le **témoin** décrit ci-dessus — le composé
   `μ ≫ μ(C⁰F)` est injectif sur les faisceaux, donc la suite des unités
   n'admet pas la null-composition d'un complexe.
3. `godementUnit_injective_of_isSheaf` : l'injectivité de `μ` sur les faisceaux
   (`injective_toGodement_of_isSheaf`, P84, rejoué) — l'exactitude de
   `0 → F → C⁰F` **en F**, seul fait d'exactitude posé à ce stade.

## Références

  - R. Godement, *Topologie algébrique et théorie des faisceaux* [God58],
    Chap. II §4.1. La résolution canonique `0 → F → C⁰F → C¹F → ⋯`, dont chaque
    pas passe par le conoyau de l'unité.
  - R. Godement, *Topologie algébrique et théorie des faisceaux* [God58],
    Chap. II §5. Acyclicité `H^n(C⁰F) = 0` pour `n ≥ 1`, frontière de la Partie
    89.
-/

universe u

open CategoryTheory Category Limits TopCat TopologicalSpace Opposite

namespace Grothendieck

variable {X : TopCat.{u}}

/-- L'**unité de Godement itérée une fois** : le morphisme canonique
`C⁰F ⟶ C⁰(C⁰F)`, défini comme l'image de `C⁰F` par la transformation naturelle
`toGodement` (l'unité `F → C⁰F` du foncteur `C⁰`, réappliquée au préfaisceau
`C⁰F`). Ce morphisme est le second maillon de la **suite des unités itérées**
`F → C⁰F → C⁰²F → ⋯`. Il n'est **pas** une différentielle de résolution :
le théorème `godementUnit_comp_injective` montre que le composer avec l'unité
ne peut pas donner zéro sur un faisceau. -/
noncomputable def godementUnitIter (F : X.Presheaf AddCommGrpCat.{u}) :
    godementPresheaf F ⟶ godementPresheaf (godementPresheaf F) :=
  toGodement (F := godementPresheaf F)

/-- **Témoin : la suite des unités itérées n'est pas un complexe.** Pour un
faisceau `F` et tout ouvert `U`, le composé `toGodement F ≫ godementUnitIter F`
est **injectif** : c'est le composé de deux morphismes injectifs — l'unité
`toGodement F` (injective sur les faisceaux, `injective_toGodement_of_isSheaf`,
P84) et l'unité réappliquée `godementUnitIter F = toGodement (C⁰F)`
(injective sans hypothèse sur `C⁰F`, car `godementPresheaf F` est toujours un
faisceau, `isSheaf_godementPresheaf`, P84). Une section non nulle reste donc
non nulle après le composé : l'égalité `μ ≫ d⁰ = 0` qu'exigerait une
différentielle est fausse pour ce morphisme. La vraie différentielle de la
résolution canonique passe par le conoyau de l'unité ([God58] II §4.1) et est
la frontière nommée de la Partie 89. -/
theorem godementUnit_comp_injective (F : X.Presheaf AddCommGrpCat.{u})
    (hF : TopCat.Presheaf.IsSheaf F) (U : Opens X) :
    Function.Injective ((toGodement F ≫ godementUnitIter F).app (op U)) := by
  intro s t hst
  -- les deux injectivités de P84, composées : l'unité en F (faisceau), puis
  -- l'unité réappliquée en C⁰F (injective sans hypothèse, C⁰F toujours faisceau)
  apply injective_toGodement_of_isSheaf F hF U
  apply injective_toGodement_of_isSheaf (godementPresheaf F) (isSheaf_godementPresheaf F) U
  rw [NatTrans.comp_app] at hst
  exact hst

/-- **L'exactitude en F de `0 → F → C⁰F`** : pour tout ouvert `U`, le
morphisme `(toGodement F).app (op U) : F(U) ⟶ C⁰F(U)` est injectif quand `F`
est un faisceau. C'est précisément le contenu de
`injective_toGodement_of_isSheaf` (P84), rejoué sur chaque ouvert. C'est le
seul fait d'exactitude posé à ce stade : l'exactitude au terme `C⁰F` (et
l'acyclicité `H^n(C⁰F) = 0`, `n ≥ 1`) exigent la vraie différentielle de la
résolution canonique — frontière nommée de la Partie 89 (God58 II.5). -/
theorem godementUnit_injective_of_isSheaf (F : X.Presheaf AddCommGrpCat.{u})
    (hF : TopCat.Presheaf.IsSheaf F)
    (U : Opens X) :
    Function.Injective ((toGodement F).app (op U)) :=
  injective_toGodement_of_isSheaf F hF U

end Grothendieck
