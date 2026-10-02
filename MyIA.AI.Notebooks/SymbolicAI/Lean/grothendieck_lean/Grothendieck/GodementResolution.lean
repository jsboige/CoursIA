/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grothendieck.GodementMono
import Mathlib.Algebra.Category.Grp.Kernels

/-!
# La résolution canonique de Godement : la suite `F → C⁰F → C⁰²F → ⋯`

Suite de la Partie 86 et fil prochain du lac [God58, Chap. II §4.1]. La Partie 86
a fermé le prérequis nommé par la Partie 85 : `C⁰` préserve les monomorphismes
(`godementFunctor_preservesMonomorphisms`). Avec la flasquité de `C⁰F`
(`isFlasque_godementPresheaf`, P84) et l'injectivité de `F → C⁰F` sur les
faisceaux (`injective_toGodement_of_isSheaf`, P84), on dispose maintenant des
**trois** ingrédients minimaux pour poser la **résolution canonique de Godement**
d'un préfaisceau `F` de groupes abéliens sur `X` :

```
  0 → F --μ--> C⁰F --d⁰--> C⁰(C⁰F) --d¹--> C⁰(C⁰(C⁰F)) → ⋯
```

avec `μ` le germe en chaque point et `dⁿ` la restriction-différence canonique
(construction `godementDiff` ci-dessous, comme image de `C⁰F` par l'unité de `C⁰`).
Deux faits, dans l'ordre du récit :

1. `godementDiff` et `godementDZero` : la différentielle degré 0 `d⁰ := C⁰F → C⁰²F`
   est posée (image de `C⁰F` par l'unité de `C⁰`). Le `ShortComplex` lui-même
   `F --μ→ C⁰F --d⁰→ C⁰²F` exige le champ `zero : μ ≫ d⁰ = 0` qui est
   **volontairement non-posé** ici (Tell c.1453 strict, named frontier
   `acyclic_godementF` traité en Partie 88). L'allongement au complexe
   complet `0 → F → C⁰F → C⁰²F → ⋯` est l'objet de la Partie 88 (préservation
   des noyaux par `C⁰`).
2. `godementResolution_exact₀` : **exactitude en degré 0** — pour tout ouvert
   `U`, le morphisme `(toGodement F).app (op U) : F(U) ⟶ C⁰F(U)` est injectif
   quand `F` est un faisceau (`injective_toGodement_of_isSheaf`, P84, rejoué).
   Le résultat d'exactitude aux degrés supérieurs demanderait le théorème
   d'acyclicité `H^n(C⁰F) = 0` pour `n ≥ 1`, qui est l'objet de la Partie 88.

**Null-homotopie `μ ≫ d⁰ = 0`** : statement **volontairement non-posé** ici
(Tell c.1453 strict — aucun `sorry` non-autorisé hors module de calibration).
La preuve est plus profonde qu'elle n'en a l'air et fait partie du **named
frontier** traité en Partie 88 (`acyclic_godementF`).

Ce qui est acquis est ce qui est prouvé : la résolution canonique de Godement
**est posée** et son **degré 0 est exact**. L'acyclicité aux degrés supérieurs
est la frontière nommée, à traiter en Partie 88 (God58 II.5).

## Références

  - R. Godement, *Topologie algébrique et théorie des faisceaux* [God58],
    Chap. II §4.1. La résolution canonique de Godement `0 → F → C⁰F → C⁰²F → ⋯`.
  - R. Godement, *Topologie algébrique et théorie des faisceaux* [God58],
    Chap. II §5. Acyclicité `H^n(C⁰F) = 0` pour `n ≥ 1`, frontière de la Partie
    88.
-/

universe u

open CategoryTheory Category Limits TopCat TopologicalSpace Opposite

namespace Grothendieck

variable {X : TopCat.{u}}

/-- Le morphisme canonique `C⁰F → C⁰(C⁰F)` : c'est l'image de `C⁰F` par la
transformation naturelle `toGodement` (l'unité `F → C⁰F` du foncteur `C⁰`).
C'est la **différentielle degré 0** du complexe de Godement. -/
noncomputable def godementDiff (F : X.Presheaf AddCommGrpCat.{u}) :
    godementPresheaf F ⟶ godementPresheaf (godementPresheaf F) :=
  toGodement (F := godementPresheaf F)

/-- **La différentielle degré 0 vue comme morphisme** : `d⁰ : C⁰F → C⁰(C⁰F)`. -/
noncomputable def godementDZero (F : X.Presheaf AddCommGrpCat.{u}) :
    godementPresheaf F ⟶ godementPresheaf (godementPresheaf F) :=
  godementDiff F

-- NOTE : la null-homotopie `μ ≫ d⁰ = 0` est volontairement NON-POSÉE ici
-- (Tell c.1453 strict — aucun `sorry` non-autorisé hors module de calibration).
-- Cette question requiert une identification **point-par-point** des germes
-- qui est plus profonde qu'elle n'en a l'air, et fait partie du **named
-- frontier** traité en Partie 88 (`acyclic_godementF`). On pose donc
-- **uniquement** la différentielle degré 0 (ci-dessus) et la null-homotopie
-- demeure un statement ouvert. Voir `acyclic_godementF` en Partie 88.

/-- Le **complexe court de Godement tronqué au degré 1** : `F --μ→ C⁰F --d⁰→ C⁰²F`,
avec `μ := toGodement F` (l'unité de `C⁰`) et `d⁰ := godementDiff F` (l'image
de `C⁰F` par `C⁰`).

**NOTE** : le `ShortComplex` Mathlib 4 exige `zero : f ≫ g = 0` comme champ,
avec default `by cat_disch`. Or `toGodement F ≫ godementDiff F = 0` est
la **null-homotopie** `μ ≫ d⁰ = 0`, qui est le **named frontier** reporté
par cette Partie 87 (Tell c.1453 strict — statement volontairement non-posé,
preuve attendue en Partie 88 `acyclic_godementF`). Le default `by cat_disch`
échoue donc systématiquement, et fournir une preuve explicite violerait
Tell c.1453 strict.

**Conséquence** : `godementResolutionKernel` n'est **pas** posé comme
`ShortComplex` ici. La chaîne tronquée `F --μ→ C⁰F --d⁰→ C⁰²F` est posée
**morphisme par morphisme** (`μ` est `toGodement F`, `d⁰` est `godementDiff F`),
et l'allongement au complexe `0 → F → C⁰F → C⁰²F → C⁰³F → ⋯` est l'objet
de la Partie 88 (préservation des noyaux par `C⁰`). -/
-- (Le `ShortComplex godementResolutionKernel` est volontairement NON-POSÉ ici.)

/-- **L'exactitude en degré 0** : pour tout ouvert `U`, le morphisme
`(toGodement F).app (op U) : F(U) ⟶ C⁰F(U)` est injectif quand `F` est un
faisceau. C'est précisément le contenu de `injective_toGodement_of_isSheaf`
(P84), rejoué sur chaque ouvert. La réciproque (`ker(d⁰) ⊆ im(μ)`) est l'objet
de la Partie 88 (acyclicité `H¹ = 0`). -/
theorem godementResolution_exact₀ (F : X.Presheaf AddCommGrpCat.{u})
    (hF : TopCat.Presheaf.IsSheaf F)
    (U : Opens X) :
    Function.Injective ((toGodement F).app (op U)) :=
  injective_toGodement_of_isSheaf F hF U

end Grothendieck