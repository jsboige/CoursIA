/-
Grothendieck Partie 22 — Suite exacte longue de Mayer-Vietoris en cohomologie des faisceaux

La Partie 21 (MayerVietorisSquare.lean) a introduit les carrés de
Mayer-Vietoris : l'entrée géométrique (un carré pushout de faisceaux) et
le complexe court exact de faisceaux abéliens libres associé.

Ce module fait le pont avec la **suite exacte longue de Mayer-Vietoris**
en cohomologie des faisceaux depuis Mathlib
(`CategoryTheory.Sites.SheafCohomology.MayerVietoris`).

Étant donné un carré de Mayer-Vietoris S pour un site (C, J) et un
faisceau abélien F, il existe une suite exacte longue :

  ... ⟶ H^n(X₄, F) ⟶ H^n(X₂, F) ⊞ H^n(X₃, F) ⟶ H^n(X₁, F) ⟶ H^{n+1}(X₄, F) ⟶ ...

où X₁ = intersection, X₂/X₃ = ouverts du recouvrement, X₄ = espace
recouvert.

Constructions clés récupérées de Mathlib :

  - `toBiprod` : somme des restrictions H^n(X₄) → H^n(X₂) ⊞ H^n(X₃)
  - `fromBiprod` : différence des restrictions H^n(X₂) ⊞ H^n(X₃) → H^n(X₁)
  - `toBiprod_fromBiprod` : la composition est nulle
  - `δ` : homomorphisme de connexion H^{n₀}(X₁) → H^{n₁}(X₄) (n₁ = n₀ + 1)
  - `sequence` : la suite exacte longue complète (ComposableArrows AddCommGrp 5)
  - `sequence_exact` : la suite est exacte
  - `δ_toBiprod` : δ >> toBiprod = 0
  - `fromBiprod_δ` : fromBiprod >> δ = 0

Ceci complète la machinerie de Mayer-Vietoris : de la condition
géométrique de recouvrement (Partie 21) à la conséquence cohomologique
(cette partie).

EPIC #1646, See #2159. Tous les `sorry` éliminés à la création.
-/

import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris

universe w v u

namespace Grothendieck.SheafCohomology.MayerVietoris

open CategoryTheory Category Opposite Limits

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J (Type v)] [HasSheafify J AddCommGrpCat.{v}]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]

/-! ## 1. Applications de restriction en cohomologie

Étant donné un carré de Mayer-Vietoris S et un faisceau abélien F, les
applications entre groupes de cohomologie sont induites par les
applications de restriction dans le carré.

`toBiprod` est la somme des restrictions :
  H^n(X₄, F) ⟶ H^n(X₂, F) ⊞ H^n(X₃, F)
envoyant y sur (f₂₄* y, f₃₄* y).

`fromBiprod` est la différence des restrictions :
  H^n(X₂, F) ⊞ H^n(X₃, F) ⟶ H^n(X₁, F)
envoyant (y₁, y₃) sur f₁₂* y₁ - f₁₃* y₃.
-/

-- Somme des restrictions : H^n(X₄, F) ⟶ H^n(X₂, F) ⊞ H^n(X₃, F).
#check @CategoryTheory.GrothendieckTopology.MayerVietorisSquare.toBiprod

-- Formule explicite pour toBiprod.
#check @CategoryTheory.GrothendieckTopology.MayerVietorisSquare.toBiprod_apply

-- Différence des restrictions : H^n(X₂, F) ⊞ H^n(X₃, F) ⟶ H^n(X₁, F).
#check @CategoryTheory.GrothendieckTopology.MayerVietorisSquare.fromBiprod

/-! ## 2. Composition et la condition de nullité

La composition toBiprod >> fromBiprod est nulle :
  H^n(X₄) ⟶ H^n(X₂) ⊞ H^n(X₃) ⟶ H^n(X₁)
C'est l'ombre cohomologique de la commutativité du carré.
-/

-- toBiprod >> fromBiprod = 0.
#check @CategoryTheory.GrothendieckTopology.MayerVietorisSquare.toBiprod_fromBiprod

-- Formule explicite pour fromBiprod appliqué à un couple.
#check @CategoryTheory.GrothendieckTopology.MayerVietorisSquare.fromBiprod_biprodIsoProd_inv_apply

/-! ## 3. L'homomorphisme de connexion

L'homomorphisme de connexion δ : H^{n₀}(X₁, F) ⟶ H^{n₁}(X₄, F) (où
n₁ = n₀ + 1) est l'application clé de la suite exacte longue. Elle mesure
l'obstruction à relever une classe de cohomologie de l'intersection
vers l'espace recouvert.

Ceci est défini comme `shortComplex_shortExact.extClass.precomp`.
-/

-- L'homomorphisme de connexion δ : H^{n₀}(X₁) ⟶ H^{n₁}(X₄).
#check @CategoryTheory.GrothendieckTopology.MayerVietorisSquare.δ

/-! ## 4. La suite exacte longue

La suite exacte longue de Mayer-Vietoris est encapsulée comme un
`ComposableArrows AddCommGrp 5` :

  H^n(X₄) ⟶ H^n(X₂) ⊞ H^n(X₃) ⟶ H^n(X₁) ⟶ H^{n+1}(X₄) ⟶ H^{n+1}(X₂) ⊞ H^{n+1}(X₃) ⟶ H^{n+1}(X₁)

Ceci est `sequence S F n₀ n₁ h` où `h : n₀ + 1 = n₁`.
-/

-- La suite exacte longue de Mayer-Vietoris (6 termes, ComposableArrows 5).
#check @CategoryTheory.GrothendieckTopology.MayerVietorisSquare.sequence

/-! ## 5. Exactitude

La suite exacte longue est exacte en toute position. Ceci est le théorème
principal du module, prouvé par comparaison avec la suite contravariante
des groupes Ext.
-/

-- La suite de Mayer-Vietoris est exacte.
#check @CategoryTheory.GrothendieckTopology.MayerVietorisSquare.sequence_exact

/-! ## 6. Conditions de bord

L'homomorphisme de connexion satisfait deux conditions de bord :
  - δ >> toBiprod = 0  (δ atterrit dans le noyau de toBiprod)
  - fromBiprod >> δ = 0  (δ factorise par le conoyau de fromBiprod)
-/

-- δ >> toBiprod = 0.
#check @CategoryTheory.GrothendieckTopology.MayerVietorisSquare.δ_toBiprod

-- fromBiprod >> δ = 0.
#check @CategoryTheory.GrothendieckTopology.MayerVietorisSquare.fromBiprod_δ

/-! ## 7. Théorèmes ponts

Théorèmes ponts reliant la suite exacte longue de Mayer-Vietoris
à une vérification concrète.
-/

/-- Théorème pont : la suite de Mayer-Vietoris est exacte. Pour un
    carré de Mayer-Vietoris S et un faisceau abélien F, la suite de
    groupes de cohomologie est exacte en toute position. -/
theorem mv_sequence_exact
    (S : J.MayerVietorisSquare) (F : Sheaf J AddCommGrpCat.{v})
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    (S.sequence F n₀ n₁ h).Exact :=
  S.sequence_exact F n₀ n₁ h

/-- Théorème pont : l'homomorphisme de connexion composé avec la
    somme des restrictions est nul : δ >> toBiprod = 0. -/
theorem mv_delta_toBiprod_eq_zero
    (S : J.MayerVietorisSquare) (F : Sheaf J AddCommGrpCat.{v})
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    S.δ F n₀ n₁ h ≫ S.toBiprod F n₁ = 0 :=
  S.δ_toBiprod F n₀ n₁ h

/-- Théorème pont : la différence des restrictions composée avec
    l'homomorphisme de connexion est nulle : fromBiprod >> δ = 0. -/
theorem mv_fromBiprod_delta_eq_zero
    (S : J.MayerVietorisSquare) (F : Sheaf J AddCommGrpCat.{v})
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    S.fromBiprod F n₀ ≫ S.δ F n₀ n₁ h = 0 :=
  S.fromBiprod_δ F n₀ n₁ h

/-!
## Bridges propres (c.1301+131)

Les définitions et théorèmes ci-dessous *re-exportent* les fields de la
structure `J.MayerVietorisSquare` exposés dans
`Mathlib/CategoryTheory/Sites/SheafCohomology/MayerVietoris.lean`. Tous ces
fields opèrent sur la structure résidente `J.MayerVietorisSquare` non
polymorphe d'univers — donc **L902 ★★ SAFE** (cf c.1301+108-L1 ★★ : les
constructors polymorphes d'univers sont à proscrire, contrairement aux
fields résidents sur X).

1. `mv_toBiprod_field` : restatement de `S.toBiprod F n` (déf, somme des
   restrictions H^n(X₄) → H^n(X₂) ⊞ H^n(X₃)).
2. `mv_fromBiprod_field` : restatement de `S.fromBiprod F n` (déf,
   différence des restrictions H^n(X₂) ⊞ H^n(X₃) → H^n(X₁)).
3. `mv_delta_field` : restatement de `S.δ F n₀ n₁ h` (déf, homomorphisme de
   connexion H^{n₀}(X₁) → H^{n₁}(X₄)).
4. `mv_sequence_field` : restatement de `S.sequence F n₀ n₁ h` (déf, la
   suite exacte longue ComposableArrows AddCommGrpCat.{w} 5).
5. `mv_toBiprod_fromBiprod_field` : restatement de `S.toBiprod_fromBiprod F
   n` (theorem, composition toBiprod >> fromBiprod = 0 — la condition
   de nullité).

Ce sont des bridges « vitrines » qui certifient que ces fields de la
structure `J.MayerVietorisSquare` sont effectivement calculables dans la
même exécution Lean.
-/

/-- Bridge : la somme des restrictions H^n(X₄) → H^n(X₂) ⊞ H^n(X₃).
    β-équivalent au field `S.toBiprod F n`. -/
noncomputable def mv_toBiprod_field
    (S : J.MayerVietorisSquare) (F : Sheaf J AddCommGrpCat.{v})
    (n : ℕ) :
    F.H' n S.X₄ ⟶ F.H' n S.X₂ ⊞ F.H' n S.X₃ :=
  S.toBiprod F n

/-- Bridge : la différence des restrictions H^n(X₂) ⊞ H^n(X₃) → H^n(X₁).
    β-équivalent au field `S.fromBiprod F n`. -/
noncomputable def mv_fromBiprod_field
    (S : J.MayerVietorisSquare) (F : Sheaf J AddCommGrpCat.{v})
    (n : ℕ) :
    F.H' n S.X₂ ⊞ F.H' n S.X₃ ⟶ F.H' n S.X₁ :=
  S.fromBiprod F n

/-- Bridge : l'homomorphisme de connexion H^{n₀}(X₁) → H^{n₁}(X₄).
    β-équivalent au field `S.δ F n₀ n₁ h`. -/
noncomputable def mv_delta_field
    (S : J.MayerVietorisSquare) (F : Sheaf J AddCommGrpCat.{v})
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    F.H' n₀ S.X₁ ⟶ F.H' n₁ S.X₄ :=
  S.δ F n₀ n₁ h

/-- Bridge : la suite exacte longue de Mayer-Vietoris (ComposableArrows
    AddCommGrpCat.{w} 5). β-équivalent à `S.sequence F n₀ n₁ h`. -/
noncomputable def mv_sequence_field
    (S : J.MayerVietorisSquare) (F : Sheaf J AddCommGrpCat.{v})
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    ComposableArrows AddCommGrpCat.{w} 5 :=
  S.sequence F n₀ n₁ h

/-- Bridge : la composition toBiprod >> fromBiprod est nulle.
    β-équivalent au lemma `S.toBiprod_fromBiprod F n`. -/
theorem mv_toBiprod_fromBiprod_field
    (S : J.MayerVietorisSquare) (F : Sheaf J AddCommGrpCat.{v})
    (n : ℕ) :
    S.toBiprod F n ≫ S.fromBiprod F n = 0 :=
  S.toBiprod_fromBiprod F n

/-! ## 8. Correspondance Stacks (groupe #12 de #28537, relevé du 26/11)

Comparaison **énoncé par énoncé** avec le référentiel `AxiomMath/Stacks`
(`StacksFrontier/Topology/Sheaves/Cohomology/MayerVietoris/`). Références
données par `fichier:ligne` du dépôt Stacks.

**Point de méthode.** Stacks et ce module **partagent la même base Mathlib**
(`Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris`) : Stacks
attache la **tag 01EB** à la suite exacte longue de Mathlib
(`LongExactSequence.lean:141-142`) et y ajoute deux résultats que ce module
n'a pas (le zéro de tête et la naturalité de la connexion).

| Énoncé | Classe | Référent Stacks | Ce que notre version ajoute / ce qui diverge |
|---|---|---|---|
| `mv_sequence_exact` | couvert | `MayerVietoris/LongExactSequence.lean:141-142` — `add_to_stacks 01EB "successive windows"` | C'est le **même** énoncé Mathlib : Stacks y attache la tag 01EB. Ce que notre version ajoute : le pont nommé, la suite longue explicitée en six termes, et le jumeau EN. |
| `mv_delta_toBiprod_eq_zero` | couvert | `MayerVietoris/ColimitDescent.lean:462` (`w₂`, via `δ_toBiprod`) | Stacks utilise le **même** champ `S.δ_toBiprod` pour établir l'exactitude de la suite après colimite. Notre version le nomme et le déclare. |
| `mv_fromBiprod_delta_eq_zero` | couvert | `MayerVietoris/ColimitDescent.lean:461` (`w₁`, via `fromBiprod_δ`) | idem, même champ `S.fromBiprod_δ`. |
| `mv_toBiprod_field` | couvert | `MayerVietoris/LongExactSequence.lean:101,109` et `ColimitDescent.lean:205-206` (`mono_toBiprod_zero`) | Stacks manipule littéralement `S.toBiprod F n`, et en tire l'injectivité de l'application de tête (`Mono (S.toBiprod F 0)`). Notre version ajoute le pont. |
| `mv_fromBiprod_field` | couvert | `MayerVietoris/ColimitDescent.lean:330-334` (`fromBiprodNat`) | Stacks manipule littéralement `S.fromBiprod F n`, et sa naturalité dans le carré. Notre version ajoute le pont. |
| `mv_delta_field` | couvert | `MayerVietoris/LongExactSequence.lean:131-132` | Stacks utilise littéralement `S.δ F n₀ n₁ h`. Notre version ajoute le pont. |
| `mv_sequence_field` | couvert | `MayerVietoris/LongExactSequence.lean:82,110` (`S.sequence F 0 1 rfl`) | idem pour la suite longue elle-même. |
| `mv_toBiprod_fromBiprod_field` | couvert | `MayerVietoris/ColimitDescent.lean:460` (`w₀`, via `toBiprod_fromBiprod`) | Même champ Mathlib ; Stacks s'en sert pour l'exactitude après colimite. |

**Ce que Stacks établit et que ce module n'établit pas** — deux écarts
enregistrés, à ne pas confondre avec les renvois ci-dessus :

- le **zéro de tête** : Stacks montre que `H⁰(X₄,F) ⟶ H⁰(X₂,F) ⊞ H⁰(X₃,F)`
  est injectif (`ColimitDescent.lean:205-206`, `mono_toBiprod_zero`), donc que
  la fenêtre de six termes commence par un zéro
  (`LongExactSequence.lean:81-87`, `mayerVietorisInitialSequence` et
  `mayerVietorisInitialSequence_exact`) ; ce module ne porte que les fenêtres
  successives (tag 01EB), sans le zéro de tête ;
- la **naturalité de la connexion en `F`** : Stacks l'établit
  (`LongExactSequence.lean:129-132`, `mayerVietoris_delta_naturality`) ; ce
  module ne l'énonce pas.

-/

end Grothendieck.SheafCohomology.MayerVietoris
