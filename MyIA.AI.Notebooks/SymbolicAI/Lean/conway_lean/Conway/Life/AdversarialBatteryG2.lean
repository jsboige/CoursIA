/-
Copyright (c) 2026 CoursIA. Tous droits réservés.
Distribué sous licence Apache 2.0 comme décrit dans le fichier LICENSE.

## Carte de décidabilité du gate G2 (centralCorrect) sur le bestiaire

Module cribleur compagnon de `Conway.Life.AdversarialBattery` (le bestiaire de
témoins MacroCell publics, #9589) et de `Conway.Life.HashlifeCorrectness`
(l'infrastructure G2 `centralCorrect` / `centralCorrect_mem`, c.153). Il
**cartographie firsthand, par `decide`, quelles parties du gate G2 sont
décidables au kernel** et documente honnêtement la partie qui ne l'est pas.

### Motivation — la structure du gate G2

La porte G2 (`centralCorrect_mem`, HashlifeCorrectness L2410) caractérise
l'appartenance ponctuelle du résultat hashlife **sans réduire `hashlifeResultAux`**
(c'est le bypass du whnf-wall par congruence, c.153) :

  `p ∈ (hashlifeResultAux (j+2) c).toGrid (2^j, 2^j) ↔
     isAlive (evolve (2^j) (c.toGrid (0, 0))) p = true ∧
     (2^j : Int) ≤ p.1 ∧ p.1 < (2^j : Int) + 2^(j+1) ∧
     (2^j : Int) ≤ p.2 ∧ p.2 < (2^j : Int) + 2^(j+1)`

sous l'hypothèse `h : centralCorrect c j`. Le gate se décompose donc en TROIS
ingrédients : (H) l'hypothèse `centralCorrect` elle-même, (A) le côté « vivant »
`isAlive (evolve ...)`, (B) le côté « bornes » `[2^j, 2^j + 2^(j+1))`. La question
décidabilité, jamais tranchée firsthand sur le bestiaire, est : **lequel de ces
trois ingrédients passe au kernel `decide`, et lequel est bloqué ?**

### Verdict firsthand (probe c.937, env WSL v4.31.0-rc1)

| Ingrédient | Décidable ? | Verdict |
|------------|-------------|---------|
| (H) `centralCorrect c j` — l'égalité de grille centrale | **Non** | **INTRINSIC** (whnf-wall) |
| (A) `evolve (2^j) (c.toGrid (0,0))` — évolution de référence | **Oui** | `decide` |
| (B) bornes `[2^j, 2^j + 2^(j+1))` — arithmétique `Int` pure | **Oui** | `decide` |

L'hypothèse (H) est **de la même classe de mur INTRINSIC** que les six théorèmes
`hashlife_*` de `Computation.lean` (sondés dans `DecideProbe.lean`) : prouver
`centralCorrect c 0` exigerait de réduire `hashlifeResultAux 2 c`, dont la
récursion sur le quadtree `MacroCell` ne se termine pas au kernel. La sonde
confirme : `failed to synthesize Decidable (centralCorrect cexBlock1 0)`.

**Conséquence pour l'attaque G2/G3 (#6724)** : on ne peut PAS établir
`centralCorrect c j` sur un témoin du bestiaire par `decide`. Le seul chemin est
de **fournir `h` comme hypothèse** (filée depuis une étape d'induction P4.3) puis
de consommer `centralCorrect_mem` — exactement la stratégie de
`centralCorrect_mem_shift` (L2443) et de l'assemblage P4.4. Les ingrédients (A) et
(B), eux, sont décidables et instanciables sur le bestiaire (sanity-checks
ci-dessous). Ce module **exerce ces deux côtés décidables** pour confirmer que le
gate, une fois l'hypothèse fournie, se décharge intégralement par calcul.

### Contraintes

Kernel-`decide` pur, **zéro axiome natif**, `native_decide` interdit, budget
compile borné (`j ≤ 1`). EPIC #3846 / #6724 / #9568. Sans sorry.
-/

/-
  Convention i18n (EPIC #4980, décision user 2026-07-04) : ce fichier est **FR
  canonique**, avec son miroir anglais dans le fichier sibling
  `AdversarialBatteryG2_en.lean`. Les énoncés de théorèmes, les tactiques Lean,
  les noms de lemmes et les références Mathlib restent en anglais (compat Mathlib
  4) ; seules les docstrings et ce bloc d'en-tête diffèrent entre les deux
  fichiers.
-/

import Conway.Life.AdversarialBattery
import Conway.Life.HashlifeCorrectness

namespace Conway
namespace Life

/-! ## Ingrédient (H) — l'hypothèse `centralCorrect` est INTRINSIC

La sonde confirme firsthand que `centralCorrect c 0` n'est pas kernel-décidable
pour les témoins du bestiaire : l'instance `Decidable` ne se synthétise pas, car
l'égalité de grille centrale traverse `hashlifeResultAux (j+2) c` dont la récursion
MacroCell ne se réduit pas. Code `by decide` tenu en commentaire + verdict, à la
manière de `DecideProbe.lean` (pour reproduire l'erreur verbatim, décommenter).

  `centralCorrect cexEmpty1 0` : PAS kernel-décidable — `hashlifeResultAux` ne se
  réduit pas (whnf-wall, classe INTRINSIC). Verdict sonde c.937 :
  `failed to synthesize Decidable`. Même classe pour `cexBlock1 0`.
-/

-- theorem cexEmpty1_centralCorrect_j0 : centralCorrect cexEmpty1 0 := by decide
-- theorem cexBlock1_centralCorrect_j0 : centralCorrect cexBlock1 0 := by decide

/-! ## Ingrédient (A) — le côté « vivant » `evolve` EST décidable

Le côté évolution de référence de `centralCorrect_mem` se réduit intégralement au
kernel : `evolve (2^j)` sur la grille d'un témoin MacroCell niveau 1 est un calcul
fini sur une grille petite. Le bloc 2×2 étant une nature morte, `evolve 1` le
fixe ; le vide reste vide. Ce sont les sanity-checks réels (honnêtes) du gate.
-/

/-- **Sanité (A)** : le bloc 2×2 est une nature morte — `evolve 1` le laisse
    invariant. C'est le côté « vivant » du gate G2 pour `cexBlock1` à `j = 0`. -/
theorem cexBlock1_evolve1_fixed :
    evolve 1 (cexBlock1.toGrid (0, 0)) = cexBlock1.toGrid (0, 0) := by decide

/-- **Sanité (A)** : le vide est fixe sous `evolve 1` (vacuité préservée). -/
theorem cexEmpty1_evolve1_fixed :
    evolve 1 (cexEmpty1.toGrid (0, 0)) = cexEmpty1.toGrid (0, 0) := by decide

/-- **Sanité (A)** : la cellule (0, 0) reste vivante après un pas d'évolution du
    bloc (le bloc est une nature morte, chaque cellule a 3 voisines et survit en
    B3/S23). Instanciation du conjoint « vivant » de `centralCorrect_mem`. -/
theorem cexBlock1_cell_alive_evolve1 :
    isAlive (evolve 1 (cexBlock1.toGrid (0, 0))) (0, 0) = true := by decide

/-- **Sanité (A)** : dans le témoin vide, (0, 0) est morte après un pas. -/
theorem cexEmpty1_cell_dead_evolve1 :
    isAlive (evolve 1 (cexEmpty1.toGrid (0, 0))) (0, 0) = false := by decide

/-! ## Ingrédient (B) — les bornes de la fenêtre centrale SONT décidables

Le conjoint « bornes » de `centralCorrect_mem` est de l'arithmétique `Int` pure :
la fenêtre centrale de niveau `j` est `[2^j, 2^j + 2^(j+1))` sur chaque axe
(`j = 0` → `[1, 3)`, `j = 1` → `[2, 6)`). Totalement kernel-`decide`. Les théorèmes
ci-dessous classent des coordonnées du bestiaire comme à l'intérieur / à
l'extérieur de la fenêtre, confirmant que la géométrie du gate se décharge par
calcul dès que l'hypothèse (H) est fournie.
-/

/-- **Sanité (B, j = 0)** : la fenêtre centrale `[1, 3)` contient le coin
    intérieur `1` (borne inférieure atteinte). -/
theorem central_window_j0_contains_lower_bound :
    (2^0 : Int) ≤ (1 : Int) ∧ (1 : Int) < (2^0 : Int) + 2^1 := by decide

/-- **Sanité (B, j = 0)** : la fenêtre centrale `[1, 3)` EXCLUT le coin absolu
    `0` (borne inférieure non atteinte — c'est le contre-exemple qui a tué le mur
    NW `p4_nw_overlap_wall` en c.91 : un bloc au coin absolu NW est hors fenêtre). -/
theorem central_window_j0_excludes_nw_abs_corner :
    ¬ ((2^0 : Int) ≤ (0 : Int) ∧ (0 : Int) < (2^0 : Int) + 2^1) := by decide

/-- **Sanité (B, j = 1)** : la fenêtre centrale `[2, 6)` contient le coin
    intérieur `2`. Instanciation au niveau `j = 1` (cellule niveau 2, fenêtre 4×4). -/
theorem central_window_j1_contains_lower_bound :
    (2^1 : Int) ≤ (2 : Int) ∧ (2 : Int) < (2^1 : Int) + 2^2 := by decide

/-! ## Synthèse — le gate G2 se décharge sauf l'hypothèse

Sous hypothèse `h : centralCorrect cexBlock1 0`, l'appartenance d'un point au
résultat hashlife se réduit — via `centralCorrect_mem` — à un conjoint « vivant »
(A) ET « bornes » (B), dont les deux côtés sont décidables au kernel
(ci-dessus). Le mur INTRINSIC est reporté sur (H) : `centralCorrect` elle-même,
qui exige la récursion `hashlifeResultAux`. Stratégie de preuve confirmée pour
l'assemblage P4.4 (#6724) : filer `h` depuis P4.3, puis consommer le gate.
-/

end Life
end Conway
