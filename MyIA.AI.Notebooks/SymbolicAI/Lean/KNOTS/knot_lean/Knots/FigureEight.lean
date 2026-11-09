/-
  Knots.FigureEight — Invariants du nœud en huit sur son code PD plan
  ====================================================================

  Ce module prouve, sur le code PD plan `figureEightPlanarDiagram` (KnotAtlas,
  défini dans `Knots.Jones`) :

  1. **Alexander signé classique à une unité près** : avec le vecteur de
     signes lu par `crossingSign` (deux croisements négatifs puis deux
     positifs, de writhe nul), le mineur désigné de la matrice d'Alexander
     signée vaut exactement `-t * (t^2 - 3*t + 1)` — le polynôme classique
     de 4_1 à l'unité `-t` près (`alexander_figureEightPlanar_classical`
     exhibe l'unité). Le vecteur de signes opposé (miroir) rend
     `-(t^2 - 3*t + 1)`, même classe d'unités, comme l'exige
     l'amphichiralité.
  2. **Déterminant 5** : `det(4_1) = |Δ(-1)| = 5`, sur la valeur signée
     (`alexander_figureEightPlanar_eval_neg_one`) comme sur la version non
     signée (`alexander_figureEightPlanar_unsigned_eval_neg_one`).
  3. **Non-tricoloriabilité** : `¬ IsTricolorable figureEightPlanarDiagram`
     (énumération finie, `decide` noyau) — le déterminant 5, non divisible
     par 3, exclut la 3-coloriabilité de Fox.
  4. **Compte de croisements du diagramme : 4** — sous la définition
     PROVISOIRE Phase 3 de `Knot.crossingNumber` (cf limitation ci-dessous).

  ## Pourquoi un module dédié au code plan

  Depuis la canonicalisation de #17595 (PR #18272), le canonique
  `figureEightDiagram` de `Knots.Basic` porte lui-même le code planaire de
  KnotAtlas : `figureEightDiagram` et `figureEightPlanarDiagram` désignent
  désormais le même diagramme plan. Les valeurs classiques du nœud en huit
  se lisent sur ce code plan, déjà utilisé par
  `bracket_figureEightPlanarDiagram` et `jones_figureEightPlanarDiagram`.
  Ce module referme la trilogie bracket / Jones / Alexander sur le même
  représentant plan, et y ajoute la tricoloriabilité.

  ## Limitations (honnêteté de portée)

  - **Pas d'invariance de Reidemeister** : comme documenté dans
    `Knots.Conway`, `alexanderPolynomialSigned` est une fonction du
    diagramme désigné ; l'invariance par les mouvements de Reidemeister
    n'est PAS prouvée dans ce lac. Les théorèmes ci-dessous sont des calculs
    sur le représentant désigné, dont les valeurs coïncident avec les
    valeurs classiques du nœud 4_1.
  - **PAS de claim de nombre de croisements minimal topologique** :
    `figureEightPlanar_crossingNumber_provisional` porte la définition
    PROVISOIRE Phase 3 de `Knot.crossingNumber` (compte des croisements du
    diagramme désigné, borne SUPÉRIEURE sur le minimum topologique, cf la
    docstring de `Knot.crossingNumber` dans `Knots.Basic`). Il n'établit PAS
    que le minimum topologique du nœud en huit vaut 4 — cela requerrait la
    classification des nœuds à ≤ 3 croisements, hors de portée du lac.

  Subgrain DEEP de l'EPIC #2874, lane myia-po-2025:CoursIA. Convention i18n
  #4980 : jumeau EN dans `FigureEight_en.lean` (code identique, docstrings
  EN).
-/

import Knots.Conway
import Knots.Jones

import Mathlib.Algebra.Polynomial.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace Knots

/-! ## 1. Signes des croisements du code plan

`crossingSign` (défini dans `Knots.Jones`) lit le signe de chaque croisement
sur l'étiquetage du code PD : positif si le brin du dessus va de `e2` à `e4`
(`e4 = nextEdge n e2`), négatif s'il va de `e4` à `e2`. Sur le code plan, les
quatre croisements se répartissent en deux négatifs puis deux positifs —
writhe nul, déjà établi par `writhe_figureEightPlanarDiagram` dans
`Knots.Jones`, signature attendue d'un diagramme alterné d'un nœud
amphichiral. -/

/-- Les signes lus par `crossingSign` sur le code plan : `[-1, -1, 1, 1]`.
Ce vecteur fonde la liste de Bool parallèle aux croisements de
`alexander_figureEightPlanar_signed` ci-dessous (`false` = négatif). -/
theorem crossingSigns_figureEightPlanarDiagram :
    (figureEightPlanarDiagram.crossings.map
      (crossingSign figureEightPlanarDiagram.numEdges)) = [-1, -1, 1, 1] := by
  decide

/-! ## 2. Polynôme d'Alexander signé : le classique à une unité près -/

/-- **Alexander signé du code plan du nœud en huit.** Avec le vecteur de
signes lu par `crossingSign` (`[-1, -1, 1, 1]`, théorème précédent — le
signe du premier croisement est inutilisé, sa ligne est éliminée par le
mineur désigné), le mineur rend exactement
`-t * (t^2 - 3*t + 1)` — le polynôme classique `Δ(t) = t² − 3t + 1` de 4_1 à
l'unité `−t` près. -/
theorem alexander_figureEightPlanar_signed :
    alexanderPolynomialSigned figureEightPlanarDiagram [false, false, true, true]
      = -(Polynomial.X) * (Polynomial.X ^ 2 - 3 * Polynomial.X + 1) := by
  simp only [alexanderPolynomialSigned, figureEightPlanarDiagram]
  simp (config := { decide := true })
  rw [det_three_aux]
  simp only [Matrix.of_apply]
  simp (config := { decide := true }) [alexanderEntrySigned, alexanderEntry, alexanderEntryNeg]
  ring

/-- **Le classique à une unité près, sous forme existentielle** : le polynôme
d'Alexander d'un nœud n'est défini qu'à une unité `±t^k` près (Alexander
1928) ; la valeur désignée ci-dessus est `ε · t^k · (t² − 3t + 1)` pour
`k = 1`, `ε = −1`, exhibés ici. -/
theorem alexander_figureEightPlanar_classical :
    ∃ (k : ℕ) (ε : ℤ), ε * ε = 1 ∧
      alexanderPolynomialSigned figureEightPlanarDiagram [false, false, true, true]
        = Polynomial.C ε * Polynomial.X ^ k * (Polynomial.X ^ 2 - 3 * Polynomial.X + 1) := by
  refine ⟨1, -1, by norm_num, ?_⟩
  rw [alexander_figureEightPlanar_signed]
  have hC : (Polynomial.C (-1 : ℤ) : Polynomial ℤ) = -1 := by simp
  rw [hC]
  ring

/-- Le vecteur de signes opposé (le diagramme miroir) rend
`-(t^2 - 3*t + 1)` — même classe d'unités que le vecteur de `crossingSign`,
comme l'exige l'amphichiralité du nœud en huit (les deux diagrammes miroirs
représentent le même nœud). Cf `alexander_figureEight_signed_mirror` dans
`Knots.Conway` pour le même fait sur le code DT. -/
theorem alexander_figureEightPlanar_signed_mirror :
    alexanderPolynomialSigned figureEightPlanarDiagram [true, true, false, false]
      = -(Polynomial.X ^ 2 - 3 * Polynomial.X + 1) := by
  simp only [alexanderPolynomialSigned, figureEightPlanarDiagram]
  simp (config := { decide := true })
  rw [det_three_aux]
  simp only [Matrix.of_apply]
  simp (config := { decide := true }) [alexanderEntrySigned, alexanderEntry, alexanderEntryNeg]
  ring

/-! ## 3. Déterminant 5 -/

/-- **Déterminant du nœud en huit : 5.** Pour un nœud, `det = |Δ(−1)|` ;
la valeur signée du code plan rend exactement `5` en `t = −1` (l'unité `−t`
de la normalisation désignée n'affecte pas cette lecture :
`|−(−1) · 5| = 5`). -/
theorem alexander_figureEightPlanar_eval_neg_one :
    (alexanderPolynomialSigned figureEightPlanarDiagram [false, false, true, true]).eval (-1)
      = 5 := by
  rw [alexander_figureEightPlanar_signed]
  simp only [Polynomial.eval_mul, Polynomial.eval_neg, Polynomial.eval_sub,
    Polynomial.eval_add, Polynomial.eval_one,
    Polynomial.eval_X, Polynomial.eval_X_pow]
  norm_num

/-- **Contrôle croisé : la version non signée sur le code plan** rend
`t^3 - 2*t^2 + 2*t` — même pathologie de chiralité que sur le code DT
(`alexander_figureEight` dans `Knots.Conway`) : le code PD ne code pas les
signes, la matrice non signée traite les croisements négatifs comme
positifs. La forme classique n'est restituée que par la variante signée ; le
déterminant, lui, survit (théorème suivant). -/
theorem alexander_figureEightPlanar_unsigned :
    alexanderPolynomialAux figureEightPlanarDiagram
      = Polynomial.X ^ 3 - 2 * Polynomial.X ^ 2 + 2 * Polynomial.X := by
  simp only [alexanderPolynomialAux, figureEightPlanarDiagram]
  simp (config := { decide := true })
  rw [det_three_aux]
  simp only [Matrix.of_apply]
  simp (config := { decide := true }) [alexanderEntry]
  ring

/-- **Le déterminant survit à la version non signée** : la valeur non signée
en `t = −1` vaut `−5`, donc `|P(−1)| = 5 = det(4_1)` — la perte de la forme
du polynôme (croisements négatifs traités comme positifs) ne détruit pas la
valeur en `−1`, fait déjà établi sur le code DT
(`alexander_figureEight_eval_neg_one` dans `Knots.Conway`). -/
theorem alexander_figureEightPlanar_unsigned_eval_neg_one :
    (alexanderPolynomialAux figureEightPlanarDiagram).eval (-1) = -5 := by
  rw [alexander_figureEightPlanar_unsigned]
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_X_pow]
  norm_num

/-! ## 4. Non-tricoloriabilité

Le déterminant 5 n'est pas divisible par 3 : la 3-coloriabilité de Fox est
exclue (pour un nœud tricoloriable, det est divisible par 3). Preuve par
énumération finie (`decide` noyau) sur l'espace des coloriages
`Fin 8 → TriColor` (3^8 = 6561), comme le jumeau non plan
`figureEight_not_tricolorable` dans `Knots.Invariant` ; la limite de
profondeur de récursion est levée au niveau de la commande, pour les mêmes
raisons documentées là-bas. -/

set_option maxRecDepth 100000 in
/-- **Le code plan du nœud en huit n'est pas tricolorable** (Fox 1962). -/
theorem figureEightPlanarDiagram_not_tricolorable :
    ¬ IsTricolorable figureEightPlanarDiagram := by
  decide

/-! ## 5. Compte de croisements du diagramme (définition PROVISOIRE) -/

/-- Le code plan porte exactement 4 croisements (compte du diagramme
désigné). -/
theorem figureEightPlanarDiagram_numCrossings :
    figureEightPlanarDiagram.numCrossings = 4 := by
  decide

/-- Nœud en huit porté par le code plan de KnotAtlas. -/
def figureEightPlanar : Knot where
  diagram := figureEightPlanarDiagram

/-- Le nœud `figureEightPlanar` est bien formé (déjà établi sur le
diagramme par `figureEightPlanarDiagram_wf` dans `Knots.Jones`). -/
theorem figureEightPlanar_wf : figureEightPlanar.diagram.wf = true :=
  figureEightPlanarDiagram_wf

/-- **Nombre de croisements sous la définition PROVISOIRE Phase 3.**

LIMITATION — ce théorème ne prouve PAS que le minimum topologique du nœud
en huit vaut 4. `Knot.crossingNumber` (défini dans `Knots.Basic`) est la
définition PROVISOIRE de la Phase 3 : le compte des croisements du diagramme
désigné, qui est une borne SUPÉRIEURE sur le vrai minimum topologique.
Établir que le minimum vaut exactement 4 requerrait de montrer qu'aucun
diagramme équivalent à ≤ 3 croisements n'existe — la classification des
nœuds à ≤ 3 croisements, hors de portée de ce lac. Le théorème établit
seulement que le diagramme désigné de `figureEightPlanar` compte 4
croisements, valeur qui coïncide avec le minimum classique attendu de 4_1
sans que cette coïncidence soit prouvée ici. -/
theorem figureEightPlanar_crossingNumber_provisional :
    Knot.crossingNumber figureEightPlanar = 4 := by
  show figureEightPlanar.crossingNumberOfDiagram = 4
  unfold Knot.crossingNumberOfDiagram Knot.diagram figureEightPlanar figureEightPlanarDiagram
  decide

end Knots
