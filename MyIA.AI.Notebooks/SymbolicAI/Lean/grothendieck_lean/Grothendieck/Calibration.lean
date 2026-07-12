/-
# Hommage Grothendieck — Partie 5 : Cibles d'étalonnage pour le harnais prouveur

Copyright (c) 2026 CoursIA. Tous droits réservés.
Distribué sous licence Apache 2.0 comme décrit dans le fichier LICENSE.

## Cibles d'étalonnage pour le harnais prouveur

Ce module héberge **4 theorem** de calibration P1-P4 destinés à la
**co-évolution du harnais prouveur** (Epic #1453) — l'instrument de
preuve multi-agent du cluster. Chaque cible est volontairement simple
mais **didactique** : elle exerce une tactique différente du kernel
Lean 4 afin d'élargir progressivement le registre couvert par le
prouveur autonome.

### Note d'accessibilité Epic #1452/#1453

Ce module est **volontairement minimaliste** : 4 theorem de calibration
chacun < 5 lignes de preuve. La substance n'est pas dans la difficulté
mathématique mais dans la **diversité tactique** (4 tactiques différentes
par cible). C'est précisément la calibration cible pour l'Epic #1453 :
exercices gradués pour le harnais prouveur autonome.

Convention i18n (EPIC #4980 ratifiée user 2026-07-04, voir
`code-style.md` §Lean i18n) : ce module substantiel est **FR canonique**,
avec son miroir anglais dans le fichier sibling `Calibration_en.lean`
(modèle sibling pair, voir PR #6154 pour le pilote sur `Utility.lean`).
-/

import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.AlgebraicGeometry.Sites.BigZariski

namespace Grothendieck

open CategoryTheory AlgebraicGeometry

/-!
## P1 : Ordre lattice — trivial ≤ discrete (évaluation fermée)

La topologie triviale (seul ⊤ couvre) est plus grossière que la topologie
discrète (tout crible couvre). Fait de niveau lattice : ⊥ ≤ ⊤.
-/

/-- ÉTALONNAGE (decide/rfl) : la topologie triviale est sous la topologie discrète
    in the lattice of Grothendieck topologies. -/
theorem trivial_le_discrete {C : Type*} [Category C] :
    (GrothendieckTopology.trivial C : GrothendieckTopology C) ≤
    GrothendieckTopology.discrete C := by
  rw [GrothendieckTopology.trivial_eq_bot, GrothendieckTopology.discrete_eq_top]
  exact bot_le

/-!
## P2 : Sieve.pullback de ⊤ vaut ⊤ (preuve directe)

Tirer en arrière le crible maximal le long d'un morphisme quelconque donne
le crible maximal.
-/

/-- ÉTALONNAGE (simp) : pullback du crible sup est le crible sup. -/
theorem pullback_top {C : Type*} [Category C] {X Y : C} (f : Y ⟶ X) :
    (Sieve.pullback f (⊤ : Sieve X)) = (⊤ : Sieve Y) := by
  ext Z g
  simp [Sieve.pullback]

/-!
## P3 : La topologie de Zariski égale la topologie générée par la prétopologie

C'est `Scheme.zariskiTopology_eq`, réénoncé ici comme cible
d'étalonnage que le prouveur doit trouver et appliquer.
-/

/-- ÉTALONNAGE (exact) : la topologie de Zariski égale celle issue de la prétopologie.
    The prover must discover `exact Scheme.zariskiTopology_eq`. -/
theorem zariski_eq_pretopology :
    (Scheme.zariskiTopology : GrothendieckTopology Scheme) =
    Scheme.zariskiPretopology.toGrothendieck :=
  Scheme.zariskiTopology_eq

/-!
## P4 : Tout préfaisceau est un faisceau pour la topologie triviale

Pour la topologie de Grothendieck la plus grossière (seul ⊤ couvre),
tout préfaisceau satisfait automatiquement la condition de faisceau.
En effet, il n'y a qu'un seul crible couvrant par objet, et la condition
de faisceau sur ⊤ est triviale.
-/

/-- ÉTALONNAGE (exact) : tout préfaisceau à valeurs dans `Type` est un faisceau pour la
    trivial (coarsest) Grothendieck topology (= ⊥).
    Uses `Presieve.isSheaf_bot` which works with `⊥`. -/
theorem isSheaf_trivial {C : Type*} [Category C] (P : Cᵒᵖ ⥤ Type*) :
    Presieve.IsSheaf (⊥ : GrothendieckTopology C) P :=
  Presieve.isSheaf_bot

end Grothendieck
