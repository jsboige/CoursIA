/-
  Core d'approbation — définition et lemmes d'identité
  ====================================================

  Tranche 2 du plan d'exécution de l'issue #17988, au-dessus du socle de
  Tranche 1 (`ApprovalDefs.lean`). Résultat de référence : Becker, Greger et
  Peters (2026), arXiv 2609.11912.

  La définition retenue est la définition **standard** du core en élection de
  comité : un comité est dans le core si aucune coalition **non vide** de
  votants ne peut strictement améliorer le sort de **tous** ses membres par un
  autre comité de même taille.

  Deux points de la définition méritent d'être lus, parce qu'ils sont les
  corrections apportées au croquis initial du cadrage (revue NanoClaw cid
  5327843625, cf. `docs/lean/approval-core-bgp2026-design.md` §7bis) :

  1. **Coalition non vide.** Sans la contrainte `T.Nonempty`, le core serait
     vide dès qu'il existe deux comités distincts : la coalition vide
     « améliore » alors vacuement. Le lemme `empty_coalition_strictlyImproves`
     ci-dessous donne ce contre-exemple, et il est le témoin que la contrainte
     n'est pas décorative.
  2. **Aucun paiement dans la condition de blocage.** La structure
     `PaymentFunction` de Tranche 1 est une composante de l'**objectif** de la
     preuve (`HarmonicEntropy`, Tranche 3), pas de la **définition** du core.
     Ici, « améliorer » se lit directement sur `Happiness`.

  Le théorème principal (le core est non vide) et sa preuve constructive vivent
  dans `ApprovalBGP2026.lean` (Tranche 3). Ce fichier ne pose que la définition
  et les lemmes d'identité — **aucun `sorry`**.

  Choix d'imports : la preuve ne requiert ni import de tactique Mathlib ni
  machinerie classique. Les lemmes sont énoncés dans leur direction
  intuitionnistement valide, et la paire
  `not_exists_improving_of_inCore` / `inCore_of_not_exists_improving` rend le
  contenu de l'équivalence sans invoquer `push_neg` ni `by_contra`.

  Convention i18n #4980 : ce fichier porte le namespace `ApprovalCore` (FR).
  Le sibling `ApprovalCore_en.lean` porte le namespace `ApprovalCore_en` (EN).
  Préservation byte-identity hors docstrings — vérifiée par
  `scripts/lean/check_i18n_siblings.py`.
-/

import ApprovalDefs
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Basic

namespace ApprovalCore

open ApprovalDefs

variable {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]

/-- Une coalition `T` **améliore strictement** sur le comité `S` lorsqu'il
    existe un autre comité `S'` de même taille qui rend **chaque** membre de
    `T` strictement plus heureux. -/
def StrictlyImproves (P : ApprovalProfile V A) (S : Committee A P.committeeSize)
    (T : Finset V) : Prop :=
  ∃ S' : Committee A P.committeeSize, S' ≠ S ∧
    ∀ v ∈ T, Happiness P S' v > Happiness P S v

/-- Un comité `S` est dans le **core** lorsqu'aucune coalition **non vide** de
    votants ne peut l'améliorer strictement. -/
def InCore (P : ApprovalProfile V A) (S : Committee A P.committeeSize) : Prop :=
  ∀ T : Finset V, T.Nonempty → ¬ StrictlyImproves P S T

/-- Identité, sens direct : un comité dans le core exclut toute coalition
    améliorante. -/
lemma not_exists_improving_of_inCore (P : ApprovalProfile V A)
    (S : Committee A P.committeeSize) (h : InCore P S) :
    ¬ ∃ T : Finset V, T.Nonempty ∧ StrictlyImproves P S T := by
  rintro ⟨T, hT, hs⟩
  exact h T hT hs

/-- Identité, sens réciproque : l'absence de coalition améliorante est
    exactement l'appartenance au core. Avec le lemme précédent, les deux
    lectures de la définition sont couvertes sans invoquer de logique
    classique. -/
lemma inCore_of_not_exists_improving (P : ApprovalProfile V A)
    (S : Committee A P.committeeSize)
    (h : ¬ ∃ T : Finset V, T.Nonempty ∧ StrictlyImproves P S T) : InCore P S := by
  intro T hT hs
  exact h ⟨T, hT, hs⟩

/-- Une coalition améliorante reste améliorante sur toute sous-coalition :
    l'amélioration stricte étant requise pour **tous** les membres, retirer des
    membres ne peut que faciliter la condition. C'est la monotonie qui rend le
    core une propriété portant sur des coalitions, pas sur des votants isolés. -/
lemma strictlyImproves_subset (P : ApprovalProfile V A)
    (S : Committee A P.committeeSize) {T T' : Finset V} (hsub : T ⊆ T')
    (h : StrictlyImproves P S T') : StrictlyImproves P S T := by
  obtain ⟨S', hne, himp⟩ := h
  exact ⟨S', hne, fun v hv => himp v (hsub hv)⟩

/-- La coalition **vide** « améliore strictement » dès qu'il existe un comité
    distinct de `S`. C'est le témoin de la correction 1 du cadrage : sans la
    contrainte `T.Nonempty` dans `InCore`, cette coalition suffirait à vider le
    core de tout comité dès que l'espace des comités a au moins deux éléments. -/
lemma empty_coalition_strictlyImproves (P : ApprovalProfile V A)
    (S : Committee A P.committeeSize) (S' : Committee A P.committeeSize)
    (hne : S' ≠ S) : StrictlyImproves P S ∅ :=
  ⟨S', hne, fun v hv => absurd hv (Finset.notMem_empty v)⟩

/-- Condition suffisante : si aucun comité de même taille ne rend un votant
    strictement plus heureux, le comité est dans le core. L'énoncé est
    volontairement faible — c'est le cas « unanimement maximal », utile comme
    test de non-vacuité de la définition, et non le résultat de Becker, Greger
    et Peters (Tranche 3). -/
lemma inCore_of_no_strict_improvement (P : ApprovalProfile V A)
    (S : Committee A P.committeeSize)
    (h : ∀ (S' : Committee A P.committeeSize) (v : V),
      Happiness P S' v ≤ Happiness P S v) : InCore P S := by
  intro T hT hs
  obtain ⟨S', _hne, himp⟩ := hs
  obtain ⟨v, hv⟩ := hT
  exact absurd (himp v hv) (not_lt.mpr (h S' v))

end ApprovalCore
