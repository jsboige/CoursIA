/-
  Core d'approbation — optimalité de Pareto
  =========================================

  Résultat **intermédiaire** de la Tranche 3 du plan d'exécution de l'issue
  #17988, au-dessus de `ApprovalCore.lean` (Tranche 2). Résultat de référence :
  Becker, Greger et Peters (2026), arXiv 2609.11912.

  Le théorème de **non-vacuité** du core (celui de BGP 2026) reste dans
  `ApprovalBGP2026.lean`. Ce fichier prouve la **condition nécessaire** qui
  l'encadre par le bas, et qui se démontre sans axiome supplémentaire :

      appartenir au core  ⟹  ne pas être dominé au sens de Pareto.

  Le **mécanisme** est le contenu intéressant, et il tient en une ligne : une
  domination de Pareto est toujours **témoignée par une coalition d'un seul
  votant**. Soit `v` le votant dont le sort s'améliore strictement ; la
  coalition `{v}` est non vide, et la condition d'amélioration stricte y est
  satisfaite par construction. Le core étant défini contre **toute** coalition
  non vide, il l'est en particulier contre celle-là.

  Ce que le résultat dit, et ce qu'il ne dit pas. Il dit que le core est
  contenu dans l'ensemble de Pareto — un encadrement, pas une caractérisation,
  et il ne dit **rien** de la non-vacuité : l'énoncé est compatible avec un
  core vide, qui est précisément le cas que la Tranche 3 doit exclure. La
  réciproque est fausse en général (un comité Pareto-optimal peut être bloqué
  par une coalition qui n'améliore pas *tout le monde*), et elle n'est pas
  revendiquée ici.

  Choix d'imports : comme `ApprovalCore.lean`, ce fichier n'importe aucune
  tactique Mathlib et n'invoque ni `push_neg` ni `by_contra`. Les énoncés sont
  dans leur direction intuitionnistement valide.

  Convention i18n #4980 : ce fichier porte le namespace `ApprovalPareto` (FR).
  Le sibling `ApprovalPareto_en.lean` porte le namespace `ApprovalPareto_en`.
  Préservation byte-identity hors docstrings — vérifiée par
  `scripts/lean/check_i18n_siblings.py`.
-/

import ApprovalDefs
import ApprovalCore
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Basic

namespace ApprovalPareto

open ApprovalDefs ApprovalCore

variable {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]

/-- Un comité `S'` **domine au sens de Pareto** le comité `S` lorsque `S'` fait
    au moins aussi bien pour **chaque** votant, et strictement mieux pour au
    moins un. La domination exige les deux : la faiblesse seule (tout le monde
    au moins aussi bien) n'est pas une domination, c'est la simple
    équivalence — c'est ce que vérifie `not_paretoDominates_self`. -/
def ParetoDominates (P : ApprovalProfile V A) (S : Committee A P.committeeSize)
    (S' : Committee A P.committeeSize) : Prop :=
  (∀ v : V, Happiness P S v ≤ Happiness P S' v) ∧
    ∃ v : V, Happiness P S v < Happiness P S' v

/-- Un comité ne se domine pas lui-même : la seconde composante de la
    définition est une inégalité **stricte**, donc irréflexive. C'est le témoin
    que la clause « strictement mieux pour au moins un » n'est pas décorative —
    sans elle, la relation serait réflexive et toute la hiérarchie s'effondrerait
    (chaque comité dominerait tous ceux de bonheur égal). -/
lemma not_paretoDominates_self (P : ApprovalProfile V A)
    (S : Committee A P.committeeSize) : ¬ ParetoDominates P S S := by
  rintro ⟨_hweak, v, hv⟩
  exact absurd hv (lt_irrefl _)

/-- **Le mécanisme de la tranche.** Une domination de Pareto est toujours
    témoignée par une coalition d'**un seul** votant : le votant dont le sort
    s'améliore strictement. La coalition `{v}` est non vide, et l'amélioration
    stricte y est acquise par construction — les autres membres n'existent pas,
    donc la quantification universelle sur `{v}` est le seul point à vérifier.

    C'est ce qui rend le blocage effectif : le core ne se défend pas contre des
    coalitions larges, il se défend déjà contre des coalitions réduites à un
    votant. -/
lemma exists_singleton_strictlyImproves_of_paretoDominates
    (P : ApprovalProfile V A) (S : Committee A P.committeeSize)
    {S' : Committee A P.committeeSize} (h : ParetoDominates P S S') :
    ∃ v : V, StrictlyImproves P S ({v} : Finset V) := by
  obtain ⟨_hweak, v, hv⟩ := h
  have hne : S' ≠ S := fun hEq => by
    rw [hEq] at hv
    exact absurd hv (lt_irrefl _)
  exact ⟨v, S', hne, fun w hw => by
    obtain rfl := Finset.mem_singleton.mp hw
    exact hv⟩

/-- **Résultat principal.** Un comité dans le core n'est dominé au sens de
    Pareto par aucun comité de même taille.

    Encadrement, pas caractérisation : la réciproque est fausse en général (un
    comité Pareto-optimal peut être bloqué par une coalition qui n'améliore pas
    tous ses membres), et l'énoncé est muet sur la non-vacuité du core — il est
    compatible avec un core vide, cas que la Tranche 3 exclut. -/
theorem not_paretoDominated_of_inCore (P : ApprovalProfile V A)
    (S : Committee A P.committeeSize) (h : InCore P S) :
    ¬ ∃ S' : Committee A P.committeeSize, ParetoDominates P S S' := by
  rintro ⟨S', hpd⟩
  obtain ⟨v, hv⟩ := exists_singleton_strictlyImproves_of_paretoDominates P S hpd
  exact h ({v} : Finset V) ⟨v, Finset.mem_singleton.mpr rfl⟩ hv

/-- Forme contraposée, celle qui sert à **exclure** un comité du core : exhiber
    une seule domination de Pareto suffit. C'est la forme utilisable côté
    application — on n'a jamais à parcourir toutes les coalitions pour montrer
    qu'un comité n'est pas dans le core, une domination suffit. -/
theorem not_inCore_of_paretoDominates (P : ApprovalProfile V A)
    (S : Committee A P.committeeSize) {S' : Committee A P.committeeSize}
    (h : ParetoDominates P S S') : ¬ InCore P S :=
  fun hc => not_paretoDominated_of_inCore P S hc ⟨S', h⟩

end ApprovalPareto
