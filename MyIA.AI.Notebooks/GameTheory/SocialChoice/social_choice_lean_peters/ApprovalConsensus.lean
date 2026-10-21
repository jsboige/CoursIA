/-
  Core d'approbation — non-vacuité sur les profils de consensus
  =============================================================

  Résidu de l'issue #17988 pointé par le coordinateur le 2026-10-13 : « la
  preuve minimale du point 3 — caractérisation par systèmes de paiement
  (théorème 3.3 du papier) OU un cas borné explicite — non livrée ».

  Ce fichier livre la seconde branche de cette alternative, et la livre plus
  large qu'un cas : une **famille** de profils sur laquelle le core est
  non vide, démontrée sans `sorry`.

  ## Ce qui est prouvé, et ce qui ne l'est pas

  **Prouvé.** Deux conditions suffisantes, symétriques l'une de l'autre :

  - si chaque votant approuve un sous-ensemble du comité `S`, alors `S` est
    dans le core (`inCore_of_ballots_subset`) : chaque votant atteint le
    cardinal de son ballot, son maximum possible ;
  - si le comité `S` est contenu dans le ballot de chaque votant, alors `S`
    est dans le core (`inCore_of_committee_subset_ballots`) : chaque votant
    touche `k`, et `k` est le maximum atteignable par tout comité de taille
    `k` (`happiness_le_committeeSize`, qui vaut sans hypothèse).

  Dans les deux cas aucune coalition — même non vide — ne peut bloquer. Le
  corollaire `exists_inCore_of_common_approval` en déduit la non-vacuité du
  core pour tout profil de **consensus** (tous les votants partagent le même
  ensemble d'approbation `U`) dès que la taille du comité ne dépasse pas
  celle de `U`.

  **Non prouvé, et nommé comme tel.** Le théorème d'existence de Becker,
  Greger et Peters (2026) vaut pour **tout** profil d'approbation, sans
  hypothèse de consensus ; sa preuve constructive passe par l'optimum local
  d'une entropie harmonique sur l'espace (comité, système de paiement) — la
  Tranche 3, hors de portée de ce cycle. La caractérisation par systèmes de
  paiement (théorème 3.3 du papier) n'est pas non plus formalisée ici. Ce
  fichier ne prétend donc **pas** clore le point 3 : il fournit le cas borné
  explicite que l'issue autorise, élargi à une classe de profils.

  ## Pourquoi le cas n'est pas dégénéré

  La tentation serait de prendre `k = |A|`, où le comité est l'univers entier
  et le résultat tombe sans hypothèse. L'instance concrète ci-dessous prend
  `|A| = 3` et `k = 2` : il existe deux comités distincts, donc une coalition
  pourrait en principe bloquer, et c'est bien la condition d'approbation
  contenue dans le comité qui l'en empêche.

  Aucun `sorry`, aucun `native_decide`.

  Convention i18n #4980 : ce fichier porte le namespace `ApprovalConsensus`
  (FR). Le sibling `ApprovalConsensus_en.lean` porte le namespace
  `ApprovalConsensus_en` (EN). Préservation byte-identity hors docstrings —
  vérifiée par `scripts/lean/check_i18n_siblings.py`.
-/

import ApprovalDefs
import ApprovalCore
import Mathlib.Data.Finset.Card

namespace ApprovalConsensus

open ApprovalDefs ApprovalCore

variable {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]

/-- Le bonheur d'un votant est majoré par le cardinal de son ballot : un
    comité ne peut pas lui accorder plus de candidats qu'il n'en approuve. -/
lemma happiness_le_approved_card (P : ApprovalProfile V A)
    (S : Committee A P.committeeSize) (v : V) :
    Happiness P S v ≤ ((P.ballots v).approved).card :=
  Finset.card_filter_le _ _

/-- Le bonheur d'un votant est aussi majoré par la taille du comité : un
    comité ne peut pas lui accorder plus de candidats qu'il n'en contient.
    Cette borne vaut **sans hypothèse** et c'est elle qui donne le second
    critère de non-vacuité. -/
lemma happiness_le_committeeSize (P : ApprovalProfile V A)
    (S : Committee A P.committeeSize) (v : V) :
    Happiness P S v ≤ P.committeeSize := by
  have hsub : ((P.ballots v).approved.filter (fun x => x ∈ S.val)) ⊆ S.val :=
    fun x hx => (Finset.mem_filter.mp hx).2
  calc Happiness P S v
      = ((P.ballots v).approved.filter (fun x => x ∈ S.val)).card := rfl
    _ ≤ S.val.card := Finset.card_le_card hsub
    _ = P.committeeSize := S.property

/-- Si le comité est contenu dans le ballot d'un votant, son bonheur atteint
    la taille du comité : le votant approuve tous les membres du comité. -/
lemma happiness_eq_committeeSize_of_subset (P : ApprovalProfile V A)
    (S : Committee A P.committeeSize) (v : V)
    (h : S.val ⊆ (P.ballots v).approved) :
    Happiness P S v = P.committeeSize := by
  have hle : Happiness P S v ≤ P.committeeSize := happiness_le_committeeSize P S v
  have hge : P.committeeSize ≤ Happiness P S v := by
    have hsub : S.val ⊆ (P.ballots v).approved.filter (fun x => x ∈ S.val) :=
      fun x hx => Finset.mem_filter.mpr ⟨h hx, hx⟩
    calc P.committeeSize = S.val.card := S.property.symm
      _ ≤ _ := Finset.card_le_card hsub
  exact le_antisymm hle hge

/-- Si le ballot d'un votant est contenu dans le comité, son bonheur atteint
    le cardinal de ce ballot : le filtre ne retire rien. -/
lemma happiness_eq_card_of_subset (P : ApprovalProfile V A)
    (S : Committee A P.committeeSize) (v : V)
    (h : ((P.ballots v).approved) ⊆ S.val) :
    Happiness P S v = ((P.ballots v).approved).card := by
  unfold Happiness
  rw [Finset.filter_true_of_mem (fun x hx => h hx)]

/-- Condition suffisante de non-vacuité : si chaque votant approuve un
    sous-ensemble du comité `S`, alors `S` est dans le core. Aucune coalition
    non vide ne peut le bloquer, puisque chaque votant est déjà au maximum de
    son bonheur atteignable. -/
theorem inCore_of_ballots_subset (P : ApprovalProfile V A)
    (S : Committee A P.committeeSize)
    (h : ∀ v : V, ((P.ballots v).approved) ⊆ S.val) : InCore P S := by
  intro T hT hs
  obtain ⟨S', _hne, himp⟩ := hs
  obtain ⟨v, hv⟩ := hT
  have hle : Happiness P S' v ≤ ((P.ballots v).approved).card :=
    happiness_le_approved_card P S' v
  have heq : Happiness P S v = ((P.ballots v).approved).card :=
    happiness_eq_card_of_subset P S v (h v)
  exact absurd (himp v hv) (not_lt.mpr (by rw [heq]; exact hle))

/-- Second critère de non-vacuité : si le comité est contenu dans le ballot de
    **chaque** votant, alors `S` est dans le core. Chaque votant touche la
    taille du comité, qui est le maximum atteignable par tout comité de cette
    taille (`happiness_le_committeeSize`). -/
theorem inCore_of_committee_subset_ballots (P : ApprovalProfile V A)
    (S : Committee A P.committeeSize)
    (h : ∀ v : V, S.val ⊆ (P.ballots v).approved) : InCore P S := by
  intro T hT hs
  obtain ⟨S', _hne, himp⟩ := hs
  obtain ⟨v, hv⟩ := hT
  have hle : Happiness P S' v ≤ P.committeeSize :=
    happiness_le_committeeSize P S' v
  have heq : Happiness P S v = P.committeeSize :=
    happiness_eq_committeeSize_of_subset P S v (h v)
  exact absurd (himp v hv) (not_lt.mpr (by rw [heq]; exact hle))

/-- Sur un profil de **consensus** — tous les votants partagent le même
    ensemble d'approbation `U` — tout comité `S` contenu dans `U` est dans le
    core. -/
theorem inCore_of_common_approval (P : ApprovalProfile V A)
    (S : Committee A P.committeeSize) {U : Finset A}
    (hballot : ∀ v : V, (P.ballots v).approved = U) (hsub : S.val ⊆ U) :
    InCore P S :=
  inCore_of_committee_subset_ballots P S (fun v => by rw [hballot v]; exact hsub)

/-- Non-vacuité du core sur un profil de consensus : dès que la taille du
    comité ne dépasse pas celle de l'ensemble approuvé commun, il existe un
    comité dans le core. -/
theorem exists_inCore_of_common_approval (P : ApprovalProfile V A) {U : Finset A}
    (hballot : ∀ v : V, (P.ballots v).approved = U)
    (hk : P.committeeSize ≤ U.card) :
    ∃ S : Committee A P.committeeSize, InCore P S := by
  obtain ⟨S, hsub, hcard⟩ := Finset.exists_subset_card_eq hk
  exact ⟨⟨S, hcard⟩, inCore_of_common_approval P ⟨S, hcard⟩ hballot hsub⟩

/-- Cas borné explicite : deux votants, trois candidats, un comité de taille
    deux, les deux votants approuvent exactement `{0, 1}`. Le seul comité de
    taille deux contenu dans l'ensemble approuvé est `{0, 1}` lui-même ; le
    core est donc non vide, et l'hypothèse de consensus n'est pas vide de
    contenu puisqu'un second comité (`{0, 2}` ou `{1, 2}`) existe et donnerait
    un bonheur strictement moindre. -/
def twoVotersThreeCandidates : ApprovalProfile (Fin 2) (Fin 3) where
  ballots := fun _ => ⟨{0, 1}⟩
  committeeSize := 2

/-- Le core du profil `twoVotersThreeCandidates` est non vide. -/
example : ∃ S : Committee (Fin 3) 2, InCore twoVotersThreeCandidates S :=
  exists_inCore_of_common_approval (U := ({0, 1} : Finset (Fin 3)))
    twoVotersThreeCandidates (by decide) (by decide)

end ApprovalConsensus
