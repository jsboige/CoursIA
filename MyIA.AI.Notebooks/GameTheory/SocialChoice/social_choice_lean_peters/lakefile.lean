/-
  DominikPeters/SocialChoiceLean Reference Project
  =================================================

  This project references DominikPeters/SocialChoiceLean as a Lake dependency
  to explore and present their formalized social choice results:

  - Gibbard-Satterthwaite theorem
  - Condorcet impossibilities (participation, reinforcement, strategyproofness)
  - Duggan-Schwartz theorem
  - Holliday's impossibility
  - 15+ voting rules with axiom verification (Split Cycle, Schulze, Black, etc.)

  Reference: https://github.com/DominikPeters/SocialChoiceLean
  License: MIT (DominikPeters)
-/

import Lake
open Lake DSL

package «social_choice_peters» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
    @ "520045ab14e26149ee970e2e617ca04b09bde5d6"

require SocialChoiceLean from git
  "https://github.com/DominikPeters/SocialChoiceLean.git"

@[default_target]
lean_lib «PetersTour» where
  -- Tour of DominikPeters/SocialChoiceLean results
  -- globs incluent le sibling EN (i18n #4980) pour que `lake build` le compile
  -- aussi : sans cela, PetersTour_en.lean n'est jamais élaboré et un Lean CI
  -- vert est un faux pass (orphan-trap #6749). Même pattern que sudoku_lean.
  globs := #[`PetersTour, `PetersTour_en]

/-
  Tranche 1 du plan #17988 (issue parente) — socle de définitions du core
  d'approbation (Becker-Greger-Peters 2026, arXiv 2609.11912).

  `ApprovalDefs` (FR) et `ApprovalDefs_en` (EN) forment une paire i18n #4980
  (sibling byte-identical hors commentaires). Le glob EN est explicite pour
  éviter l'orphan-trap #6749. Voir `scripts/lean/check_i18n_siblings.py`.
-/
@[default_target]
lean_lib «ApprovalDefs» where
  globs := #[`ApprovalDefs, `ApprovalDefs_en]

/-
  Tranche 2 du plan #17988 — définition du core d'approbation et lemmes
  d'identité (`StrictlyImproves`, `InCore`).

  `ApprovalCore` (FR) et `ApprovalCore_en` (EN) forment une paire i18n #4980
  (sibling byte-identical hors commentaires). Le glob EN est explicite pour
  éviter l'orphan-trap #6749. Voir `scripts/lean/check_i18n_siblings.py`.
-/
@[default_target]
lean_lib «ApprovalCore» where
  globs := #[`ApprovalCore, `ApprovalCore_en]

/-
  Tranche 3 (résultat intermédiaire) du plan #17988 — le core implique
  l'optimalité de Pareto (`ParetoDominates`).

  `ApprovalPareto` (FR) et `ApprovalPareto_en` (EN) forment une paire i18n
  #4980 (sibling byte-identical hors commentaires). Le glob EN est explicite
  pour éviter l'orphan-trap #6749. Voir `scripts/lean/check_i18n_siblings.py`.
-/
@[default_target]
lean_lib «ApprovalPareto» where
  globs := #[`ApprovalPareto, `ApprovalPareto_en]

/-
  Residu du plan #17988 — quotas Hare `n/k` et Droop `n/(k+1)`, seuil de
  coalition entier exact (`IsQuotaLarge`).

  `ApprovalQuota` (FR) et `ApprovalQuota_en` (EN) forment une paire i18n
  #4980 (sibling byte-identical hors commentaires). Le glob EN est explicite
  pour éviter l'orphan-trap #6749. Voir `scripts/lean/check_i18n_siblings.py`.
-/
@[default_target]
lean_lib «ApprovalQuota» where
  globs := #[`ApprovalQuota, `ApprovalQuota_en]

/-
  Residu du plan #17988 — non-vacuité du core sur les profils de consensus
  et cas borné explicite (`exists_inCore_of_common_approval`).

  `ApprovalConsensus` (FR) et `ApprovalConsensus_en` (EN) forment une paire
  i18n #4980 (sibling byte-identical hors commentaires). Le glob EN est
  explicite pour éviter l'orphan-trap #6749. Voir
  `scripts/lean/check_i18n_siblings.py`.
-/
@[default_target]
lean_lib «ApprovalConsensus» where
  globs := #[`ApprovalConsensus, `ApprovalConsensus_en]

/-
  Tranche « paiement » du plan #17988 — quotas (Hare n/k, Droop n/(k+1)),
  système de paiement fidèle à la définition 3.2 de Becker-Greger-Peters
  2026 (arXiv 2609.11912), et sens « certificat ⟹ core » du théorème 3.3
  (`not_blocksCore_of_paymentCertificate`), preuve élémentaire sans Farkas.

  `ApprovalPayment` (FR) et `ApprovalPayment_en` (EN) forment une paire
  i18n #4980 (sibling byte-identical hors commentaires). Le glob EN est
  explicite pour éviter l'orphan-trap #6749. Voir
  `scripts/lean/check_i18n_siblings.py`.
-/
@[default_target]
lean_lib «ApprovalPayment» where
  globs := #[`ApprovalPayment, `ApprovalPayment_en]
