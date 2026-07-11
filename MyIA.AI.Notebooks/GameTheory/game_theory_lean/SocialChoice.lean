/--
# SocialChoice — Théorie du choix social (Arrow + Sen + Voting)

Bibliothèque de théorie du choix social formalisée en Lean 4 (Mathlib), inspirée
de `asouther4/lean-social-choice` (Lean 3) et `chasenorman/Formalized-Voting`
(Lean 4).

## Résultats majeurs

- **Théorème d'impossibilité d'Arrow** (Geanakoplos 2005, *Three Brief Proofs of
  Arrow's Impossibility Theorem*) : aucune règle de vote ne satisfait simultanément
  les axiomes d'unanimité (P), indépendance (I) et absence de dictateur (D).
  Démonstration via la **construction de Geanakoplos** : à partir d'un profil à
  trois alternatives, on construit des profils décisifs qui forcent un cycle ou
  un dictateur.
- **Paradoxe libéral de Sen** (Sen 1970, *Collective Choice and Social Welfare*) :
  même un libéralisme minimal — chaque individu décide d'au moins une paire
  privée — entre en conflit avec le critère de Pareto minimal. Formulation
  bidirectionnelle symétrisant droits et préférences.
- **Voting.lean** ajoute les définitions par marges, les critères de Condorcet
  (Condorcet winner, Condorcet loser), les préférences **single-peaked**, le
  **Split Cycle** (Hollis & Restelli 2021) et la **clone-proofness** (Tideman
  1987 / Schulze par défaut).

## Statut formel

`Arrow.lean`, `Sen.lean`, et `Voting.lean` : **FORMAL-CERTIFIED (0 sorry)**.

`Voting.lean` : `median_voter_theorem` requiert l'hypothèse
`strictly_single_peaked_profile` (Issue #973 Option 1) ; le workhorse
`median_voter_theorem_strict` prend des hypothèses explicites de
monotonie stricte pour produire la conclusion.

## Références

- Amartya Sen, *Collective Choice and Social Welfare* (1970).
- John Geanakoplos, *Three Brief Proofs of Arrow's Impossibility Theorem* (2005).

Dépôt Lean 3 d'origine :
https://github.com/asouther4/lean-social-choice

Référence Lean 4 (DominikPeters) :
https://github.com/DominikPeters/SocialChoiceLean

Voir l'issue #4980 (i18n Lean FR+EN, EPIC ratifiée par le user le 2026-07-04).

---

# SocialChoice — Social Choice Theory (Arrow + Sen + Voting)

Social choice theory library formalized in Lean 4 (Mathlib), inspired by
`asouther4/lean-social-choice` (Lean 3) and `chasenorman/Formalized-Voting`
(Lean 4).

## Major results

- **Arrow's impossibility theorem** (Geanakoplos 2005, *Three Brief Proofs of
  Arrow's Impossibility Theorem*): no voting rule can simultaneously satisfy
  unanimity (P), independence (I), and non-dictatorship (D). Proof via the
  **Geanakoplos construction**: from a three-alternative profile, decisive
  coalitions are built that force either a cycle or a dictator.
- **Sen's liberal paradox** (Sen 1970, *Collective Choice and Social Welfare*):
  even minimal liberalism — each individual decides at least one private pair —
  conflicts with minimal Pareto. Bidirectional formulation symmetrizing rights
  and preferences.
- **Voting.lean** adds margin-based definitions, Condorcet criteria (Condorcet
  winner, Condorcet loser), **single-peaked** preferences, **Split Cycle**
  (Hollis & Restelli 2021) and **clone-proofness** (Tideman 1987 / Schulze
  default).

## Formal status

`Arrow.lean`, `Sen.lean`, and `Voting.lean`: **FORMAL-CERTIFIED (0 sorry)**.

`Voting.lean`: `median_voter_theorem` requires the hypothesis
`strictly_single_peaked_profile` (Issue #973 Option 1); the workhorse
`median_voter_theorem_strict` takes explicit strict-monotonicity hypotheses
to produce the conclusion.

## References

- Amartya Sen, *Collective Choice and Social Welfare* (1970).
- John Geanakoplos, *Three Brief Proofs of Arrow's Impossibility Theorem* (2005).

Original Lean 3 repository:
https://github.com/asouther4/lean-social-choice

Lean 4 reference (DominikPeters):
https://github.com/DominikPeters/SocialChoiceLean

See issue #4980 (Lean i18n FR+EN, EPIC ratified by user on 2026-07-04).

Convention i18n (EPIC #4980, décision user 2026-07-04) : ce fichier root
aggregator est bilingue inline (FR canonique d'abord, EN en miroir),
conformément au pattern canonique `CooperativeGames.lean` (pilote EPIC #4980,
PR #5883 MERGED 2026-07-10), `RepeatedGames.lean` (c.356, PR #6048 MERGED
2026-07-11), `Minimax.lean` (c.364, PR #6101 MERGED 2026-07-11), et `Utility.lean`
(c.353, PR #6045 MERGED 2026-07-11). Les sous-modules substantiels
(`SocialChoice.Basic`, `SocialChoice.Arrow`, `SocialChoice.Sen`, `SocialChoice.Voting`,
`SocialChoice.Framework`, `SocialChoice.SortedListCounting`, `SocialChoice.MechanismDesign`)
vivent dans des fichiers siblings `_en.lean` séparés (cf. #4980 Phase 0.5, décision
user ratifiée 2026-07-04 sur la paire FR-canonical-first + EN-mirror-second).
-/

import SocialChoice.Basic
import SocialChoice.Framework
import SocialChoice.Arrow
import SocialChoice.Sen
import SocialChoice.Voting
import SocialChoice.SortedListCounting
