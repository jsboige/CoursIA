# Inventaire des projets Lean 4 — `GameTheory`

Inventaire transverse de tous les projets de formalisation Lean 4 sous `GameTheory/`.

Réconcilié le 2026-08-26 contre les pins effectifs (`lean-toolchain`, `lake-manifest.json`) et le
module-set réel du disque (issue #13138). Comptes `sorry` mesurés avec l'instrument canonique
`scripts/lean/count_code_sorry.py --json` (champ `distinct_code_sorry`), jamais `grep -c sorry`.

## Résumé

**Lakes actifs (8)** :

| Répertoire | Toolchain | sorry (production) | Modules | Statut |
|-----------|-----------|--------------------|---------|--------|
| `game_theory_lean` | v4.32.1 | 1 (stretch Folk, #4880) | StableMarriage + CooperativeGames + SocialChoice + RepeatedGames + Swaps (49 `.lean` FR+EN) | COMPLET (EPIC #4365) |
| `lean_game_defs` | v4.32.1 | 0 | 12 (6 FR + 6 `_en`) | COMPLET (defs partagés) |
| `lean_game_defs_ext` | v4.32.1 | 0 | Bayesian/* 24 (12 FR + 12 `_en`) + 2 umbrellas | COMPLET |
| `minimax_lean` | v4.32.1 | 0 | ZeroSum + Concavity + SionApplication (+ `_en`) | COMPLET |
| `assignment_lean` | v4.32.1 | 0 | Definitions / Duality / KuhnMunkres / Optimality (+ `_en`) | COMPLET (#12598) |
| `asymmetric_information_lean` | v4.32.1 | 0 | Lemons / Signaling / Screening / MiyazakiWilson / BayesianLink (+ `_en`) | COMPLET (Epic #12844) |
| `social_choice_lean_peters` | v4.32.1 | 0 | PetersTour (+ `_en`) | Référence seule |
| `conway_cgt_lean` | v4.31.0-rc2 | 0 | CGTTour (+ `_en`) | Tour de référence |

**Tombstones (absorbés, EPIC #4365)** :

| Répertoire | Devenir |
|-----------|---------|
| ~~`cooperative_games_lean`~~ | **Supprimé** (rm #6587) → [`game_theory_lean/CooperativeGames/`](game_theory_lean/CooperativeGames/) |
| ~~`social_choice_lean`~~ | Absorbé (#6058, 2026-07-11) → [`game_theory_lean/SocialChoice/`](game_theory_lean/SocialChoice/) — ne subsistent que 4 markdown tombstone |
| ~~`repeated_games_lean`~~ | Absorbé (#6146) → [`game_theory_lean/RepeatedGames/`](game_theory_lean/RepeatedGames/) — coquille archive conservée (lakefile neutralisé, 0 module) |

Note : `SymbolicAI/Lean/examples/llm_assisted_proof.lean` (2 sorry) est un exemple pédagogique, pas du code de production. `asymmetric_information_lean` porte 2 *naive* sorry (prose/docstrings) pour 0 vrai sorry de code.

**Série hommage Conway déplacée** : `conway_lean/` (hommage Conway — Doomsday, FRACTRAN, Look-and-Say, Nim, Angel) a été déplacé vers [`SymbolicAI/Lean/conway_lean/`](../SymbolicAI/Lean/conway_lean/) car il formalise des résultats Conway moins connus (pas du contenu game-théorique en soi). Les cibles de calibration du prover définies dans `agent_tests/prover/config.py` suivent le nouveau chemin.

**Calibration déplacée** : `calibration_lean/` a été déplacé vers [`SymbolicAI/Lean/calibration_lean/`](../SymbolicAI/Lean/calibration_lean/) (issue #1764) car c'est un composant de harnais prover, pas du contenu game-théorique.

---

## Par lake

### 1. game_theory_lean

**EPIC #4365 (phase 4)** : lake cible multi-module, pôle d'absorption GT 6→2. A absorbé :
`stable_marriage_lean/` (supprimé, PRs #5904/#5905/#5910/#5911/#5913), `cooperative_games_lean/`
(rm #6587), `social_choice_lean/` (#6058), `repeated_games_lean/` (#6146). Le lake porte
également `Swaps` (grain #12222, compagnon du notebook GameTheory-03a).

**Objectif** : formaliser le curriculum GameTheory — jeux coopératifs (Shapley, cœur), mariage stable de Gale-Shapley, choix social (Arrow, Sen, électeur médian), jeux répétés (théorème folk), chemins d'échange sur jeux ordinaux 2×2.

**Toolchain** : v4.32.1 | **Dépendances** : Mathlib4

| Groupe de modules | sorry | Contenu |
|--------------|-------|---------|
| `StableMarriage/` (5 FR + 5 `_en`) | 0 | algorithme GS, terminaison, stabilité, `exists_isManOptimal`, `woman_pessimal`, treillis de Knuth + réfutations d'anciens énoncés faux |
| `CooperativeGames/` (3 FR + 3 `_en`) | 0 | jeux à transferts (TU), Core, `bondareva_shapley : Core.Nonempty ↔ Balanced`, valeur de Shapley (décomposition de Möbius), machinerie de séparation par cônes |
| `SocialChoice/` (9 FR + 8 `_en`) | 0 | Arrow (Geanakoplos 2005), paradoxe libéral de Sen, électeur médian / Split Cycle / clones, véracité Vickrey, AMD, cœur `PrefOrder`/`Profile`/SWF |
| `RepeatedGames/` (4 FR + 4 `_en`) | 1 (stretch) | `grim_trigger_sustains_iff` (théorème-phare, 0 sorry) ; `folk_theorem_discounted` / `folk_theorem_boundary` portent 1 sorry stretch (#4880) |
| `Swaps/` (FR-only) | 0 | `Table`, générateurs adjacents, certificat de chemin, `distance_dilemme_chicken` |

**Compilation** : `lake build` — SUCCESS. CI : `lean-game-theory.yml`, `lean-social-choice.yml`.

**Preuves clés** :
- `gale_shapley_stable` — PR #1194 ; `exists_isManOptimal` (honnête, via poids minimal sur le demi-treillis des jointures) ; `woman_pessimal` — PR #1521 ; `meetSpouse_injective` / `joinSpouse_injective` — PR #1522
- `no_cross_match_is_false` / `doctor_optimal_eq_top_is_false` — réfutations vérifiées au kernel d'anciens énoncés faux
- `bondareva_shapley` (`Core.Nonempty ↔ Balanced`) — prouvé intégralement, aucun axiome ajouté (tranches compactes + Weierstrass, #3954)
- `grim_trigger_sustains_iff` — FORMAL-CERTIFIED, 0 sorry

---

### 2. ~~cooperative_games_lean~~ — Supprimé (rm #6587)

> **Lake standalone supprimé** (commit `522c450e9`, PR #6587). Modules `Basic` / `ConeKernel` /
> `Shapley` (+ jumeaux `_en`) absorbés byte-identique dans
> [`game_theory_lean/CooperativeGames/`](game_theory_lean/CooperativeGames/) (EPIC #4365). La
> section ci-dessous est conservée comme trace d'audit du statut de preuve (0 sorry, préservé
> dans la cible). Pour l'état courant, voir [§1. game_theory_lean](#1-game_theory_lean).

**Statut à la suppression** : COMPLET (0 sorry). `bondareva_shapley` prouvé intégralement — le
crux d'atteinte `hb_witness` de la direction retour a été clos par la PR #3954 via un argument
tranches compactes + Weierstrass, contournant le `ProperCone.hyperplane_separation` manquant de
Mathlib sans aucun axiome ajouté. Lignage : #3933 (cone kernel) → #3941 (bridge) → #3945
(decoding) → #3951 (`hb_strict`) → #3954 (attainment).

---

### 3. ~~social_choice_lean~~ — Absorbé (#6058)

> **⚑ Tombstone documentaire — home canonique déplacé.** Depuis la PR #6058 (EPIC #4365
Phase-4, 2026-07-11), les sept modules (Basic, Framework, Arrow, Sen, Voting,
MechanismDesign, SortedListCounting) ont été absorbés byte-identique dans
[`game_theory_lean/SocialChoice/`](game_theory_lean/SocialChoice/) (FR canonique + miroirs
`_en.lean` Pattern A #4980). **Ce répertoire n'est plus un lake** — la coquille technique
(`lakefile.lean`, `lean-toolchain`, `lake-manifest.json`) a été retirée ; ne subsistent que
4 markdown (`README`, `STATUS`, `NOTICE`, `LEAN_PREREQUISITES`) conservés comme tombstone.

**Statut (historique, préservé dans le home canonique)** : COMPLET, 0 sorry — impossibilité
d'Arrow (Geanakoplos 2005), paradoxe libéral de Sen, électeur médian / Split Cycle / clones,
véracité Vickrey + contre-exemple au premier prix (#1469). Build repris par
`.github/workflows/lean-social-choice.yml` sur `game_theory_lean`.

---

### 4. social_choice_lean_peters

**Objectif** : projet de référence important DominikPeters/SocialChoiceLean comme dépendance Lake.

**Toolchain** : v4.32.1 (convergé avec le parc depuis #12134, 2026-08-21) | **Dépendances** : Mathlib4 (`520045ab`), SocialChoiceLean `94a4c650` (revs effectives du `lake-manifest.json`)

| Fichier | sorry | Description |
|------|-------|-------------|
| `PetersTour.lean` + `PetersTour_en.lean` | 0 | Tour curaté des résultats formalisés de Peters (i18n #4980) |

**Compilation** : `lake build` — SUCCESS | **Référence seule, pas une cible de preuve**

**Contenu** : importe la bibliothèque de Peters (Gibbard-Satterthwaite, Duggan-Schwartz, 4 impossibilités de Condorcet, 15+ règles de vote avec vérification d'axiomes). Lake de support du notebook compagnon du tour SocialChoiceLean (prévu, pas encore créé).

**Relation avec `social_choice_lean` (absorbé)** : complémentaire, pas un doublon. Notre cadre historique utilisait un `PrefOrder` custom (nos preuves, désormais dans `game_theory_lean/SocialChoice/`) ; ce lake expose le `LinearOrder` de Peters (référence externe). Les deux sont conservés par complétude pédagogique.

---

### 5. ~~repeated_games_lean~~ — Absorbé (#6146)

> **⚑ Archive — home canonique déplacé.** Depuis la PR #6146 (EPIC #4365 Phase-4), les quatre
modules sources (`Stage`, `Discounting`, `GrimTrigger`, `Folk`) ont été absorbés
byte-identique dans [`game_theory_lean/RepeatedGames/`](game_theory_lean/RepeatedGames/).
Ce répertoire est conservé comme **coquille archive** : `package`, `require mathlib`,
manifest et documentation restent présents, mais la `lean_lib` est neutralisée dans le
`lakefile.lean` (ses globs matchaient 0 fichier depuis le déménagement). Certification et
build repris par `game_theory_lean` (`.github/workflows/lean-game-theory.yml`).

**Statut (historique, préservé dans le home canonique)** : `grim_trigger_sustains_iff`
(préserve un Nash parfait en sous-jeux ssi δ ≥ seuil) prouvé intégralement, 0 sorry. Le théorème
Folk (`folk_theorem_discounted`) porte 1 sorry stretch, toléré au titre de #4880.

---

### 6. minimax_lean

**Objectif** : formaliser le cadre minimax des jeux à somme nulle à deux joueurs — bilinéarité des paiements, concavité, et application du minimax de Sion.

**Toolchain** : v4.32.1 | **Dépendances** : Mathlib4

| Fichier | sorry | Description |
|------|-------|-------------|
| `Minimax/ZeroSum.lean` (+ `_en`) | 0 | structure de paiement à somme nulle, bilinéarité (`payoff_add_in_x`, `smul`), `continuous_payoff` ; existence du point-selle dérivée du minimax de Sion de Mathlib |
| `Minimax/Concavity.lean` (+ `_en`) | 0 | lemmes de concavité alimentant l'application de Sion |
| `Minimax/SionApplication.lean` (+ `_en`) | 0 | application du minimax de Sion au point-selle en stratégies mixtes |

**Compilation** : `lake build Minimax` — SUCCESS | **COMPLET : 0 sorry**

**Faits clés** : bilinéarité et continuité des paiements prouvées 0 sorry ; **l'existence du point-selle** (`∃ mixed strategies, max_x min_y = min_y max_x`) est *dérivée* du théorème minimax de Sion de Mathlib — documentée et prouvée, **pas** laissée en `sorry`.

---

### 7. lean_game_defs

**Objectif** : définitions de types partagées pour la théorie des jeux (jeux sous forme normale, jeux bayésiens, jeux combinatoires, choix social, regret) — la couche fondation réutilisée par les notebooks GT Lean. Autonome (Lean core seul, zéro dépendance Mathlib).

**Toolchain** : v4.32.1 | **Dépendances** : Lean core (sans Mathlib)

| Fichier (FR + jumeau `_en`) | sorry | Description |
|---------------------------|-------|-------------|
| `LeanGameDefs/Basic.lean` | 0 | types fondamentaux NormalFormGame / FiniteGame / Game2x2 |
| `LeanGameDefs/Nash.lean` | 0 | équilibre de Nash, meilleure réponse, dominance stricte |
| `LeanGameDefs/Bayesian.lean` | 0 | types de jeux bayésiens |
| `LeanGameDefs/Combinatorial.lean` | 0 | types de jeux combinatoires, minimax |
| `LeanGameDefs/SocialChoice.lean` | 0 | primitives de choix social (`dictatorship_satisfies_pareto`, `dictatorship_satisfies_iia`) |
| `LeanGameDefs/Regret.lean` | 0 | définitions regret / CFR |

**Compilation** : `lake build LeanGameDefs` — SUCCESS (CI `lean-game-defs.yml` + `lean-game-defs-ext.yml`) | **COMPLET : 0 sorry, sans Mathlib**

**Statut** : lake autonome depuis #2752 (`lakefile.toml`, `lean-toolchain` pinné v4.32.1, `lake-manifest.json`, CI dédiée). Couche de définitions infrastructurelle (2 théorèmes vérifiant les axiomes de dictature), support des notebooks GT Lean. `lean_game_defs_ext` (suivant) l'étend avec des preuves de design de mécanismes bayésiens.

---

### 8. lean_game_defs_ext

**Objectif** : jeux bayésiens & design de mécanismes — véracité Vickrey, équilibre bayésien de Nash, enchères, réputation, jeu fictif, regret. Extension de `lean_game_defs` (définitions partagées), sans Mathlib.

**Toolchain** : v4.32.1 | **Dépendances** : Lean core (sans Mathlib)

| Fichier (FR + jumeau `_en`) | sorry | Description |
|---------------------------|-------|-------------|
| `Bayesian/Types.lean` | 0 | définitions de types de jeux bayésiens |
| `Bayesian/BNE.lean` | 0 | cadre d'équilibre bayésien de Nash + raffinement |
| `Bayesian/Vickrey.lean` | 0 | théorème de véracité de Vickrey (enchère au second prix) |
| `Bayesian/Auction.lean` | 0 | mécanismes d'enchère |
| `Bayesian/Information.lean` + `InfoGames.lean` | 0 | structures d'information, jeux d'information |
| `Bayesian/Reputation.lean` | 0 | dynamique de réputation |
| `Bayesian/FictitiousPlay.lean` + `Regret.lean` | 0 | jeu fictif, minimisation du regret |
| `Bayesian/Max.lean` + `Sum.lean` | 0 | auxiliaires max/somme |
| `Bayesian/Examples.lean` | 0 | exemples résolus |

**Compilation** : `lake build` — SUCCESS | **COMPLET : 0 sorry, sans Mathlib**

**Statut** : véracité Vickrey (stratégie dominante de l'enchère au second prix = enchérir sincèrement) prouvée 0 sorry, sans Mathlib. Support du notebook compagnon Lean-11b BayesianGamesExt.

---

### 9. conway_cgt_lean

**Objectif** : tour de référence de la théorie combinatoire des jeux (nombres surréels, jeux partisans, nimbers) telle que formalisée dans [`vihdzp/combinatorial-games`](https://github.com/vihdzp/combinatorial-games), importée comme dépendance Lake. L'amont est le home actuel de la CGT en Lean après que les modules CGT de Mathlib (`SetTheory.Surreal`/`PGame`/`Game`/`Nimber`) ont été dépréciés (#28063, août 2025) puis retirés (#35550, février 2026). Référence : Conway, *On Numbers and Games* (2001).

**Toolchain** : v4.31.0-rc2 (suit le dépôt amont) | **Dépendances** : Mathlib4 + CombinatorialGames (Apache-2.0, `3c6dcdbc`)

| Fichier | sorry | Description |
|------|-------|-------------|
| `CGTTour.lean` + `CGTTour_en.lean` | 0 | tour de `IGame`/`Game` (pré-jeux concrets + quotient), `Surreal` (théorème de simplicité), `Nimber` (Sprague-Grundy), avec tableau comparatif Mathlib-vs-amont |

**Compilation** : `lake build CGTTour` — SUCCESS | **Tour de référence, 0 sorry**

**Statut** : tour de référence / pédagogique, pas une cible de preuve. Expose l'API amont via `#check` + docstrings plutôt que de prouver de nouveaux théorèmes CGT.

---

### 10. assignment_lean

**Objectif** : squelette de correction de l'algorithme d'affectation de Kuhn-Munkres (hongrois) — lake compagnon du notebook GameTheory-27-Munkres-Assignment, hommage à James R. Munkres (1930-2026). Issue #12598 (1/3). Le primal (matrice de coûts, couplage parfait, valeur), le dual (potentiels, faisabilité, **dualité faible**), le certificat d'optimalité à écart nul, et les invariants structurels de l'algorithme (graphe d'égalité, **invariant de sortie**, **le serrage hongrois préserve la faisabilité duale**). Terminaison et complexité O(n³) volontairement hors scope.

**Toolchain** : v4.32.1 | **Dépendances** : Mathlib4

| Fichier (FR + jumeau `_en`) | sorry | Description |
|---------------------------|-------|-------------|
| `Assignment/Definitions.lean` | 0 | matrice de coûts, couplage parfait (permutation), valeur, optimalité (`value`, `IsOptimal`) |
| `Assignment/Duality.lean` | 0 | potentiels duaux `u`/`v`, faisabilité duale, **dualité faible** (`DualFeasible`, `dualValue`, `weak_duality`) |
| `Assignment/Optimality.lean` | 0 | certificat d'optimalité à écart nul + lemme d'arête d'égalité (`dualValue_eq_of_edges`, `optimality_of_zero_gap`) |
| `Assignment/KuhnMunkres.lean` | 0 | graphe d'égalité, **invariant de sortie**, le **serrage hongrois** préserve la faisabilité duale (`EqEdge`, `kuhn_munkres_correct`, `dualFeasible_tighten`) |
| `Assignment/*_en.lean` (×4) | 0 | jumeaux i18n (EPIC #4980) |

**Compilation** : `lake build Assignment Assignment_en` — SUCCESS (8665 jobs, cf PR #12614) | **COMPLET : 0 sorry** (distinct_code_sorry = 0)

**Théorèmes clés** : `weak_duality`, `dualValue_eq_of_edges`, `optimality_of_zero_gap`, `kuhn_munkres_correct`, `dualFeasible_tighten`.

**Statut** : COMPLET. Notebooks compagnons : GT-27 (implémentation Python + scipy SOTA) et GT-27b (compagnon natif `lean4-wsl` — `#check` des 10 déclarations + certificat `optimal_C3` prouvé au kernel, visibilité EPIC #11703).

---

### 11. asymmetric_information_lean

**Objectif** : formaliser les modèles fondateurs de l'asymétrie d'information — compagnon des notebooks GT-17. Epic #12844 (première livraison, portée bornée conforme à l'audit canonique c.475).

**Toolchain** : v4.32.1 | **Dépendances** : Lean core + `lean_game_defs_ext.Bayesian` (sans dépendance Mathlib)

| Fichier (FR + jumeau `_en`) | sorry | Description |
|---------------------------|-------|-------------|
| `AsymmetricInformation/Lemons.lean` | 0 | marché des lemons d'Akerlof (1970) — point fixe sur les régions de participation |
| `AsymmetricInformation/Signaling.lean` | 0 | signal éducatif de Spence (1973) |
| `AsymmetricInformation/Screening.lean` | 0 | sélection adverse Rothschild-Stiglitz (1976) |
| `AsymmetricInformation/MiyazakiWilson.lean` | 0 | subvention croisée anticipatoire Wilson (1977) / Miyazaki (1977) |
| `AsymmetricInformation/BayesianLink.lean` | 0 | pont non trivial vers `lean_game_defs_ext.Bayesian` |

**Compilation** : `lake build` — SUCCESS | **COMPLET : 0 code sorry** (2 touches naive = prose)

**Bornes explicites** (per README) : pas de théorème général d'existence/uniformité pour l'équilibre anticipatoire (Wilson-MWS) ; pas de clause auxiliaire en κ (Lemons) ; pas de subvention croisée en RS 1976 ; pas de jalon adossé à un `sorry` Mathlib — preuves sur Lean 4 core + `decide`/`omega`.

---

## Cibles de preuve restantes

| Priorité | Cible | Rép. | sorry | Faisabilité |
|----------|--------|-----|-------|-------------|
| P3 | `folk_theorem_discounted` / `folk_theorem_boundary` (stretch toléré) | `game_theory_lean/RepeatedGames/Folk.lean` (+ `_en`) | 1 stretch (#4880) | Faible — direction authentiquement difficile (`… = u_col`), grim couvre déjà le critère de fermeture |

> **Note (correction G.9, 2026-08-26) :** l'ancienne ligne P1 « Basic.lean L309 hCore / Very Low
> (Hahn-Banach) » était stale (#3954 l'a close) ; l'ancien compte « 3 (Lattice) » pour
> `game_theory_lean` était stale aussi — `StableMarriage/Lattice.lean` est à 0 sorry
> (vérifié `count_code_sorry.py` : `distinct_code_sorry = 1`, localisé à `Folk.lean:127`).
> Retirer les cibles stale évite un cycle BG-iter inutile sur un sorry qui n'existe plus
> (cf. lean-merge-discipline §2).

## GO/NO-GO par projet (pour les cycles BG iter)

| Projet | Décision | Justification |
|---------|----------|-----------|
| game_theory_lean | COMPLET | 1 sorry (stretch Folk, toléré #4880). StableMarriage : anciens énoncés faux réfutés, `exists_isManOptimal` honnête prouvé ; Lattice fermé. A absorbé `stable_marriage_lean/` + `cooperative_games_lean/` + `social_choice_lean/` + `repeated_games_lean/` (EPIC #4365). |
| ~~cooperative_games_lean~~ | **Supprimé** (rm #6587) | Absorbé byte-identique dans `game_theory_lean/CooperativeGames/`. |
| ~~social_choice_lean~~ | **Absorbé** (#6058) | 7 modules → `game_theory_lean/SocialChoice/` ; docs tombstone uniquement. |
| ~~repeated_games_lean~~ | **Absorbé** (#6146) | 4 modules → `game_theory_lean/RepeatedGames/` ; coquille archive. |
| lean_game_defs / _ext | COMPLET | 0 sorry, sans Mathlib. |
| minimax_lean | COMPLET | 0 sorry ; application de Sion prouvée. |
| assignment_lean | COMPLET | 0 sorry (#12598). |
| asymmetric_information_lean | COMPLET | 0 code sorry (Epic #12844). |
| social_choice_lean_peters | N/A | Référence seule (Peters `94a4c650`, Mathlib `520045ab`, v4.32.1). |
| conway_cgt_lean | N/A | Tour de référence (v4.31.0-rc2, suit l'amont). |

Les cibles de calibration Conway (Doomsday / FRACTRAN / Look-and-Say / Nim / Angel) vivent dans `SymbolicAI/Lean/conway_lean/` et sont toujours consommées par `agent_tests/prover/config.py` (co-évolution du harnais prover #1453).

---

## Documentation associée

- [docs/lean/sota-2026-analysis.md](../../docs/lean/sota-2026-analysis.md) — SOTA du proving Lean 4 automatisé
- [docs/lean/prover_iteration_history.md](../../docs/lean/prover_iteration_history.md) — Itérations prover F6-F11, B3
- [docs/lean/llm-endpoints.md](../../docs/lean/llm-endpoints.md) — Fournisseurs LLM pour le prover
- [docs/lean/coordinator-workflow.md](../../docs/lean/coordinator-workflow.md) — Workflow build coordinateur + BG iter
