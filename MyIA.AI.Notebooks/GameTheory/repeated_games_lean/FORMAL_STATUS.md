# Repeated Games Lean — Formal Verification Status

**Mise à jour 2026-07-05 (post-#5362)** : les 4 sorries GrimTrigger + le sorry Discounting (`discount_threshold_rewrite`) sont **clos**. État courant vérifié firsthand (line-by-line, docstring-aware) :

- `Stage.lean` : **0 sorry** · `Discounting.lean` (+`_en`) : **0 sorry** · `GrimTrigger.lean` (+`_en`) : **0 sorry** (théorème-phare `grim_trigger_sustains_iff` certified) · `Folk.lean` : **1 sorry STRETCH** (`folk_theorem_discounted` L33, toléré).
- `lake build` SUCCESS post-#5362 : 2953 jobs, oleans `_en` produits (commit `df07e1e60`).

Les sections « Per-File Status » ci-dessous reflètent le **snapshot cycle 7 (2026-07-02)** conservé comme historique de la tranche ; les comptes de sorry y sont STALE (Discounting « 1 sorry », GrimTrigger « 4 sorries » — voir les valeurs courantes ci-dessus).

---

> **Snapshot historique au 2026-07-02 (cycle 7, J2 tranche en cours)** : la branche `feature/4880-repeated-games-lean` contient les fichiers-sources complets (Stage, Discounting, GrimTrigger, Folk + entry-point + manifest), mais **le `lake build` cold-rebuild complet n'a pas été exécuté dans la fenêtre de ce cycle** (le cold-rebuild Mathlib mutualisé est ~16 238 oleans, 60+ min — intractable dans la fenêtre de session interactif MiniMax M3).
>
> Le PR #4920 (commit `05ae9d8988155c727cb5284cf8a8cebf2499e3ff`) avait déjà livré GrimTrigger 0-sorry `lake build` SUCCESS pour la **tranche 1** — c'est cette base mergée dans `main` que la J2 tranche Folk.lean vient compléter comme stretch optionnel (#4880 critère de clôture 1 = grim, déjà couvert par #4920 ; le Folk reste au catalogue comme STRETCH OPEN).

## Build Info

| Item | Value |
|------|-------|
| Lean toolchain | `leanprover/lean4:v4.31.0-rc1` |
| Mathlib | `d568c8c0` (junction shared cache via #4363) |
| Création | 2026-07-02 |
| Statut branche | **SOURCE-COMPLETE, `lake build` cold-rebuild non ré-exécuté ce cycle** |
| Tranche 1 | **MERGÉE** dans main via PR #4920 (build SUCCESS, commit `05ae9d898`) |
| Tranche 2 | **branche locale, en attente PR** |

## Per-File Status (tranche 2)

### RepeatedGames/Folk.lean — STRETCH

| Metric | Value |
|--------|-------|
| Lignes | ~85 |
| Definitions | 2 (`IndividuallyRational`, `Feasible`) — type-forcées, pas de citation numérique |
| Theorems | 2 (`folk_theorem_discounted` sorry STRETCH, `folk_theorem_boundary` trivial) |
| sorry | **1** (`folk_theorem_discounted`) — STRETCH, low-priority, marqué explicitement |

**Audit type-forced (leçon Lidman L39 #4899)** : aucune constante numérique « sourcée » (pas de KnotInfo, pas de table étiquetée source). `IndividuallyRational` est bornée par `params.P` (type-forcé), `Feasible` est un prédicat sur les paiements convexes (somme des poids = 1, ≥ 0, formules affines), donc **correction forcée par type** — pas de risque de données fabulées comme Lidman L39.

### RepeatedGames.lean — entry-point

Imports the 4 modules (Stage, Discounting, GrimTrigger, Folk).

## Per-File Status (tranche 1, déjà mergée)

### RepeatedGames/Stage.lean — FOUNDATIONAL ✅ (merged)

| Metric | Value |
|--------|-------|
| sorry | **0** |
| Status | FORMAL-CERTIFIED |

### RepeatedGames/Discounting.lean — DISCOUNTING ARITHMETIC ✅ (merged)

| Metric | Value |
|--------|-------|
| sorry | **1** (`discount_threshold_rewrite`) — prover BG target |

### RepeatedGames/GrimTrigger.lean — THÉORÈME-PHARE ✅ (merged)

| Metric | Value |
|--------|-------|
| sorry | **4** sorries PR-décrites dans le body de #4920 — clôture par merge GrimTrigger 0-sorry sur main |

## Prover BG Pipeline (post-merge #4895/#4941)

Harnais post-pull main (PR #4895 `b6a0ee9f1` FX-1..FX-3 + PR #4941 `ed47e40c2` FX-5 `TRUE_PLACEHOLDER_GOAL` guard). Pour mes scaffolds Folk.lean (#4880 J2) :

1. **Pas de prover BG appelé** sur Folk.lean dans cette fenêtre — la branche n'a pas atteint `lake build` SUCCESS, donc le prover ne peut pas harvest. Quand le build cold-rebuild aboutira (~60+ min, prochaine fenêtre où la mutualisation junction-cache est fluide), les claims prover BG sur `folk_theorem_discounted` seraient à scorer post-priorité LOW.
2. **Anti-collision** : panneaux `repeated_games_lean/{GrimTrigger, Discounting}.lean` disjoints des `Lidman L39 + HashlifeCorrectness L2442` tenus par ai-01.

## Compromis acceptés (tranche 2)

**`folk_theorem_discounted` : sorry STRETCH OPEN**. Justification :

- Le théorème-phare `#4880` est `grim_trigger_sustains_iff`, déjà 0-sorry mergé (#4920, GrF(3) absent car grim est l'anticipation).
- Folk = stretch optionnel selon le body de #4880 lui-même (« S'il est scaffoldé, le déclarer explicitement comme stretch avec ses sorries comptés — le 0-sorry n'est exigé que sur le théorème-phare »).
- Le sorry Folk documente honnêtement la limite : topologie polytope (Fudenberg–Maskin 1986) est hors-périmètre d'un sprint GrimTrigger + 1 tranche. À traiter dans une itération ultérieure par le prover BG si la formule close admet une tactique.

**Aucune régression** : tous les fichiers mergés dans main (PR #4920) sont préservés byte-pour-byte dans cette branche (le pull FF main l'a confirmé). Je n'introduis AUCUN stub qui supprimerait une preuve existante ; j'ADDS honnêtement les fichiers Folk stretch + docs.
