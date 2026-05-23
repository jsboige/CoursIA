# Coordination proactive — 1 PR/wakeup + main track + side-track async

S'applique à **tous les workers du cluster CoursIA** (po-2023/2024/2025/2026) et au **coordinateur ai-01**.

**Source** : mandat user 2026-05-23. Coordination plus directive et exigeante de chaque machine.

## Règle HARD

1. **≥1 PR entre 2 wakeups.** Chaque worker produit au moins une PR par cycle. Pas d'attente passive.
2. **2 tracks en flight minimum** : une **track principale** (dispatchée, Epic) + une **side-track autonome** (Epic distincte) que le worker fait avancer **même si le coordinateur s'absente 1-2 jours**.
3. **Side-tracks → sous-agents spécialistes async (HARD).** Quand un specialist `.claude/agents/` couvre la side-track, la déléguer en **`run_in_background: true`** pendant que le worker interactif tient la main track sur wakeup horaire. Ne pas refaire à la main ce qu'un specialist fait mieux. Roster + mapping : [docs/subagents-reference.md](../../docs/subagents-reference.md).

## Mapping machine → track principale + side-track (cycle courant)

| Machine | Track principale | Side-track autonome (Epic) | Sous-agents async |
|---------|------------------|----------------------------|-------------------|
| **po-2026** | Proving BG (lot de cibles ; Lattice INTRACTABLE → #1452) | #1453 harness co-evolution (forensic) | `general-purpose` (forensic traces) |
| **po-2024** | Trading #1409 | #1454 Training & Post-Training (RL/PPO + GenAI fine-tuning) | `qc-*`, `notebook-designer`, `notebook-iterative-builder` |
| **po-2023** | Audiobook #1273 (consolider v4 + prosodie + wrapup) | GenAI series #1385 | `notebook-modernizer/executor/validator`, `infer-notebook-enricher` |
| **po-2025** | #1455 TP→exemples guidés + nouveaux exercices | Modernisation #999 | `series-improver`, `notebook-cleaner/enricher/designer/cell-iterator` |
| **ai-01** | Coordination + merges + reviews | #1453 (proving) + #1454 (training) partagées | idem, async |

Epics co-évolutives partagées avec ai-01 : #1453 + #1454. Le **pionnier** (po-2024/po-2026) défriche sur sa carte, **ai-01 approfondit sur la grosse carte**.

## Cadence

- ScheduleWakeup horaire (~3540-3555s jitter) re-armé à chaque tour coord/worker interactif (ping-pong) — cf CLAUDE.md global "Multi-Machine Ping-Pong".
- Le sous-agent async tourne **pendant** le sommeil entre wakeups : au réveil, le worker récupère la notification de complétion et intègre/PR le livrable.

## Anti-patterns interdits

- Worker avec une seule track (BG seul, ou main seule sans side-track) → demander/prendre une 2e track immédiatement.
- Refaire à la main une tâche couverte par un specialist async (modernisation série, batch notebooks, QC robustness…).
- Side-track sans Epic de rattachement (intraçable, meurt à l'absence du coordinateur).
- Lancer 2 sous-agents éditeurs sur le **même** notebook/série (collision) — read-only OK en parallèle, éditeurs = un par fichier.

## Voir aussi

- [docs/subagents-reference.md](../../docs/subagents-reference.md) — roster spécialistes + mapping
- [docs/scripts-reference.md](../../docs/scripts-reference.md) — scripts dépôt
- [.claude/rules/coordinator-discipline.md](coordinator-discipline.md) — ai-01 merge actif, no languishing
- CLAUDE.md "PROCEDURES RECURRENTES" — productivité pendant opérations longues (2 tracks min)
