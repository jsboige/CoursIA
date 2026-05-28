# Coordination proactive — 1 PR/wakeup + main track + side-track async

S'applique à **tous les workers du cluster CoursIA** (po-2023/2024/2025/2026) et au **coordinateur ai-01**.

**Source** : mandat user 2026-05-23. Coordination plus directive et exigeante de chaque machine.

## Règle HARD

1. **≥1 PR entre 2 wakeups.** Chaque worker produit au moins une PR par cycle. Pas d'attente passive.
2. **2 tracks en flight minimum** : une **track principale** (dispatchée, Epic) + une **side-track autonome** (Epic distincte) que le worker fait avancer **même si le coordinateur s'absente 1-2 jours**.
3. **Side-tracks → sous-agents spécialistes async (HARD).** Quand un specialist `.claude/agents/` couvre la side-track, la déléguer en **`run_in_background: true`** pendant que le worker interactif tient la main track sur wakeup horaire. Ne pas refaire à la main ce qu'un specialist fait mieux. Roster + mapping : [docs/subagents-reference.md](../../docs/subagents-reference.md).
4. **Backlog pickup au wakeup vide (HARD, mandat user 2026-05-28).** Si un worker se réveille **sans nouveau feedback / sans nouvelle directive coord / sans tâche nouvelle depuis le précédent wakeup**, il **NE S'ARRÊTE PAS**. Il **pioche dans le backlog** et produit la PR du cycle. Pas d'idle, pas de "rien à faire", pas de "j'attends le prochain dispatch". Le backlog est explicitement défini ci-dessous comme un puits inépuisable d'unités de travail dispatchables sans intervention coord.

## Backlog pickup — sources autorisées (ordre de priorité décroissant)

Quand le worker se réveille sans feedback / dispatch nouveau, il **choisit la première source non-vide** dans cet ordre :

| # | Source | Action | Pourquoi cet ordre |
|---|--------|--------|---------------------|
| 1 | **Side-track Epic dispatchée propre au worker** (cf mapping ci-dessous) | Avancer la prochaine sous-tâche, produire 1 PR | Engagement déjà pris, livrable attendu |
| 2 | **Ses propres PRs OPEN en attente review/iter** | Re-iter sur feedback bot/coord, rebase, fix CI | Ne pas laisser ses propres PRs pourrir |
| 3 | **Issues `priority-high` non assignées dans son domaine** | Self-assign + dispatch + 1 PR | Urgences déclarées, scope clair |
| 4 | **PRs languishing > 3 jours sans réponse** (siennes ou domaine) | Re-iter ou cloturer proprement | Hygiène cluster, anti-stagnation |
| 5 | **Issues `priority-medium` du domaine du worker** | Self-assign + 1 PR | Travail substantiel cataloguable |
| 6 | **Low-priority Epics stockées** (#1646 Grothendieck, #1647 Conway Phase 2, #1650 Translation, #1651 Conway Phase 3 FWT) | Picorer 1 phase / 1 pilier ; produire 1 PR partielle | Stock long terme activable ; mandat user "fenêtres calmes" |
| 7 | **Audit findings non traités** (NanoClaw #488, etc.) | 1 reassessment + 1 PR si CONFIRMED (cf [audit-reassessment.md](audit-reassessment.md)) | Backlog d'enquête |
| 8 | **Consolidation/documentation de son domaine** (READMEs, docs/, MAJ catalogue) | 1 PR docs | Wiki Karpathy / SDDD documentaire |

**Règle de sélection** : prendre la **première source non-vide**, **un seul item** par wakeup (pas de shopping cart, cf G.5), produire **1 PR concrète** avant fin de tour.

## Anti-patterns interdits au wakeup vide

- "Rien de nouveau, je me rendors" → **REFUSÉ** ; pioche dans backlog (sources 1-8) avant tout `ScheduleWakeup`.
- "J'attends le prochain dispatch coord" → **REFUSÉ** ; le coord n'est pas un distributeur de tâches en flux tendu, le worker doit s'auto-alimenter.
- Picorer 3+ items du backlog "pour faire du chiffre" → **REFUSÉ** ; 1 item, 1 PR, ré-armée propre.
- Annoncer "BLOCKED" sur backlog vide alors que sources 5-8 sont non explorées → **REFUSÉ** (cf G.7 stagnation cross-cycle = escalade documentée).

## Reporting au wakeup vide

Le worker poste sur le dashboard workspace :
```
[INFO] Wakeup R<N> vide (pas de feedback/dispatch nouveau).
Backlog pickup : source <#X> "<nom source>" → item #<NNN> "<titre>".
PR cible : #<MMM> en cours.
```
Pas de `[BLOCKED]` ni de `[DONE pas de travail]`. Le wakeup vide est **par construction** une opportunité de backlog pickup, pas un blocage.

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

## Anti-patterns interdits (cycle normal)

- Worker avec une seule track (BG seul, ou main seule sans side-track) → demander/prendre une 2e track immédiatement.
- Refaire à la main une tâche couverte par un specialist async (modernisation série, batch notebooks, QC robustness…).
- Side-track sans Epic de rattachement (intraçable, meurt à l'absence du coordinateur).
- Lancer 2 sous-agents éditeurs sur le **même** notebook/série (collision) — read-only OK en parallèle, éditeurs = un par fichier.

## Voir aussi

- [docs/subagents-reference.md](../../docs/subagents-reference.md) — roster spécialistes + mapping
- [docs/scripts-reference.md](../../docs/scripts-reference.md) — scripts dépôt
- [.claude/rules/coordinator-discipline.md](coordinator-discipline.md) — ai-01 merge actif, no languishing
- CLAUDE.md "PROCEDURES RECURRENTES" — productivité pendant opérations longues (2 tracks min)
