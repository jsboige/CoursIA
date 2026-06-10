# Coordination proactive — detail

Detail de [.claude/rules/proactive-coordination.md](../../.claude/rules/proactive-coordination.md). Voir aussi [subagents-reference.md](subagents-reference.md), [scripts-reference.md](scripts-reference.md).

## Backlog pickup — sources autorisees (ordre de priorite decroissant)

Wakeup vide : prendre la **premiere source non-vide**, **un seul item**, produire **1 PR concrete**.

| # | Source | Action | Pourquoi cet ordre |
|---|--------|--------|---------------------|
| 1 | Side-track Epic dispatchée propre au worker (cf mapping) | Avancer prochaine sous-tache, 1 PR | Engagement deja pris |
| 2 | Ses propres PRs OPEN en attente review/iter | Re-iter feedback bot/coord, rebase, fix CI | Pas laisser pourrir |
| 3 | Issues `priority-high` non assignees dans son domaine | Self-assign + dispatch + 1 PR | Urgences declarees |
| 4 | PRs languishing > 3 jours sans reponse (siennes ou domaine) | Re-iter ou cloturer | Hygiene cluster |
| 5 | Issues `priority-medium` du domaine | Self-assign + 1 PR | Travail cataloguable |
| 6 | Low-priority Epics stockees (#1646 Grothendieck, #1647 Conway Phase 2, #1650 Translation, #1651 Conway Phase 3 FWT) | 1 phase / 1 pilier, 1 PR partielle | Stock activable "fenetres calmes" |
| 7 | Audit findings non traites (NanoClaw #488 etc.) | 1 reassessment + 1 PR si CONFIRMED (cf [audit-reassessment.md](../../.claude/rules/audit-reassessment.md)) | Backlog d'enquete |
| 8 | Consolidation/documentation de son domaine | 1 PR docs | Wiki Karpathy / SDDD documentaire |

## Anti-patterns wakeup vide (interdits)

- "Rien de nouveau, je me rendors" → **REFUSE** ; pioche backlog avant tout ScheduleWakeup
- "J'attends le prochain dispatch coord" → **REFUSE** ; le coord n'est pas un distributeur flux tendu
- Picorer 3+ items "pour faire du chiffre" → **REFUSE** ; 1 item, 1 PR
- Annoncer "BLOCKED" alors que sources 5-8 non explorees → **REFUSE** (G.7 stagnation cross-cycle = escalade)

## Reporting wakeup vide

```text
[INFO] Wakeup R<N> vide (pas de feedback/dispatch nouveau).
Backlog pickup : source <#X> "<nom source>" → item #<NNN> "<titre>".
PR cible : #<MMM> en cours.
```

Pas de `[BLOCKED]` ni `[DONE pas de travail]`. Wakeup vide = opportunite backlog, pas blocage.

## Mapping machine → track principale + side-track (cycle courant)

| Machine | Track principale | Side-track autonome (Epic) | Sous-agents async |
|---------|------------------|----------------------------|-------------------|
| **po-2026** | Proving BG (lot de cibles ; Lattice INTRACTABLE → #1452) | #1453 harness co-evolution (forensic) | `general-purpose` |
| **po-2024** | Trading #1409 | #1454 Training & Post-Training (RL/PPO + GenAI fine-tuning) | `qc-*`, `notebook-designer`, `notebook-iterative-builder` |
| **po-2023** | Audiobook #1273 (v4 + prosodie + wrapup) | GenAI series #1385 | `notebook-modernizer/executor/validator`, `infer-notebook-enricher` |
| **po-2025** | #1455 TP→exemples guides + nouveaux exercices | Modernisation #999 | `series-improver`, `notebook-cleaner/enricher/designer/cell-iterator` |
| **ai-01** | Coordination + merges + reviews | #1453 + #1454 partagees | idem, async |

Epics co-evolutives partagees avec ai-01 : #1453 + #1454. Le **pionnier** (po-2024/po-2026) defriche sur sa carte, **ai-01 approfondit sur la grosse carte**.

## Cadence

- ScheduleWakeup horaire (~3540-3555s jitter) re-arme a chaque tour coord/worker interactif (ping-pong) — cf CLAUDE.md global "Multi-Machine Ping-Pong".
- Le sous-agent async tourne **pendant** le sommeil entre wakeups : au reveil, recuperation notification + integre/PR.

## Anti-patterns cycle normal (interdits)

- Worker avec une seule track (BG seul, ou main seule sans side-track) → demander/prendre 2e track immediatement
- Refaire a la main une tache couverte par un specialist async (modernisation serie, batch notebooks, QC robustness…)
- Side-track sans Epic de rattachement (intracable, meurt a l'absence du coordinateur)
- Lancer 2 sous-agents editeurs sur le **meme** notebook/serie (collision) — read-only OK en parallele, editeurs = un par fichier
