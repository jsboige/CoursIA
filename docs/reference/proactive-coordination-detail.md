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

## Vérification pré-cycle (L282 / L283 / L786 / L915) — leçons post-c.264

Consolidees depuis les incidents cross-machine c.264 / c.288-289 / c.797 / c.796 et le PR feedback upstream. **Dures** : à executer AVANT tout claim, pas après.

**L282 — Mirror-lanes collision**. Une machine avec 2 lanes (CoursIA **et** CoursIA-2) = 2 workers distincts. Avant `gh issue claim` ou poster `[CLAIMED]`, verifie **le dashboard de la lane ciblee** : un doublon mirroir (incident fondateur #5640/#5641 sur #5635, 6 min apart, ai-01 arbitrage 13:51Z) est une **perte de cycle pour les deux workers** + overhead coordinateur. `roosync_dashboard(action:"read", type:"workspace", section:"all")` sur **les 2 dashboards** (workspace-CoursIA + workspace-CoursIA-2) avant de claim.

**L283 — Confiance hierarchique = `gh API > git log > dashboard intercom > status condense`**. Avant de propager un claim d'etat (merge / OPEN / contenu main) : `gh pr view N --json state,mergedAt,mergeCommit` + `git ls-tree origin/main <file>` + `git log origin/main --oneline -- <file>`. Le **status condense auto-92%** du dashboard peut **halluciner** un merge (po-2026 c.288 : "#5657 MERGED by jsboige" alors que PR OPEN CLEAN awaiting sweep). Source : condensation LLM hallucine des PRs sur 4 cycles consecutifs.

**L786 — Honest-drain diagnostic AVANT claim "lane exhausted"**. Avant de poster un statut terminal-idle (forensic-floor, drained, saturé, no-change, loophole) : `gh issue list --state open | wc -l` > 0 ne suffit pas. **Identifier le grain executable pour ta capability** (CPU-only-po et lecture OK, GPU-only exclu) — test : pour chaque issue ouverte, peux-tu (a) la lire, (b) la decomposer en sous-grain non-GPU, (c) executer le sous-grain ? Si ≥1 sous-grain executable → claim, sinon re-arme. Incident : 4 lanes "drained" simultanement c.796, pool offrait ≥6 grains CPU frais non-claimés (cf c.797 dispatch).

**L915 — PR OPEN MERGEABLE ≠ PR mergee**. Avant de claim un cycle N dependant d'une PR OPEN MERGEABLE upstream, verifie `gh pr view N --json mergedAt` (non-null = mergee). 2 options : (a) reporter c.N a `mergedAt` confirme ; (b) redécouper le grain en **substrate standalone** + c.N+1 (le livrable de N est comprehensible sans merger l'upstream). Source : worker-side claim triple phantom-dispatach (c.715 #7225, c.797 #8031, c.792 #7733) corrige par L715-L2.

**C715-L2 — Cross-repo work detection AVANT claim**. Avant de prendre un grain sur issue #X, triple-verification :
```
git log --all --oneline --grep "#<issue>"                    # 0 commit upstream
git ls-tree origin/main <path>                              # 0 fichier upstream
gh pr list --search "#<issue>" --state all                   # 0 PR antérieure
```
3 zeros = grain libre. ≥1 hit = verifier l'etat de l'upstream (`gh pr view N --json mergedAt`) et choisir (a) reporter, (b) redécouper, (c) rafraichir la substance.

**Routine verification first-and** (à coller dans `~/.claude/CLAUDE.md` personalisation ou alias bash) :

```bash
# Avant tout claim de PR dependante d'une upstream
gh pr view N --json state,mergedAt,baseRefOid 2>/dev/null | head -5
git merge-base --is-ancestor <sha> origin/main && echo "MERGED" || echo "NOT-MERGED"
```
