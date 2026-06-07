# Coordination proactive — 1 PR/wakeup + main track + side-track async

S'applique a **tous les workers du cluster CoursIA** (po-2023/2024/2025/2026) et au **coordinateur ai-01**. Source : mandat user 2026-05-23. Backlog sources + mapping machines + reporting + anti-patterns : [docs/proactive-coordination-detail.md](../../docs/reference/proactive-coordination-detail.md).

## Regles HARD

1. **≥1 PR entre 2 wakeups.** Chaque worker produit au moins une PR par cycle. Pas d'attente passive.
2. **2 tracks en flight minimum** : une **track principale** (dispatchee, Epic) + une **side-track autonome** (Epic distincte) que le worker fait avancer **meme si le coordinateur s'absente 1-2 jours**.
3. **Side-tracks → sous-agents specialistes async (HARD).** Quand un specialist `.claude/agents/` couvre la side-track, la deleguer en **`run_in_background: true`** pendant que le worker interactif tient la main track. Ne pas refaire a la main ce qu'un specialist fait mieux. Roster + mapping : [docs/subagents-reference.md](../../docs/reference/subagents-reference.md).
4. **Backlog pickup au wakeup vide (HARD, mandat user 2026-05-28).** Si un worker se reveille **sans nouveau feedback / sans nouvelle directive coord / sans tache nouvelle**, il **NE S'ARRETE PAS**. Il **pioche dans le backlog** (8 sources prioritisees, cf [detail](../../docs/reference/proactive-coordination-detail.md#backlog-pickup--sources-autorisees-ordre-de-priorite-decroissant)) et produit la PR du cycle. Pas d'idle, pas de "rien a faire".

## Regle de selection

Prendre la **premiere source non-vide** du backlog (sources 1-8 par priorite decroissante), **un seul item** par wakeup (pas de shopping cart, cf G.5), produire **1 PR concrete** avant fin de tour. Reporting format + anti-patterns wakeup vide + cycle normal : [detail](../../docs/reference/proactive-coordination-detail.md).

## Voir aussi

- [docs/proactive-coordination-detail.md](../../docs/reference/proactive-coordination-detail.md) — backlog 8 sources, mapping machines→tracks, cadence, anti-patterns
- [docs/subagents-reference.md](../../docs/reference/subagents-reference.md) — roster specialistes + mapping
- [docs/scripts-reference.md](../../docs/reference/scripts-reference.md) — scripts depot
- [coordinator-discipline.md](coordinator-discipline.md) — ai-01 merge actif, no languishing
- CLAUDE.md "PROCEDURES RECURRENTES" — productivite pendant operations longues (2 tracks min)
