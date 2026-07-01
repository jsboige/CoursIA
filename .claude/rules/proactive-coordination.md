# Coordination proactive — 1 PR/wakeup + main track + side-track async

S'applique a **tous les workers du cluster CoursIA** (po-2023/2024/2025/2026) et au **coordinateur ai-01**. Source : mandat user 2026-05-23. Backlog sources + mapping machines + reporting + anti-patterns : [docs/proactive-coordination-detail.md](../../docs/reference/proactive-coordination-detail.md).

## Regles HARD

1. **≥1 PR entre 2 wakeups.** Chaque worker produit au moins une PR par cycle. Pas d'attente passive.
2. **2 tracks en flight minimum** : une **track principale** (dispatchee, Epic) + une **side-track autonome** (Epic distincte) que le worker fait avancer **meme si le coordinateur s'absente 1-2 jours**.
3. **Side-tracks → sous-agents specialistes async (HARD).** Quand un specialist `.claude/agents/` couvre la side-track, la deleguer en **`run_in_background: true`** pendant que le worker interactif tient la main track. Ne pas refaire a la main ce qu'un specialist fait mieux. Roster + mapping : [docs/subagents-reference.md](../../docs/reference/subagents-reference.md).
4. **Backlog pickup au wakeup vide (HARD, mandat user 2026-05-28).** Si un worker se reveille **sans nouveau feedback / sans nouvelle directive coord / sans tache nouvelle**, il **NE S'ARRETE PAS**. Il **pioche dans le backlog** (8 sources prioritisees, cf [detail](../../docs/reference/proactive-coordination-detail.md#backlog-pickup--sources-autorisees-ordre-de-priorite-decroissant)) et produit la PR du cycle. Pas d'idle, pas de "rien a faire".

5. **Pool = TOUT l'ouvert, cross-lane, jamais silote (HARD, mandat user 2026-06-30 + 2026-07-01).** Cette regle DOMINE 1-4 : le backlog n'est PAS ta « famille » ni ta « lane », c'est **`gh issue list --state open` en entier** (~65 issues), partage par tous. Ta lane (`machine x workspace`) est une etiquette de **reporting**, PAS une frontiere de travail. Quand ton fil courant est epuise (rollout de ta famille sature, side-track livree), tu **NE t'arretes PAS et tu NE demandes PAS un grain au coordinateur** : tu fais `gh issue list --state open`, tu prends **n'importe quelle issue que tu sais techniquement executer** — autre famille, autre langage, autre lane (.NET, Lean, QC, GenAI, docs : **rien n'est « le turf d'un autre »**) —, tu poses `[CLAIMED] <#N> — <machine:workspace> <ts>` sur le dashboard (anti-double-claim), et tu livres la PR. **Conclure « rien a faire » alors que `gh issue list` renvoie >0 = echec de methode, jamais un etat legitime.** Sur-te-specialiser sur ta famille = te starver toi-meme.

## Regle de selection

Le pool par defaut est **`gh issue list --state open` (global, cross-lane)** ; les « 8 sources prioritisees » du detail sont un **ordre de preference DANS ce pool**, pas une restriction a ta famille. Prendre **un seul item** par wakeup (pas de shopping cart, cf G.5), produire **1 PR concrete** avant fin de tour. Reporting format + anti-patterns wakeup vide + cycle normal : [detail](../../docs/reference/proactive-coordination-detail.md).

**Anti-pattern interdit (incident 2026-07-01, po-2025).** Auditer la tranche README de SA SEULE famille, la trouver coherente, puis poster un `[ASK coordinator]` pour un grain frais — alors que `gh issue list --state open` offrait des dizaines de grains executables cross-lane (#3360 bug RL Python, #4039 gittins bi-track, #3968/#2876 cross-famille, entrees ML.Net manquantes…). Un audit de tranche etroite qui se termine en ASK = le silo, pas de la proactivite. **Le coordinateur n'est PAS un distributeur de grains** : il merge les PRs, alimente le pool en issues bien scopees, et deconflitte les claims — il ne debloque pas un worker qui a 65 issues ouvertes sous la main.

## Voir aussi

- [docs/proactive-coordination-detail.md](../../docs/reference/proactive-coordination-detail.md) — backlog 8 sources, mapping machines→tracks, cadence, anti-patterns
- [docs/subagents-reference.md](../../docs/reference/subagents-reference.md) — roster specialistes + mapping
- [docs/scripts-reference.md](../../docs/reference/scripts-reference.md) — scripts depot
- [coordinator-discipline.md](coordinator-discipline.md) — ai-01 merge actif, no languishing
- CLAUDE.md "PROCEDURES RECURRENTES" — productivite pendant operations longues (2 tracks min)
