# Coordination proactive — 1 PR/wakeup plancher + pool global + never-idle

S'applique à **tous les workers du cluster CoursIA** (po-2023/2024/2025/2026) et au **coordinateur ai-01**. Source : mandat user 2026-05-23, durci 2026-06-30, 2026-07-01, 2026-07-06, 2026-07-19.

**Détail (backlog 8 sources, mapping machines→tracks, cadence, anti-patterns, incidents)** : [docs/reference/proactive-coordination-detail.md](../../docs/reference/proactive-coordination-detail.md).

## Règles HARD

1. **≥1 PR entre 2 wakeups = PLANCHER, jamais plafond.** Une PR livrée ne **clôt pas** la session : re-pioche **immédiatement** et enchaîne autant de PRs que la fenêtre le permet (débit nominal ~2 PR/h). S'arrêter après 1 PR alors qu'il reste du temps **et** 60+ issues ouvertes = **sous-régime**, pas « cycle terminé ».
2. **2 tracks en flight minimum** : une **track principale** (dispatchée, Epic) + une **side-track autonome** que le worker avance **même si le coordinateur s'absente 1-2 jours**.
3. **Side-tracks → sous-agents spécialistes async (HARD).** Quand un specialist `.claude/agents/` couvre la side-track, la déléguer en **`run_in_background: true`** pendant que le worker interactif tient la main track. Roster : [docs/reference/subagents-reference.md](../../docs/reference/subagents-reference.md).
4. **Backlog pickup au wakeup vide (HARD).** Sans nouveau feedback / directive / tâche : **ne pas s'arrêter** — piocher dans le backlog et produire la PR du cycle.

5. **Pool = TOUT l'ouvert, cross-lane, jamais siloté (HARD).** Cette règle **domine 1-4** : le backlog n'est PAS ta « famille » ni ta « lane », c'est **`gh issue list --state open` en entier**. Ta lane (`machine × workspace`) est une étiquette de **reporting**, PAS une frontière de travail. Fil courant épuisé → tu **NE demandes PAS un grain au coordinateur** : `gh issue list --state open`, prends **n'importe quelle issue techniquement exécutable** (autre famille, autre langage, autre lane — **rien n'est « le turf d'un autre »**), pose `[CLAIMED] <#N> — <machine:workspace> <ts>` (anti-double-claim), livre. **Conclure « rien à faire » alors que `gh issue list` renvoie >0 = échec de méthode.** Sur-te-spécialiser = te starver toi-même.

6. **Variété obligatoire — le tarissement est structurellement interdit (HARD).** Les règles 1-5 interdisent l'idle ; celle-ci interdit la **monotonie**, et pose l'auto-alimentation comme **principe**, pas comme rattrapage du coordinateur. Une lane ne PEUT PAS se tarir : le worker pioche **de lui-même**, **varié**, même si le coordinateur est absent plusieurs cycles.
   - **Substance en plat principal** : chaque cycle, viser un grain d'EPIC de fond (preuve Lean, backtest/training, série notebook, moteur SOTA, sécu/infra).
   - **Nettoyage/doc = à-côté plafonné** (budget G-VAR-2, cf [variation-protocol.md](variation-protocol.md)) : nécessaire, jamais le plat unique. Une journée entière sur un seul registre monotone = sous-régime à corriger **de soi-même**.
   - **Rotation genres ET familles** : alterner Lean / .NET / Python / QC / GenAI / docs ; le pool global rend la variété toujours accessible ; ne jamais tunneliser un mono-thème.

7. **Never-idle ancré — le « forensic-floor » n'est PAS un livrable (HARD).** Les workers ont contourné 1-6 en inventant un **vocabulaire d'idle-honnête** qui *sonne* comme du travail (« forensic-floor », « drained-confirm », « NO-CHANGE-NEEDED honnête », « pool saturée », « Nᵉ cycle honnête », « due-diligence »). Parce qu'un nouveau synonyme est toujours inventable, l'autorité n'est **pas une liste de mots** mais un **test de résultat** :

   > **Test de fin de cycle.** Ai-je, ce cycle, sorti un grain de **substance** du pool global et l'ai-je transformé en PR (ou fait avancer un livrable multi-cycle) ? **Si non, et que `gh issue list` renvoie >0** — *quel que soit le label* que je m'apprête à poster — **c'est un échec de méthode, pas un cycle honnête.** Un scan forensic qui trouve 0 défaut n'est **pas** un livrable : c'est le **prélude** au pick suivant, jamais sa substitution.

   **Trois évasions mortes :**
   - **« Pas ma famille / ma capability »** — FAUX. L'assignation de famille est un ordre de **préférence de reporting**, pas une frontière. **Les seules vraies barrières sont deux** : (a) **GPU-only** (forward-pass, génération image/vidéo) ; (b) **vision-only** (QA visuel → lanes MiniMax/ai-01). **Tout le reste est piochable par n'importe quelle lane.**
   - **« Tout ce qui reste est gated »** — un *gate* qualifie une **prochaine action précise**, pas une issue entière. Avant de le déclarer, **énumérer chaque issue ouverte + son gate précis** ; si UNE a un sous-grain exécutable (doc, notebook CPU, audit, prose, test, module numpy), **le prendre**.
   - **« Les micro-fixes suffisent »** — non : nettoyage/tooling/accents/doc sont plafonnés et ne sont JAMAIS le plat principal. Viser un grain **DEEP ou MED** chaque cycle (tiers : [variation-protocol.md](variation-protocol.md)).

   **Mécanisme never-empty (ordre strict).** (1) Consommer la **deep-queue** de ta lane (dashboard, pré-autorisée « brûle dans l'ordre, ne m'attends pas, `[CLAIMED]` avant chaque item, ASK seulement sur blocker réel »). (2) Queue vide → `gh issue list --state open` + **n'importe quel** grain de substance exécutable. (3) La deep-queue est un **bootstrap éphémère**, pas la condition du travail : queue vide **et** coordinateur absent 3 cycles → le pool global reste la source, et « rien à faire » demeure **structurellement impossible** tant que `gh issue list` renvoie >0.

## Leçons ancrées (checks pré-`[DONE]`)

- **L721 ★ — stale-tracker guard.** Avant **tout** claim de « 0 PR / saturated / idle » : `gh pr list --author <self> --state open --json number -q 'length'`. L'omettre produit des états terminaux **faux négatifs** (une session parallèle a peut-être déjà livré).
- **L740 ★ — CronList 7-day verify.** Les crons `CronCreate` sont **session-only, auto-expirent à 7 j**. Avant `[DONE]`, vérifier qu'ils vivent encore et **re-armer** — un cron expiré = wakeup mort = lane-idle silencieuse.
- **L898 ★★★ — collision guard : avant d'ÉCRIRE, pas avant de pousser.** Avant de poser un `[CLAIMED]`, rédiger un steer/verdict, éditer un fichier **ou** `git push` : `git worktree list` + `gh pr list --search head:<branch>` + `gh pr list --search "<mot-clé>"` + `gh pr list --state open --json files` sur le **chemin** visé. Relire l'artefact sur `main` **ne remplace pas** ce check : `main` ne montre pas ce qui est *ouvert*. Coût ~10 s ; coût de l'omission = travail dupliqué et rétractation publique.

## Règle de sélection

Le pool par défaut est **`gh issue list --state open` (global, cross-lane)** ; les 8 sources priorisées du détail sont un **ordre de préférence DANS ce pool**, pas une restriction à ta famille. Prendre **un item à la fois** (`[CLAIMED]` avant de commencer), livrer, puis **re-piocher aussitôt**. Le garde-fou G.5 « pas de shopping cart » interdit d'ouvrir N **deep-tracks parallèles**, il ne plafonne **pas** le nombre de PRs séquentielles.

**Anti-pattern interdit** : auditer la tranche étroite de SA famille, la trouver cohérente, puis poster un `[ASK coordinator]` — alors que le pool offrait des dizaines de grains cross-lane. **Le coordinateur n'est PAS un distributeur de grains** : il merge, alimente le pool en issues scopées, et déconflitte les claims.

## Voir aussi

- [docs/reference/proactive-coordination-detail.md](../../docs/reference/proactive-coordination-detail.md) — backlog 8 sources, mapping machines→tracks, cadence, anti-patterns, incidents
- [variation-protocol.md](variation-protocol.md) — **opérationnalise R6/R7** : tag `Grain:` + 3 gates + merge-gate + provisionnement
- [coordinator-discipline.md](coordinator-discipline.md) — ai-01 merge actif, no languishing
- [docs/reference/subagents-reference.md](../../docs/reference/subagents-reference.md) — roster spécialistes
