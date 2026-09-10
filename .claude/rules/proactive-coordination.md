# Coordination proactive — 1 PR/wakeup plancher + pool global + never-idle

S'applique à **tous les workers du cluster CoursIA** (po-2023/2024/2025/2026) et au **coordinateur ai-01**. Source : mandat user 2026-05-23, durci 2026-06-30 → 2026-07-19.

**Détail (backlog 8 sources, mapping machines→tracks, cadence, anti-patterns, incidents, leçons L721/L1356 complètes, picker, veine)** : [docs/reference/proactive-coordination-detail.md](../../docs/reference/proactive-coordination-detail.md).

## Règles HARD

1. **≥1 PR entre 2 wakeups = PLANCHER, jamais plafond.** Une PR livrée ne **clôt pas** la session : re-pioche **immédiatement** et enchaîne autant de PRs que la fenêtre le permet (débit nominal ~2 PR/h). S'arrêter après 1 PR alors qu'il reste du temps **et** 60+ issues ouvertes = **sous-régime**, pas « cycle terminé ».
2. **2 tracks en flight minimum** : une **track principale** (dispatchée, Epic) + une **side-track autonome** que le worker avance **même si le coordinateur s'absente 1-2 jours**.
3. **Side-tracks → sous-agents spécialistes async (HARD).** Quand un specialist `.claude/agents/` couvre la side-track, la déléguer en **`run_in_background: true`** pendant que le worker interactif tient la main track. Roster : [docs/reference/subagents-reference.md](../../docs/reference/subagents-reference.md).
4. **Backlog pickup au wakeup vide (HARD).** Sans nouveau feedback / directive / tâche : **ne pas s'arrêter** — piocher dans le backlog et produire la PR du cycle.

5. **Pool = TOUT l'ouvert, cross-lane, jamais siloté (HARD).** Cette règle **domine 1-4** : le backlog n'est PAS ta « famille » ni ta « lane », c'est **`gh issue list --state open` en entier**. Ta lane (`machine × workspace`) est une étiquette de **reporting**, PAS une frontière de travail. Tu **NE demandes PAS un grain au coordinateur** : tu **tires** (ci-dessous), prends **n'importe quelle issue techniquement exécutable** (autre famille, autre langage, autre lane — **rien n'est « le turf d'un autre »**), poses `[CLAIMED] <#N> — <machine:workspace> <ts>` (anti-double-claim), livres. **Conclure « rien à faire » alors que `gh issue list` renvoie >0 = échec de méthode.** Sur-te-spécialiser = te starver toi-même.

**Filtre `candidate-delivered` (#10466)** : une part du pool est du travail **déjà livré mais non fermé** (`See #N` même en résolution complète → GitHub ne ferme pas). Le label, posé par le workflow advisory (PR merged référençant l'issue + silence post-merge, EPICs exclus), **signale sans fermer** — ai-01 tranche en lecture body (G.9). Ne pas re-piocher une issue ainsi labellisée sans vérification firsthand.

**Le pool ne se scanne plus à la main — il se TIRE, et le tirage est le PREMIER GESTE DE CHAQUE CYCLE (HARD, mandats user 2026-08-14 et 2026-08-20).** `gh issue list` plafonne à **30 résultats** triés par récence : un scan manuel ne voit que le récent et referme la boucle de monoculture — la troncature demande un organe, pas plus de vigilance (mesures : [détail, section Picker](../../docs/reference/proactive-coordination-detail.md)). Un steering nommé par le coordinateur **prime quand il existe** — l'exception, équilibrée entre familles et genres (§4 de [variation-protocol.md](variation-protocol.md)).

```bash
python scripts/pick_idle_grain.py --lane <machine:workspace> --prev-genre <genre du grain précédent>
```

Tirage pondéré dans **trois urnes** : **grain** (issue unitaire → la livrer) · **umbrella** (un EPIC → piocher ou **créer un sous-grain dedans**, jamais claimer l'EPIC entier) · **delivered** (une `candidate-delivered` → **réservée au coordinateur et à l'adjoint**, mandat user 2026-09-07 [#15069, garde `DELIVERED_URN_LANES` dans `pick_idle_grain.py`] : une lane worker qui en rencontre une poste `[INFO] candidate-delivered` avec sa preuve et rend la main). Pondération deux axes (âge de création + délaissement) : [détail, section Picker](../../docs/reference/proactive-coordination-detail.md).

**Le picker ne décide pas.** Il propose ; l'agent tranche selon les critères de variété de sa lane et pose son `[CLAIMED]` (`check_lane_claim.py` avant d'**éditer**, cf [lane-claim-protocol.md](lane-claim-protocol.md)). Plutôt que rejouer aveuglément : demander davantage de candidats et passer les exclusions factuelles (`--exclude-issue`, labels, bornes age/inactivité, `--urns`) ; `--reroll` reste le dernier recours ; le cache ne touche jamais les organes minute-sensitive ([détail §Cache](../../docs/reference/proactive-coordination-detail.md)). **Aucun résultat vide filtré ne justifie un `[ASK coordinator]` ni un statut idle.**

**Une exception, et elle passe avant tout : réparer son propre rouge (HARD, mandat user 2026-08-22).**
Le picker **assigne la réparation** (sortie **0** — le grain rendu *est* la reprise) tant que la lane porte
une PR **bloquée et ouverte depuis plus de 24 h** ; il nomme la liste, la cause et le geste. Une PR
réparée et mergée tient le plancher R1, avec son tag `Grain:` d'origine. **Ce qui compte comme à
reprendre** = ce qui **empêche vraiment le merge**, en **quatre** causes : un check **requis** en échec
(`isRequired`), un conflit avec `main`, un `CHANGES_REQUESTED` non levé, et — **en tête des trois
autres** — un **point de review non levé** (HARD, mandat user 2026-08-24 : reprendre ses vieilles PRs
avant de produire), structurellement aveugle aux trois surfaces de [§B.0](../../CLAUDE.md) — la détection
est déléguée à `check_unaddressed_nits.analyse`, **le même organe que le merge-gate** (s'ils
divergeaient, une lane produirait du neuf sur une PR que le merge-gate refusera ; organe injoignable ≠
ardoise propre : vérifier à la main avant de produire). Un advisory rouge n'est **pas** un rouge ;
`mergeStateStatus: BLOCKED` vaut aussi « en attente de review ». Rouge non réparable par cette lane
(garde cassée sur `main`, dépendance d'une autre PR) : l'**écrire en commentaire sur la PR**, puis
`--ignore-red` — l'échappatoire se justifie par écrit, jamais en silence. Une PR sans tag `Grain:`
lisible est invisible à ce garde : son tag manquant est lui-même le défaut à corriger, au coordinateur de
les reprendre. Historique et mesure : [détail, section Réparer son rouge](../../docs/reference/proactive-coordination-detail.md).

6. **Variété obligatoire — le tarissement est structurellement interdit (HARD).** Les règles 1-5 interdisent l'idle ; celle-ci interdit la **monotonie**, et pose l'auto-alimentation comme **principe**, pas comme rattrapage du coordinateur. Une lane ne PEUT PAS se tarir : le worker pioche **de lui-même**, **varié**, même si le coordinateur est absent plusieurs cycles.
   - **Substance en plat principal** : chaque cycle, viser un grain d'EPIC de fond (preuve Lean, backtest/training, série notebook, moteur SOTA, sécu/infra).
   - **Nettoyage/doc = à-côté plafonné** (budget G-VAR-2, cf [variation-protocol.md](variation-protocol.md)) : nécessaire, jamais le plat unique. Une journée entière sur un seul registre monotone = sous-régime à corriger **de soi-même**.
   - **Rotation genres ET familles** : alterner Lean / .NET / Python / QC / GenAI / docs ; le pool global rend la variété toujours accessible ; ne jamais tunneliser un mono-thème.

7. **Never-idle ancré — le « forensic-floor » n'est PAS un livrable (HARD).** Les workers ont contourné 1-6 en inventant un **vocabulaire d'idle-honnête** qui *sonne* comme du travail. Parce qu'un nouveau synonyme est toujours inventable, l'autorité n'est **pas une liste de mots** mais un **test de résultat** :

   > **Test de fin de cycle.** Ai-je, ce cycle, sorti un grain de **substance** du pool global et l'ai-je transformé en PR (ou fait avancer un livrable multi-cycle) ? **Si non, et que `gh issue list` renvoie >0** — *quel que soit le label* que je m'apprête à poster — **c'est un échec de méthode, pas un cycle honnête.** Un scan forensic qui trouve 0 défaut n'est **pas** un livrable : c'est le **prélude** au pick suivant, jamais sa substitution.

   **Trois évasions mortes** (labels bannis : [détail, section Vocabulaire](../../docs/reference/proactive-coordination-detail.md)) :
   - **« Pas ma famille »** — FAUX : famille = préférence de **reporting**, pas frontière. **Seules deux vraies barrières** : (a) **GPU-only** ; (b) **vision-only** (→ lanes MiniMax/ai-01). Le reste est piochable partout.
   - **« Tout ce qui reste est gated »** — un *gate* qualifie une **prochaine action**, pas une issue entière : énumérer chaque issue ouverte + son gate précis ; si UNE a un sous-grain exécutable (doc, notebook CPU, audit, test), **le prendre**.
   - **« Les micro-fixes suffisent »** — non : nettoyage/tooling/doc plafonnés, jamais le plat principal ; viser **DEEP/MED** chaque cycle (tiers : [variation-protocol.md](variation-protocol.md)).

   **Mécanisme never-empty (ordre strict, inversé le 2026-08-20).** (1) **Tirer** — `pick_idle_grain.py`, au démarrage du cycle, systématiquement. (2) Un **steering nommé** du coordinateur (deep-queue, DM `[DISPATCH→inbox]`) **prime sur le tirage quand il existe** : c'est l'exception qui passe devant, pas la règle qu'on consulte d'abord. Le brûler dans l'ordre, ne pas attendre entre items, `[CLAIMED]` avant chaque. (3) Ni tirage exploitable ni steering → le pool global reste la source : « rien à faire » demeure **structurellement impossible** tant que `gh issue list` renvoie >0. La deep-queue est un **bootstrap éphémère**, jamais la condition du travail.

8. **Veine plafonnée = interdit ciblé (HARD, #11343 tranche 2 ; amendé 2026-08-20).** Au-delà de `vein_cap=2` PRs citant la même umbrella dans la journée de la lane, la **PR suivante** DOIT appeler le picker avec la commande exposée par `variation_light_cap.py --check-pr N --genre-signals` (`picker_command` du JSON) pour **écarter l'umbrella saturée**. **Le plafond ne bloque PAS la tranche en cours** (« on ne jette pas du travail écrit », amendement ai-01 2026-08-16) : c'est la PR suivante qui est contrainte. Historique : [détail, section Veine plafonnée](../../docs/reference/proactive-coordination-detail.md).

## Leçons ancrées (checks pré-`[DONE]`)

- **L721 ★ — stale-tracker guard.** Avant tout claim « 0 PR / saturated / idle » : interroger le **tag de lane** (`Grain:`), **PAS** `--author <self>` (compte `jsboige` partagé, #13870) ; la requête se valide par ses **faux négatifs symétriques**. Repli : PR sans tag lisible → sweep `GRAIN-ORPHANS-SWEEP` (#13086). Forme canonique + mesures : [détail, section L721](../../docs/reference/proactive-coordination-detail.md).
- **L740 ★ — CronList 7-day verify.** Les crons `CronCreate` sont **session-only, expirent à 7 j** : avant `[DONE]`, vérifier `CronList` et **re-armer** — un cron expiré = lane-idle silencieuse.
- **L898 ★★★ — collision guard : avant d'ÉCRIRE, pas avant de pousser.** Avant `[CLAIMED]`/steer/édit/push : `git worktree list` + `gh pr list --search head:<branch>` + `--search "<mots-clés>"` + `--state open --json files` sur le **chemin** visé. Relire `main` ne remplace pas ce check (`main` ne montre pas l'*ouvert*). Coût ~10 s ; omission = travail dupliqué + rétractation publique.
- **L1356 ★★★ — preflight de claim : `--state all`, jamais open (incidents #13562/#13608).** Une PR **MERGÉE** ayant livré en rider (sans `Closes #N`) est invisible aux filtres open : avant tout `[CLAIMED]`, (1) `gh pr list --state all --search "<N>"`, (2) inspecter les **worktrees orphelins** nommés pour l'issue. Si livré : `[INFO] candidate-delivered` avec preuve — pas de réimplémentation, pas de close soi-même. Recette complète : [détail, section L1356](../../docs/reference/proactive-coordination-detail.md).

## Règle de sélection

Prendre **un item à la fois** (`[CLAIMED]` avant), livrer, **re-piocher aussitôt** — G.5 interdit N deep-tracks **parallèles**, pas N PRs **séquentielles**. **Anti-pattern interdit** : auditer la tranche étroite de SA famille puis poster un `[ASK coordinator]` alors que le pool offrait des grains cross-lane — c'est le silo (incident fondateur R5/R7, [détail §101](../../docs/reference/proactive-coordination-detail.md)). **Le coordinateur n'est PAS un distributeur de grains** : il merge, scoper les issues, déconflitter les claims.

## Voir aussi

- [docs/reference/proactive-coordination-detail.md](../../docs/reference/proactive-coordination-detail.md) — backlog 8 sources, mapping, cadence, anti-patterns, incidents, leçons complètes, picker, veine
- [variation-protocol.md](variation-protocol.md) — **opérationnalise R6/R7** : tag `Grain:` + 3 gates + merge-gate + provisionnement
- [coordinator-discipline.md](coordinator-discipline.md) — ai-01 merge actif, no languishing
- [docs/reference/subagents-reference.md](../../docs/reference/subagents-reference.md) — roster spécialistes
