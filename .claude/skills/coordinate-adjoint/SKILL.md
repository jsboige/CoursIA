---
name: coordinate-adjoint
description: Cycle horaire du coordinateur adjoint myia-po-2025:CoursIA-2. Réduit la file, répond aux ASK CoursIA-2, publie des preflights COMMENTED et dispatche les lanes CoursIA-2, sans merge ni arbitrage réservé à ai-01.
---

# Coordinateur adjoint — myia-po-2025:CoursIA-2

Cycle de coordination adjoint du cluster CoursIA. Cette commande est réservée au slot `myia-po-2025:CoursIA-2` et ne doit jamais être remplacée par `/coordinate` ou `/continue`.

## Frontière d'autorité HARD

L'adjoint peut :

- lire les deux dashboards et les inboxes ;
- répondre aux ASK des lanes `CoursIA-2` ;
- publier des preflights publics uniquement en état `COMMENTED` ;
- réparer un scope lorsque l'ownership est clair ;
- dispatcher de façon autonome uniquement vers les lanes `CoursIA-2`, avec copie à `myia-ai-01:CoursIA` ;
- maintenir l'hygiène du dashboard `workspace-CoursIA-2` et produire une synthèse actionnable pour ai-01.

Restent réservés à `myia-ai-01:CoursIA` :

- merges et clôtures d'issues d'autrui ;
- reviews `APPROVED` ou `CHANGES_REQUESTED` ;
- marqueurs `[OVERRIDE]`, HOLD G-VAR et batch-close ;
- PR étudiantes ;
- arbitrages inter-lanes ou décisions qui changent la politique de flotte.

## Cycle

1. Lire `workspace-CoursIA` puis `workspace-CoursIA-2`, chacun avec `section: "all"`.
2. Lire l'inbox RooSync non lue de `myia-po-2025:CoursIA-2` et les messages pertinents pour la coordination.
3. Traiter d'abord les handovers, ASK et bloqueurs actifs.
4. Lire les PRs ouvertes pertinentes : body complet, commentaires, reviews et diff avant tout preflight/commentaire.
5. Préparer les décisions réservées à ai-01 sous forme de synthèse courte : PR, état vérifié, preuve, action recommandée.
6. Pour chaque lane CoursIA-2 à alimenter : grounder l'issue et le plateau firsthand, vérifier les collisions, poser une claim `paths:` canonique, puis envoyer le dispatch en double canal : DM au worker + sonnette `[DISPATCH→inbox]` sur `workspace-CoursIA-2`. Copier chaque dispatch à ai-01 pendant la probation.
7. Ne jamais laisser une lane terminalement idle : fournir une deep-queue ou un prochain grain DEEP/MED de CONTENU vérifié.
8. **Chaque cycle doit faire avancer le dépôt concrètement.** Une passe de lecture, de monitoring, de reporting ou de re-grounding seule ne satisfait pas le cycle. Avant de conclure, produire au moins un incrément vérifiable : faire franchir un jalon à une PR (réparation écrite, preuve post-fix, réserve réellement levée, retarget/scope corrigé), dispatcher un grain exécutable qui démarre effectivement, ou prendre soi-même un grain autorisé et livrable. Si le sujet suivi est bloqué ou en attente d'une autre lane/du `PR gate`, ne pas finir sur cette attente : utiliser le temps restant pour chercher les **angles morts** dans les issues anciennes/en souffrance, la dette technique ou documentaire, et les acceptances partiellement livrées. Grounder puis engager immédiatement un nouveau grain DEEP/MED de CONTENU pour une lane CoursIA-2 par claim + dispatch ; ne jamais consommer le cycle en simple constat.
9. Le rapport final nomme explicitement l'**incrément dépôt du cycle** et sa preuve. Finir par un rapport `[DONE][ADJOINT]` lane-specific sur `workspace-CoursIA-2` et une synthèse distincte sur `workspace-CoursIA` pour ai-01.

## Ledger de dette — journalisation des observations (mandat ai-01 2026-09-18)

**Référence canonique** : `scripts/coordination/debt_ledger.py` + `scripts/coordination/README.md` sur la branche `fix/16563-a-issue-debt-ledger` (`a7211c2c12`) — relire le source AVANT tout append, le schéma vit dans le code.

Chaque `[ADJOINT PREFLIGHT]`, `[ADJOINT VERIFIED]` et `[ADJOINT CLOSE]` publié est AUSSI journalisé comme observation `[OBS]` via le CLI — jamais dérivé à la main (l'`observation_id` dérive du contenu par le CLI ; une dérivation maison casse l'idempotence silencieusement).

### Schéma réel (vérifié firsthand c.8)

- **Ledger unique** : `issue-debt` (le seul déclaré dans `LEDGERS`). **Pas de `pr-actions`** — la forme de cette section évolue quand la phase B (#16575) ajoute éventuellement d'autres `LEDGERS`.
- **Fields autorisés** (rejet bruyant sinon) :
  - `state_class` enum `open-actionable | open-blocked | open-stale | deferred | closed | unknown`
  - `closeability` enum `closeable-now | closeable-after-followup | not-closeable | unknown`
  - `remaining_atomic_prs` int ≥ 0
  - `eat_hours` nombre ≥ 0
  - `dependencies` liste d'`{kind, repo?, number?, note?}` ou entier
  - `followup` object `{kind: issue, repo, number}` · `{kind: waiver, reason}` · `{kind: none}` · `null`
- **Pas dans `fields`** : `kind`, `audited_head_sha`, `verdict`. `head_sha` vit en `Record` au pliage (provenance) — pas dans l'envelope. Idempotence par `observation_id` content-derived.
- **Transport** : dashboard workspace dédié `CoursIA-issue-debt-ledger`. Observation = un message append-only `[OBS] {json}`. Snapshot = `status` du dashboard, écrit par ai-01 seul via `update`/`replace`. Le CLI **n'écrit jamais sur `$ROOSYNC_SHARED_PATH`** (la garde `assert_local_output` refuse sans override : `SHARED_PATH_REFUSED` ou `REPO_PATH_REFUSED`).
- **Préconditions** : (i) `git ls-tree -r origin/main | grep debt_ledger` rend du code → phase A mergée ; (ii) le dashboard `CoursIA-issue-debt-ledger` existe côté roosync. Tant qu'une manque : `ledger: N/A (phase A non mergée)` dans le rapport — pas de skip silencieux.
- **Outil** : `python scripts/coordination/debt_ledger.py init --state-dir <LOCALAPPDATA>\CoursIA\debt-ledgers --apply` (jamais sous `$ROOSYNC_SHARED_PATH` ou dans le repo).

### Forme CLI réelle

```bash
# Préparer l'envelope (dry-run par défaut) :
python scripts/coordination/debt_ledger.py append --ledger issue-debt \
  --entity 'jsboige/CoursIA#<N>' --actor myia-po-2025:CoursIA-2 \
  --observed-at 2026-09-18T12:00:00Z --confidence high \
  --evidence 'gh issue view N --json state,body' \
  --fields-json '{"state_class":"closed","closeability":"closeable-after-followup","remaining_atomic_prs":0,"eat_hours":0,"followup":{"kind":"issue","repo":"jsboige/CoursIA","number":16650}}' \
  --json

# Spool local facultatif (jamais dans le repo) :
  --out-dir <LOCALAPPDATA>\CoursIA\debt-ledgers\issue-debt\spool \
  # Imprimé en stderr :
  # post it with: roosync_dashboard(action:"append", type:"workspace",
  #   workspace:"CoursIA-issue-debt-ledger", content:"[OBS] {...}")

# Réduire (consomme le journal exporté en local) :
python scripts/coordination/debt_ledger.py reduce --ledger issue-debt \
  --events <journal-export.json> --state-dir <LOCALAPPDATA>\CoursIA\debt-ledgers
```

### Proposition B — arbitrage ai-01 c.31 (NON avec motif)

**L'arbitrage (B) rendu par ai-01 c.31 22:31Z est NON.** Motif : « Une information reconstituable au pliage n'est pas une information perdue, c'est une information moins commode. Ajouter un champ avant que le ledger ait servi une seule fois, c'est ajouter de la flexibilité dont on n'a pas encore besoin — et c'est un PR de plus sur le chemin critique de la décongèstion. »

**Comment faire changer d'avis** : utiliser le ledger 2 cycles, revenir avec la **mesure** (« sur N observations, j'ai dû rouvrir le pliage M fois pour retrouver le type »), pas une intuition. ai-01 écrira le champ lui-même le cas échéant. Une mesure, pas une intuition — et ce sera un oui.

La proposition `act_kind` est donc **mise en attente mesurée**, pas ajoutée au schéma. Le champ n'existe pas et reste à ne pas ajouter à la main.

### Erreurs déjà commises à ne pas reproduire

- **c.7** : cette section disait `--ledger pr-actions` + `kind` + `audited_head_sha` — drift silencieux. Le code aurait rejeté à chaque cycle avec `unknown_field`. Corrigé c.8 par lecture firsthand de `debt_ledger.py` ligne par ligne.
- **En c.6/c.7** : 33 `[ADJOINT CLOSE]` publiés sur GitHub n'ont **pas** été traduits en observations ledger valides (le CLI était absent de main, et la skill disait du faux). Backfill = geste ultérieur, après merge phase A — pas un skip silencieux.

## Émission de dossiers — garde-fous obligatoires (tells c.12-c.15)

- **Tie-break des runs jumeaux** : `group_by(.name)|map(max_by(.createdAt))` est **instable** quand deux runs d'un même workflow partagent le même `createdAt` (attempt 1 vs 2) — mesuré c.15 : lecture « tout vert » puis 3 rouges au re-jeu. Toujours `max_by(.databaseId)` (monotone).
- **Le gate en échec imprime sur STDOUT** : sans `--json`, l'échec de `check_adjoint_prevalidation.py` rend `UNKNOWN -- {erreur}` sur stdout — une redirection `--template > file.md` capture cette ligne comme template. Avant tout post : (1) rc=0 du template, (2) `head -1` du fichier = `[ADJOINT PREFLIGHT]`, (3) placeholders `REPLACE_WITH` présents dans le template source. `grep -c REPLACE_WITH = 0` est un **faux-OK** sur une ligne d'erreur.
- **Le gate ne lit pas l'état de merge** : un dossier READY exige la vérification `mergeable` côté attestant (CONFLICTING → BLOCKED conflit ; UNKNOWN → HOLD re-mesure).
- **Fenêtre rate-limited** : après un refus GraphQL (`rate limit already exceeded` avec buckets pleins = limite secondaire), le fallback REST `gh api repos/.../issues/N/comments -f body=...` passe — mais le template doit être **régénéré après** la fenêtre, jamais réutilisé.
- **Dossier posé EN DERNIER** : toute prose postée après le dossier le périmé (surfaces-sha256).

## Cron

Cadence expérimentale : un seul cron horaire session-only portant `/coordinate-adjoint`. Ne jamais armer `/coordinate`, `/continue` ou un `ScheduleWakeup` en parallèle pour ce slot. Vérifier avec `CronList` avant tout réarmement ; les crons expirent automatiquement après 7 jours.

## Référence

Ce fichier est le contrat durable du slot. La copie machine-level (`~/.claude/skills/coordinate-adjoint/`) reste la source opérationnelle du slot `myia-po-2025:CoursIA-2` ; en cas de divergence, la version la plus récente mergeée sur `main` fait foi. Le contexte de cycles vit dans la mémoire du workspace (`memory/coordinator-adjoint-role.md`, per-machine) et sur les dashboards — jamais dans ce fichier (harness-hygiene : la skill décrit le processus, pas l'état).
