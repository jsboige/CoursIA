# Ledger de dette `issue-debt`

Un registre append-only qui porte d'un cycle a l'autre ce que la flotte
rederivait en relisant dashboards, inbox et GitHub : la **dette d'issue** (ce
qu'une issue doit encore). Ce dossier contient l'**utilitaire** : schema,
reducteur, CLI, tests. Il ne connait ni GitHub ni RooSync et **n'ecrit jamais sur
le systeme de fichiers partage**.

## Transport — a lire avant de cabler quoi que ce soit

**Le transport partage n'est PAS un fichier partage.** `$ROOSYNC_SHARED_PATH` est
un montage Drive : pas de verrou, pas de compare-and-swap. Deux lanes qui
ecrivent le meme fichier font du *last-write-wins* — un ledger multi-ecrivain y
**perdrait silencieusement des observations**, exactement la perte que le ledger
existe pour empecher.

Le transport est **un dashboard workspace dedie**, `CoursIA-issue-debt-ledger`.
Une observation est **un message append-only** dont `content` est une ligne JSON
prefixee `[OBS] ` : jamais edite, donc le journal est append-only par
construction, et un `observation_id` stable (derive du contenu) rend un rejeu
*detectable* au lieu de nuisible. Le **snapshot** est ecrit par ai-01 **SEUL**,
dans la section `status`, via `update`/`replace` — jamais en `append` (un
snapshot est une valeur derivee, pas un evenement), jamais par un second
ecrivain. Les trois appels MCP prescrits (`append` d'une observation, `read` du
journal, `update` du `status` par ai-01 seul) sont imprimes par `init` et portes
par le `schema.json` genere sous `dashboard_calls` — jamais recopies a la main.

## Artefacts locaux (jamais dans le depot, jamais sous `$ROOSYNC_SHARED_PATH`)

`assert_local_output` **refuse** (fatal, sans override) **chaque chemin ecrit** —
le repertoire d'etat **et** `--out` / `--out-dir` / `--summary-out` /
`--status-out` — sous `$ROOSYNC_SHARED_PATH` (`SHARED_PATH_REFUSED`) et dans une
arborescence git (`REPO_PATH_REFUSED`). Garder le seul repertoire d'etat aurait
laisse les quatre flags de sortie comme porte de service sur le meme montage.

`init` cree `<etat>/config.json`, puis par ledger `baseline.json` (a la main),
`schema.json` (genere depuis le code), `spool/` (boite d'envoi facultative) et
`snapshots/{snapshot.json,summary.json,status.md}`.

## Schema d'une observation

```json
{"schema": "debt-ledger-observation/v1",
 "observation_id": "obs-<sha256 tronque du contenu>",
 "ledger": "issue-debt", "actor": "myia-po-2025:CoursIA-2",
 "observed_at": "2026-09-17T19:48:00Z", "confidence": "high",
 "evidence": "gh issue view 16563 --json state,body",
 "entity": {"repo": "jsboige/CoursIA", "issue": 16563},
 "fields": {"state_class": "open-actionable", "eat_hours": 4.5}}
```

- `observed_at` est **UTC explicite** : naif (`naive_timestamp`) ou decale
  (`non_utc_timestamp`) est refuse — une heure locale lisant comme de l'UTC
  reordonne le merge en silence.
- `actor`, `evidence` et `confidence` sont **obligatoires** : une observation sans
  provenance n'est pas une observation.
- les cles inconnues (racine comme `fields`) sont **refusees** (`unknown_key`,
  `unknown_field`) : une typo qui cree un champ fantome vaut pire qu'un refus
  bruyant, parce qu'il ne fusionne jamais avec le vrai et deux lanes lisent alors
  deux verites differentes.
- l'observation porte aussi `head_transition` (toujours `false` ici). La cle est
  **conservee volontairement** : l'`observation_id` derive du contenu entier, donc
  omettre une cle changerait l'identite de chaque observation le jour ou le
  ledger PR la lit. Une identite qui bouge n'est plus une identite.

### Champs

| Champ | Type | Sens |
|---|---|---|
| `state_class` | enum | `open-actionable` · `open-blocked` · `open-stale` · `deferred` · `closed` · `unknown` |
| `closeability` | enum | `closeable-now` · `closeable-after-followup` · `not-closeable` · `unknown` |
| `remaining_atomic_prs` | entier >= 0 | PRs atomiques restantes avant que l'issue soit vraiment finie |
| `eat_hours` | nombre >= 0 | heures de tache atomique (EAT) encore dues |
| `dependencies` | liste | entiers (`repo#N` implicite) ou `{kind: issue\|pr\|external, repo?, number?, note?}` |
| `followup` | objet ou `null` | `{kind: issue, repo, number}` ou `{kind: waiver, reason}` ou `{kind: none}` |

Une observation **partielle** est legitime : rien n'est obligatoire dans `fields`,
et l'incompletude se mesure (`summary.rows.incomplete`), elle ne provoque pas
d'erreur.

## Reduction

`reduce` plie trois sources sans **aucune precedence** : chacune contribue des
observations, et la fusion est **par champ** — la plus recente observation
admissible gagne, provenance et historique sont conserves.

1. la **baseline** (observations de depart, supersedables comme les autres) ;
2. le **snapshot precedent**, plie champ par champ avec la provenance d'origine —
   c'est ce qui rend le reducteur *archive-aware* : quand le dashboard condense et
   archive d'anciens messages, l'etat qu'ils portaient est deja plie ;
3. le **journal**, lu comme une liste **plate** de messages :
   `{"ledger": "issue-debt", "messages": [{"id": "m-0", "timestamp": "...",
   "content": "[OBS] {...}"}]}` (une liste nue est acceptee aussi).

Le contenu qui n'est pas une observation (le snapshot `status` d'ai-01, une note
humaine) est **ignore** et compte dans `summary.window.ignored` — refuser la
prose peindrait en rouge un ledger sain a chaque cycle.

Ce que cette forme **n'est pas** : un export `roosync_dashboard read` tel qu'il
sort du transport, qui imbrique son journal (`data.intercom.messages`) et
enveloppe l'auteur dans un objet (`{machineId, workspace}`). L'adaptateur de cette
enveloppe, la declaration d'encodage (`format`) et le contrat de couverture
(`window.full` / `window.incremental`, checkpoint obligatoire quand l'export est
une queue) arrivent **avec le transport partage** ; jusque-la un journal est un
**fichier local complet**, et le reducteur le traite comme tel.

## CLI

```bash
python scripts/coordination/debt_ledger.py init --state-dir <etat> --apply
python scripts/coordination/debt_ledger.py append --ledger issue-debt \
    --entity jsboige/CoursIA#16563 --actor myia-po-2025:CoursIA-2 \
    --evidence "gh issue view 16563" --confidence high \
    --fields-json '{"state_class":"open-actionable","eat_hours":4.5}'
python scripts/coordination/debt_ledger.py reduce --ledger issue-debt \
    --events <journal.json> --state-dir <etat>
```

`init` n'ecrit rien sans `--apply` (il cree de l'etat, donc c'est opt-in) ;
`append` imprime et n'ecrit rien sans `--out`/`--out-dir` (il ne *peut* pas ecrire
d'etat partage — poster est un appel MCP) ; `reduce` ecrit ses trois artefacts
sauf `--dry-run`/`--stdout`. Codes de sortie : `0` ok · `1` fatal (ou rejets avec
`--fail-on-rejections`) · `2` usage.

## Metriques et tests

Le resume porte l'EAT total et par `state_class`, `remaining_atomic_prs`,
`closeable_now` (les issues fermables en l'etat), les dependances (dont
externes) et le suivi des follow-ups (`issue` / `waiver` / `none` / `missing`).
Les tests (`python -m pytest scripts/tests/test_debt_ledger.py`) couvrent les
proprietes dont chacune est un mode d'echec reel : observations concurrentes
distinctes, idempotence (re-append et re-pliage), schema invalide refuse avec sa
raison, metriques EAT, suivi des follow-ups, atomicite et verrouillage des
ecritures locales.

## Organe `merge_ready` (Q40, 2026-09-22)

Fusion hors cycle coordinateur : un organe deterministe (identite myia-ai-01,
cadence ~20 min) qui merge UNIQUEMENT ce qui passe exactement les controles du
coordinateur lui-meme, en perimetre (b) uniquement -- hors harnais (`.claude/`,
`CLAUDE.md` a tout niveau, `.github/`) et hors grains `DEEP`. Motivation
mesuree : 97 merges en 24 h sur 4 creneaux, 12 heures vides, lead time median
28,5 h ; un dossier d'adjoint perit en attendant le cycle.

Par PR (la plus ancienne d'abord), TOUT doit tenir sinon skip avec raison
nommee au journal : pas un brouillon + un commentaire `[ADJOINT PREFLIGHT]`
(prefiltre), perimetre fail-closed (liste de fichiers complete -- `changedFiles`
superieur aux fichiers listes = skip -- et tier du tag `Grain:` lu par le parseur
partage `scripts/grain_tag.py`), pre-controle bon marche du dernier dossier
(tete perimee ou `b0:` non clear = skip sans payer le gate ; illisible = decision
laissee au gate), gate `check_adjoint_prevalidation.py` a
`ready: true`, champ `b0:` du dossier accepte relu via la grammaire du gate
(`parse_dossier` importe), organe B.0 `check_unaddressed_nits.py` a exit 0,
`mergeable_state` REST a `clean` (retry sur `unknown` -- apres un merge les
soeurs passent `unknown`) et tete identique a celle evaluee, puis
`gh pr merge --squash --match-head-commit <sha>` (jamais `--delete-branch`,
jamais `--admin`).

DRY-RUN par defaut (`--apply` pour merger), `--max N` disjoncteur (defaut 15),
arret sur la premiere erreur inattendue (rc d'un outil hors codes documents),
`GH_TOKEN` epingle depuis `gh auth token --user myia-ai-01` resolu une fois
(jamais `gh auth switch`). Journal : une ligne JSON par PR evaluee dans
`%LOCALAPPDATA%\CoursIA\merge_ready\journal.jsonl`. Codes de sortie : 0
termine, 1 arret sur erreur inattendue, 2 impossible de demarrer.

Cablage local : `install_merge_ready_task.py --dry-run` imprime la commande
schtasks exacte (discipline UAC : la sortie precede toute inscription), puis
`--install` -- tache toutes les 20 minutes qui lance l'organe en `--apply`
depuis un worktree DEDIE sur `main` (defaut `D:/CoursIA-wt-merge-ready`),
ramene sur `origin/main` avant chaque tour ; un tour est refuse si ce depot
n'est pas sur `main` ou porte des modifications suivies
(journaux sous `%LOCALAPPDATA%\CoursIA\merge_ready\logs\`). Tests hermetiques :
`python -m pytest scripts/tests/test_merge_ready.py
scripts/tests/test_install_merge_ready_task.py`.
