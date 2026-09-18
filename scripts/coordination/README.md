# Ledgers de dette partages (`issue-debt`, `pr-actions`)

Deux registres append-only qui portent, d'un cycle a l'autre, ce que la flotte
rederivait jusqu'ici en relisant dashboards, inbox et GitHub : la **dette
d'issue** (ce qu'une issue doit encore) et **l'action de PR** (ce qu'une PR
attend).

Ce dossier contient l'**utilitaire generique** : schemas, reducteur, CLI, tests.
Il ne connait ni GitHub ni RooSync et **n'ecrit jamais sur le systeme de
fichiers partage**.

## Transport — a lire avant de cabler quoi que ce soit

**Le transport partage n'est PAS un fichier partage.** `$ROOSYNC_SHARED_PATH` est
un montage Drive : pas de verrou, pas de compare-and-swap. Deux lanes qui
ecrivent le meme fichier font du *last-write-wins* — un ledger multi-ecrivain y
**perdrait silencieusement des observations**, exactement la perte que le ledger
existe pour empecher.

Le transport est **deux dashboards workspace dedies**, un par nature :

| Ledger | Dashboard | Qui ecrit quoi |
|---|---|---|
| `issue-debt` | `CoursIA-issue-debt-ledger` | adjoint + bots : `append` d'observations |
| `pr-actions` | `CoursIA-pr-action-ledger` | adjoint + Hermes + NanoClaw : `append` d'observations |

- **Une observation = un message append-only.** `content` est une ligne JSON
  prefixee `[OBS] `. Le message n'est jamais edite : le journal est
  append-only par construction, et un `observation_id` stable (derive du
  contenu) rend un rejeu *detectable* au lieu de nuisible.
- **Le snapshot est ecrit par ai-01 SEUL**, dans la section `status` du dashboard
  du ledger, via `update`/`replace` — jamais en `append` (un snapshot est une
  valeur derivee, pas un evenement), jamais par un second ecrivain.

Appels MCP (forme prescrite, avec `workspace:` explicite — ces dashboards ne sont
pas celui de la lane courante) :

```
roosync_dashboard(action:"append", type:"workspace", workspace:"CoursIA-issue-debt-ledger",
                  content:"[OBS] {\"schema\":\"debt-ledger-observation/v1\", ...}")
roosync_dashboard(action:"read",   type:"workspace", workspace:"CoursIA-issue-debt-ledger",
                  section:"all")
roosync_dashboard(action:"update", type:"workspace", workspace:"CoursIA-issue-debt-ledger",
                  section:"status", content:"<snapshots/status.md>")   # ai-01 UNIQUEMENT
```

`init` imprime ces appels pour chacun des deux ledgers (le `schema.json` genere
les porte aussi sous `dashboard_calls`).

## Artefacts locaux (jamais dans le depot, jamais sous `$ROOSYNC_SHARED_PATH`)

Le reducteur et la CLI n'ecrivent que des artefacts **locaux**, sous un
repertoire d'etat local (`%LOCALAPPDATA%/CoursIA/debt-ledgers`, ou
`$COURSIA_LEDGER_STATE_DIR`, ou `--state-dir`) :

```
<etat>/config.json                          reglages + table ledger -> dashboard
<etat>/<ledger>/baseline.json               observations de depart, ecrites a la main
<etat>/<ledger>/schema.json                 contrat genere DEPUIS le code
<etat>/<ledger>/spool/<obs_id>.json         boite d'envoi locale (facultative)
<etat>/<ledger>/snapshots/snapshot.json     l'etat complet (provenance + historique)
<etat>/<ledger>/snapshots/summary.json      les metriques agregees
<etat>/<ledger>/snapshots/status.md         le texte compact que ai-01 poste
```

`assert_local_output` **refuse** (erreur fatale, sans override) **chaque chemin
ecrit** — le repertoire d'etat **et** `--out` / `--out-dir` / `--summary-out` /
`--status-out` — dans deux cas : sous `$ROOSYNC_SHARED_PATH`
(`SHARED_PATH_REFUSED`) et dans une arborescence git (`REPO_PATH_REFUSED`, la
sortie d'un ledger n'est pas du contenu de depot). Garder le seul repertoire
d'etat aurait laisse les quatre flags de sortie comme porte de service sur le
meme montage.

## Schema d'une observation

```json
{
  "schema": "debt-ledger-observation/v1",
  "observation_id": "obs-<sha256 tronque du contenu>",
  "ledger": "pr-actions",
  "actor": "myia-po-2025:CoursIA-2",
  "observed_at": "2026-09-17T19:48:00Z",
  "confidence": "high",
  "evidence": "gh pr view 16001 --json headRefOid,reviews",
  "entity": {"repo": "jsboige/CoursIA", "pr": 16001, "head_sha": "<40 hex>"},
  "head_transition": false,
  "fields": {"action_class": "review-ready", "review_required": true}
}
```

Regles dures :

- `observed_at` est **UTC explicite**. Un horodatage naif est refuse
  (`naive_timestamp`), un decalage non-UTC aussi (`non_utc_timestamp`) : une
  heure locale lisant comme de l'UTC reordonne le merge en silence.
- `actor`, `evidence` et `confidence` sont **obligatoires** : une observation sans
  provenance n'est pas une observation.
- les cles inconnues (au niveau racine comme dans `fields`) sont **refusees**
  (`unknown_key`, `unknown_field`) : une typo qui cree un champ fantome vaut
  pire qu'un refus bruyant, parce que le champ fantome ne fusionne jamais avec le
  vrai et deux lanes lisent alors deux verites differentes.
- `head_sha` est le SHA **complet** (40 hex). Une forme abregée est refusee
  (`short_head_sha`) : elle creerait une transition de tete fantome.

### Champs — `issue-debt`

| Champ | Type | Sens |
|---|---|---|
| `state_class` | enum | `open-actionable` · `open-blocked` · `open-stale` · `deferred` · `closed` · `unknown` |
| `closeability` | enum | `closeable-now` · `closeable-after-followup` · `not-closeable` · `unknown` |
| `remaining_atomic_prs` | entier >= 0 | PRs atomiques restantes avant que l'issue soit vraiment finie |
| `eat_hours` | nombre >= 0 | heures de tache atomique (EAT) encore dues |
| `dependencies` | liste | entiers (`repo#N` implicite) ou `{kind: issue\|pr\|external, repo?, number?, note?}` |
| `followup` | objet ou `null` | `{kind: issue, repo, number}` ou `{kind: waiver, reason}` ou `{kind: none}` |

### Champs — `pr-actions`

`head_bound` = le champ decrit les surfaces d'UN commit : il est **refuse** s'il
provient d'une observation prise contre une tete de PR deja remplacee.

| Champ | Type | `head_bound` | Sens |
|---|---|---|---|
| `action_class` | enum | non | `ready-to-merge` · `review-ready` · `needs-review` · `needs-repair` · `blocked-on-ci` · `blocked-on-author` · `blocked-on-reserve` · `merged` · `closed` · `unknown` |
| `review_required` | bool | non | une review est-elle encore due |
| `reviewer` | texte | non | lane ou bot attendu (adjoint, Hermes, NanoClaw, ai-01) |
| `producer` | texte | non | lane productrice |
| `live_reserves` | liste | **oui** | reserves ouvertes sur la tete COURANTE (chaine nue ou `{summary, url?, author?}`) |
| `live_checks` | objet | **oui** | nom de check -> statut |
| `update_branch_status` | enum | **oui** | `up-to-date` · `behind` · `update-required` · `unknown` |
| `dossier_status` | enum | **oui** | `absent` · `requested` · `ready` · `stale` · `invalid` |
| `next_action` | texte | **oui** | le geste unique que la lane doit |

Une observation **partielle** est legitime : rien n'est obligatoire dans
`fields`, et l'incompletude se mesure (`summary.rows.incomplete`), elle ne
provoque pas d'erreur. Une mise a jour ne touche donc qu'un champ a la fois.

## Reduction

`reduce` plie trois sources ; il n'y a **aucune precedence de source** : chacune
contribue des observations, et la regle de fusion est **par champ** — la plus
recente observation admissible gagne, provenance et historique sont conserves.

1. la **baseline** (observations de depart, supersedables comme les autres) ;
2. le **snapshot precedent**, plie champ par champ avec la provenance d'origine —
   c'est ce qui rend le reducteur *archive-aware* : quand le dashboard condense
   et archive d'anciens messages, l'etat qu'ils portaient est deja plie ;
3. le **journal exporte** (`roosync_dashboard read`) avec sa declaration de
   `window`.

### Lit l'export du producteur, pas une forme inventee

Un `roosync_dashboard read` rend une **enveloppe** (`data.intercom.messages`) et
des messages de la forme reelle
`{id, timestamp, author: {machineId, workspace}, content}`. L'adaptateur descend
l'enveloppe (profondeur 3) et normalise l'auteur en lane `machineId:workspace`
(la cle machine est **`machineId`**, pas `machine` ; `machine_id`, `machine` et
`host` sont acceptes en repli) : un lecteur qui ne regarde qu'au premier niveau
voit « pas de messages » sur un export sain et refuse tout le journal, et un
lecteur qui ne cherche que `machine` refuse **chaque** observation reelle avec
`missing_actor`.

Deux categories de messages, a ne pas confondre :

- une observation (`[OBS]`) qui ne parse pas est un **rejet** avec sa raison —
  un producteur qui ment sur son propre format est un defaut ;
- le reste du contenu du dashboard (le snapshot `status` d'ai-01, une note
  humaine) est **ignore** et compte dans `window.ignored` — refuser la prose
  peindrait en rouge un ledger sain a chaque cycle.

L'encodage est declare (`format: "json"` dans le descripteur d'`append`) et
verifie (`UNSUPPORTED_EXPORT_FORMAT`) : une enveloppe d'un autre format ne peut
pas etre lue de travers en silence.

### Contrat de checkpoint (archive-aware)

Un export **declare** ce qu'il couvre :

```json
{"window": {"kind": "full" | "incremental", "archives": ["..."]}}
```

- `full` : l'export pretend contenir tout le journal — snapshot precedent
  facultatif.
- `incremental` : export de queue (cas nominal une fois le dashboard condense) —
  **le snapshot precedent est obligatoire**.
- **absent** : traite comme `incremental`. Fail-closed : un export qui ne dit pas
  ce qu'il couvre ne sert pas a reconstruire un etat a partir de rien.

Plier un export incremental sans checkpoint leve `MISSING_CHECKPOINT` au lieu de
produire en silence un snapshot bati sur la seule queue. Un export plus **vieux**
que le checkpoint n'est pas fatal (ses observations perdent sur `observed_at`)
mais il est signale (`export_older_than_checkpoint`) : un export perime ne doit
jamais faire regresser l'etat.

### Regle de tete (PR)

Les tetes sont ordonnees par `observed_at`. Une observation qui declare une tete
**deja remplacee** ne peut pas ramener la tete en arriere, et ses champs
`head_bound` sont refuses — elle est consignee `stale_head` dans l'historique.
Les champs non `head_bound` s'appliquent quand meme (ils decrivent la PR, pas un
commit). Un retour en arriere reel (force-push) se declare explicitement avec
`head_transition: true` et se compte (`head.head_regressions`).

Un enregistrement plie depuis le checkpoint est une **observation, jamais une
declaration** : sans cette distinction, une tete deja refusee reviendrait comme
un force-push declare a chaque re-pliage, et le ledger deriverait vers la vue
perimee au lieu de tenir le refus. Le compteur
`head.stale_head_observations` compte des **observations** (par
`observation_id`), pas des champs : une observation portant trois champs
`head_bound` reste une observation perimee.

## CLI

```bash
# 1. creer l'arbre local (dry-run par defaut ; --apply pour ecrire)
python scripts/coordination/debt_ledger.py init --state-dir <etat> --apply

# 2. fabriquer une observation, imprimer l'appel MCP a poster (n'ecrit rien de partage)
python scripts/coordination/debt_ledger.py append --ledger pr-actions \
    --entity jsboige/CoursIA#16001 --head-sha <40 hex> --actor myia-po-2025:CoursIA-2 \
    --evidence "gh pr view 16001" --confidence high \
    --fields-json '{"action_class":"review-ready","review_required":true}'
#    -> ajouter --out-dir <etat>/pr-actions/spool pour garder une boite d'envoi locale

# 3. plier (le snapshot precedent est repris automatiquement comme checkpoint)
python scripts/coordination/debt_ledger.py reduce --ledger pr-actions \
    --events <export.json> --state-dir <etat>
```

Defauts de dry-run : `init` n'ecrit rien sans `--apply` (il cree de l'etat, donc
c'est opt-in) ; `append` imprime et n'ecrit rien sans `--out`/`--out-dir` (il ne
*peut* pas ecrire d'etat partage — poster est un appel MCP) ; `reduce` ecrit ses
trois artefacts sauf `--dry-run`/`--stdout`.

`--window-full` declare complet un export qui ne dit rien de sa couverture —
y compris une **liste nue** de messages (la forme la plus naturelle a la main).
Un export qui declare explicitement `incremental` n'est **jamais** converti :
le flag sert aux exports muets, pas a contredire un fait.

Codes de sortie : `0` ok · `1` fatal (ou rejets avec `--fail-on-rejections`) ·
`2` usage.

## Metriques du resume

- `issue-debt` : EAT total et par `state_class`, `remaining_atomic_prs`,
  `closeable_now` (les issues fermables en l'etat), dependances (dont externes),
  suivi des follow-ups (`issue` / `waiver` / `none` / `missing`).
- `pr-actions` : `action_class`, review due/par reviewer/par producteur, reserves
  vivantes, checks en echec, `update_branch_status`, `dossier_status`,
  `review_ready` (la file a deleguer), observations `stale_head`.

## Tests

```bash
python -m pytest scripts/tests/test_debt_ledger.py
```

Ils couvrent les proprietes dont chacune est un mode d'echec reel de la flotte :
observations concurrentes distinctes, tete perimee qui n'ecrase pas la tete
courante, idempotence (re-append et re-pliage), schema invalide refuse avec sa
raison, metriques PR/EAT, suivi des follow-ups, contrats d'archive et de
verrouillage/atomicite des ecritures locales.
