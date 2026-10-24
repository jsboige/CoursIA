# Convention `_archive/` — modèle ML-Training-Pipeline généralisé

**S'applique à :** tout dossier `_archive/` du dépôt. Le recensement est une **mesure**, pas un littéral : il se recalcule avec la commande du §« Recenser, ne pas recopier ».
**Référence :** `MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/scripts/_archive/` (consolidation #1409, 2026-06-12).
**Discipline parente :** CLAUDE.md global — « Consolider != Archiver » (préserver avant de réduire, citer la cible comme preuve).

## Pourquoi un standard

Un dossier `_archive/` sans convention devient un **puits de code mort** : on y dépose des scripts superseded, mais sans en-tête de disposition, personne ne sait s'ils sont **encore vivants mal étiquettés** ou **réellement abandonnés**. Le bilan mesuré sur le dépôt en 2026-08 :

- Les emplacements `_archive/` sont dispersés dans le dépôt (11 emplacements et 125 fichiers mesurés en 2026-08), avec des conventions hétérogènes. Ce chiffre est **daté** ; le compte courant se recalcule, il ne se recopie pas (voir le §« Recenser, ne pas recopier »).
- `scripts/genai-stack/_archive/` (constat empirique au 2026-08) : le plus gros stock du dépôt — code mort, certains cassés auto-admis. **Tranche 3 livrée le 2026-10-04** (cf table ci-dessous).
- `scripts/_archive/one_shot_fixes/` + `one_shots_post_463/` + `recycle_csp/` (constat empirique au 2026-08) : ~30 fichiers dont les README de disposition n'appliquaient pas encore tous le standard. **Cible de la tranche 2** (cf table du §« Application — les emplacements recensés »).

Le coût d'un `_archive/` non standardisé = **découverte impossible** : aucun successeur nommé, aucun verdict enregistré, aucun moyen de savoir si le script peut être ressuscité ou doit être supprimé.

## Standard — 4 critères

### 1. README obligatoire dans chaque `_archive/`

Le README liste **chaque fichier archivé** dans une table à 4 colonnes :

| Script | Verdict | Superseded by | Verdict recorded in |
|--------|---------|---------------|---------------------|
| `exemple.py` | NO BEATS (X/Y combos) | `chemin/successeur.py` (PR #1234) | `docs/RECAP_…`, PR #1234, `README.md` ladder |

Colonnes :

- **Script** : nom du fichier archivé.
- **Verdict** : verdict synthétique daté (NO BEATS / OBSOLETE / INTRINSIC / etc.).
- **Superseded by** : chemin du script successeur OU « none — closed dead-end » OU « abandonné : raison ».
- **Verdict recorded in** : référence durable au verdict (PR mergée, `docs/RECAP_*.md`, `results/*/verdict.md`, etc.).

### 2. Header de disposition per-function (chaque fichier `.py`)

Chaque fichier archivé porte **en tête** (sous le shebang/docstring d'usage) :

```python
# Archive header (standard _archive convention, 2026-08)
# - Date archived : YYYY-MM-DD
# - Superseded by : <chemin/successeur.py> | none (closed dead-end)
# - Verdict recorded in : <PR #N> | <docs/RECAP_*.md> | <results/*/verdict.md>
#
# Per-function disposition :
# - func_a() : moved to successeur.func_a (PR #N)
# - func_b() : abandoned — <raison> (verified YYYY-MM-DD)
# - func_c() : kept as reference; no successor
```

Le **per-function** est ce qui rend la traçabilité honnête : un script archivé peut avoir une fonction ressuscitée et une autre abandonnée — le dire explicitement évite la fausse équivalence « tout est mort ».

### 3. Critères d'éligibilité (4 critères obligatoires avant archivage)

Un script ne va **dans `_archive/`** que si les 4 critères sont vérifiés :

1. **NO BEATS verdict enregistré durablement** (PR mergée + body, `docs/RECAP_*.md`, `README.md` ladder table, ou archive header si `results/` gitignored).
2. **Zéro référence** depuis `docs/*.md`, `README.md`, `REGISTRY.md` (ou documentation explicite de la dépréciation).
3. **Zéro import** depuis un autre script en `scripts/` (vérifié par grep).
4. **Successeur existe** (PR mergée OU ligne de travail explicitement fermée avec raison).

Un script qui ne satisfait pas les 4 critères **ne va pas dans `_archive/`** — il reste en `scripts/` jusqu'à décision explicite, ou il est supprimé.

### 4. Pas d'unification en `docs/archive/code/`

**Garder les `_archive/` près de leur domaine.** Les scripts archivés référencent des chemins relatifs (`Path(__file__).parent / ...`) — unifier briserait leur capacité à être ressuscités sans réécriture. Le standard uniformise la **convention** (README + headers), pas la **localisation**.

Exception : si un dossier `_archive/` ne contient que des **données** (pas de scripts) — par exemple `_output.ipynb` sans sources — il peut être centralisé après vérif `execution_count`/consommateurs (cf cas `DSA AgenticDataScience/` + `PythonAgentsForDataScience/` signalés dans #13749 body).

## Recenser, ne pas recopier

Un compte d'emplacements écrit dans la prose périme sans que personne ne le remarque : il est vrai le jour où il est écrit, puis il se propage — une review ne peut ni le confirmer ni le contredire sans recompter. Le recensement se **recalcule** donc, il ne se recopie pas. Deux commandes, qui ne mesurent **pas la même chose** et ne doivent donc **pas** concorder :

```bash
# emplacements : repertoires dont le nom finit par `_archive`
git ls-tree -r -d --name-only origin/main | grep '/_archive$' | wc -l
# fichiers archives sous ces emplacements
git ls-tree -r --name-only origin/main | grep '/_archive/' | wc -l
```

Valeurs de référence au **2026-10-24** sur `origin/main` : **17** emplacements et **163** fichiers. Un emplacement contient plusieurs fichiers, donc comparer les deux totaux n'a pas de sens — et un écart entre eux n'est pas un défaut. Le prédicat de la première commande est `/_archive$`, pas `/_archive` : ce dernier rend **30**, parce qu'il compte aussi les sous-dossiers internes aux archives (`scripts/_archive/one_shot_fixes/`, `Argument_Analysis/_archive/…`) et les six répertoires de `docker-configurations/_archive-20251125/`, dont le nom ne finit pas par `_archive`.

**Cette règle est déclarative** : aucun organe ne vérifie ce prédicat en CI — ni la liste des emplacements, ni la concordance de la table avec `main`. Elle vit dans la relecture et dans les commandes ci-dessus ; la porter en gate serait une tranche à part, pas un effet de bord de cette page.

Une phrase de prose qui cite un total doit porter **sa date**. Une règle, une docstring d'organe ou un pointeur de documentation qui en cite un **sans date** est un défaut de prose quantitative : il se remplace par la commande, jamais par un chiffre plus récent.

## Application — les emplacements recensés

État au **2026-10-24** : **17** emplacements, **163** fichiers. Ce qui a changé
depuis le recensement de 2026-08 : `GenAI/Audio`, `docker-configurations` et
`notebook_tools` n'y figuraient pas. Depuis celui du 2026-10-04, trois
emplacements existaient sur `main` sans ligne dans la table —
`SymbolicAI/Argument_Analysis/_archive/`, `SymbolicAI/SmartContracts/_archive/`
et `scripts/smartcontracts/_archive/` — et y sont ajoutés ci-dessous, **non
audités** : la ligne dit qu'ils existent, pas qu'ils sont conformes.
La table ci-dessous est l'inventaire courant — chaque tranche de l'umbrella en
déplace une ligne, elle ne réécrit pas un total :

| Emplacement | README | Standard complet |
|---|---|---|
| `MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/scripts/_archive/` | ✅ | ✅ (modèle) |
| `MyIA.AI.Notebooks/GenAI/Audio/_archive/` | ✅ | ✅ (registre README, disposition **par section** — modèle `Planners/` ; tranche #13749 du 2026-09-25) |
| `MyIA.AI.Notebooks/Search/_archive/` | ✅ | partiel (registre sans en-tête de disposition par notebook) |
| `MyIA.AI.Notebooks/SymbolicAI/_archive/` | ✅ | partiel (registre sans en-tête de disposition pour le notebook) |
| `MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/_archive/` | ✅ | non audité (recensé le 2026-10-24) |
| `MyIA.AI.Notebooks/SymbolicAI/SmartContracts/_archive/` | ❌ | non audité (recensé le 2026-10-24 ; ne contient qu'un `STATUS-audit-consolidation-2026-05-26.md`) |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/scripts/_archive/` | ✅ | ✅ (registre — une ligne par script archivé) |
| `MyIA.AI.Notebooks/SymbolicAI/Planners/_archive/` | ✅ | ✅ (registre README, disposition **par section**) |
| `MyIA.AI.Notebooks/SymbolicAI/SymbolicLearning/_archive/` | ✅ | ✅ (registre de disposition au niveau `_archive/` ajouté le 2026-09-25 — tranche #13749 ; il pointe le README du lot daté `2026-07-04-Neurosymbolic-EML-precurseur-SL12/`, qui porte l'analyse) |
| `MyIA.AI.Notebooks/SymbolicAI/Tweety/scripts/_archive/` | ✅ | ✅ (tranche #13749 du 2026-09-25 : registre + en-tête de disposition ajouté à `reorganize_tweety.py`) |
| `scripts/_archive/` | ✅ | ✅ (registre parent ajouté le 2026-09-25 — tranche #13749 ; il indexe `c8257-lean18-enrichment/`, `one_shot_fixes/`, `one_shots_post_463/` et `recycle_csp/`. La ligne précédente marquait `✅` sur les seules sous-archives de #9535 et ne citait pas `c8257-lean18-enrichment/`, archivée plus tard par #14251) |
| `scripts/genai-stack/_archive/` | ✅ | ✅ (tranche #13749 du 2026-10-04 — lane `myia-po-2027:CoursIA-2` : registre 4 colonnes dans `ARCHIVE_README.md`, nom historique **préservé** car les en-têtes per-fichier et le README parent pointent dessus ; en-têtes de disposition standard ajoutés aux `.ps1` ; les `.py` gardent leurs en-têtes hérités format court, qui nomment successeur + registre) |
| `scripts/notebook_tools/_archive/` | ✅ | partiel (registre sans en-tête de disposition pour le script) |
| `scripts/smartcontracts/_archive/` | ✅ | non audité (recensé le 2026-10-24) |
| `scripts/sudoku/_archive/` | ✅ | ✅ (tranche #13749 du 2026-09-25 : registre 4 colonnes ; les en-têtes per-fichier existaient déjà) |
| `scripts/tests/_archive/` | ✅ | ✅ (tranche #13749 du 2026-10-04 : registre ajouté ; l'en-tête standard existait déjà sur `test_convert_print_to_deploy.py`, palier 1 #18153) |
| `slides/S4-trading-algorithmique/_archive/` | ✅ | ✅ (registre — une ligne par fichier archivé) |
| `docker-configurations/_archive-20251125/` | ✅ | non audité |

**Plan d'application** : tranches ciblées successives (cf umbrella #13749), une PR par tranche, dans les seuils d'anti-composite de la [§A du review](../../.claude/rules/pr-review-discipline.md) (cf G.4).

## Cas particuliers

- **`_archive/utils/reconstruct_env.py`** (genai-stack) : audit fait le 2026-10-04 (tranche #13749) — le sujet **est couvert** par le CLI (`genai.py auth reconstruct-env`, câblé `commands/auth.py` → `core/auth_manager.py::reconstruct_env_file`) : du mort correctement étiqueté, pas du vivant mal étiqueté.
- **`DSA AgenticDataScience/` + `PythonAgentsForDataScience/`** : dossiers ne contenant QUE des `*_output.ipynb` (sources migrées Track1/Track2) → supprimer après vérif `execution_count`/consommateurs (fantômes). Tranche séparée, hors #13749.
- **Scripts archive sans successeur** : la ligne de travail doit être **explicitement fermée** dans le PR d'archivage (raison + lien vers la discussion de clôture). Sans cette fermeture, le script n'est pas archivable — il est juste mort.

## Pourquoi cette convention

Un `_archive/` standardisé n'est **pas** une poubelle : c'est un **registre de décisions**. Chaque ligne dit « ce code a été supplanté par X, voici où c'est documenté ». Le futur agent (humain ou bot) qui rouvre le dépôt dans 6 mois peut alors :

- Savoir si le script peut être ressuscité (successor nommé).
- Savoir pourquoi il a été archivé (verdict daté).
- Savoir où trouver la preuve du verdict (référence durable).
- Savoir ce que chaque fonction est devenue (per-function disposition).

C'est l'application directe de « Consolider != Archiver » : **préserver avant de réduire**, citer la cible comme preuve, ne jamais déplacer vers `_archives/` sans preuve de préservation.

## Voir aussi

- CLAUDE.md global — « Consolider != Archiver »
- Umbrella #13749 — Convention `_archive/` unifiée sur le modèle ML-Training-Pipeline (V3)
- Issue #1409 — consolidation modèle ML-Training-Pipeline
- Issue #9535 — campagne rename `archive/` → `_archive/` (2026-08, V1)