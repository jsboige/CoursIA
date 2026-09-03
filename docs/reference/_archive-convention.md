# Convention `_archive/` — modèle ML-Training-Pipeline généralisé

**S'applique à :** tout dossier `_archive/` du dépôt (11 emplacements recensés en 2026-08).
**Référence :** `MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/scripts/_archive/` (consolidation #1409, 2026-06-12).
**Discipline parente :** CLAUDE.md global — « Consolider != Archiver » (préserver avant de réduire, citer la cible comme preuve).

## Pourquoi un standard

Un dossier `_archive/` sans convention devient un **puits de code mort** : on y dépose des scripts superseded, mais sans en-tête de disposition, personne ne sait s'ils sont **encore vivants mal étiquettés** ou **réellement abandonnés**. Le bilan mesuré sur le dépôt en 2026-08 :

- 11 emplacements `_archive/` dispersés (125 fichiers au total au 2026-08), conventions hétérogènes.
- `scripts/genai-stack/_archive/` (constat empirique au 2026-08, **hors scope PR actuelle**) : 28 fichiers (37 % du répertoire) — code mort, certains cassés auto-admis. **Cible de la tranche 3** (cf table lignes 73-85).
- `scripts/_archive/one_shot_fixes/` + `one_shots_post_463/` + `recycle_csp/` (constat empirique au 2026-08, **hors scope PR actuelle**) : ~30 fichiers sans README de disposition. **Cible de la tranche 2** (cf table lignes 73-85).

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

## Application — 11 emplacements, 8 restants à standardiser

État au 2026-08-31 :

| Emplacement | README | Standard complet |
|---|---|---|
| `MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/scripts/_archive/` | ✅ | ✅ (modèle) |
| `MyIA.AI.Notebooks/Search/_archive/` | ✅ | partiel (1 fichier) |
| `MyIA.AI.Notebooks/SymbolicAI/_archive/` | ✅ | partiel (1 fichier) |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/scripts/_archive/` | ❌ | tranche 4 |
| `MyIA.AI.Notebooks/SymbolicAI/Planners/_archive/` | ❌ | tranche 4 |
| `MyIA.AI.Notebooks/SymbolicAI/SymbolicLearning/_archive/` | ❌ | tranche 4 |
| `MyIA.AI.Notebooks/SymbolicAI/Tweety/scripts/_archive/` | ❌ | tranche 4 |
| `scripts/_archive/` | partiel | tranche 2A : `one_shots_post_463/` conforme ; `one_shot_fixes/` et `recycle_csp/` restent à standardiser |
| `scripts/genai-stack/_archive/` | ❌ | tranche 3 (28 fichiers constatés au 2026-08, peut nécessiter split) — **hors scope PR actuelle** |
| `scripts/sudoku/_archive/` | ❌ | tranche 4 |
| `slides/S4-trading-algorithmique/_archive/` | ❌ | tranche 4 |

**Plan d'application** : tranches ciblées successives (cf umbrella #13749), une PR par tranche, seuils < 3000 lignes / < 15 fichiers / ≤ 4 features / 1 domaine (Tell c.692-L1 strict anti-composite + G.4 PR-review A).

## Cas particuliers

- **`_archive/utils/reconstruct_env.py`** (genai-stack, 17,6 KLOC récent) : vérifier si le sujet est couvert par la feature CLI avant d'archiver — peut être du vivant mal étiquetté. Tranche 3 fait l'audit.
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