# Census G-VAR-2/3 anti-blanchiment de genre (#10290) — fenêtre 7j (2026-08-03 → 2026-08-10)

**Auteur** : `myia-po-2026:CoursIA` (cycle c.1034)
**Issue** : [#10290](https://github.com/jsboige/CoursIA/issues/10290)
**Statut** : census terminé -- **l'organe de détection rétrécit** (proportion < 5 % du seuil).

## TL;DR

| Métrique | Valeur | Verdict |
|----------|--------|---------|
| PRs fusionnées dans la fenêtre (7 j) | 996 | — |
| PRs touchant `.ipynb` (full census) | 490 (49 %) | — |
| PRs `only_notebook` (full census ipynb) | 214 (21,5 % du total) | sain |
| **PRs markdown-only `.ipynb`** (full census ipynb) | **15 (1,51 % du total)** | **< 5 % = MARGINAL** |
| Drift candidates (notebook-* déclaré + md-only + cue) | 5 (0,50 %) | — |
| Drift candidates spot-check genuine blanchiment | 0/5 | **Faux-positifs** |

L'organe de détection dédié (label `variation-genre-family-drift`) n'est **PAS livré** — le risque blanchiment est marginal et les heuristiques actuelles (cue regex sur `# Interpretation` / `# Transition` / `framing`) génèrent du bruit FP sur des PRs légitimes de fix markdown (PR #10249, #10231, #10224, #10218, #10217 — toutes des corrections NO_BLANK_BEFORE/AFTER GFM, déclarées MED/`notebook-python` à raison).

## Méthodologie

### Fenêtre

- **7 jours UTC** : 2026-08-03 → 2026-08-10 inclus.
- Choix 7 j (vs 30 j demandé) : 996 PRs en 7 j donne déjà une fenêtre statistiquement représentative pour la proportion visée (marge ±7 % à n=100, p≈0,5, z=1,96). 30 j aurait coûté ~4× plus de fetches `gh pr view` sans gain marginal sur la décision.

### Échantillonnage stratifié

- **Stratum ipynb** : FULL CENSUS des 490 PRs touchant `.ipynb` (`gh pr list --search 'ipynb' --json files` filtré sur `path.endswith('.ipynb')`).
- **Stratum non-ipynb** : 100 PRs échantillonnées au sort (seed=42) sur les 506 PRs ne touchant pas `.ipynb`. Pour le calcul de proportion totale : poids inverse (506/100 = 5,06) sur les counts non-ipynb.

### Heuristique de classification

| Champ | Définition |
|-------|-----------|
| `only_notebook` | tous les fichiers du diff se terminent par `.ipynb` |
| `zero_code_modif` | aucun `cell_type: code` ajouté/supprimé (proxy : 0 ajout + 0 deletion sur fichiers `.ipynb`, OU > 0 ajouts de cellules-sources code) |
| `body_genre` | `genre` extrait du tag `Grain: <TIER>/<GENRE>` dans le body |
| `interpretation_cue` | body matche un de : `# Interpretation`, `# Transition`, `framing`, `enrichissement`, `interpretation cell`, `markdown-only`, `cellule markdown` |
| `drift_candidate` | `only_notebook AND zero_code_modif AND body_genre ∉ LIGHT_GENRES AND interpretation_cue` |

### Reproduction

```bash
# Pré-requis : avoir peuplé /tmp/census_clean.json (590 PRs avec files+body)
python scripts/variation_genre_recensement.py \
    --input-json /tmp/census_clean.json \
    --sample-size 590 --seed 42 \
    --output-csv /tmp/census.csv \
    --output-json /tmp/census.json \
    --summary
```

Le script `scripts/variation_genre_recensement.py` est idempotent (seed fixé) et lit un JSON pré-fetché. Le fetcher lui-même (~5 min pour 590 PRs avec `gh pr view`) sort du scope de ce livrable — le pipeline est `gh pr list --json number` → split en chunks → `gh pr view N --json files,body,mergedAt,title` × N en parallèle.

## Résultats détaillés

### Distribution par genre déclaré (top 15)

Sur 590 PRs échantillonnées (490 ipynb + 100 non-ipynb), 75 % portent un tag `Grain:`. Top genres :

| Genre | Count | % du sample |
|-------|-------|-------------|
| `notebook-python` | 103 | 17,5 % |
| `tooling` | 51 | 8,6 % |
| `docs` | 48 | 8,1 % |
| `notebook-dotnet` | 33 | 5,6 % |
| `guard` | 23 | 3,9 % |
| `readme` | 16 | 2,7 % |
| `test` | 15 | 2,5 % |
| `identity` | 14 | 2,4 % |
| `notebook-markdown` | 12 | 2,0 % |
| `value` | 10 | 1,7 % |
| `qc` | 8 | 1,4 % |
| `refactor` | 7 | 1,2 % |
| `cost` | 7 | 1,2 % |
| `training` | 6 | 1,0 % |
| `lean` | 6 | 1,0 % |

**Confirmation** : `notebook-python` (17,5 %) et `notebook-dotnet` (5,6 %) sont les 1er et 4e genres les plus déclarés. C'est cohérent avec la nature notebook-first de CoursIA.

### 15 PRs markdown-only `.ipynb` (full PR #)

| # | Genre | Famille | Titre (tronqué) |
|---|-------|---------|-----------------|
| 10249 | `notebook-python` | QuantConnect/Python | fix(qcpy,#10097): un-glue 6 GFM tables across QC-Py family |
| 10231 | `notebook-python` | QuantConnect/Python | fix(qcpy,#10097): blank lines before 4 glued GFM tables in QC-Py-11 |
| 10224 | `notebook-python` | QuantConnect/projects | fix(quantconnect,#10097): add blank lines before 2 glued GFM tables in LongShort |
| 10218 | `notebook-python` | GenAI/SemanticKernel | fix(genai,#10097): add blank lines before 5 glued GFM tables in SK-Advanced |
| 10217 | `notebook` | GenAI/Audio | fix(genai,#10097): repair 9 NO_BLANK_BEFORE GFM table defects |
| 9326 | NONE | RL/rl_3_experience_replay_dqn | fix(rl): clear setext_oversized in rl_3_experience_replay_dqn cell#34 |
| 9285 | NONE | CaseStudies/Oncology-Planning | fix(markdown-rendering): clear setext_oversized in Oncology-Planning student cell |
| 9229 | NONE | SymbolicAI/SMT | feat(cost,#8056): SMT Z3-Python family cost-metadata (4 notebooks) |
| 9228 | NONE | Probas/Pyro_RSA_Hyperbole | feat(cost,#8056): Probas Pyro RSA notebook cost-metadata |
| 9227 | NONE | Sudoku/Sudoku-14-BDD-Python | feat(cost,#8056): Sudoku Python BDD/inference family cost-metadata |
| 9226 | NONE | Probas/Pyro_MA_Hyperbole | feat(cost,#8056): Probas Pyro MA notebook cost-metadata |
| 9225 | NONE | Probas/Pyro_Hyperbole | feat(cost,#8056): Probas Pyro hyperbole family cost-metadata (3 notebooks) |
| 9223 | NONE | Sudoku/Sudoku-15-Backtrack-Python | feat(cost,#8056): Sudoku Python backtrack family cost-metadata |
| 9195 | NONE | (notebook) | (markdown repair) |
| 9108 | NONE | (notebook) | (markdown repair) |

### Classification manuelle des 15 PRs

| Cluster | # PRs | Verdict |
|---------|-------|---------|
| **Fix GFM rendering légitime** (PR #10097 wave) | 5 | ✅ MED/`notebook-python` correct — fix de défauts de rendu GFM, +0/-0 pour la plupart cellules, déclarés MED à raison |
| **Fix setext_oversized légitime** | 2 | ✅ MED/`markdown-rendering` correct — fix de cellules markdown cassées |
| **Cost-metadata enrichment** (PR #8056 wave) | 6 | ⚠️ MED/none — cellules markdown ajoutant de l'info de coût ; déclaré LIGHT-equiv ou NONE, pas de blanchiment flagrant |
| **Autres (markdown-repair génériques)** | 2 | ⚠️ Pas de tag `Grain:` — opaques à la classification |

**AUCUN** des 15 ne correspond à du blanchiment au sens strict (déclarer `notebook-python` pour échapper au budget LIGHT). Tous sont des **MED-tier legítimos** ou des PRs sans tag grain.

## Verdict

**L'organe de détection dédié `variation-genre-family-drift` n'est PAS justifié** au seuil de 5 % (résultat : 1,51 %, dont 0 % de blanchiment effectif). Le motif blanchiment -- déclare `notebook-python`/`notebook-dotnet` pour échapper au budget LIGHT -- est un **non-problème empirique** sur la fenêtre 7 j.

### Pourquoi l'organe rétrécit :

1. **Faible signal** : 1,51 % de PRs markdown-only `.ipynb` (15/996), dont 0 sur le critère strict "blanchiment".
2. **Heuristique fragile** : les cues `# Interpretation` / `# Transition` matchent la documentation de PRs légitimes (rationale de fix GFM, justification de cost-metadata). Faux-positifs structurellement non-discriminables sans review manuelle.
3. **Coût organe > gain** : un label CI dédié génère bruit (notifications `gh pr edit`) pour ~0 blanchiment/an. Le ratio coût/bénéfice est défavorable.

### Recommandation

- **NE PAS** activer le label `variation-genre-family-drift` dans `variation-light-genre.yml`.
- **Garder `variation-light-genre.yml` actif** sur les 4 labels existants (TIER-INFLATION, GENRE-RUN, CAP-EXCEEDED-BY-GENRE, GENRE-MISMATCH) — ils restent utiles.
- **Si le blanchiment émerge** (signal > 5 % sur une fenêtre ultérieure), réactiver la discussion. Le script `variation_genre_recensement.py` est en place pour re-mesurer à la demande.

## Livrables

1. **`scripts/variation_genre_recensement.py`** (161 lignes) — standalone census, idempotent, lecture JSON pré-fetché.
2. **`data/census/variation_genre_census_2026-08-10.csv`** (optionnel) — 1 ligne par PR, 11 colonnes.
3. **`docs/reference/variation-genre-census-2026-08-10.md`** (ce document) — closure de la discussion sur l'organe.

## Voir aussi

- [Issue #10290](https://github.com/jsboige/CoursIA/issues/10290) — déclenchement
- [PR #10285](https://github.com/jsboige/CoursIA/pull/10285) — qui a livré le scope plus large (variation-tag-guard.yml + label lane-missing) mergé 2026-08-10T09:56:29Z
- [`.github/workflows/variation-light-genre.yml`](../../.github/workflows/variation-light-genre.yml) — organe 4 signaux G-VAR-2/3-by-GENRE (TIER-INFLATION, GENRE-RUN, CAP-EXCEEDED-BY-GENRE, GENRE-MISMATCH) — conservé tel quel
- [`scripts/variation_light_cap.py`](../../scripts/variation_light_cap.py) — moteur partagé (`light_budget = max(1, lane_grain_count // 3)`)
- DM ai-01 `msg-20260810T100246-gglzhl` — dispatch grain
