# CSV de synchro traduction — série ML/DataScienceWithAgents

**Statut** : Phase 2 rollout (Epic #4957 / #1650). La série Data Science with Agents (Python + agentic labs) est couverte par l'infrastructure i18n.

## Couvert

| Fichier | Série | Notebooks | Cellules |
|---------|-------|-----------|----------|
| [`ml-datascience.csv`](ml-datascience.csv) | `MyIA.AI.Notebooks/ML/DataScienceWithAgents/` | 27 (4 sous-dossiers) | 708 (markdown + code, 20 colonnes) |

La série couvre quatre parcours imbriqués :

- **01-PythonForDataScience** (2 notebooks) — fondamentaux NumPy et Pandas.
- **02-ML-Cours** (8 notebooks) — workflow ML, descente de gradient, régression linéaire/logistique, arbres/forêts/ensembles, biais/variance/CV/ROC, clustering KMeans/PCA, modèles non-paramétriques, théorie PAC.
- **PythonAgentsForDataScience** (7 labs) — Labs 1-7 : Python pour data science, analyse RFP, CV screening, data wrangling, viz/ML, premier agent, agent d'analyse de données.
- **AgenticDataScience** (10 labs) — Labs 8-17 : introduction ADK, premier agent ADK, file analyzer, planner-coder loop, atelier DS-Star, web search SOTA, ablation refinement, challenge Kaggle, data science agent de production, projet final.

**Schéma** : 20 colonnes (#4957 §1). `src_lang=fr`, `src_hash` (sha256-16) + `text_fr` remplies ; colonnes cibles (`text_en/es/ar/fa/zh/ru/pt`) vides pour le moteur T3 Argumentum (#1650 Phase 1).

## Régénération

```bash
# Depuis la racine du dépôt :
python scripts/translation/extract_cells_to_csv.py \
    MyIA.AI.Notebooks/ML/DataScienceWithAgents \
    -o translations/ml-datascience/ml-datascience.csv \
    --src-lang fr
```

L'extraction est **déterministe byte-identique** (même ordre de notebooks, mêmes hash sha256-16 sur texte normalisé) — re-exécuter produit le même CSV.

## Vérification de drift (T2)

```bash
python scripts/translation/check_translation_sync.py translations/ml-datascience/ml-datascience.csv
```

Résultat à l'extraction : `OK : 1 CSV vérifié(s), 0 drift` (IN_SYNC par construction).

## Pre-flight secret

Les Labs agentic (ADK, DS-Star, MLE-Star, Web-Search-SOTA, Lab13-Web-Search-SOTA) utilisent des API LLM (OpenAI, Anthropic). Scan systématique sur le CSV avant commit : `sk-*`, `sk-ant-*`, `ghp_*`, `hf_*`, `AIza*`, `os.getenv(KEY, "<literal>")` = **0 hit**. Les clés sont lues via `os.getenv` sans défaut littéral (les notebooks utilisent les environnements dédiés).

## Note owner

`ML/DataScienceWithAgents/` = famille Python (ML partition). L'extraction i18n est **safe cross-owner** : artefact dérivé (CSV de cellules upstream en lecture seule), aucune modification des notebooks source (cf note identique dans `translations/genai/README.md` et `translations/search-applications/README.md`).

## Hors scope

- `ML/ML.Net/` — série .NET distincte, déjà couverte par `translations/mlnet/`.
- `ML/learning_theory_lean/` — série Lean (hors scope i18n notebooks, cf EPIC #4980).
- `ML/DataScienceWithAgents/**/assets/`, `data/` — supports non pédagogiques (exclus par le glob `.ipynb` récursif).
