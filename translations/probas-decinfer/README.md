# CSV de synchro traduction — série Probas/DecisionTheory/DecInfer

**Statut** : Phase 2 rollout (Epic #4957 / #1650). La série Decision Theory via Infer.NET (C# .NET Interactive) est couverte par l'infrastructure i18n.

## Couvert

| Fichier | Série | Notebooks | Cellules |
|---------|-------|-----------|----------|
| [`probas_decinfer.csv`](probas_decinfer.csv) | `MyIA.AI.Notebooks/Probas/DecisionTheory/DecInfer/` | 8 (non-Lean) | 383 (246 markdown + 137 code, 21 colonnes) |

La série couvre la théorie de la décision avec Infer.NET :

- **DecInfer-1-Utility-Foundations** — fondements de l'utilité, rationalité, axiomes von Neumann–Morgenstern.
- **DecInfer-3-Utility-Money** — utilité de la richesse, aversion au risque, fonction d'utilité CRRA.
- **DecInfer-4-Multi-Attribute** — utilité multi-attributs, pondération, trade-offs.
- **DecInfer-5-Decision-Networks** — réseaux de décision (influence diagrams), valeur de l'information structurelle.
- **DecInfer-6-Value-Information** — valeur espérée de l'information (EVPI/EVSI), Infer.NET inference.
- **DecInfer-7-Expert-Systems** — systèmes experts probabilistes, règles bayésiennes.
- **DecInfer-8-Sequential** — décision séquentielle, équations de Bellman, horizon fini.
- **DecInfer-10-Thompson-Sampling** — échantillonnage de Thompson, compromis exploration/exploitation.

**Schéma** : 21 colonnes (#4957 §1). `src_lang=fr`, `src_hash` (sha256-16) + `text_fr` remplies ; colonnes cible (`text_en/es/ar/fa/zh/ru/pt`) vides pour le moteur T3 Argumentum (#1650 Phase 1).

## Régénération

```bash
# Depuis la racine du dépôt :
python scripts/translation/extract_cells_to_csv.py \
    MyIA.AI.Notebooks/Probas/DecisionTheory/DecInfer/DecInfer-1-Utility-Foundations.ipynb \
    MyIA.AI.Notebooks/Probas/DecisionTheory/DecInfer/DecInfer-3-Utility-Money.ipynb \
    MyIA.AI.Notebooks/Probas/DecisionTheory/DecInfer/DecInfer-4-Multi-Attribute.ipynb \
    MyIA.AI.Notebooks/Probas/DecisionTheory/DecInfer/DecInfer-5-Decision-Networks.ipynb \
    MyIA.AI.Notebooks/Probas/DecisionTheory/DecInfer/DecInfer-6-Value-Information.ipynb \
    MyIA.AI.Notebooks/Probas/DecisionTheory/DecInfer/DecInfer-7-Expert-Systems.ipynb \
    MyIA.AI.Notebooks/Probas/DecisionTheory/DecInfer/DecInfer-8-Sequential.ipynb \
    MyIA.AI.Notebooks/Probas/DecisionTheory/DecInfer/DecInfer-10-Thompson-Sampling.ipynb \
    -o translations/probas-decinfer/probas_decinfer.csv \
    --src-lang fr
```

L'extraction est **déterministe byte-identique** (mêmes hash sha256-16 sur texte normalisé) — re-exécuter produit le même CSV.

## Vérification de drift (T2)

```bash
python scripts/translation/check_translation_sync.py translations/probas-decinfer/probas_decinfer.csv
```

Résultat à l'extraction : `anomaly_count: 0` (IN_SYNC par construction).

## Pre-flight secret

DecInfer est une série .NET (Infer.NET probabilistic programming) sans labs agentic ni appels d'API LLM. Scan systématique sur le CSV avant commit : `sk-*`, `sk-ant-*`, `ghp_*`, `hf_*`, `AIza*`, `getenv("KEY", "<literal>")` = **0 hit**.

## Note owner

`Probas/DecisionTheory/DecInfer/` = famille Infer.NET C# (partition .NET de po-2024). L'extraction i18n est **safe cross-owner** : artefact dérivé (CSV de cellules upstream en lecture seule), aucune modification des notebooks source (cf note identique dans `translations/probas-infer/README.md` et `translations/probas-pymc/README.md`).

## Hors scope

- `DecInfer-2-Lean-ExpectedUtility.ipynb`, `DecInfer-9-Lean-Gittins.ipynb` — notebooks **Lean 4** exclus (EPIC #4980, sibling-pair FR-first, piste i18n distincte gérée par po-2026). Convention cohérente avec `probas_infer.csv` / `probas_pymc.csv` (0 notebook Lean en CSV).
- `Probas/DecisionTheory/PyMC/` (DecPyMC-1..7) — série Python PyMC, owner po-2025 (cf owner-lock `Probas-DecPyMC`). Non incluse ici.
- `Probas/DecisionTheory/Causal-Bridges/` — série causale Python standalone, non encore seedée.
