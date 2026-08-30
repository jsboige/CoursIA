# DecisionTheory / voi — adaptateurs cross-engine runtime EVPI/EVSI

Tranche 3/3 de l'**Epic #13569** : la valeur de l'information existe déjà
trois fois dans le dépôt (DecInfer-6, DecPyMC-5, DecPyMC-11), et l'ICT
(ICT-12e) doit poser le *problème de décision* d'animat et laisser les
**organes natifs** calculer. Cette tranche ne modifie pas les notebooks
sources : elle extrait leur logique de calcul et la sert sur un contrat
JSON commun, puis compare les sorties des deux moteurs bayésiens.

## Scope

```
MyIA.AI.Notebooks/Probas/DecisionTheory/voi/
├── __init__.py
├── contract.py        # VoiContract + VoiResult + reference analytique
├── adapter_pymc.py    # PyMC natif (pymc.sample)
├── adapter_infernet.py # Microsoft.ML.Probabilistic via dotnet script
├── compare.py         # Runner + CompareReport JSON-serializable
├── tests/
│   └── __init__.py    # pytest : contrat + analytique + PyMC
└── demo_cross_engine.ipynb
```

## Contrat

`VoiContract` : états, prior, actions, utilité, vraisemblance du test,
coût de l'observation. Sérialisable en JSON.

`VoiResult` : `eu_no_info`, `best_no_info`, `evpi`, `evsi`, `evsi_net`,
`observe`, `raw`. Aligné sur la signature
`ict.voi.animat_decision_summary` (tranche 1/3, PR #13652).

## Acceptance

1. Même problème envoyé aux deux moteurs via le contrat JSON.
2. **Référence analytique close-form NumPy** : `animat_decision_summary_contract`
   sert de cible de test ; tout adaptateur doit s'en approcher à `1e-2`
   près (MCMC) ou `1e-9` (Infer.NET symbolique).
3. **Contrôles** :
   - **Négatif dégénéré** : test indépendant de l'état ⇒ `EVSI = 0`.
   - **Discriminant** : `0 < EVSI nette < EVPI` quand le test a de la
     valeur et un coût < EVPI.
4. **Divergence rapportée, jamais lissée** : `CompareReport.diffs` liste
   les grandeurs hors tolérance.
5. PR atomique, `See #13569`. **Ne pas** modifier DecInfer-6 / DecPyMC-5 /
   DecPyMC-11 / PR #13664.

## Limitations / Recoverable

- `adapter_infernet.run_infernet` exige `dotnet` + `dotnet-script` dans le
  PATH. Si absent, `RuntimeError` est levée avec mention
  `RECOVERABLE-LOCAL` — voir `sota-not-workaround.md §F`. **Pas** de
  fallback masqué en Python : un adaptateur qui simule Infer.NET sans
  l'appeler serait un workaround dégradé (`SOTA` Prong A).
- `adapter_pymc.run_pymc` exige `pymc`. Mêmes conventions.

## Tests

```bash
pytest MyIA.AI.Notebooks/Probas/DecisionTheory/voi/tests/ -v
```

Les tests négatifs (PyMC / Infer.NET absents) sont skipped proprement —
ils ne bloquent pas le pipeline, mais ils tracent l'env manquant.

## Référence

- Issue **#13569** — greffe 3 (jambe C2 ICT-12e).
- PR **#13652** — tranche 1/3 (interface canonique `ict/voi.py`).
- PR **#13664** — tranche 2/3 (notebook ICT-12e mono-moteur).
- `MyIA.AI.Notebooks/Probas/DecisionTheory/DecInfer/DecInfer-6-Value-Information.ipynb`
- `MyIA.AI.Notebooks/Probas/DecisionTheory/PyMC/DecPyMC-5-Value-Information.ipynb`
