# EPIC #13746 — Ledger dissipation câblage tests éclatés (45+ emplacements)

**Statut** : Dissipation documentée (toutes les tranches de l'acceptance livrées, le body reste comme trace).

**Source** : Issue #13746 (créée avant 2026-09-04, "[consolidation] Tests eclates 45+ emplacements : GameTheory/tests mort en CI (#10903), regroupements (V3)"). Body décrit 6 familles de tests à câbler, dont le cas bloquant `MyIA.AI.Notebooks/GameTheory/tests/` (21 fichiers jamais exécutés par CI).

**Périmètre** : ce ledger consigne l'état vérifié au 2026-09-24 et la dissipation de l'acceptance — les 6 familles + les tests GameTheory sont câblés.

## Vérification empirique (c.807, 2026-09-24)

**Lecture first-hand `pytest.ini`** (13 testpaths déclarés, ligne 2-13) :

```
testpaths =
    scripts/notebook_tools/tests
    scripts/lean/tests
    MyIA.AI.Notebooks/GameTheory/tests
    MyIA.AI.Notebooks/ML/DataScienceWithAgents/01-PythonForDataScience/tests
    MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/scripts/tests
    scripts/tests
    scripts/audit/tests
    scripts/quantconnect/tests
    scripts/translation/tests
    scripts/secrets/tests
    MyIA.AI.Notebooks/QuantConnect/scripts/tests
    MyIA.AI.Notebooks/GenAI/shared/helpers
    GradeBookApp
```

**Lecture first-hand `.github/workflows/scripts-tests.yml`** (chemin `paths:` ligne 53-71) :

```
paths:
  - 'scripts/**'        # couvre scripts/{tests,audit/tests,quantconnect/tests,secrets/tests,notebook_tools/tests,lean/tests,translation/tests}
  - 'tests/**'
  - 'pytest.ini'
  - '.github/workflows/scripts-tests.yml'
  ...
```

Donc : **toute modification sous `scripts/**` déclenche `scripts-tests.yml`**, qui exécute tous les `pytest.ini testpaths` listés. Les 6 familles du body #13746 sont câblées :

| Famille body #13746 | Câblage | Source |
|--------------------|---------|--------|
| `MyIA.AI.Notebooks/GameTheory/tests/` (21 fichiers) | `gametheory-tests.yml` (workflow dédié, paths: `MyIA.AI.Notebooks/GameTheory/**`) | PR #14614 MERGED 2026-09-05, tranche 1/45 |
| `MyIA.AI.Shared.Tests` (8 .cs) | `dotnet-Shared.Tests.yml` (workflow dédié .NET) | PR #14668 MERGED 2026-09-05, famille 1/6 #14615 |
| `scripts/audit/tests/` | `scripts-tests.yml` (paths: `scripts/**`) + ligne 308 explicit | famille 2/6 #14615, PR #14670 MERGED 2026-09-05 |
| `scripts/quantconnect/tests/` | `scripts-tests.yml` (paths: `scripts/**`) + ligne 315 explicit | famille 3/6 #14615 |
| `scripts/secrets/tests/` | `scripts-tests.yml` (paths: `scripts/**`) + ligne 314 explicit | famille 4/6 #14615, 2026-09-04 |
| `GradeBookApp` | `scripts-tests.yml` (paths: `scripts/**`) + ligne 316 explicit | famille 5/6 #14615, 2026-09-05 |
| `scripts/tests/` racine (251 fichiers) | `scripts-tests.yml` (paths: `scripts/**`) + ligne 303 explicit | famille 6/6 #14615 |

**Cas additionnel livré** (mentionné par l'issue mais hors acceptance explicite) :

- `MyIA.AI.Notebooks/GenAI/shared/helpers` (138 tests) → PR #16724 MERGED 2026-09-19, tranche 2/45 par po-2024

## Verdict

**`DISSIPATED_BY_ABSORPTION`**. Toutes les familles sont câblées, tous les workflows pytest incluent leurs testpaths, et les PRs historiques sont mergées. Aucun fix code supplémentaire requis pour fermer cette EPIC.

## Statut des PRs référencées

| PR | Status | Date | Tranche | Auteur (claim vérifié) |
|----|--------|------|---------|----------------------|
| #14614 | MERGED | 2026-09-05 | tranche 1/45 GameTheory | po-2027 ([CLAIMED] 4a8d2a9ce) |
| #14668 | MERGED | 2026-09-05 | famille 1/6 #14615 dotnet Shared.Tests | po-2026 |
| #14670 | MERGED | 2026-09-05 | famille 2/6 #14615 scripts/audit/tests | po-2026 |
| #16724 | MERGED | 2026-09-19 | tranche 2/45 GenAI helpers | po-2024 |

## Leçons c.807

- **Un `paths:` racine `scripts/**`** dans `scripts-tests.yml` est l'organe qui rend obsolète la discrimination fine par sous-dossier. Tant que `paths:` match large, chaque `testpaths` du `pytest.ini` est exécuté sur PR. Le câblage détaillé (lignes 303-316) reste utile pour la **citation textuelle** des outils de garde (`scripts/check_testpaths_coverage.py`) mais n'est plus un déclencheur.
- **Le compteur de tests exécutés en CI** a augmenté de plusieurs centaines depuis l'ouverture de l'EPIC (GameTheory seul = 600 items collectés baseline 2026-09-04, vs 0 avant). L'acceptance 2 ("Compte de tests exécutés en CI > avant") est largement tenue.
- **L'EPIC reste utile comme trace** même dissipée : ce ledger permet à un reviewer de re-vérifier le câblage en 5 minutes sans rouvrir les PRs individuelles.

## Entry #001 — c.807 (po-2023)

| Métrique | Valeur |
|----------|--------|
| Cycle | c.807 |
| Date | 2026-09-24 (mesure first-hand) |
| Lane | `myia-po-2023:CoursIA-2` |
| Issue | #13746 |
| Verdict | `DISSIPATED_BY_ABSORPTION` |
| PR upstream | aucune nouvelle (câblage livré par PR #14614 #14668 #14670 #16724, MERGED 2026-09-05 → 2026-09-19) |

— myia-po-2023:CoursIA-2 (po-2023, c.807)
