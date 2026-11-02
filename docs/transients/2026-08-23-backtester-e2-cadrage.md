# MyIA.Trading.Backtester (E2) — cadrage Option C et déblocage des préconditions

> Issue [#7357](https://github.com/jsboige/CoursIA/issues/7357) (EPIC différée) · parent [#7265](https://github.com/jsboige/CoursIA/issues/7265).
> Décision user du 2026-07-19 : **Option C** (découplage Aricie, substitution des libs ML), exécution différée.
> Ce document livre les deux sous-grains prescrits par le body du 2026-08-20 : rendre la précondition « dette doc » observable (§1), et cadrer les libs de substitution (§2). Toutes les mesures sont firsthand (fork cloné sparse, compilations réelles), datées du 2026-08-23 — le point SVM de §2.3 est repris le 2026-09-03 sur les mesures #12545 et #14369 (#14371).

## 1. Précondition « absorption de la dette doc » — constat de satisfaction

Le verbatim user du 2026-07-19 diffère E2 « après absorption de la dette doc + E1 restructuré », sans définir la dette. Le body du 2026-08-20 mesurait qu'aucun tracker ne la porte (`gh search issues "dette doc"` : 0 résultat, vérifié à nouveau ce jour) et proposait trois issues : rattacher, redéfinir, ou constater caduque.

**Mesures (2026-08-23, `origin/main`)**, sous la lecture naturelle — *chaque module du patrimoine Aricie atterri sur main porte sa documentation de module* :

| Module livré | Doc | Lignes | Contenu |
|---|---|---|---|
| `MyIA.AI.Shared/` (socle) | `README.md` | 169 | rôle équivalent-moderne d'`Aricie.Shared`, composants |
| `MyIA.Trading.Converter/` (E1) | `README.md` | 123 | port, scope E1, source upstream (`612dddf9`), contournement Security Master |

Ce sont les **deux seuls** modules du patrimoine atterris à ce jour ; tous deux sont documentés. La seconde moitié de la précondition (« E1 restructuré ») était déjà constatée atteinte par le body du 2026-08-20 (commit `ca71ae5c8`, PR #7425).

**Proposition (à trancher par ai-01/user)** : la précondition est réputée satisfaite ; E2 quitte le backlog sur simple décision de planification. Le critère reste vivant pour la suite du patrimoine : *tout module Aricie atterri ultérieurement porte sa doc de module avant que l'EPIC ne soit réputée en règle*.

## 2. Cadrage des libs de substitution (Option C)

### 2.1 Ce que le fork consomme réellement (mesuré, pas supposé)

Source : `MyIntelligenceAgency/Lean`, branche `MyIABacktesting_integration`, checkout sparse de `MyIA.Trading.Backtester/` — **75 fichiers `.cs`, 91 fichiers, 16 Mo** (les chiffres de la recon po-2024 c.708 sont exacts).

| Dépendance | Empreinte mesurée |
|---|---|
| `Accord.MachineLearning` (+VectorMachines, +Boosting, Statistics, Math) | 11 fichiers porteurs (`BackTesting.cs`, `ModelStrategy.cs`, `MultiClassBoost.cs`, `TradingSvmModelConfig.cs`…) ; symboles dominants : `SvmModelConfig` ×33, `SupportVectorMachine` + `SequentialMinimalOptimization` (SMO), kernels `Linear`/`Gaussian`, boosting |
| `Microsoft.ML` + `Microsoft.ML.AutoML` | `AutoML` ×35, `ColumnInferenceResults`/`ColumnInferencePrinter` |
| 6 DLL Aricie en HintPath | `Aricie.Core`, `Aricie.DNN`, `Ciloci.Flee`, `CommonMark`, `DotNetNuke`, `Fasterflect` — à abandonner ; le socle transverse a déjà son équivalent moderne (`MyIA.AI.Shared`, dont `FleePredicateBuilder` testé sur main) |

### 2.2 Test réel sur .NET 9 (2026-08-23, SDK 9.0.317)

Mini-projet `net9.0` dans un scratchpad, répliquant les usages du fork : `InferColumns` (l'usage AutoML réel) + entraînement linéaire + `PredictionEngine` :

- **Paire résolue** : `Microsoft.ML.AutoML 0.24.0-preview.26160.2` → transitif `Microsoft.ML 6.0.0-preview.26160.2`. Restore, build et exécution **SUCCESS** : `InferColumns OK`, `SdcaMaximumEntropy : MicroAccuracy=1,000`, prédiction correcte.
- `Microsoft.ML 4.0.0` (stable) existe seule ; **AutoML n'a pas de build stable apparié récent** (NU1102 mesuré : plafond `0.24.0-preview`). Le fork tourne sur `AutoML 0.20.1` (2022).

### 2.3 Conséquences pour le port

1. **Breaking API AutoML, mesuré au compilateur** : `ColumnInferenceResults.TextLoaderEventArgs` (API 0.20.x utilisée par le fork) n'existe plus en 0.24 — remplacée par `TextLoaderOptions`/`ColumnInformation` (CS1061 reproduit puis corrigé dans le test). Le port AutoML n'est **pas** un re-packaging : c'est une adaptation d'API.
2. **SVM** : ML.NET n'offre pas de SVM à noyau ; le linéaire seul se remplace proprement (`SdcaMaximumEntropy`, multiclasse comme `MultiClassBoost.cs` du fork ; binaire : `AveragedPerceptron`/`SdcaLogisticRegression` sur label bool). **Le « gap noyau gaussien » annoncé ici à l'origine est clos — rien n'était à trancher** : #12545 a établi le verdict **SOTA-OK** sans lib tierce (doc [`backtester-e2-svm-kernel.md`](backtester-e2-svm-kernel.md)), la lib retenue étant Accord.NET lui-même ; la tranche 4 de #7357 (PR #14369) mesure ensuite qu'**Accord.NET 3.8.2-alpha** — la version du fork — restore et compile le corps upstream **verbatim** sur net9.0 (`0 Avertissement(s) 0 Erreur(s)`, pas de NU1701) : le SVM à noyau est **conservé, sans substitution**. Ce que la tranche 4 ajoute à la décision #12545 est la **génération** : la 3.8.2-alpha (API `MulticlassSupportVectorLearning` + `Learn`) compile le corps tel quel, là où la 2.6.0 validée par #12545 (génération précédente, restaurée via le shim NU1701) aurait imposé de le réécrire.
3. **Boosting** : `FastTree` (gradient boosting ML.NET) remplace les boosters Accord.
4. **Stratégie recommandée** : figer la paire preview `AutoML 0.24.0-preview.26160.2` + `ML 6.0.0-preview.26160.2` (la seule testée ci-dessus), isoler les usages AutoML derrière une interface (`IColumnInference`) pour contenir le risque preview, et répliquer le test ci-dessus comme test d'intégration du port (il est volontairement petit : CSV inline, assert `MicroAccuracy > 0.9`).

### 2.4 Périmètre restant du port (non re-mesuré ici)

`BackTesting.cs` 755 lignes, 6 DLL Aricie à découpler, `ProjectReference` vers `MyIA.Trading.Converter` (déjà sur main). L'effort reste celui du cadrage d'origine — ce document ne le réevalue pas, il en lève les deux préconditions.

## Voir aussi

- [#7357](https://github.com/jsboige/CoursIA/issues/7357) — body du 2026-08-20 (état mesuré, voies par coût croissant)
- [#7265](https://github.com/jsboige/CoursIA/issues/7265) — EPIC index du patrimoine Aricie
- [quantconnect.md](../qc/quantconnect.md) — contexte QC, contournement Security Master (E1)
