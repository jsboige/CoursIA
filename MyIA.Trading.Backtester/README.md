# MyIA.Trading.Backtester

Backtester AutoML **offline** en .NET 9 : charge des trades au format CSV (`MyIA.Trading.Converter`), en fabrique des échantillons d'entraînement, entraîne un modèle (AutoML ML.NET ou SVM à noyau Accord.NET), puis rejoue des stratégies contre un simulateur d'exchange déterministe (`Core/ExchangeSimulator`) pour produire historiques et métriques de comparaison.

Port **Option C** (décision user du 2026-07-19, issue [#7357](https://github.com/jsboige/CoursIA/issues/7357) : découplage Aricie, substitution des libs, abandon des 6 DLL PKP) du module `MyIA.Trading.Backtester` du fork [MyIntelligenceAgency/Lean](https://github.com/MyIntelligenceAgency/Lean) (branche `MyIABacktesting_integration`, sha `612dddf9`).

## État du port (mesuré le 2026-09-10 sur `origin/main`)

| | |
|---|---|
| Fichiers `.cs` du module | **58** (contre 75 upstream — voir « Résiduel » ci-dessous) |
| Fichiers upstream regroupés | 12 fichiers `Core/` séparés en amont sont portés dans 2 agrégats : `Core/MarketModels.cs` (ResponseObject, Ticker, Balance, MarketDepth, MarketInfo, AsksAndBids) et `Core/TradingModels.cs` (Payment, TradingEvent, TradingTrend, Transaction, TransactionType, TradingAPIUrls) |
| Tests | **114/114 verts** (`dotnet test` sur `MyIA.Trading.Backtester.Tests`, 1 min 35 s), couverture : Core (Order, OrderTrade, UnixTime, FastRandom, simulation), orchestrateur (`BacktestingOrchestrationTests` : `RunSimulation` chaîne complète CSV → wallets → baseline Hodl + ModelStrategy stub → `SimulationInfo` ; `RunSimple` boucle SimpleStopStrategy), stratégies (bande market-maker, couche stratégie), configs, SVM, AutoML |
| DLL Aricie PKP référencées | **0** (critère de fermeture de l'EPIC) |
| Cible | `net9.0` |

Tranches mergées : scaffold (#13669) · couche config+données (#13858 en amont : tranche 2) · AutoML config (#13858) · corps SVM à noyau (#14369, disposition upstream de `CalibrateComplexity` : #14522) · couverture unitaire (#14400) · cœur de simulation déterministe (#14753) · couche stratégies et résultats (#14819) · orchestration configuration (#14857) · orchestrateur `BackTesting.cs` (#15072) · couche stratégies Core bande market-maker + adaptateur Flee (#15081).

## Structure

```
Core/                  Cœur de simulation : ExchangeSimulator, MarketModels, TradingModels,
                       Wallet, TradingContext/History/Series, stratégies de base,
                       SimpleExpression (prédicats dynamiques via Flee)
AutoML/                ConsoleHelper, ProgressHandlers (adaptation API AutoML 0.24)
TradingModelConfig.cs  Base des modèles + exécution à limite de temps
TradingSvmModelConfig.cs  SVM multiclasse à noyau (Accord) + CalibrateComplexity + SvmBenchmark
TradingAutoMlModelConfig.cs  Entraînement AutoML ML.NET
TradingTrainingDataConfig.cs Fabrique des jeux train/test (équilibre par classe, normalisation)
BackTesting.cs         Orchestrateur : configs → modèles → simulations → comparaison
BackTestingConfig.cs / BackTestingSettings.cs / BacktestResult.cs
Stratégies racine      ModelStrategy, BoostedStrategy, HodlStrategy, SimpleStopStrategy,
                       MultiClassBoost, CompareBackTestings
TradeHelper.cs         Sérialisation (Binary=MessagePack, Csv=TinyCsv, Json=UTF-8, Xml, 7z)
```

## Substitutions et verdicts SOTA

Le cadrage complet (mesures firsthand, test de compilations réelles) : [docs/reference/backtester-e2-cadrage.md](../docs/reference/backtester-e2-cadrage.md) et [docs/reference/backtester-e2-svm-kernel.md](../docs/reference/backtester-e2-svm-kernel.md).

| En amont (fork) | Dans ce port | Verdict |
|---|---|---|
| `Accord.MachineLearning` 3.8.2-alpha (SVM à noyau) | **Conservé tel quel** — `Accord.* 3.8.2-alpha` restore, compile et exécute le corps upstream verbatim sur net9.0 | **SOTA-OK** (#12545, génération validée #14369) |
| `Microsoft.ML.AutoML` 0.20.1 + `Microsoft.ML` | `Microsoft.ML.AutoML 0.24.0-preview.26160.2` + `Microsoft.ML 6.0.0-preview.26160.2` (paire figée, test d'intégration `AutoMlInferenceTests` réplique le mini-test du cadrage : `MicroAccuracy > 0.9`) | **SOTA-OK** — adaptation d'API, pas un re-packaging (`ColumnInferenceResults.TextLoaderEventArgs` a disparu en 0.24) |
| `Ciloci.Flee.dll` (DLL Aricie) | `Flee 2.0.0` NuGet (transitif via `MyIA.AI.Shared`), consommé par `Core/SimpleExpression.cs` et `Core/TradingStrategy.cs` | **SOTA-OK** (#15081) |
| Sérialisation binaire `Apex.Serialization` | MessagePack (le Converter sert les mêmes caches `.bin.lz4`) — Apex lève `TypeInitializationException` sur net9.0 (champ backing readonly) | Documenté dans `TradeHelper.cs` (tranche 6B-3) |
| 6 DLL Aricie PKP (`Aricie.Core`, `Aricie.DNN`, `DotNetNuke`, `CommonMark`, `Fasterflect` + Flee) | Abandonnées (Option C) ; le socle transverse vit dans `MyIA.AI.Shared` | Décision user 2026-07-19 |

Écarts délibérés avec l'upstream, documentés dans les en-têtes des fichiers concernés : `using DotNetNuke` mort supprimé ; ordre des membres `KnownKernel` stabilisé (l'ordinal sérialisé ne doit pas bouger) ; `CalibrateComplexity` réparée (le corps upstream ne calibrait rien — signalé en amont : [Lean#40](https://github.com/MyIntelligenceAgency/Lean/issues/40)).

## Résiduel : fichiers upstream volontairement non portés

**11 fichiers sur 75**, aucun référencé par le cœur porté (le module compile et la suite passe sans eux — c'est la mesure, pas une intention) :

| Fichiers upstream | Nature | Disposition |
|---|---|---|
| `Core/Account.cs` (21 l.) | Compte exchange en ligne (hérite `ResponseObject`) | Hors périmètre : couche live-trading, pas backtest offline |
| `Core/CommercialAccount.cs` (152 l.), `CommercialCredentials.cs` (31 l.), `CommercialFee.cs` (45 l.), `CommercialPlan.cs` (66 l.) | Gestion de compte **commercial** (plans, frais, crédits) du service d'origine | Hors périmètre : monétisation d'un service en ligne, sans objet pédagogique ici |
| `Core/ExchangeCredentials.cs` (24 l.), `OnlinePayment.cs` (21 l.), `WalletPayment.cs` (22 l.) | Credentials API exchange, paiements en ligne | Hors périmètre : jamais instanciés par l'orchestrateur porté |
| `Core/InitialWallet.cs` (10 l., enum) | Choix de portefeuille initial pour le live | Hors périmètre live ; le simulateur porte son propre wallet initial |
| `Program.cs` (77 l.) | Entry console de démo du fork | Non porté : le module est une bibliothèque, les tests d'intégration en sont la démo exécutable |
| `TradingData.cs` (68 l.) | **Code mort en amont** : classe entièrement commentée dans le fork | Rien à porter |

Si un usage futur exige cette couche (ex. rejouer contre une API d'exchange), ce sera une décision de périmètre à documenter sur l'EPIC — pas un résidu oublié.

## Exécution

```bash
dotnet test MyIA.Trading.Backtester.Tests   # 114 tests, ~1 min 35 s
```

Dépendances de projet : `MyIA.AI.Shared` (socle transverse, Flee 2.0.0) · `MyIA.Trading.Converter` (formats CSV/dossier Lean, caches `.bin.lz4`).

## Voir aussi

- [#7357](https://github.com/jsboige/CoursIA/issues/7357) — EPIC du port Option C (historique des tranches)
- [#7265](https://github.com/jsboige/CoursIA/issues/7265) — EPIC index du patrimoine Aricie
- [docs/reference/backtester-e2-cadrage.md](../docs/reference/backtester-e2-cadrage.md) — cadrage, préconditions, choix de libs mesurés
- [docs/reference/backtester-e2-svm-kernel.md](../docs/reference/backtester-e2-svm-kernel.md) — verdict SOTA du SVM à noyau et disposition upstream
