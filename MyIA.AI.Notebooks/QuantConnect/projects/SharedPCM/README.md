# SharedPCM — module canonique du PCM par poches

`pouches_pcm.py` porte `MultiStrategyPouchesPCM`, le Portfolio Construction
Model partagé par tous les composites multi-alpha du dépôt (brique 1 de la
ligue #19821). Avant l'extraction, chaque projet composite déclarait sa
propre copie de `MultiStrategyPCM` dans `portfolio_construction.py` — quatre
copies divergentes mesurées sur `main` au moment de l'extraction : deux avec
le mode intent (`Framework_Composite_EMATrend`, `Framework_Composite_MomentumRegime`),
deux sans (`Framework_Composite_FamaFrenchAllWeather`,
`Framework_Composite_TrendWeather`). Les projets composites importent
désormais ce module ; leurs copies sont retirées.

## Sémantique (mode intent par défaut)

- une poche de capital fixe par alpha (`alpha_allocations`) ;
- dans chaque poche, le dernier insight actif par couple (symbole,
  `source_model`) — poids par weight hint, sinon équipartition ;
- somme des poches par symbole, sans levier : chaque poche plafonne à sa
  tranche.

Le mode `base` historique (un insight par symbole, dernier émetteur gagnant)
reste disponible via `additive=False` pour les comparaisons A/B. Le
reconstructeur du mode intent lit les insights actifs à travers l'algorithme :
`additive=True` exige `algorithm=self` (le constructeur refuse le silence).

## Câblage sur QC Cloud — bibliothèque de projet

Ce dossier est un projet QC comme les autres. Pour qu'un projet consommateur
compile sur QC Cloud, il faut l'attacher une fois comme **bibliothèque de
projet** (fonctionnalité « Add Library » du panneau Projet —
[docs](https://www.quantconnect.com/docs/v2/cloud-platform/projects/shared-libraries)),
puis importer dans le `main.py` du consommateur :

```python
from SharedPCM.pouches_pcm import MultiStrategyPouchesPCM
```

L'attachement est un geste d'interface (ni l'API REST ni le MCP ne l'exposent).
Tant qu'il n'est pas fait, la compilation du consommateur échoue sur
l'`ImportError` ci-dessus — échec fermé et explicite, jamais une replique
silencieuse du module.

**Contrainte de nommage (mesurée au 2026-10-17) :** QC Cloud refuse les
underscores dans les noms de bibliothèque (« Only letters, numbers and '/' are
supported in library names ») — le dossier s'appelle donc `SharedPCM`, sans
underscore, et le chemin d'import suit. Une bibliothèque cloud homonyme
`Library/SharedPCM` porte ce module ; la compile du consommateur et le backtest
d'équivalence sont cités dans la PR d'extraction.

## Consommateurs

| Projet | Poches (`alpha_allocations`) | Rebalance |
| --- | --- | --- |
| `Framework_Composite_EMATrend` | EMACross 0.70 / TrendStocks 0.30 | 7 j |
| `Framework_Composite_MomentumRegime` | SectorMomentum 0.60 / RegimeSwitching 0.40 | 31 j |
| `Framework_Composite_FamaFrenchAllWeather` | FamaFrench 0.20 / AllWeather 0.80 | 31 j |
| `Framework_Composite_TrendWeather` | TrendStocks 0.75 / AllWeather 0.25 | 31 j |
| `composite-c1-multiasset` | Momentum 1/3 / MACD 1/3 / RelStrength 1/3 (sous-classe `CappedPouchesPCM`, plafond de 40 % par ligne) | 7 j |

Duplication restante hors périmètre de l'extraction (copies pédagogiques ou
projets autonomes, à migrer par tranches séparées) — quatre projets portent
encore un `portfolio_construction.py` déclarant `MultiStrategyPCM` :
`TrendWeatherPointInTime`, `TrendStocks-Alpha`, `EMA-Cross-Alpha` et
`MomentumRegime-AdaptiveWeights` ; s'y ajoutent
`partner-course-quant-trading/kit-transitoire` et la cellule pédagogique du
notebook `QC-Py-14` (déclarée copie d'enseignement).
