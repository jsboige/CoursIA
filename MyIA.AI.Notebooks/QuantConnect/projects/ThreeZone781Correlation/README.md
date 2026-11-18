# ThreeZone781Correlation

Corrélations hebdomadaires entre la stratégie 781 (réimplémentée) et les
paniers ETF des allocations du dépôt (issue
[jsboige/CoursIA#18905](https://github.com/jsboige/CoursIA/issues/18905),
point 3). Projet compagnon de
[`ThreeZoneSPYDrawdownRotation`](../ThreeZoneSPYDrawdownRotation/).

## Méthode

L'algorithme principal **est** la 781 (même logique que le projet
principal) : sa série de retours hebdomadaires est son equity. Chaque
allocation du dépôt est suivie en **portefeuille ombre** (poids cibles,
séparé du portefeuille réel) :

| Panier | Poids | Source dépôt |
|--------|-------|--------------|
| `VT2` | SPY/QQQ/IEF/GLD poids égaux | `Cloud-VolTargeting` variante 2 (proxy déclaré : l'ERC réel est approximé par poids égaux) |
| `AW` | SPY 30 % / IEF 30 % / GLD 30 % / XLP 10 % | `AllWeather` v5.0 |
| `TW` | idem `AW` | sleeve AllWeather de `Framework_Composite_TrendWeather` ; la jambe 75 % stock-picking n'est **pas** répliquée (déclaré) |

Retours hebdomadaires échantillonnés le vendredi ; corrélations de Pearson
calculées en fin de backtest sur la période pleine et par année civile.
Sorties : statistiques custom (`corr_VT2`, `corr_AW`, `corr_TW`) et
`781_corr.json` dans l'ObjectStore du projet.

**Fenêtre par défaut** : 2018-01-01 → 2024-12-31 = fenêtre commune aux
trois allocations du dépôt (VT2 2018-2025, AW 2015-2024, TW 2015-2025).

## État

Projet créé (cloud `37320712`), déploiement + run de test au cycle suivant.