# Option-Wheel

**Classe d'actifs :** Actions US (options sur SPY)
**ID projet Cloud :** 34881290

## Description

Stratégie du « wheel » (roue) sur options SPY : vend des puts hors-cours
(OTM 5 %, ~21 DTE) pour encaisser la prime. En cas d'assignation, vend des
calls couverts sur la position SPY résultante. Cycle complet : put nu →
assignation → call couvert → cession → put nu.

Filtre de régime VIX : désactive la vente de puts quand VIX > 20 (volatilité
élevée / stress de marché) ; vente agressive quand VIX < 15. Puts cash-secured
avec exposition maximale 80 % et marge désactivée pour la sécurité.
Backtest en résolution minute, compte Cash IBKR.

Paramètres clés (`main.py`, vérifiés firsthand) :
- Période : 2015-01-01 → 2024-12-31 (10 ans, inclut crash COVID + récupération)
- Capital initial : 1 000 000 $
- DTE : 21 jours (`days_to_expiry`)
- OTM : 5 % (`otm_threshold`)
- Exposition max : 80 % (`max_exposure_fraction`)
- Filtre VIX : skip puts si VIX > 20 ; agressif si VIX < 15

## Comment exécuter

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/Option-Wheel"`
```bash
lean backtest --project .
```

**QC Cloud :** Ouvrir le projet 34881290 dans l'IDE QuantConnect et cliquer sur « Backtest ».

## Métriques de backtest (2015-2026, run courant du registre)

| Métrique | Valeur |
|----------|--------|
| Sharpe Ratio | 0.529 |
| CAGR | 12.78% |
| Max Drawdown | 26.4% |
| Net Profit | 286.0% ($2 167 801) |
| PSR | 10.63% |

> **Provenance** : run courant du registre — `docs/qc/qc-strategies-status.md` l.280
> (2015-2026, 2821 j., Needs-improvement : « bon profil long-terme mais edge non
> significative »). Run précédent, supersédé : backtest QC Cloud
> `4b8c217c3927ab637379f8641f676679` (2026-08-06, projet 34881290, IBKR Cash, capital
> initial 1 000 000 $, résolution minute, 2015-01-01 → 2024-12-31, 2516 j., 1029 ordres,
> DTE/OTM 21 j/5 % : Sharpe 0.575 / CAGR 13.088 % / MaxDD 26.5 % / PSR 4.23 % /
> NP 242.4 %) — remplacé par le run 2015-2026 ci-dessus.
>
> **Lecture honnête** : le wheel est une stratégie *très populaire* dans la littérature
> de « revenu passif par les options », souvent présentée comme quasi-garantie. Les
> chiffres montrent le contraire. Un CAGR de 12,8 % sur 2015-2026 est **comparable au
> buy & hold de SPY** sur la même période (≈ 13-14 %), mais avec un **Sharpe de 0,529
> nettement inférieur** à celui du benchmark (~0,7-0,8) et un **PSR de 10,6 %**
> catastrophique — l'edge statistique est nul, très loin du seuil de confiance de
> 50 % (et a fortiori 95 %). Le Max Drawdown de 26,4 % est par
> ailleurs substantiel.
>
> En d'autres termes : la vente de primes d'options n'extrait **pas d'alpha** ici ;
> elle réplique approximativement l'exposition long-SPY en ajoutant de la complexité,
> des frais de transaction et un risque d'assignation. **C'est un contre-exemple
> pédagogique** à l'encontre du narratif « wheel = revenu garanti ». La valeur
> pédagogique est dans la démonstration (via filtre VIX, gestion cash-secured,
> cycle put→call) du *mécanisme* du wheel, pas dans un quelconque alpha. Comparer
> avec EMA-Cross-Stocks (même univers US, Sharpe 0.991 mais beta Mag7) et
> EMA-Cross-Alpha (contre-exemple framework Alpha Model, Sharpe -0,01).

## Fichiers

- `main.py` - Stratégie wheel (put nu → call couvert, filtre VIX, gestion exposition)
- `research.ipynb` - Analyse des primes d'options et optimisation DTE/OTM
- `quantbook.ipynb` - Recherche QC (chaînes d'options, grecques)
- `wheel_analysis.png` - Visualisation d'analyse
- `README.en.md` - Version anglaise (original historique, non mise à jour)

## Références

- Wheel strategy : collection systématique de primes via vente put/call couvert
- Brokerage : Interactive Brokers (modèle compte Cash, marge désactivée)
- Réf : Tastytrade research sur delta/DTE pour la vente de primes d'options
