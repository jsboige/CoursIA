# Option-Wheel

**Classe d'actifs :** Actions US (options sur SPY)
**ID projet Cloud :** 34881290

## Description

Stratégie du « wheel » (roue) sur options SPY : vend des puts hors-cours
(OTM 5 %, ~21 DTE) pour encaisser la prime. En cas d'assignation, vend des
calls couverts sur la position SPY résultante. Cycle complet : put nu →
assignation → call couvert → cession → put nu.

Le code interrompt le traitement des ordres lorsque le VIX dépasse 20. Il déclare aussi
un seuil bas à 15, mais ne l'utilise pas pour augmenter la fréquence ou la taille des
ventes. Les puts sont cash-secured, avec une exposition maximale configurée à 80 % et
un contrôle de liquidités avant l'ordre. Le backtest utilise le modèle IBKR Cash et
une résolution minute.

Paramètres clés (`main.py`, vérifiés firsthand) :
- Période : 2015-01-01 → 2024-12-31 (10 ans, inclut crash COVID + récupération)
- Capital initial : 1 000 000 $
- DTE : 21 jours (`days_to_expiry`)
- OTM : 5 % (`otm_threshold`)
- Exposition max : 80 % (`max_exposure_fraction`)
- Filtre VIX : arrêt du traitement des ordres si VIX > 20 ; le seuil bas 15 est déclaré, mais non utilisé

## Comment exécuter

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/Option-Wheel"`
```bash
lean backtest --project .
```

**QC Cloud :** Ouvrir le projet 34881290 dans l'IDE QuantConnect et cliquer sur « Backtest ».

## Métriques de backtest (2015–2024, run QC Cloud vérifiable)

| Métrique | Valeur |
|----------|--------|
| Sharpe Ratio | 0.575 |
| CAGR | 13.088% |
| Max Drawdown | 26.500% |
| Net Profit (`totalNetProfit`) | 242.406% |
| Net Profit (`netProfitAbsolute`) | $2 127 458.45 |
| PSR | 4.230% |

> **Provenance** : backtest QC Cloud `4b8c217c3927ab637379f8641f676679` (2026-08-06,
> projet 34881290, IBKR Cash, capital initial 1 000 000 $, résolution minute,
> 2015-01-01 → 2024-12-31, 2516 j., 1029 ordres, DTE/OTM 21 j/5 %), **relu via MCP
> `qc-mcp-lite` le 2026-10-08** (#19737) — seul run de l'historique du projet.
>
> **Écart `netProfit` tranché (re-mesure #19737, 2026-10-08)** : le run
> « 2821 j. (2015–2026), NP 286.0 % ($2 167 801) » que portait le registre n'est
> **plus reproductible** — le `main.py` courant (cloud et dépôt, identiques) porte
> `set_end_date(2024, 12, 31)`, et l'historique du projet ne contient aucun run
> 2015–2026. Sa paire (% ; $) ne réconciliait pas (286 % × 1 M$ = 2.86 M$ ≠
> 2.17 M$) et **aucun des deux champs n'est vérifiable** : la ligne du registre a été
> réalignée sur la mesure vérifiable ci-dessus. La même divergence **% ≠ $ frappe
> aussi le run vérifiable** : `totalNetProfit` 242.406 % (→ 2.42 M$ attendus) vs
> `netProfitAbsolute` $2 127 458.45 (= +212.7 % sur le capital initial) — les deux
> champs QC vivent sur des bases distinctes sur ce run et se citent ensemble,
> sans réconciliation forcée (même annotation que la ligne `OptionsIncome` du
> registre). Re-mesure fraîche d'un run 2015–2026 à revoir quand un nœud
> backtest sera disponible (cluster saturé au 2026-10-08 : `create_backtest`
> rejeté « no spare nodes »).
>
> **Lecture honnête** : le run QC Cloud vérifié (2015–2024, provenance ci-dessus) rapporte un CAGR de 13.088 %, un Sharpe de 0.575, un PSR de 4.230 % et un drawdown maximal de 26.500 %. Ces valeurs décrivent ce run précis. Le README ne cite pas de métrique SPY issue de ce run ; l'estimation approximative de la version précédente ne permet donc pas de conclure à une absence ou à une présence d'alpha.
>
> Le wheel encaisse des primes en vendant des options, mais une prime n'est pas un revenu garanti : si le put est assigné, le portefeuille détient SPY et porte son risque de baisse. La vente ultérieure d'un call couvert peut faire céder ces actions au prix d'exercice et plafonner leur hausse au-delà de ce prix. La limite d'exposition et le contrôle de liquidités encadrent la taille des positions ; les frais de transaction s'inscrivent dans le modèle de courtage IBKR Cash utilisé pour ce run, sans ventilation distincte dans les métriques présentées.
>
> Pour explorer des mécanismes voisins, voir [EMA-Cross-Stocks](../EMA-Cross-Stocks/README.md), qui applique un signal EMA aux grandes valeurs technologiques, et [EMA-Cross-Alpha](../EMA-Cross-Alpha/README.md), qui expose ce type de signal via le framework Alpha Model. Ces projets ont un univers et une construction de portefeuille différents ; leurs métriques ne constituent pas un classement directement comparable au wheel.

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
