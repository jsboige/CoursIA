# Filing-Language-Stability (qc-research #20966)

**Classe d'actifs :** Actions US (top 100 liquides → top 25 par similarité de langage des filings)
**ID projet Cloud :** 36331851

## Description

Jambe longue de l'anomalie *Lazy Prices* (Cohen, Malloy & Nguyen, Journal of Finance 75(3), 2020) : les entreprises dont les sections « Risk Factors » (Item 1A) des filings 10-K/10-Q changent peu d'une année sur l'autre sur-performent. La stratégie classe les 100 actions US les plus liquides par similarité de langage (dataset **Brain Language Metrics on Company Filings**, section risk-factors avec repli rapport complet), tient le top 25 en poids max-Sharpe (fenêtre 12 mois de rendements quotidiens) et rebalance mensuellement. Long-only, sans levier.

Portage fidèle de l'article « Filing language stability as a selection signal » (Emily Xinyu Sun, qc-research #20966) — évaluation de l'issue #15392 (verdict **NOUVEAU** : le hook filings-NLP était absent du bouquet).

## Comment exécuter

**QC Cloud :** projet 36331851 (backtest janv. 2020 - juin 2026, daily).
**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/Filing-Language-Stability"` (nécessite l'abonnement Brain Language Metrics).

## Métriques de backtest

**État : jambe Cloud bloquée par l'entitlement du dataset (verdict RECOVERABLE-USER-HAND).**

- Le port compile vert (BuildSuccess ×3 sur le projet Cloud 36331851) mais le run janv. 2020 - juin 2026 (v3) termine avec **0 sélection, 0 ordre** : l'univers `BrainCompanyFilingLanguageMetricsUniverseAll` ne délivre **aucun point de données** dans cette organisation.
- Sonde dédiée (backtest 2024 : le sélecteur `raise` dès le premier filing reçu) : **complétion propre, 0 ordre** — le sélecteur n'a jamais été appelé avec des données. Diagnostic : le dataset Brain Language Metrics n'est pas activé pour l'org (aucun autre projet « Brain » dans les 254 projets).
- Action débloquante (user, one-time) : activer *Brain Language Metrics on Company Filings* dans l'organisation QuantConnect, puis relancer le backtest sur le projet 36331851.
- Chiffres de l'article (source, non mesurés ici) : Sharpe **0.558** (janv. 2020 - juin 2026) vs SPY buy-and-hold **0.533** ; 9/25 combinaisons du sweep (36 %) battent le benchmark ; l'auteure attribue le résultat principalement à la **fenêtre de l'optimiseur** max-Sharpe plutôt qu'à la largeur du panier.

## Variante libre EDGAR-2

`main_edgar.py` remplace la dépendance Brain par une série historique dérivée des
endpoints publics SEC. `edgar_signal.build_history` lit le bloc récent **et** les
archives `submissions-*.json`, ordonne tous les 10-K, puis calcule chaque paire
annuelle adjacente. Une paire entre dans LEAN à son `available_at`, calculé depuis
le timestamp d'acceptation SEC le plus tardif : ni la période comptable ni la
date seule ne servent d'horloge au backtest.

Protocole borné :

- panier fixe `AAPL, MSFT, KO, WMT, GE`, identique au smoke EDGAR-1 ;
- Item 1A de 10-K uniquement, sans repli sur le rapport complet ;
- OOS du 1er janvier 2022 au 31 décembre 2024 ;
- `mode=signal` : top 2 des similarités disponibles, poids égaux ;
- `mode=equal` : les mêmes actions dont l'extraction produit une série valide,
  en poids égaux et sans classement (quatre titres sur ce run ; GE est exclu des
  deux jambes après 9/9 échecs explicites d'extraction) ;
- coûts explicites de 5 points de base par ordre sur le notionnel ;
- SPY reste le second benchmark externe.

Le CSV dérivé `edgar_signals.csv`, les textes SEC et le cache HTTP restent sous
`runs/` / `cache/`, tous deux gitignorés. La matérialisation appelle
`build_history(ticker, cik, since=date(2016, 1, 1), until=date(2024, 12, 31))`
pour chacun des cinq couples ticker/CIK définis dans
`tests/test_smoke_sec_real.py::BASKET`, trie les paires par
`(available_at, ticker)`, puis appelle `write_csv` et `write_cloud_module`. Le
module Python dérivé accepté par QC est chargé uniquement dans le projet Cloud
36331851. Cette expérience
ne reproduit donc pas l'univers de 100 titres de l'article : elle teste si la
sélection linguistique ajoute quelque chose au **même panier** de cinq titres.

### Résultat OOS Cloud (2022-01-01 → 2024-12-31)

Les trois runs ont terminé (`progress=1`) sur 753 dates négociables, avec le
même modèle de frais actions à 5 bps :

| Jambe | Backtest Cloud | Ordres | Sharpe | CAGR | MaxDD |
|---|---|---:|---:|---:|---:|
| EDGAR top 2 | `b99f7afcff7ec09e2d522ab915a56da7` | 66 | 0,151 | 7,482 % | 31,4 % |
| Panier éligible égal | `716eee17e4e77d50e999c8eadc0b6fb9` | 117 | 0,429 | 13,390 % | 18,4 % |
| SPY | `e7f6ef5f242445b6f995e3cee14626a0` | 3 | 0,193 | 8,607 % | 24,5 % |

**Verdict : NO BEATS.** La sélection EDGAR est dominée OOS par les deux
contrôles : Sharpe inférieur de 0,278 au panier égal et de 0,042 à SPY, CAGR
plus faible, drawdown plus profond. Aucun test de significativité additionnel
ne peut transformer cette domination brute en `BEATS` ; le résultat ne doit pas
être extrapolé au véritable univers de 100 titres de l'article.

Limites point-in-time connues : `_next_us_session` ne modélise que les week-ends
et les timestamps SEC sont conservés sans fuseau explicite. Dans ce backtest à
résolution quotidienne, les observations ne sont consommées que lors d'un
`OnData` postérieur, ce qui rend ces imprécisions conservatrices en pratique ;
elles restent à formaliser avant tout passage intraday.

## Fichiers

- `main.py` — stratégie Brain originale, laissée byte-identique
- `main_edgar.py` — variante EDGAR libre, panier fixe, coûts 5 bps et baseline égale
- `edgar_signal.py` — acquisition, extraction Item 1A et séries historiques point-in-time
- `tests/test_edgar_backtest_cpu.py` — invariants archives, adjacence, anti-look-ahead et CSV
- `research.ipynb` — vérificateur EDGAR-1, laissé byte-identique

## Références

- Sun, E. X., *Filing language stability as a selection signal*, qc-research #20966
- Cohen, L., Malloy, C., & Nguyen, L., *Lazy Prices*, Journal of Finance 75(3), 2020, DOI 10.1111/jofi.12885
- Dataset : Brain Language Metrics on Company Filings (QuantConnect)
