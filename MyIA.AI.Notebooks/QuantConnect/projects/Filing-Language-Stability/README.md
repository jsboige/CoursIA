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

## Fichiers

- `main.py` — Stratégie (univers liquidité 100 → similarité Brain top 25 → max-Sharpe 12 mois, mensuel)
- `research.ipynb` — Vérificateur local indépendant : extraction réelle des Item 1A depuis SEC EDGAR, similarité TF-IDF cosinus, ranking du panier (EXEC_PROVED, 0 erreur)

## Références

- Sun, E. X., *Filing language stability as a selection signal*, qc-research #20966
- Cohen, L., Malloy, C., & Nguyen, L., *Lazy Prices*, Journal of Finance 75(3), 2020, DOI 10.1111/jofi.12885
- Dataset : Brain Language Metrics on Company Filings (QuantConnect)
