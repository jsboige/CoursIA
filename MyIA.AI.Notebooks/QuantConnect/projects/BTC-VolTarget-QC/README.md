# BTC-VolTarget-QC — exposition BTC pilotée par la volatilité

Candidat de la ligue de stratégies (#19821), issue de recherche **#21143** — le protocole y est pré-enregistré avant tout backtest. Cette page en donne l'état courant ; les mesures et le verdict y seront consignés à mesure des runs.

## Idée

Détenir BTC avec une exposition inversement proportionnelle à sa volatilité réalisée. L'hypothèse n'est **pas** un edge directionnel — les mesures de timing crypto du dépôt (cohorte BTC tranche 11, BitcoinRegimeGate #19929, BTC-ETH-Rotation #20189, momentum crypto transversal #20214) sont toutes NO BEATS — mais celle du vol targeting : lisser le risque d'un actif volatil sans en prédire la direction, et livrer au panier une poche au profil de pertes borné, faiblement corrélée au cœur actions.

Distinct de `BitcoinRegimeGate-QC` : là-bas le BTC sert de **signal** pour allouer QQQ/SHY (face crypto → equity) ; ici le BTC est l'**actif détenu**, sa volatilité ne pilote que sa propre taille.

## Règle (pré-enregistrée)

Évaluation quotidienne à la clôture, marché BTC 24/7 :

- `sigma_hat` : EWMA des rendements journaliers BTC, span 30 barres, annualisée en racine de 365 ;
- cible `w = clip(sigma_etoile / sigma_hat, 0, 1)`, `sigma_etoile = 30 %` — jamais de levier, le reste en liquidités ;
- bande de trading : ordre seulement si `|w_cible − w_courant| ≥ 0,05` ;
- exécution : vente d'abord, puis achat borné aux liquidités disponibles après les sorties — l'ordre d'achat ne peut pas être refusé pour pouvoir d'achat insuffisant (mécanisme mesuré dans #20388).

Si `sigma_hat ≤ 0` (prix plats), la cible précédente est conservée.

## Instrumentation

`main.py` expose par paramètres : `start`, `end`, `mode` (`base`, `hold-btc`, `spy`, `sixty40`), `fee_mult` (défaut 1), `sigma_etoile`, `vol_span`, `trade_band`. Le graphique `shadow` porte une valeur par barre journalière (`e0..e4` : portefeuille ; `b0..b4` : clôture BTCUSD) — contrat du rejeu en ombre #18923.

Architecture : IBKR pour les jambes equity des références, BTC en données journalières Bitfinex — la même que BitcoinRegimeGate-QC (#19929). Frais : modèle de courtier par défaut de Lean, mis à l'échelle par `fee_mult` (le mécanisme de #19929, identique sur tous les modes).

## Mesures

Pré-enregistrées dans #21143 : fenêtre 2016-01-01 → 2026-09-30, essai court d'instrumentation d'abord, puis `base`, `hold-btc`, `sixty40` (références du verdict) et `spy` (descriptive). Sharpe à taux sans risque nul, CAGR, pire baisse, rotation annuelle, frais annuels, ordres, exposition moyenne `w_bar`. Verdict : bootstrap circulaire par blocs de 21 séances, 10 000 tirages, graine 18921, correction de Holm contre `hold-btc` et `sixty40` — la même règle que #19587. Grille et frais doublés seulement si une p Holm passe sous 0,05.

**État : instrumentation posée, runs non encore lancés.** Le verdict sera consigné ici et dans #21143, puis la série `base` gelée au registre d'ombre (#18923), quel que soit le verdict.

## Sources

- Moskowitz, Ooi, Pedersen — « Time Series Momentum » (2012, JFE 104(2)) : l'origine du constat vol/rendement qui motive le dimensionnement par le risque.
- Moreira & Muir — « Volatility-Managed Portfolios » (2017, JF 72(4)) : la gestion d'exposition par volatilité réalisée, mesurée sur des poches diversifiées.

Part of #19821 (protocole de mesure commun, candidats à pré-enregistrer).
