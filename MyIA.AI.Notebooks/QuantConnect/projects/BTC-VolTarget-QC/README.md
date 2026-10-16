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

## Mesures et verdict (fenêtre 2016-01-01 → 2026-09-30, QC Cloud projet 37950433)

Quatre runs à frais du courtier (`fee_mult` = 1), un essai court d'instrumentation d'abord (2016-Q1 : 12 ordres, +6,05 %, pire baisse 8,1 %). Statistiques rapportées par QC :

| Mode | Sharpe | CAGR | Pire baisse | Profit total | Ordres |
|---|---|---|---|---|---|
| `base` (candidat) | 1,259 | 37,4 % | 55,3 % | +2 951 % | 736 |
| `hold-btc` | 1,522 | 63,2 % | 82,9 % | +19 302 % | 1 |
| `spy` | 0,677 | 21,2 % | 46,1 % | +689 % | 3 |
| `sixty40` | 0,481 | 9,3 % | 21,3 % | +161 % | 205 |

Sur les séries du contrat d'ombre (une valeur de portefeuille par barre journalière, `significance.py` : bootstrap circulaire **apparié** par blocs de 21 séances, 10 000 tirages, graine 18921, Holm) :

| Référence | Sharpe (série ombre, dates communes) | Δ Sharpe | p brut | p Holm |
|---|---|---|---|---|
| `hold-btc` (3 925 barres) | 1,070 vs 1,098 | +0,028 | 0,417 | 0,834 |
| `sixty40` (3 632 barres) | 1,121 vs 1,145 | +0,024 | 0,488 | 0,834 |

**Verdict : NO BEATS** — aucune p Holm < 0,05, les différences sont positives mais bien en deçà du seuil. Grille et frais doublés non lancés (réservés au cas p < 0,05 par le protocole).

Mesures complémentaires : exposition moyenne réalisée `w_bar` ≈ **0,46** (pente de la régression rendement poche ~ rendement BTC ; ~54 % du temps en liquidités) ; corrélation hebdomadaire au 60/40 : **+0,20** (`hold-btc` : +0,18 — le dimensionnement ne décorrèle pas mieux que la détention simple). Sous-périodes `base` − `hold-btc` : +0,20 (2016-2020), −0,05 (2021-2023), −0,10 (2024 → 2026-09) — l'avantage éventuel se concentre sur la seule première période.

**Lecture honnête** : le vol targeting fait ce qu'il annonce — il **façonne le risque, il ne crée pas de rendement**. Pire baisse ramenée de 83 % à 55 %, au prix de 26 points de CAGR abandonnés et d'un Sharpe inchangé en significativité. Pour un panier qui veut une poche BTC, la question pertinente devient celle du budget de risque alloué, pas celle d'un edge de timing — la détention simple domine ce candidat sur cette fenêtre.

Note d'instrument : le bootstrap de `significance.py` a été corrigé avant tout verdict (départs de blocs uniformes i.i.d. — la version systématique tessellait le cercle quand pgcd(21, n) = 1 et produisait des p dégénérés ∈ {0 ; 0,5 ; 1}). Calibration mesurée sur 15 paires indépendantes de même loi : moyenne 0,458, dispersion (0,04 ; 0,85). Aucune p-valeur du verdict n'a été calculée avec la version défectueuse.

La série `base` est gelée à la date du verdict (2026-10-17) et inscrite au registre d'ombre (#18923) — le hors-échantillon s'accumule sans être choisi après coup.

## Sources

- Moskowitz, Ooi, Pedersen — « Time Series Momentum » (2012, JFE 104(2)) : l'origine du constat vol/rendement qui motive le dimensionnement par le risque.
- Moreira & Muir — « Volatility-Managed Portfolios » (2017, JF 72(4)) : la gestion d'exposition par volatilité réalisée, mesurée sur des poches diversifiées.

Part of #19821 (protocole de mesure commun, candidats à pré-enregistrer).
