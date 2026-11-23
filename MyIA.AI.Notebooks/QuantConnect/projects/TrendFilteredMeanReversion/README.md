# Stratégie TrendFilteredMeanReversion

**Statut** : ❌ PLAFOND STRUCTUREL CONFIRMÉ — Contre-exemple à des fins pédagogiques

## Performance

Mesure QC Cloud du `main.py` actuel (v1.0) sur sa fenêtre codée, avec un témoin SPY achat-conservation dans les mêmes conditions (modèle de courtage déclaré dans le code, frais inclus, données journalières) :

| Métrique | TrendFilteredMeanReversion | Témoin SPY |
|----------|----------------------------|------------|
| Sharpe Ratio | **-0** (arrondi QC au millième : négatif, inférieur à 0,0005 en valeur absolue) | 0,535 |
| CAGR | 2,99 % | 12,99 % |
| Drawdown maximum | 11,4 % | 33,5 % |
| PSR | 0,006 % | 3,08 % |
| Beta | 0,112 | 0,994 |
| Trades clos | 84 (8,4 par an) | — |
| Taux de réussite | 70,2 % (59 sur 84) | — |
| Gain moyen / perte moyenne | 1,16 % / -1,52 % | — |
| Durée moyenne d'un trade | 4,4 jours | — |
| Période | 2015-01-01 → 2024-12-31 | 2015-01-01 → 2024-12-31 |

*Backtests du 2026-11-12 : projet 39308942, backtest `05c344893b49fb8f28b303efb85f14cb` (stratégie) ; projet 39308949, backtest `e52d55fd4812e0542585f11a3c9ecca4` (témoin SPY). La position est ouverte environ 10 % des jours calendaires de la fenêtre (somme des durées des 84 trades).*

Les chiffres publiés jusqu'ici (Sharpe -0,016, CAGR 3,4 %, MaxDD 11,4 %, « 2015-2026 ») ne citaient ni projet ni date, et annonçaient une fenêtre plus longue que celle du code. La mesure ci-dessus les remplace ; le tableau des versions plus bas reste un historique non re-mesuré.

## Pourquoi cette stratégie a échoué

### Cause racine : arbitrage fréquence vs. qualité du signal

Cette stratégie combine :
1. **RSI(2) < 10** : signal de survente extrême (repli)
2. **Filtre SMA200** : ne trader qu'en marché haussier
3. **Time stop 5 jours** : sortie si le signal ne se matérialise pas

**Le problème** : c'est un **signal valide** (70 % de trades gagnants mesurés) mais qui survient **trop rarement** (8,4 trades par an mesurés).

### Décomposition des performances

Historique des itérations, chiffres non datés et sans projet cité, annoncés sur « 2015-2026 » et non re-mesurés (seule la v1.0 est le code actuel, mesurée plus haut) :

| Version | Signal | Sharpe | Transactions/an | Taux de réussite | Max DD |
|---------|--------|--------|-----------------|------------------|--------|
| v1.0 | RSI(2) < 10 | -0.016 | ~9 | 73% | 11.4% |
| v2.0 | RSI(2) < 20 | -0.002 | ~31 | 71% | 16.2% |
| v3.0 | RSI(3) < 15 | -0.050 | ~12 | 72% | 10.3% |
| v4.0 | Multi-instrument (3x) | -0.129 | ~27 | 65% | 18.5% |

**Schéma observé** :
- **Signal strict** (RSI<10) = haute qualité mais trop rare
- **Signal laxiste** (RSI<20) = plus fréquent mais de moindre qualité
- **Multi-instrument** = plus de transactions mais dilue l'avantage + risque de corrélation accru

### Cause de l'échec : cash drag (coût de détention de liquidités)

| Métrique | Valeur |
|----------|--------|
| Temps en liquidités | ~90 % (mesuré : position ouverte ~10 % des jours calendaires) |
| Rendement du cash (2015-2024) | ~0% (aucun intérêt perçu) |
| Taux sans risque (T-bills) | 2-5% annualisé |

**Le problème structurel** :
- La stratégie est en liquidités environ 90 % du temps
- Le cash rapporte 0 % tandis que le sans risque (T-bills) rapporte 2-5 %
- Ce **coût d'opportunité** crée un alpha négatif
- Même avec 70 % de trades gagnants, le cash drag détruit la performance

### Pourquoi le multi-instrument a échoué (v4.0)

Nous avons testé SPY + QQQ + IWM pour augmenter les opportunités :
- **Hypothèse** : 3x plus d'instruments = 3x plus de signaux
- **Réalité** : les signaux sont corrélés (les 3 se déclenchent ensemble) + la qualité individuelle baisse
- **Résultat** : Sharpe -0.129 (pire que la baseline)

### Leçons apprises

1. **Qualité vs. fréquence du signal est un véritable arbitrage** : on ne peut pas avoir les deux
2. **Le cash drag n'est pas théorique** : être en liquidités ~90 % du temps = -2 à -5 % annualisé vs. T-bills
3. **Multi-instrument ≠ signaux indépendants** : des marchés corrélés n'augmentent pas les vraies opportunités
4. **Savoir quand s'arrêter** : nous avons testé RSI(2), RSI(3), RSI(7), multi-instrument — tous ont échoué
5. **Dépendance au régime** : cette stratégie ne fonctionne qu'en marchés haussiers avec replis francs (rares)

## Quand cette approche PEUT fonctionner

Des stratégies similaires peuvent fonctionner en :
- **Marchés baissiers** : les replis de RSI sont plus fréquents
- **Forte volatilité** : lectures RSI plus extrêmes
- **Screening d'actions individuelles** : sélectionner les meilleurs setups (non systématique)
- **Autres classes d'actifs** : crypto, FX où le retour à la moyenne est plus fort

**Pour SPY (2015-2024, fenêtre mesurée)** : plafond structurel confirmé.

## Valeur pédagogique

Cette stratégie illustre :
- ❌ L'importance de la **fréquence du signal** dans la conception de stratégie
- ❌ Le **cash drag** comme coût caché (notamment vs. taux sans risque)
- ❌ Quand déclarer un **plafond structurel** (après tests exhaustifs)
- ❌ Le **piège des 70 % de réussite** : taux de réussite élevé ≠ rentabilité si les trades sont trop rares

## Références

- **OPTIMIZATION_BACKLOG.md** : historique complet des itérations (v1.0-v4.0)
- **MeanReversion** : stratégie similaire avec des paramètres différents

---

**Note** : cette stratégie a un signal valide mais est structurellement non rentable à cause du cash drag. Elle sert de leçon sur le coût d'opportunité et la fréquence du signal.

---

*Version anglaise préservée dans [README.en.md](README.en.md).*
