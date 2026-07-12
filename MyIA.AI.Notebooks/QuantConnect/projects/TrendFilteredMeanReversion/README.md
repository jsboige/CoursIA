# Stratégie TrendFilteredMeanReversion

**Statut** : ❌ PLAFOND STRUCTUREL CONFIRMÉ — Contre-exemple à des fins pédagogiques

## Performance

| Métrique | Valeur |
|----------|--------|
| Sharpe Ratio | **-0.016** |
| CAGR | 3.4% |
| Drawdown maximum | 11.4% |
| Période | 2015-2026 |

## Pourquoi cette stratégie a échoué

### Cause racine : arbitrage fréquence vs. qualité du signal

Cette stratégie combine :
1. **RSI(2) < 10** : signal de survente extrême (repli)
2. **Filtre SMA200** : ne trader qu'en marché haussier
3. **Time stop 5 jours** : sortie si le signal ne se matérialise pas

**Le problème** : c'est un **signal valide** (73 % de taux de réussite) mais qui survient **trop rarement** (~9 transactions/an).

### Décomposition des performances

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
| Temps en liquidités | ~85% |
| Rendement du cash (2015-2026) | ~0% (aucun intérêt perçu) |
| Taux sans risque (T-bills) | 2-5% annualisé |

**Le problème structurel** :
- La stratégie est en liquidités 85 % du temps
- Le cash rapporte 0 % tandis que le sans risque (T-bills) rapporte 2-5 %
- Ce **coût d'opportunité** crée un alpha négatif
- Même avec 73 % de taux de réussite, le cash drag détruit la performance

### Pourquoi le multi-instrument a échoué (v4.0)

Nous avons testé SPY + QQQ + IWM pour augmenter les opportunités :
- **Hypothèse** : 3x plus d'instruments = 3x plus de signaux
- **Réalité** : les signaux sont corrélés (les 3 se déclenchent ensemble) + la qualité individuelle baisse
- **Résultat** : Sharpe -0.129 (pire que la baseline)

### Leçons apprises

1. **Qualité vs. fréquence du signal est un véritable arbitrage** : on ne peut pas avoir les deux
2. **Le cash drag est réel** : être en liquidités 85 % du temps = -2 à -5 % annualisé vs. T-bills
3. **Multi-instrument ≠ signaux indépendants** : des marchés corrélés n'augmentent pas les vraies opportunités
4. **Savoir quand s'arrêter** : nous avons testé RSI(2), RSI(3), RSI(7), multi-instrument — tous ont échoué
5. **Dépendance au régime** : cette stratégie ne fonctionne qu'en marchés haussiers avec replis francs (rares)

## Quand cette approche PEUT fonctionner

Des stratégies similaires peuvent fonctionner en :
- **Marchés baissiers** : les replis de RSI sont plus fréquents
- **Forte volatilité** : lectures RSI plus extrêmes
- **Screening d'actions individuelles** : sélectionner les meilleurs setups (non systématique)
- **Autres classes d'actifs** : crypto, FX où le retour à la moyenne est plus fort

**Pour SPY (2015-2026)** : plafond structurel confirmé.

## Valeur pédagogique

Cette stratégie illustre :
- ❌ L'importance de la **fréquence du signal** dans la conception de stratégie
- ❌ Le **cash drag** comme coût caché (notamment vs. taux sans risque)
- ❌ Quand déclarer un **plafond structurel** (après tests exhaustifs)
- ❌ Le **piège du 73 % de réussite** : taux de réussite élevé ≠ rentabilité si les trades sont trop rares

## Références

- **OPTIMIZATION_BACKLOG.md** : historique complet des itérations (v1.0-v4.0)
- **MeanReversion** : stratégie similaire avec des paramètres différents

---

**Note** : cette stratégie a un signal valide mais est structurellement non rentable à cause du cash drag. Elle sert de leçon sur le coût d'opportunité et la fréquence du signal.

---

*Version anglaise préservée dans [README.en.md](README.en.md).*
