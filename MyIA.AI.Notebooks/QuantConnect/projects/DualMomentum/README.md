# DualMomentum Strategy

**Statut** : ⚠️ REMPLACÉE par DualMomentumNoTLT — contre-exemple à visée pédagogique.

## Performance

| Métrique | Valeur | Note |
|----------|--------|------|
| Sharpe Ratio | **0.350** | Plus faible que le remplacement |
| CAGR | 9.2 % | Similaire au remplacement |
| Max Drawdown | **33.6 %** | Pire que le remplacement |
| Période | 2015-2026 | |

## Figures du notebook de recherche

Le notebook [`research.ipynb`](research.ipynb) documente l'analyse du dual momentum : exploration, comparaison des drawdowns entre configurations, robustesse au lookback (H2) et comparaison du Sharpe. La stratégie est remplacée par DualMomentumNoTLT (échec de TLT en 2022) — contre-exemple pédagogique. Provenance détaillée : [`MANIFEST.md`](assets/readme/MANIFEST.md).

**Exploration — cartographier les régimes avant de calibrer.** L'analyse exploratoire examine la dynamique des actifs de l'univers (rendements, volatilité, corrélations) pour distinguer les régimes où le signal de momentum est fiable de ceux où il se retourne — le diagnostic préalable à tout calibrage.

<p align="center">
  <img src="assets/readme/dm-exploration.png" alt="Analyse exploratoire dual-panel 2015-2026 — gauche : rendements cumulés Buy & Hold base 1 sur 11 ans, BND bleu termine ~1.25, EFA orange ~2.20, SPY vert ~4.0 (le grand gagnant) ; droite : volatilité réalisée 63j annualisée, pic commun mars 2020 (COVID) vers 0.60 pour SPY vert, rebond vers 0.34 vers 2024, BND reste la moins volatile (~0.05-0.10) sur toute la période (axe Y gauche 1.0→4.0, axe Y droite 0→0.60, axe X 2016→2026)" width="900"/><br>
  <em>Exploration — dual-panel BND/EFA/SPY 2015-2026 : gauche = rendements cumulés (SPY ~4.0, EFA ~2.20, BND ~1.25), droite = volatilité 63j annualisée avec pic COVID mars 2020 (~0.60 SPY). BND = valeur refuge structurellement moins volatile (cellule 4 du notebook, audit vision c.438).</em>
</p>

**Drawdowns — où la stratégie saigne.** La comparaison des drawdowns entre configurations isole les épisodes de perte maximale (crash COVID de 2020, cycle de hausse des taux de 2022) et montre lesquels pèsent sur le Max DD de 33,6 % — l'origine structurelle qui motive le remplacement par DualMomentumNoTLT.

<p align="center">
  <img src="assets/readme/dm-drawdown.png" alt="Diagnostic complet Dual Momentum vs SPY Buy &amp; Hold 2015-2026, triple-panel empile : haut = equity cumulee Dual Momentum bleu plein termine ~2.25 vs SPY B&amp;H orange tirets termine ~3.9 (le B&amp;H gagne sur la periode complete, rally 2017+2020+2024) ; milieu = Holdings par mois en barres verticales empilees, SPY vert domine quand momentum US positif, EFA bleu sur periodes Europe forte (2017), BND gris sert de refuge lors des stress (2022) ; bas = Drawdown comparison, Dual Momentum bleu aire bleu clair atteint max DD ~-25% vers 2022-2023, SPY B&amp;H orange tirets subit le meme choc mais sur fenetre plus courte (aire bleu clair = periode d'ecart de drawdown), la strategie preserve le capital en stress au prix d'un rendement absolu inferieur (axe Y haut 1.0→4.0, axe Y bas -25%→0%)" width="900"/><br>
  <em>Drawdown — triple-panel equity/holdings/drawdown Dual Momentum vs SPY B&amp;H 2015-2026 : haut = equity (Dual ~2.25 vs SPY ~3.9), milieu = holdings mensuels empilés (SPY/EFA/BND selon régime), bas = drawdown comparison avec max DD Dual Momentum ~-25 % vers 2022-2023. Préserve le capital en stress au prix d'un rendement absolu inférieur (cellule 14 du notebook, audit vision c.438).</em>
</p>

**H2 — robustesse au *lookback*, ou la stabilité du signal.** La deuxième hypothèse teste si la performance tient quand on change la fenêtre de momentum (*lookback period*). Une courbe plate signe un signal robuste ; une courbe qui s'effondre révèle un sur-ajustement à une fenêtre unique.

<p align="center">
  <img src="assets/readme/dm-h2-lookback.png" alt="Test robustesse H2 impact du lookback period, dual-panel bar charts avec 6 lookbacks testes (3, 6, 9, 12, 18, 24 mois) : gauche = Sharpe Ratio barres bleues (axe Y 0→0.85) 3 mois ~0.62, 6 mois ~0.39 le pire, 9 mois ~0.46, 12 mois ~0.46, 18 mois ~0.60, 24 mois ~0.88 le meilleur ; droite = Max Drawdown absolu barres saumon/orange (axe Y 0→0.27) 3 mois ~0.20, 6 mois ~0.24, 9 mois ~0.20, 12 mois ~0.20, 18 mois ~0.27 le pire, 24 mois ~0.24. Conclusion visuelle : lookback 24 mois offre le meilleur couple Sharpe/MaxDD (~0.88 Sharpe pour ~24% DD), tandis que 18 mois est a eviter (Sharpe 0.60 mais DD 27%). Pas de correlation monotone entre longueur du lookback et performance, la robustesse est non-lineaire" width="900"/><br>
  <em>H2 — dual-panel robustesse Sharpe/MaxDD par lookback 3-24 mois : gauche = Sharpe Ratio (axe Y 0→0.85, barres bleues, winner 24 mois ~0.88), droite = Max Drawdown abs (axe Y 0→0.27, barres saumon, pire 18 mois ~0.27). Conclusion : 24 mois = meilleur couple Sharpe/MaxDD, 18 mois à éviter (cellule 16 du notebook, audit vision c.438).</em>
</p>

**Sharpe — rendement ajusté au risque, configuration par configuration.** La comparaison du ratio de Sharpe clôt le diagnostic : elle quantifie le gain (ou la perte) de rendement ajusté au risque au fil des variantes et confirme le verdict — DualMomentum (0,350) dominé par DualMomentumNoTLT (0,469).

<p align="center">
  <img src="assets/readme/dm-sharpe.png" alt="Analyse stabilite temporelle du Sharpe Ratio glissant sur 12 mois (axe Y -2→+5, axe X 2016→2025) : deux courbes plus ligne de reference. Dual Momentum bleu plein oscille autour de SPY B&amp;H orange tirets, mais sous-performe presque toujours (Dual Momentum plus bas sur la majeure partie de la periode). Pics conjoints vers +4.5 en 2017 (rally synchronise) ; Dual Momentum touche -1.8 vers 2018-2019 (sous-performance marquee), remonte vers +1.5 vers 2024, finit vers +1.2 vs SPY ~+1.4 fin 2025. Sharpe=0.5 target ligne horizontale verte pointillee = seuil de rentabilite ajustee au risque, les 2 strategies passent au-dessus en 2017, 2020, 2021, 2024, et plongent en dessous en 2018-2019, 2022-2023 (stress periods ou momentum defavorable). Demontre la forte variance temporelle du momentum (fenetre de lookback glissante = signal bruite)" width="900"/><br>
  <em>Sharpe — line plot unique Sharpe Ratio glissant 12 mois 2016-2025 (axe Y -2→+5) : Dual Momentum bleu plein vs SPY B&amp;H orange tirets, ligne horizontale verte pointillée Sharpe=0.5 target. Pics conjoints +4.5 en 2017, creux Dual Momentum -1.8 vers 2018-2019, fin +1.2 vs SPY +1.4 fin 2025. Forte variance temporelle du momentum (cellule 21 du notebook, audit vision c.438).</em>
</p>

## Pourquoi cette stratégie a été remplacée

### Cause racine : échec du TLT (obligations long terme) en risk-off

Cette stratégie utilise **TLT** comme actif risk-off pendant les marchés baissiers :
- **Hypothèse** : TLT offre une valeur refuge pendant les baisses actions
- **Réalité (2022)** : TLT s'est effondré de -26 % pendant le cycle de hausse des taux
- **Impact** : Max drawdown de 33.6 % (surtout issu de COVID + 2022)

### Le problème COVID (mars 2020)

| Événement | Baisse SPY | Baisse TLT | Impact stratégie |
|-----------|------------|------------|------------------|
| Crash COVID (mars 2020) | -34 % | +2 % | TLT a fonctionné comme prévu |
| Cycle de hausse des taux (2022) | -25 % | **-26 %** | TLT a ÉCHOUÉ comme valeur refuge |

**Le problème structurel** : TLT est un **risque de duration**, pas une vraie diversification :
- En cycle de hausse des taux, TLT se corrèle AVEC les actions (les deux baissent)
- 2022 a cassé l'hypothèse « obligations = valeur refuge »
- Le Max DD de 33.6 % est structurel (ne peut pas être corrigé par ajustement de paramètres)

### Remplacement : DualMomentumNoTLT

| Stratégie | Sharpe | CAGR | Max DD | Amélioration |
|-----------|--------|------|--------|--------------|
| DualMomentum (original) | 0.350 | 9.2 % | 33.6 % | Référence |
| **DualMomentumNoTLT** | **0.469** | **11.0 %** | **23.6 %** | **+34 % Sharpe, -10 % Max DD** |

**Ce qui a changé** :
- Retrait du TLT, remplacé par des **actifs défensifs** (XLP, IEF, GLD)
- Max DD réduit de 33.6 % → 23.6 %
- Sharpe amélioré de 0.350 → 0.469

### Leçons retenues

1. **TLT n'est pas une valeur refuge dans tous les régimes** : le risque de duration crée une corrélation avec les actions pendant les hausses de taux
2. **Le Max DD est structurel** : un drawdown de 33.6 % est inacceptable pour la plupart des investisseurs
3. **Le choix d'actif compte** : le choix de l'actif risk-off est aussi important que le signal
4. **Sensibilité au régime** : les stratégies doivent tenir compte des différents régimes de marché (hausse vs. baisse des taux)
5. **Ne pas sur-ajuster à une période** : TLT a fonctionné sur 2015-2020 mais a cassé en 2022

## Quand DualMomentum (avec TLT) PEUT fonctionner

Cette approche originale peut fonctionner dans :
- **Environnements de baisse des taux** : TLT bénéficie des baisses de taux
- **Périodes déflationnistes** : les obligations offrent une vraie diversification
- **Backtests plus courts** : 2015-2020 montre de bons résultats (mais 2022 le casse)

**Pour le cycle complet (2015-2026)** : utiliser DualMomentumNoTLT à la place.

## Valeur pédagogique

Cette stratégie sert de contre-exemple pour :
- ⚠️ **Risque de sélection d'actif** : l'actif « valeur refuge » peut devenir une source de risque
- ⚠️ **Dépendance au régime** : une stratégie qui fonctionne dans un régime peut échouer dans un autre
- ⚠️ **Le Max DD compte** : un drawdown de 33.6 % est psychologiquement et financièrement dommageable
- ⚠️ **L'importance du backtest sur période complète** : 2015-2020 paraît bon, 2022 le casse

## Comparaison au remplacement

```python
# Original (DualMomentum)
UNIVERSE = [SPY, QQQ, IEF, GLD, XLP, TLT]  # TLT inclus
RISK_OFF_ASSETS = [TLT, IEF, GLD, XLP]

# Remplacement (DualMomentumNoTLT)
UNIVERSE = [SPY, QQQ, IEF, GLD, XLP]  # TLT retiré
RISK_OFF_ASSETS = [IEF, GLD, XLP]  # Défensif, sans risque de duration
```

## Références

- **DualMomentumNoTLT** : la version améliorée sans TLT
- **SectorMomentum** : approche dual-momentum similaire avec actifs défensifs
- **OPTIMIZATION_BACKLOG.md** : historique complet des itérations

---

**Note** : cette stratégie est conservée comme contre-exemple. Pour un usage en production, voir **DualMomentumNoTLT** qui retire le TLT et atteint de meilleurs rendements ajustés au risque.
