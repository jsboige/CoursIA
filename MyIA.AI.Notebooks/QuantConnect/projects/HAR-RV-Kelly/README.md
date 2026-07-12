# HAR-RV-Kelly

**Classe d'actifs :** Multi-actifs (Actions, Obligations, Matières premières)

**ID projet Cloud :** Voir `config.json` (local-id : 230839018)

## Description

Modèle HAR-RV (Heterogeneous Autoregressive Realized Variance, Corsi 2009) pour prévoir la variance réalisée à 5 jours sur six actifs (SPY, EFA, EEM, TLT, GLD, DBC). Utilise le critère de Kelly à fraction 1/4 pour le dimensionnement des positions basé sur la prévision HAR. Inclut la direction du momentum à 5 jours. Ré-ajustement du modèle par OLS tous les 22 jours sur une fenêtre glissante de 500 jours. Rebalancement hebdomadaire.

## Comment exécuter

### Lean CLI
```bash
lean backtest --algorithm HAR-RV-Kelly/main.py
```

### QC Cloud
Ouvrir le projet cloud (local-id : 230839018), compiler et lancer un backtest.

## Métriques du backtest

| Méthode | Rebalancement | Paramètres clés |
|---------|---------------|-----------------|
| HAR-RV + Critère de Kelly | Hebdomadaire | Fraction Kelly 1/4, prévision 5 jours, ré-ajustement OLS tous les 22 jours, fenêtre 500 jours |

## Fichiers

| Fichier | Description |
|---------|-------------|
| `main.py` | Prévision de volatilité HAR-RV avec dimensionnement par critère de Kelly sur 6 ETFs multi-actifs |
| `config.json` | Configuration du projet (local-id) |
| `research.ipynb` | Notebook de recherche avec analyse du modèle HAR-RV et exploration de la fraction Kelly |

## Références

- Corsi, F. (2009). *A Simple Approximate Long-Memory Model of Realized Volatility*. Journal of Financial Econometrics.
- Kelly, J.L. (1956). *A New Interpretation of Information Rate*. Bell System Technical Journal.
- [QuantConnect Documentation](https://www.quantconnect.com/docs/)
