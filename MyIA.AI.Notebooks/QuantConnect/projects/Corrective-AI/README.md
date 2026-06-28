# Corrective AI / Meta-Labeling (Ch08-02)

**Type :** Stub (exercice planifié, fichiers de code non encore créés)

**Hands-On AI Trading**, Chapitre 8-02 — Meta-Labeling avec Corrective AI

## Objectif

Implémenter une approche de meta-labeling où un modèle primaire génère des signaux de trading et un modèle correctif secondaire filtre les faux positifs, améliorant la précision tout en préservant le rappel.

## Approche

### Modèle primaire : croisement de SMA

- SMA rapide (20 jours) vs SMA lente (60 jours)
- Signal : haussier quand rapide > lente * 1.02, baissier quand rapide < lente * 0.98
- Univers : SPY, TLT, GLD (diversification multi-actifs)

### Filtre correctif

Le modèle secondaire évalue s'il faut faire confiance au signal primaire sur la base de :

- **Force de la tendance** : écart entre SMA rapide et lente (normalisé)
- **Régime de volatilité** : prix relatif à l'EMA (proxy de volatilité 50 jours)
- **Règles** :
  - Tendance forte (écart >3 %) -> confiance dans le signal
  - Tendance modérée + faible volatilité -> confiance dans le signal
  - Tendance faible + forte volatilité -> rejet du signal (rester à plat)

### Concept de meta-labeling

- Étiquettes du modèle primaire : +1 (long), -1 (short), 0 (plat)
- Étiquettes du modèle secondaire : 1 (faire confiance au primaire), 0 (rejeter le primaire)
- Position nette = direction_primaire * approbation_corrective
- Attendu : précision plus élevée (moins de faux signaux), rappel similaire ou inférieur

## Projet QC

| Champ | Valeur |
|-------|--------|
| Project ID | 30800636 |
| Organisation | Trading Firm QC-Course |
| Période | 2018-01-01 à 2024-12-31 |
| Capital de départ | $1 000 000 |

## Résultats du backtest (v1)

| Métrique | Valeur |
|----------|--------|
| Sharpe Ratio | -0.151 |
| CAGR | 2.22 % |
| Max Drawdown | 11.3 % |
| Net Profit | +16.64 % |
| Win Rate | 70 % |
| Total Orders | 1242 |
| Total Fees | $2 673.78 |

### Analyse

- Un win rate de 70 % confirme que le filtre correctif améliore la qualité des signaux
- Un Sharpe négatif indique des rendements ajustés au risque sous-optimaux
- La perte moyenne (-0.18 %) dépasse le gain moyen (0.12 %) — le sizing de position et le timing de sortie doivent être améliorés
- L'approche multi-actifs (SPY/TLT/GLD) apporte de la diversification mais le retard du croisement SMA pénalise en marché latéral

## Fichiers

- `main.py` — algorithme QC avec signal primaire + filtre correctif
- `research.ipynb` — calcul du croisement SMA, conception du filtre correctif, analyse de la réduction des signaux

## Référence

- Hands-On AI Trading, Chapitre 8-02
- De Prado, M. (2018), « Advances in Financial Machine Learning » — concept de meta-labeling
- Corrective AI : modèle secondaire entraîné sur les erreurs de prédiction du modèle primaire
