# Three-Zone SPY Drawdown Rotation

Évaluation sous frais IBKR de la stratégie publique **781** « Three-Zone SPY
Drawdown Rotation Strategy » du Strategy Explorer QuantConnect (auteur affiché :
Viliam Balara, v1.0.0 du 29/09/2026). Protocole complet : issue
[jsboige/CoursIA#18905](https://github.com/jsboige/CoursIA/issues/18905).

## Résumé

| Paramètre | Valeur |
|-----------|--------|
| **Type** | Rotation de régime (drawdown SPY) |
| **Signal** | Baisse du SPY depuis son plus haut 52 semaines |
| **Zones** | verte < 5 % ; jaune 5-10 % ; rouge ≥ 10 % (grille, voir ci-dessous) |
| **Portefeuille dividende** | ≤ 20 titres, rendement ≥ 3 %, payout 5-80 %, historique 10 ans |
| **Revue** | Hebdomadaire (lundi après l'ouverture) |
| **Frais** | Interactive Brokers (`InteractiveBrokersFeeModel`) |
| **Fenêtre** | 2018-01-01 → 2026-09-25 |

## Réimplémentation déclarée

Le projet source (37135744) n'est **pas lisible par le compte de la flotte**
(`read_project` : « You do not own this project ») et la fiche n'est pas
accessible anonymement. Cette implémentation suit la **description publique**
de la fiche ; les seuils exacts des zones vivent dans le code inaccessible de
l'auteur. La grille de robustesse (point 4 du protocole) balaie ces seuils :

| Paramètre | Défaut | Grille prévue |
|-----------|--------|---------------|
| `zone1_dd` | 0.05 | {0.04, 0.05, 0.07} |
| `zone2_dd` | 0.10 | {0.08, 0.10, 0.12} |
| `top_n` | 20 | {10, 20} |
| `min_yield` | 0.03 | {0.025, 0.03, 0.04} |

Proxys déclarés (non spécifiés par la fiche) :

- **Taux de distribution** = rendement du dividende / rendement des bénéfices
  (le champ fondamental direct n'est pas stable d'une source à l'autre).
- **Historique de dividende 10 ans** = au moins 8 années distinctes avec
  paiement sur les 10 dernières (tolérance 2 années), vérifié une fois par
  mois et mis en cache.
- **Liquidité** : prix > 5 $, dollar volume > 20 M$, capitalisation > 2 Md$
  (écarte les micro-caps ; la fiche ne filtre pas explicitement).

## Allocations par zone

| Zone | Drawdown SPY | SPY | Dividendes |
|------|--------------|-----|------------|
| Verte | < `zone1_dd` | 100 % | — |
| Jaune | [`zone1_dd`, `zone2_dd`) | 50 % | 50 % |
| Rouge | ≥ `zone2_dd` | — | 100 % |

## État du protocole (issue #18905)

| Point | État |
|-------|------|
| 1. Cloner le projet source | Non réalisable (accès refusé) → réimplémentation déclarée, DM envoyé au coordinateur pour le canal d'accès de la flotte |
| 2. Backtest frais IBKR | Projet QC 37317779 créé, compile `BuildSuccess` ; backtest de base différé (saturation du node pool flotte au 04/10) |
| 3. Mesures + comparaisons | À venir (60/40, SPY détenu, corrélations) |
| 4. Verdict + robustesse | À venir |
| 5. Couverture données fondamentales | Vérification à venir (trous rendement/payout sur 2018-2026) |
| 6. Gel du code au verdict | À venir |

Chiffres affichés par la fiche (non vérifiés) : CAGR 16,7 %, pire baisse
20,9 % — aucun historique hors échantillon (publication du 29/09/2026).
