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

Mode de balayage (déclaré avant tout calcul, c.`59a808dd84`) : **un paramètre
à la fois (OAT)** — chaque variante ne change qu'un seul seuil, les autres
restant à leur défaut. Soit 7 backtests : `zone1_dd` ∈ {0.04, 0.07} ;
`zone2_dd` ∈ {0.08, 0.12} ; `top_n` ∈ {10} ; `min_yield` ∈ {0.025, 0.04}
(les défauts 0.05 / 0.10 / 20 / 0.03 sont portés par le run de base). Le
produit cartésien complet (3 × 3 × 2 × 3 = 54 points) n'est pas exécuté :
quota d'appels API QC partagé par la flotte (10/min). L'OAT couvre chaque
axe indépendamment ; la base `f41b0eed` sert de référence à chaque ligne.

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

## Résultat de base (2018-2026, frais IBKR)

Backtest `781-base-2018-2026-ibkr-v2` (`f41b0eed`, projet 37317779, 2195 jours,
91 ordres) :

| Mesure | Valeur |
|--------|--------|
| Sharpe | 0,404 |
| CAGR | 9,22 % |
| Pire baisse | 16,4 % |
| Profit net total | +116,1 % |
| PSR | 1,5 % |

Comparaisons (même fenêtre, mêmes frais — projet
[ThreeZone781Benchmarks](../ThreeZone781Benchmarks/)) :

| Run | Sharpe | CAGR | Pire baisse | Total |
|-----|--------|------|-------------|-------|
| **781 réimplémentée** | **0,404** | **9,22 %** | **16,4 %** | **+116 %** |
| SPY détenu (`43fa2e07`) | 0,499 | 13,91 % | 33,6 % | +212 % |
| 60/40 SPY/IEF (`d4a2b089`) | 0,383 | 8,86 % | 21,2 % | +110 % |

Lecture mesurée : la rotation **domine le 60/40 sur les trois axes**
(Sharpe, CAGR, drawdown) et divise la pire baisse du SPY détenu par deux
(16,4 % vs 33,6 %) au prix de 4,7 points de CAGR annuel. Profil défensif —
pas un dominant du SPY en rendement absolu. Verdict différé aux volets
restants (grille de robustesse, frais doublés, corrélations, sous-périodes).

Rotation annuelle (proxy déclaré : ordres/an sur la fenêtre) : 781 ≈ 10,4
ordres/an (91 ordres sur 8,73 ans) ; 60/40 ≈ 19,8/an (173 ordres) ; SPY
détenu 1 ordre.

## Grille de robustesse (OAT, 7 variantes)

Sept backtests sur le même compile v2 (`4449fda8`, source identique au run de
base), un paramètre à la fois (mode déclaré ci-dessus) :

| Variante | Sharpe | CAGR | Pire baisse | Ordres | Lecture |
|----------|--------|------|-------------|--------|---------|
| **base (défauts)** | **0,404** | **9,22 %** | **16,4 %** | **91** | référence |
| `zone1_dd`=0.04 | 0,365 | 8,57 % | 14,8 % | 107 | rotation plus précoce → dégrade |
| `zone1_dd`=0.07 | 0,432 | 9,94 % | 16,3 % | 59 | rester investi SPY paie |
| `zone2_dd`=0.08 | 0,317 | 7,92 % | 13,8 % | 80 | les deux sens dégradent |
| `zone2_dd`=0.12 | 0,341 | 8,35 % | 21,3 % | 97 | défaut 0.10 = point fort local |
| `top_n`=10 | 0,404 | 9,22 % | 16,4 % | 91 | non-mordant (identique à la base) |
| `min_yield`=0.025 | 0,404 | 9,22 % | 16,4 % | 91 | non-mordant (identique à la base) |
| `min_yield`=0.04 | 0,402 | 9,22 % | 16,4 % | 91 | quasi non-mordant |

Lecture d'ensemble :

- **Les seuls axes qui mordent sont les seuils de zones** (`zone1_dd`,
  `zone2_dd`) — précisément les seuils que la fiche ne publie pas.
  `zone1_dd` est monotone (plus le seuil est haut, mieux cela vaut sur cette
  fenêtre) ; `zone2_dd` est non monotone et son défaut 0.10 est un point
  fort local en Sharpe.
- **`top_n` et `min_yield` ne mordent pas** : le filtre d'historique de
  dividende est le goulot — il n'admet jamais plus de ~10 titres à chaque
  revue, et le top-40 trié par rendement décroissant est saturé de titres
  ≥ 3 %. Baisser le seuil ne change pas la sélection ; le plafond de 20
  titres ne contraint jamais. (`min_yield`=0.04 montre un Sharpe de 0,402
  avec profit identique au centime près : écart sous la résolution des
  statistiques QC.)
- **La dominance sur le 60/40 n'est pas robuste aux seuils** : 3 des 7
  variantes (`z1=0.04`, `z2=0.08`, `z2=0.12`) tombent sous le Sharpe du
  60/40 (0,383). La domination mesurée aux défauts dépend du choix exact
  des seuils de zones, non publiés par la fiche.
- Aucune variante ne bat SPY détenu (0,499).

## État du protocole (issue #18905)

| Point | État |
|-------|------|
| 1. Cloner le projet source | Non réalisable (accès refusé) → réimplémentation déclarée, DM envoyé au coordinateur pour le canal d'accès de la flotte |
| 2. Backtest frais IBKR | **Livré** : v2 `f41b0eed` Completed (Sharpe 0,404 / CAGR 9,22 % / DD 16,4 %) |
| 3. Mesures + comparaisons | **SPY détenu et 60/40 livrés** ; corrélations ETF : projet compagnon [ThreeZone781Correlation](../ThreeZone781Correlation/) (cloud 37320712) déployé, compile BuildSuccess, run en cours |
| 4. Verdict + robustesse | **Grille OAT livrée** (7/7 backtests, table ci-dessus) ; restent : frais doublés (`fee_mult`=2), sous-périodes, puis verdict BEATS/NO BEATS/INCONCLUSIVE |
| 5. Couverture données fondamentales | Vérification à venir (trous rendement/payout sur 2018-2026) |
| 6. Gel du code au verdict | À venir |

Chiffres affichés par la fiche (non vérifiés) : CAGR 16,7 %, pire baisse
20,9 % — aucun historique hors échantillon (publication du 29/09/2026).
