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

## Invalidation des résultats v2/v3 (mesurée, 2026-10-04)

Les runs `f41b0eed` (base v2), la grille OAT 7/7, le run corrélations et le
run `fee_mult=2` ci-dessous décrivent une implémentation **buguée** : l'appel
`self.history(self.dividends, ...)` lève une `AttributeError` sur Lean master
v18155 (« object has no attribute 'dividends' »), attrapée par le `except` du
filtre → **tout titre était rejeté, la jambe dividende n'a jamais investi**.
La stratégie effectivement mesurée est « SPY-ou-cash » (verte = SPY, jaune =
50 % SPY + 50 % cash, rouge = cash), pas la rotation de la fiche.

Preuve : logs du run `781-fee2-2018-2026` (projet 37317779) et du run
`781-corr-2018-2024` (projet 37320712) — centaines de lignes « dividend
history error … has no attribute 'dividends' » (qui ont de surcroît épuisé le
quota de 100 kb de logs) ; « Lowest Capacity Asset : SPY » (aucun titre
individuel tradé). Les axes « non-mordants » de la grille (`top_n`,
`min_yield`) s'expliquent par ce bug, pas par un goulot du filtre.

Fix : `self.history(Dividend, symbol, ...)` (la classe `Dividend`, pas
l'instance inexistante `self.dividends`). La base, la grille OAT, les
corrélations et le run à frais doublés doivent être **rejoués** sur le code
corrigé — les sections ci-dessous restent visibles comme comportement mesuré
de la version buguée, pour la traçabilité, jusqu'à remplacement.

## Résultat de base v4 (2018-2026, frais IBKR, code corrigé)

Backtest `781-base-2018-2026-ibkr-v4-fix-dividend` (`bf0655ac`, projet
37317779, compile `e855ce4a`, 2195 jours, **1961 ordres**) :

| Mesure | Valeur |
|--------|--------|
| Sharpe | 0,426 |
| CAGR | 11,48 % |
| Pire baisse | 27,7 % |
| Profit net total | +158,5 % |
| PSR | 1,69 % |

Preuve que la jambe dividende investit (vs la v2 buguée à 91 ordres) :
1961 ordres, et les logs du run montrent des `set_holdings` sur des titres
individuels nommés (WMB, DH, NWL, CCL, MET, FD, OXY…), sans aucune ligne
« dividend history error ». Les « Backtest Handled Error : … does not have
an accurate price » résiduelles sont bénines : premier ciblage d'un titre
admis avant sa première barre daily (l'ordre part à la revue suivante).

Comparaisons (même fenêtre, mêmes frais — projet
[ThreeZone781Benchmarks](../ThreeZone781Benchmarks/)) :

| Run | Sharpe | CAGR | Pire baisse | Total |
|-----|--------|------|-------------|-------|
| **781 réimplémentée v4** | **0,426** | **11,48 %** | **27,7 %** | **+158 %** |
| SPY détenu (`43fa2e07`) | 0,499 | 13,91 % | 33,6 % | +212 % |
| 60/40 SPY/IEF (`d4a2b089`) | 0,383 | 8,86 % | 21,2 % | +110 % |

Lecture mesurée : la 781 corrigée **bat le 60/40 en Sharpe et en CAGR**
mais **cède sur la pire baisse** (27,7 % vs 21,2 %) — la dominance sur les
trois axes mesurée en v2 était un artefact du cash (jambe dividende morte =
zone rouge 100 % cash, DD 16,4 %). La vraie 781 prend un portefeuille
d'actions à dividende en zone rouge : plus de rendement, plus de drawdown.
Elle réduit toujours le drawdown du SPY détenu (27,7 % vs 33,6 %) mais
beaucoup moins que la version buguée ne le laissait croire. Aucun dominant
du SPY en rendement absolu. Verdict différé aux rejeux (grille OAT, frais
doublés, corrélations, sous-périodes).

Rotation annuelle (proxy déclaré : ordres/an sur la fenêtre) : 781 v4 ≈
224,6 ordres/an (1961 ordres sur 8,73 ans — le rebalancement hebdo du
portefeuille dividende en zones jaune/rouge porte l'activité) ; 60/40 ≈
19,8/an (173 ordres) ; SPY détenu 1 ordre.

## Résultat v2 invalidé (traçabilité)

Backtest `781-base-2018-2026-ibkr-v2` (`f41b0eed`, 2195 jours, 91 ordres) :
Sharpe 0,404 · CAGR 9,22 % · pire baisse 16,4 % · +116,1 % · PSR 1,5 %.
Ce run décrivait la « SPY-ou-cash » (voir « Invalidation » ci-dessus) — la
lecture initiale de dominance défensive sur le 60/40 (trois axes) et de pire
baisse divisée par deux venait du cash, pas de la stratégie.

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
| 2. Backtest frais IBKR | **Rejoué sur code corrigé** (v4 `bf0655ac`, 2018-2026, 1961 ordres) ; grille OAT en cours de rejeu sur compile v4 |
| 3. Mesures + comparaisons | Benchmarks SPY détenu et 60/40 **valides** (aucun titre dividende requis) ; corrélations ETF mesurées puis invalidées, à rejouer |
| 4. Verdict + robustesse | **Grille OAT invalidée** (elle mesurait une SPY-ou-cash) ; à rejouer sur code corrigé, puis verdict |
| 5. Couverture données fondamentales | Vérification à venir (trous rendement/payout sur 2018-2026) |
| 6. Gel du code au verdict | À venir |

Chiffres affichés par la fiche (non vérifiés) : CAGR 16,7 %, pire baisse
20,9 % — aucun historique hors échantillon (publication du 29/09/2026).
