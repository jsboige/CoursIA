# Multi-Horizon Momentum 676 (réimplémentation déclarée)

Évaluation, sous frais de courtier, de la stratégie publique **676** « Multi-Horizon ETF
Momentum Rotation Strategy » du Strategy Explorer QuantConnect (auteur affiché : Jon
Thibodeaux, v1.1.0 du 01/10/2026). Protocole : issue
[jsboige/CoursIA#19174](https://github.com/jsboige/CoursIA/issues/19174). Discussion
publique de la fiche : [forum QuantConnect, discussion 21181](https://www.quantconnect.com/forum/discussion/21181/).
Références de comparaison : celles de l'évaluation #18904, projet
`FourSleeve774Benchmarks` ([PR #19139](https://github.com/jsboige/CoursIA/pull/19139)),
réutilisées sans être relancées (même fenêtre, mêmes frais, même rebalancement).

## Pourquoi une réimplémentation

Le projet publié (`34803853`) n'est **pas lisible** par le compte de la flotte
(`files/read` : « You do not own this project »), et la page de la discussion 21181 ne
rend pas son contenu sans navigateur. Aucune ligne du code d'origine n'est donc reprise :
`main.py` est écrit d'après la **description publique** de la fiche, lue par l'API
publique `POST /api/v2/strategies/read`. Chaque point que cette description laisse
ouvert est tranché ci-dessous et **déclaré**. Un écart entre nos chiffres et ceux de la
fiche peut venir de ces choix, en particulier de l'univers, et pas seulement de la
stratégie : il est rapporté, il ne sert pas de verdict.

## Ce que dit la description publique

- Rotation mensuelle entre 20 ETF : actions US et internationales, obligations,
  matières premières, devises.
- Score de chaque ETF : moyenne de cinq taux de variation, sur 5, 21, 63, 126 et 252
  séances, chacun mesuré avec un saut de 21 séances pour écarter le bruit de court terme.
- Le premier jour de bourse du mois, les cinq ETF au meilleur score sont retenus. Si les
  cinq scores sont négatifs, tout passe en liquidités.
- Poids inversement proportionnels à l'écart-type des rendements journaliers sur 63
  séances : un actif plus risqué reçoit une part plus petite.
- Toutes les positions sont liquidées avant la pose des nouvelles cibles.
- La version 1.1.0 a ajouté le saut de 21 séances et cinq ETF à l'univers : UUP, FXF,
  AIA, DBA et RLY.

## Choix déclarés

| Point laissé ouvert | Choix de cette réimplémentation |
|---------------------|---------------------------------|
| Univers (20 ETF) | les 5 ajouts nommés par la version 1.1.0 (UUP, FXF, AIA, DBA, RLY) et les autres, choisis ici : actions US SPY, QQQ, IWM, VNQ ; actions hors US EFA, EEM, EWJ, VGK ; obligations TLT, IEF, SHY, LQD, TIP ; matières premières GLD, DBC |
| Taux de variation avec saut | `P[t−21] / P[t−21−h] − 1` pour h ∈ {5, 21, 63, 126, 252}, sur les clôtures journalières ajustées, `t` étant la dernière clôture connue |
| Score | moyenne simple des cinq taux de variation |
| Moment du calcul | 30 minutes après l'ouverture du premier jour de bourse du mois, sur les clôtures jusqu'à la séance précédente |
| « Si les cinq scores sont négatifs » | lecture littérale : liquidités si les cinq retenus sont négatifs ; sinon les cinq lignes sont détenues, y compris celles de score négatif |
| Liquidités | dollars non investis, rendement nul (pas d'ETF monétaire) |
| Poids | 1 / écart-type (ddof 1) des 63 derniers rendements journaliers, normalisés à une somme de 1 ; aucun levier |
| Liquidation | lecture littérale : tout est vendu, puis les cibles sont achetées en entier, même pour une ligne conservée (`liquidate=1`) |
| Exécution | ordres au marché, exécutés à la clôture en données journalières : ventes et achats du même rebalancement partent à la même clôture, ventes d'abord ; frais du courtier, modèle par défaut de Lean, mis à l'échelle par `fee_mult` |
| Premier mois | aucun prix n'est connu à 10 h le premier jour d'une fenêtre : le premier investissement a lieu au rebalancement suivant, comme pour les références de #18904 (même mécanique des deux côtés) |

**Note d'implémentation.** Avec `liquidate=1`, les quantités cibles absolues sont fixées
avant la liquidation. Une première version appelait `set_holdings` après `liquidate()` :
comme les ventes n'étaient pas encore exécutées, elle n'envoyait que les écarts et
laissait le portefeuille sous-investi. Le défaut est documenté sur #19174, et les runs de
cette version ont été annulés avant toute publication de verdict.

## Paramètres de backtest

| Paramètre | Défaut | Rôle |
|-----------|--------|------|
| `start`, `end` | aucun (obligatoires) | fenêtre, contrat du rejeu en ombre (#18923) |
| `fee_mult` | 1 | multiplicateur des frais (2 = frais doublés) |
| `top` | 5 | nombre d'ETF retenus |
| `skip` | 21 | saut, en séances, avant chaque taux de variation (0 = sans saut) |
| `liquidate` | 1 | `1` : tout vendre puis racheter ; `0` : ne traiter que les écarts |
| `weights` | `invvol` | `invvol` (inverse de la volatilité) ou `equal` (poids égaux) |

## Sorties

Contrat du rejeu en ombre (`ML-Training-Pipeline/shadow/README.md`) : à chaque clôture,
valeur du portefeuille dans le graphique `shadow` (séries `e0` à `e4` à tour de rôle),
frais cumulés (`fees`, en fraction du capital de départ) et rotation cumulée (`turnover`).
Les mesures (Sharpe à taux sans risque nul, CAGR, pire baisse, rotation annuelle) se
calculent sur ces séries, pas sur les statistiques du rapport QuantConnect.

Chaque rebalancement écrit une ligne dans le journal de l'algorithme :
`sel <date> <ticker>:<poids>:<score> ...`, ou `sel <date> cash` pour un mois en liquidités.

## Résultats

La règle de verdict a été pré-enregistrée sur #19174 avant le premier backtest. La grille
de sensibilité (`top` 3 et 7, `skip=0`, `weights=equal`) n'a **pas été lancée** : le
pré-enregistrement la conditionnait à une p Holm < 0,05 contre au moins une référence,
et le test principal rend 1,0 contre les deux. Elle ne pouvait plus changer le verdict.

### Verdict : `NO BEATS` contre les deux références

Fenêtre 2018-01-01 → 2026-09-25, 2 194 rendements journaliers alignés, aucune séance
manquante d'un côté ni de l'autre. Bootstrap circulaire par blocs de 21 séances,
10 000 tirages, graine 18921, correction de Holm.

| Comparaison | Différence de Sharpe | p Holm | IC 95 % | Verdict |
|-------------|----------------------|--------|---------|---------|
| 676 − SPY détenu | −0,110 | 1,000 | [−0,600 ; 0,347] | `NO BEATS` |
| 676 − 60/40 SPY/IEF | −0,140 | 1,000 | [−0,638 ; 0,358] | `NO BEATS` |

Les deux différences sont négatives. Les contrôles de robustesse ne les renversent pas :

| Condition | 676 − SPY | 676 − 60/40 |
|-----------|-----------|-------------|
| Frais doublés | −0,128 | −0,157 |
| Sous-période 2018-2020 | −0,371 | −0,637 |
| Sous-période 2021-2023 | −0,013 | +0,225 |
| Sous-période 2024 → 2026-09-25 | −0,117 | −0,110 |

### Mesures par run

Sharpe à taux sans risque nul. Frais annuels en % du capital de départ.

| Run | Sharpe | CAGR | Pire baisse | Rotation / an | Frais / an | Ordres |
|-----|--------|------|-------------|---------------|------------|--------|
| 676 | 0,675 | 8,48 % | −22,72 % | 23,6 | 0,27 % | 1 035 |
| 676, frais doublés | 0,658 | 8,23 % | −22,76 % | 23,6 | 0,54 % | 1 035 |
| 676, `liquidate=0` | 0,683 | 8,59 % | −22,74 % | 9,0 | 0,14 % | 646 |
| 676, fenêtre de la fiche (2021-10-01 → 2026-09-30) | 0,776 | 9,58 % | −12,15 % | 23,3 | 0,25 % | 585 |
| SPY détenu | 0,785 | 13,92 % | −33,61 % | 0,11 | 0,00 % | — |
| 60/40 SPY/IEF | 0,815 | 8,87 % | −21,19 % | 0,32 | 0,02 % | — |

Les références viennent du projet `FourSleeve774Benchmarks` (évaluation #18904,
[PR #19139](https://github.com/jsboige/CoursIA/pull/19139)), réutilisées sans être relancées.

Ce que ces runs montrent :

- **La rotation ne protège pas mieux que le 60/40.** Sa pire baisse (−22,7 %) est celle
  du 60/40 (−21,2 %), pour un CAGR à peine plus bas (8,5 % contre 8,9 %) : le Sharpe
  reste en dessous des deux références sur la fenêtre entière.
- **Aucun mois en liquidités.** Sur les 105 rebalancements, la condition « les cinq scores
  négatifs » ne s'est jamais réalisée ; 8 mois détiennent au moins une ligne de score
  négatif (lecture littérale déclarée). Lignes les plus souvent retenues : QQQ (70 mois),
  SPY (53), GLD (52), AIA (43) ; obligations longues et intermédiaires rarement (TLT 17,
  IEF 10).
- **La liquidation complète coûte sans rien apporter.** En moyenne 3,5 positions sur 5 sont
  reconduites d'un mois sur l'autre, et la règle les vend puis les rachète. Ne traiter
  que les écarts (`liquidate=0`) vise les mêmes cibles, divise la rotation par 2,6 et
  presque par deux les frais, pour environ 0,1 point de CAGR en plus.
- **Écart à la fiche.** Sur sa fenêtre de 5 ans (2021-10-01 → 2026-09-30, hypothèse
  déclarée), CAGR 9,58 % contre 8,07 % affichés, pire baisse −12,15 % contre −15,6 %.
  L'écart peut venir de l'univers choisi ici ; il n'est pas attribuable sans le code
  d'origine.
- **Corrélations hebdomadaires** sur la fenêtre principale : 0,76 avec `vt2`, 0,73 avec
  `aw` (paniers proxys du projet compagnon de #18904), 0,73 avec la 774. Ces trois paniers
  ont un Sharpe nettement supérieur (1,048, 1,033 et 0,978).

Détail complet (p brutes, intervalles, version du code, chemin des séries) :
[verdict sur #19174](https://github.com/jsboige/CoursIA/issues/19174#issuecomment-5985904599).
