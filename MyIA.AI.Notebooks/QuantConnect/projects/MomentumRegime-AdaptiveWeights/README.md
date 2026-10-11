# MomentumRegime-AdaptiveWeights

**Classe d'actifs :** Actions US (SPY/QQQ/IEF/GLD)
**Cloud project ID :** 31524424
**Baseline :** Framework_Composite_MomentumRegime (chiffres antérieurs à #19740 : Sharpe 0.185, CAGR 4.73 %)

## Description

Variante à poids adaptatifs de Framework_Composite_MomentumRegime.
Décale l'allocation vers SectorMomentum (85/15 contre 60/40 pour la baseline),
élargit l'univers de momentum pour inclure QQQ et privilégie des lookbacks plus courts.

Les deux modèles alpha émettent sur les quatre mêmes ETF. `MultiStrategyPCM` annonce qu'il
additionne les parts des deux stratégies sur les titres communs ; sous le code d'origine, ce
n'était pas le cas (voir la mesure ci-dessous).

## Mesure #19759 (tranche 2) : `NO BEATS`

Backtests QC Cloud du 2026-10-08, du 2015-01-02 au 2026-07-10 (2895 séances), avec les frais
du modèle de courtage fixé par le code. Le protocole et la règle de verdict ont été fixés avant
tout calcul ([#19759](https://github.com/jsboige/CoursIA/issues/19759), même règle que #19740).
Le Sharpe est calculé à taux sans risque nul sur la valeur du portefeuille à chaque clôture,
par une analyse hors dépôt ; il diffère donc du Sharpe affiché par QC, qui retranche un taux
sans risque.

**SectorMomentum n'atteignait jamais les cibles.** Lean garde un seul insight actif par
symbole avant d'appeler `determine_target_percent`. RegimeSwitching émet sur les quatre ETF
de SectorMomentum, et c'est son insight qui reste. Le compteur de la liste reçue le montre
sous `base` ; il est mesuré avant la reconstruction des cibles :

| Compteur | `base` (code d'origine) | `intent` |
|----------|-------------------------|----------|
| Appels de `determine_target_percent` dont la liste reçue contient un insight SectorMomentum (avant reconstruction) | 0 sur 403 | 0 sur 403 |
| Exposition brute moyenne | 0,15 | 1,00 |
| Corrélation hebdomadaire avec RegimeSwitching seul | 1,00 | 0,76 |
| Corrélation hebdomadaire avec SectorMomentum seul | 0,69 | 0,995 |

Sous `base`, le portefeuille détenait donc RegimeSwitching à 15 % et 85 % de liquidités. Le
mode `intent` reprend le `MultiStrategyPCM` de #19758 : il reconstruit les cibles à partir du
dernier insight actif de chaque couple (titre, modèle source), puis les additionne par titre.
Le premier compteur vaut 0 dans les deux modes, car il compte la liste reçue par
`determine_target_percent`, avant cette reconstruction ; la reconstruction se lit dans
l'exposition brute et dans les corrélations.

| Version | Sharpe | CAGR | Pire baisse | Rotation par an | Exposition brute moyenne |
|---------|--------|------|-------------|-----------------|--------------------------|
| `intent` (défaut) | 0,90 | 14,6 % | −23,4 % | 8,6 | 1,00 |
| `base` (code avant #19759) | 0,90 | 1,9 % | −4,4 % | 1,4 | 0,15 |
| SectorMomentum seul (`sm`) | 0,87 | 14,9 % | −26,4 % | 8,4 | 1,00 |
| RegimeSwitching seul (`rs`) | 0,91 | 12,5 % | −27,4 % | 9,5 | 1,00 |
| SPY détenu (`spy`) | 0,83 | 13,9 % | −33,7 % | 0,09 | 1,00 |
| 60 % SPY / 40 % IEF (`sixty40`) | 0,88 | 8,9 % | −21,1 % | 0,29 | 1,00 |

Un Sharpe à taux sans risque nul ne change pas quand on réduit l'exposition : `base` a celui
de RegimeSwitching seul, avec un CAGR divisé par plus de six.

**Verdict.** Il est `NO BEATS` pour `intent` comme pour `base` : aucun écart de Sharpe avec les
références n'est significatif. La différence est testée par bootstrap circulaire par blocs de
21 séances (10 000 tirages, correction de Holm sur les deux références).

| Candidate | Écart avec SPY [IC 95 %] | Écart avec le 60/40 [IC 95 %] | p Holm (SPY / 60/40) |
|-----------|--------------------------|-------------------------------|----------------------|
| `intent` | +0,08 [−0,48 ; +0,59] | +0,02 [−0,50 ; +0,54] | 0,83 / 0,83 |
| `base` | +0,07 [−0,30 ; +0,41] | +0,02 [−0,37 ; +0,38] | 0,75 / 0,75 |

Les écarts de Sharpe sont calculés avant l'arrondi des valeurs du tableau : par exemple,
`intent` − SPY vaut 0,0761, `intent` − `sm` vaut 0,0357 et `intent` − `rs` vaut −0,0010.
La soustraction des Sharpes affichés à deux décimales peut donc donner un autre arrondi.

Par sous-période (2015-2018, 2019-2022, 2023 → 2026-07), `intent` est derrière les deux
références en 2015-2018 (−0,21 contre SPY, −0,32 contre le 60/40), puis devant (+0,11 et
+0,08 contre SPY). `base` fait l'inverse : devant en 2015-2018, derrière ensuite. La grille de
paramètres et le run à frais doublés n'étaient prévus que pour une candidate significative :
ils n'ont pas été lancés.

**Apport de chaque modèle.** Sous `intent`, l'écart de Sharpe avec SectorMomentum seul vaut
+0,04 [−0,02 ; +0,09], et la corrélation hebdomadaire des rendements vaut 0,995 : à 85 %, le
composite se comporte comme SectorMomentum seul. Avec RegimeSwitching seul, l'écart vaut
0,00 [−0,45 ; +0,45]. Ces écarts sont descriptifs, hors correction de Holm.

**Ce que change la variante.** Comparé au run `intent` de #19758
(Framework_Composite_MomentumRegime, parts 0,60 / 0,40, sans les deux autres changements de
la variante), l'écart de Sharpe vaut +0,08 [−0,21 ; +0,38] sur 2894 séances communes,
descriptif. Une fois les parts additionnées, les trois changements de la variante ne
produisent pas d'écart mesurable.

**Ce que détient la stratégie.** Sous `intent`, le résultat des positions fermées vient pour
moitié de GLD (50 %), puis de QQQ (37 %), de SPY (10 %) et d'IEF (3 %).

**Choix du défaut.** Le protocole prévoyait que `intent` devienne le mode par défaut si le
défaut était constaté selon l'un de deux critères : sous `base`, moins de la moitié des appels
voient SectorMomentum (0 sur 403) ; ou l'exposition brute de `base` est inférieure de plus de
10 points à celle d'`intent` (0,15 contre 1,00). Le compteur constate le filtrage sous `base`,
mais reste à zéro dans les deux modes : il ne vérifie pas la reconstruction. La preuve qui
discrimine les modes est l'exposition brute, confortée par les corrélations du tableau.
Le changement rend le code conforme à ce qu'annonce `MultiStrategyPCM` ; il ne crée pas
d'avantage démontré.

**Limites.**
- La variante (parts, QQQ, poids de retour) a été choisie après avoir vu le Sharpe hors
  échantillon du composite d'origine, donc en connaissant une partie de la période. Ce biais
  favorisait les candidates, ce qui renforce le `NO BEATS`.
- Les backtests demandaient une fin au 2026-09-30. Les nœuds de calcul utilisés retiennent
  les 90 derniers jours et ont ramené la fin au 2026-07-10, sans erreur. Toutes les versions
  ont tourné sur les mêmes nœuds : les comparaisons portent sur les mêmes séances. Le run
  `intent` de #19758 s'arrête au 2026-07-09.

## Paramètres du projet

Tous facultatifs :

| Paramètre | Défaut | Rôle |
|-----------|--------|------|
| `mode` | `intent` | `intent` : parts additionnées par titre ; `base` : code d'origine ; `sm`, `rs` : un seul modèle alpha, à 100 % ; `spy` : SPY détenu ; `sixty40` : 60 % SPY et 40 % IEF, rééquilibrés le premier jour de bourse de chaque mois |
| `start`, `end` | `2018-01-01`, `2025-01-01` | fenêtre du backtest |
| `sm_allocation`, `rs_allocation` | 0,85, 0,15 | parts des deux modèles |
| `sm_weights` | `0.5,0.2,0.2,0.1` | poids des retours à 1, 3, 6 et 12 mois de SectorMomentum |
| `rs_lookback` | 63 | fenêtre de momentum de RegimeSwitching, en séances |
| `fee_mult` | 1 | multiplicateur des frais de courtage |

Le graphique `shadow` porte la valeur du portefeuille à chaque clôture ; les statistiques
d'exécution donnent les ordres par ETF, l'exposition brute moyenne et les compteurs du PCM.

## Chiffres antérieurs à #19759

Les deux sections ci-dessous datent d'avant la mesure ; elles sont conservées pour
l'historique.

**Lecture corrigée par #19759.**
- **Chiffres.** Le run `readme` (`base` sur 2018-01-01 → 2025-01-01, 1760 séances) reproduit
  ceux du registre sur la même fenêtre : Sharpe QC −0,72 (contre −0,729), CAGR 1,87 %
  (1,88 %), pire baisse 4,4 % (4,3 %), 290 ordres. Le PSR diffère (0 % contre 17,4 %) ; la
  cause n'a pas été mesurée. Le tableau ci-dessous ne donne pas sa fenêtre ; 21,1 % de profit
  net à 1,76 % par an correspondent à environ onze ans, soit la fenêtre d'origine 2015-2025.
- **Sharpe négatif.** Le Sharpe QC retranche un taux sans risque que les 85 % de liquidités
  ne rapportent pas dans le backtest. À taux sans risque nul, `base` a le Sharpe de
  RegimeSwitching seul (0,90 contre 0,91) : la variante ne détruisait pas de valeur par ses
  choix, elle n'était investie qu'à 15 %.
- **Causes 1 et 2 (sur-concentration sur SectorMomentum, QQQ qui dilue le signal).**
  SectorMomentum ne tradait pas sous `base` : ces causes ne peuvent pas expliquer le
  résultat. Sous `intent`, QQQ porte 37 % du résultat des positions fermées.
- **Cause 3 (beta faible, actifs défensifs).** Le beta de 0,081 tient à l'exposition brute de
  0,15, pas au choix des actifs.
- **Cause 4 (RegimeSwitching trop faible pour compter).** C'était l'inverse : RegimeSwitching
  à 15 % était la seule part investie.
- **Baseline.** Framework_Composite_MomentumRegime portait le même défaut (#19740) : la
  comparaison « baseline contre variante » opposait deux versions où SectorMomentum ne
  tradait pas.

### Résultats de backtest

| Métrique | Baseline (T60/RS40) | Cette variante (T85/RS15) | Delta |
|----------|---------------------|---------------------------|-------|
| Sharpe Ratio | 0.185 | **-0.74** | -0.925 |
| CAGR | 4.73 % | 1.76 % | -2.97 pp |
| Max Drawdown | - | 4.4 % | - |
| Net Profit | - | 21.1 % | - |
| Beta (vs SPY) | - | 0.081 | - |
| Total Orders | - | 403 | - |
| Win Rate | - | 71 % | - |

**Verdict : NO BEATS.** Sharpe ratio négatif. Le décalage 85/15 a détruit de la valeur.

### Analyse

La variante sous-performe dramatiquement la baseline. Causes profondes :

1. **Sur-concentration sur SectorMomentum** : à 85 % de poids, SectorMomentum
   domine les allocations. Quand son signal mensuel s'inverse (fréquent avec des
   lookbacks courts 0.5/0.2/0.2/0.1), le portefeuille navigue entre les actifs.

2. **L'ajout de QQQ dilue la qualité du signal** : ajouter QQQ à l'univers de
   SectorMomentum crée une course à 4 où l'actif au meilleur score tourne fréquemment,
   générant un turnover inutile.

3. **Beta faible (0.081)** : la stratégie passe l'essentiel du temps dans des actifs
   défensifs (IEF/GLD) malgré des conditions de marché haussier, ce qui suggère que le
   scoring composite de SectorMomentum, avec un biais court terme, surpondère les
   replis transitoires.

4. **RegimeSwitching à 15 %** : trop faible pour compter. Le filet de sécurité de
   commutation de régime qui protège en marché baissier/latéral est effectivement
   désactivé.

## Fichiers

- main.py - Stratégie (allocation T85/RS15), instrumentée pour la mesure #19759
- alpha_models.py - Modèles alpha SectorMomentum + RegimeSwitching
- portfolio_construction.py - Construction de portefeuille MultiStrategyPCM (mode `intent` repris de #19758)

## Références

- Hands-On AI Trading, Section 06
- Baseline : Framework_Composite_MomentumRegime
