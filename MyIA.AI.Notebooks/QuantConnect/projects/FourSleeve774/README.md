# Four-Sleeve 774 (réimplémentation déclarée)

Évaluation, sous frais de courtier, de la stratégie publique **774** « Four-Sleeve
Adaptive Growth Strategy - Cash account » du Strategy Explorer QuantConnect (auteur
affiché : sanchari, v1.0.1 du 28/09/2026). Protocole : issue
[jsboige/CoursIA#18904](https://github.com/jsboige/CoursIA/issues/18904). Discussion
publique de la fiche : [forum QuantConnect, discussion 21464](https://www.quantconnect.com/forum/discussion/21464/).
Projets compagnons : [`FourSleeve774Benchmarks`](../FourSleeve774Benchmarks/) (références
de comparaison et paniers proxys de corrélation).

## Pourquoi une réimplémentation

Le projet publié (`37078429`) n'est **pas lisible** par le compte de la flotte
(`read_project` : « You do not own this project ») et la discussion 21464 ne contient pas
de code. Aucune ligne du code d'origine n'est donc reprise : `main.py` est écrit d'après
la **description publique** de la fiche, lue par l'API `POST /api/v2/strategies/read`.
Chaque point que cette description laisse ouvert est tranché ci-dessous et **déclaré**.
Un écart entre nos chiffres et ceux de la fiche peut donc venir de ces choix, et pas
seulement de la stratégie : il est rapporté, il ne sert pas de verdict.

## Ce que dit la description publique

Quatre poches dans un seul compte sans marge, exposition brute visée de 98 %, plafond
de 30 % par titre, aucun levier, actions entières, réserve de liquidités de 5 % :

| Poche | Part | Description publiée |
|-------|------|---------------------|
| 1 | 35 % | retour à la moyenne court terme parmi les 100 plus grandes actions US, jusqu'à 10 titres, rang des plus bas récents, choisis chaque mois |
| 2 | 25 % | momentum filtré par la tendance (cours au-dessus de l'EMA 189 jours, ADX sous 35), rendements multi-horizons pondérés, jusqu'à 10 titres ; bons du Trésor quand le stress de largeur dépasse 45 % |
| 3 | 25 % | momentum des grandes capitalisations (≥ 5 Md$), mêmes conditions de tendance, nombre de lignes divisé par deux en marché agité |
| 4 | 15 % | ETF tactiques, évalués chaque jour : 70 % de rotation à règles entre actions, obligations, or et ETF inverses ; 30 % de régime de tendance Nasdaq avec dimensionnement par le VIX |

Signaux sur barres journalières closes, ordres au marché à l'ouverture de la séance
suivante, règlement T+1, coupe de la dérive chaque jour, relance des ordres différés,
dimensionnement par la volatilité.

## Choix déclarés

| Point laissé ouvert | Choix de cette réimplémentation |
|---------------------|---------------------------------|
| Univers | 500 plus grandes capitalisations US (prix > 5 $, volume en dollars > 5 M$), revu le premier jour de bourse du mois |
| Stress de largeur | part des 500 titres dont le cours est sous leur EMA (`ema`, 189 par défaut) |
| Poche 1 : rang des plus bas | les 10 titres des 100 plus grandes capitalisations dont le cours est le plus proche de son plus bas des 20 dernières séances |
| Poche 2 : rendements pondérés | moyenne simple des rendements 3, 6 et 12 mois ; 10 meilleurs parmi les titres au-dessus de leur EMA avec ADX 14 sous `adx_max` ; toute la poche en bons du Trésor si le stress dépasse `stress_max` ; une place non pourvue va aux bons du Trésor |
| Poche 3 : marché agité | « agité » = stress au-dessus de `stress_max` ; momentum 12 mois hors dernier mois ; 10 positions, 5 en marché agité (l'autre moitié en bons du Trésor) |
| Dimensionnement dans une poche | inverse de la volatilité des rendements journaliers sur 63 séances (`sizing=invvol`) ; poids égaux en variante (`sizing=equal`) |
| Bons du Trésor | ETF `BIL` (exempt du plafond de 30 %) |
| Poche 4 : rotation (70 %) | SPY au-dessus de sa moyenne 200 jours → QQQ, ou `BIL` si le RSI 10 de QQQ dépasse 80 ; sinon RSI 10 de QQQ sous 30 → QQQ ; sinon QQQ sous sa moyenne 20 jours → PSQ (inverse) ; sinon le meilleur de TLT et GLD sur 21 séances s'il est positif, `BIL` sinon |
| Poche 4 : tendance Nasdaq (30 %) | QQQ au-dessus de sa moyenne 100 jours → QQQ à hauteur de min(1, 20 / VIX), arrondi par paliers de 0,25 ; le reste en `BIL` |
| ETF à effet de levier | **écartés** (la description parle de « zero leverage ») |
| Réserve de 5 % | appliquée au dimensionnement : chaque ligne vise 95 % de sa cible, soit environ 93 % investis |
| Ordres | événement 20 minutes avant l'ouverture, ordres `market_on_open` ; ventes d'abord ; achats limités à 97 % des liquidités réglées, réduits au prorata ; la part non servie repart à la séance suivante (relance différée) ; ordre minimal 0,2 % du portefeuille |
| Coupe de la dérive | une ligne au-delà de 1,25 fois sa cible est ramenée à la cible (ventes seulement, pas de complément en cours de mois) |
| Rebalancement | poches 1 à 3 le premier jour de bourse du mois, poche 4 chaque séance ; un ordre ne part que pour une ligne dont la cible a changé ou qui a dérivé |
| Frais et compte | modèle de frais par défaut de Lean pour ce courtier, compte sans marge, règlement T+1 des actions |

## Paramètres de backtest

| Paramètre | Défaut | Rôle |
|-----------|--------|------|
| `start`, `end` | aucun (obligatoires) | fenêtre, contrat du rejeu en ombre (#18923) |
| `fee_mult` | 1 | multiplicateur des frais (2 = frais doublés) |
| `ema` | 189 | longueur de l'EMA du filtre de tendance et du stress |
| `adx_max` | 35 | seuil d'ADX du filtre de tendance |
| `stress_max` | 0.45 | seuil de stress de largeur |
| `sizing` | `invvol` | `invvol` ou `equal` |
| `sleeve` | `all` | `all`, ou `1`, `2`, `3`, `4` : une poche seule, portée à tout le portefeuille, plafond par ligne mis à la même échelle ; avec `layout=775` : `all`, `stock` ou `etf` |
| `layout` | `774` | `774` (cette stratégie) ou `775` (réimplémentation déclarée de la 775, [section dédiée](#variante-775--adaptive-etf-and-stock-momentum-20168)) |
| `lev` | `3` | avec `layout=775` seulement : `1` exécute chaque ETF ×3 par son équivalent ×1 (TQQQ → QQQ, SOXL → SMH, SQQQ → PSQ) |

## Sorties

Contrat du rejeu en ombre (`ML-Training-Pipeline/shadow/README.md`) : à chaque clôture,
valeur du portefeuille dans le graphique `shadow` (séries `e0` à `e4` à tour de rôle),
frais cumulés (`fees`, en fraction du capital de départ) et rotation cumulée (`turnover`).
Les mesures (Sharpe à taux sans risque nul, CAGR, pire baisse, rotation annuelle) se
calculent sur ces séries, pas sur les statistiques du rapport QuantConnect.

## Résultats

Règle de verdict pré-enregistrée sur #18904 avant le premier backtest. La grille de
7 runs a été retirée avant son premier run (complément daté sur l'issue) : le test
principal excluait déjà `BEATS`, elle ne pouvait donc plus changer le verdict.

### Verdict : `INCONCLUSIVE` contre les deux références

Fenêtre 2018-01-01 → 2026-09-25, 2 194 rendements journaliers alignés. Bootstrap
circulaire par blocs de 21 séances, 10 000 tirages, correction de Holm.

| Comparaison | Différence de Sharpe | p Holm | IC 95 % | Verdict |
|-------------|----------------------|--------|---------|---------|
| 774 − SPY détenu | +0,193 | 0,513 | [−0,357 ; 0,699] | `INCONCLUSIVE` |
| 774 − 60/40 SPY/IEF | +0,163 | 0,513 | [−0,411 ; 0,706] | `INCONCLUSIVE` |

La différence reste positive à frais doublés et sur 2 des 3 sous-périodes (négative
sur 2021-2023), contre les deux références.

### Mesures par run

Sharpe à taux sans risque nul. Frais annuels en % du capital de départ.

| Run | Sharpe | CAGR | Pire baisse | Rotation / an | Frais / an | Ordres |
|-----|--------|------|-------------|---------------|------------|--------|
| 774 | 0,978 | 17,31 % | −21,51 % | 16,3 | 0,71 % | 5 971 |
| 774, frais doublés | 0,955 | 16,82 % | −21,58 % | 16,2 | 1,42 % | 5 967 |
| SPY détenu | 0,785 | 13,92 % | −33,61 % | 0,11 | 0,00 % | 1 |
| 60/40 SPY/IEF | 0,815 | 8,87 % | −21,19 % | 0,32 | 0,02 % | 173 |
| Poche 1 seule | 0,347 | 4,36 % | −35,64 % | 18,9 | 0,35 % | 2 810 |
| Poche 1 seule, sans frais | 0,367 | 4,70 % | −35,62 % | 18,9 | 0,00 % | 2 817 |
| Poche 2 seule | 0,923 | 25,27 % | −33,97 % | 12,2 | 0,32 % | 1 855 |
| Poche 3 seule | 0,921 | 26,38 % | −33,05 % | 11,0 | 0,30 % | 1 914 |
| Poche 4 seule | 0,976 | 15,70 % | −20,04 % | 21,4 | 0,22 % | 949 |

Ce que ces runs montrent :

- **La poche 1 est la plus faible**, alors qu'elle a la plus grosse part (35 %), et
  elle le reste sans frais : les frais ne lui coûtent que 0,34 point de CAGR. Les
  poches 2 et 3 portent le rendement ; le mélange ramène la pire baisse à −21,5 %.
- **Les frais suivent le nombre d'ordres.** Environ 680 ordres par an, à 0,10 point de
  base du capital de départ en moyenne, à peu près le minimum par ordre du modèle de
  frais : le même nombre d'ordres pèse plus lourd, en proportion, sur un capital plus
  petit.
- **Écart à la fiche.** Sur la fenêtre de 5 ans de la fiche (2021-09-28 → 2026-09-25),
  CAGR 18,61 % contre 31,8 % affichés, pire baisse −19,29 % contre −22,9 %. L'écart
  n'est pas attribuable sans le code d'origine.
- **Corrélations hebdomadaires** avec les paniers proxys du projet compagnon : 0,69
  (`vt2`) et 0,57 (`aw`) sur la fenêtre principale, où leur Sharpe (1,048 et 1,033)
  dépasse celui de la 774.

Détail complet (sous-périodes, ordres refusés, version du code, chemin des séries) :
[commentaire de verdict sur #18904](https://github.com/jsboige/CoursIA/issues/18904#issuecomment-5983808875).

### Suivi en ombre

La stratégie est gelée à la date du verdict, avec ses paramètres par défaut, au commit de
`main` qui porte ces fichiers (empreinte de `main.py` revérifiée : `9b4ff36fc02d…`, celle
des runs du verdict). Elle est inscrite au
[registre du suivi en ombre](../../ML-Training-Pipeline/shadow/registry.json) (#18923) sous
l'identifiant `fs774`, gelée au 2026-10-04 ; premier passage à la première séance de novembre.

## Variante 775 — Adaptive ETF and Stock Momentum (#20168)

La stratégie publique **775** « Adaptive ETF and Stock Momentum » du même auteur (v1.0.1
du 28/09/2026, [discussion 21465](https://www.quantconnect.com/forum/discussion/21465/))
recombine des briques de la 774 : une poche d'ETF tactiques (45 %) qui ajoute à la
rotation des ETF à levier ×3 et inverses sur le Nasdaq-100 et les semi-conducteurs, et
une poche de momentum des grandes capitalisations (55 %) avec une sortie complète en bons
du Trésor quand la largeur du marché se dégrade. Son projet publié n'est pas plus lisible
que celui de la 774 : `layout=775` est écrit d'après la description publique, avec la
même méthode. Protocole et règle de verdict, inscrits avant le premier backtest :
issue [#20168](https://github.com/jsboige/CoursIA/issues/20168), fille de la ligue de
stratégies [#19821](https://github.com/jsboige/CoursIA/issues/19821).

`layout=775` réutilise l'univers, l'EMA, l'ADX, le stress de largeur, l'exécution et le
contrat `shadow` de la 774 : rien n'est dupliqué. Les titres propres à la 775 ne sont
souscrits qu'avec ce paramètre ; avec `layout=774` (défaut), le code se comporte comme
avant. L'entrée gelée `fs774` se rejoue au SHA de son gel.

### Choix déclarés de la 775

| Point laissé ouvert | Choix de cette réimplémentation |
|---------------------|---------------------------------|
| Parts des poches | poche actions 55 % (clé 3), poche ETF 45 % (clé 4) ; les poches 1 et 2 de la 774 sont vides |
| Indice de bande | rang centile du stress du jour parmi les stress quotidiens des 200 dernières séances, recalculés sur l'historique au moment du choix mensuel |
| Marché agité | indice de bande ≥ 0,5 : 5 lignes au lieu de 10 |
| Mise à l'échelle | exposition de la poche actions × (1 − indice de bande / 2), de 100 % à 50 % ; le reste en bons du Trésor |
| Poids dans la poche actions | proportionnels au score de momentum (moyenne des rendements 3, 6 et 12 mois), titres au-dessus de leur EMA avec ADX sous `adx_max` et à score positif ; une place non pourvue va aux bons du Trésor |
| Sortie de largeur | au choix mensuel, stress > `stress_max` : toute la poche actions en bons du Trésor ; retour au premier choix mensuel où le stress est revenu sous `stress_max`, ou d'office 180 jours calendaires après la sortie |
| Rotation (70 % de la poche ETF) | SPY au-dessus de sa moyenne 200 jours : TQQQ, ou SHV si le RSI 10 de QQQ dépasse 79 ; sinon TQQQ si le RSI 10 de QQQ est sous 30 ; sinon SOXL si le RSI 10 de SMH est sous 30 ; sinon, QQQ sous sa moyenne 20 jours : celui de SQQQ et BSV qui a le RSI 10 le plus haut ; sinon le meilleur de TLT, IEF et GLD sur 21 séances s'il est positif, SHV sinon |
| Tendance Nasdaq (30 % de la poche ETF) | QQQ au-dessus de sa moyenne 100 jours : TQQQ à hauteur de min(1, 20 / VIX), par paliers de 0,25 ; motif de retournement (QQQ sous sa moyenne 100 jours, au-dessus de sa moyenne 20 jours, VIX sous sa moyenne 20 jours) : QQQ à la même échelle ; sinon VIX au-dessus de 1,2 fois sa moyenne 20 jours : SQQQ sur un quart de la sous-poche ; le reste en SHV |
| Bons du Trésor | ETF `SHV` (exempt du plafond de 30 %) |
| Plafond, rebalancement, ordres, frais | ceux de la 774 (tableau ci-dessus) : plafond de 30 % appliqué après addition des poches, poche actions le premier jour de bourse du mois, poche ETF chaque séance |

Deux contrôles, utilisés seulement par les runs descriptifs : `lev=1` exécute chaque ETF ×3
par son équivalent ×1 (le signal ne change pas), et `sleeve=etf` / `sleeve=stock` porte
une poche seule à tout le portefeuille. En fin de backtest, deux statistiques
d'exécution : `days_x3` (part des séances avec une cible non nulle sur un ETF ×3,
haussier ou inverse) et `days_out` (part des séances où la poche actions est en sortie
de largeur).

### Résultats de la 775

Règle de verdict pré-enregistrée dans le corps de #20168 avant le premier backtest.
Fenêtre 2012-01-03 → 2026-06-30, 3 642 rendements journaliers alignés : les nœuds de
backtest utilisés arrêtent la fin de fenêtre 90 jours avant la date du jour. Bootstrap
circulaire par blocs de 21 séances, 10 000 tirages, correction de Holm sur les deux
comparaisons.

#### Verdict : `NO BEATS` contre les deux références

| Comparaison | Différence de Sharpe | p Holm | IC 95 % | Verdict |
|-------------|----------------------|--------|---------|---------|
| 775 − SPY détenu | +0,358 | 0,171 | [−0,137 ; 0,847] | `NO BEATS` |
| 775 − QQQ détenu | +0,282 | 0,171 | [−0,135 ; 0,711] | `NO BEATS` |

Les deux différences sont positives, mais aucune n'est significative : la règle de
l'issue classe ce cas `NO BEATS`. Le run à frais doublés et la grille de robustesse ne
se lancent que si une p Holm passe sous 0,05 ; ils n'ont pas été lancés. Par
sous-période (descriptif), la différence est positive sur les trois contre SPY ;
contre QQQ, elle est négative sur 2017-2021 (−0,065).

#### Mesures par run

Sharpe à taux sans risque nul. Frais annuels en % du capital de départ.

| Run | Sharpe | CAGR | Pire baisse | Rotation / an | Frais / an | Ordres |
|-----|--------|------|-------------|---------------|------------|--------|
| 775 | 1,268 | 30,96 % | −26,28 % | 15,6 | 0,48 % | 4 428 |
| 775, ETF ×1 (`lev=1`) | 1,267 | 20,22 % | −23,89 % | 15,3 | 0,18 % | 4 271 |
| Poche ETF seule (`sleeve=etf`) | 1,124 | 35,65 % | −33,14 % | 21,2 | 0,76 % | 1 850 |
| Poche actions seule (`sleeve=stock`) | 1,109 | 24,92 % | −35,10 % | 10,4 | 0,16 % | 2 762 |
| 774 (`layout=774`), même fenêtre | 1,174 | 18,86 % | −21,48 % | 16,0 | 0,30 % | 9 890 |
| SPY détenu | 0,909 | 14,64 % | −33,68 % | 0,07 | 0,00 % | 3 |
| QQQ détenu | 0,985 | 19,76 % | −35,05 % | 0,07 | 0,00 % | 3 |

Ce que ces runs montrent :

- **Le levier ×3 ne change pas le Sharpe.** Avec le même signal et chaque ETF ×3
  exécuté par son équivalent ×1, le Sharpe est le même (différence +0,001,
  IC 95 % [−0,151 ; 0,158]). Le levier fait passer le CAGR de 20,2 % à 31,0 % et la
  pire baisse de −23,9 % à −26,3 %. La poche ETF vise un ETF ×3, haussier ou inverse,
  à 94 % des séances. C'est le constat de #20141 sur une autre stratégie : le levier
  change l'échelle du rendement, pas sa qualité.
- **Les poches seules** dépassent chacune leur référence sans significativité : poche
  ETF − QQQ +0,14 (p 0,27), poche actions − SPY +0,20 (p 0,28). Leur mélange relève le
  Sharpe (1,27 contre 1,12 et 1,11) et réduit la pire baisse (−26,3 % contre −33,1 %
  et −35,1 %).
- **La 775 contre la 774**, sur la même fenêtre : +0,09 de Sharpe (p 0,25, descriptif),
  avec moins de la moitié des ordres (4 428 contre 9 890).
- **Sortie de largeur** : la poche actions est entièrement en bons du Trésor pendant
  15 % des séances.
- **Écart à la fiche.** Sur 2021-07-01 → 2026-06-30, soit les 5 ans de la fiche décalés
  de trois mois par la fin de fenêtre : CAGR 37,8 % contre 41,3 % affichés, pire baisse
  −23,6 % contre −31,5 %. L'écart n'est pas attribuable sans le code d'origine.

#### Non-régression de `layout=774`

Le nouveau `main.py` en `layout=774` a été comparé au `main.py` gelé de la 774
(empreinte `9b4ff36fc02d…`, celle de l'entrée `fs774`) sur l'année 2020. Résultat :
mêmes 708 ordres (heure, titre, quantité, prix), même valeur du portefeuille à chacune
des 253 clôtures (écart maximal nul), mêmes frais. Seul l'ordre de soumission des
ordres d'une même séance diffère. Comme chaque exécution est rapportée à la valeur du
portefeuille à son instant, la rotation cumulée bouge d'au plus 0,0028 sur 18,17. Deux
exécutions du même code gelé diffèrent de la même façon (563 positions sur 708, au plus
0,0041) : l'écart vient du moteur, pas du changement.

#### Limites

- **Pas de période hors échantillon** : la 775 est publiée en 2026 et sa fiche couvre la
  même histoire.
- **Les ETF ×3 américains ne sont pas accessibles** à un investisseur particulier
  européen (#20141) : un `BEATS` aurait ouvert une transposition, pas une adoption.
- **Réimplémentation d'après la description publique** : un écart à la fiche peut
  venir des choix déclarés ci-dessus.

Pas de gel : la règle ne gèle la 775 qu'en cas de `BEATS`. Détail (sous-périodes, version
du code, chemin des séries) : commentaire de résultat sur
[#20168](https://github.com/jsboige/CoursIA/issues/20168).
