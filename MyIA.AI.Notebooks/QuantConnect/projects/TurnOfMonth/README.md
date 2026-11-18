# TurnOfMonth — effet de fin de mois

**Classe d’actifs :** actions américaines (SPY et QQQ dans l’algorithme)
**État :** stratégie archivée ; voir [ARCHIVE.md](ARCHIVE.md)

## Présentation

Ce projet explore l’effet de fin de mois (*turn of the month*, ToM) : l’algorithme
cherche à détenir des ETF autour du changement de mois et filtre ses entrées selon
la tendance de SPY. Il sert à étudier une anomalie calendaire, le filtrage de
régime et la dépendance des résultats à la période observée. Il est archivé et
n’est pas présenté comme une stratégie validée pour un usage en portefeuille.

L’algorithme [main.py](main.py) implémente la version archivée v2.1 : SPY et
QQQ, une fenêtre de quatre séances estimées à la fin du mois et les quatre
premières séances, un poids cible de 75 % par ETF (levier nominal total de 1,5×)
et un filtre de moyenne mobile simple sur 200 séances de SPY. Le code planifie
l’examen du signal 30 minutes après l’ouverture.

### Limite de calendrier

Le calcul de l’algorithme estime les séances restantes en multipliant les jours
civils restants par 0,7 ; il ne compte donc pas exactement les séances de bourse.
Le notebook de recherche, lui, construit la fenêtre à partir des séances
historiques. Ces deux méthodes ne sont pas équivalentes, notamment autour des
jours fériés et des mois atypiques ; aucune métrique n’est déduite de cette
comparaison entre implémentations.

## Mesures archivées rapportées

`ARCHIVE.md` attribue à la version v2.1 les métriques historiques suivantes
pour la période 2015–2026 :

| Version | Période indiquée dans l’archive | Sharpe | CAGR | Drawdown maximal |
|---|---|---:|---:|---:|
| v2.1, SPY + QQQ | 2015–2026 | 0,128 | 4,8 % | 23,7 % |

L’archive précise qu’il s’agit de résultats d’un backtest antérieur, non
reproduits lors de l’itération d’avril 2026. La période indiquée ne correspond
pas aux dates actuellement configurées dans [main.py](main.py) (début 2015,
fin 2024) : le tableau restitue le rapport historique de l’archive et ne prouve
pas ces métriques pour l’état actuel du code.

## Carnets de recherche

| Fichier | Rôle | Outils et portée |
|---|---|---|
| [research.ipynb](research.ipynb) | Analyse exploratoire de l’effet ToM et comparaison de fenêtres, d’univers, de levier, du filtre SMA200 et de sous-périodes. Le carnet contient six hypothèses (H1–H6). | Python, `yfinance`, pandas et NumPy ; séries SPY/QQQ récupérées via yfinance. Les résultats dépendent de ces données et des choix de calcul du carnet. |
| [quantbook.ipynb](quantbook.ipynb) | Reprise de l’analyse avec l’API `QuantBook` : fenêtres, univers SPY/QQQ/IWM/DIA, levier, filtres SMA et sous-périodes, avec graphiques comparatifs. | Environnement de recherche QuantConnect/Lean et historique chargé par `qb.history`. Le carnet vérifie la présence des symboles et la fraîcheur des données avant ses calculs. |

Le carnet `quantbook.ipynb` conserve les sorties de la réexécution Lean de
[la PR #8730](https://github.com/jsboige/CoursIA/pull/8730), sur les données du 3 janvier 2005 au 31 décembre 2025 : tableaux par
fenêtre, univers, levier, filtre et sous-période, ainsi que figures. Ces
résultats décrivent cette exécution et ne constituent pas un verdict sur la
stratégie. `research.ipynb` conserve ses propres sorties, distinctes de celles
de `QuantBook`. L’historique des variantes et les limites documentaires sont
détaillés dans [ARCHIVE.md](ARCHIVE.md).

Le code de `main.py` mentionne également des essais historiques H7–H9 dans sa
docstring. Ils ne font pas partie des six hypothèses H1–H6 présentées dans
`research.ipynb`.

## Exécution

Le dossier contient un projet Lean Python (`config.json`). Pour lancer
l’algorithme avec Lean CLI depuis sa racine :

```bash
lean backtest .
```

`quantbook.ipynb` requiert un kernel de recherche compatible avec QuantConnect
et les données Lean attendues par le carnet ; un kernel Python générique ne
fournit pas `QuantBook`. Cette documentation n’atteste pas d’une exécution
locale ou dans le cloud.

## Références

- Ariel (1987), « A Monthly Effect in Stock Returns ».
- Lakonishok et Smidt (1988), « Are Seasonal Anomalies Real? ».
