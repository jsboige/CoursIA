# OvernightAnomaly-QC

L'anomalie de nuit sur le SPY : acheter à la clôture, revendre à l'ouverture suivante, chaque jour de bourse. Le projet mesure la règle contre son miroir (détenir la séance seulement) et contre le SPY détenu, avec et sans frais. La règle de décision a été publiée sur #28404 avant le premier backtest.

## Description

**Source.** Article de recherche QuantConnect n° 15296, « Overnight Anomaly ». L'article cite Quantpedia (« Overnight Anomaly ») et conclut que le rendement de nuit disparaît une fois les frais déduits : avec le modèle de frais du courtier IB, les frais d'un backtest de vingt ans y représentent près de 25 % du capital de départ.

**La règle** : chaque jour de bourse, un ordre au marché à la clôture (MOC) achète le SPY, et un ordre au marché à l'ouverture (MOO) le revend le lendemain. Le portefeuille ne détient donc le titre que de la clôture à l'ouverture suivante.

Le paramètre `mode` choisit le portefeuille :

| Mode | Portefeuille | Ordres | Rôle |
|---|---|---|---|
| `overnight` (défaut) | SPY de la clôture à l'ouverture suivante | MOC envoyé 20 minutes avant la clôture, MOO envoyé 5 minutes après | la règle |
| `intraday` | SPY de l'ouverture à la clôture | le miroir : MOO envoyé après la clôture, MOC 20 minutes avant la clôture suivante | diagnostic : la moitié du rendement que la règle laisse |
| `hold` | SPY détenu | un MOO à la première ouverture, plus aucun ordre ensuite | référence du verdict |

Les trois modes engagent 98 % du portefeuille ; les 2 % restants absorbent l'écart entre le cours d'envoi et le cours rempli. Le délai de 20 minutes respecte la limite de Lean, qui refuse un ordre MOC envoyé moins de 15,5 minutes avant la clôture, y compris les jours de clôture anticipée.

## How to Run

Projet QC Cloud : un `main.py` sans dépendance hors de Lean. SPY à la minute, cours bruts (les frais par action portent sur le vrai nombre de titres, et les dividendes sont versés en liquidités à qui détient le titre), compte sur marge du courtier IB. Paramètres :

- `mode` : `overnight`, `intraday` ou `hold` ;
- `fees` : `ib` (défaut, barème par action du courtier IB tel que Lean le modélise, avec minimum par ordre) ou `none` (frais nuls, pour mesurer ce que coûtent les frais) ;
- `slip_bps` : glissement constant par ordre, en points de base (défaut 0) ;
- `start`, `end` : format `%Y-%m-%d`, obligatoires, sans valeur par défaut. Une fin explicite évite que la coupure d'environ 90 jours de certains nœuds de backtest raccourcisse la fenêtre en silence.

Le graphique `shadow` suit le contrat du rejeu en ombre (#18923) : 5 minutes après chaque clôture du SPY, il porte la valeur du portefeuille, répartie sur les séries `e0` à `e4`, les frais cumulés divisés par la valeur de départ (`fees`) et la rotation cumulée, en fraction du portefeuille (`turnover`). Les statistiques d'exécution publient `invalid_orders`, `fees_pct_start` (frais en pourcentage du capital de départ) et `turnover`.

Le carnet `research.ipynb` (QuantBook, données LEAN journalières du SPY, décembre 2007 → juillet 2026) décompose le rendement entre la nuit et la séance, chiffre le coût d'un aller-retour, découpe par sous-période et par année, et écrit la règle de décision avant le verdict.

## Protocole (#28404)

La règle complète est le commentaire de pré-enregistrement de #28404. En résumé :

- **bras** : `overnight`, `intraday` et `hold` avec frais, plus `overnight` avec `fees=none` ;
- **fenêtres** : A = 2004-01-01 → 2015-12-31 (découverte), B = 2016-01-01 → 2026-07-31 (contrôle, lue après A) ;
- **règle**, sur le Sharpe QC de `overnight` avec frais : `BEATS` s'il dépasse celui de `hold` sur A **et** sur B ; `NO BEATS` s'il est inférieur à celui de `hold` sur B ; `INCONCLUSIVE` dans les autres cas ;
- **prédictions**, qui ne changent pas la règle : sans frais, le CAGR de `overnight` dépasse celui d'`intraday` sur les deux fenêtres ; avec frais, le CAGR de `overnight` est sous celui de `hold` sur les deux fenêtres ;
- **hors mesure** : les ordres MOC et MOO sont remplis au prix d'enchère, sans écart entre prix acheteur et prix vendeur ni impact de marché ; le glissement reste une sensibilité, hors verdict.

## Verdict

**`NO BEATS`** (QC Cloud, 2026-11-24, #28404). Sur la fenêtre de contrôle B, le Sharpe QC de `overnight` avec frais vaut 0,393, contre 0,573 pour `hold`. Il était déjà inférieur sur A (0,140 contre 0,235).

| Bras | Fenêtre | Sharpe QC | CAGR | Perte max. | Frais (% du capital de départ) | Ordres |
|---|---|---|---|---|---|---|
| `overnight` | A | 0,140 | 4,33 % | 31,9 % | 27,56 | 6 041 |
| `overnight`, `fees=none` | A | 0,293 | 6,29 % | 30,2 % | 0 | 6 041 |
| `intraday` | A | −0,166 | −1,02 % | 45,1 % | 18,96 | 6 040 |
| `hold` | A | 0,235 | 6,42 % | 50,8 % | 0,00 | 1 |
| `overnight` | B | 0,393 | 8,55 % | 29,5 % | 10,44 | 5 317 |
| `overnight`, `fees=none` | B | 0,448 | 9,32 % | 29,4 % | 0 | 5 317 |
| `intraday` | B | 0,078 | 4,15 % | 25,1 % | 9,03 | 5 316 |
| `hold` | B | 0,573 | 13,89 % | 31,5 % | 0,00 | 1 |

Aucun des huit backtests n'a d'ordre invalide.

- **Prédictions.** La seconde est tenue : avec frais, le CAGR de `overnight` reste sous celui de `hold` sur les deux fenêtres. La première ne se tranche pas avec les backtests, puisque le bras `intraday` n'a tourné qu'avec frais. Dans le carnet, sans frais, le CAGR de la nuit dépasse celui de la séance sur 2008-2015 (5,07 % contre 1,21 %) comme sur 2016-2026 (9,36 % contre 5,10 %).
- **Ce que coûtent les frais.** 27,6 % du capital de départ sur les douze ans de A, ce qui recoupe les près de 25 % sur vingt ans de l'article. Ils pèsent moins sur B (10,4 %), parce que le SPY y coûte plus cher et que le barème se paie par action.
- **L'anomalie brute.** Sans frais, la nuit bat le titre détenu en Sharpe sur A (0,293 contre 0,235), grâce à une perte maximale de 30 % contre 51 %. Ce sont les frais qui la font passer dessous. Sur B, elle ne bat le titre détenu ni avant ni après frais.
- **Le glissement**, mesuré dans le carnet hors verdict : à 1 pb par ordre, le rendement net de la nuit s'efface presque entièrement. Un remplissage réel ne pourrait que dégrader le résultat.
