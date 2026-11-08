# PuppiesOfTheDow-QC

**Classe d'actifs :** Actions US (composantes du Dow Jones)
**ID projet Cloud :** 39061051 (mesure #25130)

## Description

Clone de la stratégie 211 de la Strategy Library QuantConnect, *Puppies of the Dow Value-Income Tilt*, que la bibliothèque rattache à Michael O'Higgins, *Beating the Dow* (1991). Les « Dogs of the Dow » sont les dix titres du Dow Jones au plus haut rendement. Les « Puppies » sont les cinq moins chers de ces dix.

À la première séance de chaque année, `main.py` :

1. prend les constituants de l'ETF DIA (le Dow 30), servis à la date de la sélection ;
2. garde ceux dont le prix dépasse 5 et dont le rendement est positif ;
3. retient les 10 plus hauts rendements, puis les 5 moins chers de ces 10 ;
4. place 20 % du capital sur chacun et vend les autres positions.

Le portefeuille tourne avec les frais du modèle de courtage déclaré dans le code, en compte sur marge, et un capital de 100 000. Il n'a ni levier, ni couverture, ni stop.

## Ce que le code trie : le rendement total, pas le rendement du dividende

L'en-tête du code annonce un classement par rendement du dividende (« rank by dividend yield »). Le code trie pourtant sur `valuation_ratios.total_yield`. D'après la documentation de Lean (classe `ValuationRatios`), ce champ est « The total yield that shareholders can expect, by summing Dividend Yield and Buyback Yield ». Il s'agit donc du dividende plus les rachats d'actions.

Le choix change la sélection. Le contrôle `div` trie sur `trailing_dividend_yield`, le rendement du dividende annoncé par l'en-tête. Sur les 17 sélections de la fenêtre principale, `base` et `div` ne retiennent les mêmes cinq titres qu'une seule année. En moyenne, ils ont 2,6 titres en commun. Le rendement total fait entrer des titres qui rachètent beaucoup leurs actions. Par exemple, Travelers en 2010 affiche un rendement total de 13,9 %, et HP en 2012 un rendement total de 19,8 %. Ni l'un ni l'autre n'entre dans la sélection `div` de la même année.

## Port : ce qui change et ce qui ne change pas

La règle de trading est reprise sans changement : univers, filtres, tri, tailles, poids, date de rééquilibrage, courtier.

Ce qui change :

- **Fenêtre.** Le code d'origine appelle `set_start_date(self.end_date - timedelta(12*365))` **avant** `set_end_date(2025, 1, 1)`. Il lit donc la date de fin par défaut de Lean, et non le 2025-01-01. Le début se déplace avec la date du lancement : deux runs du même code ne couvrent pas la même période. Le port prend les dates en paramètres, avec pour défauts l'intention lisible du code, 12 × 365 jours avant le 2025-01-01, soit 2013-01-04 → 2025-01-01.
- **Paramètres de mesure.** Avec les défauts, la règle est celle d'origine.
- **Instrumentation de mesure.** Un graphique `shadow` porte la valeur du portefeuille à chaque clôture, ainsi que les frais cumulés et la rotation. C'est le contrat du rejeu en ombre (#18923). Chaque sélection est écrite au journal (`select <date> constituents=.. eligible=.. chosen=TITRE:prix:rendement,...`). Les sélections, rééquilibrages et ordres refusés sont comptés dans les statistiques d'exécution.

| Paramètre | Valeurs | Rôle |
|---|---|---|
| `start`, `end` | 2013-01-04, 2025-01-01 | fenêtre |
| `mode` | `base` (défaut), `dogs`, `spy`, `dia` | `base` : règle d'origine ; `dogs` : les 10 plus hauts rendements à 10 % chacun, sans l'étape de prix ; `spy`, `dia` : l'ETF détenu à 100 % sur le même harnais, comme référence |
| `yield_field` | `total` (défaut), `dividend` | champ trié : `total_yield` (code d'origine) ou `trailing_dividend_yield` |
| `n` | 5 (défaut) | taille du portefeuille |
| `fee_mult` | 1 (défaut) | multiplicateur des frais du courtier |

## Lancer

- **Lean CLI** : `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/PuppiesOfTheDow-QC"`. Les paramètres se passent avec `--parameter <nom> <valeur>`, par exemple `--parameter mode spy`.
- **QC Cloud** : projet 39061051, qui porte ce `main.py`. Les paramètres se règlent dans l'onglet des paramètres du projet.

Le seul fichier du projet est `main.py`.

## Sources

- **Règle** : Michael O'Higgins, *Beating the Dow*, 1991, cité par la bibliothèque. Le livre n'est pas archivé : ce README ne lui attribue rien, et la règle mesurée est celle du code.
- **Code** : QuantConnect Strategy Library, stratégie 211, <https://www.quantconnect.com/strategies/211>, clonée le 2026-04-05.
- **Champ `total_yield`** : documentation de Lean, classe `ValuationRatios`.

## Mesure (#25130)

La règle de verdict a été inscrite dans le body de l'issue #25130 avant le premier backtest. Elle est appliquée ici sans changement.

**Protocole.** La fenêtre principale va du 2010-01-04 au 2026-07-31, soit 4 168 séances communes à tous les passages. Les constituants de DIA sont servis dès le 2010-01-04 : l'essai court du 2010-01-04 au 2010-03-31 l'a vérifié avant les autres runs. La statistique est l'écart de Sharpe journalier, sans taux sans risque, entre `base` et chaque référence : SPY et DIA, détenus sur le même harnais. Le p unilatéral vient d'un bootstrap circulaire par blocs de 21 séances (10 000 tirages, graine 18921), corrigé par Holm sur les deux références.

`base` ne gagne (**BEATS**) que s'il remplit trois conditions :

- p Holm < 0,05 contre au moins une référence ;
- contre cette référence, un écart positif à frais doublés et sur au moins deux des trois sous-périodes (2010-2015, 2016-2020, 2021 → 2026-07-31) ;
- un écart positif sur au moins quatre des cinq tailles de portefeuille (`n` de 3 à 7).

### Résultats

| Passage | Sharpe (sans taux) | Sharpe QC | CAGR | Drawdown max | Rotation / an | Frais / an, en part du capital initial | Ordres |
|---|---|---|---|---|---|---|---|
| `base` (candidate, règle d'origine) | 0,74 | 0,50 | 12,0 % | −25,1 % | 1,19 | 0,043 % | 126 |
| `spy` (référence) | 0,87 | 0,61 | 14,1 % | −33,5 % | 0,06 | 0 | 1 |
| `dia` (référence) | 0,81 | 0,55 | 12,5 % | −36,3 % | 0,06 | 0 | 1 |
| `dogs` (contrôle, les 10 à 10 %) | 0,90 | 0,63 | 14,1 % | −31,0 % | 0,90 | 0,031 % | 225 |
| `div` (contrôle, tri sur le dividende) | 0,62 | 0,39 | 9,2 % | −39,9 % | 0,70 | 0,032 % | 106 |

Le « Sharpe QC » est celui des statistiques de QuantConnect, calculé avec un taux sans risque. La rotation compte la valeur échangée, rapportée à la valeur du portefeuille. Aucun ordre n'a été refusé dans aucun passage.

### Verdict

| Référence | Écart de Sharpe | IC 95 % | p Holm | 2010-2015 | 2016-2020 | 2021-2026 | Verdict |
|---|---|---|---|---|---|---|---|
| SPY | −0,13 | [−0,51 ; 0,23] | 1,00 | +0,05 | −0,41 | −0,01 | **NO BEATS** |
| DIA | −0,07 | [−0,43 ; 0,26] | 1,00 | +0,07 | −0,35 | +0,05 | **NO BEATS** |

Les deux écarts sont négatifs, et aucun n'est significatif. La règle ne demande donc ni passage à frais doublés ni grille sur `n`, et aucun n'a été lancé.

La pire baisse de `base` (−25,1 %) est plus faible que celle de SPY (−33,5 %) et de DIA (−36,3 %). Mais son rendement l'est aussi, et son Sharpe reste en dessous des deux références. L'écart vient surtout de la sous-période 2016-2020 (−0,41 contre SPY, −0,35 contre DIA) ; sur les deux autres, il reste proche de zéro.

### Lectures descriptives

Ces lectures n'entrent pas dans le verdict.

1. **L'étape de prix.** L'écart de Sharpe `base` − `dogs` vaut −0,16, IC 95 % [−0,38 ; 0,04], p unilatéral 0,94. Garder les cinq moins chers des dix ne fait pas mieux que garder les dix. Le prix nominal d'une action ne mesure pas sa valorisation, et le filtre divise par deux le nombre de lignes. Le Sharpe de `dogs` dépasse celui de SPY, mais ce bras de contrôle n'a pas été testé contre les références.
2. **Le champ de rendement.** L'écart `base` − `div` vaut +0,12, IC 95 % [−0,15 ; 0,39], p unilatéral 0,18. Le tri sur le dividende seul, celui qu'annonce l'en-tête, fait moins bien que le tri du code, sans écart significatif.
3. **Les deux références.** Sur la même fenêtre, l'écart DIA − SPY vaut −0,05, IC 95 % [−0,19 ; 0,10] : les deux références sont proches, d'où des verdicts semblables.
4. **La fenêtre d'intention du code.** Le passage `orig` est `base` sur 2013-01-04 → 2025-01-01 : il couvre 3 017 séances, et ses sélections de 2013 à 2024 sont celles de `base`. Son Sharpe vaut 0,68, sa CAGR 10,9 % et sa pire baisse −25,1 %. Sur ces mêmes séances, SPY fait 0,89 (CAGR 14,3 %) et DIA 0,81 (CAGR 12,5 %). L'écart contre SPY vaut −0,21 (IC 95 % [−0,70 ; 0,21]), et contre DIA −0,13 (IC 95 % [−0,58 ; 0,26]).
5. **Les chiffres de la bibliothèque** : Sharpe hors échantillon sur un an de 1,99, CAGR sur cinq ans de 10,16 %, pire baisse sur cinq ans de 22,90 %. La bibliothèque ne date pas ses fenêtres. Sur des fenêtres reconstituées qui finissent à la date du clone (2026-04-03), `base` donne :
   - sur l'année : un Sharpe de 2,02, contre 1,28 pour SPY ;
   - sur cinq ans : une CAGR de 9,0 % et une pire baisse de −21,6 %, contre 11,6 % et −24,5 % pour SPY.

   Le 1,99 publié est donc du même ordre que le Sharpe d'une seule année favorable. Sur seize ans et demi, le Sharpe de la même règle vaut 0,74.
6. **Le registre du dépôt** citait un backtest sur 2018-2025 (projet 32732704) : Sharpe 0,302, CAGR 9,61 %, pire baisse 28,80 %, 60 ordres. Sur 2018-01-02 → 2024-12-31, `base` donne un Sharpe sans taux de 0,37, une CAGR de 5,6 % et une pire baisse de −25,1 %. Ce chiffre n'est pas reproduit, et son départ exact est inconnu : avec le défaut de fenêtre du code d'origine, il dépendait de la date du lancement.

### Limites

- **Peu de décisions.** La règle choisit une fois par an : la fenêtre principale porte 17 sélections. Les sous-périodes ne disent pas toutes la même chose.
- **Deux champs de rendement seulement.** Les autres définitions (dividende prévisionnel, rendement de l'année civile, dates d'O'Higgins) ne sont pas mesurées.
- **Constituants à la date.** Les constituants de DIA sont servis à la date de chaque sélection (Kraft en 2010, HP jusqu'en 2013, DowDuPont en 2019, Dow à partir de 2020). L'univers suit donc l'indice. Il porte 31 constituants le 2022-01-03, jour d'une transition de composition.
- **Paramètres d'origine.** La taille de cinq titres et le seuil de prix sont repris tels quels. La grille sur `n` n'a pas été lancée, faute de significativité.

Les traces de chaque passage sont rangées hors dépôt, dans `G:\Mon Drive\MyIA\IA\QC-traces\25130-puppies-dow`. Elles comprennent les plans, les identifiants de backtest, les graphiques `shadow`, les journaux complets et de sélection, et `results.json`. On y trouve aussi les scripts d'analyse et la version de `main.py` qui a tourné (empreinte `9566325cd7c3`). Ces scripts s'appuient sur `shadow_replay`, `strategy_metrics` et `voltarget_strategy_verdict` de `ML-Training-Pipeline/scripts`.
