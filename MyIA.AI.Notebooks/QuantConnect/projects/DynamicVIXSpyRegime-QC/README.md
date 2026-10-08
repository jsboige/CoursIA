# DynamicVIXSpyRegime-QC

**Classe d'actifs :** Actions US (SPY)
**ID projet Cloud :** QC Project ID: 32921262 (redeployed 2026-06-15)

## Description

Clone de la QC Strategy Library #50 (Dynamic VIX-SPY Regime Switching par Ahmet Kasti). Détection de régime basée sur le VIX sur SPY, alternant entre positionnement agressif et défensif. Overlay ML (RandomForestClassifier, 11 features VIX/SPY).

## Mesures

### Mesure #19825 : `NO BEATS`, lecture du VIX du jour même corrigée

Backtests QC Cloud du 2026-10-08, du 2015-01-02 au 2026-07-08 (2893 séances), avec les frais du modèle de courtier fixé par le code. Le protocole et la règle de verdict ont été fixés avant tout calcul ([#19825](https://github.com/jsboige/CoursIA/issues/19825)). Le Sharpe est calculé à taux sans risque nul sur la valeur du portefeuille à chaque clôture, par une analyse hors dépôt ; il diffère donc du Sharpe affiché par QC, qui retranche un taux sans risque.

**Lecture du VIX du jour même.** La classe `CBOE` datait chaque ligne du CSV à son jour de bourse, sans heure de fin. Lean livre une donnée personnalisée à son heure de début : la clôture du VIX du jour D était donc visible dès D 00:00, et `CheckSignal`, qui tourne à D 10:00, décidait sur une clôture encore inconnue à cette heure. Le compteur ajouté le confirme :

| Compteur | `base` (code d'origine) | `lag` |
|----------|-------------------------|-------|
| Décisions dont la dernière ligne VIX lue est du jour même | 2894 sur 2894 | 0 sur 2894 |
| Entraînements mensuels dont le VIX finit après SPY | 139 sur 139 | 2 sur 139 |

Le mode `lag` date chaque ligne du lendemain de son jour de bourse : la décision de D ne voit que la clôture de D-1, comme pour SPY. Les deux entraînements résiduels ne sont pas expliqués ; hypothèse non vérifiée : des jours où le CSV du CBOE porte une ligne et SPY aucune barre.

| Version | Sharpe | CAGR | Pire baisse | Rotation par an | Frais par an (part du portefeuille) |
|---------|--------|------|-------------|-----------------|-------------------------------------|
| `lag` (défaut) | 0,80 | 10,1 % | −30,9 % | 30,7 | 0,24 % |
| `base` (code avant #19825) | 0,77 | 9,6 % | −30,2 % | 30,7 | 0,25 % |
| SPY détenu (`spy`) | 0,82 | 13,7 % | −33,7 % | 0,09 | 0,00 % |
| 60 % SPY / 40 % IEF (`sixty40`) | 0,87 | 8,8 % | −21,2 % | 0,28 | 0,01 % |

**Verdict.** Il est `NO BEATS` pour `lag` comme pour `base` : les deux écarts de Sharpe avec les références sont négatifs, et aucun n'est significatif. La différence est testée par bootstrap circulaire par blocs de 21 séances (10 000 tirages, correction de Holm sur les deux références).

| Candidate | Écart avec SPY [IC 95 %] | Écart avec le 60/40 [IC 95 %] | p Holm |
|-----------|--------------------------|-------------------------------|--------|
| `lag` | −0,02 [−0,30 ; +0,31] | −0,07 [−0,32 ; +0,22] | 1,00 |
| `base` | −0,05 [−0,31 ; +0,26] | −0,10 [−0,35 ; +0,19] | 1,00 |

Par sous-période (2015-2018, 2019-2022, 2023 → 2026-07), `base` ne devance les deux références que sur 2015-2018 ; `lag` les devance sur 2015-2018 et 2023-2026, et recule sur 2019-2022. La grille de paramètres et le run à frais doublés n'étaient prévus que pour une candidate significative : ils n'ont pas été lancés.

**Part du résultat due à la lecture du jour même.** L'écart de Sharpe `base` − `lag` vaut −0,03 [−0,16 ; +0,10], à titre descriptif, hors correction de Holm. Lire la clôture du jour n'apportait aucun avantage mesurable : les deux versions passent à peu près le même nombre d'ordres (3927 contre 3830), et leurs rendements hebdomadaires sont corrélés à 0,98.

**Ce que la stratégie détient.** Sous `lag`, le gain clos vient surtout de SPY, puis de GLD ; TLT finit en perte. Les rendements hebdomadaires de `lag` sont corrélés à 0,86 avec SPY détenu et à 0,89 avec le 60/40 : la rotation suit le marché d'actions de près, pour une rotation de plus de 30 fois le portefeuille par an.

**Choix du défaut.** Le protocole prévoyait que le mode par défaut devienne `lag` si le compteur confirmait la lecture du jour même : c'est le cas. Le changement retire une information qui n'existait pas à l'heure de la décision ; il ne crée pas d'avantage mesuré.

**Limites.**
- Les seuils (VIX 13 et 20, percentile 80, 3 %, 1,2) et la fenêtre de 2015 viennent de la bibliothèque QC, publiée après une partie de la période : il n'y a pas de période hors échantillon. Ce biais favorisait la candidate, ce qui renforce le `NO BEATS`.
- Les backtests demandaient une fin plus tardive ; les nœuds de calcul utilisés retiennent les 90 derniers jours et ont ramené la fin au 2026-07-08, sans erreur. Toutes les versions ont tourné sur les mêmes nœuds : les comparaisons portent sur les mêmes séances.

### Chiffres antérieurs à #19825

Le tableau ci-dessous date d'avant la mesure ; il est conservé pour l'historique.

| Source | Sharpe | CAGR | MaxDD | Période | Univers |
|--------|--------|------|-------|---------|---------|
| **QC Strategy Library #50** (revendication originale, `main.py:10`) | **1.72** | **29.76%** | **17.80%** | **OOS 1Y** (5Y CAGR — window non précisée) | SPY + TLT + GLD + BIL |
| `research.ipynb` cell[9] (exec=5) — BASELINE (paramètres défaut) | **0.97** | **23.83%** | **-22.09%** | 2015-01-02 → 2025-12-30 (2765 jours) | SPY + TLT + GLD + BIL + ^VIX |
| `research.ipynb` cell[26] (exec=13) — **BEST (H3: Exposition gross=2.0)** | **1.023** | **31.35%** | **-29.07%** | 2015-01-02 → 2025-12-30 (2765 jours) | idem |
| `research.ipynb` cell[9] (exec=5) — **Benchmark SPY Buy & Hold** | 0.536 | 13.54% | -33.72% | 2015-2025 | SPY seul |

L'ancien README concluait que « l'edge de la stratégie est reproductible » et que `research.ipynb` était la référence de la stratégie déployable.

**Lecture corrigée par #19825.**
- **`research.ipynb` ne mesure pas `main.py`.** Le notebook décale déjà le VIX d'un jour (`vix_c[i-1]`), applique une exposition brute de 1,5 et calcule son Sharpe avec un taux sans risque de 4 % (`calculate_metrics(..., risk_free=0.04)`). Ses chiffres décrivent une autre règle. Il ne compare pas non plus sa différence avec SPY à un test.
- **`main.py` sur sa propre fenêtre.** Le run `orig` (`base`, 2015-01-01 → 2024-12-31) donne un Sharpe de 0,70 à taux sans risque nul (0,39 selon QC), un CAGR de 8,5 %, une pire baisse de −30,2 % et 3386 ordres. Il ne reproduit ni le 0,97 / 23,83 % du notebook, ni la revendication de la bibliothèque, dont la fenêtre n'est pas précisée.
- **Statut du registre.** Le « 69.4% (backtest vérifié) » de `docs/qc/qc-strategies-status.md` n'apparaissait nulle part dans le projet ; il est remplacé par le verdict ci-dessus.

## Hypothèses testées (extrait `research.ipynb`)

Ces configurations portent sur la règle du notebook (VIX décalé d'un jour, exposition brute paramétrable, Sharpe avec un taux sans risque de 4 %), pas sur `main.py`. Cf. `research.ipynb` cell[3] et cell[26] pour le tableau comparatif complet (12 configurations). Top 3 par Sharpe :

| Config | Sharpe | CAGR | MaxDD | WinRate |
|--------|--------|------|-------|---------|
| **H3: Exposition gross=2.0** | **1.023** | 31.35% | -29.07% | 55.2% |
| H1: Seuil ML threshold=0.6 (= baseline) | 0.970 | 23.83% | -22.09% | 55.2% |
| H3: Exposition gross=1.5 | 0.970 | 23.83% | -22.09% | 55.2% |

## Comment exécuter

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/DynamicVIXSpyRegime-QC"`
**QC Cloud :** QC Project ID `32921262` (redeployed 2026-06-15). Le notebook `research.ipynb` utilise le kernel QC Cloud (RandomForest + StandardScaler + données CBOE VIX non chargés en Docker local).

**Paramètres du projet** (tous facultatifs) :

| Paramètre | Défaut | Rôle |
|-----------|--------|------|
| `mode` | `lag` | `lag` : VIX livré le lendemain de son jour de bourse ; `base` : code d'origine (VIX du jour même) ; `spy` : SPY détenu ; `sixty40` : 60 % SPY et 40 % IEF, rééquilibrés le premier jour de bourse de chaque mois |
| `start`, `end` | `2015-01-01`, `2024-12-31` | fenêtre du backtest |
| `vix_pct` | 80 | percentile du VIX qui signale un pic |
| `ml_threshold` | 0.6 | seuil de probabilité de la forêt aléatoire |
| `vix_low` | 13 | seuil de « VIX bas » |
| `fee_mult` | 1 | multiplicateur des frais du courtier |

Le graphique `shadow` porte la valeur du portefeuille à chaque clôture ; les statistiques d'exécution donnent le nombre d'ordres par ETF et les compteurs de la lecture du VIX.

## Fichiers

- `main.py` - Stratégie (clone QC Library #50, 4-asset regime switching + ML overlay), instrumentée pour la mesure #19825
- `research.ipynb` - 5 hypothèses H1-H5 + tableau comparatif + benchmark SPY (2015-2025, 2765 jours), sur la règle du notebook

## Références

- QuantConnect Strategy Library #50 - Dynamic VIX-SPY Regime Switching par Ahmet Kasti : https://www.quantconnect.com/strategies/50
- Brock et al. (1992), "Simple Technical Trading Rules and the Stochastic Properties of Stock Returns"
- `research.ipynb` cell[0] (MD) : méthodologie complète avec hyperparamètres ML et features VIX/SPY
