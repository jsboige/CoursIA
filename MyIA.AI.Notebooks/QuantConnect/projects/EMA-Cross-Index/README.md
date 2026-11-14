# EMA-Cross-Index

**Asset class:** US Equities (S&P 500 ETF)
**Cloud project ID:** 38090937 (mesure #21392 ; projet de contrôle, code d'origine : 38090932)

## Description

Dual EMA crossover on SPY (S&P 500 index ETF). Long when EMA(20) > EMA(60), flat otherwise.
Includes a 3-day cooldown after exit to prevent immediate re-entry on false signals.

Le couple EMA 20/60 a été retenu parmi les cinq meilleurs couples IS après comparaison sur la fenêtre OOS 2010–2015 : Sharpe de 0,853 en IS (2015–2026) et 1,325 en OOS, soit un rapport OOS/IS de 1,55, le plus élevé des cinq. La fenêtre OOS ayant servi à choisir le couple, elle ne constitue pas une validation finale indépendante et ne suffit pas à écarter le surapprentissage.
Slow=60 captures quarterly trends and reduces whipsaws compared to the standard 50-period.

## Paramètres

| Paramètre | Valeurs | Défaut | Rôle |
|---|---|---|---|
| `mode` | `strategy`, `spy`, `6040` | `strategy` | `strategy` garde la décision du code ; `spy` détient SPY à 100 % ; `6040` détient SPY à 60 % et BND à 40 %, rééquilibrés au début de chaque mois, une minute après l'ouverture |
| `start_date` | date `%Y%m%d` | 2015-01-01 | début de la fenêtre |
| `end_date` | date `%Y%m%d` | 2024-12-31 | fin de la fenêtre |

Les trois modes tracent chaque jour la valeur du portefeuille à l'ouverture de SPY (graphique `shadow`, séries `e0` à `e4`). Sans paramètre, la décision de la stratégie ne change pas : le contrôle ci-dessous le vérifie ordre par ordre.

## Verdict contre références détenues (#21392)

Le protocole a été écrit dans #21392 avant le premier backtest, sur le modèle de #21329. Les deux références tournent dans le même algorithme que la stratégie, sous le même modèle de courtage et avec le même préchauffage de 70 séances. La stratégie investit 95 % du portefeuille, les références 100 % : cet écart fait partie de la règle codée.

Les séries comparées sont la valeur du portefeuille à chaque ouverture de SPY. Les tests passent par `Paradox46Benchmarks/significance.py`, avec un taux sans risque nul :

- écart de Sharpe de Ledoit-Wolf ;
- bootstrap stationnaire ;
- écart de moyennes de Newey-West.

Sur chaque fenêtre, la correction de Holm porte sur les six p-valeurs.

Règle de verdict, écrite avant la mesure :

- `BEATS` : écart de Sharpe positif et significatif (Holm < 0,05) contre les deux références ;
- `NO BEATS` : Sharpe de la stratégie inférieur à celui de SPY détenu ;
- `INCONCLUSIVE` : tous les autres cas.

**Contrôle d'innocuité : tenu.** En mode `strategy`, sur la fenêtre codée, le code instrumenté reproduit le backtest du code d'origine (`101f5fa746c36af72d10a84efa147289`, projet 38090932) :

- 33 ordres sur 33, sans écart de date, de symbole ni de quantité ;
- 27 statistiques QC sur 27.

Les ordres de la stratégie (fenêtre codée et hors échantillon) sont tous horodatés à la clôture de New York ; aucun n'est passé à minuit.

| Fenêtre | Séances | Sharpe stratégie (taux nul) | SPY détenu (taux nul) | 60/40 (taux nul) | p Holm (Ledoit-Wolf, SPY / 60/40) | Verdict |
|---|---|---|---|---|---|---|
| Codée, 2015-01-02 → 2024-12-31 | 2516 | 0,862 | 0,786 | 0,802 | 1,0 / 1,0 | **INCONCLUSIVE** |
| Hors échantillon, 2025-01-02 → 2026-07-21 | 387 | 1,010 | 1,034 | 1,158 | 1,0 / 1,0 | **NO BEATS** |

Statistiques QC (calculées par QC avec son propre taux sans risque). Leurs Sharpe ne se comparent pas à ceux de la table du dessus : QC retranche un taux sans risque non nul et part de ses propres séries quotidiennes, alors que le protocole prend un taux nul sur la valeur du portefeuille à l'ouverture. Le classement des portefeuilles peut donc changer d'une table à l'autre, et le verdict se lit sur la table du dessus.

| Fenêtre | Mode | Sharpe QC (taux de QC, autre échelle) | CAGR | Pire baisse | Ordres | Backtest |
|---|---|---|---|---|---|---|
| Codée | stratégie | 0,501 | 9,33 % | 17,5 % | 33 | `39d9b0dd71da386114fc64d0046af1f1` |
| Codée | SPY détenu | 0,533 | 12,97 % | 33,7 % | 1 | `9f91c49c8e124ea3141ea370823bba43` |
| Codée | 60/40 | 0,441 | 8,41 % | 21,7 % | 201 | `30e513cd0cb6fc38161897a4a2b40a21` |
| Hors échantillon | stratégie | 0,419 | 10,77 % | 8,3 % | 5 | `fbbed475cd485afc8ec04749c37c638b` |
| Hors échantillon | SPY détenu | 0,651 | 18,49 % | 18,7 % | 2 | `c4c28921f8ae0a6f2d1413a02da707b7` |
| Hors échantillon | 60/40 | 0,554 | 12,80 % | 11,2 % | 30 | `5622c03350124887af1d7173efcd8a3a` |

Le backtest hors échantillon a été demandé jusqu'au 2026-10-19, mais il s'arrête le 2026-07-21 : les nœuds QC utilisés coupent les backtests environ 90 jours avant la date du jour. Aucun paramètre n'a été réglé sur cette période.

**Lecture.** Sur la fenêtre codée, la stratégie a le Sharpe ponctuel le plus élevé des trois portefeuilles. Sa pire baisse est près de deux fois plus faible que celle de SPY détenu, mais son CAGR est inférieur. L'écart de Sharpe n'est pas significatif : p brute de Ledoit-Wolf 0,77 contre SPY détenu, intervalle bootstrap à 95 % de −0,38 à +0,52. Hors échantillon, son Sharpe passe sous celui de SPY détenu. Le code actuel ne bat donc aucune des deux références de façon mesurable.

## Figures du notebook de recherche

Le notebook [`research.ipynb`](research.ipynb) documente la sélection des périodes EMA et la validation de robustesse : grille de Sharpe par périodes (fast/slow), backtest de référence, hypothèses H2 (triple EMA), H3 (filtre volume), H4 (cooldown post-faux-signal), H5 (trailing stop vs sortie EMA), H6 (ajout QQQ), classification des régimes de marché et filtre SPY SMA200. Provenance détaillée : [`MANIFEST.md`](assets/readme/MANIFEST.md).

Les chiffres de cette section et du tableau « Backtest Metrics » viennent de ce carnet. Ils sont calculés en pandas sur 2015-2026, hors moteur Lean. Plusieurs configurations testées ne sont pas le code actuel : la baseline 20/50 précède la v2.0, et le stop suiveur a été écarté. Ce ne sont pas des verdicts. La mesure du code actuel est la section précédente.

### H1 — la grille de périodes EMA confirme-t-elle que 20/50 n'est pas optimal ?

**Constat — grille IS (2015–2026)** : la heatmap révèle un **plateau (fast=8-12, slow=60-100)** et un pic à **fast=8, slow=100 (Sharpe 0.923)**. Dans cette même grille, EMA 20/60 obtient 0.853 et la baseline EMA 20/50 obtient 0.765 : le résultat de 20/60 dépasse la baseline, mais reste sous le pic de la grille. Ce classement décrit les combinaisons testées sur cette fenêtre ; il ne démontre pas une dominance générale.

**Comparaison OOS (2010–2015)** : pour EMA 20/60, le Sharpe est **0.853 en IS et 1.325 en OOS**. Le rapport OOS/IS est 1,55 (1,325 / 0,853), le plus élevé des cinq couples présélectionnés sur leur Sharpe IS. Les cinq couples ont un Sharpe OOS supérieur à leur Sharpe IS ; cette hausse générale ne permet donc pas à elle seule de conclure que le signal est structurel.

**Lecture** : la baseline EMA 20/50 choisie a priori N'EST PAS dans le top 5 de la grille IS. Le Sharpe du couple **fast=20, slow=60** (cohérent avec la capture trimestrielle) est supérieur à celui du 20/50 sur les deux fenêtres comparées. En revanche, le MaxDD IS est pratiquement identique : −25,6 % pour 20/60 contre −25,5 % pour 20/50 ; il n'est pas divisé par deux. Le couple 20/60 a été retenu après examen des résultats OOS des cinq candidats : ce choix reste exposé à la sélection des paramètres et mérite une validation indépendante.

<p align="center"><img src="assets/readme/ema-grid-heatmap.png" alt="Dual-panel « Grille Sharpe et MaxDD par périodes EMA » — heatmaps divergentes RdYlGn (axe X Fast EMA period [8,10,12,15,20] × axe Y Slow EMA period [30,40,50,60,100]) : Sharpe ratio panel gauche (range 0,62-0,92) avec le pic fast=8 slow=100 = Sharpe 0,923, EMA 20/60 à ~0,85 et baseline EMA 20/50 à ~0,76 ; MaxDD inversé panel droite (range 15,2-28,7 %, vert = plus petit) avec fast=20 slow=40 = -28,7 % pire DD (rouge), EMA 20/60 lit ~-25 % (jaune). Les Sharpe 0,923 et 0,853 proviennent de la même grille IS 2015-2026 ; le rapport OOS/IS de 1,55 pour 20/60 vient de la comparaison séparée avec 2010-2015, dont les résultats ont servi au choix parmi cinq couples." width="900"/><br/><em>H1 — Grille des Sharpe et MaxDD pour les périodes EMA (fast 8-20, slow 30-100), mesurée sur la fenêtre IS 2015-2026. Les couples fast=8/slow=100 et fast=20/slow=60 ont respectivement un Sharpe de 0,923 et 0,853 dans cette grille. Ce classement dépend des couples et de la fenêtre examinés ; il n'établit pas une dominance structurelle générale.</em></p>

### H2 — la triple EMA (fast/medium/slow) améliore-t-elle le signal ?

**Verdict — INFIRMÉ**. La triple EMA 8/21/55 (Sharpe 0.688) **dégrade systématiquement** la baseline dual (Sharpe 0.765). Le triple filtre exigeant fast > medium > slow génère 51 trades vs 19 baseline (+2.7×), time-in-market 64 % vs 77 % — c'est-à-dire qu'on whipsaw en plein milieu de tendances naissantes (2017-2018 et 2024 captent mal).

**Lecture** : la condition additionnelle « triple alignement » capture des retournements fantômes et rate les tendances fortes. Le marché trend-follow SPY 2015-2026 récompense la réactivité (dual EMA) plutôt que la confirmation (triple EMA). Le code garde DUAL.

<p align="center"><img src="assets/readme/ema-backtest.png" alt="Dual-panel « Performance cumulée: Dual vs Triple EMA vs SPY B&H » sur 2015-2026 : panel haut equity cumulée base 1 (Dual EMA 20/50 S=0,765 bleu fin ~2,5× ; Triple EMA 8/21/55 S=0,688 orange fin ~2,0× — UNDERPERFORME ; SPY B&H vert pointillé fin ~4,0×) ; panel bas drawdown comparé (Dual EMA bleu ~-25 %, Triple EMA orange ~-30 % plus profond). H2 verdict INFIRMÉ : la condition triple alignement fast>medium>slow capture des retournements fantômes et rate les tendances fortes." width="900"/><br/><em>H2 — performance cumulée (haut) et drawdown (bas). Dual EMA (bleu) finit à 2.5×, Triple EMA (orange) à 2.0×, SPY B&amp;H (pointillé vert) à 4.0×. La triple EMA UNDERPERFORME la baseline dual.</em></p>

### H3 — le filtre volume lors des cross-up valide-t-il le signal ?

**Verdict — INFIRMÉ**. La distribution des volumes aux cross-up (moyenne 0.84× du volume moyen) ne discrimine pas les mouvements réels. Le filtre « volume > 1.2× moyenne » rejette **trop** de cross-up valides, dégradant le Sharpe même à des seuils permissifs (0.8×, 1.0×).

**Lecture** : sur SPY en données journalières, le **volume n'est pas un signal directionnel** — il amplifie surtout les événements exogènes (FOMC, earnings season) qui ne créent pas d'edge systématique. La baseline EMA 20/50 reste la référence sans filtre.

### H4 — un cooldown post-faux-signal réduit-il les whipsaws ?

**Verdict — CONFIRMÉ (modeste)**. La distribution des rendements par trade (cf figure) est **légèrement asymétrique positive** (médiane ≈ +2 %, queue droite jusqu'à +50 % sur le trade gagnant de la reprise COVID). Sans cooldown, 5 trades perdants > 2 % sur 19 (26 %).

**Lecture** : un **cooldown 3 jours post-sortie** améliore le Sharpe baseline de **0.765 → 0.800 (+4.6 %)** et filtre les re-entrées sur faux cross-up. Le coût = 1 trade manqué (19 → 18), acceptable. Confirmé et intégré à la baseline v2.0.

<p align="center"><img src="assets/readme/ema-h4-cooldown.png" alt="Histogramme vertical « Distribution des rendements par trade - EMA 20/50 SPY » (axe X rendement par trade -0,05 à +0,5, axe Y nombre de trades 0 à 3, 19 trades au total) : médiane ~+2 % (ligne rouge verticale), queue droite épaisse jusqu'à +0,5 (COVID bounce outlier), ligne orange pointillée verticale « Seuil -5% » à gauche. Distribution asymétrique positive : 5 trades perdants >-2 % sur 19 (26 %), queue droite des gains plus épaisse que queue gauche des pertes." width="900"/><br/><em>H4 — distribution des rendements par trade (EMA 20/50 SPY). Asymétrie positive : médiane ≈ +2 %, queue droite +50 % (COVID bounce), queue gauche −3 %.</em></p>

### H5 — un trailing stop protège-t-il mieux que la sortie EMA ?

**Constat — compromis entre Sharpe, baisse et fréquence des transactions.** La sortie de la cellule 26 compare les stops sur la baseline EMA 20/50 : le stop à 3 % augmente le Sharpe de 0,765 à 0,855, mais porte le nombre de transactions de 19 à 68. Le stop à 5 % réduit la pire baisse de 25,5 % à 24,1 %, mais abaisse le Sharpe à 0,718 et porte le nombre de transactions à 37. La conclusion du carnet écarte le stop serré, qui change la fréquence de la stratégie, et les stops plus larges, qui dégradent le Sharpe. Ces résultats exploratoires ne démontrent pas un avantage hors échantillon.

**Lecture** : SPY 2015-2026 est dominé par les **mouvements tendanciels longs** (> 3 mois) où la sortie EMA reste en position jusqu'au retournement réel. Un trailing stop 5 % **casse trop tôt** sur les corrections intra-tendance (été 2023, mars 2024). La sortie EMA capture mieux la tendance globale.

<p align="center"><img src="assets/readme/ema-h5-trailing.png" alt="Dual-panel « Trailing Stop 5% vs EMA Exit seul » sur 2015-2026 : panel haut equity cumulée base 1 (EMA exit seul S=0,765 bleu fin ~2,5× ; Trail 5% + EMA exit S=0,718 orange fin ~2,3× UNDERPERFORME ; SPY B&H vert pointillé fin ~4,0×) ; panel bas drawdown avec/sans trailing stop (Sans trail bleu plus profond ~-25,5 %, Trail 5% orange ~-24,2 % marginalement contenu mais perd la capture post-COVID bounce). H5 verdict INFIRMÉ sur trail court : SPY 2015-2026 dominé par tendances longues où la sortie EMA capture mieux." width="900"/><br/><em>H5 — Trailing stop 5 % + EMA exit (orange) vs EMA exit seul (bleu). Sharpe 0.718 < 0.765 baseline. La courbe orange suit la bleue avec un léger retard sur les rebonds 2020/2023.</em></p>

### H6 — l'ajout de QQQ comme 2ème instrument diversifie-t-il ?

**Verdict — INFIRMÉ**. SPY 50 % + QQQ 50 % donne **Sharpe 0.612, CAGR 9.5 %** vs baseline SPY seul **Sharpe 0.765, CAGR 8.7 %** — donc CAGR légèrement supérieur mais Sharpe inférieur (β combinée plus élevée, MaxDD -27.4 % vs -25.5 %). Les deux signaux long corrèlent à 74 % du temps, ce qui limite la diversification.

**Lecture** : QQQ et SPY partagent la même macro US large-cap. Les 19 % de jours où l'un est long et l'autre out génèrent principalement des rendements SPY > QQQ (QQQ a plus de drawdown), donc **surpondérer QQQ coûte plus qu'il ne rapporte**. La baseline reste SPY seul.

### Régimes de marché — un filtre SPY > SMA200 améliore-t-il le signal ?

**Constat** : sur 2766 jours de trading (2015-2026), **77 % sont en régime Bull** (SPY > SMA200), 16 % Bear. Le signal EMA 20/50 reste en position 77 % du temps (TIM baseline). La heatmap regime-colorée révèle que **les 13 transitions bear (bandes rouges verticales) se corrèlent visuellement avec les drawdowns** les plus marqués (2020-Q1 COVID, 2022 inflation, 2023 mini-bear).

**Lecture** : la baseline capture naturellement la dynamique bull/bear sans filtre additionnel. Activer un filtre SPY > SMA200 sortirait du marché pendant les rallies post-transition (typiquement les 6 mois les plus rentables post-bear) — sous-performerait la baseline sur CAGR.

<p align="center"><img src="assets/readme/ema-regime.png" alt="Triple-panel vertical « Régimes de marché SPY + signal EMA + performance » sur 2015-2026 : panel haut « SPY avec régimes (rouge = Bear: SPY < SMA200) » (SPY bleu ~170→690, SMA200 orange pointillé ~170→620, 13 bandes rouges verticales Bear = 2015-Q4 / 2018-Q4 / 2019-Q2 / 2020-Q1 COVID / 2022-H1 inflation / 2022-Q3 / 2023 mini-bear) ; panel milieu « Signal EMA 20/50 (1 = en position) » step 0/1 bleu (TIM baseline ~77 %, en position sur 2015-2018 et post-2024 continu, oscillations plus fréquentes 2019-2023) ; panel bas « Performance cumulée: Strategy vs B&H » (EMA Strategy bleu fin ~2,5×, SPY B&H orange pointillé ~4,0× — UNDERPERFORME sur fenêtre bull continue)." width="900"/><br/><em>Régimes — SPY avec bandes rouges Bear (SPY < SMA200) en haut, signal EMA 20/50 (1 = en position) au milieu, performance cumulée strategy vs B&amp;H en bas. La stratégie coupe 23 % du temps et UNDERPERFORME le B&amp;H sur la fenêtre complète.</em></p>

### Synthèse — que montre la variante avec stop face à SPY détenu ?

**Bilan exploratoire — rendement inférieur à SPY détenu.** Parmi les variantes comparées dans la cellule 44, **EMA 20/60 + trail 5 %** livre :
- Sharpe 0.797 (+0.033 vs baseline 0.765)
- CAGR 9.0 % vs baseline 8.7 %
- MaxDD −24.2 % vs baseline −25.5 % (marginalement mieux)
- β strategy = 0.404 (exposition au marché réduite dans cette simulation)
- **Écart de rendement annualisé dans les séances bear : 10 pp**, affiché par la cellule 42 pour cette même variante EMA 20/60 avec stop de 5 % : −21,6 % contre −31,5 % pour SPY détenu. Le régime bear est défini par SPY sous sa SMA200 ; il s’agit des rendements annualisés sur ces seules séances, pas du CAGR de la période complète.

**Comparaison visuelle (cellule 42)** : le graphique superpose la baseline EMA 20/50 et la variante EMA 20/60 avec stop de 5 %, toutes deux autour de 2,5 fois le capital initial, contre environ 4 fois pour SPY détenu. Ces multiples sont des lectures approximatives de la figure, distinctes des CAGR calculés ; ils ne mesurent pas le code actuel avec cooldown et sans stop.

**Lecture** : cette variante présente une exposition au marché réduite et une baisse maximale moindre sur la fenêtre étudiée, au prix d’un CAGR inférieur à celui de SPY détenu. La période 2000–2010 n’est pas mesurée ici : son comportement sur ce cycle reste à tester. Les cellules 43 et 46 retiennent pour `main.py` **EMA 20/60 avec cooldown de trois jours, sans stop suiveur**, ce qui correspond au code actuel. La variante avec stop de la cellule 44 reste une comparaison de recherche ; ses résultats ne constituent ni une recommandation de déploiement ni une mesure du code actuel.

| Configuration | Sharpe | CAGR | MaxDD | Verdict |
|---------------|--------|------|-------|---------|
| **Baseline EMA 20/50** | 0.765 | 8.7 % | -25.5 % | Ancienne baseline (avant la v2.0) |
| **EMA 20/60 (rapport OOS/IS 1,55 parmi cinq candidats)** | 0.853 | 9.8 % | -25.6 % | Périodes retenues ; cooldown ajouté séparément |
| **EMA 20/60 + trail 5 % (variante défensive)** | 0.797 | 9.0 % | -24.2 % | Variante de recherche avec stop, non retenue |
| SPY Buy & Hold (2015-2026) | ~0.80* | 12.4 % | -33.7 % | Référence |

(*) Sharpe SPY B&H recalculé sur la fenêtre identique pour comparaison.

<p align="center"><img src="assets/readme/ema-sma200-filter.png" alt="Single-panel line chart « Performance finale: Baseline vs Configuration Optimale » sur 2015-2026 base 1 : Baseline EMA 20/50 (S=0,765) bleu fin ~2,5× ; Optimal EMA 20/60 + Trail5% (S=0,797) orange fin ~2,55× quasi-superposé à baseline (écart +4 % Sharpe à peine visible sur la courbe) ; SPY B&H vert pointillé ~4,0× (gap croissant post-2023). β de la variante avec stop = 0,404 ; son CAGR reste inférieur à celui de SPY détenu sur la fenêtre 2015-2026." width="900"/><br/><em>Synthèse — performance finale Baseline (bleu) vs Optimal EMA 20/60 + trail 5 % (orange) sur 2015-2026. Sharpe marginal +4 %, visuellement les deux courbes se superposent presque. Le bêta mesuré de la variante avec stop est de 0,404 ; son CAGR reste inférieur à SPY B&amp;H sur la fenêtre.</em></p>

## How to Run

**Lean CLI:** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/EMA-Cross-Index"`
```bash
lean backtest --project .
```

**QC Cloud:** mesuré le 2026-10-19 (#21392), voir la section « Verdict contre références détenues ». Les paramètres `mode`, `start_date` et `end_date` se passent au backtest.

## Backtest Metrics (2015-2026)

Mesures du carnet de recherche (pandas, hors moteur Lean), pas du code actuel : voir la note de la section « Figures du notebook de recherche ».

| Configuration | Sharpe | CAGR | MaxDD | Verdict |
|---------------|--------|------|-------|---------|
| Baseline EMA 20/50 (avant la v2.0) | 0.765 | 8.7 % | -25.5 % | Ancienne baseline |
| **EMA 20/60 (rapport OOS/IS 1,55 parmi cinq candidats)** | **0.853** | **9.8 %** | -25.6 % | Périodes retenues ; cooldown ajouté séparément |
| EMA 20/60 + trail 5 % (variante défensive) | 0.797 | 9.0 % | -24.2 % | Variante de recherche avec stop, non retenue |
| SPY Buy & Hold | ~0.80 | 12.4 % | -33.7 % | Référence bull market |

## Files

- `main.py` - Strategy (v2.0, EMA 20/60 with cooldown)
- `research.ipynb` - EMA period grid search and robustness validation (6 hypothèses H1-H6 + régimes + synthèse)
- `quantbook.ipynb` - Research QuantBook « EMA Crossover SPY Index » : reproduction QuantBook de la stratégie EMA crossover sur SPY

## References

- Brock et al. (1992), "Simple Technical Trading Rules and the Stochastic Properties of Stock Returns"
- research.ipynb: H1-H6 hypothesis testing on EMA parameters + régime analysis + α-vs-β décomposition
