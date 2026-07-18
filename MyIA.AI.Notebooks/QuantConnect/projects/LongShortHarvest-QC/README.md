# LongShortHarvest-QC

**Asset class:** US Equities (long/short)
**Cloud project ID:** None (local only)

## Description

QC Strategy Library clone. Long/short equity strategy harvesting alpha from both directions via pairs-style mean reversion.

## Figures du notebook de recherche

Le notebook [`research.ipynb`](research.ipynb) documente l'analyse complète : backtest de référence sur SPY/GLD/VIX, sensibilité aux hyperparamètres (sweep `score_threshold` H1, `ext_k` H2), validation walk-forward et performance par régime de marché. Provenance détaillée : [`MANIFEST.md`](assets/readme/MANIFEST.md).

**Référence — backtest long-terme 2007-2026, l'ancre du diagnostic.** La figure de référence pose le profil de la stratégie sur ~19 ans : un **dual-panel** empilé (equity + drawdown, axe temporel commun 2007-2026) issu de `backtest_lsh()` sur les sous-jacents SPY/GLD/VIX. La courbe d'equity monte de ~1.0 à ~8.0 USD (gain cumulé ~7×), avec accélération post-COVID de ~5 à ~8 entre 2020 et 2024-2025. Le drawdown en aire rouge marque **trois pics majeurs** : -18 % mi-2008 (Lehman), -16 % mi-2020 (COVID), -11 % en 2022 (bear bonds), recovery rapide entre chaque. Les **métriques extraites de `research.ipynb` cell[9]·out[0]** sont **Sharpe 0.939, CAGR 11.47 %, MaxDD -17.96 %, WinRate 55.3 %** (note : le tableau « Backtest Metrics » ci-dessous conserve la valeur 3.39 / 57.94 % du QC Strategy Library d'origine — chiffre **non reproduit localement**, à ne pas confondre avec la perf `research.ipynb`).

<p align="center">
  <img src="assets/readme/lsh-reference.png" alt="Dual-panel equity + drawdown LongShortHarvest 2007-2026 (1.0→~8.0, MaxDD -18 %)" width="840"/><br>
  <em>Référence — equity + drawdown LongShortHarvest 2007-2026 (cell[9]·out[1] du notebook de recherche).</em>
</p>

**H1 — sweep `score_threshold`, verdict nul.** La première hypothèse teste la sensibilité au seuil de score d'entrée (filtre de qualité du signal) sur 6 valeurs `ST ∈ {0.7, 0.75, 0.8, 0.85, 0.9, 0.95}`. Le **dual-panel barres** juxtapose Sharpe et MaxDD par seuil : les 6 barres Sharpe sont **quasi-identiques à ~0.94** (seule `ST=0.9` est colorée verte comme winner marginal à 0.944, cf cell[11]), et les 6 barres MaxDD sont **strictement identiques à -17.96 %**. **Verdict : sweep NUL** — le paramètre `score_threshold` est **inopérant** sur la métrique Sharpe/MaxDD, les différences sont < 1 % entre tous les seuils. Aucun gain de robustesse ni de drawdown à attendre d'un raffinement de ce seuil.

<p align="center">
  <img src="assets/readme/lsh-h1-sweep.png" alt="Sweep H1 score_threshold NUL — 6 barres Sharpe ≈0.94, 6 barres MaxDD ≈-18 %" width="840"/><br>
  <em>H1 — sweep score_threshold : Sharpe ≈0.94 et MaxDD ≈-18 % invariants sur 6 seuils (sweep nul, cell[11]·out[1]).</em>
</p>

**H1 (suite) — courbes de capital par seuil, sweep nul visuel.** Pour confirmer le verdict quantitatif, la cellule suivante superpose les **6 courbes d'equity** correspondantes sur 2007-2026 : ligne bleue `ST=0.7`, orange `ST=0.75`, verte `ST=0.8`, rouge `ST=0.85`, violette `ST=0.9`, marron `ST=0.95`. Les 6 courbes sont **superposées à 1 pixel près** sur tout l'horizon — le profil est strictement le même, ~1 → ~5 sur 2007-2020 puis ~5 → ~8 sur 2020-2025 (rallye post-COVID). **Confirmé visuellement** : raffiner `ST` ne produit aucune courbe distinctive. La légende haut-gauche permet de vérifier l'identité des 6 séries.

<p align="center">
  <img src="assets/readme/lsh-h1-equity.png" alt="6 equity curves score_threshold superposées 2007-2026 (sweep nul visuel)" width="840"/><br>
  <em>H1 (suite) — 6 courbes d'equity superposées à 1 pixel près : aucun seuil ne se distingue (cell[12]·out[0]).</em>
</p>

**H2 — sweep `ext_k` (multiplicateur ATR), verdict nul identique.** La deuxième hypothèse teste la sensibilité au multiplicateur d'ATR sur 5 valeurs `ext_k ∈ {1.0, 1.5, 2.0, 2.5, 3.0}`. Les **5 courbes d'equity** correspondantes sont tracées sur 2007-2026 (légende haut-gauche : bleu 1.0, orange 1.5, vert 2.0, rouge 2.5, violet 3.0). Profil **identique au sweep H1** : ~1 → ~5 sur 2007-2020 puis ~5 → ~8 sur 2020-2025, **5 courbes superposées à 1 pixel près**. Le sweep quantitatif Sharpe (`ext_k=3.0` → 0.941 winner marginal, cf cell[14]) confirme : **variations < 0.5 %** entre les 5 valeurs, le paramètre est **inopérant sur la perf long-terme**. Conclusion stratégique : le moteur est robuste au choix du multiplicateur ATR, pas besoin de tuner finement.

<p align="center">
  <img src="assets/readme/lsh-h2-equity.png" alt="5 equity curves ext_k superposées 2007-2026 (sweep nul)" width="840"/><br>
  <em>H2 — 5 courbes d'equity par multiplicateur ATR superposées à 1 pixel près (sweep nul, cell[15]·out[0]).</em>
</p>

**Validation walk-forward — la robustesse inter-régime.** Pour tester la stabilité hors-échantillon, l'analyse walk-forward découpe l'historique en **3 fenêtres disjointes** : 2007-2012, 2012-2018, 2018-2025. Le **dual-panel** juxtapose les equity curves (haut) et les drawdowns par période (bas) sur le même axe temporel. Verdict (cell[24]) : **fenêtre 1 (2007-2012)** Sharpe 0.790, CAGR 11.79 %, MaxDD -17.96 %, gain cumulé ~100 % avec pic mi-2011 puis crash -12 % fin 2011 ; **fenêtre 2 (2012-2018)** Sharpe 0.702, CAGR 5.41 %, MaxDD -8.38 %, croissance linéaire modérée (~50 % sur 6 ans) ; **fenêtre 3 (2018-2025)** Sharpe **1.165**, CAGR **13.80 %**, MaxDD -16.22 %, **explosion** post-COVID (~185 % sur 7 ans). **Verdict global** : la **3ᵉ fenêtre écrase les 2 précédentes** (Sharpe 1.165 vs 0.79 vs 0.70), validant la robustesse en régime récent mais performance molle sur 2007-2018. Lecture prudente : backtest très dépendant du rallye post-2020.

<p align="center">
  <img src="assets/readme/lsh-walkforward.png" alt="Walk-forward 3 fenêtres : 2007-2012 (~100 %), 2012-2018 (~50 %), 2018-2025 (~185 %)" width="840"/><br>
  <em>Walk-forward — equity + DD par fenêtre, la 3ᵉ fenêtre (2018-2025) écrase les 2 précédentes (cell[25]·out[0]).</em>
</p>

**Régimes de marché — dépendance forte au VIX.** Pour comprendre dans quels environnements la stratégie performe (et où elle perd), l'analyse par régime segmente l'historique en **3 buckets VIX-based** : Calme (VIX<15), Normal (15-25), Stress (VIX>25). Le **triple-panel barres** juxtapose Sharpe (gauche), rendement annuel (milieu), volatilité (droite) par régime, avec palette sémantique vert/bleu/rouge. Verdict (cell[27]) : **Calme (VIX<15)** sur 1538 jours, **Sharpe 3.7**, rendement **+22.88 %/an**, vol 6.02 % — **excellent** ; **Normal (15-25)** sur 2372 jours, **Sharpe 1.075**, rendement **+9.90 %/an**, vol 9.21 % — correct ; **Stress (VIX>25)** sur 868 jours, **Sharpe -0.156** (négatif), rendement **-3.64 %/an**, vol 23.37 % — **perdant**. **Conclusion stratégique** : la stratégie **excelle en Calme**, **tient en Normal**, **perd en Stress** — dépendance forte au régime, à coupler avec un **filtre VIX pour live** (désactiver quand VIX>25 pour éviter les épisodes perdants).

<p align="center">
  <img src="assets/readme/lsh-regime.png" alt="Triple-panel Sharpe/Rendement/Volatilité par régime VIX : Calme S=3.7, Normal S=1.05, Stress S=-0.2" width="840"/><br>
  <em>Régimes VIX — Calme S=3.7 (excellent), Normal S=1.075 (correct), Stress S=-0.156 (perdant, désactiver) (cell[27]·out[1]).</em>
</p>

## How to Run

**Lean CLI:** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/LongShortHarvest-QC"`
**QC Cloud:** Not yet deployed. Copy files to a new QC Cloud project to run.

## Backtest Metrics

Les chiffres du tableau « Source = QC Strategy Library clone » restent **historiques** (Sharpe 3.39, CAGR 57.94 %, MaxDD -15.20 %) et **n'ont pas été reproduits localement**. Les **valeurs effectives** du notebook `research.ipynb` (cell[9]·out[0], référence paramètres originaux) sont reportées dans le tableau « Source = research.ipynb » et correspondent à la figure `lsh-reference.png` ci-dessus.

| Metric | Value | Source |
|--------|-------|--------|
| Sharpe Ratio | 0.939 | research.ipynb cell[9]·out[0] |
| CAGR | 11.47 % | research.ipynb cell[9]·out[0] |
| Max Drawdown | -17.96 % | research.ipynb cell[9]·out[0] |
| WinRate | 55.3 % | research.ipynb cell[9]·out[0] |
| Sharpe Ratio | 3.39 | QC Strategy Library clone (non reproduit) |
| CAGR | 57.94 % | QC Strategy Library clone (non reproduit) |
| Max Drawdown | -15.20 % | QC Strategy Library clone (non reproduit) |

## Files

- main.py - Strategy (QC Library clone)

## References

- QuantConnect Strategy Library
