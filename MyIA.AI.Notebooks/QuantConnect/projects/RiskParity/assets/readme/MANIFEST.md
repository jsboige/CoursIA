# Manifeste des figures — RiskParity

Audit vision fondateur c.454 (G.1 firsthand — 6 PNG lus via vision + attributions cell×output vérifiées par `set_title()`/`suptitle()` matching contre `research.ipynb`). Provenance de chaque figure (convention d'indexation **all-cells** du module `extract_readme_figures.py` : `cellule` = indice de cellule dans le notebook, `output` = indice de sortie de cette cellule). Sources vérifiées sur `origin/main`, extraites de [`research.ipynb`](../../research.ipynb) (notebook de recherche local).

| Figure | Fichier | Dimensions | Poids | Source (cellule · output) | Sujet |
|--------|---------|------------|-------|---------------------------|-------|
| Exploration | `rp-exploration.png` | 1544×487 | 114 Ko | cellule 4 · output 1 | **Dual-panel** : courbe « Rendements cumulés 2015-2026 » ($1 investi, 6 actifs) + heatmap « Matrice de corrélation ». GLD = meilleur Sharpe 0.81 + diversifieur (corr SPY 0.04) ; DBC sous-performant (S=0.20, CAGR 3.45 %) (§2) |
| H1 — Inverse-vol | `rp-h1-inversevol.png` | 1787×493 | 34 Ko | cellule 6 · output 1 | **Triple-panel bar chart** « Capital vs Contribution au Risque selon la méthode de pondération » : 60/40 vs 1/N vs Risk Parity. Verdict : 60/40 SPY+EFA = 78.9 % du risque vs RP SPY+EFA = 49.7 % — l'inverse-vol **égalise** les contributions (H1) |
| H2 — Backtest | `rp-h2-backtest.png` | 1586×986 | 166 Ko | cellule 8 · output 1 | **Dual-panel** : haut « Rendements cumulés : Risk Parity vs Benchmarks (2015-2026) », bas « Allocation Risk Parity au fil du temps » (aires empilées = poids dynamiques). RP Sharpe 0.544 < SPY 0.655 mais MaxDD -20.26 % vs SPY -33.72 % (H2) |
| H3 — Impact TLT | `rp-h3-tlt.png` | 800×495 | 187 Ko | cellule 12 · output 0 | **Quad-panel** « Analyse de la période TLT Pain (2020-2023) » : (1) TLT vs SPY vs GLD base 100, (2) Volatilité roulante 60j, (3) Poids Risk Parity, (4) Performance relative. Métriques : RP 24.1 % ≈ 60/40 24.5 % « SPY 55.8 % sur la fenêtre — downscale depuis 1587×983 |
| H4 — Lookback | `rp-h4-lookback.png` | 1387×487 | 34 Ko | cellule 14 · output 1 | **Dual-panel** : « Sharpe selon la fenêtre de volatilité » + « Max Drawdown selon la fenêtre de volatilité », 5 lookbacks 20/40/60/90/120j. Range Sharpe 0.544-0.580 quasi-plat = robustesse (non overfitté), winner 40j S=0.580 / MaxDD -19.29 % (H4) |
| Régime | `rp-regime.png` | 1387×587 | 36 Ko | cellule 16 · output 2 | **Bar chart mono-panel** « Rendements par régime : Risk Parity vs SPY », 5 régimes. Bull 2015-19 RP 29.7 vs SPY 76.1 ; Inflation 2022 RP -9.8 vs SPY -18.6 (RP perd 2× moins) ; Recovery 2023-25 RP 47.9 vs SPY 86.3 — RP échange upside contre protection (§7) |

**Total** : 6 figures, 573 Ko. **Politique** (#5654) : ≤200 Ko/fichier, downscale ≤1200 px max. H3 (297 Ko natif, dense) downscaled à 800×495 ; les autres passent natifs (34–166 Ko). Arc : exploration (GLD diversifieur) → H1 inverse-vol (égalisation des contributions au risque, SPY+EFA 78.9 % → 49.7 %) → H2 backtest risk parity (Sharpe 0.544 < SPY 0.655 mais MaxDD moitié moindre) → H3 impact TLT 2020-2023 (RP ≈ 60/40, loin de SPY) → H4 sensibilité au lookback (range 0.544-0.580 quasi-plat = robuste) → analyse par régime (RP perd 2× moins en inflation 2022, upside raboté en bull).

## Diagnostic G.1 firsthand (audit vision c.454)

| # | Fichier | Alt-text précédent | Verdict | Contenu réel vérifié |
|---|---------|---------------------|---------|----------------------|
| 1 | `rp-exploration.png` | « Analyse exploratoire des actifs (§2) » | **CONTENT-DRIFTED** (omet dual-panel + identité du diversifieur GLD) | **Dual-panel** 1544×487 : courbe « Rendements cumulés 2015-2026 » ($1 investi, 6 actifs) + heatmap « Matrice de corrélation ». Stats annualisées : SPY S=0.75/CAGR 13.46 %, EFA S=0.43, GLD S=0.81/CAGR 12.02 %/corr SPY 0.04 (diversifieur clé), DBC S=0.20/CAGR 3.45 %/corr 0.35 |
| 2 | `rp-h1-inversevol.png` | « Inverse-volatility weighting égalise les contributions (H1) » | **CONTENT-DRIFTED** (verdict juste mais omet la métrique pivot 78.9 % → 49.7 %) | **Triple-panel bar chart** 1787×493 « Capital vs Contribution au Risque selon la méthode de pondération » : 60/40 / 1/N / Risk Parity. 60/40 SPY+EFA = 78.9 % du risque, RP SPY+EFA = 49.7 % ; RP poids GLD 0.222 / risk 0.200, SPY 0.184 poids / 0.240 risk |
| 3 | `rp-h2-backtest.png` | « Simulation du backtest risk parity (H2) » | **CONTENT-DRIFTED** (omet dual-panel + le verdict Sharpe 0.544 < SPY 0.655 + MaxDD moitié moindre) | **Dual-panel** 1586×986 : haut « Rendements cumulés : Risk Parity vs Benchmarks (2015-2026) », bas « Allocation Risk Parity au fil du temps » (aires empilées poids dynamiques). RP Sharpe 0.544 vs SPY 0.655 (cell[10]) ; RP MaxDD -20.26 % vs SPY -33.72 % |
| 4 | `rp-h3-tlt.png` | « Impact de TLT en 2020-2023 (hausse des taux, H3) » | **CONTENT-DRIFTED** (omet quad-panel complet + métriques 24.1 % vs 55.8 %) | **Quad-panel** 800×495 « Analyse de la période TLT Pain (2020-2023) » : (1) TLT vs SPY vs GLD base 100, (2) Volatilité roulante 60j annualisée, (3) Poids Risk Parity, (4) Performance relative. Métriques 2020-2023 : RP 24.1 % ≈ 60/40 24.5 % « SPY 55.8 % |
| 5 | `rp-h4-lookback.png` | « Sensibilité au lookback de volatilité (H4) » | **CONTENT-DRIFTED** (omet dual-panel + verdict range 0.544-0.580 quasi-plat + winner 40j) | **Dual-panel** 1387×487 « Sharpe selon la fenêtre de volatilité » + « Max Drawdown selon la fenêtre de volatilité », 5 lookbacks 20/40/60/90/120j. Sharpe range 0.544-0.580 quasi-plat = robustesse (non overfitté) ; winner 40j S=0.580/MaxDD -19.29 % |
| 6 | `rp-regime.png` | « Analyse par régime de marché (§7) » | **CONTENT-DRIFTED** (omet le verdict pivot Inflation 2022 RP perd 2× moins) | **Bar chart mono-panel** 1387×587 « Rendements par régime : Risk Parity vs SPY », 5 régimes. Bull 2015-19 RP 29.7 vs SPY 76.1 ; COVID 2020 RP 10.0 vs SPY 17.2 (RP MaxDD -20.3 %) ; Inflation 2022 RP -9.8 vs SPY -18.6 (RP perd 2× moins) ; Recovery 2023-25 RP 47.9 vs SPY 86.3 |

**Score** : **0/6 ACCURATE** — **6 corrections content-driven**.

## Sous-pattern identifié c.454 — (g) CONTENT-DRIVEN DRIFT : alt-text générique omettant le contenu multi-panel réel

Contrairement aux sous-patterns précédents (dual-panel où le 2ᵉ subplot est invisible, noms de fichiers trompeurs, attributions cell×output inversées, sweeps NULS/DISCRIMINANTS), le défaut c.454 est **purement content-driven** : les alt-text d'origine sont **génériquement justes** (ils nomment bien l'hypothèse H1/H2/H3/H4 et le thème) mais **ne rendent pas compte du contenu réel** de la figure. Le pipeline d'auto-extraction génère l'alt-text à partir du **commentaire de cellule** (`# H1: Inverse-vol` → « Inverse-volatility weighting ») **sans lire le PNG** ni capturer :

- la **structure multi-panel** (dual/triple/quad-panel invisible — ex: rp-h3-tlt.png est un **quad-panel** mais l'alt-text dit juste « Impact de TLT »),
- les **valeurs mesurées** (Sharpe, MaxDD, rendements par régime, % contribution au risque),
- les **verdicts discriminants** (winner lookback 40j, GLD diversifieur corr 0.04, Inflation 2022 RP perd 2× moins).

**3 observations distinctes** :

1. **6/6 figures = alt-text générique juste mais incomplet** : aucune attribution cell×output inversée (contrairement à c.450 ForexCarry h1↔h4), aucun nom de fichier trompeur (contrairement à c.449/c.450), aucun sweep NUL/DISCRIMINANT mal caractérisé (contrairement à c.451/c.452/c.453). Le défaut est **uniformément content-driven** — le lecteur d'alt-text ignore la structure et les valeurs de chaque figure.

2. **Structure multi-panel systématiquement invisible** : exploration = dual-panel (courbe + heatmap), H1 = triple-panel (3 méthodes de pondération), H2 = dual-panel (equity + allocation), H3 = **quad-panel** (4 sous-figures TLT Pain), H4 = dual-panel (Sharpe + MaxDD), régime = mono-panel. L'alt-text générique ne mentionne **jamais** la structure multi-panel — c'est l'angle mort fondateur du pipeline.

3. **Sharpe headline MANIFEST/README = 0.399 FAUX vs notebook 0.544** : la ligne politique d'origine citait « Sharpe 0.399, contre-exemple pédagogique ». Vérification : `0.399` n'apparaît **dans aucune sortie** du notebook ; le verdict réel (cell[10]) est **Risk Parity Sharpe 0.544 < SPY 0.655** (MaxDD RP -20.26 % vs SPY -33.72 %). La valeur 0.399 provient du README `README.md` (« plafond structurel (Sharpe 0.399) ») et a été propagée au MANIFEST sans vérification. **Corrigé c.454 : 0.544** (source : cell[10]·out[0]).

## Cause racinaire confirmée

Alt-texts d'origine générés par **auto-extraction à partir des commentaires de cellule** (e.g. `# H1: Inverse-vol` → alt-text « Inverse-volatility weighting »), sans lecture visuelle du PNG ni capture des `set_title()`/`suptitle()` des subplots ni des valeurs imprimées dans les outputs texte. Corrigé c.454 par audit visuel + vérification croisée du code source des cellules (`set_title()` matching) et des outputs numériques.

## Découverte majeure c.454 — Risk Parity = protection downside au prix de l'upside ( Sharpe 0.544 < SPY 0.655 mais MaxDD moitié moindre)

Contrairement à l'alt-text « contre-exemple pédagogique » (Sharpe 0.399) qui suggère une stratégie défaillante, le notebook documente un **compromis risque-rendement délibéré et partiellement validé** :

| Métrique | Risk Parity | SPY | Verdict |
|---|---|---|---|
| Sharpe (2015-2026) | 0.544 | 0.655 | RP perd ~17 % en Sharpe |
| CAGR | 7.28 % | 13.46 % | RP rend ~ moitié |
| MaxDD | -20.26 % | -33.72 % | **RP MaxDD ~ moitié moindre** |
| Inflation 2022 | -9.8 % | -18.6 % | **RP perd 2× moins** |
| Recovery 2023-25 | 47.9 % | 86.3 % | RP upside raboté |

**Conclusion** : la stratégie Risk Parity **ne bat pas SPY** en rendement absolu, mais **réduit le drawdown d'environ moitié** (MaxDD -20 % vs -34 %) et **perd 2× moins en régime d'inflation** (2022 : -9.8 % vs -18.6 %). C'est un **compromis défensif** (protection downside vs upside), pas un « contre-exemple défaillant ». Le verdict « plafond structurel » reste valable (RP ne surperforme pas SPY en Sharpe), mais le Sharpe réel est **0.544** (pas 0.399).

## Différence c.454 vs cycles précédents vague QC

| Cycle | Projet | Défaut dominant | Sharpe headline |
|---|---|---|---|
| c.447 | AllWeather | dual-panel subplot invisible + 2 FAUX alt-texts | — |
| c.448 | EMA-Cross-Crypto | dual-panel 4/5 + 2 FAUX alt-texts | 0/10 zone cible |
| c.449 | EMA-Cross-Index | dual/triple-panel + noms trompeurs | Dual S=0.765 < SPY ~4.0 |
| c.450 | ForexCarry | **attributions cell×output SWAPÉES** | v3e S=1.69 winner |
| c.451 | LongShortHarvest-QC | sweeps NULS + 1 FAUX alt-text | Stress S=-0.2 |
| c.452 | ML-RandomForest | sweeps DISCRIMINANTS | 4/5 battent SPY (Universe 5 S=1.118) |
| c.453 | ML-XGBoost | DOUBLE-NATURE + inversion feature importance | **0/15 battent SPY** |
| **c.454** | **RiskParity** | **(g) CONTENT-DRIFTED uniforme** (6/6 alt-text génériques) + **Sharpe headline FAUX 0.399→0.544** | **RP 0.544 < SPY 0.655, MaxDD moitié moindre** |

**Particularité c.454** : seul cycle de la vague QC où le défaut est **purement content-driven** (ni attribution inversée, ni nom trompeur, ni sweep mal caractérisé) — l'angle mort du pipeline est ici l'**incomplétude uniforme** plutôt qu'une erreur ponctuelle. Et seul cycle où une **valeur numérique headline** (Sharpe 0.399) s'avère **inexacte** vs le notebook (0.544), propagée depuis le README.

## Preuves vérifiables

- 6/6 PNG ouverts via `Read` (vision), analysés et décrits dans le MANIFEST enrichi
- 6/6 attributions cell×output confirmées via `python json.load(research.ipynb)` + matching `set_title()`/`suptitle()` :
  - `rp-exploration.png` → cell[4] out[1] ✓ (`set_title('Rendements cumules 2015-2026')` + `set_title('Matrice de correlation')`)
  - `rp-h1-inversevol.png` → cell[6] out[1] ✓ (`suptitle('Capital vs Contribution au Risque selon la methode de ponderation')`)
  - `rp-h2-backtest.png` → cell[8] out[1] ✓ (`set_title('Rendements cumules: Risk Parity vs Benchmarks (2015-2026)')` + `set_title('Allocation Risk Parity au fil du temps')`)
  - `rp-h3-tlt.png` → cell[12] out[0] ✓ (`suptitle('Analyse de la periode TLT Pain (2020-2023)')` + 4 `set_title`)
  - `rp-h4-lookback.png` → cell[14] out[1] ✓ (`set_title('Sharpe selon la fenetre de volatilite')` + `set_title('Max Drawdown selon la fenetre de volatilite')`)
  - `rp-regime.png` → cell[16] out[2] ✓ (`set_title('Rendements par regime: Risk Parity vs SPY')`)
- Sharpe headline corrigé : `0.399` absent de toute sortie notebook ; verdict réel cell[10]·out[0] = Risk Parity Sharpe 0.544, SPY 0.655, RP MaxDD -20.26 % vs SPY -33.72 %

## Cumul EPIC #5780 vague QC projets

| Cycle | PR | Projet | Figures | Ratio |
|-------|----|---------|---------|-------|
| c.438 | #6541 | DualMomentum | 4 | 4:4 systemic |
| c.447 | #6655 | AllWeather | 6 | 5:1 systemic |
| c.448 | #6656 | EMA-Cross-Crypto | 5 | 5:5 doctrinal |
| c.449 | #6661 | EMA-Cross-Index | 6 | 6:6 doctrinal |
| c.450 | #6668 | ForexCarry | 6 | 6:6 doctrinal + 2 ATTRIB inversées |
| c.451 | #6671 | LongShortHarvest-QC | 6 | 6:6 doctrinal + 1 FAUX alt-text + 3 sweeps NULS |
| c.452 | #6674 | ML-RandomForest | 6 | 6:6 doctrinal + 5 sweeps DISCRIMINANTS |
| c.453 | #6676 | ML-XGBoost | 6 | 6:6 doctrinal + DOUBLE-NATURE + inversion feature importance + sous-perf SPY |
| **c.454** | **(cette PR)** | **RiskParity** | **6** | **6:6 content-driven drifted + Sharpe headline 0.399→0.544 corrigé** |

**14/16 projets QC couverts** (cf `QuantConnect/projects/`). La vague QC projets est **COMPLETE** pour les projets à figures README. Voir [#5780](https://github.com/jsboige/CoursIA/issues/5780).
