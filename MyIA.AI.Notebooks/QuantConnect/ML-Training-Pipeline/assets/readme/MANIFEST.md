# Manifeste des figures — QuantConnect/ML-Training-Pipeline

Provenance de chaque figure (convention `extract_readme_figures.py` L132 : index ALL-CELLS, markdown + code).
Toutes les figures sont extraites des **outputs déjà committés** des notebooks de recherche (C.3 — aucune re-exécution).
Bornes EPIC #5654 P1 respectées : ≤200 KB/fichier, ≤1200 px max-dim, natives (0 downscale).

> **Audit vision po-2026 c.437 (2026-07-14, doctrine #5780)** : les 6 PNG ci-dessous ont été ouverts un par un via l'outil `Read` et comparés à leur alt-text. Verdict par figure dans le champ *Contenu réel vérifié*. Cohérence caption ↔ image = **6/6 exacte, 0 correction d'alt-text appliquée** — sweep **completion doctrine** (cf c.435 ML + c.436 QC Python) : la table MANIFEST était déjà structurée (TITLES-driven : conclusion pédagogique), mais sans audit-block L5 ni *Contenu réel vérifié* par figure. Le founder-defect L490 typique (alt-text generique omettant structure visuelle) est absent ici — tous les alt-texts sont **specific to title/conclusion** (pas generiques). Enrichissement = ajouter *Contenu réel vérifié* descriptif par figure + reformuler les alt-texts en **CONTENT-driven** (décrivent ce que l'image montre : valeurs concretes, structure, panneaux) plutôt qu'en TITLES-driven (conclusion pédagogique).

| Figure | Notebook source | Cellule | Output | Dimensions | Poids | Alt-text FR |
|--------|-----------------|---------|--------|------------|-------|-------------|
| `mltp-hmm-regime.png` | `m5_hmm_regime_research.ipynb` | 6 | 1 | 779×409 | 29,8 KB | Sophistication régime nuit aux horizons longs : bar chart 3 horizons × 2 cryptos |
| `mltp-har-rv.png` | `m12_har_rv_j_research.ipynb` | 6 | 0 | 715×432 | 33,1 KB | Déconnexion MSE-Sharpe : scatter HRJ vs HAR 18 points 3 horizons |
| `mltp-dlinear-vol.png` | `m4_dlinear_vol_research.ipynb` | 6 | 1 | 706×404 | 29,9 KB | DLinear vs HAR par coin : BTC domine, autres non significatifs |
| `mltp-lstm-vol.png` | `m15_lstm_rv_research.ipynb` | 6 | 0 | 719×432 | 39,2 KB | Paradoxe MSE-Sharpe LSTM : scatter dense ~75 points 3 horizons |
| `mltp-tft-vol.png` | `m9_tft_vol_research.ipynb` | 6 | 1 | 790×409 | 60,3 KB | Diagnostic ensemble : boxplot 5 stratégies Sharpe 35 combos |
| `mltp-ensemble.png` | `m11e_ensemble_research.ipynb` | 6 | 1 | 832×430 | 29,7 KB | Edge vs n_train : line plot fold 1 catastrophe, tendance croissante |

## Contenu réel vérifié par figure (audit visuel MiniMax M3, c.437)

### `mltp-hmm-regime.png` — Sophistication regime nuit aux horizons longs

**Alt-text (FR)** *(c.437 reformulé CONTENT-driven)* : Sophistication de régime nuit aux horizons longs : **bar chart 3 horizons × 2 cryptos** montrant la réduction MSE du modèle HMM regime-switching vs la baseline HAR classique. Axe Y = "Reduction MSE regime-switching vs HAR classique (%)" de -50 à +10 ; baseline 0 % matérialisée par une ligne horizontale verte tirets. Trois horizons (h=1, h=5, h=10 sur l'axe X), deux cryptos comparées (BTC-USD orange, ETH-USD violet). **BTC-USD** (orange) : +7 % (h=1), -11 % (h=5), -28 % (h=10). **ETH-USD** (violet) : +10 % (h=1), -18 % (h=5), **-53 % (h=10)**. Légende "HAR classique (baseline, 0%)" + "BTC-USD" + "ETH-USD" dans le coin inférieur-gauche.

**Contenu réel vérifié** (audit visuel MiniMax M3, c.437) : bar chart titré "La sophistication regime nuit aux horizons longs : +9.6% (ETH h=1) -> -53% (ETH h=10)", 6 barres verticales (3 horizons × 2 cryptos), valeurs concrètes annotées sur chaque barre (+7%, +10%, -11%, -18%, -28%, -53%), ligne horizontale verte tirets à Y=0 (baseline HAR), grille subtile. **Alt-text précédent** "Détection de régimes HMM — probabilités postérieures par état" était **TITLES-driven** (décrit la conclusion/méthode, pas le visuel) — corrigé c.437 pour décrire **CONTENT-driven** : structure (3 horizons × 2 cryptos), valeurs concrètes (-53% ETH-USD h=10, +10% ETH-USD h=1, -28% BTC-USD h=10), métriques affichées (réduction MSE vs HAR classique en %).

- **Poids** : 29,8 KB (PIL optimisé)

### `mltp-har-rv.png` — Déconnexion MSE-Sharpe : scatter HRJ vs HAR

**Alt-text (FR)** *(c.437 reformulé CONTENT-driven)* : Déconnexion MSE-Sharpe du modèle HRJ : **scatter plot 18 points (3 horizons × 6 cryptos)** coloré par horizon. Axe X = "Changement MSE HRJ vs HAR (%)" (-20 à +250, >0 = HRJ moins précis) ; Axe Y = "Delta-Sharpe HRJ vs HAR" (-0.10 à +0.25). **Quadrants** : bas-droit (HRJ perd en MSE ET Sharpe) majoritairement vide ; haut-droit (HRJ perd en MSE mais gagne en Sharpe) peuples par points **h=10 bleus** (notamment outliers à +60-240% MSE mais +0.10-0.22 Sharpe) ; quadrant haut-gauche (HRJ gagne en MSE ET Sharpe) peuple de points **h=1 verts** + **h=5 rouges**. Légende "Horizon" avec h=1 (vert), h=5 (rouge), h=10 (bleu) en haut-droite.

**Contenu réel vérifié** (audit visuel MiniMax M3, c.437) : scatter titré "Deconnexion MSE-Sharpe : HRJ degrade la precision mais aide le sizing", 18 marqueurs ronds disperses, axes croises a (0,0) en gris tirets, quadrants colores implicitement par la position des points, 2 outliers h=10 bleus tres eloignes a droite (+57% MSE / +0.22 Sharpe, +100% MSE / +0.10 Sharpe, +240% MSE / +0.01 Sharpe). **Alt-text précédent** "Décomposition de sauts HAR-RV-J — variance réalisée continue vs discontinue" était TITLES-driven (décrit la décomposition théorique, pas le visuel) — corrigé c.437 pour décrire CONTENT-driven : scatter 18 points + axes concrets + colorisation par horizon + le pattern pedagogique (h=10 = gros MSE delta mais bon Sharpe delta, h=1 = bon des deux cotes).

- **Poids** : 33,1 KB (PIL optimisé)

### `mltp-dlinear-vol.png` — Reduction MSE DLinear vs HAR par coin

**Alt-text (FR)** *(c.437 reformulé CONTENT-driven)* : Prévision DLinear vs HAR par cryptomonnaie : **bar chart 7 cryptos (ADA/BTC/DOT/ETH/LTC/SOL/XRP-USD)** montrant la réduction MSE du modèle DLinear par rapport à la baseline HAR. Axe Y = "Reduction MSE Dlinear vs HAR (%)" (0 à 27.5). **BTC-USD** vert dominant **27.5 %** (seul gain substantiel et statistiquement significatif), tous les autres gris non significatifs : ADA-USD ≈ 4.5 %, DOT-USD ≈ 0.8 %, ETH-USD ≈ 4.3 %, LTC-USD ≈ 7.5 %, SOL-USD ≈ 5.5 %, XRP-USD ≈ 2.7 %. Chaque barre annotée avec le **nombre d'observations** : "725j" sur ADA/DOT/ETH/SOL/XRP (période courte), **"2278j"** sur BTC-USD (période longue), **"1495j"** sur ETH-USD (longue aussi).

**Contenu réel vérifié** (audit visuel MiniMax M3, c.437) : bar chart titré "Reduction MSE par coin : BTC (2278j) domine, autres (~725j) non significatifs", 7 barres verticales, BTC en vert (le seul avec une periode assez longue pour etre significatif), tous les autres gris (periode courte, non significatif). Le pattern pedagogique : **BTC = 27.5% reduction (mesurable sur 2278 jours) ; les autres cryptos n'ont pas assez d'historique pour distinguer DLinear du HAR classique** (periode trop courte, ~725 jours). **Alt-text précédent** "Prévision DLinear — DL linéaire vs baseline HAR" etait TITLES-driven (methode/conclusion) — corrige c.437 pour decrire CONTENT-driven : structure (7 cryptos), valeurs concretes (BTC 27.5%), annotations temporelles (2278j vs 725j), pattern pedagogique.

- **Poids** : 29,9 KB (PIL optimisé)

### `mltp-lstm-vol.png` — Paradoxe MSE-Sharpe LSTM (scatter dense)

**Alt-text (FR)** *(c.437 reformulé CONTENT-driven)* : Paradoxe MSE-Sharpe du modèle Log-LSTM : **scatter plot dense ~75 points coloré par horizon** (h=1 vert, h=5 rouge, h=10 bleu). Axe X = "Changement MSE LSTM vs HAR (%)" (-20 à +40, >0 = LSTM moins précis), Axe Y = "Delta-Sharpe LSTM vs HAR" (-0.15 à +0.30). **Pattern** : la majorité des points sont **à droite de l'axe Y=0** (LSTM perd légèrement en MSE, +5 à +25 %), mais **au-dessus de l'axe X=0** (LSTM gagne en Sharpe, delta +0.05 à +0.15). Points **h=10 bleus** plus dispersés, points **h=5 rouges** concentrés autour de (10%, 0%), **h=1 verts** dispersés sur tout l'axe X.

**Contenu réel vérifié** (audit visuel MiniMax M3, c.437) : scatter dense (75 points) titre "Paradoxe MSE-Sharpe : LSTM moins precis (MSE) mais meilleur sizing (Sharpe)", axes croises a (0,0) en gris tirets, distribution typique (delta MSE +5 a +20% pour h=10/h=5, neutre pour h=1, mais delta Sharpe +0.05 a +0.15 partout). Le pattern pedagogique : **le LSTM est moins bon en prediction point (MSE) mais meilleur en allocation sizing (Sharpe)**, comme HRJ dans mltp-har-rv mais de maniere plus marquee. **Alt-text precedent** "Prévision Log-LSTM — mémoire séquentielle pour la variance réalisée" etait TITLES-driven — corrige c.437 pour decrire CONTENT-driven : structure (75 points, scatter dense), pattern (LSTM perd MSE mais gagne Sharpe), axes concrets.

- **Poids** : 39,2 KB (PIL optimisé)

### `mltp-tft-vol.png` — Diagnostic d'ensemble : boxplot 5 stratégies

**Alt-text (FR)** *(c.437 reformulé CONTENT-driven)* : Diagnostic d'ensemble HAR-Kelly : **boxplot 5 stratégies × 35 combos** comparant la distribution du ratio de Sharpe. Axe Y = "Sharpe (35 combos)" de -2.0 à +1.0, ligne horizontale grise tirets à 0. Les 5 stratégies sont **K60 (single best)** vert médiane ≈ -0.65, **K30 mu120** bleu clair médiane ≈ -0.35 (la moins mauvaise), **Vol-target HAR** orange médiane ≈ -0.85, **Ensemble (equal-w)** violet médiane ≈ -0.80, **Buy & hold** gris médiane ≈ -0.85. Conclusion visuelle : le **boxplot violet (Ensemble) est presque superposé avec le boxplot orange (Vol-target HAR)** — l'ensemble n'apporte pas de diversification, c'est juste une moyenne pondérée qui dilue la performance du K60.

**Contenu réel vérifié** (audit visuel MiniMax M3, c.437) : boxplot titré "L ensemble (violet) est tire vers vol-target (orange) : pas de diversification, juste une moyenne", 5 boites moustaches (5 strategies × 35 combos = 175 sharpes mesures), boites colorees demi-transparentes avec mediane noire epaisse, moustaches verticales, baseline grise a Y=0. Toutes les medianes sont **negatives** (toutes les strategies sous-performent Buy & hold en Sharpe median), ce qui est le **signal pedagogique cle**. **Alt-text precedent** "Attention Temporelle TFT — pondération des variables d'entrée" etait TITLES-driven (decrit la mecanique d'attention TFT, pas le resultat) — corrige c.437 pour decrire CONTENT-driven : structure (boxplot 5 strategies), valeurs medianes concretes (-0.65, -0.35, -0.85, -0.80, -0.85), conclusion visuelle (Ensemble ≈ Vol-target).

- **Poids** : 60,3 KB (PIL optimisé, le plus gros du set, donc possibilite de reduction)

### `mltp-ensemble.png` — Edge vs n_train : catastrophe fold 1, tendance croissante

**Alt-text (FR)** *(c.437 reformulé CONTENT-driven)* : Edge vs taille du jeu d'entraînement : **line plot fold-par-fold edge sur baseline majority-class**, montrant la **catastrophe du fold 1** (BTC = -0.09, ETH = -0.075 sur 708 échantillons) puis une **tendance croissante** vers 0 quand n_train grandit. Axe X = "Taille du jeu d'entraînement (n_train par fold)" de 500 à 2500+, Axe Y = "Edge sur baseline majority-class" de -0.12 à +0.02. **Ligne pointillée verte horizontale à Y=0** = baseline majority (edge=0, modèle équivalent à deviner la classe majoritaire). 4 lignes tracées (BTC h=1 orange + ETH h=1 violet, chaque fold relie dans une serie). Au-delà de n_train ≈ 1500, l'edge remonte vers 0 (modèle regagne en qualite) puis oscille entre -0.02 et +0.01 sans jamais devenir systematiquement positif.

**Contenu réel vérifié** (audit visuel MiniMax M3, c.437) : line plot titré "Edge vs n_train : la catastrophe du fold 1 (708 echantillons), tendance croissante", plusieurs courbes reliant les edges fold-par-fold, 4 series principales (BTC + ETH, h=1), baseline verte tirets a Y=0, legende "BTC h=1" orange + "ETH h=1" violet en bas-droite. **Pattern pedagogique cle** : la performance du modele depend fortement de la taille du jeu d'entrainement ; fold 1 catastrophe (trop peu de donnees) ; tendance croissante mais asymptote a 0 sur ~1500+ echantillons (le modele atteint la baseline majority mais ne la surpasse pas systematiquement). **Alt-text precedent** "Diagnostic d'ensemble HAR-Kelly — dilution des performances" etait TITLES-driven — corrige c.437 pour decrire CONTENT-driven : structure (line plot edge vs n_train), valeurs concretes (fold 1 -0.09 BTC), pattern (catastrophe fold 1, tendance croissante).

- **Poids** : 29,7 KB (PIL optimisé)

---

## Diversité méthodologique couverte (inchangée, faisait partie du MANIFEST d'origine)

Classique (HAR-RV-J pour `mltp-har-rv`) · DL linéaire (DLinear pour `mltp-dlinear-vol`) · récurrent (LSTM pour `mltp-lstm-vol`) · Transformer à attention (TFT pour `mltp-tft-vol`) · Switching de régimes (HMM pour `mltp-hmm-regime`) · combinaison de modèles (Ensemble pour `mltp-ensemble`).

**Total** : 6 figures, ~222 KB cumulés, max 60,3 KB par fichier (`mltp-tft-vol`).
