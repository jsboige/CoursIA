# MANIFEST des figures README — IIT/ICT-Series

Provenance des images de `assets/readme/` (EPIC #5654, source 1 = extraction d'outputs de notebooks Python, série `ict/`). Les index de cellule sont absolus (toutes cellules : markdown + code), conformément à la convention `extract_readme_figures.py`. Les figures couvrent les strates 1-5 de la série (les strates 1-4 sont stables ; la strate 5 a ICT-16 livré, ICT-15..25 gated — Epic #4588).

**Audit visuel juillet 2026** : chaque PNG a été rouvert via l'outil `Read` (Claude vision) et son **contenu réel** documenté ci-dessous. Les figures ont été **ré-intégrées dans le flux narratif** du `README.md` (au niveau du notebook discuté, pas dans une section Galerie isolée), avec une légende qui décrit exactement ce qui est visible et signale honnêtement ce qui ne l'est pas (« limitation illustrative assumée »). Plusieurs noms de fichiers s'écartent du contenu rendu — c'est une dette de nommage connue, discloseée dans la légende de chaque figure concernée.

## ict1-phitrajectories.png

- **Source** : notebook `ICT-1-PhiTrajectories.ipynb` (cellule 12, output 0)
- **Strate** : 1 (Phi-trajectories)
- **Contenu réel vérifié** : 4 courbes superposées, axe X = `pas de temps` (0 à 6), axe Y = `Φ de l'état courant` (0 à ~2.3), légende interne en haut-droite (4 départs : `depart 000` bleu, `depart 100` orange, `depart 010` vert, `depart 111` rouge). Les 4 trajectoires oscillent entre 0 et ~2.3, marquant des **pulsations** (alternance haut/bas) plutôt qu'une convergence asymptotique unique. La Φ est ici calculée par **PyPhi** sur un réseau AND/OR (jouet).
- **Alt-text (FR)** : Trajectoires de Φ sur réseau AND/OR — quatre départs (000, 100, 010, 111), Φ varie entre 0 et ~2.3 sur 6 pas de temps.
- **Poids** : 52.2 KB (natif)
- **Ce qui n'est PAS dans la figure** : un paysage de Φ en 2D/3D (Φ est tracée en 1D au cours du temps) ; la robustesse aux perturbations (c'est une mesure distincte dans une autre cellule du notebook).

## ict2-selfsorting.png

- **Source** : notebook `ICT-2-SelfSortingMorphogenesis.ipynb` (cellule 7, output 0)
- **Strate** : 1 (tri auto-organisé)
- **Contenu réel vérifié** : 2 panneaux côte-à-côte mesurant le **tri auto-organisé** d'une séquence par un automate minimal. **Panneau gauche** : `Inversions (désordre global)`, axe X `pas` (0 à ~220), axe Y `inversions` (0 à 60), courbe rouge décroissante monotone de 60 à 0 (signature d'un tri efficace : le nombre de paires désordonnées chute vers 0). **Panneau droite** : `Sortedness vs erreur de monotonie`, axe X `pas` (0 à ~210), axe Y (0 à 1.0) ; courbe verte = `sortedness` (0.5→1.0 croissante, monotonie globale), courbe orange = `erreur de monotonie (locale)` (~0.5→0 décroissante avec fluctuations, monotonie locale). Les deux panneaux convergent : la séquence devient globalement ET localement monotone.
- **Alt-text (FR)** : Métriques de tri auto-organisé : gauche « Inversions (désordre global) » 60→0 en ~220 pas, droite « Sortedness vs erreur de monotonie » (sortedness 0.5→1.0 croissante verte, erreur locale orange qui décroît).
- **Poids** : 40.2 KB (natif)
- **Ce qui n'est PAS dans la figure** : (a) la **dynamique Gray-Scott** sous-jacente (la morphogenèse Gray-Scott elle-même est rendue dans `ict9-gray-scott.png`) ; (b) la **robustesse aux cellules défectueuses** et l'**auto-réparation après ablation**, traitées dans ICT-3 et ICT-4 (figures distinctes).

## ict8-attractor.png

- **Source** : notebook `ICT-8-AttractorLandscapesEWS.ipynb` (cellule 3, output 0)
- **Strate** : 2 (paysages d'attracteurs)
- **Contenu réel vérifié** : 4 courbes, axe X = `x (biomasse de végétation)` (0 à 10), axe Y = `dx/dt` (-3.0 à +1.0), légende interne avec 4 valeurs du paramètre de pâturage `c ∈ {1.60, 2.20, 2.60, 2.90}`. À `c=1.60` (bleu), 3 zéros (bistabilité : 2 équilibres stables + 1 instable) ; à `c=2.90` (rouge), 1 seul zéro (régime mono-stable). La bifurcation pli est lisible par la **disparition** des zéros entre `c=2.20` et `c=2.60`.
- **Alt-text (FR)** : Champ de vitesse dx/dt pour 4 valeurs du paramètre c (1.60, 2.20, 2.60, 2.90) — les zéros de la courbe sont les équilibres, leur nombre passe de 3 (bistable) à 1 au-delà du pli.
- **Poids** : 55.1 KB (natif)
- **Ce qui n'est PAS dans la figure** : les signaux précurseurs (variance ↑, autocorrélation ↑, τ de Kendall) — tracés dans des cellules séparées du notebook.

## ict9-gray-scott.png

- **Source** : notebook `ICT-9-AgencyRegeneration.ipynb` (cellule 3, output 0)
- **Strate** : 2 (agence et régénération)
- **Contenu réel vérifié** : 2 panneaux côte-à-côte illustrant la **morphogenèse générative** par réaction-diffusion (Gray-Scott, Pearson 1993). Le titre interne est « Morphogenèse générative : la réaction-diffusion engendre un attracteur de forme ». **Panneau gauche** : `t=0 : germe localisé` (carré rouge centré sur fond bleu sombre uniforme). **Panneau droit** : `t=6000 : motif auto-entretenu` (structure=0.0095, ~25 taches rougeâtres disposées en grille décalée, sur fond noir). C'est la **dynamique de référence** qu'ICT-9 soumet ensuite à l'ablation `do(·)` pour mesurer le gain de réparation (`repair_gain`).
- **Alt-text (FR)** : Morphogenèse générative (Gray-Scott) : t=0 (germe localisé en rouge sur fond bleu sombre) à gauche, t=6000 (motif auto-entretenu de ~25 taches rougeâtres, structure=0.0095) à droite.
- **Poids** : 51.8 KB (natif)
- **Ce qui n'est PAS dans la figure** : (a) les **métriques de tri auto-organisé** (inversions / sortedness), qui sont rendues dans `ict2-selfsorting.png` ; (b) le `repair_gain` formel (RD vs diffusion, mesure contrefactuelle) et l'ablation `do(·)`, qui sont calculés dans des cellules séparées du notebook avec leur propre figure dédiée.

## ict13-axelrod.png

- **Source** : notebook `ICT-13-AxelrodStrategicMorphodynamics.ipynb` (cellule 13, output 0)
- **Strate** : 3 (morphodynamique stratégique)
- **Contenu réel vérifié** : 6 courbes, axe X = `bruit d'implémentation ε` (0.00 à 0.40), axe Y = `score de tournoi` (~1.7 à 2.6), légende interne en bas-gauche avec les 6 stratégies (`allc`/`alld`/`tft`/`grim`/`pavlov`/`tft-generous`). Le titre annonce « Gate 3 : effondrement sous bruit (TFT chute, Pavlov résiste) ». **Lecture critique** : `TFT` (rouge) chute de ~2.6 à ~2.1 entre ε=0 et ε=0.05, puis remonte progressivement vers ~2.4 à ε=0.40 ; `Pavlov` (vert) reste ~2.5 (quasi-stable) ; `allc` (bleu) plonge à 1.7 vers ε=0.10 puis remonte à ~2.1 ; `allD` (orange) reste leader ~2.4-2.5.
- **Alt-text (FR)** : Gate 3 — effondrement sous bruit (TFT chute, Pavlov résiste) : 6 stratégies (allc/alld/tft/grim/pavlov) tracées par leur score de tournoi en fonction du bruit d'implémentation ε ∈ [0, 0.40].
- **Poids** : 46.7 KB (natif)
- **Ce qui n'est PAS dans la figure** : les Gates 1 (score pur sans bruit), 2 (seuil δ* du Folk theorem) et 4 (bassins d'invasion) — discutés dans le texte du notebook, tracés dans des cellules séparées.

## ict14-freeenergy.png

- **Source** : notebook `ICT-14-FreeEnergySurprise.ipynb` (cellule 4, output 0)
- **Strate** : 4 (énergie libre et représentationnel)
- **Contenu réel vérifié** : 2 panneaux. **Haut** : `Lacet de prédation (sinus bruité)`, axe X `temps` (0 à 300), axe Y `position` (-1 à 1) ; 3 courbes (`proie o_t` bleue, `p̂_t (anticipateur)` orange, `persistance` verte) suivant un signal sinusoidal bruité. **Bas** : `surprise S_t` (~0.9 à 1.1), 2 courbes (`S_t - p̂` bleue, `S_t - persistance` orange) — la surprise de l'anticipateur est **plus basse** (signal plus prévisible pour `p̂`).
- **Alt-text (FR)** : Lacet de prédation (sinus bruité) : panneau haut = position proie/anticipateur/persistance, panneau bas = surprise S_t - p̂ (bleu) vs S_t - persistance (orange).
- **Poids** : 132.0 KB (natif)
- **Ce qui n'est PAS dans la figure** : (a) la **free energy** formelle $F = E_q[\ln q(\theta) - \ln p(\theta, x)]$ et l'**expected free energy** $G$ (interviennent dans le texte mais ne sont pas tracées) ; (b) une généralisation à un signal non sinusoidal.
- **Dette de nommage (disclose)** : le nom de fichier `ict14-freeenergy.png` est **trompeur** — la figure illustre en réalité le **lacet de prédation** (batterie anticipation/persistance développée dans ICT-10 sur la catastrophe fronce) appliquée à un signal sinusoidal bruité. Le lien avec la free energy est dans le texte du notebook, mais la figure rendue ici est un cas d'application du **représentant interne `p̂`**. Le nom de fichier est conservé par compatibilité avec la table d'extraction.

## ict16-mdl-bosse.png

- **Source** : notebook `ICT-16-MDLTwoPartCode.ipynb` (cellule 11, output 0)
- **Strate** : 5 (MDL et bosse complexité-entropie)
- **Contenu réel vérifié** : 1 panneau, axe X `Taux d'entropie H (bits/symbole)` (~0.4 à 3.0), axe Y `Longueur de code du modèle (bits)` (-50 à +40). Points gris = `trajectoires échantillonnées` (n=20), courbe rouge avec marqueurs = `mediane par bucket (bosse)`, étoile dorée = `pic C*≈38.3 bits à H*≈1.99`. La médiane montre un **creux** vers H≈1.0 (C≈-50) puis un **pic** marqué à H*≈2.0 (C*≈38). C'est la **bosse complexité-entropie** canonique de Crutchfield-Feldman 1998 : la complexité statistique du modèle est maximale à entropie intermédiaire.
- **Alt-text (FR)** : Bosse complexité-entropie (Crutchfield-Feldman 1998) — axe X = taux d'entropie H (bits/symbole, 0.5-3.0), axe Y = longueur de code du modèle C (bits, -40 à +40) ; points gris = trajectoires échantillonnées, courbe rouge = médiane par bucket, étoile = pic C*≈38.3 bits à H*≈1.99.
- **Poids** : 57.0 KB (PIL optimisé)
- **Ce qui n'est PAS dans la figure** : la généralisation cross-substrat (gate Φ/F/K d'ICT-15, qui prend la bosse comme observable d'un des substrats du banc). La bosse est ici calculée pour un seul couple (modèle, famille de sources).

---

**Total** : 7 figures, ~440 KB. **Politique** (#5654) : ≤200 KB/fichier, downscale ≤1200 px max. PNG lossless natif pour les courbes matplotlib (netteté du texte privilégiée). Arc pédagogique : Strate 1 (Φ-trajectories + tri Gray-Scott) → Strate 2 (bifurcation pli May + métriques réparation) → Strate 3 (Axelrod régime-dépendance) → Strate 4 (lacet anticipation/persistance) → Strate 5 (bosse Crutchfield-Feldman MDL). Chaque figure est placée **dans la section du README où le notebook correspondant est discuté** (et non dans une section Galerie isolée), conformément à la doctrine figures amendée 2026-07-09.
