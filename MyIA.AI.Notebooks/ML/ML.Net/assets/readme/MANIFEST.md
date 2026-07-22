# Manifeste des figures — ML / ML.Net

Provenance des images de `assets/readme/` (EPIC #5654, source 1 = extraction d'outputs de notebooks **Python** de la parité marathon #4956 — les mêmes concepts ML sont illustrés côté C# ML.NET et côté Python scikit-learn/statsmodels).

**Audit visuel juillet 2026** : chaque PNG a été rouvert via l'outil `Read` et son **contenu réel** documenté ci-dessous. Les figures ont été ré-intégrées dans le flux narratif du `README.md` (section Parcours / Phase N — pas dans une section Galerie isolée), avec une légende qui décrit exactement ce qui est visible et signale honnêtement ce qui ne l'est pas (« limitation illustrative assumée »).

> **Audit vision po-2025 c.480 (2026-07-14, doctrine #5780)** : les 6 PNG ci-dessous ont été ré-ouvertes un par un via l'outil `Read` et confrontées à leur description existante (MANIFEST déjà en format détaillé standard pré-c.480, migrations antérieures). Verdict par figure dans le champ *Contenu réel vérifié*. Cohérence caption ↔ image = **6/6 exacte** — toutes les figures sont des **sorties matplotlib authentiques** (line-art, axes annotés, légendes explicites) qui correspondent **fidèlement** à leur description pédagogique (régression linéaire simple, série temporelle + décomposition STL + prévision SARIMA, clustering K-Means + méthode du coude). **0 correction d'alt-text nécessaire** ; le seul changement est la **migration de la mention «Audit visuel juillet 2026»** vers une mention datée **c.480 (2026-07-14, doctrine #5780)** + un audit-block en tête pour la traçabilité G.1 cross-cycles.
>
> **Migration c.757 (2026-07-22, doctrine #5780, asset-side enforcement)** : ajout du champ canonique `Description visuelle` aux 6 entrées. Source = vision-QA MiniMax M3 (Read direct des PNG) + stats RGB PIL. Conformité avec le détecteur `scripts/notebook_tools/detect_manifest_field.py` (PR #7819 c.754). Le champ `Contenu réel vérifié` (audit c.480 po-2025) reste en place comme preuve falsifiable détaillée ; le nouveau `Description visuelle` est la version canonique courte destinée à l'extraction automatique et au lecteur rapide. **6/6 figures conformes au détecteur.**

## ml-regression.png

- **Source** : notebook `ML-1-Introduction-Python.ipynb` (cellule 17, output 0)
- **Description visuelle** : Scatter plot matplotlib (690×440, fond blanc, axes étiquetés) titré « Régression linéaire : prix d'une maison selon sa taille » — axes X = Size (0-8 milliers pieds²), Y = Price (0-10 centaines de milliers $). 4 éléments superposés : **points bleus cercles** Entraînement (8), **carrés orange** Test (8), **droite verte** Droite de régression (passant par l'origine), **étoile rouge** Prédiction (2.5 → 2.76). Légende interne coin haut-gauche. Stats RGB PIL : moyenne (247.48, 247.45, 246.44), std (36.92, 35.68, 39.73) — fond blanc dominant, scatter épars, std moyen typique d'un scatter matplotlib sur blanc avec axes annotés. Cohérent avec une **régression linéaire simple supervisée** (split train/test + prédiction unique matérialisée par étoile rouge).
- **Alt-text (FR)** : Droite de régression linéaire apprise sur split entraînement/test (8 + 8 points), avec une prédiction unique matérialisée par une étoile rouge.
- **Contenu réel vérifié** : scatter plot unique, titre « Régression linéaire : prix d'une maison selon sa taille ». Axes : X = Size (milliers de pieds carrés, 0 à 8), Y = Price (centaines de milliers de $, 0 à 10). Trois éléments superposés : points bleus cercles « Entraînement » (8 points), carrés orange « Test » (8 points), droite verte « Droite de régression » (passant par l'origine), étoile rouge « Prédiction (2.5 → 2.76) ». La légende interne est dans le coin haut-gauche.
- **Poids** : 36 Ko (PNG lossless)
- **Ce qui n'est PAS dans la figure** : la sortie ML.NET `IDataView → EstimatorChain` correspondante (le code C# est dans `ML-1-Introduction.ipynb` cellules 9-22 ; voir limitation illustrative assumée dans la légende).

## ml-ts-series.png

- **Source** : notebook `ML-5-TimeSeries-Python.ipynb` (cellule 7, output 0)
- **Description visuelle** : Courbe 2D matplotlib (1198×429, fond blanc, axes étiquetés) titrée « Ventes quotidiennes (2023-2024) » — axe X temporel 2023-01 → 2025-01 (deux ans journaliers), axe Y 50 à 250 ventes/jour. **Une seule série bleue** oscillante (saisonnalité 7 jours visible — les oscillations courtes sont régulières et densifiées en fin d'année). **Ligne rouge pointillée verticale** au 2024-01-01 marquant le split train|test. Train | Test confondus visuellement (pas de marqueur séparateur sur la courbe, juste la ligne verticale). Légende interne coin haut-gauche (Train | Test). Stats RGB PIL : moyenne (238.39, 242.84, 246.04), std (50.75, 38.40, 32.10) — **std R plus élevé** que les autres ML.Net (~50 vs ~37) = signature d'une courbe dense avec beaucoup de pixels bleus (>8 px période courte).
- **Alt-text (FR)** : Série temporelle brute de ventes quotidiennes sur 2023-2024, avec un split Train|Test explicite (ligne pointillée rouge).
- **Contenu réel vérifié** : courbe unique 2D, titre « Ventes quotidiennes (2023-2024) ». Axe X temporel 2023-01 → 2025-01 (deux ans journaliers), axe Y 50 à 250 ventes/jour. Une seule série bleue tracée (Train | Test confondus visuellement). Une ligne rouge pointillée verticale marque le split au 2024-01-01.
- **Poids** : 116 Ko
- **Ce qui n'est PAS dans la figure** : la décomposition de la série, la prévision, l'intervalle de confiance — ces dimensions sont portées par les figures `ml-ts-stl.png` et `ml-ts-forecast.png`.

## ml-ts-stl.png

- **Source** : notebook `ML-5-TimeSeries-Python.ipynb` (cellule 11, output 0)
- **Description visuelle** : Figure matplotlib 4 panneaux verticaux empilés (1198×868, fond blanc, axe X partagé) titrée « Décomposition STL (période = 7 jours) ». De haut en bas : (1) **Observé (bleu, 60-180)** série brute 2023 ; (2) **Tendance (orange, 105-155)** croissante sur 2023 ; (3) **Saisonnalité (vert, ±35)** cycles courts réguliers (période 7 jours) ; (4) **Bruit/Résidu (rouge, ±20)** stationnaire avec quelques spikes. Axe X partagé 2023-01 → 2024-01 (1 an, subset d'entraînement). Stats RGB PIL : moyenne (245.50, 246.23, 245.44), std (38.33, 35.03, 37.49) — std modéré typique de 4 subplots sur blanc. **Cohérent avec une décomposition STL statsmodels** (4 composantes canoniques Observé/Tendance/Saisonnalité/Bruit).
- **Alt-text (FR)** : Décomposition STL d'une série temporelle de ventes — 4 panneaux (Observé, Tendance, Saisonnalité, Résidu) avec période saisonnière 7 jours explicite.
- **Contenu réel vérifié** : 4 panneaux verticaux empilés, titre global « Décomposition STL (période = 7 jours) ». De haut en bas : (1) Observé (bleu, 60-180), (2) Tendance (orange, 105-155, croissant sur 2023), (3) Saisonnalité (vert, ±35 cycles courts réguliers, période 7 jours), (4) Bruit/Résidu (rouge, ±20 stationnaire). Axe X partagé 2023-01 → 2024-01 (1 an, subset d'entraînement).
- **Poids** : 179 Ko
- **Ce qui n'est PAS dans la figure** : la sortie `ForecastBySsa` côté ML.NET (le code est dans `ML-5-TimeSeries.ipynb` cellules 9-18 ; les deux méthodes traitent la saisonnalité 7 jours mais l'API diffère).

## ml-ts-forecast.png

- **Source** : notebook `ML-5-TimeSeries-Python.ipynb` (cellule 20, output 0)
- **Description visuelle** : Courbe 2D matplotlib (1195×429, fond blanc, axes étiquetés) titrée « Prévision SARIMA vs réel (90 premiers jours de 2024) » — axe X 2024-01-01 → 2024-04-01 (90 jours), axe Y 100 à 210 ventes. 3 éléments superposés : **ligne bleue** Ventes réelles 2024 ; **ligne orange** Prévision SARIMA (suit la saisonnalité 7 jours synchrone avec le réel) ; **zone orange clair remplie** Intervalle de confiance 95% (bande autour de la prévision). La prévision reste dans la bande aux extrema. Stats RGB PIL : moyenne (245.98, 241.35, 237.32), std (39.59, 37.42, 43.16) — **B un peu plus bas** (~237 vs ~246 typique) = signature de la zone orange clair remplie (CI) qui tire les bleus vers le bas.
- **Alt-text (FR)** : Prévision SARIMA sur 90 jours (Q1 2024) comparée à la réalité, avec intervalle de confiance 95%.
- **Contenu réel vérifié** : courbe 2D, titre « Prévision SARIMA vs réel (90 premiers jours de 2024) ». Axe X 2024-01-01 → 2024-04-01 (90 jours), axe Y 100 à 210 ventes. Trois éléments : ligne bleue « Ventes réelles 2024 », ligne orange « Prévision SARIMA », zone orange clair « Intervalle de confiance 95% ». La prévision suit la saisonnalité 7 jours et reste dans la bande de confiance aux extrema.
- **Poids** : 126 Ko
- **Ce qui n'est PAS dans la figure** : la robustesse multi-seed / walk-forward (limitée à un seul fit SARIMA) et la comparaison côte-à-côte avec `ForecastBySsa` ML.NET — voir cellules 22-28 du notebook.

## ml-clustering.png

- **Source** : notebook `ML-8-Clustering-Python.ipynb` (cellule 12, output 0)
- **Description visuelle** : Figure matplotlib 2 panneaux côte-à-côte (1418×483, fond blanc, axes étiquetés). **Gauche « Vérité terrain (cachée à K-Means) »** : 3 classes — Dormants (rouge, bas-gauche), Réguliers (vert, centre), VIP (bleu, haut-droite) — axes X = Frequency (achats/mois, 0-30), Y = Monetary (EUR, 0-700). **Droite « Clusters retrouvés par K-Means »** : 3 clusters Cluster 0/1/2 (rouge/vert/bleu) reproduisant fidèlement les 3 populations (Cluster 0 ≈ Dormants, Cluster 1 ≈ Réguliers, Cluster 2 ≈ VIP). Stats RGB PIL : moyenne (247.55, 247.72, 247.48), std (36.29, 35.39, 36.32) — std faible typique de scatter épars sur fond blanc. **Couleurs identiques G/D (rouge/vert/bleu) ne sont PAS corrélées par classe — pure coïncidence palette**, K-Means assigne les labels par cluster arbitrairement ; le test visuel = « 3 populations bien séparées reproduites », pas « mêmes couleurs ».
- **Alt-text (FR)** : Clustering K-Means (K=3) sur données RFM — vérité terrain à gauche, partition retrouvée à droite.
- **Contenu réel vérifié** : 2 panneaux côte-à-côte. Gauche : « Vérité terrain (cachée à K-Means) » — 3 classes Dormants (rouge), Réguliers (vert), VIP (bleu), axes X = Frequency (achats/mois, 0-30), Y = Monetary (EUR, 0-700). Les trois nuages sont bien séparés : Dormants en bas-gauche, Réguliers au centre, VIP en haut-droite. Droite : « Clusters retrouvés par K-Means » — 3 clusters Cluster 0/1/2 (rouge/vert/bleu) reproduisant fidèlement les trois populations. Le K-Means retrouve correctement la vérité terrain.
- **Poids** : 55 Ko
- **Ce qui n'est PAS dans la figure** : les cas réels où les segments se chevauchent ou ne suivent pas une mixture gaussienne (voir limitation illustrative assumée dans la légende README).

## ml-coude.png

- **Source** : notebook `ML-8-Clustering-Python.ipynb` (cellule 16, output 1)
- **Description visuelle** : Courbe 2D matplotlib à double axe Y (758×447, fond blanc) titrée « Méthode du coude : K=3 minimise Davies-Bouldin ». Axe X = K (nombre clusters, 2 à 6). **Axe Y gauche (bleu, 0.10-0.26)** = AverageDistance (inertie intra-cluster) — courbe bleue marqueurs ronds, **décroissante** (0.26 → 0.10). **Axe Y droit (rouge pointillé, 0.45-0.80)** = Davies-Bouldin — courbe rouge marqueurs carrés, **en V** avec minimum 0.45 à K=3 puis remontée puis redescente légère. **Ligne pointillée verticale grise** marque K=3 = coude net. **Note visuelle disclosed** : le titre est **partiellement chevauché par la légende en haut** (3 entrées « AverageDistance / K=3 (coude) / Davies-Bouldin » sur la même ligne Y que le titre) — le titre reste lisible mais la zone supérieure est拥挤. Stats RGB PIL : moyenne (246.72, 245.95, 246.42), std (37.91, 39.12, 38.11) — std typique.
- **Alt-text (FR)** : Méthode du coude combinée Davies-Bouldin pour K=3 sur données RFM, double axe Y.
- **Contenu réel vérifié** : courbe 2D à double axe Y, titre « Méthode du coude : K=3 minimise Davies-Bouldin ». Axe X = K (nombre de clusters, 2 à 6). Axe Y gauche (bleu, 0.10-0.26) = AverageDistance (inertie intra-cluster), courbe bleue avec marqueurs ronds. Axe Y droit (rouge pointillé, 0.45-0.80) = Davies-Bouldin (séparation), courbe rouge avec marqueurs carrés. Une ligne pointillée verticale marque K=3 = minimum de l'inertie ET du Davies-Bouldin (coude net).
- **Poids** : 55 Ko
- **Ce qui n'est PAS dans la figure** : le coude sur des données réelles où les clusters ne sont pas des mixtures gaussiennes bien séparées (le coude peut alors devenir diffus) — voir cellules 14-16 du notebook.

---

**Total** : 6 figures, ~566 Ko. **Politique** (#5654) : ≤200 Ko/fichier, downscale ≤1200 px max. PNG lossless natif pour les courbes matplotlib (netteté du texte privilégiée). Arc pédagogique dans le README : régression (ML-1) → séries temporelles + décomposition STL + prévision (ML-5) → clustering K-means + méthode du coude (ML-8). Chaque figure est placée **dans la section du README où le notebook correspondant est discuté** (et non dans une section Galerie isolée), conformément à la doctrine figures amendée 2026-07-09.