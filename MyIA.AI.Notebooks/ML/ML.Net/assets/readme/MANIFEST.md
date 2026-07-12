# Manifeste des figures — ML / ML.Net

Provenance des images de `assets/readme/` (EPIC #5654, source 1 = extraction d'outputs de notebooks **Python** de la parité marathon #4956 — les mêmes concepts ML sont illustrés côté C# ML.NET et côté Python scikit-learn/statsmodels).

**Audit visuel juillet 2026** : chaque PNG a été rouvert via l'outil `Read` et son **contenu réel** documenté ci-dessous. Les figures ont été ré-intégrées dans le flux narratif du `README.md` (section Parcours / Phase N — pas dans une section Galerie isolée), avec une légende qui décrit exactement ce qui est visible et signale honnêtement ce qui ne l'est pas (« limitation illustrative assumée »).

## ml-regression.png

- **Source** : notebook `ML-1-Introduction-Python.ipynb` (cellule 17, output 0)
- **Contenu réel vérifié** : scatter plot unique, titre « Régression linéaire : prix d'une maison selon sa taille ». Axes : X = Size (milliers de pieds carrés, 0 à 8), Y = Price (centaines de milliers de $, 0 à 10). Trois éléments superposés : points bleus cercles « Entraînement » (8 points), carrés orange « Test » (8 points), droite verte « Droite de régression » (passant par l'origine), étoile rouge « Prédiction (2.5 → 2.76) ». La légende interne est dans le coin haut-gauche.
- **Alt-text (FR)** : Droite de régression linéaire apprise sur split entraînement/test (8 + 8 points), avec une prédiction unique matérialisée par une étoile rouge.
- **Poids** : 36 Ko (PNG lossless)
- **Ce qui n'est PAS dans la figure** : la sortie ML.NET `IDataView → EstimatorChain` correspondante (le code C# est dans `ML-1-Introduction.ipynb` cellules 9-22 ; voir limitation illustrative assumée dans la légende).

## ml-ts-series.png

- **Source** : notebook `ML-5-TimeSeries-Python.ipynb` (cellule 7, output 0)
- **Contenu réel vérifié** : courbe unique 2D, titre « Ventes quotidiennes (2023-2024) ». Axe X temporel 2023-01 → 2025-01 (deux ans journaliers), axe Y 50 à 250 ventes/jour. Une seule série bleue tracée (Train | Test confondus visuellement). Une ligne rouge pointillée verticale marque le split au 2024-01-01.
- **Alt-text (FR)** : Série temporelle brute de ventes quotidiennes sur 2023-2024, avec un split Train|Test explicite (ligne pointillée rouge).
- **Poids** : 116 Ko
- **Ce qui n'est PAS dans la figure** : la décomposition de la série, la prévision, l'intervalle de confiance — ces dimensions sont portées par les figures `ml-ts-stl.png` et `ml-ts-forecast.png`.

## ml-ts-stl.png

- **Source** : notebook `ML-5-TimeSeries-Python.ipynb` (cellule 11, output 0)
- **Contenu réel vérifié** : 4 panneaux verticaux empilés, titre global « Décomposition STL (période = 7 jours) ». De haut en bas : (1) Observé (bleu, 60-180), (2) Tendance (orange, 105-155, croissant sur 2023), (3) Saisonnalité (vert, ±35 cycles courts réguliers, période 7 jours), (4) Bruit/Résidu (rouge, ±20 stationnaire). Axe X partagé 2023-01 → 2024-01 (1 an, subset d'entraînement).
- **Alt-text (FR)** : Décomposition STL d'une série temporelle de ventes — 4 panneaux (Observé, Tendance, Saisonnalité, Résidu) avec période saisonnière 7 jours explicite.
- **Poids** : 179 Ko
- **Ce qui n'est PAS dans la figure** : la sortie `ForecastBySsa` côté ML.NET (le code est dans `ML-5-TimeSeries.ipynb` cellules 9-18 ; les deux méthodes traitent la saisonnalité 7 jours mais l'API diffère).

## ml-ts-forecast.png

- **Source** : notebook `ML-5-TimeSeries-Python.ipynb` (cellule 20, output 0)
- **Contenu réel vérifié** : courbe 2D, titre « Prévision SARIMA vs réel (90 premiers jours de 2024) ». Axe X 2024-01-01 → 2024-04-01 (90 jours), axe Y 100 à 210 ventes. Trois éléments : ligne bleue « Ventes réelles 2024 », ligne orange « Prévision SARIMA », zone orange clair « Intervalle de confiance 95% ». La prévision suit la saisonnalité 7 jours et reste dans la bande de confiance aux extrema.
- **Alt-text (FR)** : Prévision SARIMA sur 90 jours (Q1 2024) comparée à la réalité, avec intervalle de confiance 95%.
- **Poids** : 126 Ko
- **Ce qui n'est PAS dans la figure** : la robustesse multi-seed / walk-forward (limitée à un seul fit SARIMA) et la comparaison côte-à-côte avec `ForecastBySsa` ML.NET — voir cellules 22-28 du notebook.

## ml-clustering.png

- **Source** : notebook `ML-8-Clustering-Python.ipynb` (cellule 12, output 0)
- **Contenu réel vérifié** : 2 panneaux côte-à-côte. Gauche : « Vérité terrain (cachée à K-Means) » — 3 classes Dormants (rouge), Réguliers (vert), VIP (bleu), axes X = Frequency (achats/mois, 0-30), Y = Monetary (EUR, 0-700). Les trois nuages sont bien séparés : Dormants en bas-gauche, Réguliers au centre, VIP en haut-droite. Droite : « Clusters retrouvés par K-Means » — 3 clusters Cluster 0/1/2 (rouge/vert/bleu) reproduisant fidèlement les trois populations. Le K-Means retrouve correctement la vérité terrain.
- **Alt-text (FR)** : Clustering K-Means (K=3) sur données RFM — vérité terrain à gauche, partition retrouvée à droite.
- **Poids** : 55 Ko
- **Ce qui n'est PAS dans la figure** : les cas réels où les segments se chevauchent ou ne suivent pas une mixture gaussienne (voir limitation illustrative assumée dans la légende README).

## ml-coude.png

- **Source** : notebook `ML-8-Clustering-Python.ipynb` (cellule 16, output 1)
- **Contenu réel vérifié** : courbe 2D à double axe Y, titre « Méthode du coude : K=3 minimise Davies-Bouldin ». Axe X = K (nombre de clusters, 2 à 6). Axe Y gauche (bleu, 0.10-0.26) = AverageDistance (inertie intra-cluster), courbe bleue avec marqueurs ronds. Axe Y droit (rouge pointillé, 0.45-0.80) = Davies-Bouldin (séparation), courbe rouge avec marqueurs carrés. Une ligne pointillée verticale marque K=3 = minimum de l'inertie ET du Davies-Bouldin (coude net).
- **Alt-text (FR)** : Méthode du coude combinée Davies-Bouldin pour K=3 sur données RFM, double axe Y.
- **Poids** : 55 Ko
- **Ce qui n'est PAS dans la figure** : le coude sur des données réelles où les clusters ne sont pas des mixtures gaussiennes bien séparées (le coude peut alors devenir diffus) — voir cellules 14-16 du notebook.

---

**Total** : 6 figures, ~566 Ko. **Politique** (#5654) : ≤200 Ko/fichier, downscale ≤1200 px max. PNG lossless natif pour les courbes matplotlib (netteté du texte privilégiée). Arc pédagogique dans le README : régression (ML-1) → séries temporelles + décomposition STL + prévision (ML-5) → clustering K-means + méthode du coude (ML-8). Chaque figure est placée **dans la section du README où le notebook correspondant est discuté** (et non dans une section Galerie isolée), conformément à la doctrine figures amendée 2026-07-09.