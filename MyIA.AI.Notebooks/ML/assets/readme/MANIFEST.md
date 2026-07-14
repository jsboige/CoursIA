# MANIFEST des figures README

Provenance des images de `assets/readme/` (EPIC #5654, source 1 = extraction d'outputs de notebooks).

> **Audit vision po-2026 c.435 (2026-07-14, doctrine #5780)** : les 6 PNG ci-dessous ont été ouverts un par un via l'outil `Read` et comparés à leur alt-text. Verdict par figure dans le champ *Contenu réel vérifié*. Cohérence caption ↔ image = **5/6 exacte, 1 correction d'alt-text appliquée** (lab1-foundations : alt-text generique «fondations Python» omettait la structure dual-panel pédagogique cruciale — reformulé pour mentionner explicitement les deux sous-graphiques).

## ml1-intro.png

- **Source** : notebook `ML.Net/ML-1-Introduction-Python.ipynb` (cellule 17, output 0)
- **Alt-text (FR)** : Régression linéaire : droite apprise par scikit-learn superposée aux données d'entraînement et de test (prix immobiliers).
- **Contenu réel vérifié** (audit visuel MiniMax M3, c.435) : figure titrée « Régression linéaire : prix d'une maison selon sa taille », scatter bleu (Entraînement, ~12 points alignés) + orange (Test, ~8 points) + droite verte + étoile rouge « Prédiction (2.5 → 2.76) ». Axes X = Size (milliers de pieds carrés, 0-9), Y = Price (centaines de milliers de $, 0-10). **Alt-text cohérent avec l'image**.
- **Poids** : 35.8 KB (PIL optimise)

## ml5-timeseries.png

- **Source** : notebook `ML.Net/ML-5-TimeSeries-Python.ipynb` (cellule 11, output 0)
- **Alt-text (FR)** : Décomposition STL d'une série temporelle : signal observé, tendance, composante saisonnière (période 7 hebdomadaire) et résidus.
- **Contenu réel vérifié** (audit visuel MiniMax M3, c.435) : figure titrée « Décomposition STL (période = 7 jours) », 4 sous-graphiques empilés — Observé (série oscillante bleue, ~365 jours sur 2023), Tendance (orange, croissance régulière ~107 → ~160), Saisonnalité (verte, sinusoïde stable amplitude ±40), Bruit (rouge, résidus ±20). **Alt-text cohérent avec l'image** — les 4 composantes STL sont effectivement présentes.
- **Poids** : 187.6 KB (PIL optimise)

## ml8-clustering.png

- **Source** : notebook `ML.Net/ML-8-Clustering-Python.ipynb` (cellule 12, output 0)
- **Alt-text (FR)** : Clustering K-Means : restitution des 3 segments cachés (Dormants, Réguliers, VIP) sans supervision, projetés sur deux variables.
- **Contenu réel vérifié** (audit visuel MiniMax M3, c.435) : deux sous-graphiques côte-à-côte — gauche « Vérité terrain (cachée à K-Means) » Dormants (rouge, fréquence 0-3, €0-100) / Réguliers (vert, fréquence 5-13, €100-260) / VIP (bleu, fréquence 12-30, €350-720) ; droite « Clusters retrouvés par K-Means » Cluster 0/1/2 (mêmes zones, couleurs réassignées). **Alt-text cohérent avec l'image**.
- **Poids** : 114.7 KB (PIL optimise)

## lab1-foundations.png

- **Source** : notebook `DataScienceWithAgents/PythonAgentsForDataScience/Day1/Labs/Lab1-PythonForDataScience.ipynb` (cellule 8, output 0)
- **Alt-text (FR)** *(corrigé c.435)* : Visualisation exploratoire d'un DataFrame Pandas avec `matplotlib.pyplot.subplots` : **deux sous-graphiques côte-à-côte** produits sur un échantillon tabulaire de ventes — à gauche courbe journalière « Ventes Widget A (20 premiers jours) » (axe X = dates 2024-01-01 → 2024-01-20, axe Y = Ventes 120-190), à droite bar chart « Ventes moyennes par catégorie » (Accessoires ≈45, Electronique ≈130, Premium ≈225). Démontre `pandas.groupby` + plotting Matplotlib.
- **Contenu réel vérifié** (audit visuel MiniMax M3, c.435) : figure composite à 2 panneaux. Gauche : courbe bleu « Ventes Widget A (20 premiers jours) », dates pivotées, oscillations 123-188. Droite : bar chart 3 catégories (Accessoires bleu ≈45, Electronique orange ≈130, Premium vert ≈225). **Alt-text précédent disait «Fondations Python pour la data science : visualisation exploratoire des ventes (graphiques Matplotlib) sur un échantillon tabulaire» — corrigé : la formulation generique occultait la structure dual-panel pedagogiquement cruciale (le TP Lab1 illustre `pandas.groupby` + `subplots` ; le bar chart par catégorie est la sortie du `groupby`, pas un élément décoratif). Reformulé pour mentionner explicitement les deux sous-graphiques.**
- **Poids** : 103.1 KB (PIL optimise)

## lab5-viz.png

- **Source** : notebook `DataScienceWithAgents/PythonAgentsForDataScience/Day3/Labs/Lab5-Viz-ML/Lab5-Viz-ML.ipynb` (cellule 11, output 0)
- **Alt-text (FR)** : Visualisation de données : évolution journalière du chiffre d'affaires agrégé, tracée avec Seaborn sur un dataframe Pandas.
- **Contenu réel vérifié** (audit visuel MiniMax M3, c.435) : figure titrée « Évolution du Chiffre d'Affaires Journalier », courbe bleu simple sur 4 jours (2024-10-01 → 2024-10-04), décroissance brutale 760 → 230 puis remontée à 480. Style Seaborn (`whitegrid`). **Alt-text cohérent avec l'image** — CA agrégé visible, période courte (3-4 jours).
- **Poids** : 31.0 KB (PIL optimise)

## lab9-adk.png

- **Source** : notebook `DataScienceWithAgents/AgenticDataScience/Day4-Foundations/Lab9-First-ADK-Agent.ipynb` (cellule 17, output 0)
- **Alt-text (FR)** : Premier agent ADK : un agent du Agent Development Kit génère et exécute du code Matplotlib (revenu par produit) via sa boucle d'outils.
- **Contenu réel vérifié** (audit visuel MiniMax M3, c.435) : bar chart titré « Revenu total par produit », 4 barres verticales décroissantes (Gadget Y ≈46000, Widget B ≈44000, Gadget X ≈34000, Widget A ≈27000), axes X = Produit / Y = Revenu. Style Matplotlib par défaut (`bar` cyan bord noir). **Alt-text cohérent avec l'image** — la sortie est bien un bar chart Matplotlib généré par l'agent ADK.
- **Poids** : 18.8 KB (PIL optimise)
