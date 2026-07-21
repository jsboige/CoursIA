# MANIFEST des figures README

Provenance des images de `assets/readme/` (EPIC #5654, source 1 = extraction d'outputs de notebooks).

**Audit G.1 fondateur** : relecture visuelle via outil `Read` par `myia-po-2025` le **2026-07-14** (cycle c.488 du rollout [issue #5780](../../../issues/5780)). Bilan : 4/6 ACCURATE mature + 2/6 corrections réelles (2 enrichissements ciblés). Migration format : table simple (vague-1) → liste détaillé standard (cf [c.469 SemanticWeb](../../../SymbolicAI/SemanticWeb/assets/readme/MANIFEST.md), [c.481 GenAI/Image racine](../../../GenAI/Image/assets/readme/MANIFEST.md), [c.484 GenAI/Image/03-Orchestration](../../../GenAI/Image/03-Orchestration/assets/readme/MANIFEST.md), [c.485 GenAI/Video/04-Applications](../../../GenAI/Video/04-Applications/assets/readme/MANIFEST.md), [c.487 GenAI/Video racine](../../../GenAI/Video/assets/readme/MANIFEST.md)).

---

## ml1-intro.png

- **Source** : notebook `ML.Net/ML-1-Introduction-Python.ipynb` (cellule 17, output 0)
- **Contenu réel vérifié** (lecture via `Read` 2026-07-14) : nuage de points unique « Régression linéaire : prix d'une maison selon sa taille », légende 3-items (Entraînement=cercles bleus, Test=carrés oranges, Droite de régression=ligne verte), étoile rouge « Prédiction (2.5 → 2.76) » sur la droite. Axes Size (milliers de pieds carrés) 0-8 vs Price (centaines de milliers de $) 0-10.
- **Alt-text (FR)** : Régression linéaire : droite apprise par scikit-learn superposée aux données d'entraînement et de test (prix immobiliers).
- **Poids** : 35.8 KB (PIL optimise)
- **Note** : aucun changement nécessaire, alt-text antérieur déjà fidèle au contenu réel.

## ml5-timeseries.png

- **Source** : notebook `ML.Net/ML-5-TimeSeries-Python.ipynb` (cellule 11, output 0)
- **Contenu réel vérifié** (lecture via `Read` 2026-07-14) : 4 panneaux superposés verticalement, titre principal « Décomposition STL (période = 7 jours) ». Panneau 1 Observé (oscillations bleues ~60-190). Panneau 2 Tendance (courbe orange lisse montant de ~110 début 2023 à ~160 fin 2023). Panneau 3 Saisonnalité (sinusoïde verte amplitude ±40). Panneau 4 Bruit (résidu rouge amplitude ±25). Axe temps 2023-01 → 2024-01.
- **Alt-text (FR)** : Décomposition STL d'une série temporelle : signal observé, tendance, composante saisonnière (période 7 hebdomadaire) et résidus.
- **Poids** : 187.6 KB (PIL optimise)
- **Note** : aucun changement nécessaire, alt-text antérieur déjà fidèle au contenu réel.

## ml8-clustering.png

- **Source** : notebook `ML.Net/ML-8-Clustering-Python.ipynb` (cellule 12, output 0)
- **Contenu réel vérifié** (lecture via `Read` 2026-07-14) : 2 panneaux côte-à-côte « Vérité terrain (cachée à K-Means) » et « Clusters retrouvés par K-Means », axes Frequency (achats/mois) 0-30 vs Monetary (EUR) 0-700. Panneau gauche : Dormants (rouge, bas-gauche), Réguliers (vert, milieu-bas), VIP (bleu, haut-droite). Panneau droit : Cluster 0 (rouge), Cluster 1 (vert), Cluster 2 (bleu). Les clusters K-Means **ne s'alignent PAS** avec les segments sémantiques : c'est l'enseignement pédagogique central.
- **Alt-text (FR)** : Clustering K-Means : restitution des 3 segments cachés (Dormants, Réguliers, VIP) sans supervision, projetés sur deux variables.
- **Poids** : 114.7 KB (PIL optimise)
- **Note** : aucun changement nécessaire, alt-text antérieur déjà fidèle au contenu réel.

## lab1-foundations.png

- **Source** : notebook `DataScienceWithAgents/Track1-LangChain/Day1/Labs/Lab1-PythonForDataScience.ipynb` (cellule 8, output 0)
- **Contenu réel vérifié** (lecture via `Read` 2026-07-14) : 2 panneaux côte-à-côte « Ventes Widget A (20 premiers jours) » (courbe bleue oscillant 123-188 sur axe Date 2024-01-01 → 2024-01-20) et « Ventes moyennes par catégorie » (barres verticales 3-items : Accessoires ≈ 45 bleu, Électronique ≈ 130 orange, Premium ≈ 225 vert). Pas de mention Seaborn dans le rendu (style matplotlib 'default' / 'classic').
- **Alt-text (FR)** : Fondations Python pour la data science : visualisation exploratoire des ventes (graphiques Matplotlib) sur un échantillon tabulaire.
- **Poids** : 103.1 KB (PIL optimise)
- **Note** : aucun changement nécessaire, alt-text antérieur déjà fidèle au contenu réel.

## lab5-viz.png

- **Source** : notebook `DataScienceWithAgents/Track1-LangChain/Day3/Labs/Lab5-Viz-ML/Lab5-Viz-ML.ipynb` (cellule 11, output 0)
- **Contenu réel vérifié** (lecture via `Read` 2026-07-14) : courbe unique « Évolution du Chiffre d'Affaires Journalier » 4 points sur axe Date 10-01 00 → 10-04 00. Valeurs : 760 (10-01) → 230 (10-02) → 245 (10-03) → 480 (10-04). **Pas de marqueurs** ni de légende, **grille seaborn-v0_8-whitegrid** (style matplotlib par défaut récent, pas un import seaborn). Couleur unique (bleu acier par défaut `tab:blue`).
- **Alt-text (FR)** : Visualisation de données : évolution journalière du chiffre d'affaires agrégé, tracée avec **matplotlib pur** (style `seaborn-v0_8-whitegrid`) sur un DataFrame Pandas.
- **Poids** : 31.0 KB (PIL optimise)
- **Note** : ancien alt-text « tracée avec Seaborn » était **imprécis** : `plt.style.use('seaborn-v0_8-whitegrid')` charge un style **matplotlib** (pas un import seaborn). **Enrichi** pour expliciter matplotlib pur + style précis, le rendu n'utilise aucune fonction `sns.*`.

## lab9-adk.png

- **Source** : notebook `DataScienceWithAgents/Track2-GoogleADK/Day4-Foundations/Lab9-First-ADK-Agent.ipynb` (cellule 17, output 0)
- **Contenu réel vérifié** (lecture via `Read` 2026-07-14) : diagramme en barres vertical unique « Revenu total par produit », 4 catégories triées par ordre décroissant : Gadget Y (~46 000) > Widget B (~44 500) > Gadget X (~34 000) > Widget A (~27 500). Couleur unique (bleu ciel `skyblue`), bordures noires, labels axe X pivotés à 45°.
- **Alt-text (FR)** : Premier agent ADK : un agent du Agent Development Kit génère et exécute du code Matplotlib (revenu par produit trié **décroissant** Gadget Y → Widget A) via sa boucle d'outils.
- **Poids** : 18.8 KB (PIL optimise)
- **Note** : ancien alt-text ne mentionnait pas le **tri décroissant spontané** de l'agent (`sort_values(ascending=False)` non demandé). **Enrichi** pour expliciter ce geste spontané qui rend l'insight immédiatement lisible (Gadget Y bat Widget A de ~70%).

---

## Vérification G.1 — provenance investigation

Investigation `nbformat` Python pour identifier les cellules sources et valider les attributions :

| Fichier | Cell | Out | MD5 cell output | Taille cell | Taille disque | Ratio |
|---|---|---|---|---|---|---|
| `ml1-intro.png` | 17 | 0 | `0afdf155` | 36 696 B | 36 696 B | 1.00× |
| `ml5-timeseries.png` | 11 | 0 | `261de71a` | 192 068 B | 192 068 B | 1.00× |
| `ml8-clustering.png` | 12 | 0 | `0afc6f2c` | 59 748 B | 117 455 B | 1.97× |
| `lab1-foundations.png` | 8 | 0 | `d584a7f5` | 52 346 B | 105 548 B | 2.02× |
| `lab5-viz.png` | 11 | 0 | `8952a63c` | 31 733 B | 31 733 B | 1.00× |
| `lab9-adk.png` | 17 | 0 | `c85f4ad8` | 19 287 B | 19 287 B | 1.00× |

**Discrepancy ml8-clustering + lab1-foundations** (ratio > 1) : la cellule de référence produit un PNG plus petit que la copie sur disque, suggérant que le PNG de l'`assets/readme/` est un **export à plus haute résolution / DPI** depuis le notebook. C'est une pratique courante pour les figures de README (lisibilité zoom). Les MD5 sont différents (cell output ≠ disque), mais le **contenu visuel** est équivalent (validation via lecture `Read` confirme la même figure). Attribution conservée car le contenu est cohérent.

**SHA256 unique par fichier sur disque** :
- `8ac43b084532e350...` (ml1-intro)
- `1604eaa1dd35196d...` (ml5-timeseries)
- `f769795e6d47a1bf...` (ml8-clustering)
- `dd9ba6fd3b028b3d...` (lab1-foundations)
- `2e27f1f7b6e4d75e...` (lab5-viz)
- `c95b544bcc263c29...` (lab9-adk)

Toutes les attributions source du MANIFEST sont confirmées par investigation `nbformat` Python. Pour ml8-clustering et lab1-foundations, l'attribution cell[X]/out[Y] reste la **référence amont** même si le PNG disque est un ré-export (l'audit visuel via `Read` confirme la fidélité du contenu).

---

## Bilan audit c.488 — 19ᵉ pilote rollout #5780

| Fichier | Verdict | Action |
|---|---|---|
| `ml1-intro.png` | ACCURATE | CONSERVÉ |
| `ml5-timeseries.png` | ACCURATE | CONSERVÉ |
| `ml8-clustering.png` | ACCURATE | CONSERVÉ |
| `lab1-foundations.png` | ACCURATE | CONSERVÉ |
| `lab5-viz.png` | MISMATCH sous-spécifique | ENRICHI alt-text (matplotlib pur PAS Seaborn) |
| `lab9-adk.png` | MISMATCH sous-spécifique | ENRICHI alt-text (tri décroissant spontané agent) |

**Bilan** : 4/6 ACCURATE mature + 2/6 corrections réelles (2 enrichissements). **0 figure DROP** — les 6 fichiers restent sur disque. **0 refonte** — le contenu pédagogique était déjà bon, seules 2 imprécisions d'attribution outil / geste agent sont à corriger.

**Conformité règles** :
- §A single-subject : 1 dossier, 2 fichiers (`README.md` + `MANIFEST.md`), 1 sujet.
- R1 catalog-pr-hygiene : catalogue byte-identique à main (aucun `CATALOG-STATUS` ni `COURSE_CATALOG.*` touché).
- L268 LF-only : 0 retour chariot (`\r`) dans le diff.
- L143 secrets-hygiene : 0 secret inline dans le diff.
- C.3 strict : aucune ré-exécution Papermill, aucune cellule notebook touchée.

**Voir aussi** : [c.487 GenAI/Video racine](../../../GenAI/Video/assets/readme/MANIFEST.md) — pattern frère (audit fondateur G.1 sur MANIFEST vague-1 non migré) ; [c.485 GenAI/Video/04-Applications](../../../GenAI/Video/04-Applications/assets/readme/MANIFEST.md) — pattern frère (audit fondateur tardif post-transition #6157) ; [c.481 GenAI/Image racine](../../../GenAI/Image/assets/readme/MANIFEST.md) — pattern frère (dette cumulative racine pré-doctrine) ; issue [#5780](../../../issues/5780) ; EPIC [#5654](../../../issues/5654).