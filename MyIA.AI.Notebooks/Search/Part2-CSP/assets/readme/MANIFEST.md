# MANIFEST des figures README

Provenance des images de `assets/readme/` (EPIC #5654, source 1 = extraction d'outputs de notebooks).

## csp1-backtracking-tree.png

- **Source** : notebook `CSP-1-Fundamentals.ipynb` (cellule 9, output 0)
- **Alt-text (FR)** : Graphe de contraintes de la coloration de l'Australie : sept variables — WA, NT, SA, Q, NSW, V, T (Tasmanie) — chacune avec un domaine de trois couleurs (Rouge, Vert, Bleu), reliées par des contraintes de différence sur les frontières partagées. La Tasmanie, sans voisin, flotte hors du graphe. Le titre de fichier historique `csp1-backtracking-tree` renvoie à la section du notebook qui produit ce tracé (introduction du backtracking MRV avant l'exemple de coloration).
- **Poids** : 29.0 KB (PIL optimisé)
- **Note** : nom de fichier `csp1-backtracking-tree` conservé par compatibilité EPIC #5654 ; le PNG illustre le graphe de contraintes (coloration), pas un arbre de backtracking — dette de nommage disclosed (EPIC #5780).

## csp2-ac3-propagation.png

- **Source** : notebook `CSP-2-Consistency.ipynb` (cellule 20, output 0)
- **Alt-text (FR)** : Propagation de contraintes AC-3 sur le graphe de la coloration de l'Australie, avant / après fixation de WA = Rouge : à gauche les domaines complets (trois couleurs par variable), à droite les domaines réduits après l'arc-cohérence (WA singleton Rouge, SA et NT ramenés à {Vert, Bleu} par déduction, les autres variables intactes).
- **Poids** : 92.0 KB (PIL optimisé)

## csp3-global-constraints.png

- **Source** : notebook `CSP-3-Advanced.ipynb` (cellule 10, output 0)
- **Alt-text (FR)** : Contrainte globale Cumulative d'OR-Tools CP-SAT : ordonnancement optimal de quatre tâches (A[0-3], B[3-5], C[0-4], D[4-6]) sur deux machines de capacité 2 — diagramme de Gantt en haut, profil de charge en bas qui sature la capacité 2 presque partout (un seul créneau de capacité 1 visible).
- **Poids** : 29.9 KB (PIL optimisé)
- **Note** : nom de fichier `csp3-global-constraints` conservé ; la figure illustre spécifiquement la contrainte `Cumulative` (section 2.2 du notebook), pas `AllDifferent` — dette de nommage disclosed (EPIC #5780).

## csp4-jobshop-gantt.png

- **Source** : notebook `CSP-4-Scheduling.ipynb` (cellule 7, output 0)
- **Alt-text (FR)** : Diagramme de Gantt d'un ordonnancement Job-Shop (JSSP) résolu par CP-SAT : trois jobs (trois opérations chacun) entrelacés sur trois machines via `IntervalVar` et `NoOverlap`. Makespan optimal = 11, fin de la dernière opération à t=11.
- **Poids** : 21.6 KB (PIL optimisé)

## csp6-lazy-clause-generation.png

- **Source** : notebook `CSP-6-Hybridization.ipynb` (cellule 20, output 0)
- **Alt-text (FR)** : Benchmark de parallélisation CP-SAT sur N-Queens 12 : deux graphiques — temps de résolution (en secondes) pour 1, 2 puis 4 workers (≈ 4.7 / 5.6 / 6.5 ms, croissance légère), et speedup effectif vs workers (courbe verte décroissante sous 1×, idéal linéaire en pointillé). Sur cette instance le surcoût de coordination l'emporte et le speedup réel reste sous 1×.
- **Poids** : 36.1 KB (PIL optimisé)
- **Note** : nom de fichier `csp6-lazy-clause-generation` conservé par compatibilité EPIC #5654 ; la figure illustre le benchmark multi-workers (section 5 du notebook), pas des clauses apprises LCG — dette de nommage disclosed (EPIC #5780).

## csp8-allen-algebra.png

- **Source** : notebook `CSP-8-Temporal.ipynb` (cellule 6, output 0)
- **Alt-text (FR)** : Algèbre d'intervalles d'Allen : rendu partiel des 13 relations temporelles de base entre deux intervalles — seulement 5 vignettes correctement tracées (before, meets, overlaps, during, equals) sur les 13 attendues. Le tracé des huit autres vignettes (after, started-by, contains, finishes, finished-by, started-by, overlaps-with-inverse, met-by) est défaillant dans la sortie actuelle du notebook ; limitation illustrative assumée, en attente de correction du tracé et de ré-exécution.
- **Poids** : 36.9 KB (PIL optimisé)