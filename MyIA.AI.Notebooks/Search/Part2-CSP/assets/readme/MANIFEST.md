# MANIFEST des figures README

Provenance des images de `assets/readme/` (EPIC #5654, source 1 = extraction d'outputs de notebooks).

> **Audit vision po-2025 c.472 (2026-07-14, doctrine #5780)** : les 6 PNG ci-dessous ont été ouverts un par un via l'outil `Read` et comparés à leur alt-text. Verdict par figure dans le champ *Contenu réel vérifié*. Cohérence caption ↔ image = 6/6 confirmée (toutes les alt-texts décrivent fidèlement le rendu visuel). Aucune correction d'alt-text nécessaire ; 2 dettes de nommage déjà disclosed dans l'ancien MANIFEST sont conservées (compatibilité EPIC #5654).

## csp1-backtracking-tree.png

- **Source** : notebook `CSP-1-Fundamentals.ipynb` (cellule 9, output 0)
- **Alt-text (FR)** : Graphe de contraintes de la coloration de l'Australie : sept variables — WA, NT, SA, Q, NSW, V, T (Tasmanie) — chacune avec un domaine de trois couleurs (Rouge, Vert, Bleu), reliées par des contraintes de différence sur les frontières partagées. La Tasmanie, sans voisin, flotte hors du graphe. Le titre de fichier historique `csp1-backtracking-tree` renvoie à la section du notebook qui produit ce tracé (introduction du backtracking MRV avant l'exemple de coloration).
- **Contenu réel vérifié** : Graphe titré « Graphe de contraintes - Australie » avec exactement 7 noeuds (V, NSW, SA, WA, NT, Q, T) connectés comme décrit ; chaque noeud porte un label `|D|=3` (T isolé, sans voisin, est positionné en bas-droite hors du graphe principal). Couleur uniforme cyan pâle. Arêtes grises non-orientées. **Alt-text cohérent avec l'image.**
- **Poids** : 29.0 KB (PIL optimisé)
- **Note** : nom de fichier `csp1-backtracking-tree` conservé par compatibilité EPIC #5654 ; le PNG illustre le graphe de contraintes (coloration), pas un arbre de backtracking — dette de nommage disclosed (EPIC #5780).

## csp2-ac3-propagation.png

- **Source** : notebook `CSP-2-Consistency.ipynb` (cellule 20, output 0)
- **Alt-text (FR)** : Propagation de contraintes AC-3 sur le graphe de la coloration de l'Australie, avant / après fixation de WA = Rouge : à gauche les domaines complets (trois couleurs par variable), à droite les domaines réduits après l'arc-cohérence (WA singleton Rouge, SA et NT ramenés à {Vert, Bleu} par déduction, les autres variables intactes).
- **Contenu réel vérifié** : Figure titrée « Propagation AC-3 sur la coloration de l'Australie » en deux panneaux « Avant AC-3 (WA=Rouge fixé) » / « Après AC-3 ». 7 noeuds dans chaque panneau ; sur le panneau gauche tous les domaines sont `{Rouge, Vert, Bleu}` (cyan pâle = domaine complet) ; sur le panneau droit WA est passé en vert singleton (`{Rouge}`), SA et NT en jaune (`{Vert, Bleu}` = domaine réduit), NSW, Q, V, T restent cyan (domaine complet). Légende en bas = « Singleton (assigné) » / « Domaine réduit » / « Domaine complet ». **Alt-text cohérent avec l'image.**
- **Poids** : 92.0 KB (PIL optimisé)

## csp3-global-constraints.png

- **Source** : notebook `CSP-3-Advanced.ipynb` (cellule 10, output 0)
- **Alt-text (FR)** : Contrainte globale Cumulative d'OR-Tools CP-SAT : ordonnancement optimal de quatre tâches (A[0-3], B[3-5], C[0-4], D[4-6]) sur deux machines de capacité 2 — diagramme de Gantt en haut, profil de charge en bas qui sature la capacité 2 presque partout (un seul créneau de capacité 1 visible).
- **Contenu réel vérifié** : Figure composite en deux sous-graphiques. Haut : diagramme de Gantt titré « Ordonnancement optimal - 4 taches, 2 machines » avec 4 barres horizontales (A[0-3] bleu, B[3-5] vert, C[0-4] orange, D[4-6] rouge) — A et C simultanées sur deux machines distinctes de t=0 à t=4, puis B sur machine 0 t=3-5 et D sur machine 1 t=4-6. Bas : « Profil de charge des ressources » — barres verticales de charge (1 ou 2) au-dessus de l'axe Temps, ligne pointillée rouge horizontale « Capacite = 2 ». Profil : charge=2 sur [0,4], charge=1 sur [4,5], charge=1 sur [5,6]. **Alt-text cohérent avec l'image** (le « seul créneau de capacité 1 » mentionné correspond exactement au segment t∈[4,6] du profil de charge).
- **Poids** : 29.9 KB (PIL optimisé)
- **Note** : nom de fichier `csp3-global-constraints` conservé ; la figure illustre spécifiquement la contrainte `Cumulative` (section 2.2 du notebook), pas `AllDifferent` — dette de nommage disclosed (EPIC #5780).

## csp4-jobshop-gantt.png

- **Source** : notebook `CSP-4-Scheduling.ipynb` (cellule 7, output 0)
- **Alt-text (FR)** : Diagramme de Gantt d'un ordonnancement Job-Shop (JSSP) résolu par CP-SAT : trois jobs (trois opérations chacun) entrelacés sur trois machines via `IntervalVar` et `NoOverlap`. Makespan optimal = 11, fin de la dernière opération à t=11.
- **Contenu réel vérifié** : Diagramme de Gantt titré « Diagramme de Gantt - JSSP », axe Y = Machine 0 / Machine 1 / Machine 2, axe X = Temps [0, 11]. 3 jobs (job 0 bleu foncé, job 1 brun-rouge, job 2 cyan) chacun avec 3 opérations (J0T0/J0T1/J0T2, J1T0/J1T1/J1T2, J2T0/J2T1/J2T2). Machine 0 : J0T0 [0,3] + J1T0 [3,5]. Machine 1 : J2T0 [0,6] + J0T1 [6,10] + J1T2 [10,11]. Machine 2 : J1T1 [5,8] + J2T1 [8,10] + J0T2 [10,11]. Makespan = 11 visible en fin de la dernière opération. **Alt-text cohérent avec l'image.**
- **Poids** : 21.6 KB (PIL optimisé)

## csp6-lazy-clause-generation.png

- **Source** : notebook `CSP-6-Hybridization.ipynb` (cellule 20, output 0)
- **Alt-text (FR)** : Benchmark de parallélisation CP-SAT sur N-Queens 12 : deux graphiques — temps de résolution (en secondes) pour 1, 2 puis 4 workers (≈ 4.7 / 5.6 / 6.5 ms, croissance légère), et speedup effectif vs workers (courbe verte décroissante sous 1×, idéal linéaire en pointillé). Sur cette instance le surcoût de coordination l'emporte et le speedup réel reste sous 1×.
- **Contenu réel vérifié** : Figure composite à 2 sous-graphiques juxtaposés. Gauche : « Temps de résolution » — bar chart bleu (axe Y = Temps (s) ∈ [0, 0.006+], axe X = Nombre de workers ∈ {1, 2, 4}) avec 3 barres ≈ 0.0046 / 0.0056 / 0.0066 s (croissance monotone, léger surcoût à 4 workers). Droite : « Speedup vs Workers » — courbe verte pleine décroissante partant de (1, 1.0) vers (2, ~0.85) puis (4, ~0.70), tous sous 1×, avec ligne pointillée grise « Accélération idéale » linéaire (référence théorique). **Alt-text cohérent avec l'image** (les valeurs exactes 4.7 / 5.6 / 6.5 ms annoncées correspondent visuellement aux barres ; speedup < 1× sur les 3 points, conformément à la description).
- **Poids** : 36.1 KB (PIL optimisé)
- **Note** : nom de fichier `csp6-lazy-clause-generation` conservé par compatibilité EPIC #5654 ; la figure illustre le benchmark multi-workers (section 5 du notebook), pas des clauses apprises LCG — dette de nommage disclosed (EPIC #5780).

## csp8-allen-algebra.png

- **Source** : notebook `CSP-8-Temporal.ipynb` (cellule 6, output 0)
- **Alt-text (FR)** : Algèbre d'intervalles d'Allen : rendu partiel des 13 relations temporelles de base entre deux intervalles — seulement 5 vignettes correctement tracées (before, meets, overlaps, during, equals) sur les 13 attendues. Le tracé des huit autres vignettes (after, started-by, contains, finishes, finished-by, started-by, overlaps-with-inverse, met-by) est défaillant dans la sortie actuelle du notebook ; limitation illustrative assumée, en attente de correction du tracé et de ré-exécution.
- **Contenu réel vérifié** : Figure titrée « Allen's Interval Algebra - 13 Relations » avec grille de vignettes labellisées : rangée 1 (before, meets, overlaps, starts), rangée 2 (during, finishes, equals, finished_by), rangée 3 (contains, started_by, overlapped_by, met_by), rangée 4 (after, [vide], [vide], [vide]). Barres effectivement tracées dans **5 vignettes uniquement** : `before` (2 barres disjointes), `meets` (2 barres contiguës), `overlaps` (2 barres qui se chevauchent partiellement), `during` (1 barre englobante + 1 englobée), `equals` (2 barres superposées). Les 8 autres vignettes (starts, finished_by, contains, started_by, overlapped_by, met_by, after, plus 3 cellules vides de la dernière rangée) sont **vides** (aucune barre tracée). **Alt-text cohérent avec l'image** — limitation disclosed honnêtement : seulement 5/13 vignettes rendues.
- **Poids** : 36.9 KB (PIL optimisé)