# Deck S2 - IA exploratoire et symbolique : Analyse Visuelle et Plan d'Amélioration

**Statistiques:** 54 slides, 54 images, 2546 mots, 2.06 MB, dernière mise à jour novembre 2024

**Nature:** Deck TP pratique C# - implémentation hands-on

---

## 1. Diagnostic global

### Points forts
- **Excellent ratio image/slide (1.0)**: Chaque slide a du support visuel
- **Focus pratique cohérent**: TP C# bien identifié, complète les decks théoriques 02 et 03
- **Visuels classiques efficaces**: Carte de Roumanie (AIMA), diagrammes d'algorithmes
- **Taille raisonnable**: 2.06 MB permet un chargement rapide

### Points d'amélioration
- **Actualisation des exemples**: Dernière mise à jour novembre 2024, vérifier si les notebooks C# ont évolué depuis
- **Intégration notebook**: Potentiel pour lier directement aux notebooks `Search/`, `Sudoku/`, `SymbolicAI/`
- **Animations**: Les algorithmes de recherche (A*, génétiques) bénéficieraient d'animations pas-à-pas
- **Cohérence branding**: Footer "Intelligence(s)" à uniformiser avec les autres decks

---

## 2. Recommandations par section

### Section 1: Recherches non informées et informées
**Visuels attendus:**
- ✅ Carte de Roumanie (slide 25)
- 🔄 Suggéré: Animations A*, diagrammes d'arbre de recherche
- 🔄 Suggéré: Screenshots des notebooks Search/ en exécution

**Améliorations:**
- Ajouter des visualisations interactives (gif/animation) pour BFS, DFS, A*
- Capturer des outputs du notebook `Search/AStar.ipynb` pour montrer les résultats réels
- Diagrammes comparatifs de performance (temps/mémoire)

### Section 2: Algorithmes génétiques
**Visuels attendus:**
- ✅ Diagrammes de flux génétique probable
- 🔄 Suggéré: Courbes de fitness, visualisations de convergence

**Améliorations:**
- Graphiques d'évolution de la fitness sur plusieurs générations
- Screenshots du notebook Sudoku/ utilisant GA (si applicable)
- Schémas de crossover et mutation avec exemples concrets

### Section 3: Logique propositionnelle
**Visuels attendus:**
- ✅ Tableaux de vérité, diagrammes logiques probable
- 🔄 Suggéré: Arbres de résolution, CNF/DNF visualisés

**Améliorations:**
- Captures d'écran de Z3 Solver en action
- Diagrammes BDD (Binary Decision Diagrams) pour optimisation
- Exemples de SAT solving avec visualisation des clauses

### Section 4: FOL (First-Order Logic)
**Visuels attendus:**
- ✅ Diagrammes de quantificateurs probable
- 🔄 Suggéré: Graphes de prédicats, exemples de preuves

**Améliorations:**
- Visualisations de la résolution en FOL
- Screenshots de Tweety Framework (si utilisé dans SymbolicAI/)
- Exemples de traduction FOL -> SMT

### Section 5: SMTs (Satisfiability Modulo Theories)
**Visuels attendus:**
- ✅ Diagrammes de solveurs probable
- 🔄 Suggéré: Comparaisons SMT vs SAT, exemples de théories

**Améliorations:**
- Captures de Z3 résolvant des problèmes réels du notebook Sudoku/
- Diagrammes architecturaux des solveurs SMT
- Comparaisons de performance entre différentes stratégies

---

## 3. Cross-references notebooks

### Notebooks directement liés
| Notebook | Lien avec le deck | Opportunité |
|----------|-------------------|-------------|
| `Search/AStar.ipynb` | Recherche informée A* | Capturer outputs, animations |
| `Search/GeneticAlgorithms.ipynb` | Algorithmes génétiques | Courbes de fitness, exemples |
| `Sudoku/SudokuZ3.ipynb` | SMT solving pratique | Screenshots de résolution |
| `SymbolicAI/FOL-Tweety.ipynb` | FOL avec Tweety | Exemples de preuves |
| `SymbolicAI/Z3-SMT.ipynb` | SMT avancé | Cas d'usage complexes |

### Mise à jour recommandée
1. **Exécuter tous les notebooks** avec `/execute-notebook` pour capturer les outputs à jour
2. **Extraire les visualisations** générées par matplotlib/graphviz dans les notebooks
3. **Créer des gifs** pour les algorithmes itératifs (A*, GA) avec `notebook-tools.py`

---

## 4. Plan d'amélioration prioritaire

### Phase 1: Synchronisation avec notebooks (1-2h)
- [ ] Exécuter les notebooks `Search/` et capturer les visualisations A*/BFS/DFS
- [ ] Exécuter `Sudoku/SudokuZ3.ipynb` et capturer les étapes de résolution Z3
- [ ] Vérifier la cohérence des exemples C# avec les notebooks .NET Interactive

### Phase 2: Enrichissement visuel (2-3h)
- [ ] Créer des animations pour les algorithmes de recherche (gif ou slides animées)
- [ ] Ajouter des courbes de performance (fitness GA, temps de résolution SMT)
- [ ] Insérer des screenshots de code C# avec syntax highlighting (pas de texte brut)

### Phase 3: Cohérence et branding (30min)
- [ ] Uniformiser les footers "Intelligence(s)" avec les autres decks
- [ ] Vérifier la numérotation des slides et sections
- [ ] Ajouter des slides "Questions?" entre sections majeures (pause pédagogique)

### Phase 4: Validation (30min)
- [ ] Relecture complète avec un focus sur la clarté des diagrammes
- [ ] Tester la navigation (liens internes, transitions)
- [ ] Vérifier que chaque concept C# a un exemple visuel

---

## Priorités immédiates

1. **HAUTE**: Capturer les outputs des notebooks Search/ et Sudoku/ pour illustrations réelles
2. **HAUTE**: Créer des animations pour A* (l'exemple classique Roumanie mérite une animation)
3. **MOYENNE**: Ajouter des courbes de fitness pour les algorithmes génétiques
4. **BASSE**: Harmoniser le branding avec les autres decks

---

**Note**: Ce deck a un bon équilibre visuel. L'amélioration principale consiste à **dynamiser** les contenus statiques (animations) et **synchroniser** avec les notebooks C# pour montrer des résultats réels d'exécution.
