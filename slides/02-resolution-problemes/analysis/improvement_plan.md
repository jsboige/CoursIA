# Deck 02 - Resolution de problemes : Analyse Visuelle et Plan d'Amelioration

**Date d'analyse** : 2026-02-13
**Fichier source** : Intelligence Artificielle - 2 - Resolution de problemes.pptx
**Statistiques** : 93 slides, 56 images, 3.6 MB
**Sections** : Exploration (non informee + informee), Jeux (minimax, alpha-beta, MCTS), CSPs

---

## 1. Diagnostic global

### Points forts
- **Bien plus visuel que le deck 01** : nombreux diagrammes AIMA (arbres, graphes, cartes)
- **Bons exemples concrets** : carte de Roumanie (slide 7), taquin (12), 8 reines (13), missionnaires/cannibales (30 - excellente illustration), escalade avec visuels (45)
- **Arbre minimax** (slide 60) : classique AIMA, bien presente
- **Graphe de contraintes** (slide 75) : coloration Australie, clair
- **Section CSP** solide avec exemples visuels (coloration, Sudoku mentionne)
- **Pseudo-code** bien formate tout au long (slides 6, 16, 18, etc.)
- **Monte-Carlo Tree Search** (slide 65) : sujet moderne et pertinent

### Problemes identifies
1. **Slides "Questions?" vides** : au moins slide 14, pattern recurrent
2. **Slides TP minimalistes** : slides 50 et 90 sont quasi-vides (juste un lien)
3. **Slide 85** (Structure des problemes) : **extremement dense**, trop de texte + pseudo-code + diagrammes comprimes
4. **Section exploration non informee** : beaucoup de slides textuelles consecutives (21-30)
5. **Certains diagrammes AIMA pixelises** : images scannees/captures basse resolution
6. **Pas de mention des notebooks** Sudoku, Search, CSPs_Intro existants
7. **Footer inconstant** : alterne "IA 101" et "CS 405" (slides 65, 80)

### Metriques visuelles estimees
- Slides avec diagrammes/images : ~40/93 (43%) - bien meilleur que deck 01
- Slides texte pur dense : ~25/93
- Slides de navigation/sommaire : ~8/93
- Slides placeholder (Questions?, TP vides) : ~5/93

---

## 2. Recommandations par section

### Section Exploration non informee (slides 15-30)
- **Conserver** : arbres BFS/DFS (bons visuels), carte Roumanie, missionnaires
- **Ameliorer** : slide 21 (texte pur -> ajouter tableau comparatif BFS/DFS/UCS/IDS)
- **Slides 50, 90** (TP) : enrichir avec liens vers notebooks `Search/`, `Sudoku/`

### Section Exploration informee (slides 35-55)
- **Conserver** : escalade avec visuels (paysage, 8 reines)
- **Ameliorer** : ajouter visualisation A* pas-a-pas sur la carte Roumanie
- **Moderniser** : mentionner l'utilisation de A* dans les jeux video, GPS

### Section Jeux (slides 56-70)
- **Conserver** : arbre minimax, alpha-beta
- **Moderniser** : slide MCTS mentionne AlphaGo mais pourrait ajouter MuZero, Pluribus
- **Cross-ref** : `GameTheory/` notebooks

### Section CSPs (slides 70-90)
- **Conserver** : graphe de contraintes Australie, backtracking
- **Ameliorer** : slide 85 beaucoup trop dense, eclater en 2-3 slides
- **Cross-ref** : `Sudoku/Sudoku-1-Backtracking.ipynb` a `Sudoku-6-Infer.ipynb`, `Search/CSPs_Intro.ipynb`

---

## 3. Cross-references notebooks

| Slide(s) | Concept | Notebooks |
|-----------|---------|-----------|
| 7, 16-29 | Exploration BFS/DFS/A* | `Search/Exploration_non_informee_et_informee_intro.ipynb` |
| 12-13 | Taquin, 8 reines | `Sudoku/Sudoku-1-Backtracking.ipynb` (meme logique) |
| 45 | Exploration locale, genetique | `Search/Portfolio_Optimization_GeneticSharp.ipynb`, `Sudoku/Sudoku-2-Genetic.ipynb` |
| 60-65 | Minimax, Alpha-Beta, MCTS | `GameTheory/GameTheory-8-CombinatorialGames.ipynb` |
| 70-85 | CSPs, Backtracking, AC-3 | `Search/CSPs_Intro.ipynb`, `Sudoku/Sudoku-3-ORTools.ipynb`, `Sudoku/Sudoku-4-Z3.ipynb` |
| 80 | AllDiff, contraintes globales | `Sudoku/Sudoku-5-DancingLinks.ipynb` |

---

## 4. Plan d'amelioration prioritaire

### P1 : Corrections immediates
1. ~~Supprimer les slides "Questions?" vides~~ **GARDER** : servent de respiration entre sections
2. Harmoniser les footers (IA 101 partout)
3. Enrichir les slides TP (50, 90) avec liens notebooks

### P2 : Ameliorations visuelles
4. Eclater slide 85 (trop dense) en 2-3 slides
5. Ameliorer la resolution des diagrammes AIMA captures
6. Ajouter tableau comparatif des strategies d'exploration (BFS/DFS/UCS/IDS/A*)

### P3 : Modernisation
7. Mettre a jour section MCTS : MuZero (2019), Pluribus poker (2019)
8. Ajouter slide cross-ref notebooks a la fin
9. Mention Sudoku comme exemple-fil-rouge des CSPs avec notebooks

### Estimation : ~2-3h d'ameliorations
