# Deck 03 - Logique : Analyse Visuelle et Plan d'Amelioration

**Date d'analyse** : 2026-02-13
**Fichier source** : Intelligence Artificielle - 3 - Logique.pptx
**Statistiques** : 66 slides, 45 images, 4449 mots, 5.43 MB
**Sections** : Agents KB, Logique propositionnelle, FOL, Planification, Representation des connaissances

---

## 1. Diagnostic global

### Points forts
- **Contenu solide et complet** : couvre AIMA ch. 7-12 de maniere exhaustive
- **Monde du Wumpus** (slide 5) : bon exemple fil-rouge avec visuels de grille
- **Chainage avant/arriere** (slide 14) : diagrammes clairs avec fleches
- **Web semantique** (slide 58) : slide riche avec pile W3C, logos dotNetRDF/BrightstarDB
- **Graphes de planification** (slides 48-49) : diagrammes detailles avec exemples
- **Aparte Argumentation** (slides 28-32) : section originale liant logique et pensee critique
- **Pseudo-code** bien presente (slides 15, 16)
- **References outils modernes** : Z3, Lean, Tweety, e-prover, OR-Tools (slide 40)

### Problemes identifies
1. **Deck extremement textuel** : la majorite des slides sont des murs de texte sans visuels
2. **Slides tres denses** : slide 18 (143 mots), slide 49 (155 mots), slide 65 (177 mots)
3. **Footer inconstant** : alterne "IA 101" et "CS 405" (slides 35, 40, 45-54, 58-62)
4. **Section Smart Contracts** (slide 61) : semble hors sujet dans un deck logique
5. **Argumentation** (slides 28-32) : bonne digression mais 100% texte, aucun schema
6. **Projets de groupe** (slide 65) : liste tres dense et datee (mentionne CNTK, Encog, Lucene.Net)
7. **Pas de visuels pour les concepts cles** : tables de verite, arbres de preuve, unification
8. **Section FOL** (slides 23-34) : 12 slides textuelles consecutives quasi sans images
9. **Pas de cross-references notebooks** : Lean, Z3, Tweety sont dans le workspace

### Metriques visuelles estimees
- Slides avec images/diagrammes significatifs : ~20/66 (30%)
- Slides texte pur dense : ~35/66 (53%) - le plus austere des 3 premiers decks
- Slides navigation/sommaire : ~7/66
- Slides Questions? (respiration) : 5/66 (slides 8, 21, 43, 55, 63)

---

## 2. Recommandations par section

### Section Agents KB (slides 1-8)
- **Conserver** : Wumpus (slide 5), representation et logique (slide 6)
- **Ameliorer** : slide 7 (types de logiques) - ajouter le tableau AIMA avec exemples
- **Slide 4** : ajouter diagramme agent KB (AIMA fig. 7.1)

### Section Logique propositionnelle (slides 9-21)
- **Conserver** : chainage (14), resolution (15), DPLL (16), exploration locale (17)
- **Ameliorer** : slide 10 - ajouter table de verite visuelle coloree
- **Ameliorer** : slide 12 (regles d'inference) - trop de texte, ajouter arbre de preuve
- **Eclater** : slide 18 (143 mots, agents logiques) en 2-3 slides
- **Ajouter** : visualisation du Wumpus pas-a-pas avec inference

### Section FOL (slides 22-43)
- **La plus austere** : 12 slides textuelles consecutives (23-34)
- **Ameliorer** : slide 23 (FOL intro) - ajouter diagramme objets/relations/fonctions
- **Ameliorer** : slide 26 (quantificateurs) - schema portee/negation
- **Ameliorer** : slide 27 (traductions) - arbres syntaxiques des formules
- **Argumentation** (28-32) : ajouter schema graphe d'attaque (Dung), taxonomie visuelle des fallacies
- **Moderniser** : slide 36 (HOL) - mention Lean 4, proof assistants modernes
- **Moderniser** : slide 40 (SMT) - Z3 + Microsoft Copilot verification, OR-Tools exemples

### Section Planification (slides 44-55)
- **Ameliorer** : slide 45 - ajouter diagramme espace d'etats vs espace de plans
- **Conserver** : slides 48-49 (graphes de planification, bien illustrees)
- **Ameliorer** : slide 50 - ajouter schema SatPlan/CSP
- **Moderniser** : mentionner planification avec LLMs (ex: SayCan, Code-as-Policies)

### Section Representation des connaissances (slides 56-66)
- **Conserver** : slide 58 (web semantique, bon visuel)
- **Ameliorer** : slide 57 (ontologies) - ajouter diagramme hierarchie de classes
- **Moderniser** : slide 61 (Smart Contracts) - lien discutable avec la logique, mais pertinent comme application
- **Eclater** : slide 65 (projets) - trop dense (177 mots), mettre a jour les sujets
- **Cross-ref** : lier aux notebooks SymbolicAI/

---

## 3. Cross-references notebooks

| Slide(s) | Concept | Notebooks |
|-----------|---------|-----------|
| 5, 18 | Wumpus, agents logiques | `Search/Exploration_non_informee_et_informee_intro.ipynb` |
| 12-15 | Regles d'inference, resolution | `SymbolicAI/Lean/Lean-1-Setup.ipynb` a `Lean-10-LeanDojo.ipynb` |
| 16-17 | DPLL, SAT, WalkSAT | `Sudoku/Sudoku-4-Z3.ipynb` (SAT/SMT) |
| 27 | Traductions FOL, fallacies | `SymbolicAI/Argument_Analysis/` (5 notebooks) |
| 28-32 | Argumentation, analyse rhetorique | `SymbolicAI/Argument_Analysis/Argument_Analysis_*.ipynb` |
| 35 | Prolog, chainage, e-prover | `SymbolicAI/Lean/Lean-10-LeanDojo.ipynb` |
| 36-37 | HOL, logique modale | `SymbolicAI/Lean/Lean-3-Propositions.ipynb`, `Lean-5-Tactics.ipynb` |
| 38 | Logiques argumentatives (Dung) | `SymbolicAI/Argument_Analysis/Argument_Analysis_Tweety.ipynb` |
| 40 | SMT, Z3, OR-Tools | `Sudoku/Sudoku-4-Z3.ipynb`, `Sudoku/Sudoku-3-ORTools.ipynb` |
| 45-50 | Planification, PDDL | `Search/CSPs_Intro.ipynb` |
| 57-58 | Ontologies, web semantique | `SymbolicAI/RDF/` notebooks |

---

## 4. Plan d'amelioration prioritaire

### P1 : Corrections immediates
1. Harmoniser les footers ("IA 101" partout, retirer "CS 405")
2. Mettre a jour slide 65 (projets) : remplacer technologies obsoletes (CNTK, Encog)
3. Ajouter liens vers notebooks dans les slides TP/projets

### P2 : Ameliorations visuelles
4. Slide 10 (logique propositionnelle) : ajouter table de verite coloree
5. Slide 12 (regles d'inference) : ajouter arbre de preuve visuel
6. Slide 23 (FOL intro) : ajouter diagramme objets/relations/fonctions
7. Slide 26 (quantificateurs) : ajouter schema portee
8. Eclater slide 18 (trop dense, 143 mots) en 2 slides
9. Slides 28-32 (argumentation) : ajouter schema graphe d'attaque de Dung

### P3 : Modernisation
10. Slide 36 (HOL) : mentionner Lean 4, Coq, proof assistants modernes
11. Slide 40 (SMT) : exemples Z3 modernes, lien notebooks
12. Ajouter mention planification LLM-based (post-2023)
13. Ajouter slide cross-ref notebooks a la fin de chaque section

### Estimation : ~3-4h d'ameliorations
