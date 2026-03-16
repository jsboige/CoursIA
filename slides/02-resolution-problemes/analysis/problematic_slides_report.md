# Rapport des Slides Problématiques - Deck 02-resolution-problemes

Ce rapport identifie les slides qui nécessitent une attention particulière lors de la conversion vers Marp, avec des recommandations spécifiques.

---

## Catégorie 1: Slides Trop Denses (>100 mots)

Ces slides contiennent trop de texte pour une présentation efficace. Elles devraient être fractionnées.

### Slide 9 - Formulation de problèmes
**Statistiques**: 113 mots, 0 image
**Layout**: Title and Content

**Problème**:
- Liste dense avec 9 points
- Formules mathématiques intégrées
- Définitions techniques complexes

**Solution Marp**: Fractionner en 2 slides
```markdown
---
# Formulation de problèmes

Un problème est défini par les éléments suivants:

- **Etat initial**: e.g., "à Arad"
- **Actions**: Fonction successeur S(x) = ensemble de paires actions-état
- **Test de but**: Explicite ou implicite
- **Coût de chemin**: Optionnel, additif

---
# Formulation de problèmes (suite)

**Exemples**:

- Etat initial: "à Arad"
- S(Arad) = {<Arad → Zerind, Zerind>, … }
- Test explicite: x = "à Bucharest"
- Test implicite: EchecEtMat(x)
- Coût: Somme des distances, nombre d'actions
```

### Slide 25 - Exploration en profondeur d'abord (DFS)
**Statistiques**: 115 mots, 1 image
**Layout**: Title and Content

**Problème**:
- Liste de caractéristiques très longue
- Notation mathématique (O(bm))
- Variante (backtracking) en bas

**Solution Marp**: Séparer caractéristiques et variantes
```markdown
---
# Exploration en profondeur d'abord (DFS)

Développe les nœuds les plus profonds en premier
La frontière est une Pile (LIFO)

**Caractéristiques**:
- Complet? Non (échoue dans espaces de profondeur infinie)
- Complexité en temps: O(b^m)
- Complexité en espace: O(bm) - linéaire!
- Optimal? Non

---
# Variante: Backtracking

On développe 1 seul successeur à la fois → **O(m)** en espace

**Optimisation**:
- Modifier les états plutôt que les copier
- Retour arrière = annulation
```

### Slide 38 - Exploration A*
**Statistiques**: 100 mots, 0 image
**Layout**: Title and Content

**Problème**:
- Formules mathématiques
- Théorèmes avec démonstrations
- Dense en concepts

**Solution Marp**: Split en 2 slides
```markdown
---
# Exploration A*

Idée: éviter de développer les nœuds déjà coûteux
Minimisation du coût total estimé de la solution

**Fonction d'évaluation**: f(n) = g(n) + h(n)
- g(n) = coût pour atteindre n
- h(n) = coût estimé de n au but
- f(n) = coût total estimé du chemin au but en passant par n

Identique à UCS avec **g+h** au lieu de g

---
# Théorèmes A*

**Si h(n) est admissible**:
- A* est optimal en exploration d'arbre
- Démonstration par l'absurde

**Si h(n) est consistante**:
- A* est optimal en exploration de graphe
- f est monotone → Démonstration par l'absurde
```

### Slide 42 - Production d'heuristiques
**Statistiques**: 125 mots, 0 image
**Layout**: Title and Content

**Problème**:
- 6 sections différentes
- Exemples multiples
- Concepts variés

**Solution Marp**: Fractionner en 3 slides
```markdown
---
# Production d'heuristiques (1/3)

**Problèmes relaxés**:
Problème avec moins de restrictions = problème relaxé
Coût exact d'une solution optimale relaxée = heuristique admissible

**Exemple du Taquin**:
- Une pièce peut bouger n'importe où → h1 (nb pièces mal placées)
- Une pièce peut bouger sur case adjacente → h2 (distance Manhattan)

---
# Production d'heuristiques (2/3)

**Sous-problèmes**:
Exemple: Taquin, pièces 1,2,3,4 uniquement

**Bases de données de motifs**:
- Coût exact de solutions de sous-problèmes
- Motifs disjoints
- Question de l'additivité

---
# Production d'heuristiques (3/3)

**Apprentissage d'heuristiques**:
- Utilisation de l'expérience sur solutions connues
- Apprentissage inductif à partir de caractéristiques pertinentes
- Approche classique: h(n) = c1·x1(n) + c2·x2(n)
- Domaine vaste: Machine Learning
```

### Slide 63 - Décisions imparfaites
**Statistiques**: 148 mots, 0 image
**Layout**: Title and Content

**Problème**: **Plus dense du deck**

**Solution Marp**: Fractionner en 3 slides minimum
```markdown
---
# Décisions imparfaites: Approche

**Utilité → Fonction d'évaluation heuristique**
- Eval(s) sur états non terminaux

**Test de terminaison → Test d'arrêt**
- Cutoff(s) pour savoir quand appliquer l'évaluation
- Ex: profondeur limite dlim

---
# Fonction d'évaluation

**Cf. Humains** ← attributs d'un état
- Classe d'équivalence → valeur attendue (utilité pondérée)
- Trop de classes → valeur matérielle → fonction linéaire pondérée
- **Eval(s) = w1·f1(s) + w2·f2(s) + … + wn·fn(s)**
- Non indépendance → fonction non linéaire
- Sans expérience: apprentissage possible (1 fou = 3 pions!)

---
# Exploration avec arrêt

**Alpha Beta Itératif**:
- Pour respecter limite de temps (+ ordre des coups)

**Problème des situations instables au cutoff**:
- Solution: Recherche de stabilité ("quiescence", ex: pas de prise)

**Effet d'horizon**:
- Un évènement peut être retardé au-delà du cutoff
- Solution: Extension de singularité (ex: prises)
```

### Slide 76 - Types de contraintes
**Statistiques**: 128 mots, 1 image
**Layout**: Title and Content

**Problème**:
- Exemple cryptarithmétique très long
- Formules mathématiques
- Image à droite

**Solution Marp**: Split en 2 slides
```markdown
---
# Types de contraintes

**Unaires**: 1 variable (ex: SA ≠ vert)

**Binaires**: 1 paire de variables (ex: SA ≠ WA)

**Globales**: 3+ variables

**Représentation**: Hypergraphe des contraintes
- Variables auxiliaires possibles
- Réduction à contraintes binaires (Graphe Biparti)

**Contraintes de préférences**:
CSP → COP (Problème d'optimisation de contraintes)

---
# Exemple: Cryptarithmétique

```
  F T U W R O
+ F T U W R O
-------------
  C O D E R
```

**Variables**: F,T,U,W,R,O,X1,X2,X3
**Domaines**: {0,1,2,3,4,5,6,7,8,9}

**Contraintes**:
- AllDiff(F,T,U,W,R,O)
- O+O = R + 10·X1
- X1+W+W = U + 10·X2
- X2+T+T = O + 10·X3
- X3 = F, T≠0, F≠0
```

### Slide 78 - Formulation standard d'exploration
**Statistiques**: 92 mots, 0 image
**Layout**: Title and Content

**Solution Marp**: Simplifier légèrement
```markdown
---
# Formulation standard d'exploration CSP

**Les états** = valeurs assignées

**Etat initial**: assignation vide {}

**Fonction successeur**:
- Assigner valeur aux variables non assignées
- Compatible avec assignation courante
- Echec si pas d'assignation légale

**Test de but**: assignation complète

---
# Propriétés

- Identique pour tous les CSPs
- Chaque solution = profondeur n (n variables)
- **Exploration DFS**: Le chemin n'est pas important
- Facteur de branchement: b = (n-p)·d à profondeur p
- **n!·d^n feuilles**
```

### Slide 82 - Ordre des variables et des valeurs
**Statistiques**: 100 mots, 3 images
**Layout**: **Two Content** (Layout spécial!)

**Problème**: Layout PPTX Two Content avec 3 images dans colonne droite

**Solution Marp**: Utiliser layout two-cols
```markdown
---
<!-- _class: two-cols -->
# Ordre des variables et des valeurs

**Objectif**: Détecter incohérences au plus tôt

## Heuristiques de choix de variables

**MRV** (Minimum Remaining Values):
Variable avec le moins de valeurs légales

**Degré**:
Si égalité MRV → Variable la plus contraignante

**LCV** (Least Constraining Value):
Valeur qui exclut le moins de choix

**Weighted Degree**:
Priorise variables dans nombreux conflits

<div class="right">

![MRV](slide_82_img_000.png)
![Degré](slide_82_img_001.png)
![LCV](slide_82_img_002.png)

</div>
```

### Slide 84 - Exploration locale pour les CSPs
**Statistiques**: 132 mots, 0 image
**Layout**: **Two Content**

**Problème**: Layout Two Content, très dense

**Solution Marp**: Split en 2 slides
```markdown
---
<!-- _class: two-cols -->
# Exploration locale pour les CSPs

**Algorithmes très efficaces** quand solutions denses

**Formulation**: Etats complets
**Modification**: Une variable à la fois
**Elimination**: Contraintes violées

**Heuristique Min-Conflits**:
- Choisir valeur minimisant conflits
- N-reines: Nombre d'étapes quasi constant!

**Avantage**: Changement à la volée
Ex: Trafic aérien et météo

**Colonne 2**:
- Déplacements latéraux
- Exploration taboue
- Pondération de contraintes
- Hybridation CP + Métaheuristiques

---
# Techniques avancées

**Exploration taboue**:
Eviter de revenir sur états récents

**Pondération de contraintes**:
- Contraintes reçoivent un poids
- Minimiser le poids
- Poids mis à jour chaque étape

**Hybridation CP + Métaheuristiques**:
- Large Neighborhood Search (LNS)
- Relâchement partiel + Réparation CP
- Recherche locale stochastique + Propagation
```

### Slide 85 - Structure des problèmes
**Statistiques**: 154 mots, 2 images
**Layout**: Title and Content

**Problème**: **Deuxième slide la plus dense**

**Solution Marp**: Fractionner en 2 slides
```markdown
---
# Structure des problèmes (1/2)

**Idée**: Décomposition en sous-problèmes

**Composantes connexes**:
Sous-problèmes indépendants
Ex: Tasmanie vs Australie continentale
Complexité: O(d^c·n/c) → **Exponentielle → Linéaire!**

**Structure d'arbre**:
- Cohérence d'arc dirigé (DAC)
- Tri topologique + DAC en O(n·d²)
- Assignation sans retour arrière

![Graphe composantes](slide_85_img_000.png)

---
# Structure des problèmes (2/2)

**Faire apparaitre l'arbre**:
- Assignation des "bonnes" variables: Australie méridionale
- **Ensemble coupe-cycle** (cutset)
- Coupe cycle minimal NP-complet (ex: graphes petit-monde)

**Méthodes**:
- Conditionnement du coupe cycle
- Décomposition en arbre de sous-problèmes connexes
- Largeur d'arbre w → O(n·d^(w+1))

**Structure des domaines**:
Ex: Coloration, n! permutations → **symétrie**
→ Contrainte de rupture de symétrie
ex: NT < SA < WA

![Arbre décomposition](slide_85_img_001.png)
```

---

## Catégorie 2: Slides avec Layouts Spéciaux

### Slide 17 - Arbre d'exploration: exemple
**Statistiques**: 6 mots, 1 image (diagramme)
**Layout**: Title and Content

**Problème**: Image centrée très large (~60%)

**Solution Marp**:
```markdown
---
<!-- _class: centered-img -->
# Arbre d'exploration: exemple

<br><br>

![search-map3c](slide_17_img_000.png)

<br>

*Exemple de carte de recherche avec arbre d'exploration*
```

### Slide 29 - Résumé Exploration non informée
**Statistiques**: 43 mots, 1 image (tableau)
**Layout**: Title and Content

**Problème**: Tableau large (~80% de largeur)

**Solution Marp**:
```markdown
---
# Résumé Exploration non informée

Nécessité d'une abstraction du monde réel
Variété des stratégies: En largeur (Queue) vs En profondeur (Pile)

| Critère | BFS | UCS | DFS | DLS | IDS |
|---------|-----|-----|-----|-----|-----|
| Complet | Oui | Oui | Non | Si l≥d | Oui |
| Optimal | Oui | Oui | Non | Non | Oui |
| Temps | O(b^d) | O(b^d) | O(b^m) | O(b^l) | O(b^d) |
| Espace | O(b^d) | O(b^d) | O(b·m) | O(b·l) | O(b·d) |
```

### Slide 59 - Arbre de jeu
**Statistiques**: 30 mots, 1 image
**Layout**: Title and Content

**Solution Marp**: Image centrée
```markdown
---
<!-- _class: centered-img -->
# Arbre de jeu

Ex: Morpion

<br>

![tictactoe](slide_59_img_000.png)
```

### Slide 60 - Minimax
**Statistiques**: 4 mots, 1 image
**Layout**: Title and Content

**Solution Marp**: Image centrée grande
```markdown
---
<!-- _class: centered-img -->
# Minimax

<br>

![minimax](slide_60_img_000.png)

*Algorithme Minimax avec valeurs remontées*
```

### Slide 62 - Elagage Alpha-Bêta
**Statistiques**: 5 mots, 1 image
**Layout**: Title and Content

**Solution Marp**: Image centrée très large
```markdown
---
<!-- _class: centered-img -->
# Elagage Alpha-Bêta

<br>

![alpha-beta-progress4c](slide_62_img_000.png)

*Elagage alpha-bêta pour réduire l'arbre de recherche*
```

---

## Catégorie 3: Slides avec Images Multiples Empilées

### Slide 19 - Infrastructure: Etats vs Nœuds
**Statistiques**: 59 mots, 2 images
**Layout**: Title and Content

**Solution Marp**:
```markdown
---
<!-- _class: two-cols -->
# Infrastructure: Etats vs Nœuds

**Etats ≠ Nœuds**

Un **Etat** est une représentation de la configuration réelle

Un **Nœud** est une structure de données constitutive d'une exploration:
- Inclut l'état
- Le nœud parent
- L'action
- Le coût d'étape g(x)
- La profondeur

La fonction de développement crée de nouveaux nœuds et utilise la fonction successeur.

<div class="right">

![Image1](slide_19_img_000.png)
![Image2](slide_19_img_001.png)

</div>
```

### Slide 22 - Exploration en largeur d'abord (BFS)
**Statistiques**: 24 mots, 2 images
**Layout**: Title and Content

**Solution Marp**:
```markdown
---
<!-- _class: two-cols -->
# Exploration en largeur d'abord (BFS)

Développe les nœuds les moins profonds en premier

La frontière est une **queue** (File ou FIFO)

<div class="right">

![BFS tree](slide_22_img_000.png)
![BFS queue](slide_22_img_001.png)

</div>
```

### Slide 45 - Exploration par escalade (HCS)
**Statistiques**: 43 mots, 3 images
**Layout**: Title and Content

**Solution Marp**:
```markdown
---
<!-- _class: two-cols -->
# Exploration par escalade (HCS)

**Escalade par la plus forte pente**:
Exploration locale "gloutonne"

**Problèmes**:
- Maxima locaux
- Crêtes, plateaux, paliers

**Solutions**:
- Déplacement latéraux (avec limites)
- Escalade stochastique du premier choix
- Escalade avec reprise aléatoire (complet)

<div class="right">

![HCS basic](slide_45_img_000.png)
![8queens local minimum](slide_45_img_001.png)
![HCS variations](slide_45_img_002.png)

</div>
```

### Slide 49 - Algorithme génétique pour les 8 reines
**Statistiques**: 11 mots, 2 images
**Layout**: Title and Content

**Solution Marp**:
```markdown
---
<!-- _class: two-cols -->
# Algorithme génétique pour les 8 reines

**Génétique**

<div class="right">

![Genotype](slide_49_img_000.png)
![Phenotype](slide_49_img_001.png)

</div>
```

### Slide 66 - Classes de Jeux complexes
**Statistiques**: 7 mots, 3 images
**Layout**: Title and Content

**Solution Marp**:
```markdown
---
<!-- _class: two-cols -->
# Classes de Jeux complexes

<div class="right">

![Game type 1](slide_66_img_000.png)
![Game type 2](slide_66_img_001.png)
![Game type 3](slide_66_img_002.png)

</div>
```

---

## Résumé des Actions Recommandées

### Actions Immédiates (Critiques)

1. **Fractionner 10 slides très denses** (>100 mots)
   - Slides: 9, 25, 38, 42, 63, 76, 78, 82, 84, 85
   - Résultat: ~20 slides au lieu de 10

2. **Créer layouts CSS personnalisés**
   - `two-cols`: Pour les 35 slides texte + 1 image
   - `centered-img`: Pour les 7 slides à image centrée
   - `wide-table`: Pour le tableau de la slide 29

3. **Extraire et optimiser les images**
   - Les images sont déjà dans `extracted/images/`
   - Vérifier la résolution pour les images larges (slides 29, 60, 62, 81)

### Actions Secondaires

4. **Normaliser les layouts Two Content**
   - Slides 82 et 84 utilisent un layout PPTX Two Content
   - Adapter avec le layout Marp `two-cols`

5. **Optimiser les slides à images multiples**
   - 7 slides avec 2+ images
   - S'assurer que les images s'empilent correctement

### Statistiques de Conversion

| Métrique | Avant | Après (estimé) |
|----------|-------|----------------|
| Total slides | 93 | ~103-108 |
| Slides texte + image | 42 | 42 |
| Slides très denses | 10 | 0 (fractionnées) |
| Slides à layout spécial | 7 | 7 (avec CSS dédié) |

---

## Fichiers de Configuration Marp Proposés

### marp-config.js

```javascript
module.exports = {
  theme: 'custom',
  themeSet: {
    custom: './custom-theme.css'
  },
  plugins: []
};
```

### custom-theme.css

```css
/* @theme custom */

/* Layout two-cols standard */
.slide.two-cols {
  display: grid;
  grid-template-columns: 62% 36%;
  gap: 2%;
  align-items: start;
}

.slide.two-cols.wide-img {
  grid-template-columns: 55% 43%;
}

.slide.two-cols .right {
  display: flex;
  flex-direction: column;
  gap: 0.5rem;
  align-items: center;
}

.slide.two-cols .right img {
  max-width: 100%;
  height: auto;
}

/* Layout centered-img */
.slide.centered-img {
  display: flex;
  flex-direction: column;
  align-items: center;
}

.slide.centered-img img {
  max-width: 90%;
  max-height: 70vh;
  object-fit: contain;
}

/* Layout wide-table */
.slide.wide-table table {
  width: 95%;
  margin: 0 auto;
  font-size: 0.85em;
}

.slide.wide-table th,
.slide.wide-table td {
  padding: 0.3em 0.5em;
}
```

---

## Conclusion

Ce deck de 93 slides est bien structuré et utilise principalement le layout **Title and Content** de PowerPoint. La conversion vers Marp est donc relativement simple avec:

1. **Layout `two-cols`** pour la majorité (35 slides)
2. **Layout `centered-img`** pour les diagrammes centraux (7 slides)
3. **Fractionnement** de 10 slides très denses

Les images sont déjà extraites et les patterns sont cohérents tout au long du deck.
