# Analyse des Layouts PPTX - Deck 02-resolution-problemes

**Fichier**: `Intelligence Artificielle - 2 - Résolution de problèmes.pptx`
**Total slides**: 93
**Slides avec images**: 42 slides (45%)
**Total images**: 56 images

---

## Résumé Exécutif

Ce deck utilise majoritairement le layout **Title and Content** de PowerPoint, avec quelques exceptions notables utilisant **Two Content**. Les images sont généralement positionnées à droite du contenu texte, occupant environ 30-40% de la largeur.

### Principaux patterns identifiés

| Pattern | Fréquence | Description |
|---------|-----------|-------------|
| **Title and Content** | 90 slides | Titre + contenu vertical (liste ou image) |
| **Title Slide** | 2 slides | Slide de titre/partition |
| **Two Content** | 1 slide | Deux colonnes de contenu |

### Layouts avec images par type

- **Title and Content + 1 image**: 35 slides
- **Title and Content + 2 images**: 5 slides
- **Title and Content + 3 images**: 2 slides (slides 45, 66)

---

## Slides avec Images - Analyse Détaillée

### Section 1: Introduction (Slides 1-14)

| Slide | Titre | Layout PPTX | Images | Position | % Largeur | Recommandation Marp |
|-------|-------|-------------|--------|----------|-----------|---------------------|
| 4 | Agent fondé sur des buts | Title and Content | 1 | Droite | ~40% | `columns: 2` gauche 60% texte, droite 40% image |
| 6 | Agents de résolution de problèmes | Title and Content | 1 | Centrée | ~50% | Image centrée sous texte |
| 7 | Exemple: Itinéraire | Title and Content | 1 | Droite | ~35% | `columns: 2` gauche 65% texte, droite 35% image |
| 11 | Exemple Abstraction: Assemblage robotique | Title and Content | 1 | Droite | ~40% | `columns: 2` gauche 60% texte, droite 40% image |
| 12 | Problème jouet: Le taquin | Title and Content | 1 | Droite | ~35% | `columns: 2` gauche 65% texte, droite 35% image |
| 13 | Problème jouet: Les 8 reines | Title and Content | 1 | Droite | ~35% | `columns: 2` gauche 65% texte, droite 35% image |

### Section 2: Exploration non informée (Slides 15-31)

| Slide | Titre | Layout PPTX | Images | Position | % Largeur | Recommandation Marp |
|-------|-------|-------------|--------|----------|-----------|---------------------|
| 16 | Arbre d'exploration | Title and Content | 1 | Droite | ~45% | `columns: 2` gauche 55% texte, droite 45% image |
| 17 | Arbre d'exploration: exemple | Title and Content | 1 (diagramme) | Centrée | ~60% | Image centrée, texte minimal |
| 18 | Exploration de graphe | Title and Content | 1 | Droite | ~45% | `columns: 2` gauche 55% texte, droite 45% image |
| 19 | Infrastructure: Etats vs Nœuds | Title and Content | 2 | Empilées | ~40% chacune | Deux images en colonne droite |
| 22 | Exploration en largeur d'abord (BFS) | Title and Content | 2 | Empilées | ~35% chacune | Deux diagrammes empilés à droite |
| 23 | Propriétés de l'exploration en largeur | Title and Content | 1 | Droite | ~35% | `columns: 2` gauche 65% texte, droite 35% image |
| 25 | Exploration en profondeur d'abord (DFS) | Title and Content | 1 | Droite | ~35% | `columns: 2` gauche 65% texte, droite 35% image |
| 26 | Exploration en profondeur limitée (DLS) | Title and Content | 1 | Droite | ~35% | `columns: 2` gauche 65% texte, droite 35% image |
| 27 | Exploration itérative en profondeur (IDS) | Title and Content | 1 | Droite | ~35% | `columns: 2` gauche 65% texte, droite 35% image |
| 28 | Exploration Bidirectionnelle | Title and Content | 1 | Droite | ~40% | `columns: 2` gauche 60% texte, droite 40% image |
| 29 | Résumé Exploration non informée | Title and Content | 1 | Bas | ~80% | Tableau large en bas |
| 30 | Les missionnaires et cannibales | Title and Content | 1 | Droite | ~40% | `columns: 2` gauche 60% texte, droite 40% image |

### Section 3: Exploration informée (Slides 32-56)

| Slide | Titre | Layout PPTX | Images | Position | % Largeur | Recommandation Marp |
|-------|-------|-------------|--------|----------|-----------|---------------------|
| 36 | Exploration gloutonne | Title and Content | 2 | Empilées | ~35% chacune | Carte + graphe empilés |
| 37 | Heuristiques admissibles et consistantes | Title and Content | 1 | Droite | ~40% | `columns: 2` gauche 60% texte, droite 40% image |
| 39 | Caractéristiques de A* | Title and Content | 1 | Droite | ~40% | `columns: 2` gauche 60% texte, droite 40% image |
| 43 | Algorithmes d'exploration locale | Title and Content | 1 | Droite | ~35% | `columns: 2` gauche 65% texte, droite 35% image |
| 44 | Paysage de l'espace des états | Title and Content | 1 | Droite | ~40% | `columns: 2` gauche 60% texte, droite 40% image |
| 45 | Exploration par escalade (HCS) | Title and Content | 3 | Droite empilées | ~30% chacune | 3 graphes empilés à droite |
| 46 | Exploration par recuit simulé (SA) | Title and Content | 1 | Droite | ~35% | `columns: 2` gauche 65% texte, droite 35% image |
| 48 | Algorithmes génétiques (GAs) | Title and Content | 1 | Droite | ~35% | `columns: 2` gauche 65% texte, droite 35% image |
| 49 | Algorithme génétique pour les 8 reines | Title and Content | 2 | Empilées | ~35% chacune | Deux schémas empilés |
| 51 | Exploration locale d'espaces continus | Title and Content | 1 | Droite | ~35% | `columns: 2` gauche 65% texte, droite 35% image |
| 52 | Exploration avec actions non déterministes | Title and Content | 1 | Droite | ~40% | `columns: 2` gauche 60% texte, droite 40% image |
| 53 | Exploration avec observations partielles | Title and Content | 1 | Droite | ~40% | `columns: 2` gauche 60% texte, droite 40% image |
| 54 | Exploration en ligne | Title and Content | 1 | Droite | ~35% | `columns: 2` gauche 65% texte, droite 35% image |

### Section 4: Jeux (Slides 57-68)

| Slide | Titre | Layout PPTX | Images | Position | % Largeur | Recommandation Marp |
|-------|-------|-------------|--------|----------|-----------|---------------------|
| 59 | Arbre de jeu | Title and Content | 1 | Centrée | ~50% | Diagramme centré |
| 60 | Minimax | Title and Content | 1 | Centrée | ~60% | Grand arbre centré |
| 61 | Algorithme Minimax | Title and Content | 1 | Droite | ~40% | `columns: 2` gauche 60% texte, droite 40% image |
| 62 | Elagage Alpha-Bêta | Title and Content | 1 | Centrée | ~65% | Grand diagramme alpha-bêta |
| 65 | Exploration d'arbre de Monte-Carlo | Title and Content | 1 | Droite | ~40% | `columns: 2` gauche 60% texte, droite 40% image |
| 66 | Classes de Jeux complexes | Title and Content | 3 | Empilées | ~30% chacune | 3 captures d'écran empilées |

### Section 5: CSPs (Slides 69-93)

| Slide | Titre | Layout PPTX | Images | Position | % Largeur | Recommandation Marp |
|-------|-------|-------------|--------|----------|-----------|---------------------|
| 70 | Problèmes à satisfaction de contraintes (CSPs) | Title and Content | 1 | Droite | ~40% | `columns: 2` gauche 60% texte, droite 40% image |
| 71 | Exemple: coloration de carte | Title and Content | 1 | Droite | ~40% | `columns: 2` gauche 60% texte, droite 40% image |
| 72 | Solutions d'un CSP | Title and Content | 1 | Droite | ~35% | `columns: 2` gauche 65% texte, droite 35% image |
| 75 | Graphe de contraintes | Title and Content | 1 | Droite | ~40% | `columns: 2` gauche 60% texte, droite 40% image |
| 76 | Types de contraintes | Title and Content | 1 | Droite | ~35% | `columns: 2` gauche 65% texte, droite 35% image |
| 81 | Exploration avec backtracking des CSPs | Title and Content | 1 | Centrée | ~60% | Arbre de backtrack |
| 82 | Ordre des variables et des valeurs | Two Content | 3 | Droite | ~35% chacune | **Layout Two Content spécial** |
| 83 | Vérification avant et examen en amont | Title and Content | 1 | Droite | ~40% | `columns: 2` gauche 60% texte, droite 40% image |
| 84 | Exploration locale pour les CSPs | Two Content | 0 | - | - | **Layout Two Content sans image** |
| 85 | Structure des problèmes | Title and Content | 2 | Empilées | ~35% chacune | Deux diagrammes empilés |

---

## Patterns Marp Recommandés

### Pattern 1: Standard Texte + Image (35 slides)

```markdown
---
<!-- _class: two-cols -->
# Titre de la slide

Colonne gauche - Texte/liste:

- Point 1
- Point 2
- Point 3

<div class="right">

![Image](path/to/image.png)

</div>
```

**Ratios typiques**:
- Texte 60-65%, Image 35-40%
- Variante: Texte 55%, Image 45% pour diagrammes complexes

### Pattern 2: Image Centrée (7 slides)

Pour les slides avec grand diagramme centré (slides 17, 29, 59, 60, 62, 81):

```markdown
---
# Titre

<br>

![Diagramme](path/to/image.png)

*Note explicative si nécessaire*
```

### Pattern 3: Deux Images Empilées (5 slides)

Slides 19, 22, 36, 49 avec deux images:

```markdown
---
<!-- _class: two-cols -->
# Titre

Texte introductif...

<div class="right">

![Image 1](path1.png)
![Image 2](path2.png)

</div>
```

### Pattern 4: Trois Images (2 slides)

Slides 45 et 66 avec 3 images:

```markdown
---
<!-- _class: two-cols -->
# Titre

Description...

<div class="right">

![Image 1](path1.png)
![Image 2](path2.png)
![Image 3](path3.png)

</div>
```

### Pattern 5: Tableau Large (1 slide)

Slide 29 avec tableau de comparaison:

```markdown
---
# Résumé Exploration non informée

| Stratégie | Complétude | Optimalité | Temps | Espace |
|-----------|------------|------------|-------|--------|
| BFS | Oui | Oui | O(b^d) | O(b^d) |
| ...
```

### Pattern 6: Two Content (2 slides)

Slides 82 et 84 utilisent le layout Two Content de PPTX:

```markdown
---
<!-- _class: two-cols -->
# Titre

**Colonne 1**

Texte de la colonne 1...

**Colonne 2**

Texte de la colonne 2...

<div class="right">

![Image](path.png)

</div>
```

---

## Problèmes Potentiels Décelés

### 1. Slides avec fort débordement texte

| Slide | Problème | Solution |
|-------|----------|----------|
| 9 | 113 mots - texte dense | Fractionner en 2 slides |
| 25 | 115 mots - liste longue | Simplifier ou split |
| 38 | 100 mots - définitions | Extraire code/exemples |
| 42 | 125 mots - nombreux points | Split en 2 slides |
| 63 | 148 mots - très dense | Fractionner obligatoire |
| 76 | 128 mots - contraintes | Split en 2 slides |
| 78 | 92 mots - formulation | Simplifier |
| 82 | 100 mots + 3 images | **Layout Two Content** |
| 84 | 132 mots - exploration locale | Split ou simplifier |
| 85 | 154 mots - structure | **Très dense** - split |

### 2. Slides avec contenu mixte complexe

- **Slide 19** (Infrastructure: Etats vs Noeuds): 2 images + texte dense
- **Slide 45** (Exploration par escalade): 3 images empilées
- **Slide 66** (Classes de Jeux complexes): 3 images empilées

### 3. Images très larges

- **Slide 29**: Tableau de comparaison (~80% de largeur)
- **Slide 60**: Arbre Minimax (~60% centré)
- **Slide 62**: Alpha-Bêta (~65% centré)
- **Slide 81**: Backtracking (~60% centré)

---

## Recommandations de Migration Marp

### 1. CSS Layouts

```css
/* two-cols layout pour la majorité des slides */
.slide.two-cols {
  display: grid;
  grid-template-columns: 60% 40%;
  gap: 1rem;
}

.slide.two-cols .right {
  display: flex;
  flex-direction: column;
  justify-content: center;
}

/* Variant pour images plus larges */
.slide.two-cols.wide-img {
  grid-template-columns: 55% 45%;
}

/* Layout pour image centrée */
.slide.centered-img {
  text-align: center;
}

.slide.centered-img img {
  max-width: 90%;
  height: auto;
}
```

### 2. Stratégie de conversion

1. **Slides texte simple (51 slides)**: Conversion directe, pas de layout spécial
2. **Slides texte + 1 image (35 slides)**: Utiliser `two-cols` par défaut
3. **Slides avec 2+ images (7 slides)**: Adapter le layout ou créer des slides séparées
4. **Slides très denses (10 slides)**: Fractionner en plusieurs slides

### 3. Images à extraire

Toutes les images sont déjà extraites dans `extracted/images/` avec le format `slide_XX_img_YYY.png`.

---

## Statistiques Finales

| Métrique | Valeur |
|----------|-------|
| Total slides | 93 |
| Slides avec images | 42 (45%) |
| Slides texte-only | 51 (55%) |
| Layout Title and Content | 90 (97%) |
| Layout Title Slide | 2 (2%) |
| Layout Two Content | 1 (1%) |
| Images totales | 56 |
| Moyenne images/slide avec image | 1.33 |
| Slides à densité élevée (>100 mots) | 10 (11%) |

---

## Fichiers de Référence

- **Inventory JSON**: `extracted/inventory.json`
- **Rendus PNG**: `extracted/renders/slide_XX.png`
- **Images extraites**: `extracted/images/slide_XX_img_YYY.png`
- **Contenu markdown**: `extracted/content.md`
