# Corrections prioritaires PPTX → Slidev

## Corrections immédiates (blockers)

### 1. Grille de logos (Slide 14 - "Qui fait de l'IA ?")

**Problème:** Les 13 logos ne s'affichent pas en grille 4x4 comme dans le PPTX.

**Correction:** Ajouter dans `slides/theme-ia101.css`:

```css
.image-grid {
  display: grid;
  grid-template-columns: repeat(4, 1fr);
  gap: 12px;
  margin-top: 20px;
}

.image-grid img {
  max-width: 100%;
  height: auto;
  object-fit: contain;
  max-height: 60px;
}
```

### 2. Tableau coloré (Slide 10 - "Quatre visions de l'IA")

**Problème:** Le tableau 2x2 avec cellules marron/orange est en markdown standard.

**Correction:** Créer un composant `components/ColoredTable.vue`:

```vue
<template>
  <div class="colored-table">
    <table>
      <tr>
        <td class="brown-cell">Penser comme l'homme</td>
        <td class="brown-cell">Penser de façon rationnelle</td>
      </tr>
      <tr>
        <td class="brown-cell">Agir comme l'homme</td>
        <td class="brown-cell">Agir de façon rationnelle</td>
      </tr>
    </table>
  </div>
</template>

<style scoped>
.brown-cell {
  background-color: #c17b5f;
  color: white;
  padding: 16px;
  text-align: center;
  font-weight: bold;
}
</style>
```

Puis dans slides.md:
```markdown
# Quatre visions de l'IA

<ColoredTable />
```

### 3. Layout "Intelligences" (Slide 25)

**Problème:** Le layout complexe avec sections imbriquées dans un rectangle rouge-orangé n'est pas reproduit.

**Correction:** Créer un composant `components/IntelligenceTypes.vue` ou diviser en 4 slides séparées avec transitions.

**Option simple** - Diviser en slides:
- Slide 1: Procédurale
- Slide 2: Exploratoire
- Slide 3: Symbolique
- Slide 4: Probabiliste

### 4. Tableaux complexes (Slides 31 et 33)

**Problème:** Les tableaux PPTX sont convertis en images qui peuvent être de mauvaise qualité.

**Vérification:** Ouvrir `img_028.png` et `img_029.png` pour vérifier la lisibilité. Si illisibles, recréer en markdown.

**Pour slide 31** (5 colonnes):
```markdown
| Type d'agent | Mesure de performance | Environnement | Effecteurs | Capteurs |
|:-------------|:---------------------|:--------------|:-----------|:---------|
| Diagnostic médical | Santé du patient | Patient, hôpital | Affichage | Symptômes |
| Analyse satellites | Catégories correctes | Images satellites | Affichage | Pixels |
| Robot pièces | % correct | Banque de pièces | Bras, pince | Caméra |
| Contrôleur raffinerie | Pureté, rendement | Raffinerie | Valves, pompes | Temp., pression |
| Répétiteur anglais | Score étudiants | Étudiants | Exercices | Clavier |
```

### 5. Chronologie en 2 colonnes (Slide 12)

**Problème:** La liste chronologique PPTX est en 2 colonnes (années à gauche, descriptions à droite).

**Correction:** Utiliser `layout: two-cols`:

```markdown
layout: two-cols
# Histoire succincte

**1943**
McCulloch & Pitts: le cerveau comme un circuit logique

**1950**
Turing "Computing Machinery and Intelligence"

**1956**
Rencontre de Dartmouth : "Artificial Intelligence"

::right::

**1950-70**
Enthousiasme des débuts

**1950s**
Premiers programmes: Samuel (jeu de dames), Newell & Simon (théoricien logique)

**1965**
Robinson: Algorithme complet de raisonnement

**1970s**
L'IA découvre la complexité calculatoire
```

## Corrections secondaires (améliorations)

### 6. Formules mathématiques

Pour les formules comme `f: P* → A`, utiliser MathJax:

```markdown
$$f: \mathcal{P}^* \to \mathcal{A}$$
```

### 7. Images multiples (Slide 13)

Pour afficher 2 images côte à côte:

```markdown
<div class="image-row">
  <img src="./images/img_005.jpg" style="width: 48%; margin-right: 2%">
  <img src="./images/img_006.jpg" style="width: 48%">
</div>
```

Ou avec v-click pour les faire apparaître séquentiellement:

```markdown
<img src="./images/img_005.jpg" style="width: 45%">
<div v-click="1">
  <img src="./images/img_006.jpg" style="width: 45%; margin-top: 8px">
</div>
```

### 8. Vérifier les images manquantes

Créer un script pour vérifier que toutes les images référencées existent:

```bash
#!/bin/bash
cd slides/01-introduction/images
for img in img_{001..040}.{png,jpg}; do
  if [ ! -f "$img" ]; then
    echo "MANQUANT: $img"
  fi
done
```

## Checklist de validation

- [ ] Grille de logos (slide 14) s'affiche correctement
- [ ] Tableau coloré (slide 10) a les bonnes couleurs
- [ ] Layout "Intelligences" (slides 27-28) est lisible
- [ ] Tableaux slides 31 et 33 sont lisibles ou recréés
- [ ] Chronologie slide 12 est en 2 colonnes
- [ ] Toutes les images référencées existent
- [ ] Formules mathématiques s'affichent correctement
- [ ] Animations v-click sont dans le bon ordre
