# Corrections Immédiates - Deck 01-Introduction

**Date**: 2026-03-25
**Priorité** : Critique
**Statut** : À faire avant validation

---

## Correction 1 : Image Manquante (Bloquant)

### Problème

L'image `slide_03_img_000.jpg` du PPTX n'a pas de correspondance dans Slidev.

### Localisation

**Slide 3 - Sommaire** :
- PPTX utilise une image (probablement `Picture6.jpg` dans le contenu original)
- Slidev référence `./images/img_001.jpg` avec le layout `image-overlay`

### Investigation

```bash
# Vérifier l'image originale
ls -la slides/01-introduction/extracted/images/slide_03_img_000.jpg

# Vérifier ce qui est référencé dans Slidev
grep -A5 "^layout: image-overlay" slides/01-introduction/slides.md | head -10
```

### Solution

**Option A : Créer le fichier img_000.jpg**

```bash
cp slides/01-introduction/extracted/images/slide_03_img_000.jpg \
   slides/01-introduction/images/img_000.jpg
```

**Option B : Renommer img_001.jpg en img_000.jpg**

```bash
# Si img_001.jpg n'est pas utilisé ailleurs
mv slides/01-introduction/images/img_001.jpg \
   slides/01-introduction/images/img_000.jpg

# Puis mettre à jour slides.md
sed -i 's/img_001/img_000/g' slides/01-introduction/slides.md
```

**Option C : Copier depuis img_001.jpg**

```bash
# Si img_001.jpg est la même image
cp slides/01-introduction/images/img_001.jpg \
   slides/01-introduction/images/img_000.jpg
```

### Validation

Après correction, vérifier :
```bash
ls -la slides/01-introduction/images/img_000.jpg

# Redémarrer le serveur Slidev
cd slides/01-introduction
npm run dev

# Ouvrir http://localhost:3031#3 et vérifier que l'image s'affiche
```

---

## Correction 2 : Image en Trop (Mineur)

### Problème

L'image `img_040.png` existe dans Slidev mais n'a pas de correspondance PPTX.

### Investigation

```bash
# Vérifier si l'image est utilisée
grep -r "img_040" slides/01-introduction/slides.md

# Vérifier l'image
ls -la slides/01-introduction/images/img_040.png
```

### Solution

**Si l'image n'est pas utilisée** :
```bash
rm slides/01-introduction/images/img_040.png
```

**Si l'image est utilisée** :
- Documenter pourquoi elle n'est pas dans le PPTX
- Vérifier si c'est une erreur d'indexation

---

## Correction 3 : Composant ColoredTable (Moyen)

### Problème

Le composant `<ColoredTable />` est utilisé dans slide 10 mais nécessite du CSS.

### Investigation

Vérifier que le CSS existe dans le thème :
```bash
grep -r "colored-table" slides/theme-ia101/
```

### Solution

Si le CSS n'existe pas, l'ajouter à `slides/theme-ia101/styles/index.css` :

```css
.colored-table-container {
  display: flex;
  justify-content: center;
  margin: 2rem 0;
}

.colored-table {
  border-collapse: collapse;
  width: 100%;
  max-width: 800px;
}

.colored-table td {
  border: 2px solid #333;
  padding: 1rem;
  text-align: center;
  font-size: 1.1rem;
}

.header-cell {
  background-color: #2c3e50;
  color: white;
  font-weight: bold;
}

.content-cell {
  background-color: #ecf0f1;
  color: #2c3e50;
}

.content-cell.highlight {
  background-color: #e74c3c;
  color: white;
  font-weight: bold;
}
```

### Validation

```bash
cd slides/01-introduction
npm run dev

# Ouvrir http://localhost:3031#10 et vérifier :
# - Le tableau est centré
# - Les en-têtes sont sur fond bleu foncé
# - Les cellules sont sur fond clair
# - "Agents rationnels" est sur fond rouge (highlight)
```

---

## Correction 4 : Tests des Layouts (Moyen)

### Layouts à tester

1. **layout: cover** (slide 1)
2. **layout: section** (slide 7)
3. **layout: image-overlay** (slide 3, 11+)

### Script de test

```bash
cd slides/01-introduction

# Démarrer le serveur
npm run dev

# Dans le navigateur, naviguer vers :
# - http://localhost:3031#1  (cover)
# - http://localhost:3031#7  (section)
# - http://localhost:3031#3  (image-overlay)
# - http://localhost:3031#11 (image-overlay)
```

### Checklist de validation

#### Layout Cover (slide 1)
- [ ] Le titre est centré
- [ ] Le sous-titre est visible
- [ ] Les informations enseignant sont alignées
- [ ] Le fond de couleur est correct

#### Layout Section (slide 7)
- [ ] Le fond de couleur couvre toute la slide
- [ ] Le texte "Questions?" est visible
- [ ] Le contraste est suffisant
- [ ] La police est lisible

#### Layout Image-Overlay (slides 3, 11)
- [ ] L'image est en arrière-plan
- [ ] Le texte est superposé et lisible
- [ ] Le contraste est suffisant
- [ ] L'image n'est pas déformée

---

## Script de Validation Automatique

Créer `scripts/validate-slidev.sh` :

```bash
#!/bin/bash

echo "Validation Slidev - Deck 01-Introduction"
echo "=========================================="

# 1. Vérifier les images
echo ""
echo "1. Vérification des images..."
if [ -f "slides/01-introduction/images/img_000.jpg" ]; then
    echo "   ✓ img_000.jpg existe"
else
    echo "   ✗ img_000.jpg MANQUANT"
fi

if [ -f "slides/01-introduction/images/img_040.png" ]; then
    echo "   ⚠ img_040.png existe (devrait peut-être être supprimé)"
fi

# 2. Vérifier le CSS ColoredTable
echo ""
echo "2. Vérification du CSS ColoredTable..."
if grep -q "colored-table" slides/theme-ia101/styles/*.css; then
    echo "   ✓ CSS colored-table trouvé"
else
    echo "   ✗ CSS colored-table MANQUANT"
fi

# 3. Vérifier les layouts dans slides.md
echo ""
echo "3. Vérification des layouts..."
echo "   layout: cover utilisé $(grep -c 'layout: cover' slides/01-introduction/slides.md) fois"
echo "   layout: section utilisé $(grep -c 'layout: section' slides/01-introduction/slides.md) fois"
echo "   layout: image-overlay utilisé $(grep -c 'layout: image-overlay' slides/01-introduction/slides.md) fois"

# 4. Résumé
echo ""
echo "=========================================="
echo "Validation terminée"
echo "Lance 'npm run dev' pour tester visuellement"
```

---

## Ordre de Priorité

1. **Immédiat** : Corriger l'image manquante (img_000.jpg)
2. **Immédiat** : Ajouter le CSS ColoredTable
3. **Court terme** : Tester les layouts
4. **Court terme** : Supprimer img_040.png si inutile
5. **Moyen terme** : Tests de navigation complets

---

## Après Corrections

Une fois les corrections appliquées :

1. Relancer l'analyse de mapping des images
2. Vérifier visuellement les slides concernées
3. Mettre à jour les rapports d'analyse
4. Documenter les corrections appliquées

---

**Fichier de suivi** : `slides/01-introduction/analysis/IMMEDIATE_FIXES.md`
**Statut** : En attente de correction
