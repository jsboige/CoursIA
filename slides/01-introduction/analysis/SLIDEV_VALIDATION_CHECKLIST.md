# Slidev Validation Checklist - Deck 01-Introduction

**Date**: 2026-03-25
**Slides**: 1-10 analysées sur 43 totales
**Statut**: Analyse partielle terminée

---

## Actions Immédiates (Bloquantes)

### 1. Correspondance des Images

**Problème** : Les noms de fichiers image ne correspondent pas entre PPTX et Slidev

| Slide | PPTX | Slidev | Action |
|-------|------|--------|--------|
| 3 | `Picture6.jpg` | `img_001.jpg` | Vérifier équivalence |
| 9 | `Image1.jpg` | `img_002.png` | Vérifier équivalence |
| 11+ | À vérifier | `img_003.png`, `img_004.png`, `img_005.jpg` | Mapping complet |

**Commande pour lister les images** :
```bash
# Images PPTX
ls slides/01-introduction/extracted/images/

# Images Slidev
ls slides/01-introduction/images/
```

### 2. Validation du Composant ColoredTable

**Fichier** : Utilisé dans slide 10 (Quatre visions de l'IA)

**Vérifications** :
- [ ] Le composant est bien défini (compilé dans le build)
- [ ] Le CSS `.colored-table` est présent dans le thème
- [ ] Les classes `header-cell`, `content-cell`, `highlight` fonctionnent
- [ ] La cellule "Agents rationnels" est bien mise en évidence

**Test** : Ouvrir http://localhost:3031#10 et vérifier le rendu

### 3. Tests des Layouts Personnalisés

| Layout | Slide | Test |
|--------|-------|------|
| `cover` | 1 | [ ] Vérifier rendu titre, sous-titre, infos enseignant |
| `section` | 7 | [ ] Vérifier fond couleur, lisibilité texte |
| `image-overlay` | 3, 11+ | [ ] Vérifier position image, superposition texte |

---

## Actions Court Terme (Recommandées)

### 1. Tests de Navigation

```bash
cd slides/01-introduction
npm run dev
# Ouvrir http://localhost:3031
```

**Checklist** :
- [ ] Navigation clavier (ArrowRight, ArrowLeft)
- [ ] Animations fragments (v-click sur slide 3)
- [ ] Mode présentateur (touche p)
- [ ] Numérotation des slides
- [ ] Pagination

### 2. Export PDF

```bash
cd slides/01-introduction
npm run build
# PDF dans dist/
```

**Vérifications** :
- [ ] PDF généré sans erreurs
- [ ] Toutes les slides sont présentes
- [ ] Les images sont de bonne qualité
- [ ] Le texte est lisible

### 3. Comparaison Visuelle

**Méthode 1 - PDF côte à côte** :
```bash
# Ouvrir les PDF côte à côte
# - PPTX export : slides/01-introduction/modernized/01-introduction.pdf
# - Slidev export : slides/01-introduction/dist/01-introduction.pdf
```

**Méthode 2 - Captures d'écran** :
```bash
# Utiliser l'export PDF Slidev comme référence
# Comparer avec les renders PPTX dans modernized/renders/
```

---

## Résumé des Problèmes

### Critiques (Impact Élevé)

*Aucun problème critique identifié*

### Moyens (Impact Moyen)

1. **Correspondance des images** (slides 3, 9)
   - Noms de fichiers différents
   - Contenu à vérifier

2. **Composant ColoredTable** (slide 10)
   - Composant custom nécessitant CSS
   - Rendu à valider

### Faibles (Impact Faible)

1. **Layouts personnalisés** (slides 1, 7, 3+)
   - Dépendance au thème ia101
   - À tester mais non bloquant

2. **Découpage de contenu** (slide 5)
   - Objectifs du cours découpés en 2 slides
   - Restructuration acceptable

---

## Statistiques

| Métrique | Valeur |
|----------|-------|
| Slides analysées | 10 / 43 (23%) |
| Slides fidèles | 6 (60%) |
| Slides à vérifier | 4 (40%) |
| Problèmes bloquants | 0 |
| Problèmes moyens | 2 |
| Problèmes faibles | 2 |

---

## Prochaine Analyse

**Slides 11-20** à analyser :
- Slide 11: Les fondements de l'IA (layout: image-overlay)
- Slide 12: Histoire succincte (1/2)
- Slide 13: Histoire succincte (2/2)
- Slide 14: État de l'art (1/2)
- Slide 15: Qui fait de l'IA? (logos multiples)
- Slide 16: Dans la vie de tous les jours
- Slide 17: Test de Turing
- Slide 18-20: Sciences cognitives, Lois de la raison, Agents

**Focus** :
- Vérifier les images `img_003.png`, `img_004.png`, `img_005.jpg`
- Valider les layouts image-overlay
- Tester la gestion des logos multiples (slide 14)

---

## Commandes Utiles

```bash
# Démarrer le serveur de développement
cd slides/01-introduction
npm run dev

# Builder le PDF
npm run build

# Comparer les images
diff -q slides/01-introduction/extracted/images/ slides/01-introduction/images/

# Lister les slides dans le markdown
grep "^---$" slides/01-introduction/slides.md | wc -l

# Chercher les composants custom
grep "<[A-Z][a-zA-Z]*" slides/01-introduction/slides.md
```

---

**Documents de référence** :
- Analyse complète : `analysis/pptx_vs_slidev_analysis.md`
- Source PPTX : `modernized/renders/slide_*.png`
- Source Slidev : `slides.md`
- Thème : `theme-ia101/`
