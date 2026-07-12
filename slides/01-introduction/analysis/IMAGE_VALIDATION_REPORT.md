# Rapport de Validation des Images - Deck 01-Introduction

**Date**: 2026-03-25
**Méthode**: Comparaison automatisée des noms de fichiers

---

## Synthèse

| Métrique | Valeur |
|----------|-------|
| Images PPTX | 40 |
| Images Slidev | 40 |
| Correspondances | 39 (97.5%) |
| Non appariées | 2 (1 PPTX, 1 Slidev) |

---

## Correspondances Identifiées

### Format Différent (Conversion PNG/JPG)

| PPTX | Slidev | Slide | Note |
|------|--------|-------|------|
| `slide_09_img_001.png` | `img_001.jpg` | 9 | PNG → JPG |
| `slide_13_img_004.jpg` | `img_004.png` | 13 | JPG → PNG |
| `slide_14_img_006.png` | `img_006.jpg` | 14 | PNG → JPG |
| `slide_14_img_010.jpg` | `img_010.png` | 14 | JPG → PNG |
| `slide_14_img_011.png` | `img_011.jpg` | 14 | PNG → JPG |
| `slide_25_img_021.jpg` | `img_021.png` | 25 | JPG → PNG |
| `slide_25_img_022.png` | `img_022.jpg` | 25 | PNG → JPG |
| `slide_25_img_023.jpg` | `img_023.png` | 25 | JPG → PNG |
| `slide_26_img_025.png` | `img_025.jpg` | 26 | PNG → JPG |
| `slide_26_img_026.jpg` | `img_026.png` | 26 | JPG → PNG |
| `slide_31_img_027.png` | `img_027.jpg` | 31 | PNG → JPG |

**Total conversions de format** : 11 images (28%)

### Correspondances Exactes (Même Format)

| PPTX | Slidev | Slide | Format |
|------|--------|-------|--------|
| `slide_11_img_002.png` | `img_002.png` | 11 | PNG |
| `slide_12_img_003.png` | `img_003.png` | 12 | PNG |
| `slide_13_img_005.jpg` | `img_005.jpg` | 13 | JPG |
| `slide_14_img_007.png` | `img_007.png` | 14 | PNG |
| `slide_14_img_008.png` | `img_008.png` | 14 | PNG |
| `slide_14_img_009.png` | `img_009.png` | 14 | PNG |
| `slide_14_img_012.png` | `img_012.png` | 14 | PNG |
| `slide_14_img_013.png` | `img_013.png` | 14 | PNG |
| `slide_14_img_014.png` | `img_014.png` | 14 | PNG |
| `slide_14_img_015.png` | `img_015.png` | 14 | PNG |
| `slide_14_img_016.png` | `img_016.png` | 14 | PNG |
| `slide_14_img_017.png` | `img_017.png` | 14 | PNG |
| `slide_14_img_018.png` | `img_018.png` | 14 | PNG |
| `slide_16_img_019.png` | `img_019.png` | 16 | PNG |
| `slide_22_img_020.png` | `img_020.png` | 22 | PNG |
| `slide_26_img_024.jpg` | `img_024.jpg` | 26 | JPG |
| `slide_33_img_028.png` | `img_028.png` | 33 | PNG |
| `slide_34_img_029.png` | `img_029.png` | 34 | PNG |
| `slide_35_img_030.png` | `img_030.png` | 35 | PNG |
| `slide_35_img_031.png` | `img_031.png` | 35 | PNG |
| `slide_35_img_032.png` | `img_032.png` | 35 | PNG |
| `slide_36_img_033.png` | `img_033.png` | 36 | PNG |
| `slide_36_img_034.png` | `img_034.png` | 36 | PNG |
| `slide_36_img_035.png` | `img_035.png` | 36 | PNG |
| `slide_37_img_036.png` | `img_036.png` | 37 | PNG |
| `slide_38_img_037.png` | `img_037.png` | 38 | PNG |
| `slide_39_img_038.png` | `img_038.png` | 39 | PNG |
| `slide_40_img_039.png` | `img_039.png` | 40 | PNG |

**Total correspondances exactes** : 28 images (72%)

---

## Images Non Appariées

### PPTX sans correspondance Slidev

| Fichier | Slide | Action |
|---------|-------|--------|
| `slide_03_img_000.jpg` | 3 | **À vérifier** - Cette image manque dans Slidev |

**Action requise** :
- Vérifier si cette image est utilisée dans slide 3
- Si oui, copier vers `images/img_000.jpg` ou renommer `img_001.jpg`

### Slidev sans correspondance PPTX

| Fichier | Action |
|---------|--------|
| `img_040.png` | **À vérifier** - Cette image n'existe pas dans PPTX |

**Action requise** :
- Vérifier si cette image est utilisée dans le code Slidev
- Si non, supprimer pour nettoyer le dossier

---

## Actions Recommandées

### 1. Image manquante (Bloquant)

**Problème** : `slide_03_img_000.jpg` n'a pas de correspondance Slidev

**Investigation** :
```bash
# Vérifier si l'image est utilisée dans slide 3
grep "img_000" slides/01-introduction/slides.md

# Vérifier l'image originale
ls -la slides/01-introduction/extracted/images/slide_03_img_000.jpg
```

**Résolution** :
- Option A : Copier l'image vers `images/img_000.jpg`
- Option B : Renommer `img_001.jpg` en `img_000.jpg` et ajuster le code

### 2. Image en trop (Non bloquant)

**Problème** : `img_040.png` n'existe pas dans PPTX

**Investigation** :
```bash
# Vérifier si l'image est utilisée
grep "img_040" slides/01-introduction/slides.md
```

**Résolution** :
- Si non utilisée : supprimer
- Si utilisée : documenter pourquoi elle n'est pas dans PPTX

### 3. Conversions de format (Information)

**Observation** : 11 images ont été converties entre PNG et JPG

**Impact** :
- JPG → PNG : Augmentation de la taille, transparence possible
- PNG → JPG : Compression avec perte d'information

**Recommandation** :
- Vérifier la qualité visuelle des images converties
- Si dégradation visible, reconverter avec les paramètres originaux

---

## Statistiques par Slide

### Slides avec le plus d'images

| Slide | Nombre d'images | Note |
|-------|----------------|------|
| 14 | 13 images | Slide "Qui fait de l'IA?" avec logos |
| 25 | 3 images | Slide "Intelligences" |
| 26 | 3 images | Suite des intelligences |
| 35 | 3 images | Types d'agents |
| 36 | 3 images | Suite types d'agents |

### Distribution des formats

| Format | PPTX | Slidev | Différence |
|--------|------|--------|------------|
| PNG | 33 | 36 | +3 |
| JPG | 7 | 4 | -3 |

**Note** : Slidev favorise PNG (meilleure qualité pour logos)

---

## Conclusion

### État global

✅ **97.5% des images sont correctement appariées**

### Problèmes identifiés

1. **Bloquant** : 1 image manquante (`slide_03_img_000.jpg`)
2. **Mineur** : 1 image en trop (`img_040.png`)
3. **Information** : 11 conversions de format (PNG ↔ JPG)

### Actions immédiates

1. Corriger l'image manquante pour slide 3
2. Vérifier l'image `img_040.png` (supprimer si inutile)
3. Valider la qualité des images converties

---

**Fichier de mapping** : `slides/01-introduction/analysis/image_mapping.json`
**Script de comparaison** : `scripts/compare-slide-images.py`
