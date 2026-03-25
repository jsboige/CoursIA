# Corrections appliquées - Slides 31-41

**Date**: 2026-03-25
**Deck**: 01-introduction
**Slides corrigées**: 34, 35, 36

---

## Résumé des corrections

### Slide 34 - Types d'agents ✅ CORRIGÉ

**Problème**: Layout `image-overlay` masquait la liste des 5 types d'agents

**Correction appliquée**:
```diff
---
-layout: image-overlay
-image: ./images/img_030.png
+layout: two-cols
 ---

 # Types d'agents

 **f(agent) = Architecture physique + Programme**

-Un agent naif pourrait stocker une table "percepts → action", mais cette approche est impraticable : la table serait gigantesque et impossible a construire.
+Un agent naif pourrait stocker une table "percepts → action", mais cette approche est impraticable.

 **Cinq architectures d'agents, par ordre de généralité :**

 1. Agent réflexe simple
 2. Agent réflexe fondé sur un modele
 3. Agent fonde sur des buts
 4. Agent fonde sur l'utilite
 5. Agent capable d'apprentissage
+
+::right::
+
+<img src="./images/img_030.png" width="500">
```

**Résultat**: La liste des 5 types est maintenant visible dans la colonne gauche, avec le diagramme dans la colonne droite.

---

### Slide 35 - Agent réflexe ✅ CORRIGÉ

**Problème**: L'image `img_033.png` était affichée dans la colonne gauche au lieu de la droite

**Correction appliquée**:
```diff
 **Exemples:**

 <div v-click="2">
 - Intelligence animale
 </div>
-- Béhaviorisme
-- Vie artificielle
-- Automates cellulaires
-
-<img src="./images/img_033.png" width="80">
+- Béhaviorisme
+- Vie artificielle
+- Automates cellulaires

 ::right::

 <img src="./images/img_031.png" width="420">
 <img src="./images/img_032.png" width="350">
+<img src="./images/img_033.png" width="300">
```

**Résultat**: Les 3 images (img_031, img_032, img_033) sont maintenant affichées dans la colonne droite, correspondant au layout PPTX.

---

### Slide 36 - Agent réflexe fondé sur un modèle ✅ CORRIGÉ

**Problème**: L'image `img_036.png` était affichée dans la colonne gauche au lieu de la droite

**Correction appliquée**:
```diff
 **Exemple: Subsomption (Brooks)**

 - Modele non representatif
 - Comportements simples
 - Couches d'automates
 - Emergence

-<img src="./images/img_036.png" width="80">

 ::right::

 <img src="./images/img_034.png" width="420">
 <img src="./images/img_035.png" width="350">
+<img src="./images/img_036.png" width="300">
```

**Résultat**: Les 3 images (img_034, img_035, img_036) sont maintenant affichées dans la colonne droite, correspondant au layout PPTX.

---

## Statut final des slides 31-41

| Slide | Titre | Statut | Action |
|-------|-------|--------|--------|
| 31 | Environnements de tâche: exemples | ✅ OK | Aucune |
| 32 | Types d'environnement (1/2) | ⚠️ MODIFIÉ | Acceptable (divisé en 2 slides) |
| 33 | Types d'environnement: exemples | ✅ OK | Aucune |
| 34 | Types d'agents | ✅ CORRIGÉ | Layout changé image-overlay → two-cols |
| 35 | Agent réflexe | ✅ CORRIGÉ | img_033.png déplacé gauche → droite |
| 36 | Agent réflexe fondé sur un modèle | ✅ CORRIGÉ | img_036.png déplacé gauche → droite |
| 37 | Agent fondé sur des buts | ✅ OK | Aucune |
| 38 | Agent fondé sur l'utilité | ✅ OK | Aucune |
| 39 | Agent capable d'apprentissage | ✅ OK | Aucune |
| 40 | Fonctionnement interne des agents | ✅ OK | Aucune |
| 41 | Résumé | ⚠️ À vérifier | Vérification visuelle recommandée |

---

## Actions restantes

### Optionnel
- **Slide 32-33**: Décider si l'on fusionne les 2 slides en 1 (comme le PPTX) ou si l'on garde la division actuelle (meilleure lisibilité)
- **Slide 41**: Vérification visuelle pour confirmer la structure hiérarchique

### Vérification
- Rafraîchir le navigateur Slidev (http://localhost:3031) pour voir les corrections
- Comparer visuellement avec les PPTX originaux dans `modernized/renders/`

---

## Fichiers modifiés

- `slides/01-introduction/slides.md` : 3 slides corrigées (34, 35, 36)
