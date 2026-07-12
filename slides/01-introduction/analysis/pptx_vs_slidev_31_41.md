# Comparaison PPTX vs Slidev - Slides 31-41

**Date**: 2026-03-25
**Deck**: 01-introduction
**Slides analysées**: 31-41 (11 slides)

---

## Synthèse des problèmes

### Problèmes critiques (à corriger)

| Slide | Problème | Sévérité |
|-------|----------|----------|
| 34 | Liste des 5 types d'agents non visible sur image-overlay | CRITIQUE |
| 35 | Image img_033.png manquante à droite | CRITIQUE |
| 36 | Image img_036.png manquante à droite | CRITIQUE |

### Problèmes mineurs

| Slide | Problème | Sévérité |
|-------|----------|----------|
| 32-33 | Contenu divisé sur 2 slides au lieu de 1 | MINEUR |

---

## Analyse détaillée par slide

### Slide 31 - Environnements de tâche: exemples

**Statut**: ✅ CORRECT

**Layout PPTX**: Tableau PEAS centré
**Layout Slidev**: Image centrée img_028.png

**Correspondance**: IDENTICAL - Le tableau est affiché comme une image centrée dans les deux versions.

---

### Slide 32 - Types d'environnement

**Statut**: ⚠️ MODIFIÉ (acceptable)

**Layout PPTX**: Liste complète des 8 types sur UNE slide
**Layout Slidev**: Liste divisée sur DEUX slides (32 et 33)

**Contenu PPTX** (slide 32 unique):
- Complètement vs partiellement observable
- Déterministe vs stochastique
- Episodique vs séquentiel
- Statique vs Dynamique
- Discret vs continu
- Agent simple vs multiagent
- Connu vs inconnu
- Mention "Monde réel → cas complexes"

**Contenu Slidev**:
- Slide 32: 4 premiers types seulement
- Slide 33: 4 derniers types avec v-click

**Recommandation**:
- Option A (recommandée): Garder la division en 2 slides pour améliorer la lisibilité
- Option B: Fusionner pour correspondre exactement au PPTX

---

### Slide 33 - Types d'environnement: exemples

**Statut**: ✅ CORRECT

**Layout PPTX**: Tableau d'exemples
**Layout Slidev**: Image centrée img_029.png

**Correspondance**: IDENTICAL

---

### Slide 34 - Types d'agents

**Statut**: ❌ CRITIQUE - Contenu manquant

**Layout PPTX**:
- Titre "Types d'agents"
- Formule: "f(agent) = Architecture physique + Programme"
- Paragraphe d'intro sur la table percepts→action
- **Liste des 5 types d'agents**:
  1. Agent réflexe
  2. Agent réflexe fondés sur un modèle
  3. Agent fondé sur des buts
  4. Agent fondé sur l'utilité
  5. + Agent apprenant

**Layout Slidev actuel**:
```markdown
---
layout: image-overlay
image: ./images/img_030.png
---

# Types d'agents

**f(agent) = Architecture physique + Programme**

Un agent naif pourrait stocker une table "percepts → action", mais cette approche est impraticable : la table serait gigantesque et impossible a construire.

**Cinq architectures d'agents, par ordre de généralité :**

1. Agent réflexe simple
2. Agent réflexe fondé sur un modele
3. Agent fonde sur des buts
4. Agent fonde sur l'utilite
5. Agent capable d'apprentissage
```

**Problème**: Le texte est bien présent dans le markdown, mais le layout image-overlay avec img_030.png masque probablement la liste des 5 types.

**Correction nécessaire**:
```markdown
---
layout: two-cols
---

# Types d'agents

**f(agent) = Architecture physique + Programme**

Un agent naif pourrait stocker une table "percepts → action", mais cette approche est impraticable.

**Cinq architectures d'agents** :

1. Agent réflexe simple
2. Agent réflexe fondé sur un modele
3. Agent fonde sur des buts
4. Agent fonde sur l'utilite
5. Agent capable d'apprentissage

::right::

<img src="./images/img_030.png" width="500">
```

---

### Slide 35 - Agent réflexe

**Statut**: ❌ CRITIQUE - Image manquante

**Layout PPTX**:
- Colonne gauche: Texte (Caractéristiques + Exemples)
- Colonne droite: **3 images** empilées

**Layout Slidev actuel**:
```markdown
---
layout: two-cols
---

# Agent réflexe

**Caracteristiques:**
- Pas de mémoire
- Percepts courants
- Regles Conditions / Actions

**Exemples:**
<div v-click="2">
- Intelligence animale
</div>
- Béhaviorisme
- Vie artificielle
- Automates cellulaires

<img src="./images/img_033.png" width="80">

::right::

<img src="./images/img_031.png" width="420">
<img src="./images/img_032.png" width="350">
```

**Problème**:
- img_033.png est dans la colonne GAUCHE (dans le flux de texte)
- PPTX montre 3 images à DROITE

**Correction nécessaire**:
```markdown
---
layout: two-cols
---

# Agent réflexe

**Caracteristiques:**
- Pas de mémoire
- Percepts courants
- Regles Conditions / Actions

**Exemples:**
<div v-click="2">
- Intelligence animale
</div>
- Béhaviorisme
- Vie artificielle
- Automates cellulaires

::right::

<img src="./images/img_031.png" width="420">
<img src="./images/img_032.png" width="350">
<img src="./images/img_033.png" width="300">
```

---

### Slide 36 - Agent réflexe fondé sur un modèle

**Statut**: ❌ CRITIQUE - Image manquante

**Layout PPTX**:
- Colonne gauche: Texte (Caractéristiques + Exemple Subsomption)
- Colonne droite: **3 images** empilées

**Layout Slidev actuel**:
```markdown
---
layout: two-cols
---

# Agent réflexe fondé sur un modele

**Caracteristiques:**
<div v-click="1">
- État du monde
</div>
- Historique des percepts
- Mémoire du changement

**Exemple: Subsomption (Brooks)**
- Modele non representatif
- Comportements simples
- Couches d'automates
- Emergence

<img src="./images/img_036.png" width="80">

::right::

<img src="./images/img_034.png" width="420">
<img src="./images/img_035.png" width="350">
```

**Problème**:
- img_036.png est dans la colonne GAUCHE (dans le flux de texte)
- PPTX montre 3 images à DROITE

**Correction nécessaire**:
```markdown
---
layout: two-cols
---

# Agent réflexe fondé sur un modele

**Caracteristiques:**
<div v-click="1">
- État du monde
</div>
- Historique des percepts
- Mémoire du changement

**Exemple: Subsomption (Brooks)**
- Modele non representatif
- Comportements simples
- Couches d'automates
- Emergence

::right::

<img src="./images/img_034.png" width="420">
<img src="./images/img_035.png" width="350">
<img src="./images/img_036.png" width="300">
```

---

### Slide 37 - Agent fondé sur des buts

**Statut**: ✅ CORRECT

**Layout PPTX**: Texte + diagramme
**Layout Slidev**: image-overlay avec img_037.png

**Correspondance**: GOOD - Le texte est bien visible sur l'image de fond.

---

### Slide 38 - Agent fondé sur l'utilité

**Statut**: ✅ CORRECT

**Layout PPTX**: Texte à gauche, diagramme à droite
**Layout Slidev**: image-overlay avec img_038.png

**Correspondance**: GOOD - Le texte est bien visible sur l'image de fond.

---

### Slide 39 - Agent capable d'apprentissage

**Statut**: ✅ CORRECT

**Layout PPTX**: Texte à gauche, diagramme à droite
**Layout Slidev**: image-overlay avec img_039.png

**Correspondance**: GOOD - Le texte est bien visible sur l'image de fond.

---

### Slide 40 - Fonctionnement interne des agents

**Statut**: ✅ CORRECT

**Layout PPTX**: Texte à gauche, diagramme pyramide à droite
**Layout Slidev**: image-overlay avec img_040.png

**Correspondance**: GOOD - Le texte est bien visible sur l'image de fond.

---

### Slide 41 - Résumé

**Statut**: ⚠️ À vérifier

**Layout PPTX**: Liste structurée de résumé
**Layout Slidev**: Liste à puces

**Note**: Cette slide nécessite une vérification visuelle pour confirmer que la structure hiérarchique du PPTX est bien respectée.

---

## Actions requises

### Corrections immédiates (slides.md)

1. **Slide 34**: Changer image-overlay en two-cols et déplacer img_030.png à droite
2. **Slide 35**: Déplacer img_033.png de la colonne gauche vers la colonne droite
3. **Slide 36**: Déplacer img_036.png de la colonne gauche vers la colonne droite

### Optionnel

1. **Slides 32-33**: Décider si l'on fusionne ou si l'on garde la division en 2 slides

---

## Fichier de corrections

Voir slides/01-introduction/slides.md lignes:
- Slide 34: lignes 546-564
- Slide 35: lignes 566-595
- Slide 36: lignes 597-625
