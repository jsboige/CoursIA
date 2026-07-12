# Rapport de comparaison PPTX vs Slidev - Deck 01-Introduction

**Date:** 2026-02-26
**Deck:** 01-Introduction
**Slides PPTX:** 43
**Slides Slidev:** 53 (avec slides animées en multiples)

---

## Résumé exécutif

La conversion PPTX vers Slidev a réussi à préserver le contenu principal, mais plusieurs problèmes de layout et de fidélité ont été identifiés. Les principaux problèmes concernent:

1. **Layouts complexes non préservés** (tableaux, grilles de logos)
2. **Images manquantes ou mal positionnées**
3. **Texte déchet et artefacts de conversion**
4. **Animations intégrées avec v-click mais parfois mal ordonnées**

---

## Problèmes identifiés par slide

### Slide 03 - Sommaire (avec image livre)
**Problème:** Layout image-droite non préservé fidèlement
- **PPTX:** Image du livre Russell & Norvig à droite de la liste
- **Slidev:** Utilise `layout: image-right` mais l'image est positionnée en bas via YAML frontmatter
- **Correction:** Le layout semble correct, vérifier le rendu visuel

### Slide 10 - Quatre visions de l'IA
**Problème:** Tableau 2x2 avec cellules colorées
- **PPTX:** Tableau avec cellules de couleur marron/orange, texte en blanc
- **Slidev:** Tableau markdown standard sans style de couleur
- **Correction:** Ajouter des styles CSS personnalisés ou utiliser un composant pour reproduire les couleurs des cellules

```markdown
| Penser comme l'homme | Penser de façon rationnelle |
| --- | --- |
| Agir comme l'homme | Agir de façon rationnelle |
```

**Suggestion:** Créer un composant `ColoredTableCell.vue` ou utiliser des classes CSS inline.

### Slide 11 - Les fondements de l'IA
**Problème:** Format tabulaire perdu
- **PPTX:** Liste en deux colonnes avec des tabulations alignées
- **Slidev:** Liste markdown standard à puces
- **Correction:** Utiliser `layout: two-cols` ou un tableau markdown

**Suggestion:**
```markdown
layout: two-cols

**Philosophie**
Logique, méthodes de raisonnement, esprit physique, apprentissage, langage, raison

**Mathématiques**
Représentation formelle et preuve, algorithmes, calcul, (in)décidabilité, complexité, probabilités

::right::

**Économie**
Utilité, théorie des jeux, la décision, agents économiques rationnels

**Biologie**
Intelligence naturelle et animale
...
```

### Slide 12 - Histoire succincte
**Problème:** Format chronologique en deux colonnes
- **PPTX:** Années en rouge à gauche, descriptions en noir à droite
- **Slidev:** Liste à puces simple
- **Image:** Diagramme du Test de Turing présent sur le PPTX mais référence incorrecte (`![turing](Picture4.jpg)`)

**Correction:**
```markdown
layout: two-cols

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
Premiers programmes: Samuel (jeu de dames), Newell & Simon (théoricien logique), Gelernter (moteur géométrique), Lisp

**1965**
Robinson: Algorithme complet de raisonnement
...
```

**Image:** Corriger le chemin de l'image du diagramme Turing.

### Slide 13 - Etat de l'art
**Problème:** Deux images sur la slide
- **PPTX:** Deux images côte à côte ou superposées
- **Slidev:** Références image brisées (`![](Image10.jpg)` et `![http://image-net.org/index_files/logo.jpg](Picture16.jpg)`)

**Correction:**
```markdown
<div class="image-row">
<img src="./images/img_005.jpg" width="45%">
<img src="./images/img_006.jpg" width="45%">
</div>
```

Ou utiliser v-click pour les faire apparaître séquentiellement:
```markdown
<div v-click="1"><img src="./images/img_005.jpg"></div>
<div v-click="2"><img src="./images/img_006.jpg"></div>
```

### Slide 14 - Qui fait de l'IA (13 logos)
**Problème majeur:** Grille de 13 logos non reproduite fidèlement
- **PPTX:** 13 logos disposés en grille (4x4 avec dernière ligne incomplète)
- **Slidev:** `<div class="image-grid">` avec 13 images mais le layout CSS n'est pas défini dans le thème

**Layout PPTX observé:**
- Ligne 1: 4 logos (CMU, MIT, Berkeley, Stanford/UT Austin)
- Ligne 2: 4 logos (Google, Facebook, Honeywell, BodyMedia)
- Ligne 3: 4 logos (Microsoft, Amazon, MITRE, Fujitsu)
- Ligne 4: 1 logo (autre)

**Correction:** Définir la classe `.image-grid` dans le thème `ia101.css`:
```css
.image-grid {
  display: grid;
  grid-template-columns: repeat(4, 1fr);
  gap: 16px;
  margin-top: 24px;
}

.image-grid img {
  max-width: 100%;
  height: auto;
  object-fit: contain;
}
```

### Slide 16 - Test de Turing
**Problème:** Diagramme manquant
- **PPTX:** Diagramme du Test de Turing avec HUMAN INTERROGATOR, HUMAN, AI SYSTEM
- **Slidev:** `layout: image-right` avec `./images/img_020.png` - vérifier que cette image correspond au diagramme

**Correction:** Si l'image n'est pas le diagramme complet, créer un composant SVG/Mermaid pour reproduire le diagramme.

### Slide 22 - Les agents
**Problème:** Diagramme flux avec formule mathématique
- **PPTX:** Diagramme montrant Agent, Environnement, Capteurs, Effecteurs avec flèches. Formule f: P* → A centrée et encadrée
- **Slidev:** `layout: image-right` avec `./images/img_021.png` - vérifier que cette image contient le diagramme complet
- **Formule:** La formule est présente dans le texte mais pas mise en valeur

**Suggestion:** Utiliser MathJax/KaTeX pour la formule:
```markdown
$$f: \mathcal{P}^* \to \mathcal{A}$$
```

### Slide 25 - Intelligences
**Problème majeur:** Layout complexe non reproduit
- **PPTX:** Rectangle rouge-orangé contenant 3 sections (Procédurale, Exploratoire, Symbolique/Probabiliste) avec images et sous-sections
- **Slidev:** `layout: two-cols` avec texte à gauche et 4 images à droite - complètement différent du PPTX

**Layout PPTX:**
- Section "Procédurale": Image puzzle + boîtes "Automates", "Algorithmes"
- Section "Exploratoire": Image carte + boîtes "Recherche de chemin", "Escalades", "Arbres de jeux", "Satisfaction de contraintes"
- Section "Symbolique": Image arbre + boîtes "Raisonnement", "Bases de connaissances", "Solveurs", "Planificateurs", "Smart-contracts"
- Sous-section "Probabiliste" (imbriquée): Image réseau + boîtes "Modèles graphiques", "Réseaux de décision", "Politiques Markoviennes", "Théorie des jeux" (en violet)

**Correction:** Créer un composant personnalisé ou utiliser plusieurs slides avec v-click pour reproduire ce layout complexe.

**Suggestion:** Diviser en 4 slides ou créer un composant `IntelligenceTypes.vue`:
```vue
<template>
  <div class="intelligence-container">
    <div class="section procedural">
      <h3>Procédurale</h3>
      <img src="./images/img_022.jpg">
      <div class="boxes">
        <div class="box">Automates</div>
        <div class="box">Algorithmes</div>
      </div>
    </div>
    ...
  </div>
</template>
```

### Slide 30 - Environnement de tâche (PEAS)
**Problème:** Structure tabulaire perdue
- **PPTX:** Liste structurée avec retrait et formatage spécifique (PEAS en gras, exemples indentés)
- **Slidev:** Liste markdown standard

**Suggestion:** Améliorer avec un tableau ou un composant personnalisé:
```markdown
| Composant | Description |
|-----------|-------------|
| **P**erformance | Mesure de performance |
| **E**nvironnement | Environnement de tâche |
| **A**ctuators | Effecteurs |
| **S**ensors | Capteurs |

**Exemple: Taxi**
- **Performance:** Prudent, rapide, légal, confortable, rentable
- **Environnement:** Route, trafic, piétons, clients, véhicule
- **Effecteurs:** Volant, accélérateur, frein, clignotants, klaxon
- **Capteurs:** Caméras, sonar, accéléromètre, GPS, Lidar, clavier etc.
```

### Slide 31 - Environnements de tâche: exemples
**Problème majeur:** Tableau 5 colonnes x 6 lignes
- **PPTX:** Tableau complet avec 5 colonnes (Type d'agent, Mesure de performance, Environnement, Effecteurs, Capteurs) et 5 exemples
- **Slidev:** Image `./images/img_028.png` - vérifier que cette image est une capture du tableau ou reproduire le tableau en markdown

**Suggestion:** Recréer le tableau en markdown:
```markdown
| Type d'agent | Mesure de performance | Environnement | Effecteurs | Capteurs |
|--------------|----------------------|---------------|------------|----------|
| Diagnostic médical | Santé du patient | Patient, hôpital | Affichage des questions, traitements | Symptômes, signes vitaux |
| Analyse d'images satellites | Catégories correctes | Images satellites | Affichage des catégories | Pixels d'images satellites |
| Robot contrôleur de pièces | Pourcentage correct | Banque de pièces | Bras robotique, saisissement | Caméra, joint angle sensor |
| Contrôleur de raffinerie | Pureté, rendement | Raffinerie | Valves, pompes, chauffages | Température, pression, capteurs chimiques |
| Répétiteur d'anglais | Score des étudiants | Ensemble d'étudiants | Affichage d'exercices, commentaires | Frappes au clavier |
```

### Slide 33 - Types d'environnement: exemples
**Problème:** Tableau 7 colonnes x 9 lignes
- **PPTX:** Tableau avec 7 colonnes (Environnement de tâche, Observable, Agents, Déterministe, Épisodique, Statique, Discret)
- **Slidev:** Image `./images/img_029.png` - vérifier que cette image capture le tableau

**Suggestion:** Si l'image n'est pas lisible, recréer le tableau en markdown. Attention: les tableaux larges peuvent ne pas tenir sur une slide.

### Slide 34 - Types d'agents
**Problème:** Liste numérotée avec image
- **PPTX:** Image du diagramme des types d'agents à droite
- **Slidev:** `layout: image-right` avec `./images/img_030.png`

**Vérification:** Confirmer que l'image correspond au diagramme complet (5 types d'agents).

### Slide 35 - Agent réflexe
**Problème:** Layout deux colonnes avec diagramme et images
- **PPTX:** Colonne gauche: texte + petite image livre. Colonne droite: diagramme agent réflexe + code fonctionnel
- **Slidev:** `layout: two-cols` avec texte à gauche et 2 images à droite

**Vérification:** Confirmer que `img_031.png` et `img_032.png` correspondent au diagramme et au code.

### Slide 36 - Agent réflexe fondé sur un modèle
**Problème:** Layout deux colonnes avec diagramme
- **PPTX:** Similaire à slide 35
- **Slidev:** `layout: two-cols` avec texte et 2 images

**Vérification:** Confirmer les images.

### Slide 40 - Fonctionnement interne des agents
**Problème:** Diagramme de hiérarchie des représentations
- **PPTX:** Diagramme montrant Atomique → Factorisé → Structuré avec visuels
- **Slidev:** `layout: image-right` avec `./images/img_040.png`

**Vérification:** Confirmer que l'image contient le diagramme complet.

---

## Problèmes transversaux

### 1. Images manquantes ou chemins incorrects
- Plusieurs références à `Picture*.jpg` dans le contenu extrait ne correspondent pas aux images renommées en `img_XXX.*`
- **Correction:** Script de mapping entre les noms PPTX et les noms Slidev

### 2. Texte déchet
- Numéros de slide isolés (ex: "1", "2", "3" sous les titres)
- "IA 101" répété sur chaque slide en bas à gauche
- Notes de présentation incluses dans le contenu ("### Notes:", "Timing?", etc.)

**Correction:** Ces éléments sont probablement ajoutés par le script d'extraction et peuvent être ignorés dans le markdown Slidev (le thème gère les numéros et le footer).

### 3. Tableaux avec styles
- Les tableaux PPTX avec couleurs de fond ne sont pas reproduits en markdown
- **Suggestion:** Utiliser des classes CSS personnalisées ou des composants Vue pour les tableaux stylisés

### 4. Layouts complexes non standard
- Slides 25 (Intelligences) avec rectangle contenant sections imbriquées
- Slides avec grilles d'images (slide 14)
- **Suggestion:** Créer des composants Vue personnalisés pour ces layouts spécifiques

### 5. Animations
- Les animations PPTX sont converties en `v-click` mais l'ordre peut ne pas correspondre exactement
- **Vérification:** Tester manuellement l'ordre des animations sur les slides avec v-click

---

## Recommendations

### Actions prioritaires

1. **Vérifier toutes les images** : Confirmer que chaque image référencée existe et correspond au visuel PPTX
2. **Reproduire les tableaux** : Pour les slides 31 et 33, recréer les tableaux en markdown ou utiliser des images haute résolution
3. **Corriger le layout slide 25** : Créer un composant personnalisé ou diviser en plusieurs slides
4. **Définir .image-grid** : Ajouter le CSS pour la grille de logos (slide 14)
5. **Styles de tableau** : Ajouter des classes CSS pour les tableaux colorés (slide 10)

### Améliorations suggérées

1. **Composants Vue** : Créer une bibliothèque de composants pour les layouts récurrents (tableaux stylisés, grilles, diagrammes)
2. **Thème IA101** : Enrichir le thème avec des styles pour tableaux, grilles, et boîtes colorées
3. **Tests visuels** : Pour chaque slide PPTX, comparer côte à côte avec le rendu Slidev
4. **Script de validation** : Créer un script qui vérifie que toutes les images référencées existent

---

## Tableau de correspondence PPTX → Slidev

| Slide PPTX | Titre | Slidev | Layout | État |
|------------|-------|--------|--------|------|
| 1 | Intelligence artificielle | 1 | cover | OK |
| 2 | IA 101 | 2 | default | OK |
| 3 | Sommaire | 3 | image-right | À vérifier |
| 4 | Sommaire (2) | 4 | default | OK |
| 5 | Objectifs du cours | 5-6 | default | Scindé en 2 slides (OK) |
| 6 | Plan du cours | 7 | default | OK |
| 7 | Questions? | 8 | questions | OK |
| 8 | Introduction à l'IA | 9 | default | OK |
| 9 | Qu'est-ce que l'IA? | 10 | default | OK |
| 10 | 4 visions de l'IA | 11 | default | Tableau sans style |
| 11 | Les fondements de l'IA | 12 | image-right | À vérifier (format tabulaire perdu) |
| 12 | Histoire succincte | 13 | image-right | Chronologie en 2 colonnes perdue |
| 13 | Etat de l'art | 14-15 | image-right + v-click | Scindé en 2 slides |
| 14 | Qui fait de l'IA | 16 | default + image-grid | Grille CSS manquante |
| 15 | Dans la vie de tous les jours | 17 | default | OK |
| 16 | Test de Turing | 18 | image-right | À vérifier |
| 17 | Sciences cognitives | 19 | default | OK |
| 18 | Pensée rationnelle | 20 | default | OK |
| 19 | Agent rationnel | 21 | default | OK |
| 20 | Questions? | 22 | questions | OK |
| 21 | Systèmes d'agents | 23 | default | OK |
| 22 | Les agents | 24 | image-right | À vérifier (diagramme + formule) |
| 23-24 | Agents rationnels | 25-26 | default | Scindé en 2 slides (OK) |
| 25 | Intelligences | 27-28 | two-cols | Layout complexe non reproduit |
| 26 | (continuation) | - | - | Absent |
| 27 | Intelligence de la recherche | 29 | default | OK |
| 28 | Intelligence de la pensée logique | 30 | default | OK |
| 29 | Intelligence de l'incertitude | 31 | default | OK |
| 30 | Environnement de tâche | 32 | default | Structure perdue |
| 31 | Exemples env. de tâche | 33 | image | Tableau → image |
| 32 | Types d'environnement | 34-35 | default + v-click | Scindé en 2 slides |
| 33 | Exemples types d'env. | 36 | image | Tableau → image |
| 34 | Types d'agents | 37 | image-right | À vérifier |
| 35 | Agent réflexe | 38 | two-cols | À vérifier |
| 36 | Agent réflexe + modèle | 39 | two-cols | À vérifier |
| 37 | Agent fondé sur buts | 40 | image-right | OK |
| 38 | Agent fondé sur utilité | 41 | image-right | OK |
| 39 | Agent apprenant | 42 | image-right | OK |
| 40 | Fonctionnement interne | 43 | image-right | À vérifier |
| 41 | Résumé | 44 | default | OK |
| 42 | Plan du cours | 45 | default | OK |
| 43 | Merci | 46-47 | cover + crossref | Slide supplémentaire notebooks |

---

## Conclusion

La conversion PPTX → Slidev est globalement réussie pour le contenu textuel et les images simples. Les principaux défis résident dans:

1. **Layouts complexes** (tableaux, grilles) qui nécessitent soit des images, soit des composants personnalisés
2. **Styles visuels** (couleurs de tableau, boîtes colorées) qui ne sont pas supportés nativement en markdown
3. **Fidélité visuelle** pour les slides avec diagrammes complexes

Les suggestions ci-dessus permettent d'améliorer progressivement la fidélité du rendu Slidev par rapport au PPTX original.
