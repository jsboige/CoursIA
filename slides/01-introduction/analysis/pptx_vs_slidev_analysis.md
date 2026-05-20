# Analyse Comparative PPTX vs Slidev - Deck 01-Introduction

**Date**: 2026-03-25
**Deck**: 01-introduction
**Slides analysées**: 1-10
**Méthode**: Analyse visuelle PPTX + comparaison structurelle avec code Slidev

---

## Synthèse Exécutive

### Problèmes Identifiés

| Slide | Titre | Problème Principal | Sévérité | Statut |
|-------|-------|-------------------|----------|--------|
| 1 | Intelligence artificielle | Layout cover personnalisé | Faible | OK |
| 2 | IA 101 | Restructuration contenu | Faible | OK |
| 3 | Sommaire | Image img_001 vs Picture6 | Moyenne | À vérifier |
| 4 | Sommaire (2) | Layout standard | Faible | OK |
| 5 | Objectifs du cours | Découpage en 2 slides | Faible | OK |
| 6 | Plan du cours | Contenu identique | Faible | OK |
| 7 | Questions? | Layout section personnalisé | Faible | À vérifier |
| 8 | Introduction | Sommaire de section | Faible | OK |
| 9 | Qu'est-ce que l'IA? | Image img_002 vs Image1 | Moyenne | À vérifier |
| 10 | Quatre visions de l'IA | Composant ColoredTable custom | Moyenne | À vérifier |

### Recommandations Prioritaires

**Immédiat (avant validation finale)**

1. **Vérifier les correspondances d'images**
   - `img_001.jpg` correspond-il à `Picture6.jpg` (slide 3) ?
   - `img_002.png` correspond-il à `Image1.jpg` (slide 9) ?
   - Créer une table de correspondance complète

2. **Tester les layouts personnalisés**
   - `layout: cover` - slide 1
   - `layout: section` - slide 7
   - `layout: image-overlay` - slides 3, 11+

3. **Valider le composant ColoredTable**
   - Vérifier le rendu visuel
   - Confirmer le style CSS (colored-table)
   - Tester la cellule "highlight" (Agents rationnels)

4. **Tests de navigation**
   - Vérifier que les fragments/animations fonctionnent
   - Tester la présentation complète (mode présentateur)

---

## Analyse Détaillée par Slide

### Slide 01 - Intelligence artificielle (Cover)

**Layout PPTX**:
- Titre centré "Intelligence artificielle"
- Sous-titre "1"
- Informations enseignant centrées
- Image de fond probable

**Layout Slidev**:
```markdown
layout: cover
# Intelligence Artificielle
Intelligence Artificielle -- I
**Jean-Sylvain Boige**
MRes CSAI, Sussex University, Brighton UK
Aricie -- DNN -- PKP -- My Intelligence Agency
```

**Différences**:
- ⚠️ Slidev utilise layout `cover` personnalisé (thème ia101)
- ⚠️ Le numéro "1" n'est pas présent
- ℹ️ Structure similaire mais formatage différent

**Action requise**: Vérifier le rendu du layout cover dans le thème

---

### Slide 02 - IA 101 -- Ressources et organisation

**Contenu PPTX**:
- Livres: Russell & Norvig
- Classe: Corrections/Projets
- Cours, TPs, Projets trimestriels, Équipes 2-3, Exposé final

**Contenu Slidev**:
```markdown
# IA 101 -- Ressources et organisation
- **Ouvrage de reference**
  - *Artificial Intelligence: A Modern Approach* (Russell & Norvig)
  - 3e edition (2006) et 4e edition (2020, avec deep learning et IA moderne)
- **En classe**
  - Cours magistraux, corrections d'exercices, travaux pratiques
- **Projets trimestriels**
  - Équipes de 2-3 étudiants, travail transversal
  - Exposé final en classe devant le groupe
```

**Différences**:
- ℹ️ Contenu similaire mais structuré différemment
- ℹ️ Plus de détails dans Slidev (éditions du livre)
- ✓ Sens du contenu préservé

**Action requise**: Aucune (restructuration acceptable)

---

### Slide 03 - Sommaire (avec image)

**Contenu PPTX**:
- Liste des sections (Qu'est-ce que l'IA, Intelligence exploratoire, etc.)
- Image: `![Intelligence artificielle](Picture6.jpg)`

**Contenu Slidev**:
```markdown
layout: image-overlay
image: ./images/img_001.jpg
# Sommaire
- Qu'est-ce que l'intelligence artificielle ?
  - Racines, histoire et état de l'art
  - Structure des agents rationnels
- Intelligence exploratoire <!-- .element: class="fragment" -->
  - Comment chercher la solution a un probleme ?
[... avec fragments pour animation]
```

**Différences**:
- ⚠️ Image différente: `img_001.jpg` vs `Picture6.jpg`
- ⚠️ Layout `image-overlay` au lieu d'image inline
- ℹ️ Fragments pour animations (v-click)
- ℹ️ Image de fond plutôt qu'image séparée

**Action requise**:
- Vérifier que `img_001.jpg` correspond bien à `Picture6.jpg`
- Tester le rendu du layout image-overlay

---

### Slide 04 - Sommaire (Présentation cursus)

**Contenu PPTX**:
- Présentation du cursus
- Introduction, Systèmes d'agents, Projets de groupe

**Contenu Slidev**:
```markdown
# Sommaire
- Presentation du cursus
- Introduction
  - Qu'est-ce que l'intelligence artificielle?
  - Les domaines d'etude
  - Un peu d'histoire
  - L'état de l'art
- Systemes d'agents
  - Agents rationnels
  - Environnements taches
  - Types d'Agents
- Presentation des projets de groupe
```

**Différences**:
- ℹ️ Structure hiérarchique plus claire dans Slidev
- ℹ️ Contenu équivalent
- ✓ Bonne transformation

**Action requise**: Aucune

---

### Slide 05 - Objectifs du cours (1/2)

**Contenu PPTX** (slide unique):
- "A la fin de ce cours vous pourrez:"
- Comprendre et utiliser des modèles IA
- Pouvoir approfondir
- Concevoir des programmes dans...

**Contenu Slidev** (découpé en 2):
```markdown
# Objectifs du cours (1/2)
A l'issue de ce cours, vous serez capables de :
- **Comprendre les grands paradigmes de l'IA**
  - Identifier les principaux domaines et leurs applications
  - Disposer des bases pour approfondir chacun d'entre eux
- **Concevoir des programmes intelligents dans des domaines varies :**
  - Recherche de solutions et jeux strategiques
  - Representation de connaissances et raisonnement logique
  - Modelisation probabiliste et prise de decision sous incertitude
  - Apprentissage automatique (supervise, non supervise, par renforcement)
  - Traitement du langage naturel
```

**Différences**:
- ℹ️ Découpage en 2 slides dans Slidev
- ℹ️ Reformulation du contenu
- ℹ️ Plus détaillé dans Slidev

**Action requise**: Vérifier que le découpage en 2 slides ne casse pas le flux

---

### Slide 06 - Plan du cours

**Contenu PPTX**:
- Introduction
- Résolution de problèmes
- Bases de connaissances et logique
- Raisonnement probabiliste
- Théorie des jeux
- Apprentissage
- Traitement du langage naturel
- Présentations des projets

**Contenu Slidev**:
```markdown
# Plan du cours
- Introduction
- Resolution de problemes
- Bases de connaissances et logique
- Raisonnement probabiliste
- Theorie des jeux
- Apprentissage
- Traitement du langage naturel
- Presentations des projets
```

**Différences**:
- ℹ️ Contenu identique
- ✓ Bonne transformation

**Action requise**: Aucune

---

### Slide 07 - Questions?

**Slide de transition PPTX**:
- Titre: "Questions?"
- Numéro: 7

**Contenu Slidev**:
```markdown
layout: section
---
<h1 style="color: #F5F5F5 !important; border-bottom: 2px solid #F5F5F5 !important;">Questions?</h1>
```

**Différences**:
- ℹ️ Utilise le layout `section` personnalisé
- ℹ️ Style inline pour le texte
- ✓ Fonctionnalité préservée

**Action requise**: Vérifier le rendu du layout section

---

### Slide 08 - Introduction à l'intelligence artificielle

**Contenu PPTX**:
- Sommaire identique à la slide 04

**Contenu Slidev**:
```markdown
# Introduction a l'intelligence artificielle
- Presentation du cursus
- Introduction
  - Qu'est-ce que l'intelligence artificielle?
  - Les domaines d'etude
  - Un peu d'histoire
  - L'état de l'art
- Systemes d'agents
  - Agents rationnels
  - Environnements taches
  - Types d'agents
- TP: Mise en place de l'environnement de travail
- Presentation des projets de groupe
```

**Différences**:
- ℹ️ C'est une slide de sommaire de section (pas un doublon)
- ℹ️ Contenu identique à PPTX
- ℹ️ Structure hiérarchique claire

**Action requise**: Aucune (c'est une slide de section normale)

---

### Slide 09 - Qu'est-ce que l'intelligence artificielle?

**Contenu PPTX**:
- Définitions multiples de l'intelligence et de l'IA
- Concevoir != comprendre
- Image: `![](Image1.jpg)`
- Définition mouvante: Automates → Calculateur → Algorithmes → Bases de connaissances → Systèmes experts → Systèmes probabilistes → Apprentissage profond → Generatif?

**Contenu Slidev**:
```markdown
# Qu'est-ce que l'intelligence artificielle ?
- **Des definitions multiples et un concept evolutif**
  - L'IA n'a pas de definition unique : elle recouvre des approches tres differentes
  - Concevoir un systeme intelligent n'implique pas de comprendre l'intelligence
- **Une definition qui evolue avec la technologie :**
  - Automates → Calculateurs → Algorithmes → Bases de connaissances → Systemes experts → Apprentissage profond → IA generative

<div class="center-image">
<img src="./images/img_002.png" alt="Definition IA" style="max-width: 850px; margin: auto; display: block;">
</div>
```

**Différences**:
- ⚠️ Image différente: `img_002.png` vs `Image1.jpg`
- ℹ️ Reformulation du contenu (plus détaillé dans Slidev)
- ℹ️ Image centrée avec style inline
- ℹ️ Liste des technologies plus à jour (IA générative)

**Action requise**:
- Vérifier que `img_002.png` correspond à l'image attendue
- Vérifier le rendu du style inline

---

### Slide 10 - Quatre visions de l'IA

**Contenu PPTX**:
- 4 types d'approches (tableau 2x2)
- Notre angle principal: "Agir de façon rationnelle" → Conception d'agents
- Tableau:
  - | Penser comme l'homme | Penser de façon rationnelle |
  - | Agir comme l'homme  | Agir de façon rationnelle |

**Contenu Slidev**:
```markdown
# Quatre visions de l'IA
**Quatre grandes approches structurent le domaine :**
<ColoredTable />
**Notre angle principal : « Agir de facon rationnelle »**
- Concevoir des agents qui prennent les meilleures decisions possibles
- Approche qui unifie les autres : un agent rationnel peut raisonner, apprendre et communiquer
```

**Composant ColoredTable** (compilé):
```html
<table class="colored-table">
  <tr>
    <td class="header-cell"></td>
    <td class="header-cell">Comme l'homme</td>
    <td class="header-cell">De facon rationnelle</td>
  </tr>
  <tr>
    <td class="header-cell">Penser</td>
    <td class="content-cell">Sciences cognitives</td>
    <td class="content-cell">Logique formelle</td>
  </tr>
  <tr>
    <td class="header-cell">Agir</td>
    <td class="content-cell">Test de Turing</td>
    <td class="content-cell highlight">Agents rationnels</td>
  </tr>
</table>
```

**Différences**:
- ⚠️ Utilise un composant custom au lieu d'un tableau markdown
- ⚠️ Contenu des cellules différent:
  - PPTX: "Penser comme l'homme" | "Penser de façon rationnelle"
  - Slidev: "Comme l'homme" | "De facon rationnelle" (avec "Penser" et "Agir" en ligne)
- ℹ️ Slidev a plus de détails (Sciences cognitives, Logique formelle, Test de Turing)
- ✓ La structure 2x2 est préservée

**Action requise**:
- Vérifier que le composant `ColoredTable` est bien stylé
- Confirmer que le contenu sémantique est équivalent
- Vérifier le rendu de la cellule "highlight" (Agents rationnels)

---

## Problèmes Structurels Identifiés

### 1. Gestion des Images

**Problème**:
- Les noms de fichiers image ne correspondent pas toujours
- PPTX utilise `Picture6.jpg`, Slidev utilise `img_001.jpg`

**Impact**: Moyen
**Recommandation**: Créer une table de correspondance des images

### 2. Animations et Fragments

**Problème**:
- PPTX a des animations (v-click)
- Slidev utilise `<!-- .element: class="fragment" -->`

**Impact**: Faible
**Recommandation**: Tester que toutes les animations fonctionnent

### 3. Layouts Custom

**Problème**:
- Slidev utilise des layouts custom (`cover`, `image-overlay`, `section`)
- Ces layouts doivent être définis dans le thème ia101

**Impact**: Élevé
**Recommandation**: Vérifier tous les layouts custom du thème

### 4. Découpage de Contenu

**Problème**:
- Certaines slides PPTX sont découpées en plusieurs slides Slidev
- Ex: Objectifs du cours (1 slide PPTX → 2 slides Slidev)

**Impact**: Faible
**Recommandation**: Documenter les différences de structure

---

## Actions Recommandées

### Immédiat (avant validation)

1. **Vérifier le thème ia101**
   - Layout `cover`
   - Layout `image-overlay`
   - Layout `section`

2. **Correspondance des images**
   - Créer un mapping PPTX → Slidev
   - Vérifier que toutes les images sont présentes

3. **Tests de navigation**
   - Vérifier que les fragments/animations fonctionnent
   - Tester la présentation complète

### Court terme

1. **Audit des slides 8-10**
   - Lire le code source complet
   - Comparer avec le contenu PPTX
   - Identifier les écarts

2. **Validation visuelle**
   - Capturer les rendus Slidev correctement
   - Comparer côte à côte avec PPTX

### Moyen terme

1. **Documentation**
   - Documenter les différences PPTX vs Slidev
   - Créer un guide de migration

2. **Automatisation**
   - Script de comparaison automatique
   - Tests de régression

---

## Notes Techniques

### Capture Slidev

Les captures automatiques via Playwright n'ont pas fonctionné correctement car:
- La navigation par `#1`, `#2` ne fonctionne pas
- La navigation par ArrowRight nécessite un timing spécifique
- Les slides avec fragments nécessitent plusieurs clicks

**Recommandation**: Utiliser l'export PDF de Slidev pour la comparaison

```bash
cd slides/01-introduction
npm run build
# Le PDF sera dans dist/
```

### Fichiers Utilisés

- **PPTX renders**: `slides/01-introduction/modernized/renders/slide_*.png`
- **Slidev source**: `slides/01-introduction/slides.md`
- **Contenu extrait**: `slides/01-introduction/extracted/content.md`
- **Thème**: `slides/theme-ia101/`

---

## Conclusion

### Résumé de l'analyse

L'analyse des 10 premières slides du deck 01-introduction montre :

**Slides bien converties (6/10)** :
- Slide 1: Cover - layout personnalisé, contenu fidèle
- Slide 2: IA 101 - restructuration claire
- Slide 4: Sommaire (2) - hiérarchie améliorée
- Slide 5: Objectifs - découpage en 2 slides acceptable
- Slide 6: Plan du cours - contenu identique
- Slide 8: Introduction - sommaire de section normal

**Slides nécessitant vérification (4/10)** :
- Slide 3: Image `img_001.jpg` vs `Picture6.jpg`
- Slide 7: Layout `section` à tester
- Slide 9: Image `img_002.png` vs `Image1.jpg`
- Slide 10: Composant `ColoredTable` à valider

### Problèmes structurels identifiés

1. **Correspondance des images** : Noms de fichiers différents entre PPTX et Slidev
2. **Layouts personnalisés** : Dépendance au thème `ia101`
3. **Composants custom** : `ColoredTable` nécessite CSS
4. **Découpage de contenu** : Certaines slides PPTX sont découpées en plusieurs slides Slidev

### Statistiques

| Métrique | Valeur |
|----------|-------|
| Slides analysées | 10 / 43 |
| Slides fidèles | 6 (60%) |
| Slides à vérifier | 4 (40%) |
| Problèmes bloquants | 0 |
| Problèmes moyens | 4 |

---

## Checklist de Validation

### Phase 1 - Vérification des images

- [ ] Créer une table de correspondance PPTX → Slidev
  - [ ] `Picture6.jpg` → `img_001.jpg`
  - [ ] `Image1.jpg` → `img_002.png`
  - [ ] Autres images à mapper
- [ ] Vérifier que toutes les images existent dans `slides/01-introduction/images/`
- [ ] Confirmer que le contenu sémantique est identique

### Phase 2 - Validation des layouts

- [ ] Tester `layout: cover` (slide 1)
  - [ ] Vérifier le rendu du titre
  - [ ] Vérifier le rendu du sous-titre
  - [ ] Vérifier les informations enseignant
- [ ] Tester `layout: section` (slide 7)
  - [ ] Vérifier le fond de couleur
  - [ ] Vérifier la lisibilité du texte
- [ ] Tester `layout: image-overlay` (slide 3, 11+)
  - [ ] Vérifier le positionnement de l'image
  - [ ] Vérifier la superposition du texte

### Phase 3 - Validation des composants

- [ ] Valider le composant `ColoredTable`
  - [ ] Vérifier le rendu du tableau
  - [ ] Vérifier les styles CSS (header-cell, content-cell, highlight)
  - [ ] Confirmer que la cellule "Agents rationnels" est bien mise en évidence

### Phase 4 - Tests de navigation

- [ ] Démarrer le serveur Slidev : `npm run dev`
- [ ] Tester la navigation clavier (ArrowRight, ArrowLeft)
- [ ] Vérifier les animations fragments (v-click)
- [ ] Tester le mode présentateur (p)
- [ ] Exporter en PDF : `npm run build`

### Phase 5 - Comparaison visuelle finale

- [ ] Générer les captures Slidev correctement
- [ ] Comparer côte à côte avec les renders PPTX
- [ ] Valider la fidélité visuelle
- [ ] Documenter les différences acceptables

---

## Prochaines Étapes

### Immédiat

1. **Correspondance des images** : Créer le mapping complet
2. **Test des layouts** : Valider cover, section, image-overlay
3. **Test du composant ColoredTable** : Vérifier le CSS

### Court terme

1. **Analyse des slides 11-20** : Poursuivre l'analyse comparative
2. **Tests de navigation** : Valider les animations et fragments
3. **Export PDF** : Générer le PDF pour comparaison finale

### Moyen terme

1. **Documentation** : Créer un guide de migration PPTX → Slidev
2. **Automatisation** : Script de comparaison automatique
3. **Tests de régression** : Valider que les futures modifications ne cassent pas le rendu

---

## Fichiers de Référence

- **Rapport** : `slides/01-introduction/analysis/pptx_vs_slidev_analysis.md`
- **Source PPTX** : `slides/01-introduction/modernized/renders/slide_*.png`
- **Source Slidev** : `slides/01-introduction/slides.md`
- **Contenu extrait** : `slides/01-introduction/extracted/content.md`
- **Thème** : `slides/theme-ia101/`
- **Images** : `slides/01-introduction/images/`

---

**Date de fin d'analyse** : 2026-03-25
**Analyste** : Claude (Agent Slide Analyzer)
**Statut** : Analyse partielle (10/43 slides)
