# Comparaison PPTX vs Slidev - Slides 11-20

**Date**: 2026-03-25
**Deck**: 01-introduction
**Slides analysées**: 11-20

---

## Méthodologie

Analyse comparative des rendus PPTX (`modernized/renders/`) avec le code source Slidev (`slides.md`).
Pour chaque slide, identification des problèmes de fidélité de mise en forme.

---

## Slide 11 - Les fondements de l'IA

### Contenu PPTX
- Titre: "Les fondements de l'IA"
- Liste de 8 disciplines avec descriptions multilignes:
  - Philosophie, Maths, Economie, Biologie, Neurosciences, Psychologie, Informatique, Théorie du contrôle, Linguistique
- Image: Image1.jpg
- Footer: "IA 101"

### Contenu Slidev
```markdown
layout: image-overlay
image: ./images/img_003.png

# Les fondements de l'IA

L'IA est une discipline profondément interdisciplinaire :

- **Philosophie :** logique, raisonnement, nature de l'esprit
- **Mathematiques :** algorithmes, complexite, probabilites, decidabilite
...
```

### Problèmes identifiés
1. **Layout différent**: PPTX utilise un layout standard avec texte + image séparée, Slidev utilise `image-overlay`
2. **Image**: PPTX a Image1.jpg, Slidev a img_003.png (à vérifier si c'est la même image)
3. **Formatage texte**: Slidev a reformatté les descriptions (plus concises)
4. **Hiérarchie**: PPTX présente les disciplines en tableau-like format, Slidev en liste à puces

### Actions requises
- [ ] Vérifier correspondance Image1.jpg ↔ img_003.png
- [ ] Comparer rendu visuel: le layout image-overlay peut masquer du texte

---

## Slide 12 - Histoire succincte

### Contenu PPTX
- Titre: "Histoire succincte"
- Timeline structurée par décennies (1943-2010s)
- Image: Picture4.jpg (Turing)
- Footer: "IA 101"

### Contenu Slidev
```markdown
layout: image-overlay
image: ./images/img_004.png

# Histoire succincte (1/2)

**Les débuts (1943-1970)**
- **1943** : McCulloch & Pitts...
...
```

**Problème majeur**: Le PPTX a UNE slide, Slidev l'a divisé en DEUX slides (1/2 et 2/2)

### Problèmes identifiés
1. **Division du contenu**: Slidev a scindé en 2 slides vs 1 slide PPTX
2. **Layout**: image-overlay au lieu de layout standard
3. **Perte de continuité**: L'étudiant doit voir 2 slides au lieu de 1

### Actions requises
- [ ] Décider: fusionner en 1 slide ou garder 2 slides
- [ ] Si 1 slide: utiliser layout standard avec image à droite
- [ ] Vérifier correspondance Picture4.jpg ↔ img_004.png

---

## Slide 13 - Etat de l'art

### Contenu PPTX
- Titre: "État de l'art"
- Liste d'accomplissements (1997-2019)
- Images: Image10.jpg, Picture16.jpg (ImageNet logo)
- Footer: "IA 101"

### Contenu Slidev
```markdown
layout: image-overlay
image: ./images/img_005.jpg

# État de l'art (1/2)
...
```

**Même problème**: Slidev divise en 2 slides (1/2 et 2/2)

### Problèmes identifiés
1. **Division du contenu**: 1 slide PPTX → 2 slides Slidev
2. **Images multiples**: PPTX a 2 images, Slidev en a 1 seule
3. **Layout**: image-overlay peut masquer du texte

### Actions requises
- [ ] Fusionner les 2 slides Slidev en 1 seule
- [ ] Ajouter la deuxième image (ImageNet logo)
- [ ] Utiliser layout two-cols ou image-right

---

## Slide 14 - Qui fait de l'IA

### Contenu PPTX
- Titre: "Qui fait de l'IA"
- 3 sections: Recherche académique, Gouvernements, Beaucoup de sociétés
- **GRILLE DE 13 LOGOS** en bas de slide
- Image: Image1.jpg
- Footer: "IA 101"

### Contenu Slidev
```markdown
# Qui fait de l'IA ?

**Recherche académique**

<div class="image-grid">
<img src="./images/img_007.png" alt="CMU">
<img src="./images/img_008.png" alt="MIT">
...
</div>

**Industrie et laboratoires**

<div class="image-grid">
<img src="./images/img_012.png" alt="Google">
...
</div>
```

### Problèmes identifiés
1. **Layout image-grid**: PPTX a une grille compacte de 13 logos, Slidev utilise un layout CSS custom
2. **Section "Gouvernements" manquante**: PPTX mentionne "NASA, NRL, NIST, IBM, AT&T, SRI, ISI, MERL", Slidev l'a omise
3. **Nombre d'images**: PPTX a 13 logos, à vérifier dans Slidev
4. **Image1.jpg manquante**: PPTX a une image en plus des logos

### Actions requises
- [ ] Ajouter la section "Gouvernements et laboratoires privés"
- [ ] Vérifier que les 13 logos sont présents
- [ ] Vérifier rendu de la grille image-grid (ne pas déborder)
- [ ] Ajouter Image1.jpg si nécessaire

---

## Slide 15 - Dans la vie de tous les jours

### Contenu PPTX
- Titre: "Dans la vie de tous les jours"
- 8 catégories avec exemples: Poste, Banque, Trading, Service client, Internet, Sécurité, Jeux
- Footer: "IA 101"

### Contenu Slidev
```markdown
# L'IA dans la vie de tous les jours

- **Banque et finance** : scoring de crédit, détection de fraude, trading algorithmique
- **Service client** : chatbots, reconnaissance vocale, routage intelligent
- **Internet** : recommandation (Netflix, Spotify), détection de spam, publicité ciblée
- **Sécurité** : reconnaissance faciale, détection de plaques, vidéosurveillance
- **Transport** : navigation GPS, véhicules autonomes, optimisation logistique
- **Santé** : aide au diagnostic, analyse d'imagerie médicale, découverte de médicaments
- **Quotidien** : assistants vocaux (Siri, Alexa), traduction automatique, filtres photo
```

### Problèmes identifiés
1. **Catégories différentes**:
   - PPTX: Poste, Banque, Trading, Service client, Internet, Sécurité, Jeux
   - Slidev: Banque, Service client, Internet, Sécurité, Transport, Santé, Quotidien
2. **Contenu réécrit**: Slidev a reformatté et ajouté des exemples
3. **Perte de fidélité**: Le contenu n'est pas identique au PPTX

### Actions requises
- [ ] Aligner les catégories avec le PPTX
- [ ] Conserver les exemples originaux (Poste, Trading, Jeux)
- [ ] Décider: version PPTX (originale) ou version Slidev (améliorée?)

---

## Slide 16 - Agir comme l'homme: le Test de Turing

### Contenu PPTX
- Titre: "Agir comme l'homme: le Test de Turing"
- Section: "Turing (1950)"
- Liste: Précis, Compétences, Langage, Représentation de connaissances, Raisonnement, Apprentissage
- "Total Turing (+ caméra)": Vision, Robotique
- "→ Principales disciplines de l'IA"
- "Dont 4 détaillées dans ce cours"
- "Dnn + Portal Keeper: plateforme web d'agents"
- Image: Picture4.jpg (Turing)
- Footer: "IA 101"

### Contenu Slidev
```markdown
layout: image-overlay
image: ./images/img_020.png

# Agir comme l'homme : le Test de Turing

**Alan Turing (1950)** propose un test opérationnel : une machine est "intelligente" si un humain ne peut la distinguer d'un autre humain en conversant avec elle.

**Compétences requises pour réussir le test :**
- Traitement du langage naturel
- Representation de connaissances
- Raisonnement automatique
- Apprentissage

**« Total Turing » (+ camera)** ajoute la vision et la robotique.

**Ces compétences définissent les grandes disciplines de l'IA** -- dont quatre seront détaillées dans ce cours.
```

### Problèmes identifiés
1. **Layout**: image-overlay au lieu de layout standard
2. **Section "Précis" manquante**: PPTX a "Précis" comme élément séparé
3. **"Dnn + Portal Keeper" manquant**: Slidev a supprimé cette référence spécifique au cours
4. **Formatage**: Slidev a reformatté en paragraphes au lieu de liste structurée

### Actions requises
- [ ] Décider: garder "Dnn + Portal Keeper" ou supprimer (contexte spécifique?)
- [ ] Vérifier si le layout image-overlay masque du texte
- [ ] Restaurer la structure "Précis" si nécessaire

---

## Slide 17 - Penser comme l'homme: sciences cognitives

### Contenu PPTX
- Titre: "Penser comme l'homme: sciences cognitives"
- Bullet points sur la révolution cognitive, top-down vs bottom-up, distinction IA/sciences cognitives, irrationalité, reverse-engineering, hardware différent
- Footer: "IA 101"

### Contenu Slidev
```markdown
# Penser comme l'homme : sciences cognitives

- **La "révolution cognitive" (années 1960)**
  - La psychologie commence à modéliser la pensée comme un traitement de l'information
- **Deux approches pour étudier le cerveau**
  - *Top-down* : modéliser le comportement humain observable
  - *Bottom-up* : observer directement l'activité neurologique (IRMf, EEG)
- **Pourquoi l'IA s'en distingue aujourd'hui**
  - Les humains sont souvent irrationnels (biais cognitifs)
  - Le reverse-engineering du cerveau reste extrêmement difficile
  - Le "hardware" biologique diffère fondamentalement du silicium
```

### Problèmes identifiés
1. **Formatage**: Slidev a structuré en 3 sections avec sous-points
2. **Contenu**: Semble fidèle au PPTX mais réorganisé
3. **Perte de section "Introspection, experiences psychologiques, et imagerie"**: Cette section est dans les notes du PPTX mais pas dans Slidev

### Actions requises
- [ ] Vérifier rendu visuel (les sous-points peuvent être trop petits)
- [ ] Décider: ajouter la section sur l'imagerie si pédagogiquement pertinente

---

## Slide 18 - Penser de façon rationnelle: lois de la raison

### Contenu PPTX
- Titre: "Penser de façon rationnelle: lois de la raison"
- Contenu sur Aristote, logique, IA, représentation, inférence, problèmes (incertitude, délibération, pensées)
- Footer: "IA 101"

### Contenu Slidev
```markdown
# Penser de façon rationnelle : lois de la raison

- **Depuis Aristote : quels sont les arguments corrects ?**
  - La logique formelle fournit des règles de dérivation rigoureuses
- **La logique au service de l'IA**
  - Représenter les faits du monde sous forme formelle
  - Utiliser l'inférence pour déduire de nouvelles connaissances
  - Exemple : prouveurs automatiques de théorèmes
- **Limites de l'approche purement logique**
  - Le monde réel est incertain (capteurs imparfaits, information incomplète)
  - Tout comportement intelligent ne relève pas d'une délibération logique
  - En pratique, il faut aussi définir des buts et évaluer des coûts
```

### Problèmes identifiés
1. **Structure identique**: Slidev a bien structuré en 3 sections
2. **Contenu fidèle**: Semble correspondre au PPTX
3. **Formatage**: Sous-points peuvent être difficiles à lire en amphithéâtre

### Actions requises
- [ ] Vérifier lisibilité des sous-points en projection
- [ ] Simplifier si nécessaire (moins de profondeur hiérarchique)

---

## Slide 19 - Agir de façon rationnelle: l'agent

### Contenu PPTX
- Titre: "Agir de façon rationnelle: l'agent"
- Définition du comportement rationnel
- "N'implique pas forcément de penser (ex. clignement, réflexes)"
- "mais penser sert la rationalité de l'action"
- Théorie de la décision / Economie
- Evaluation, Maximisation, Utilité espérée
- Footer: "IA 101"

### Contenu Slidev
```markdown
# Agir de façon rationnelle : l'agent

- **Un comportement rationnel consiste à faire la bonne chose :**
  - Choisir l'action qui maximise les chances d'atteindre l'objectif, compte tenu de l'information disponible
- **Agir rationnellement n'implique pas forcément de penser**
  - Un réflexe (cligner des yeux) peut être rationnel sans délibération
  - Mais la réflexion reste un outil puissant au service de l'action
- **Lien avec la théorie de la décision**
  - Evaluer les états possibles et les actions disponibles
  - Maximiser l'utilité espérée, même sous incertitude
- **C'est l'approche centrale de ce cours** : concevoir des agents rationnels
```

### Problèmes identifiés
1. **Structure identique**: 4 sections bien organisées
2. **Contenu fidèle**: Correspond au PPTX
3. **Mise en valeur**: "C'est l'approche centrale de ce cours" est bien mis en avant

### Actions requises
- Aucune - slide bien convertie

---

## Slide 20 - Questions?

### Contenu PPTX
- Titre: "Questions?"
- Footer: "IA 101"

### Contenu Slidev
```markdown
---
layout: section
---

<h1 style="color: #F5F5F5 !important; border-bottom: 2px solid #F5F5F5 !important;">Questions?</h1>
```

### Problèmes identifiés
1. **Layout**: Slidev utilise `layout: section` (slide plein écran avec fond coloré)
2. **Style inline**: Le style CSS est inline dans le HTML
3. **Footer**: Le footer "IA 101" n'apparaît pas avec layout section

### Actions requises
- [ ] Vérifier rendu visuel (contrast, lisibilité)
- [ ] Décider: garder layout section ou utiliser layout standard

---

---

## Analyses détaillées PPTX (via sk-agent vision)

### Slide 11 - Les fondements de l'IA
**Analyse PPTX**: Layout avec image à droite, liste de 8 disciplines en colonne gauche
**Note PPTX**: Non évaluée (erreur sk-agent)
**Problème**: Slidev utilise `image-overlay` qui peut masquer du texte

### Slide 12 - Histoire succincte
**Analyse PPTX**: Deux colonnes (années gauche, descriptions droite), image centrale de schéma Turing
**Note PPTX**: 8/10 - organisation claire, couleurs distinctes pour les années
**Contenu PPTX**:
- Chronologie 1943-2010s
- 1943: McCulloch & Pitts
- 1950: Turing "Computing Machinery and Intelligence"
- 1956: Dartmouth "Artificial Intelligence"
- 1950-70: Enthousiasme des débuts
- 1950s: Premiers programmes (Samuel, Newell & Simon, Gelernter, Lisp)
- 1965: Robinson (algorithme complet de raisonnement)
- 1970s: Complexité calculatoire, réseaux de neurones calle
- 1969-79: Systèmes experts
- 1980s: IA devient une industrie
- 1986: Retour réseaux de neurones (rétropropagation)
- 1990s: IA devient une science
- 1995: Agents intelligents, diagnostic, GAs
- 2000s: Data mining, web sémantique
- 2010s: Big data, deep learning, chatbots, smart contracts

**Problème MAJEUR**: PPTX a 1 slide, Slidev a 2 slides (1/2 et 2/2)

### Slide 13 - Etat de l'art
**Analyse PPTX**: Structure en listes hiérarchisées par années, 2 logos (DARPA, ImageNet)
**Note PPTX**: 8/10 - hiérarchie claire, mais texte un peu dense
**Contenu PPTX**:
- 1997: Echecs - Deep Blue bat Kasparov
- Preuve conjectures Robbins, vol/conduite autonome, planification guerre du Golfe, NASA
- 2007: Jeu de dames résolu, Backgammon
- Trading algorithmique (85% du volume 2012)
- 2010: Explosion deep-learning
  - ImageNet: performances quasi humaines
  - 2014: GANs
  - 2016: AlphaGo bat Lee Sedol
  - TPUs
  - 2018: AlphaZero
  - 2017: Poker - Libratus
  - 2019: DeepMind StarCraft 2, Pluribus
- 2010: Traitement langage naturel
  - LinkedData, Watson, Proverb, Transformers (GPT2, BERT), chatbots

**Problème MAJEUR**: PPTX a 1 slide avec 2 images, Slidev a 2 slides avec 1 image

### Slide 14 - Qui fait de l'IA
**Analyse PPTX**: 3 sections, 12 logos en grille
**Note PPTX**: 8/10 - structure logique, bien lisible
**Contenu PPTX**:
- Recherche académique (5 logos): CMU, Stanford, Berkeley, MIT, Caltech, U Austin, IDSIA
- Gouvernements et laboratoires privés (0 logos): NASA, NRL, NIST, IBM, AT&T, SRI, ISI, MERL
- Beaucoup de sociétés (7 logos): Google, Apple, Microsoft, Facebook, Amazon, Honeywell, Teknowledge, SAIC, MITRE, Fujitsu, Global InfoTek, BodyMedia

**Problème CRITIQUE**: Slidev a SUPPRIMÉ la section "Gouvernements et laboratoires privés"

### Slide 15 - Dans la vie de tous les jours
**Analyse PPTX**: 6 catégories avec sous-points
**Note PPTX**: 8/10 - bon contraste, hiérarchie claire
**Contenu PPTX**:
- Poste: reconnaissance adresses, tri courrier
- Banque: lecture chèques, vérification signatures, évaluation crédits, trading
- Service client: synthèse/reconnaissance vocale, agents conversationnels
- Internet: identification visiteur, marketing, segmentation, détection spam/fraude
- Sécurité: détection plaques, visages
- Jeux: personnages/adversaires intelligents

**Problème**: Slidev a réécrit le contenu (catégories différentes: Transport, Santé, Quotidien ajoutés; Poste, Trading, Jeux supprimés)

### Slide 16 - Agir comme l'homme: Test de Turing
**Analyse PPTX**: Non évaluée (erreur sk-agent)
**Contenu PPTX** (selon content.md):
- Turing (1950)
- Précis
- Compétences: Langage, Représentation connaissances, Raisonnement, Apprentissage
- "Total Turing" (+ caméra): Vision, Robotique
- → Principales disciplines de l'IA
- Dont 4 détaillées dans ce cours
- Dnn + Portal Keeper: plateforme web d'agents

**Problème**: Slidev a supprimé "Précis" et "Dnn + Portal Keeper", layout image-overlay

### Slide 17 - Penser comme l'homme: sciences cognitives
**Analyse PPTX**: Une colonne, hiérarchie claire avec puces rouges/jaunes
**Note PPTX**: 8/10 - très lisible, structure logique
**Contenu PPTX**:
- Révolution cognitive (1960s): Psychologie comme traitement de l'information
- Théories scientifiques activité cerveau humain
  - Modèles comportement humain (top-down)
  - Observation activité neurologique (bottom-up)
- Deux approches aujourd'hui distinctes de l'IA
  - Hommes souvent irrationnels
  - Reverse-engineering difficile
  - Hardware différent

**Slidev**: Contenu fidèle, bien structuré

### Slide 18 - Penser de façon rationnelle: lois de la raison
**Analyse PPTX**: Une colonne, fond bleu-vert pâle, hiérarchie claire
**Note PPTX**: 7/10 - structure claire mais texte dense pour amphithéâtre
**Contenu PPTX**:
- Aristote: arguments corrects?
- Règles dérivations pour la pensée
- En lien maths/philosophie (Logique) à l'IA
- Représentation faits du monde
- Inférence logique
- Ex: prouveurs théorèmes
- Problèmes: incertitude, délibération, bonnes pensées, monde réel → buts/coûts

**Slidev**: Contenu fidèle, bien structuré en 3 sections

### Slide 19 - Agir de façon rationnelle: l'agent
**Analyse PPTX**: Une colonne, fond gris clair, hiérarchie très claire
**Note PPTX**: 8.5/10 - bien structurée, lisible
**Contenu PPTX**:
- Comportement rationnel: faire la bonne chose
  - Maximiser chances d'atteindre objectif
- N'implique pas forcément de penser (réflexes)
  - Mais penser sert la rationalité
- Théorie décision / Economie
  - Evaluation états/actions
  - Maximisation utilité
  - Utilité espérée si incertaine

**Slidev**: Contenu fidèle, bien structuré, aucune correction nécessaire

### Slide 20 - Questions?
**Analyse PPTX**: Titre "Questions?", layout simple
**Note PPTX**: Non évaluée (sk-agent a analysé "Systèmes d'agents" à la place)

**Problème**: Slidev utilise `layout: section` (plein écran), PPTX a layout standard

---

## Tableau récapitulatif MIS À JOUR

| Slide | Titre | Note PPTX | Fidélité | Problème principal |
|-------|-------|-----------|----------|-------------------|
| 11 | Les fondements de l'IA | N/A | Moyenne | Layout image-overlay vs standard |
| 12 | Histoire succincte | 8/10 | Faible | Division en 2 slides vs 1 |
| 13 | Etat de l'art | 8/10 | Faible | Division en 2 slides, image manquante |
| 14 | Qui fait de l'IA | 8/10 | Faible | Section gouvernements SUPPRIMÉE |
| 15 | Dans la vie de tous les jours | 8/10 | Moyenne | Catégories différentes, contenu réécrit |
| 16 | Test de Turing | N/A | Moyenne | Layout image-overlay, sections manquantes |
| 17 | Sciences cognitives | 8/10 | Bonne | Aucun |
| 18 | Lois de la raison | 7/10 | Bonne | Aucun |
| 19 | L'agent | 8.5/10 | Bonne | Aucun |
| 20 | Questions? | N/A | Bonne | Layout section vs standard |

---

## Slides CRITIQUES (corrections obligatoires)

### 1. Slide 14 - Qui fait de l'IA (CRITIQUE)
**Problème**: Section "Gouvernements et laboratoires privés" COMPLETEMENT SUPPRIMÉE
**Action IMMÉDIATE**: Ajouter la section manquante
```markdown
**Gouvernements et laboratoires privés**
- NASA, NRL, NIST, IBM, AT&T, SRI, ISI, MERL...
```

### 2. Slide 12 - Histoire succincte (CRITIQUE)
**Problème**: Contenu divisé en 2 slides vs 1 slide PPTX
**Action**: Décider pédagogiquement:
- Option A: Fusionner en 1 slide (respecte PPTX)
- Option B: Garder 2 slides (meilleure lisibilité?)
- **Recommandation**: Fusionner pour respecter le rythme original

### 3. Slide 13 - Etat de l'art (CRITIQUE)
**Problème**: Contenu divisé en 2 slides, image ImageNet manquante
**Action**:
- Fusionner les 2 slides Slidev
- Ajouter la deuxième image (ImageNet logo)
- Utiliser layout two-cols ou image-right

---

## Actions requises par slide

### Slide 11 - Les fondements de l'IA
- [ ] Changer layout de `image-overlay` à `image-right` ou layout standard
- [ ] Vérifier correspondance Image1.jpg ↔ img_003.png

### Slide 12 - Histoire succincte
- [ ] **FUSIONNER** les 2 slides (1/2 et 2/2) en 1 seule
- [ ] Utiliser layout standard avec image à droite
- [ ] Vérifier correspondance Picture4.jpg ↔ img_004.png

### Slide 13 - Etat de l'art
- [ ] **FUSIONNER** les 2 slides (1/2 et 2/2) en 1 seule
- [ ] **AJOUTER** la deuxième image (ImageNet logo - Picture16.jpg)
- [ ] Utiliser layout two-cols ou image-right

### Slide 14 - Qui fait de l'IA (CRITIQUE)
- [ ] **AJOUTER** la section "Gouvernements et laboratoires privés"
- [ ] Vérifier rendu de la grille image-grid
- [ ] Compter les logos: doit y avoir 12 logos (5 académiques + 0 gouvernements + 7 sociétés)

### Slide 15 - Dans la vie de tous les jours
- [ ] Décider: garder version PPTX ou version Slidev?
- [ ] Si PPTX: restaurer Poste, Trading, Jeux
- [ ] Si Slidev: documenter pourquoi les changements

### Slide 16 - Agir comme l'homme: Test de Turing
- [ ] Changer layout de `image-overlay` à `image-right` ou layout standard
- [ ] Décider: ajouter "Précis" et "Dnn + Portal Keeper" ou supprimer?

### Slide 17 - Penser comme l'homme: sciences cognitives
- [ ] Aucune action - slide correcte

### Slide 18 - Penser de façon rationnelle: lois de la raison
- [ ] Aucune action - slide correcte

### Slide 19 - Agir de façon rationnelle: l'agent
- [ ] Aucune action - slide correcte

### Slide 20 - Questions?
- [ ] Décider: garder layout section ou utiliser layout standard

---

## Problèmes récurrents identifiés

### 1. Layout image-overlay inapproprié
**Slides affectées**: 11, 12, 13, 16
**Problème**: Le layout `image-overlay` met l'image en arrière-plan semi-transparent, ce qui réduit la lisibilité du texte
**Solution**: Remplacer par `layout: image-right` ou layout standard avec image séparée

### 2. Division de contenu non justifiée
**Slides affectées**: 12 (Histoire), 13 (Etat de l'art)
**Problème**: Le PPTX a 1 slide, Slidev a 2 slides
**Impact**: Change le rythme de la présentation, peut perdre l'audience
**Solution**: Fusionner ou documenter pourquoi la division est pédagogiquement justifiée

### 3. Contenu manquant
**Slides affectées**: 14 (Gouvernements), 13 (ImageNet), 16 (Précis, Dnn+PortalKeeper)
**Problème**: Sections ou images supprimées lors de la conversion
**Solution**: Restaurer le contenu manquant

---

## Recommandations globales

1. **Revoir tous les layouts image-overlay**: Ces layouts réduisent la lisibilité. Préférer `image-right` ou layouts standard.
2. **Standardiser les footers**: Certains layouts (section) n'affichent pas "IA 101"
3. **Vérifier toutes les images**: S'assurer que toutes les images PPTX ont un équivalent dans Slidev
4. **Prendre des screenshots Slidev**: Pour vérifier visuellement le rendu final

---

## Note pour vérification visuelle

**À FAIRE**: Prendre des screenshots du serveur Slidev (http://localhost:3031) pour chaque slide 11-20

**Méthode suggérée**:
1. Naviguer sur http://localhost:3031
2. Pour chaque slide, utiliser les touches fléchées pour naviguer
3. Prendre un screenshot (Windows: Win+Shift+S)
4. Comparer visuellement avec les PNG PPTX

**Priorité**: Slides 12, 13, 14 (corrections critiques)

---

**Fin du rapport**
**Date**: 2026-03-25
**Analyste**: Claude Code + sk-agent vision
