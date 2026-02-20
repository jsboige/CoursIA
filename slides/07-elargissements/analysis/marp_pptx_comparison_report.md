# Rapport de Comparaison Marp vs PPTX
# Deck 07 - Elargissements

**Date**: 2026-02-20
**Marp slides**: 40
**PPTX slides**: 37

---

## Problème Critique Identifié

Les rendus PPTX dans `extracted/renders/` **NE correspondent PAS** au contenu du fichier PPTX original. L'outil de rendu (LibreOffice/OpenOffice) génère des images incorrectes.

**Exemple**:
- PPTX slide 20 (contenu): "Sécurité de l'IA"
- PPTX slide 20 (rendu PNG): "Questions?"

Le rendu PNG affiche le contenu d'un **autre deck** (probablement le deck 02 - Résolution de problèmes).

---

## Analyse Basée sur le Contenu Markdown vs Contenu Extrait

### Correspondance des Slides

| Marp # | PPTX # | Titre Marp | Titre PPTX | Statut |
|--------|--------|------------|------------|--------|
| 1 | 1 | Elargissements | Elargissements | OK |
| 2 | 2 | Plan du cours | Plan du cours | OK |
| 3 | 3 | Sommaire | Sommaire | OK |
| 4 | 4 | Les limites de l'IA – Histoire et aujourd'hui | Les limites de l'IA – Histoire et aujourd'hui | OK |
| 5 | 5 | L'informalité des comportements humains | L'informalité des comportements humains | OK |
| 6 | 6 | L'argument de l'incapacité | L'argument de l'incapacité | OK |
| 7 | 7 | L'objection mathématique | L'objection mathématique | OK |
| 8 | 8 | Mesurer l'intelligence | Mesurer l'intelligence | OK |
| 9 | 9 | Machines et pensée | Machines et pensée | OK |
| 10 | 10 | La chambre chinoise (Searle, 1980) | La chambre chinoise (Searle, 1980) | OK |
| 11 | 11 | Théories de la conscience (1/2) | Théories modernes de la conscience | FUSION |
| 12 | 12 | Théories de la conscience (2/2) | Integrated Information Theory | FUSION |
| 13 | 13 | L'éthique de l'IA | L'éthique de l'IA | OK |
| 14 | 14 | Armes autonomes létales | Armes autonomes létales | OK |
| 15 | 15 | Surveillance, sécurité et vie privée | Surveillance, sécurité et vie privée | OK |
| 16 | 16 | Biais et équité | Biais et équité | OK |
| 17 | 17 | Transparence et confiance | Transparence et confiance | OK |
| 18 | 18 | L'avenir de l'emploi | L'avenir de l'emploi | OK |
| 19 | 19 | Droits des robots | Droits des robots | OK |
| 20 | 20 | Sécurité de l'IA | Sécurité de l'IA | OK |
| 21 | 21 | Construire un futur éthique pour l'IA | Construire un futur éthique pour l'IA | OK |
| 22 | 22 | Questions? | Avenir de l'IA | DECALAGE |
| 23 | 23 | Avenir de l'IA | Progrès actuels de l'IA | DECALAGE |
| 24 | 24 | Composants - Capteurs et Actionneurs | Composants - Capteurs et Actionneurs | OK |
| 25 | 25 | Composants - Représentation du Monde | Composants - Représentation du Monde | OK |
| 26 | 26 | Composants - Sélection d'Actions | Composants - Sélection d'Actions | OK |
| 27 | 27 | Composants - Définir les Objectifs | Composants - Définir les Objectifs | OK |
| 28 | 28 | Apprentissage et Deep Learning | Apprentissage et Deep Learning | OK |
| 29 | 29 | Ressources et Infrastructures | Ressources et Infrastructures | OK |
| 30 | 30 | Architectures d'Agents | Architectures d'Agents | OK |
| 31 | 31 | IA Générale | IA Générale | OK |
| 32 | 32 | Ingénierie de l'IA | Ingénierie de l'IA | OK |
| 33 | 33 | L'IA Scientifique | L'IA Scientifique | OK |
| 34 | 34 | Souveraineté & Géopolitique | Souveraineté & Géopolitique | OK |
| 35 | 35 | Compression, Esthétique et Cosmologie | Compression, Esthétique et Cosmologie | OK |
| 36 | 36 | Questions? | Questions? | OK |
| 37 | 37 | Pour aller plus loin : Notebooks | Merci | DIFFERENT |
| 38 | - | (non présente dans PPTX) | - | ABSENT |
| 39 | - | (non présente dans PPTX) | - | ABSENT |
| 40 | - | Merci | - | ABSENT |

---

## Différences Structurelles

### 1. Slides "Questions?" Interstitielles

**Marp**: Deux slides "Questions?" interstitielles
- Slide 22: après "Construire un futur éthique"
- Slide 36: après "Compression, Esthétique et Cosmologie"

**PPTX**: Une seule slide "Questions?" à la fin (slide 36)

**Impact**: Le PPTX regroupe le contenu en une seule section continue, alors que le Marp crée une pause après la section éthique.

### 2. Section "Théories de la Conscience"

**Marp**: 2 slides séparées
- Slide 11: "Théories de la conscience (1/2)"
- Slide 12: "Théories de la conscience (2/2)"

**PPTX**: 2 slides avec organisation différente
- Slide 11: "Théories modernes de la conscience" (contenu fusionné)
- Slide 12: "Integrated Information Theory" (focus sur IIT)

**Impact**: Le PPTX réorganise le contenu pour mettre l'accent sur IIT séparément.

### 3. Section "Avenir de l'IA"

**Marp**:
- Slide 22: Questions?
- Slide 23: Avenir de l'IA (intro)

**PPTX**:
- Slide 22: Avenir de l'IA (fusion de l'intro avec le contenu)

**Impact**: Le PPTX condense l'introduction avec le contenu.

### 4. Slides Finales

**Marp**:
- Slide 37: Pour aller plus loin : Notebooks
- Slide 38: (vide)
- Slide 39: (vide)
- Slide 40: Merci

**PPTX**:
- Slide 37: Merci

**Impact**: Le Marp a 3 slides de plus, dont une slide "Pour aller plus loin" absente du PPTX.

---

## Contenu et Images

### Slide 20 - Sécurité de l'IA

**Marp**: Layout 2 colonnes avec 2 images
```markdown
<div class="columns">
<div class="col-left">
[Texte]
</div>
<div class="col-right">
![w:300](images/img_001.png)
![w:200](images/img_002.png)
</div>
</div>
```

**PPTX**: Contient des références à `Picture2.jpg` et `Picture4.jpg`

**Problème**: Les images référencées dans le Markdown (`images/img_001.png`, `images/img_002.png`) ne correspondent pas aux noms dans le PPTX (`Picture2.jpg`, `Picture4.jpg`).

**Images extraites**: 2 images trouvées dans `extracted/images/`
- `Picture2.jpg`
- `Picture4.jpg`

---

## Ajustements Nécessaires

### Critiques

1. **Images manquantes dans le Marp**
   - Les images `img_001.png` et `img_002.png` référencées dans le Markdown n'existent pas
   - Il faut utiliser les images extraites du PPTX: `Picture2.jpg` et `Picture4.jpg`

2. **Différence de structure "Questions?"**
   - Le PPTX n'a qu'une slide "Questions?" à la fin
   - Le Marp en a 2 (après éthique et à la fin)
   - **Recommandation**: Garder les 2 slides Marp pour meilleure pédagogie

3. **Slide "Pour aller plus loin" absente du PPTX**
   - Cette slide (références aux notebooks) est présente dans le Marp mais pas dans le PPTX
   - **Recommandation**: Garder cette slide dans le Marp

4. **Organisation "Théories de la conscience"**
   - Le PPTX organise différemment (IIT séparé)
   - **Recommandation**: Garder l'organisation Marp (2 slides équilibrées)

### Actions Requises

1. **Corriger les images de la slide 20**:
   ```markdown
   <!-- Remplacer -->
   ![w:300](images/img_001.png)
   ![w:200](images/img_002.png)

   <!-- Par -->
   ![w:300](../extracted/images/Picture2.jpg)
   ![w:200](../extracted/images/Picture4.jpg)
   ```

2. **Vérifier le nombre total de slides**
   - Marp: 40 slides
   - PPTX: 37 slides
   - Différence expliquée par: 1 slide "Questions?" + 1 slide "Pour aller plus loin" + 2 slides vides

---

## Note de Fidélité Globale

### Contenu Textuel: **9/10**

- Le contenu textuel est très fidèle
- Quelques réorganisations mineures (conscience, avenir de l'IA)
- Le Marp ajoute une slide "Pour aller plus loin" utile

### Structure et Organisation: **8/10**

- Bonne correspondance globale
- Le PPTX condense certaines sections
- Le Marp crée plus de pauses pédagogiques (slides "Questions?")

### Visuels et Images: **4/10**

- **Problème majeur**: Les références d'images dans le Markdown ne correspondent pas aux images extraites
- 2 images référencées mais non trouvées
- Les rendus PPTX sont incorrects (ne correspondent pas au contenu)

### Layout et Mise en Forme: **7/10**

- Le Marp utilise correctement le layout 2 colonnes pour la slide 20
- Les styles (couleurs, polices) sont fidèles au thème `ia101`
- Les différences de résolution (Marp: 1280x720, PPTX: 1920x1080) sont gérées correctement

---

## Note Finale: **7/10**

**Forces**:
- Contenu textuel fidèle
- Bonne organisation pédagogique
- Styles et cohérence visuelle corrects

**Faiblesses**:
- Images non synchronisées (références incorrectes)
- Rendus PPTX non fiables pour comparaison visuelle
- Différence de nombre de slides (40 vs 37)

---

## Recommandations

1. **Copier les images extraites** vers `_assets/images/` avec des noms cohérents
2. **Mettre à jour les références** dans `slides.md`
3. **Regénérer les rendus PPTX** avec un outil plus fiable que LibreOffice
4. **Documenter les différences structurelles** intentionnelles (slides "Questions?", "Pour aller plus loin")
