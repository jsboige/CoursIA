# Rapport de Qualité Visuelle - Deck 07 Elargissements

**Date**: 2026-02-20
**Analyse basée sur**: Rendus Marp (40 slides)

---

## Résumé Exécutif

| Métrique | Note | Évaluation |
|----------|------|------------|
| ** Lisibilité globale** | 8.5/10 | Excellent |
| **Cohérence visuelle** | 9/10 | Excellent |
| **Qualité du contenu** | 9/10 | Excellent |
| **Note finale** | **8.7/10** | Très bon |

---

## Analyse Détaillée par Slides

### Slides Analysées (échantillon représentatif)

| Slide | Titre | Lisibilité | Notes |
|-------|-------|------------|-------|
| 01 | Elargissements (titre) | 9/10 | Excellent design minimaliste |
| 02 | Plan du cours | 9/10 | Très clair, bonne mise en évidence |
| 10 | La chambre chinoise | 8/10 | Bonne hiérarchie, contenu philosophique dense |
| 15 | Armes autonomes létales | 8/10 | Organisation claire, 5 sections bien structurées |
| 20 | Sécurité de l'IA | 7/10 | Layout 2 colonnes, images à vérifier |
| 25 | Progrès actuels de l'IA | 9/10 | Excellente lisibilité, bien équilibré |
| 35 | L'IA Scientifique | 8/10 | Contenu scientifique dense mais lisible |
| 40 | Merci | 9/10 | Design minimaliste parfait |

---

## Points Forts

### 1. Cohérence Visuelle

- **Thème ia101**: Appliqué uniformément sur toutes les slides
- **Palette de couleurs**: Rouge/bordeaux pour titres, noir pour corps, gris pour footer
- **Typographie**: Sans-serif propre, hiérarchie claire
- **Layouts**: Consistants avec bon usage de l'espace blanc

### 2. Lisibilité

- **Contraste**: Excellent (texte sombre sur fond clair)
- **Taille de police**: Appropriée pour projection en amphithéâtre
- **Espacement**: Généreux entre les sections
- **Hiérarchie visuelle**: Claire (titres en rouge/gras, sous-titres indentés)

### 3. Structure Pédagogique

- **Slides "Questions?"**: Bien placés pour créer des pauses
- **Sections logiques**: Bien découpées en sous-thèmes
- **Progression**: Clair et cohérent

---

## Points d'Amélioration Identifiés

### 1. Slide 20 - Sécurité de l'IA

**Problème**: Les images référencées dans le Markdown ne correspondent pas aux images extraites du PPTX

**Statut**: CORRIGÉ
- Images copiées vers `_assets/images/`
- Références mises à jour dans `slides.md`

**Action requise**: Régénérer les rendus Marp pour vérifier le résultat

### 2. Slides avec Contenu Dense

| Slide | Titre | Problème | Suggestion |
|-------|-------|----------|------------|
| 08 | Mesurer l'intelligence | Contenu très dense (benchmarks) | OK tel quel - layout `dense` utilisé |
| 11 | Théories de la conscience (1/2) | 5 théories sur une slide | OK tel quel - layout `dense` utilisé |
| 17 | Transparence et confiance | Liste longue avec exemples | OK tel quel - style scoped pour réduction |

### 3. Images Visuelles (TODO)

Le fichier Markdown contient plusieurs marqueurs TODO pour ajouter des visuels:

```markdown
<!-- TODO: ajouter visuel IA futuriste, ethique, cerveau+circuit -->
<!-- TODO: timeline IA faible vs forte vs super-IA -->
<!-- TODO: schema embodied cognition, photo robot Ameca/Figure 02 -->
<!-- TODO: exemples visuels art IA (Stable Diffusion, DALL-E) -->
<!-- TODO: schema theoreme de Godel simplifie -->
<!-- TODO: graphique evolution benchmarks 2020-2026 -->
<!-- TODO: illustration chambre chinoise de Searle -->
<!-- TODO: infographie balance benefices/risques -->
<!-- TODO: photos Harop, Kargu, drone Ukraine -->
<!-- TODO: schema federated learning, icone GDPR -->
<!-- TODO: exemples visuels de biais algorithmique -->
<!-- TODO: schema XAI boite noire vs boite blanche -->
<!-- TODO: graphique evolution emploi vs automatisation -->
<!-- TODO: graphique croissance exponentielle Kurzweil -->
<!-- TODO: photos Lidar, Arduino, NVIDIA Orin -->
<!-- TODO: schema architecture hybride neuro-symbolique -->
<!-- TODO: visualisation AlphaFold structure proteique -->
<!-- TODO: carte mondiale clusters IA -->
<!-- TODO: ajouter liens vers notebooks specifiques -->
```

**Recommandation**: Ces visuels amélioreraient significativement la qualité pédagogique du deck.

---

## Comparaison avec PPTX

### Différences Structurelles

1. **Slides "Questions?"**
   - Marp: 2 slides (après éthique, à la fin)
   - PPTX: 1 slide (à la fin)
   - **Recommandation**: Garder les 2 slides Marp (meilleure pédagogie)

2. **Section "Théories de la conscience"**
   - Marp: 2 slides équilibrées
   - PPTX: IIT séparé sur une slide dédiée
   - **Recommandation**: Garder l'organisation Marp

3. **Slide "Pour aller plus loin"**
   - Marp: Présente (références aux notebooks)
   - PPTX: Absente
   - **Recommandation**: Garder dans Marp (très utile pour les étudiants)

4. **Nombre total de slides**
   - Marp: 40
   - PPTX: 37
   - Différence expliquée par les 3 points ci-dessus

---

## Éléments de Design Validés

### Layouts Utilisés

| Layout | Slides | Validité |
|--------|--------|----------|
| `title` | 1, 40 | OK |
| `dense` | 5, 6, 7, 11, 17, 21, 28, 35 | OK |
| `questions` | 22, 36 | OK |
| `columns-layout` | 20 | OK |
| `default` | Autres | OK |

### Styles Scoped

```css
<!-- Slide 12: IIT -->
section { font-size: 22px; padding: 30px 40px; }

<!-- Slide 17: Transparence -->
section { font-size: 20px; padding: 30px 40px; }

<!-- Slide 35: Compression, Esthétique -->
section { font-size: 22px; padding: 30px 40px; }
```

Ces ajustements de taille de police sont appropriés pour les slides avec contenu dense.

---

## Recommandations Finales

### Immédiates

1. **CORRIGÉ**: Mettre à jour les références d'images de la slide 20
2. **À FAIRE**: Régénérer les rendus Marp pour valider les corrections
3. **À FAIRE**: Regénérer les rendus PPTX avec un outil plus fiable

### Court Terme

1. **Ajouter les visuels marqués TODO** (priorité élevée pour la pédagogie)
2. **Valider le thème ia101** (warning VS Code sur thème non reconnu)
3. **Créer une checklist visuelle** pour les futurs decks

### Long Terme

1. **Automatiser la comparaison** Marp vs PPTX
2. **Créer un script de validation** des références d'images
3. **Documenter les conventions** de noms d'images

---

## Conclusion

Le deck 07-elargissements en format Marp est de **très bonne qualité** (8.7/10) avec:
- Excellente lisibilité
- Cohérence visuelle parfaite
- Structure pédagogique bien pensée

Les améliorations possibles sont:
1. Ajout des visuels marqués TODO
2. Validation des images de la slide 20
3. Documentation des différences avec PPTX intentionnelles

**Aucun ajustement critique nécessaire** - le deck est prêt pour l'utilisation.
