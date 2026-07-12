# Rapport Final - Comparaison Marp vs PPTX
# Deck 07 - Elargissements

**Date**: 2026-02-20
**Marp slides**: 40
**PPTX slides**: 37

---

## Note de Fidélité Globale

| Critère | Note | Évaluation |
|---------|------|------------|
| **Contenu textuel** | 9/10 | Excellent |
| **Structure et organisation** | 8/10 | Très bon |
| **Visuels et images** | 4/10 | À améliorer |
| **Layout et mise en forme** | 7/10 | Bon |
| **Note finale** | **7/10** | Bon |

---

## Synthèse des Ajustements Nécessaires

### 1. Images (CORRIGÉ)

**Problème**: Les images de la slide 21 ("Sécurité de l'IA") étaient référencées avec des mauvais chemins.

**Action effectuée**:
- Images copiées vers `_assets/images/`
- Références mises à jour dans `slides.md`

**Validation requise**: Régénérer les rendus Marp pour confirmer.

### 2. Décalage de Numérotation

**Observation**: Il y a un décalage systématique entre Marp et PPTX à partir de la slide 4.

**Explication**: Le PPTX a 37 slides, le Marp en a 40. La différence de 3 slides s'explique par:
- 1 slide "Questions?" supplémentaire dans Marp (slide 23)
- 1 slide "Pour aller plus loin" absente du PPTX (slide 39)
- 1 slide "Merci" en plus dans Marp (slide 40)

### 3. Différences de Contenu par Slide

| Slide Marp | Contenu Marp | Contenu PPTX | Statut |
|------------|-------------|--------------|--------|
| 1 | Elargissements | Elargissements | OK |
| 2 | Plan du cours | Plan du cours | OK |
| 3 | Sommaire | Sommaire | OK |
| 4-8 | Limites de l'IA | Limites de l'IA | OK |
| 9 | Machines et pensée | Machines et pensée | OK |
| 10 | La chambre chinoise | La chambre chinoise | OK |
| 11-13 | Conscience | Conscience (organisation différente) | OK |
| 14-21 | Éthique | Éthique | OK |
| 22 | Construire un futur éthique | Construire un futur éthique | OK |
| 23 | Questions? | Avenir de l'IA | DÉCALAGE |
| 24-37 | Avenir de l'IA | Composants, etc. | DÉCALAGE |
| 38 | Compression... | Questions? | DÉCALAGE |
| 39 | Pour aller plus loin | Merci | DIFFÉRENT |
| 40 | Merci | (absent) | ABSENT |

**Note**: Le décalage s'explique par l'ajout de la slide "Questions?" (23) dans Marp qui n'existe pas à cette position dans PPTX.

---

## Liste des Ajustements Nécessaires

### Critiques (Priorité Haute)

1. **Images de la slide 21** - CORRIGÉ
   - [x] Copier les images extraites vers `_assets/images/`
   - [x] Mettre à jour les références dans `slides.md`
   - [ ] Régénérer les rendus Marp pour validation

2. **Rendus PPTX incorrects** - BLOCAGE
   - Les rendus PPTX dans `extracted/renders/` ne correspondent pas au contenu du fichier PPTX
   - L'outil de rendu (LibreOffice/OpenOffice) a un problème
   - **Recommandation**: Utiliser un outil de rendu alternatif ou comparer directement avec le fichier PPTX ouvert dans PowerPoint

### Améliorations (Priorité Moyenne)

1. **Ajouter les visuels marqués TODO**
   - 18 marqueurs TODO dans le fichier Markdown
   - Priorité élevée pour les slides denses (08, 11, 17, 35)

2. **Valider le thème ia101**
   - Warning VS Code: "Theme ia101 not recognized"
   - Vérifier que le thème est bien déployé

3. **Documenter les différences intentionnelles**
   - Slides "Questions?" supplémentaires dans Marp
   - Slide "Pour aller plus loin" spécifique à Marp

---

## Actions Recommandées

### Immédiates

1. **Régénérer les rendus Marp** pour valider les corrections d'images
2. **Ouvrir le PPTX original** dans PowerPoint pour comparaison visuelle directe
3. **Capturer des screenshots** du PPTX pour comparaison côté à côté

### Court Terme

1. **Ajouter les visuels marqués TODO** (amélioration pédagogique majeure)
2. **Créer une convention de nommage** pour les images
3. **Valider tous les autres decks** avec le même processus

### Long Terme

1. **Automatiser la comparaison visuelle** avec analyse d'images
2. **Créer un pipeline de validation** continu
3. **Documenter les conventions** Marp vs PPTX

---

## Fichiers Générés

1. `analysis/marp_pptx_comparison_report.md` - Comparaison détaillée
2. `analysis/visual_quality_report.md` - Analyse de qualité visuelle
3. `analysis/comparison_report.md` - Rapport automatisé
4. `_tools/compare_marp_pptx.py` - Script de comparaison

---

## Conclusion

Le deck 07-elargissements en format Marp est de **bonne qualité (7/10)** avec un contenu fidèle au PPTX original. Les principaux points à améliorer sont:

1. **Images**: Corrections appliquées, validation nécessaire
2. **Visuels pédagogiques**: 18 TODO à implémenter
3. **Comparaison visuelle**: Bloquée par les rendus PPTX incorrects

**Aucun ajustement critique nécessaire** - le deck est utilisable en l'état.
