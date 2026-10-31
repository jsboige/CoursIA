# Archive - Notebooks Tweety

Ce répertoire contient les anciennes versions et fichiers historiques de la série Tweety.

## Fichiers Archivés

### Tweety.ipynb (Original Monolithique)
**Date d'archivage**: 2026-01-23
**Raison**: Remplacé par la série de notebooks thématiques

**Contenu original** (monolithe markdown + code):
- Configuration environnement (JDK, JPype, JARs)
- Logiques fondamentales (PL, FOL, DL, ML, QBF, CL)
- Révision de croyances et incohérence
- Argumentation abstraite (Dung)
- Argumentation structurée (ASPIC+, DeLP, ABA, ASP)
- Argumentation avancée (ADF, Bipolaire, Ranking, Probabiliste)

**Nouvelle structure** (notebooks séparés):
1. **Tweety-01-Setup-Python.ipynb** - Configuration environnement uniquement
2. **Tweety-02-Basic-Logics-Python.ipynb** - PL et FOL
3. **Tweety-3-Advanced-Logics.ipynb** - DL, Modale, QBF
4. **Tweety-4-Belief-Revision.ipynb** - Révision de croyances, MUS
5. **Tweety-5-Abstract-Argumentation.ipynb** - Cadres de Dung
6. **Tweety-06-Structured-Argumentation-Python.ipynb** - ASPIC+, DeLP, ABA, ASP
7. **Tweety-7-Advanced-Argumentation.ipynb** - ADF, Ranking, Probabiliste

**Avantages de la nouvelle structure**:
- ✅ Modules indépendants et réutilisables
- ✅ Navigation plus claire (liens entre notebooks)
- ✅ Temps de chargement réduits
- ✅ Meilleure organisation pédagogique
- ✅ Initialisation JVM optimisée par notebook

**Vérification de la migration**:
- Original: le code du monolithe
- Nouveaux: le code du monolithe, plus les cellules d'init JVM réparties dans les notebooks suivants
- ✅ Tout le contenu a été migré avec succès

## Référence Historique

Ce fichier est conservé pour référence historique et peut être utile pour:
- Comparer l'approche monolithique vs modulaire
- Retrouver d'anciennes versions de code
- Comprendre l'évolution de la série

**Pour utiliser la série Tweety, consultez les notebooks dans le répertoire parent.**
