# SymbolicAI - Notebooks TweetyProject

Collection de notebooks Jupyter pour l'apprentissage de l'IA symbolique avec la bibliothèque Java [TweetyProject](https://tweetyproject.org/).

## 📚 Série Tweety - Notebooks Principaux

**Statut**: ✅ Série complète validée (100% - 0 erreurs)

Explorez les logiques symboliques et l'argumentation computationnelle avec ces 7 notebooks progressifs:

### 1. [Tweety-1-Setup.ipynb](Tweety-1-Setup.ipynb) - Configuration ⚙️
**Durée**: 10 min | **Prérequis**: Aucun

Installation et configuration de l'environnement complet:
- Installation automatique Python + JPype + Tweety
- Téléchargement JDK portable (Zulu 17)
- Téléchargement JARs TweetyProject v1.28
- Configuration outils externes (Clingo, SPASS)
- Démarrage et test JVM

**IMPORTANT**: À exécuter en premier, obligatoire pour tous les autres notebooks.

### 2. [Tweety-2-Basic-Logics.ipynb](Tweety-2-Basic-Logics.ipynb) - Logiques de Base 🔤
**Durée**: 30 min | **Prérequis**: Tweety-1

- **Logique Propositionnelle (PL)**: Syntaxe, parsing, mondes possibles, solveurs SAT
- **Logique du Premier Ordre (FOL)**: Signatures, sorts, prédicats, raisonnement

### 3. [Tweety-3-Advanced-Logics.ipynb](Tweety-3-Advanced-Logics.ipynb) - Logiques Avancées 🧮
**Durée**: 20 min | **Prérequis**: Tweety-1

- **Logique de Description (DL)**: ABox, TBox, concepts, rôles
- **Logique Modale (ML)**: Opérateurs modaux, sémantiques Kripke
- **QBF**: Formules booléennes quantifiées
- **Logique Conditionnelle (CL)**

### 4. [Tweety-4-Belief-Revision.ipynb](Tweety-4-Belief-Revision.ipynb) - Révision de Croyances 🔄
**Durée**: 25 min | **Prérequis**: Tweety-1

- Révision de croyances multi-agents (CrMas)
- Mesures d'incohérence (distance, contension, fuzzy)
- Énumération MUS (Minimal Unsatisfiable Subsets)
- MaxSAT avec Open-WBO

### 5. [Tweety-5-Abstract-Argumentation.ipynb](Tweety-5-Abstract-Argumentation.ipynb) - Argumentation Abstraite 🎯
**Durée**: 30 min | **Prérequis**: Tweety-1

- Cadres d'argumentation de Dung
- Sémantiques: Grounded, Preferred, Stable, Complete, CF2
- Génération et apprentissage de cadres
- Raisonneurs alternatifs

### 6. [Tweety-6-Structured-Argumentation.ipynb](Tweety-6-Structured-Argumentation.ipynb) - Argumentation Structurée 🏗️
**Durée**: 30 min | **Prérequis**: Tweety-1, Tweety-5

- **ASPIC+**: Construction PL/FOL, conversion vers Dung
- **DeLP**: Defeasible Logic Programming
- **ABA**: Assumption-Based Argumentation
- **Argumentation Déductive**
- **ASP**: Answer Set Programming avec Clingo

### 7. [Tweety-7-Advanced-Argumentation.ipynb](Tweety-7-Advanced-Argumentation.ipynb) - Argumentation Avancée 🚀
**Durée**: 40 min | **Prérequis**: Tweety-1, Tweety-5

- Abstract Dialectical Frameworks (ADF)
- Frameworks bipolaires (support + attaque)
- Frameworks pondérés, sociaux, SetAF
- Frameworks étendus (attaques sur attaques)
- Sémantiques ranking
- Argumentation probabiliste

**Durée totale série**: ~3h10 (lecture + exécution)

---

## 📂 Structure du Répertoire

```
SymbolicAI/
├── Tweety-1-Setup.ipynb                      # Configuration environnement
├── Tweety-2-Basic-Logics.ipynb               # PL + FOL
├── Tweety-3-Advanced-Logics.ipynb            # DL, ML, QBF
├── Tweety-4-Belief-Revision.ipynb            # Révision, MUS
├── Tweety-5-Abstract-Argumentation.ipynb     # Dung
├── Tweety-6-Structured-Argumentation.ipynb   # ASPIC+, DeLP, ABA
├── Tweety-7-Advanced-Argumentation.ipynb     # ADF, Ranking
│
├── scripts/                                   # Scripts utilitaires
│   ├── verify_all_tweety.py                  # Vérification complète
│   ├── reorganize_tweety.py                  # Réorganisation notebooks
│   ├── install_clingo.py                     # Installation Clingo
│   └── README.md
│
├── reports/                                   # Rapports de qualité
│   ├── TWEETY_QUALITY_REPORT.md              # Rapport complet 2026-01-23
│   └── README.md
│
├── archive/                                   # Versions historiques
│   ├── Tweety.ipynb                          # Original monolithique
│   └── README.md
│
├── libs/                                      # JARs TweetyProject (auto-téléchargés)
├── resources/                                 # Fichiers de données (.aba, .aspic, etc.)
├── ext_tools/                                 # Outils externes (Clingo, SPASS)
├── jdk-17-portable/                          # JDK portable (auto-téléchargé)
└── README.md                                  # Ce fichier
```

---

## 🚀 Démarrage Rapide

### Installation (Première Fois)

1. **Cloner le dépôt** (si pas déjà fait):
```bash
git clone https://github.com/jsboige/CoursIA.git
cd CoursIA/MyIA.AI.Notebooks/SymbolicAI
```

2. **Lancer Jupyter**:
```bash
jupyter notebook
```

3. **Exécuter Tweety-1-Setup.ipynb** en entier (cellule par cellule)
   - Installe automatiquement: Python packages, JDK, JARs Tweety, outils
   - Durée: ~5-10 minutes selon connexion internet

4. **Explorer les notebooks 2-7** dans l'ordre ou à la carte

### Utilisation Quotidienne

Si l'environnement est déjà configuré:
1. Lancer Jupyter
2. Ouvrir directement le notebook souhaité (Tweety-2 à Tweety-7)
3. L'initialisation JVM se fait automatiquement dans chaque notebook

---

## 🧪 Vérification et Tests

### Vérifier l'intégrité de la série

```bash
cd scripts/
python verify_all_tweety.py
```

**Résultats attendus**: 7/7 notebooks OK, 0 erreurs

### Tests individuels avec Papermill

```bash
python -m papermill Tweety-1-Setup.ipynb output.ipynb --kernel python3
```

---

## 📊 Qualité et Statut

### Dernière Vérification: 2026-01-23

| Notebook | Cellules | Durée | Statut |
|----------|----------|-------|--------|
| Tweety-1 | 7 | 5s | ✅ VALIDE |
| Tweety-2 | 4 | 170s | ✅ VALIDE |
| Tweety-3 | 4 | 8s | ✅ VALIDE |
| Tweety-4 | 5 | 12s | ✅ VALIDE |
| Tweety-5 | 5 | 15s | ✅ VALIDE |
| Tweety-6 | 6 | 18s | ✅ VALIDE |
| Tweety-7 | 9 | 25s | ✅ VALIDE |
| **TOTAL** | **40** | **~5min** | **✅ 100%** |

**Rapport détaillé**: [reports/TWEETY_QUALITY_REPORT.md](reports/TWEETY_QUALITY_REPORT.md)

---

## 🛠️ Dépendances

### Automatiquement Installées

- **Python packages**: jpype1, requests, tqdm, clingo
- **JDK**: Zulu 17 portable (auto-téléchargé)
- **TweetyProject**: v1.28 (23 JARs - core + modules)
- **Clingo**: v5.4.0 (Windows/Linux auto-install)

### Optionnelles (Améliorent l'Expérience)

- **SPASS**: Prouveur FOL/ML (installation manuelle recommandée)
- **EProver**: Prouveur FOL (installation manuelle)
- **Open-WBO**: Solveur MaxSAT (installation manuelle)

---

## 📖 Ressources

- **TweetyProject**: https://tweetyproject.org/
- **Documentation**: http://tweetyproject.org/doc/
- **GitHub**: https://github.com/TweetyProjectTeam/TweetyProject
- **JPype**: https://jpype.readthedocs.io/

---

## 🤝 Contribution

Cette série a été créée et vérifiée en Janvier 2026. Pour signaler des problèmes ou suggérer des améliorations:

1. Utiliser `scripts/verify_all_tweety.py` pour identifier les régressions
2. Consulter `reports/TWEETY_QUALITY_REPORT.md` pour l'état de référence
3. Tester localement avant de commiter

---

## 📜 Licence

Ce matériel pédagogique fait partie du projet CoursIA.
Voir LICENSE à la racine du dépôt pour détails.

---

**Dernière mise à jour**: 2026-01-23
**Auteur**: Jean-Sébastien Bevilacqua (jsboige@gmail.com)
**Vérification**: Claude Code (Anthropic)
