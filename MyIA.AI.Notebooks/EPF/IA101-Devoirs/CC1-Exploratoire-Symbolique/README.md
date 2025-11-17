# CC1 - IA Exploratoire et Symbolique
## Système de Diagnostic Médical Multi-Contraintes pour le Diabète de Type 2

### 📋 Vue d'Ensemble

Ce projet implémente un système de diagnostic médical intelligent combinant quatre approches algorithmiques complémentaires :

1. **Agent de Diagnostic Rationnel** : Classification basée sur des règles cliniques
2. **Algorithme A*** : Recherche informée dans l'espace d'états diagnostiques
3. **Algorithmes Génétiques** : Optimisation évolutionnaire des paramètres diagnostiques
4. **Solveur Z3** : Validation par contraintes des protocoles thérapeutiques

### 🎯 Objectifs Pédagogiques

- Maîtriser les algorithmes de recherche (BFS, DFS, A*)
- Comprendre la programmation par contraintes (Z3, CSP)
- Implémenter des algorithmes génétiques pour l'optimisation
- Analyser la complexité et les performances
- Appliquer l'IA au domaine biomédical (diabète type 2)

### 📁 Structure du Projet

```
CC1-Exploratoire-Symbolique/
├── CC1-Diagnostic-Medical.ipynb          # Template étudiant (à compléter)
├── enonce/
│   └── sujet.md                         # Sujet du devoir
├── data/
│   └── patients.csv                      # Données de test (10 patients)
└── README.md                             # Ce fichier
```

### 🔧 Installation

#### Prérequis

- **Python 3.8+** (recommandé: Python 3.9 ou 3.10)
- **Jupyter Notebook** ou **JupyterLab**
- **Conda** (optionnel mais recommandé)

#### Option 1 : Installation avec Conda (recommandé)

```bash
# Créer un environnement virtuel
conda create -n cc1-diagnostic python=3.9
conda activate cc1-diagnostic

# Installer Jupyter
conda install jupyter notebook

# Installer les dépendances
pip install numpy pandas matplotlib seaborn z3-solver
```

#### Option 2 : Installation avec pip

```bash
# Créer un environnement virtuel
python -m venv venv

# Activer l'environnement
# Windows:
venv\Scripts\activate
# Linux/Mac:
source venv/bin/activate

# Installer Jupyter et les dépendances
pip install jupyter notebook numpy pandas matplotlib seaborn z3-solver
```

### 📦 Dépendances Requises

| Package | Version | Description |
|---------|---------|-------------|
| `numpy` | >= 1.20.0 | Calculs scientifiques |
| `pandas` | >= 1.3.0 | Manipulation de données |
| `matplotlib` | >= 3.4.0 | Visualisation |
| `seaborn` | >= 0.11.0 | Visualisation statistique |
| `z3-solver` | >= 4.8.0 | Solveur de contraintes SMT |

### 🚀 Utilisation

#### 1. Pour les Étudiants

```bash
# Démarrer Jupyter
jupyter notebook

# Ouvrir le fichier
CC1-Diagnostic-Medical.ipynb
```

**Instructions** :
1. Lisez attentivement chaque cellule markdown (théorie et explications)
2. Complétez les cellules de code marquées avec `# TODO`
3. Testez chaque partie avant de passer à la suivante
4. Utilisez les exemples fournis pour valider votre implémentation

#### 2. Pour les Évaluateurs

```bash
# Ouvrir le notebook corrigé
jupyter notebook CC1-Diagnostic-Medical-corrigé.ipynb
```

**Actions** :
1. Exécuter toutes les cellules (`Cell → Run All`)
2. Vérifier que tous les tests passent
3. Comparer avec les travaux étudiants
4. Utiliser la grille d'évaluation du fichier `enonce/sujet.md`

### 📊 Données de Test

Le fichier `data/patients.csv` contient 10 patients avec des profils variés :

| ID | Nom | Âge | Glycémie Jeun | HbA1c | Type |
|----|-----|-----|---------------|-------|------|
| 1 | Alice | 45 | 110.0 | 6.8 | Pré-diabète |
| 2 | Bob | 58 | 140.0 | 8.2 | Diabète Type 2 |
| 3 | Claire | 35 | 90.0 | 5.5 | Normal |
| ... | ... | ... | ... | ... | ... |

**Format CSV** :
- **Colonnes** : id, nom, age, glycemie_jeun, glycemie_postprandiale, hba1c, symptomes, antecedents, pression_arterielle, imc
- **Symptômes** : Séparés par `;` (exemple: `fatigue;soif intense`)
- **Antécédents** : Séparés par `;` (exemple: `hypertension;surpoids`)

### 🧪 Tests et Validation

#### Tests Intégrés

Le notebook corrigé inclut des tests automatisés pour valider chaque composant :

```python
# Exécuter la suite de tests complète
tests_automatises()
```

#### Tests Manuels

Pour tester individuellement chaque partie :

```python
# Test Agent de Diagnostic
tester_agent_diagnostic()

# Test Performance A*
tester_performance_astar()

# Test Convergence Génétique
tester_convergence_genetique()

# Test Validation Z3
tester_validation_z3()
```

#### Exécution du Pipeline Complet

```python
# Exécuter le pipeline d'intégration
main()
```

### ⚠️ Problèmes Courants et Solutions

#### 1. ImportError: No module named 'z3'

```bash
# Solution
pip install z3-solver
```

#### 2. FileNotFoundError: data/patients.csv

```bash
# Vérifier le chemin relatif
# Le notebook doit être exécuté depuis le répertoire CC1-Exploratoire-Symbolique/
```

#### 3. Erreur de convergence A*

```python
# Augmenter le nombre max d'itérations
astar = AStarDiagnostic()
# Dans la méthode rechercher_diagnostic_optimal, modifier:
max_iterations = 2000  # au lieu de 1000
```

#### 4. Z3 Solver très lent

```python
# Simplifier les contraintes ou réduire le timeout
self.solver.set("timeout", 5000)  # 5 secondes
```

### 📚 Ressources Complémentaires

#### Théorie IA

- **Russell & Norvig** : *Artificial Intelligence: A Modern Approach*, Chapitres 1, 3, 4, 6
- **Dechter** : *Learning While Searching in Constraint-Satisfaction Problems*
- **Pearl** : *Heuristics: Intelligent Search Strategies*

#### Algorithmes Spécifiques

- **A* Search** : https://en.wikipedia.org/wiki/A*_search_algorithm
- **Genetic Algorithms** : https://en.wikipedia.org/wiki/Genetic_algorithm
- **Z3 Solver** : https://github.com/Z3Prover/z3
- **Constraint Programming** : https://en.wikipedia.org/wiki/Constraint_programming

#### Applications Médicales

- **ADA/EASD Guidelines** : Standards diabète type 2
- **WHO Diabetes** : Recommandations internationales
- **Medical CSP** : Programmation par contraintes en santé

### 📈 Critères d'Évaluation

Chaque cellule a remplir ou compléter sera évaluée pour constituer la note finale sur 20.

**Bonus** (jusqu'à +2 points) :
- Innovation algorithmique
- Interface utilisateur
- Tests exhaustifs
- Performance exceptionnelle

### 🎓 Compétences Développées

À la fin de ce devoir, vous aurez acquis :

✅ Maîtrise des algorithmes de recherche informée (A*)
✅ Compréhension de la programmation par contraintes (Z3)
✅ Pratique des algorithmes génétiques
✅ Application de l'IA au domaine biomédical
✅ Analyse de complexité et optimisation
✅ Documentation technique et tests

---

**Bonne chance avec votre implémentation !** 🎯