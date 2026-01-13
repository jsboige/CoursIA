# Configurations GradeBook

Ce répertoire contient les configurations spécifiques pour chaque classe/formation.

## Structure

Chaque configuration est un module Python autonome qui définit un dictionnaire `CONFIG` et peut être exécuté directement.

```
configs/
├── __init__.py              # Package Python
├── README.md                # Ce fichier
├── epf_2026_ml.py          # Config EPF MIS 2026 - Machine Learning
└── epf_2026_genai.py       # Config EPF GenAI 2026 - IA Générative
```

## Configurations disponibles

### EPF MIS 2026 - Machine Learning (`epf_2026_ml.py`)
- **Cours**: MSMIS5IN11 - IA probabiliste et machine learning
- **Moyenne cible**: 15.5/20
- **Écart-type cible**: 2.0
- **Pondération**: 50% professeur / 50% étudiants

### EPF GenAI 2026 - IA Générative (`epf_2026_genai.py`)
- **Cours**: MSMIN5IN52 - IA Générative et Chatbots
- **Moyenne cible**: 15.0/20
- **Écart-type cible**: 2.0
- **Pondération**: 50% professeur / 50% étudiants
- **Groupes blacklistés**: Gestion des doublons connus

## Utilisation

### Méthode 1: Exécution directe (recommandé)

Depuis le répertoire `configs/`:
```bash
cd GradeBookApp/configs
python epf_2026_ml.py
python epf_2026_genai.py
```

### Méthode 2: Module Python

Depuis la racine du projet:
```bash
python -m GradeBookApp.configs.epf_2026_ml
python -m GradeBookApp.configs.epf_2026_genai
```

### Méthode 3: Import programmatique

```python
from GradeBookApp.configs.epf_2026_ml import CONFIG
from gradebook import run_pipeline

# Modifier la config si besoin
CONFIG['target_mean'] = 16.0

# Exécuter le pipeline
run_pipeline(CONFIG)
```

## Structure du dictionnaire CONFIG

Chaque configuration doit définir les clés suivantes:

```python
CONFIG = {
    # Identification
    'nom_classe': str,  # Nom de la classe/formation
    
    # Chemins des fichiers (absolus ou relatifs)
    'inscriptions_path': str,      # CSV des inscriptions
    'evaluations_path': str,       # CSV des évaluations
    'output_path': str,            # Fichier Excel de sortie
    
    # Mapping des colonnes CSV → champs internes
    'column_mapping': {
        "Prénom": "prenom",
        "Nom de famille": "nom",
        "Projet": "sujet_projet_1"  # ou "Sujet"
    },
    
    # Paramètres de redressement statistique
    'target_mean': float,          # Moyenne cible (ex: 15.0)
    'target_std': float,           # Écart-type cible (ex: 2.0)
    
    # Paramètres de pondération
    'teacher_weight': float,       # 1.0 = 50%/50%, 2.0 = 66%/33%
    'professor_email': str,        # Email du professeur
    
    # Groupes blacklistés (optionnel)
    'blacklisted_groups': list     # Liste des noms de groupes à exclure
}
```

## Créer une nouvelle configuration

### Étape 1: Créer le fichier

Dupliquer une configuration existante:
```bash
cd GradeBookApp/configs
cp epf_2026_ml.py nouvelle_classe.py
```

### Étape 2: Adapter le CONFIG

Modifier les paramètres selon votre classe:
```python
CONFIG = {
    'nom_classe': 'Nouvelle Classe 2026',
    'inscriptions_path': r"chemin/vers/inscriptions.csv",
    'evaluations_path': r"chemin/vers/evaluations.csv",
    'output_path': r"chemin/vers/Notes_Finales.xlsx",
    # ... autres paramètres
}
```

### Étape 3: Tester

```bash
python nouvelle_classe.py
```

### Étape 4: Mettre à jour `__init__.py`

Ajouter le nouveau module dans `__all__`:
```python
__all__ = ['epf_2026_ml', 'epf_2026_genai', 'nouvelle_classe']
```

## Notes techniques

### Gestion des chemins

Les configurations utilisent des chemins absolus vers Google Drive pour faciliter l'exécution.
Si Google Drive n'est pas monté, le pipeline créera les fichiers localement.

### Imports dynamiques

Les configurations ajoutent automatiquement le répertoire parent au `sys.path`:
```python
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent.parent))
from gradebook import run_pipeline
```

Cela permet d'importer [`gradebook.py`](../gradebook.py) même depuis le sous-répertoire.

### Mapping des colonnes

Le `column_mapping` permet de gérer les variations de nommage entre les CSV:
- EPF MIS utilise `"Sujet"` pour le projet
- EPF GenAI utilise `"Projet"` pour le projet

Les deux sont mappés vers `"sujet_projet_1"` en interne.

## Dépannage

### Erreur "No module named 'gradebook'"

Vérifiez que vous exécutez depuis le bon répertoire ou que le `sys.path` est correctement configuré.

### Fichier Excel non créé

Le chemin Google Drive peut être inaccessible. Vérifiez les logs pour le chemin de fallback local.

### Doublons détectés

Ajoutez les groupes problématiques dans `blacklisted_groups`:
```python
'blacklisted_groups': [
    "Groupe_problematique_1",
    "Groupe_problematique_2"
]
```

## Voir aussi

- [`gradebook.py`](../gradebook.py) - Pipeline principal
- [`run_grading.py`](../run_grading.py) - Point d'entrée historique
