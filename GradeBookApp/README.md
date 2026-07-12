# GradeBookApp - Systeme de Notation Etudiants

Application de calcul et gestion des notes étudiants, **agnostique des écoles** : le moteur de notation est public, les configurations par cohorte (ECE / ESGF / EPITA / EPF) sont privées sur GDrive. Support du grading collégial (évaluation par les pairs).

## Vue d'ensemble

| Composant | Technologie | Description |
|-----------|-------------|-------------|
| Pipeline Python | Python 3.10+ | Calcul automatique des notes |
| Interface C# | .NET 9.0 | Visualisation et export |
| Configurations | Python modules | Paramétrage par cours |

### Fonctionnalités

- **Grading collégial** : Les étudiants s'évaluent entre eux, le professeur a un poids configurable
- **Fuzzy matching** : Correspondance tolérante pour les noms d'étudiants
- **Multi-projets** : Support de plusieurs projets par cours avec poids configurables
- **Intégration Google** : Lecture des évaluations depuis Google Forms/Sheets
- **Export Excel** : Génération de rapports avec mise en forme automatique

## Structure

```
GradeBookApp/
├── gradebook.py              # Pipeline Python principal
├── run_grading.py            # Script de lancement
├── Program.cs                # Interface C# .NET
├── StudentRecord.cs          # Modele etudiant
├── EvaluationRecord.cs       # Modele evaluation
├── ProjectModel.cs           # Modele projet
├── GradeBookApp.csproj       # Projet .NET
│
└── configs/                  # Package marqueur — configs sur GDrive (cf README)
    ├── __init__.py
    └── README.md             # Modèle GDrive + shim COURSIA_ROOT
```

> **Dépôt agnostique des écoles.** Les configs par cohorte (notes, emails,
> overrides) sont privées et vivent sur GDrive :
> `G:\Mon Drive\MyIA\Formation\<école>\<année>\grading\`, résolvant le moteur
> via `COURSIA_ROOT` (fallback `D:\CoursIA`). Détail : [configs/README.md](configs/README.md).

## Utilisation

### Pipeline Python

```bash
# Exécution avec configuration par défaut
python GradeBookApp/gradebook.py

# Exécution pour un cours spécifique (config sur GDrive, cf configs/README.md)
cd "G:\Mon Drive\MyIA\Formation\EPF\2026\grading"
python epf_2026_genai.py
```

### Interface C#

```bash
# Compilation
dotnet build GradeBookApp/GradeBookApp.csproj

# Execution avec fichiers de donnees
dotnet run --project GradeBookApp "chemin/inscriptions.csv" "chemin/evaluations.csv"
```

## Configuration

### Fichiers de donnees requis

| Fichier | Format | Contenu |
|---------|--------|---------|
| Inscriptions | CSV/Excel | Liste etudiants avec projets assignes |
| Evaluations | CSV (Google Forms) | Evaluations collegiales |

### Parametres globaux (gradebook.py)

```python
number_of_projects = 2           # Nombre de projets par cours
nb_eval_fields_per_project = [3, 3]  # Criteres par projet
professor_email = "..."          # Email du professeur
SIMILARITY_THRESHOLD = 80        # Seuil fuzzy matching (%)
TEACHER_WEIGHT = 1.0             # Poids note professeur (1.0 = 50%)
```

### Ajouter un nouveau cours

1. Creer la config sur GDrive : `Formation\<ecole>\<annee>\grading\<ecole>_YYYY_course.py`
2. Definir les chemins (GDrive) vers les fichiers de donnees
3. Configurer les parametres specifiques + le shim `COURSIA_ROOT` (cf [configs/README.md](configs/README.md))
4. Lancer depuis le dossier grading : `python <ecole>_YYYY_course.py`

## Workflow de notation

1. **Collecte** : Les etudiants remplissent le formulaire Google Forms
2. **Export** : Telecharger les reponses en CSV
3. **Calcul** : `python gradebook.py` calcule les moyennes
4. **Verification** : Interface C# pour visualiser les resultats
5. **Export** : Generation du fichier Excel final

## Dependances

### Python

```bash
pip install pandas numpy openpyxl rapidfuzz unidecode
```

### .NET

```bash
dotnet restore GradeBookApp/GradeBookApp.csproj
```

## Tests

Le moteur de notation est couvert par une suite de tests xUnit dans
[`GradeBookApp.Tests/`](../GradeBookApp.Tests/) (#1928) : pliage des accents
(`FoldAccents`), modèles `StudentRecord` / `ProjectModel` / `EvaluationRecord`.

```bash
dotnet test GradeBookApp.Tests
```

## Licence

Voir la licence du repository principal.
