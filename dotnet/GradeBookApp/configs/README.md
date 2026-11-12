# Configurations GradeBook — déplacées sur GDrive

> **Le dépôt CoursIA est agnostique des écoles.** Les configurations de notation
> par cohorte (notes, emails étudiants, overrides, ajustements manuels) sont des
> **données privées** : elles ne vivent **plus** dans ce dépôt public. Elles sont
> sur Google Drive, point d'entrée unique de tout le contenu spécifique aux écoles.

## Où vivent les configs

```
G:\Mon Drive\MyIA\Formation\<école>\<année>\grading\
```

Exemples (2026) :

| École / cohorte | Dossier GDrive | Fichiers |
|-----------------|----------------|----------|
| EPITA-IS — PrCon | `Formation\Epita\2026\grading\` | `prcon_2026_config.py`, `compile_prcon_2026.py`, `epf_2026_prcon.py` (collégiale, *superseded*) |
| EPF — GenAI / MIS / Min1 / Min2 | `Formation\EPF\2026\grading\` | `epf_2026_genai.py`, `epf_2026_ml.py`, `epf_2026_min1.py`, `epf_2026_min2.py` |
| ECE | `Formation\ECE\2026\grading\` | doc pipeline = `…\ECE\2026\grading\ece-grading.md` (GDrive, privé) |
| ESGF | `Formation\ESGF\2026\grading\` | doc pipeline = `…\ESGF\2026\grading\esgf-grading.md` (GDrive, privé) |

## Ce qui reste dans le dépôt (moteur agnostique)

- [`gradebook.py`](../gradebook.py) — pipeline de notation (collégiale, redressement statistique, multi-épreuve)
- [`run_grading.py`](../run_grading.py) — orchestrateur historique
- `configs/__init__.py` — marqueur de package (vide, configs sur GDrive)

## Résolution du moteur depuis GDrive — `COURSIA_ROOT`

Chaque config sur GDrive retrouve le moteur du dépôt via la variable
d'environnement `COURSIA_ROOT` (fallback `D:\CoursIA`) :

```python
if __name__ == '__main__':
    import sys, os
    from pathlib import Path
    # Engine lives in the repo (school-agnostic); resolved via COURSIA_ROOT.
    sys.path.insert(0, str(Path(os.environ.get("COURSIA_ROOT", r"D:\CoursIA")) / "GradeBookApp"))
    from gradebook import run_pipeline
    run_pipeline(CONFIG)
```

## Exécution

```bash
# Définir COURSIA_ROOT si le dépôt n'est pas en D:\CoursIA
setx COURSIA_ROOT "D:\CoursIA"          # une fois (Windows)

cd "G:\Mon Drive\MyIA\Formation\EPF\2026\grading"
python epf_2026_ml.py
python epf_2026_genai.py
```

## Créer une nouvelle config

1. Dans `Formation\<école>\<année>\grading\` (pas dans le dépôt), dupliquer une config existante.
2. Adapter `CONFIG` (chemins GDrive, mapping colonnes, `target_mean`/`target_std`, `professor_email`).
3. Conserver le bloc `__main__` avec le shim `COURSIA_ROOT` ci-dessus.
4. Tester : `python <nouvelle_config>.py`.

## Structure du dictionnaire `CONFIG`

Inchangée (le moteur `gradebook.py` la consomme telle quelle) :

```python
CONFIG = {
    'nom_classe': str,
    'inscriptions_path': str,      # CSV inscriptions (GDrive)
    'evaluations_path': str,       # CSV évaluations (GDrive)
    'output_path': str,            # XLSX de sortie (GDrive)
    'column_mapping': {"Prénom": "prenom", "Nom de famille": "nom", "Projet": "sujet_projet_1"},
    'target_mean': float,
    'target_std': float,
    'teacher_weight': float,       # 1.0 = 50%/50%
    'professor_email': str,
    'blacklisted_groups': list,    # optionnel
}
```

Configs multi-épreuves (Min1/Min2) : voir la clé `epreuves` dans les fichiers sur GDrive.

## Voir aussi

- [`gradebook.py`](../gradebook.py) — moteur
- `Formation\ECE\2026\grading\ece-grading.md` (GDrive, privé) — même schéma (ECE)
- `Formation\ESGF\2026\grading\esgf-grading.md` (GDrive, privé) — même schéma (ESGF)
