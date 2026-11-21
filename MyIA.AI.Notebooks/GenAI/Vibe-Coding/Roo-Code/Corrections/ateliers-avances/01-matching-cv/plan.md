# Plan d'Action Technique : Automatisation du Matching CV / Fiche de Poste

Ce document détaille le plan technique pour la création d'un script Python visant à automatiser le matching entre les profils de consultants et les fiches de poste client.

## 1. Objectif

L'objectif est de développer un script Python qui :
1.  Lit les données des consultants et des fiches de poste à partir de fichiers CSV.
2.  Calcule un score de pertinence (matching) pour chaque paire consultant/fiche de poste.
3.  Génère un fichier CSV (`results.csv`) contenant les scores de matching.

## 2. Décisions Techniques

- **Langage de programmation :** Python 3.x
- **Librairies principales :**
  - `pandas` : Pour la manipulation efficace des données tabulaires (CSV).
- **Environnement de développement :** Le script sera conçu pour être exécutable dans un environnement Python standard où `pandas` est installé.
- **Fichiers source :**
    - Script principal : `exercice-1-v2/match.py`
    - Données consultants : `ateliers/data_metier_csv/Base consultants.csv`
    - Données fiches de poste : `ateliers/data_metier_csv/Fiches de poste client.csv`
- **Fichier de sortie :**
    - Résultats : `exercice-1-v2/results.csv`
    - Colonnes : `consultant_id`, `job_id`, `match_score`

## 3. Méthodologie de Matching

Pour assurer la simplicité et la rapidité de l'implémentation, nous utiliserons une approche basée sur la **recherche de mots-clés**.

1.  **Définition d'un lexique :** Une liste prédéfinie de compétences et de mots-clés pertinents (techniques, fonctionnels, etc.) sera utilisée comme base de comparaison.
2.  **Normalisation du texte :** Les textes des descriptions de poste et des CVs seront normalisés (conversion en minuscules, suppression de la ponctuation) pour fiabiliser la recherche.
3.  **Calcul du score :** Le score de matching sera calculé comme le nombre de mots-clés du lexique présents à la fois dans la fiche de poste et dans le profil du consultant. Un score plus élevé indique une meilleure adéquation.

## 4. Plan de Développement Détaillé

Le développement sera divisé en étapes séquentielles :

### Étape 1 : Initialisation du Projet
- Créer le fichier `exercice-1-v2/match.py`.

### Étape 2 : Chargement et Prétraitement des Données
- **Action :** Implémenter une fonction pour charger les deux fichiers CSV (`Base consultants.csv` et `Fiches de poste client.csv`) dans des DataFrames `pandas`.
- **Action :** Implémenter une fonction de nettoyage de texte (`normalize_text`) qui prend une chaîne de caractères et la retourne en minuscules et sans ponctuation superflue.
- **Action :** Appliquer cette fonction de normalisation aux colonnes textuelles pertinentes des deux DataFrames.

### Étape 3 : Définition des Mots-clés et Extraction
- **Action :** Définir une liste (lexique) de mots-clés à rechercher (ex: `['python', 'java', 'sql', 'gestion de projet', 'agile', 'data science']`).
- **Action :** Créer une fonction `extract_keywords(text, lexicon)` qui retourne un ensemble de mots-clés du lexique trouvés dans le texte fourni.

### Étape 4 : Implémentation de la Logique de Matching
- **Action :** Créer la fonction principale `main()`.
- **Action :** Dans `main()`, initialiser une liste vide pour stocker les résultats.
- **Action :** Itérer sur chaque ligne du DataFrame des fiches de poste.
    - Pour chaque fiche de poste, extraire les mots-clés en utilisant `extract_keywords`.
- **Action :** À l'intérieur de cette boucle, itérer sur chaque ligne du DataFrame des consultants.
    - Pour chaque consultant, extraire les mots-clés de son profil.
    - **Calculer le score :** Comparer les deux ensembles de mots-clés et compter le nombre d'éléments en commun.
    - **Stocker le résultat :** Ajouter un dictionnaire `{'consultant_id': ..., 'job_id': ..., 'match_score': ...}` à la liste de résultats.

### Étape 5 : Génération du Fichier de Résultats
- **Action :** À la fin des boucles, convertir la liste de résultats en un DataFrame `pandas`.
- **Action :** Exporter ce DataFrame final vers le fichier `exercice-1-v2/results.csv` en utilisant la méthode `to_csv`, avec `index=False`.

## 5. Structure du Script `match.py`

```python
import pandas as pd
import re

# Constantes
CONSULTANTS_FILE = 'ateliers/data_metier_csv/Base consultants.csv'
JOBS_FILE = 'ateliers/data_metier_csv/Fiches de poste client.csv'
OUTPUT_FILE = 'exercice-1-v2/results.csv'
KEYWORD_LEXICON = ['python', 'java', 'sql', 'gestion de projet', 'agile', 'data science', 'machine learning', 'devops']

def normalize_text(text):
    """Met le texte en minuscules et supprime la ponctuation de base."""
    if not isinstance(text, str):
        return ""
    text = text.lower()
    text = re.sub(r'[^\w\s]', '', text)
    return text

def extract_keywords(text, lexicon):
    """Extrait les mots-clés du lexique trouvés dans un texte."""
    found_keywords = set()
    for keyword in lexicon:
        if keyword in text:
            found_keywords.add(keyword)
    return found_keywords

def main():
    """Fonction principale du script de matching."""
    # 1. Charger les données
    df_consultants = pd.read_csv(CONSULTANTS_FILE)
    df_jobs = pd.read_csv(JOBS_FILE)

    # 2. Normaliser les colonnes textuelles pertinentes (à adapter selon les vrais noms de colonnes)
    # Exemple :
    # df_consultants['description_norm'] = df_consultants['description'].apply(normalize_text)
    # df_jobs['description_norm'] = df_jobs['description'].apply(normalize_text)

    # 3. Processus de matching
    results = []
    
    # Itérer sur les jobs et les consultants pour calculer le score
    # ... (logique de boucle) ...

    # 4. Sauvegarder les résultats
    df_results = pd.DataFrame(results)
    df_results.to_csv(OUTPUT_FILE, index=False)
    print(f"Le rapport de matching a été généré : {OUTPUT_FILE}")

if __name__ == "__main__":
    main()