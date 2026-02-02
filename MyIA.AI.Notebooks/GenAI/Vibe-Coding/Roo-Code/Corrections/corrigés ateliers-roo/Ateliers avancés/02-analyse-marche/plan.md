# Plan Technique pour le Script `analyse_marche.py`

## 1. Objectif du Script

L'objectif est de créer un script Python qui analyse deux sources de données CSV pour fournir une vue synthétique de la tension du marché IT. Le script doit identifier les compétences les plus demandées sur le marché externe et les comparer aux besoins en recrutement internes de l'entreprise.

## 2. Technologies et Librairies

- **Langage :** Python 3.x
- **Librairie principale :** `pandas` pour la manipulation et l'analyse des données.
- **Environnement :** Aucune autre dépendance externe n'est requise. Le script sera exécutable dans un terminal standard avec Python et pandas installés.

## 3. Structure du Fichier

Le script sera organisé en plusieurs fonctions pour une meilleure lisibilité et maintenance, avec un point d'entrée principal.

```python
import pandas as pd
import os

# 1. Constantes
# Définition des chemins relatifs vers les fichiers de données pour la robustesse.
DATA_DIR = '../data_metier_csv/'
MARKET_DATA_PATH = os.path.join(DATA_DIR, 'Marché (scraping).csv')
INTERNAL_DATA_PATH = os.path.join(DATA_DIR, 'Indicateurs internes.csv')

# 2. Fonctions d'analyse

def charger_donnees(chemin_fichier: str) -> pd.DataFrame:
    """Charge un fichier CSV dans un DataFrame pandas."""
    # ... logique de chargement ...

def analyser_competences_marche(df_marche: pd.DataFrame) -> pd.Series:
    """Analyse le DataFrame du marché pour extraire le top 5 des compétences."""
    # ... logique d'extraction et de comptage ...

def analyser_besoins_internes(df_interne: pd.DataFrame) -> list:
    """Analyse le DataFrame interne pour identifier les profils recherchés."""
    # ... logique de filtrage ...

def generer_rapport_console(top_competences: pd.Series, besoins_internes: list):
    """Affiche les résultats de l'analyse de manière formatée dans la console."""
    # ... logique d'affichage ...

# 3. Fonction Principale (Orchestrateur)

def main():
    """Point d'entrée principal du script."""
    # Orchestration des appels de fonctions
    
    # Charger les données
    df_marche = charger_donnees(MARKET_DATA_PATH)
    df_interne = charger_donnees(INTERNAL_DATA_PATH)
    
    # Analyser les données
    top_5_competences = analyser_competences_marche(df_marche)
    missions_ouvertes = analyser_besoins_internes(df_interne)
    
    # Générer le rapport
    generer_rapport_console(top_5_competences, missions_ouvertes)

# 4. Point d'entrée du script

if __name__ == "__main__":
    main()
```

## 4. Logique d'Implémentation Détaillée

### a. `charger_donnees`
- Prend en entrée un chemin de fichier (string).
- Utilise `pd.read_csv(chemin_fichier)`.
- **Arbitrage :** On ajoutera un bloc `try-except` pour gérer les `FileNotFoundError` et afficher un message d'erreur clair si un fichier est manquant.
- Retourne un DataFrame pandas.

### b. `analyser_competences_marche`
- Prend en entrée le DataFrame du marché.
- **Hypothèse :** La colonne clé est nommée `'technologies'`. Les compétences y sont listées sous forme de chaîne, séparées par des virgules.
- **Étapes :**
    1.  Sélectionner la colonne `'technologies'`.
    2.  Supprimer les lignes avec des valeurs manquantes (`.dropna()`).
    3.  Transformer la colonne en une seule chaîne de texte, avec toutes les compétences séparées par des virgules.
    4.  Utiliser `.split(',')` pour créer une liste de toutes les compétences.
    5.  **Nettoyage :** Pour chaque compétence dans la liste, appliquer `.strip().lower()` pour normaliser les données (supprimer les espaces et passer en minuscules).
    6.  Convertir la liste nettoyée en une `pd.Series`.
    7.  Utiliser `.value_counts()` pour obtenir la fréquence de chaque compétence.
    8.  Retourner les 5 premières valeurs avec `.head(5)`.

### c. `analyser_besoins_internes`
- Prend en entrée le DataFrame des indicateurs internes.
- **Hypothèses :** Les colonnes clés sont `'Type'` et `'Profil'`.
- **Étapes :**
    1.  Filtrer le DataFrame pour ne garder que les lignes où la valeur de la colonne `'Type'` est égale à `'Mission ouverte'`.
    2.  Sélectionner la colonne `'Profil'` de ce DataFrame filtré.
    3.  Convertir cette Series en une liste (`.tolist()`).
    4.  Retourner la liste des profils.

### d. `generer_rapport_console`
- Prend en entrée les `top_competences` (une `pd.Series`) et les `besoins_internes` (une `list`).
- Utilise des `print()` formatés (`f-strings`) pour structurer la sortie.
- **Format de sortie :**
    ```
    ==================================================
    === Rapport d'Analyse du Marché de l'Emploi IT ===
    ==================================================

    --> Top 5 des compétences les plus demandées sur le marché :

    1. [Nom Compétence 1] (Mentionnée [X] fois)
    2. [Nom Compétence 2] (Mentionnée [Y] fois)
    ...

    --> Besoins internes actuels (Missions ouvertes) :

    - [Profil 1]
    - [Profil 2]
    ...

    ==================================================
    ```

## 5. Exécution du Script

- Le script doit être exécuté depuis le répertoire `ateliers/02-analyse-marche/`.
- La commande d'exécution est `python analyse_marche.py`.
- Les chemins relatifs dans les constantes sont conçus pour fonctionner depuis cet emplacement.