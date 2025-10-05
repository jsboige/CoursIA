# GradeBookApp Project

Ce projet calcule les notes des étudiants en se basant sur les fichiers d'inscription et d'évaluation.

## Fichiers de données

L'application nécessite des chemins vers les fichiers de données CSV. Voici les chemins pour chaque classe :

### Classe : PrCon

*   **Fichier d'inscriptions :** `G:\Mon Drive\MyIA\Formation\Epita\2025\SCIA-2026-Inscription-PrCon.xlsx - konbert-output-3e545591.csv`
*   **Fichier d'évaluations :** `G:\Mon Drive\MyIA\Formation\Epita\2025\Epita - 2025 - PCon - Evaluations (réponses) - Réponses au formulaire 1.csv`

### Classe : IASY

*   **Fichier d'inscriptions :** `G:\Mon Drive\MyIA\Formation\Epita\2025\2025 - SCIA - NLP - IA Symbolique - Inscription.xlsx - eleves.csv`
*   **Fichier d'évaluations :** `G:\Mon Drive\MyIA\Formation\Epita\2025\Epita - 2025 - IASY - Evaluations (réponses) - Réponses au formulaire 1.csv`

## Utilisation

Pour lancer l'application, utilisez la commande `dotnet run` en fournissant les chemins des fichiers en arguments :

```shell
dotnet run --project GradeBookApp "chemin/vers/inscriptions.csv" "chemin/vers/evaluations.csv"