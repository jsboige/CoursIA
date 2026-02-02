# Guide de contribution au projet Demo roo-code

Ce document décrit les règles et bonnes pratiques pour contribuer au projet Demo roo-code, conçu pour être intégré comme sous-dossier dans un dépôt Git existant.

## 🌟 Principes généraux

1. **Autonomie du sous-dossier**: Les contributions doivent préserver l'autonomie du sous-dossier, en évitant les dépendances externes non documentées.
2. **Cohérence**: Maintenir la cohérence avec le style et la structure existants du projet.
3. **Documentation**: Toute nouvelle fonctionnalité doit être correctement documentée.
4. **Tests**: Les nouvelles fonctionnalités doivent être testées dans le contexte d'intégration comme sous-dossier.

## 📂 Conventions de nommage et structure

### Structure des répertoires

```
demo-roo-code/
├── 01-decouverte/
│   ├── demo-1-conversation/
│   │   ├── docs/
│   │   ├── ressources/
│   │   └── workspace/
│   └── demo-2-vision/
│       ├── docs/
│       ├── ressources/
│       └── workspace/
├── 02-orchestration-taches/
│   └── ...
└── ...
```

### Conventions de nommage

1. **Répertoires thématiques**: Utilisez le format `XX-nom-theme` où XX est un numéro à deux chiffres.
2. **Démos**: Utilisez le format `demo-X-nom-demo` où X est un numéro séquentiel.
3. **Fichiers README**: Chaque répertoire doit contenir un fichier `README.md` décrivant son contenu.
4. **Ressources**: Les fichiers de ressources doivent avoir des noms descriptifs en minuscules avec des tirets.
5. **Scripts**: Les scripts doivent être disponibles en versions PowerShell (`.ps1`) et Bash (`.sh`).

## 🔄 Processus de contribution

### 1. Préparation

1. Assurez-vous de comprendre la structure du projet et son intégration comme sous-dossier.
2. Consultez les fichiers README.md et README-integration.md pour comprendre le contexte.
3. Vérifiez les issues existantes pour éviter les doublons.

### 2. Développement

1. Créez une branche dédiée à votre contribution avec un nom descriptif.
2. Respectez les conventions de nommage et la structure existante.
3. Assurez-vous que vos modifications fonctionnent dans le contexte d'un sous-dossier.
4. Mettez à jour la documentation si nécessaire.
5. Testez vos modifications avec les scripts de préparation et de nettoyage.

### 3. Soumission d'une Pull Request

1. Créez une Pull Request avec une description claire de vos modifications.
2. Référencez les issues pertinentes dans votre description.
3. Remplissez le template de Pull Request fourni.
4. Assurez-vous que tous les tests passent.

### 4. Revue de code

1. Attendez la revue de votre Pull Request par les mainteneurs.
2. Répondez aux commentaires et apportez les modifications demandées.
3. Une fois approuvée, votre Pull Request sera fusionnée.

## 📝 Directives spécifiques

### Modification des démos existantes

1. Préservez la structure et le format des démos existantes.
2. Assurez-vous que les modifications sont compatibles avec les scripts de préparation et de nettoyage.
3. Mettez à jour la documentation correspondante.

### Ajout de nouvelles démos

1. Suivez la structure standard: `docs/`, `ressources/`, `workspace/`.
2. Créez un README.md détaillé expliquant l'objectif et le fonctionnement de la démo.
3. Assurez-vous que la démo fonctionne avec les scripts existants.
4. Mettez à jour le README.md principal pour référencer la nouvelle démo.

### Modification des scripts

1. Assurez-vous que les modifications sont compatibles avec Windows et Linux/macOS.
2. Testez les scripts dans les deux environnements si possible.
3. Documentez clairement les changements dans les commentaires du script.
4. Mettez à jour la documentation correspondante.

## 🛠️ Environnement de développement recommandé

> **Note**: Pour une installation complète et détaillée de l'environnement de développement, consultez le [guide d'installation complet](./guide_installation.md).

1. **Visual Studio Code** avec les extensions suivantes:
   - Markdown All in One
   - PowerShell
   - Shell Script
   - EditorConfig
   - Extension Roo

2. **Git** configuré avec:
   - Nom d'utilisateur et email
   - Authentification SSH (recommandé)

3. **PowerShell 5.1+** ou **Bash** pour tester les scripts

4. **Python** et **Node.js** pour l'utilisation des MCPs (Model Context Protocol servers)

## 📚 Ressources utiles

- [Documentation Git](https://git-scm.com/doc)
- [Guide Markdown](https://www.markdownguide.org/)
- [Documentation PowerShell](https://docs.microsoft.com/en-us/powershell/)
- [Documentation Bash](https://www.gnu.org/software/bash/manual/)

## ❓ Questions et support

Si vous avez des questions sur le processus de contribution, n'hésitez pas à:
- Ouvrir une issue avec le tag "question"
- Contacter les mainteneurs du projet

---

Merci de contribuer au projet Demo roo-code! Votre participation aide à améliorer cet outil pour tous les utilisateurs.