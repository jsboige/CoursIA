# Guide de maintenance de la démo Roo

## Introduction

Ce document fournit des instructions détaillées pour maintenir et mettre à jour la démo d'initiation à Roo. Il est destiné aux développeurs et mainteneurs responsables de l'évolution de la démo, de l'ajout de nouvelles fonctionnalités et de la résolution des problèmes.

## Table des matières

1. [Structure du projet](#structure-du-projet)
2. [Processus de maintenance](#processus-de-maintenance)
3. [Ajout de nouvelles démos](#ajout-de-nouvelles-démos)
4. [Mise à jour de la documentation](#mise-à-jour-de-la-documentation)
5. [Gestion des versions](#gestion-des-versions)
6. [Résolution des problèmes courants](#résolution-des-problèmes-courants)
7. [Bonnes pratiques](#bonnes-pratiques)

## Structure du projet

La démo d'initiation à Roo est organisée selon la structure suivante:

```
demo-roo-code/
├── VERSION.md                    # Fichier de versionnement
├── README.md                     # Documentation principale
├── README-integration.md         # Guide d'intégration
├── CONTRIBUTING.md               # Guide de contribution
├── install-demo.ps1              # Script d'installation unifié
├── prepare-workspaces.ps1        # Script de préparation des workspaces
├── clean-workspaces.ps1          # Script de nettoyage des workspaces
├── .env.example                  # Modèle de configuration
├── docs/                         # Documentation
│   └── demo-maintenance.md       # Ce guide de maintenance
├── 01-decouverte/                # Répertoire thématique 1
│   ├── README.md
│   ├── demo-1-conversation/      # Démo spécifique
│   │   ├── README.md
│   │   ├── docs/                 # Documentation pour les agents
│   │   ├── ressources/           # Fichiers nécessaires pour la démo
│   │   └── workspace/            # Espace de travail pour l'utilisateur
│   └── demo-2-vision/
│       └── ...
├── 02-orchestration-taches/      # Répertoire thématique 2
│   └── ...
├── 03-assistant-pro/             # Répertoire thématique 3
│   └── ...
├── 04-creation-contenu/          # Répertoire thématique 4
│   └── ...
└── 05-projets-avances/           # Répertoire thématique 5
    └── ...
```

## Processus de maintenance

### Maintenance régulière

1. **Vérification des liens et références**
   - Vérifiez régulièrement que tous les liens dans la documentation sont valides
   - Assurez-vous que les références aux fichiers et répertoires sont correctes

2. **Mise à jour des dépendances**
   - Vérifiez les versions des dépendances (Python, Node.js, etc.)
   - Testez la compatibilité avec les nouvelles versions de VS Code et de l'extension Roo

3. **Tests des scripts**
   - Testez régulièrement les scripts de préparation et de nettoyage
   - Vérifiez que le script d'installation fonctionne correctement sur différents systèmes

4. **Revue de la documentation**
   - Assurez-vous que la documentation est à jour et reflète l'état actuel de la démo
   - Corrigez les erreurs et améliorez la clarté si nécessaire

### Cycle de maintenance recommandé

- **Hebdomadaire**: Vérification rapide des problèmes signalés et corrections mineures
- **Mensuelle**: Revue complète de la documentation et des scripts
- **Trimestrielle**: Mise à jour des dépendances et test complet de toutes les démos
- **Semestrielle**: Évaluation pour l'ajout de nouvelles démos ou fonctionnalités

## Ajout de nouvelles démos

Pour ajouter une nouvelle démo au projet, suivez ces étapes:

1. **Planification**
   - Identifiez le répertoire thématique approprié (01-decouverte, 02-orchestration-taches, etc.)
   - Définissez clairement l'objectif et le public cible de la démo
   - Esquissez les étapes principales et les résultats attendus

2. **Création de la structure de répertoires**
   ```
   XX-theme/demo-N-nom/
   ├── README.md                  # Instructions détaillées pour la démo
   ├── docs/
   │   └── guide-agent.md         # Guide pour les agents Roo
   ├── ressources/                # Fichiers nécessaires pour la démo
   └── workspace/
       └── README.md              # Instructions pour l'utilisateur
   ```

3. **Développement du contenu**
   - Créez les fichiers ressources nécessaires
   - Rédigez une documentation claire et détaillée
   - Testez la démo dans un environnement isolé

4. **Intégration**
   - Assurez-vous que les scripts de préparation et de nettoyage reconnaissent la nouvelle démo
   - Mettez à jour les références dans la documentation principale
   - Ajoutez la démo aux parcours recommandés si pertinent

5. **Test et validation**
   - Testez la démo avec différents profils d'utilisateurs
   - Vérifiez que les scripts fonctionnent correctement avec la nouvelle démo
   - Assurez-vous que la documentation est claire et complète

6. **Mise à jour de la version**
   - Mettez à jour le fichier VERSION.md avec les détails de la nouvelle démo
   - Créez un commit avec un message descriptif

### Conventions de nommage

- Les répertoires thématiques sont numérotés de 01 à XX
- Les démos sont numérotées séquentiellement dans chaque répertoire thématique
- Les noms des démos doivent être courts et descriptifs
- Format: `demo-N-nom` où N est un nombre et nom est un identifiant court

## Mise à jour de la documentation

La documentation est un élément crucial de la démo. Voici comment la maintenir efficacement:

1. **Documentation principale**
   - `README.md`: Vue d'ensemble du projet, instructions d'installation rapide, parcours recommandés
   - `README-integration.md`: Instructions spécifiques à l'intégration dans le dépôt principal
   - `CONTRIBUTING.md`: Guide pour les contributeurs

2. **Documentation des démos**
   - Chaque démo doit avoir son propre README.md avec:
     - Une description claire de l'objectif
     - Des instructions pas à pas
     - Des exemples de prompts à utiliser avec Roo
     - Des captures d'écran si nécessaire

3. **Documentation pour les agents**
   - Le répertoire `docs/` de chaque démo contient des guides pour les agents Roo
   - Ces guides expliquent comment aborder les tâches de la démo et quelles capacités utiliser

4. **Guides généraux**
   - `docs/demo-guide.md`: Guide d'introduction à la démo
   - `docs/installation-complete.md`: Guide d'installation détaillé
   - `docs/demo-maintenance.md` (ce document): Guide de maintenance

### Processus de mise à jour de la documentation

1. Identifiez les sections qui nécessitent une mise à jour
2. Rédigez les modifications en suivant le style et le format existants
3. Vérifiez l'exactitude technique et la clarté des instructions
4. Mettez à jour les captures d'écran si nécessaire
5. Vérifiez les liens et références
6. Mettez à jour la date de dernière modification si applicable

## Gestion des versions

Le projet utilise un système de versionnement sémantique (MAJEUR.MINEUR.CORRECTIF) documenté dans le fichier `VERSION.md`.

### Processus de mise à jour de version

1. **Déterminer le type de mise à jour**
   - **MAJEUR**: Changements incompatibles avec les versions précédentes
   - **MINEUR**: Ajouts de fonctionnalités rétrocompatibles
   - **CORRECTIF**: Corrections de bugs rétrocompatibles

2. **Mettre à jour le fichier VERSION.md**
   - Incrémentez le numéro de version approprié
   - Ajoutez une nouvelle section dans l'historique des versions
   - Incluez la date et une description détaillée des changements

3. **Mettre à jour les références à la version**
   - Vérifiez si d'autres fichiers font référence à la version et mettez-les à jour

4. **Créer un commit**
   - Utilisez un message de commit clair: `"Version X.Y.Z: Description des changements"`

### Branches et tags

- Utilisez des branches pour les développements majeurs
- Créez des tags Git pour marquer les versions importantes
- Format recommandé pour les tags: `v1.0.0`, `v1.1.0`, etc.

## Résolution des problèmes courants

### Problèmes liés aux scripts

#### Les scripts ne trouvent pas les répertoires workspace
- Vérifiez que vous exécutez les scripts depuis le répertoire `demo-roo-code`
- Assurez-vous que la structure des répertoires n'a pas été modifiée
- Vérifiez que les noms des dossiers de démo suivent le format attendu (`demo-X-nom`)

#### Erreurs de permission sur les scripts bash
```bash
chmod +x *.sh
```

#### Problèmes de fins de ligne
Si vous obtenez des erreurs du type "bad interpreter", convertissez les fins de ligne:
```bash
# Installation de dos2unix si nécessaire
sudo apt-get install dos2unix

# Conversion des fins de ligne
dos2unix *.sh
```

### Problèmes liés à l'environnement

#### L'extension Roo ne se charge pas
- Vérifiez que vous avez la dernière version de VS Code
- Désinstallez et réinstallez l'extension
- Redémarrez VS Code après l'installation

#### Roo ne répond pas comme prévu
- Assurez-vous d'avoir sélectionné le bon mode pour votre tâche
- Essayez de reformuler votre question de manière plus précise
- Vérifiez votre connexion internet

#### Les fichiers ne s'affichent pas dans le workspace
- Exécutez à nouveau le script de préparation
- Vérifiez que vous êtes dans le bon répertoire
- Rafraîchissez l'explorateur de fichiers de VS Code

### Problèmes spécifiques à Windows/Mac

#### Exécution des scripts PowerShell
Si vous ne pouvez pas exécuter les scripts PowerShell en raison de restrictions de sécurité:
```powershell
Set-ExecutionPolicy -Scope Process -ExecutionPolicy Bypass
```

#### Chemins trop longs sur Windows
Windows peut avoir des problèmes avec les chemins dépassant 260 caractères. Activez la prise en charge des chemins longs:
```powershell
# Nécessite des droits administrateur
New-ItemProperty -Path "HKLM:\SYSTEM\CurrentControlSet\Control\FileSystem" -Name "LongPathsEnabled" -Value 1 -PropertyType DWORD -Force
```

## Bonnes pratiques

### Organisation du code

- Maintenez une structure de répertoires cohérente
- Utilisez des noms de fichiers descriptifs
- Commentez le code des scripts pour expliquer leur fonctionnement
- Utilisez des fonctions pour factoriser le code répétitif

### Documentation

- Privilégiez la clarté et la concision
- Incluez des exemples concrets
- Utilisez des listes à puces et des tableaux pour améliorer la lisibilité
- Ajoutez des captures d'écran pour illustrer les étapes complexes

### Tests

- Testez les démos sur différents systèmes d'exploitation
- Vérifiez la compatibilité avec différentes versions de VS Code
- Testez les scénarios d'erreur pour s'assurer que les messages d'erreur sont clairs
- Demandez des retours d'utilisateurs de différents niveaux d'expertise

### Sécurité

- Ne commettez jamais de clés API ou d'informations sensibles
- Utilisez le fichier `.env.example` pour montrer quelles variables sont nécessaires
- Vérifiez que le fichier `.env` est bien dans `.gitignore`
- Utilisez des clés factices dans les exemples et la documentation

## Conclusion

Ce guide de maintenance vous fournit les informations nécessaires pour maintenir et faire évoluer la démo d'initiation à Roo. En suivant ces instructions et bonnes pratiques, vous contribuerez à offrir une expérience de qualité aux utilisateurs et à assurer la pérennité du projet.

Pour toute question ou suggestion concernant ce guide, veuillez contacter l'équipe de développement ou créer une issue dans le dépôt principal.

---

*Dernière mise à jour: 21 mai 2025*