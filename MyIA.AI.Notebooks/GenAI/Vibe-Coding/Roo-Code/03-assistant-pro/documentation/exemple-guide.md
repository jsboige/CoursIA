# Guide utilisateur - Application TaskFlow

## Introduction

Bienvenue dans le guide utilisateur de TaskFlow, votre solution de gestion de tâches et de projets en équipe. Ce guide vous accompagnera pas à pas dans la prise en main de l'application, de l'installation à l'utilisation des fonctionnalités avancées.

**Version de l'application**: 2.5.3  
**Dernière mise à jour**: 15 mai 2025  
**Plateformes supportées**: Windows 10/11, macOS 12+, Linux (Ubuntu 22.04+), iOS 15+, Android 11+

## Table des matières

1. [Installation](#1-installation)
2. [Premiers pas](#2-premiers-pas)
3. [Gestion des tâches](#3-gestion-des-tâches)
4. [Gestion des projets](#4-gestion-des-projets)
5. [Collaboration en équipe](#5-collaboration-en-équipe)
6. [Fonctionnalités avancées](#6-fonctionnalités-avancées)
7. [Paramètres et personnalisation](#7-paramètres-et-personnalisation)
8. [Résolution des problèmes](#8-résolution-des-problèmes)
9. [Support et ressources](#9-support-et-ressources)

## 1. Installation

### 1.1 Configuration requise

**Configuration minimale**:
- **Processeur**: Dual-core 2 GHz ou supérieur
- **Mémoire**: 4 Go RAM
- **Espace disque**: 500 Mo d'espace libre
- **Connexion Internet**: Requise pour la synchronisation et les fonctionnalités collaboratives
- **Navigateur** (version web): Chrome 90+, Firefox 88+, Safari 14+, Edge 90+

### 1.2 Installation sur Windows

1. Téléchargez le programme d'installation depuis [notre site web](https://www.taskflow-app.example/download).
2. Double-cliquez sur le fichier `TaskFlow-Setup-2.5.3.exe`.
3. Suivez les instructions à l'écran:
   - Acceptez les conditions d'utilisation
   - Choisissez l'emplacement d'installation (ou conservez l'emplacement par défaut)
   - Sélectionnez les composants à installer
   - Cliquez sur "Installer"
4. Une fois l'installation terminée, lancez TaskFlow depuis le raccourci créé sur le bureau ou dans le menu Démarrer.

### 1.3 Installation sur macOS

1. Téléchargez le fichier DMG depuis [notre site web](https://www.taskflow-app.example/download).
2. Ouvrez le fichier `TaskFlow-2.5.3.dmg`.
3. Faites glisser l'icône TaskFlow dans le dossier Applications.
4. Lancez TaskFlow depuis le Launchpad ou le dossier Applications.
5. Lors du premier lancement, vous devrez peut-être autoriser l'application dans les paramètres de sécurité.

### 1.4 Installation sur Linux (Ubuntu)

```bash
# Ajout du dépôt TaskFlow
curl -s https://repo.taskflow-app.example/key.gpg | sudo apt-key add -
sudo add-apt-repository "deb https://repo.taskflow-app.example/apt stable main"

# Installation de l'application
sudo apt update
sudo apt install taskflow

# Lancement de l'application
taskflow
```

### 1.5 Installation sur appareils mobiles

1. Accédez à l'App Store (iOS) ou au Google Play Store (Android).
2. Recherchez "TaskFlow".
3. Appuyez sur "Installer" ou "Obtenir".
4. Une fois l'installation terminée, ouvrez l'application.

## 2. Premiers pas

### 2.1 Création de compte

1. Lancez l'application TaskFlow.
2. Sur l'écran d'accueil, cliquez sur "Créer un compte".
3. Remplissez le formulaire avec vos informations:
   - Adresse e-mail professionnelle
   - Mot de passe (8 caractères minimum, incluant lettres, chiffres et caractères spéciaux)
   - Prénom et nom
   - Nom de l'organisation (optionnel)
4. Cliquez sur "S'inscrire".
5. Vérifiez votre boîte de réception et cliquez sur le lien de confirmation.

![Écran de création de compte](https://www.taskflow-app.example/images/signup-screen.png)

### 2.2 Connexion à un compte existant

1. Lancez l'application TaskFlow.
2. Sur l'écran d'accueil, entrez votre adresse e-mail et votre mot de passe.
3. (Optionnel) Cochez "Se souvenir de moi" pour rester connecté.
4. Cliquez sur "Se connecter".

> **Astuce**: Si vous avez oublié votre mot de passe, cliquez sur "Mot de passe oublié?" et suivez les instructions envoyées par e-mail.

### 2.3 Interface utilisateur principale

L'interface de TaskFlow est organisée en plusieurs zones:

![Interface principale](https://www.taskflow-app.example/images/main-interface.png)

1. **Barre latérale gauche**: Navigation principale entre les différentes sections (Tableau de bord, Tâches, Projets, Équipe, Rapports).
2. **Barre d'outils supérieure**: Recherche, notifications, aide et paramètres du compte.
3. **Zone de contenu principale**: Affiche le contenu de la section sélectionnée.
4. **Panneau d'informations**: Affiche les détails de l'élément sélectionné.

### 2.4 Tour guidé

Lors de votre première connexion, un tour guidé vous sera proposé. Nous vous recommandons de le suivre pour découvrir les fonctionnalités principales:

1. Cliquez sur "Commencer le tour" lorsque l'invitation apparaît.
2. Suivez les instructions à l'écran qui vous guideront à travers les différentes sections.
3. Vous pouvez quitter le tour à tout moment en cliquant sur "Terminer le tour".
4. Pour relancer le tour ultérieurement, allez dans "Aide" > "Tour guidé".

## 3. Gestion des tâches

### 3.1 Création d'une tâche

Pour créer une nouvelle tâche:

1. Cliquez sur le bouton "+" dans la section "Tâches" ou utilisez le raccourci clavier `Ctrl+N` (Windows/Linux) ou `Cmd+N` (macOS).
2. Remplissez les champs du formulaire:
   - **Titre**: Nom concis de la tâche (obligatoire)
   - **Description**: Détails supplémentaires (optionnel)
   - **Date d'échéance**: Date et heure limite (optionnel)
   - **Priorité**: Basse, Moyenne, Haute, Urgente
   - **Projet**: Associer à un projet existant (optionnel)
   - **Assigné à**: Vous-même ou un membre de l'équipe
   - **Étiquettes**: Mots-clés pour catégoriser la tâche
3. Cliquez sur "Créer" pour enregistrer la tâche.

![Création de tâche](https://www.taskflow-app.example/images/task-creation.png)

### 3.2 Affichage et filtrage des tâches

TaskFlow offre plusieurs vues pour organiser vos tâches:

- **Vue Liste**: Affichage simple sous forme de liste
- **Vue Kanban**: Organisation par statut (À faire, En cours, Terminé)
- **Vue Calendrier**: Organisation par date
- **Vue Gantt**: Visualisation temporelle des tâches et dépendances

Pour filtrer les tâches:

1. Cliquez sur "Filtrer" dans la barre d'outils.
2. Sélectionnez les critères de filtrage:
   - Statut
   - Priorité
   - Date d'échéance
   - Assigné à
   - Projet
   - Étiquettes
3. Cliquez sur "Appliquer" pour voir les résultats filtrés.

> **Astuce**: Enregistrez vos filtres fréquemment utilisés en cliquant sur "Enregistrer ce filtre" et en lui donnant un nom.

### 3.3 Modification et suivi des tâches

Pour modifier une tâche:

1. Cliquez sur la tâche pour ouvrir ses détails dans le panneau d'informations.
2. Cliquez sur "Modifier" ou directement sur le champ à modifier.
3. Effectuez vos modifications.
4. Cliquez sur "Enregistrer" ou appuyez sur `Entrée`.

Pour suivre la progression:

1. Dans les détails de la tâche, utilisez le curseur de progression pour indiquer l'avancement (0-100%).
2. Mettez à jour le statut de la tâche (À faire, En cours, En attente, Terminé).
3. Ajoutez des commentaires pour documenter les progrès ou les obstacles.

### 3.4 Sous-tâches et dépendances

Pour créer des sous-tâches:

1. Ouvrez les détails d'une tâche.
2. Faites défiler jusqu'à la section "Sous-tâches".
3. Cliquez sur "Ajouter une sous-tâche".
4. Entrez le titre et les détails de la sous-tâche.
5. Cliquez sur "Ajouter".

Pour établir des dépendances entre les tâches:

1. Ouvrez les détails d'une tâche.
2. Accédez à la section "Dépendances".
3. Cliquez sur "Ajouter une dépendance".
4. Recherchez et sélectionnez la tâche dont dépend celle-ci.
5. Choisissez le type de dépendance (Fin-Début, Début-Début, etc.).
6. Cliquez sur "Ajouter".

## 4. Gestion des projets

### 4.1 Création d'un projet

Pour créer un nouveau projet:

1. Dans la section "Projets", cliquez sur "Nouveau projet".
2. Remplissez les informations du projet:
   - **Nom**: Titre du projet (obligatoire)
   - **Description**: Présentation et objectifs du projet
   - **Date de début**: Date de démarrage du projet
   - **Date de fin prévue**: Date d'échéance estimée
   - **Responsable**: Chef de projet
   - **Membres**: Participants au projet
   - **Catégorie**: Type de projet
3. Cliquez sur "Créer le projet".

### 4.2 Tableau de bord du projet

Le tableau de bord du projet offre une vue d'ensemble:

- **Résumé**: Statut général, dates clés, progression
- **Activité récente**: Dernières actions et mises à jour
- **Tâches**: Liste des tâches du projet avec leur statut
- **Membres**: Participants au projet et leurs rôles
- **Documents**: Fichiers associés au projet
- **Jalons**: Étapes importantes du projet

### 4.3 Gestion des jalons

Les jalons marquent les étapes importantes d'un projet:

1. Dans le tableau de bord du projet, accédez à l'onglet "Jalons".
2. Cliquez sur "Ajouter un jalon".
3. Définissez:
   - **Nom**: Titre du jalon
   - **Description**: Détails et critères de réussite
   - **Date**: Échéance du jalon
   - **Tâches associées**: Tâches qui doivent être terminées pour atteindre ce jalon
4. Cliquez sur "Créer".

## 5. Collaboration en équipe

### 5.1 Invitation de membres

Pour inviter de nouveaux membres:

1. Accédez à la section "Équipe".
2. Cliquez sur "Inviter des membres".
3. Entrez les adresses e-mail des personnes à inviter (séparées par des virgules).
4. Sélectionnez leur rôle (Administrateur, Membre, Observateur).
5. Personnalisez le message d'invitation (optionnel).
6. Cliquez sur "Envoyer les invitations".

### 5.2 Communication et commentaires

Pour communiquer au sein d'une tâche:

1. Ouvrez les détails de la tâche.
2. Faites défiler jusqu'à la section "Commentaires".
3. Rédigez votre message dans le champ de texte.
4. Pour mentionner un membre, utilisez "@" suivi de son nom.
5. Pour joindre un fichier, cliquez sur l'icône de trombone.
6. Cliquez sur "Publier" pour envoyer votre commentaire.

### 5.3 Notifications et alertes

Gérez vos notifications:

1. Accédez à "Paramètres" > "Notifications".
2. Configurez vos préférences pour chaque type d'événement:
   - Assignation de tâche
   - Commentaires
   - Échéances approchantes
   - Mises à jour de projet
   - Mentions
3. Choisissez le canal de notification (Application, E-mail, Mobile).
4. Définissez la fréquence des résumés par e-mail (Instantané, Quotidien, Hebdomadaire).

## 6. Fonctionnalités avancées

### 6.1 Automatisations et règles

Créez des automatisations pour gagner du temps:

1. Accédez à "Paramètres" > "Automatisations".
2. Cliquez sur "Nouvelle règle".
3. Définissez le déclencheur (ex: "Quand une tâche est marquée comme terminée").
4. Définissez l'action (ex: "Notifier le responsable du projet").
5. Ajoutez des conditions si nécessaire (ex: "Seulement si la tâche a une priorité haute").
6. Nommez votre règle et cliquez sur "Enregistrer".

### 6.2 Rapports et analyses

Générez des rapports pour suivre la performance:

1. Accédez à la section "Rapports".
2. Choisissez le type de rapport:
   - Progression des tâches
   - Charge de travail par membre
   - Performance du projet
   - Respect des délais
   - Temps passé par catégorie
3. Définissez la période et les filtres.
4. Cliquez sur "Générer le rapport".
5. Exportez le rapport au format PDF, Excel ou CSV si nécessaire.

### 6.3 Intégrations avec d'autres outils

TaskFlow s'intègre avec de nombreux outils:

1. Accédez à "Paramètres" > "Intégrations".
2. Parcourez les intégrations disponibles:
   - Google Workspace / Microsoft 365
   - Slack / Microsoft Teams
   - GitHub / GitLab
   - Zoom / Google Meet
   - Dropbox / Google Drive / OneDrive
3. Cliquez sur "Configurer" à côté de l'outil souhaité.
4. Suivez les instructions pour autoriser la connexion.
5. Personnalisez les paramètres de l'intégration.

## 7. Paramètres et personnalisation

### 7.1 Paramètres du compte

Pour modifier vos informations personnelles:

1. Cliquez sur votre avatar dans le coin supérieur droit.
2. Sélectionnez "Paramètres du compte".
3. Modifiez vos informations:
   - Photo de profil
   - Nom et prénom
   - Adresse e-mail
   - Mot de passe
   - Fuseau horaire
   - Langue de l'interface
4. Cliquez sur "Enregistrer les modifications".

### 7.2 Personnalisation de l'interface

Adaptez l'interface à vos préférences:

1. Accédez à "Paramètres" > "Apparence".
2. Choisissez:
   - Thème (Clair, Sombre, Automatique)
   - Densité d'affichage (Confortable, Standard, Compact)
   - Vue par défaut pour les tâches
   - Éléments à afficher sur le tableau de bord
3. Cliquez sur "Appliquer" pour voir les changements.

### 7.3 Raccourcis clavier

Utilisez les raccourcis clavier pour gagner en efficacité:

| Action | Windows/Linux | macOS |
|--------|--------------|-------|
| Nouvelle tâche | Ctrl+N | Cmd+N |
| Recherche | Ctrl+F | Cmd+F |
| Enregistrer | Ctrl+S | Cmd+S |
| Tableau de bord | Ctrl+1 | Cmd+1 |
| Tâches | Ctrl+2 | Cmd+2 |
| Projets | Ctrl+3 | Cmd+3 |
| Équipe | Ctrl+4 | Cmd+4 |
| Aide | F1 | F1 |

Pour voir la liste complète des raccourcis, appuyez sur `Ctrl+/` (Windows/Linux) ou `Cmd+/` (macOS).

## 8. Résolution des problèmes

### 8.1 Problèmes de connexion

Si vous ne parvenez pas à vous connecter:

1. Vérifiez que votre adresse e-mail et votre mot de passe sont corrects.
2. Assurez-vous que votre connexion Internet fonctionne.
3. Videz le cache de votre navigateur ou application.
4. Si vous avez oublié votre mot de passe, utilisez l'option "Mot de passe oublié".
5. Vérifiez que votre compte n'a pas été désactivé par un administrateur.

### 8.2 Problèmes de synchronisation

Si vos données ne se synchronisent pas:

1. Vérifiez votre connexion Internet.
2. Cliquez sur l'icône de synchronisation pour forcer une synchronisation manuelle.
3. Déconnectez-vous puis reconnectez-vous à l'application.
4. Vérifiez que vous n'avez pas atteint votre limite de stockage.

### 8.3 Questions fréquentes

**Q: Puis-je utiliser TaskFlow hors ligne?**  
R: Oui, l'application de bureau et mobile permet de travailler hors ligne. Vos modifications seront synchronisées lorsque vous vous reconnecterez à Internet.

**Q: Comment puis-je récupérer une tâche ou un projet supprimé?**  
R: Accédez à "Paramètres" > "Corbeille". Les éléments supprimés y sont conservés pendant 30 jours avant d'être définitivement effacés.

**Q: Quelle est la limite de stockage pour les pièces jointes?**  
R: Le plan gratuit offre 1 Go de stockage. Les plans professionnels offrent entre 10 Go et stockage illimité selon la formule.

**Q: Comment puis-je exporter toutes mes données?**  
R: Accédez à "Paramètres" > "Données" > "Exporter". Vous pourrez choisir les données à exporter et le format (JSON, CSV, Excel).

## 9. Support et ressources

### 9.1 Centre d'aide

Accédez à notre centre d'aide complet:

1. Cliquez sur l'icône "?" dans la barre d'outils supérieure.
2. Sélectionnez "Centre d'aide".
3. Parcourez les catégories ou utilisez la recherche pour trouver des réponses.

### 9.2 Formation et tutoriels

Améliorez vos compétences avec nos ressources de formation:

- **Webinaires**: Sessions en direct hebdomadaires (inscription dans la section "Formation")
- **Tutoriels vidéo**: Disponibles dans la section "Apprentissage" du centre d'aide
- **Guides pratiques**: Documents PDF téléchargeables pour chaque fonctionnalité
- **Certification TaskFlow**: Programme de certification pour les utilisateurs avancés

### 9.3 Contacter le support

Si vous avez besoin d'aide supplémentaire:

1. Cliquez sur l'icône "?" dans la barre d'outils supérieure.
2. Sélectionnez "Contacter le support".
3. Remplissez le formulaire avec:
   - Sujet de votre demande
   - Description détaillée du problème
   - Captures d'écran si nécessaire
4. Cliquez sur "Envoyer".

Notre équipe de support vous répondra dans un délai de 24 heures ouvrables.

---

© 2025 TaskFlow Inc. Tous droits réservés.  
Version du document: 2.5.3-GU-FR  
Dernière mise à jour: 15 mai 2025