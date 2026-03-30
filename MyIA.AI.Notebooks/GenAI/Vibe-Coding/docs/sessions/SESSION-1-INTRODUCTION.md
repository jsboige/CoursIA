# Session 1 - Introduction à l'IA Générative (4h)

## 📋 Vue d'Ensemble

**Durée** : 4 heures (13h30 - 17h30)
**Public** : Étudiants Master EPF - MSMIN5IN52
**Format** : Théorie + Pratique avec ateliers

## 🎯 Objectifs Pédagogiques

À l'issue de cette session, les étudiants seront capables de :

1. **Comprendre** les concepts fondamentaux de l'IA Générative
2. **Installer et configurer** Roo Code ou Claude Code
3. **Utiliser** un assistant IA pour des tâches pratiques
4. **Explorer** les différents outils GenAI disponibles

## 📚 Structure de la Session

### Partie 1 : Introduction Théorique (60 min)

**Support** : `Intelligence Artificielle - 8 - IA Générative.pptx`

**Contenu** :
- Historique et évolution (GPT-1 à GPT-4, Claude)
- Concepts fondamentaux :
  - Tokens et embeddings
  - Architecture Transformer et attention
  - LLMs et génération de texte
- Techniques clés :
  - Prompt Engineering (zero-shot, few-shot, CoT)
  - RAG (Retrieval Augmented Generation)
  - Fine-tuning vs In-context learning
- Cas d'usage en entreprise
- Enjeux éthiques et limitations

**Document de référence** : [docs/INTRO-GENAI.md](../INTRO-GENAI.md)

### Partie 2 : Configuration de l'Environnement (45 min)

**Choix de l'outil** :
- **Option A** : Roo Code (recommandé pour débutants)
- **Option B** : Claude Code (pour utilisateurs avancés)

**Support** :
- Roo Code : [docs/roo-code/INSTALLATION-ROO.md](../roo-code/INSTALLATION-ROO.md)
- Claude Code : [docs/claude-code/INSTALLATION-CLAUDE-CODE.md](../claude-code/INSTALLATION-CLAUDE-CODE.md)

**Activités** :
1. Installation VS Code (si nécessaire)
2. Installation de l'extension / CLI
3. Configuration OpenRouter (clé API fournie)
4. Test de la première connexion
5. Vérification du fonctionnement

**Outils complémentaires** (optionnels) :
- Open-WebUI comme "playground" local
- Configuration de MCP servers de base

### 🕐 Pause (15 min)

### Partie 3 : Atelier Pratique Guidé (90 min)

**Support principal** : [docs/roo-code/ROO-GUIDED-PATH.md](../roo-code/ROO-GUIDED-PATH.md)
**Matériel pratique** : Dossier [Ateliers-roo-code/](../../Ateliers-roo-code/)

**Progression** :

#### 3.1 Découverte (30 min)
- **Demo 1** : Conversation avec Roo/Claude
  - Premières questions
  - Utilisation du contexte
  - Modes de conversation
- **Demo 2** : Analyse d'images (si temps)
  - Capacités multimodales
  - Extraction d'informations

#### 3.2 Orchestration (30 min)
- **Demo 3** : Planification de tâches
  - Mode Architect/Plan
  - Structuration de projet
- **Demo 4** : Recherche et synthèse
  - Outils de recherche web
  - Génération de synthèses

#### 3.3 Assistant Professionnel (30 min)
- **Demo 5** : Analyse de données (si temps)
  - Exploration de fichiers
  - Visualisations
- **Demo 6** : Rédaction professionnelle
  - Emails et rapports
  - Communications adaptées

### Partie 4 : Synthèse et Perspectives (30 min)

- Retours d'expérience étudiants
- Questions/réponses
- Présentation des sessions suivantes :
  - Session 2 : Activités pédagogiques
  - Session 3 : Projets avancés
  - Session 4 : Checkpoint projet
  - Session 5 : Soutenances
- Ressources pour approfondir

## 📁 Fichiers et Ressources

### Documents à Distribuer
- [README.md](../../README.md) : Vue d'ensemble du cours
- Guide d'installation selon l'outil choisi
- [ROO-GUIDED-PATH.md](../roo-code/ROO-GUIDED-PATH.md) ou équivalent Claude Code

### Matériel Pratique
- Dossier [Ateliers-roo-code/](../../Ateliers-roo-code/) complet
- Dossier [Ateliers-claude-code/](../../Ateliers-claude-code/) (optionnel)
- Slides PowerPoint du cours

### Liens Utiles
- Open-WebUI : http://localhost:3000 (si installé localement)
- OpenRouter : https://openrouter.ai/ (pour crédits API)
- Documentation officielle : voir README.md

## 🎓 Instructions pour les Étudiants

### Pré-requis Techniques
- **VS Code** 1.60.0+ installé et fonctionnel
- **Accès Internet** stable
- **PowerShell** 5.1+ (Windows) ou bash/zsh (macOS/Linux)
- **Clé API OpenRouter** : Fournie par le formateur

### Préparation Avant la Session
1. Installer VS Code si pas déjà fait
2. Tester la connexion internet
3. Avoir un compte GitHub (pour le projet)

### Pendant la Session
1. Suivre le guide d'installation étape par étape
2. Ne pas hésiter à demander de l'aide
3. Tester chaque fonctionnalité présentée
4. Prendre des notes sur les difficultés rencontrées

### Après la Session
1. Compléter les démos non terminées
2. Explorer les modules 04 et 05 en autonomie
3. Préparer questions pour la session 2
4. Commencer à réfléchir au projet final

## 🛠️ Préparation Enseignant

### Vérifications Techniques Pré-session

- [ ] VS Code + Roo/Claude Code fonctionnel sur machine de démonstration
- [ ] Clés API OpenRouter actives et créditées
- [ ] Open-WebUI configuré et accessible (optionnel)
- [ ] Slides PowerPoint testés et mis à jour
- [ ] Exemples pratiques vérifiés
- [ ] Connexion internet stable (WiFi + backup 4G)

### Matériel à Préparer

- [ ] Clés API OpenRouter pour les étudiants
- [ ] Liste des noms pour workspaces
- [ ] Guides PDF imprimés (backup si problème réseau)
- [ ] Exemples de prompts efficaces
- [ ] FAQ préparée

### Infrastructure

- [ ] Projecteur et écran fonctionnels
- [ ] Micro si grande salle
- [ ] Tableau blanc pour schémas
- [ ] Prises électriques accessibles

## ⏱️ Planning Détaillé

| Horaire | Activité | Durée | Support |
|---------|----------|-------|---------|
| 13:30-14:30 | Introduction théorique | 60 min | PowerPoint + INTRO-GENAI.md |
| 14:30-15:15 | Installation & Configuration | 45 min | INSTALLATION-*.md |
| 15:15-15:30 | **PAUSE** | 15 min | - |
| 15:30-16:00 | Atelier Découverte | 30 min | Demo 1-2 |
| 16:00-16:30 | Atelier Orchestration | 30 min | Demo 3-4 |
| 16:30-17:00 | Atelier Assistant Pro | 30 min | Demo 5-6 |
| 17:00-17:30 | Synthèse & Questions | 30 min | Discussion |

## 📝 Points d'Attention

### Gestion des Difficultés Techniques

**Problème réseau** :
- Avoir modèles locaux prêts en backup (Ollama)
- Exemples pré-générés disponibles
- Guides PDF hors-ligne

**Installation échouée** :
- Machines de démonstration partagées
- Sessions en binômes
- Support individuel après session

**Versions incompatibles** :
- Guide de dépannage dans INSTALLATION-*.md
- Versions testées documentées
- Alternative navigateur (OpenRouter web)

### Adaptation du Rythme

**Groupe rapide** :
- Modules 04 et 05 disponibles
- Projets personnels suggérés
- Exploration MCP servers avancés

**Groupe lent** :
- Focus sur démos 1-2-3 seulement
- Reporter démos 4-5-6 en autonomie
- Support renforcé post-session

**Questions fréquentes** :
- FAQ préparée et distribuée
- Documentation complète dans docs/
- Canal Discord/Moodle pour questions asynchrones

## 🔗 Intégration Moodle

### Structure Recommandée

**Section "Session 1 - Introduction et Premiers Pas"**
- 📊 Slides : Intelligence Artificielle - 8 - IA Générative.pptx
- 📘 Guide installation (selon outil choisi)
- 📋 Parcours guidé : ROO-GUIDED-PATH.md
- 📦 Matériel pratique : Ateliers-roo-code.zip
- 🔗 Référence outils : INTRO-GENAI.md

**Section "Ressources Complémentaires"**
- 💡 Documentation OpenRouter
- 📚 Documentation officielle Roo/Claude Code
- 🎥 Vidéos de démonstration (à créer)
- 🔗 Awesome Claude Code / Roo Community

**Section "Forum de Discussion"**
- Questions techniques
- Partage d'expériences
- Entraide entre étudiants

## 📊 Évaluation

**Pas d'évaluation formelle pour la Session 1**, mais :

- **Participation** : Notée informellement
- **Installation réussie** : Vérifiée en fin de session
- **Compréhension** : Évaluée via questions/réponses

**Feedback demandé** :
- Difficulté de l'installation (1-5)
- Clarté des explications (1-5)
- Suggestions d'amélioration

## 📚 Ressources Complémentaires

### Pour Approfondir

**IA Générative** :
- [Microsoft Generative AI for Beginners](https://github.com/microsoft/generative-ai-for-beginners)
- Attention Is All You Need (paper original)

**Roo Code** :
- Documentation complète dans Ateliers-roo-code/
- Communauté Discord

**Claude Code** :
- [Documentation officielle](https://code.claude.com/docs)
- [Best Practices](https://www.anthropic.com/engineering/claude-code-best-practices)

**Prompt Engineering** :
- OpenAI Prompt Engineering Guide
- Anthropic Claude Prompt Library

### Lectures Recommandées

Pour la prochaine session :
- Lire [Activités-GenAI.md](../activites/Activites-GenAI.md) en entier
- Explorer les notebooks Python fournis
- Tester différents paramètres de génération

---

## ✅ Checklist Finale

**Veille de la session** :
- [ ] Tous les supports sont à jour
- [ ] Clés API créditées et testées
- [ ] Machines de démo fonctionnelles
- [ ] Salle réservée et équipée
- [ ] Étudiants informés (rappel email)

**Jour J - 30 min avant** :
- [ ] Projecteur testé
- [ ] Slides chargées
- [ ] VS Code + extension ouverts
- [ ] Connexion internet vérifiée
- [ ] Documents d'urgence accessibles

**Pendant la session** :
- [ ] Chronométrer les parties
- [ ] Noter les questions récurrentes
- [ ] Observer les difficultés techniques
- [ ] Recueillir le feedback

**Après la session** :
- [ ] Mettre à jour FAQ si nécessaire
- [ ] Envoyer ressources complémentaires
- [ ] Répondre aux questions Moodle/Discord
- [ ] Préparer Session 2

---

*Guide préparé pour EPF 2026 - Session du 10 septembre 2025*
*Dernière mise à jour : Janvier 2026*
