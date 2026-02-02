# 💬 Demo 1 - Conversation avec Roo

## Objectif de la démo

Cette démo vous permet de découvrir les bases de l'interaction avec Roo en mode conversation. Vous apprendrez comment poser des questions efficaces et explorer différents cas d'usage, tant professionnels que personnels.

## Prérequis

- Avoir accès à Roo dans VSCode
- Aucune connaissance préalable en IA n'est nécessaire

## Instructions pas à pas

### 1. Préparation de l'environnement

1. Assurez-vous que le contenu du répertoire workspace est initialisé :
   ```
   ./prepare-workspaces.ps1 -UserName "VotreNom"   # Windows
   ```
   Remplacez "VotreNom" par votre nom d'utilisateur souhaité.

2. Dans l'explorateur de fichiers VSCode, naviguez jusqu'au dossier `01-decouverte/demo-1-conversation/workspace`

3. Ouvrez le panneau Roo en cliquant sur l'icône Roo dans la barre latérale

4. Sélectionnez le mode "Conversation" (💬 Ask)

### 2. Votre première conversation

Commencez par une question simple pour vous familiariser avec Roo :

```
Bonjour Roo, comment peux-tu m'aider dans mon travail quotidien ?
```

Observez comment Roo répond et présente ses capacités.

### 3. Explorer les cas d'usage professionnels

Essayez ces exemples de questions professionnelles :

- **Assistance administrative** :
  ```
  Aide-moi à rédiger un email professionnel pour demander un report de réunion.
  ```

- **Analyse et synthèse** :
  ```
  Comment puis-je structurer efficacement un rapport d'analyse pour mon équipe ?
  ```

- **Préparation de présentations** :
  ```
  Donne-moi des conseils pour créer une présentation plus engageante.
  ```

### 4. Explorer les cas d'usage personnels

Essayez ces exemples de questions personnelles :

- **Organisation** :
  ```
  Peux-tu me suggérer un système simple pour organiser mes documents personnels ?
  ```

- **Apprentissage** :
  ```
  Explique-moi simplement comment fonctionne [un sujet qui vous intéresse].
  ```

- **Loisirs** :
  ```
  Donne-moi des idées d'activités créatives à faire ce weekend.
  ```

### 5. Améliorer vos questions

Pratiquez l'art de poser des questions efficaces :

#### Exemple 1 : Question vague vs. question précise

❌ **Inefficace** : "Aide-moi avec mon projet."  
✅ **Efficace** : "Aide-moi à organiser les étapes de mon projet de développement d'application mobile."

#### Exemple 2 : Ajouter du contexte

❌ **Inefficace** : "Comment rédiger un email ?"  
✅ **Efficace** : "Comment rédiger un email pour demander un délai supplémentaire à un client important ?"

#### Exemple 3 : Questions de suivi

Après avoir reçu une réponse, approfondissez avec des questions comme :
- "Peux-tu développer ce point ?"
- "Comment appliquer ce conseil dans mon cas spécifique ?"
- "As-tu un exemple concret de cette approche ?"

## Exercice pratique

Créez un nouveau fichier dans le répertoire workspace nommé `mes_questions.md` et notez-y :

1. Trois questions professionnelles que vous pourriez poser à Roo
2. Trois questions personnelles que vous pourriez poser à Roo
3. Une question vague que vous pourriez améliorer
4. La version améliorée de cette question

Posez ensuite ces questions à Roo et observez les réponses.

## Ressources supplémentaires

Dans le répertoire `ressources`, vous trouverez :
- Une liste étendue d'exemples de questions
- Des conseils pour formuler des questions efficaces
- Des cas d'usage spécifiques à différents domaines professionnels

## Documentation pour les agents

Dans le répertoire `docs`, vous trouverez :
- Des explications détaillées sur le fonctionnement du mode conversation
- Des conseils pour guider les utilisateurs dans leur découverte de Roo
- Des réponses aux questions fréquemment posées

## Prochaines étapes

Après avoir exploré cette démo, vous pouvez :
- Passer à la [Demo 2 - Vision avec Roo](../demo-2-vision/README.md) pour découvrir les capacités visuelles de Roo
- Explorer les autres sections du dossier [01-decouverte](../../01-decouverte/README.md) pour plus d'exemples et de cas d'usage
- Découvrir les fonctionnalités avancées dans [02-orchestration-taches](../../02-orchestration-taches/README.md) et [03-assistant-pro](../../03-assistant-pro/README.md)