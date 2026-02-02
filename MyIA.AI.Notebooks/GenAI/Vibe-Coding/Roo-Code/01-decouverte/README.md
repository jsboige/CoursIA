# 🔍 Découverte de Roo : Votre assistant personnel intelligent

## Présentation des démos disponibles

Ce répertoire contient plusieurs démos pour vous aider à découvrir les capacités de Roo, votre assistant personnel intelligent. Chaque démo est organisée dans un sous-répertoire dédié avec sa propre documentation et ressources.

### Liste des démos

1. **[Demo 1 - Conversation avec Roo](./demo-1-conversation/README.md)**
   - Découvrez les bases de l'interaction avec Roo
   - Apprenez à poser des questions efficaces
   - Explorez les cas d'usage professionnels et personnels

2. **[Demo 2 - Vision avec Roo](./demo-2-vision/README.md)**
   - Découvrez comment Roo peut analyser des images
   - Apprenez à poser des questions sur des contenus visuels
   - Explorez différents types d'analyses visuelles

3. **[Demo 3 - Organisation et productivité](./demo-3-organisation/README.md)**
   - Utilisez Roo pour organiser vos documents
   - Planifiez efficacement votre temps
   - Améliorez votre productivité quotidienne

4. **[Demo 4 - Questions techniques et conceptuelles](./demo-4-questions/README.md)**
   - Posez des questions complexes à Roo
   - Obtenez des explications claires sur des sujets techniques
   - Approfondissez vos connaissances dans divers domaines

## Structure des démos

Chaque démo est organisée de la même façon :

- **README.md** : Instructions détaillées pour réaliser la démo
- **workspace/** : Répertoire où se déroule la démo (sera nettoyé lors de la réinitialisation)
- **ressources/** : Fichiers nécessaires à la démo (ne seront pas modifiés)
- **docs/** : Documentation supplémentaire pour les agents

## Comment utiliser ces démos

1. Lisez le README.md de la démo qui vous intéresse
2. Exécutez le script de préparation pour initialiser l'espace de travail depuis la racine du projet :
   ```
   # Depuis la racine du sous-dossier Demo roo-code
   ./prepare-workspaces.ps1 -UserName "VotreNom"   # Windows
   ```
   Remplacez "VotreNom" par votre nom d'utilisateur souhaité.
3. Suivez les instructions spécifiques à chaque démo
4. Expérimentez librement dans le répertoire workspace

> **Note importante** : Le contenu des répertoires workspace sera nettoyé lors de la réinitialisation du projet. Si vous souhaitez conserver vos expérimentations, pensez à les sauvegarder ailleurs.

## Prochaines étapes

Une fois que vous avez exploré ces démos de base, vous pouvez passer aux sections plus avancées :

- [02-orchestration-taches](../02-orchestration-taches/) : Apprenez à gérer des tâches plus complexes
- [03-assistant-pro](../03-assistant-pro/) : Découvrez comment Roo peut vous assister dans un contexte professionnel
- [04-creation-contenu](../04-creation-contenu/) : Explorez les capacités de création de contenu
- [05-projets-avances](../05-projets-avances/) : Plongez dans des projets plus complexes et avancés

> **Note sur l'intégration**: Ce projet fait partie d'un dépôt plus large. Pour plus d'informations sur l'intégration, consultez le fichier [README-integration.md](../README-integration.md) à la racine du sous-dossier.