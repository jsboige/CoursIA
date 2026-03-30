# 👁️ Demo 2 - Vision avec Roo

## Objectif de la démo

Cette démo vous permet de découvrir les capacités de vision de Roo, qui lui permettent d'analyser des images et de répondre à des questions à leur sujet. Vous apprendrez comment soumettre des images à Roo et comment poser des questions efficaces pour obtenir des analyses pertinentes.

## Introduction aux capacités de vision

Claude, le modèle qui alimente Roo, possède des capacités multimodales qui lui permettent de "voir" et d'analyser des images. Cette fonctionnalité est particulièrement utile pour :

- Analyser des captures d'écran de code ou d'interfaces
- Comprendre des diagrammes techniques
- Interpréter des graphiques et des visualisations de données
- Examiner des maquettes ou des designs d'interface
- Analyser des erreurs visuelles dans des applications

## Prérequis

- Avoir accès à Roo dans VSCode
- Disposer d'images à analyser (des exemples sont fournis dans le répertoire ressources)

## Instructions pas à pas

### 1. Préparation de l'environnement

1. Assurez-vous que le contenu du répertoire workspace est initialisé :
   ```
   ./prepare-workspaces.ps1 -UserName "VotreNom"   # Windows
   ```
   Remplacez "VotreNom" par votre nom d'utilisateur souhaité.

2. Dans l'explorateur de fichiers VSCode, naviguez jusqu'au dossier `01-decouverte/demo-2-vision/workspace`

3. Ouvrez le panneau Roo en cliquant sur l'icône Roo dans la barre latérale

4. Sélectionnez le mode "Conversation" (💬 Ask)

### 2. Soumettre une image à Roo

Il existe plusieurs façons de soumettre une image à Roo :

- **Glisser-déposer** une image directement dans la zone de conversation
- **Copier-coller** une image depuis votre presse-papiers
- **Utiliser le bouton d'upload** pour sélectionner une image depuis votre système de fichiers
- **Faire une capture d'écran** et la partager directement avec Roo

Pour cette démo, vous pouvez utiliser les images fournies dans le répertoire `ressources`.

### 3. Poser des questions sur l'image

Accompagnez votre image d'une question ou d'une instruction claire pour obtenir les meilleurs résultats :

✅ **Efficace** : "Que représente ce diagramme d'architecture ?"  
✅ **Efficace** : "Explique ce qui pourrait causer l'erreur visible sur cette capture d'écran."  
✅ **Efficace** : "Analyse cette maquette d'interface et suggère des améliorations d'UX."

❌ **Moins efficace** : "Que vois-tu ?" (trop vague)  
❌ **Moins efficace** : "Aide-moi avec cette image." (manque de direction)

### 4. Explorer différents types d'analyses visuelles

Essayez ces différents types d'analyses avec les images appropriées :

#### Analyse de code
- Soumettez une capture d'écran de code et demandez : "Identifie les bugs potentiels dans ce code."
- Ou : "Comment pourrais-je optimiser ce code ?"

#### Analyse de diagrammes techniques
- Soumettez un diagramme d'architecture et demandez : "Explique ce que représente ce diagramme."
- Ou : "Quels sont les composants clés de cette architecture ?"

#### Analyse d'interfaces utilisateur
- Soumettez une capture d'écran d'interface et demandez : "Quels problèmes d'UX identifies-tu dans cette interface ?"
- Ou : "Comment pourrais-je améliorer cette interface utilisateur ?"

#### Analyse de données visuelles
- Soumettez un graphique ou un tableau et demandez : "Que montrent ces données ?"
- Ou : "Quelles conclusions peut-on tirer de ce graphique ?"

### 5. Poser des questions de suivi

Vous pouvez approfondir l'analyse en posant des questions de suivi sur la même image :

- "Peux-tu me donner plus de détails sur la partie X de l'image ?"
- "Comment pourrais-je améliorer ce design ?"
- "Y a-t-il des problèmes potentiels dans ce code que tu peux identifier ?"

## Exercice pratique

1. Choisissez une image du répertoire ressources ou utilisez votre propre image
2. Soumettez-la à Roo avec une question initiale
3. Posez au moins deux questions de suivi pour approfondir l'analyse
4. Notez vos observations sur la qualité et la pertinence des réponses

## Guide détaillé des questions d'analyse

### Questions générales d'analyse

Commencez par des questions générales pour obtenir une vue d'ensemble :

1. "Décris en détail ce que tu vois dans cette image."
2. "De quel type de diagramme ou de visualisation s'agit-il ?"
3. "Quel est le sujet principal représenté dans cette image ?"
4. "Résume les informations clés présentées dans ce visuel."

### Questions spécifiques pour un diagramme d'architecture

Si vous utilisez un diagramme d'architecture :

#### Analyse structurelle

5. "Identifie les principaux composants de cette architecture et explique leurs rôles."
6. "Quelles sont les relations entre les différentes couches de cette architecture ?"
7. "Trace le parcours d'une requête utilisateur à travers ce système, de l'interface jusqu'à la base de données."
8. "Quels patterns d'architecture reconnaissables sont implémentés dans ce diagramme ?"

#### Analyse critique

9. "Quels sont les points forts de cette architecture ?"
10. "Identifie les potentiels points faibles ou goulots d'étranglement dans cette conception."
11. "Comment cette architecture pourrait-elle être améliorée pour une meilleure scalabilité ?"
12. "Y a-t-il des composants redondants ou manquants dans cette architecture ?"

#### Questions techniques approfondies

13. "Comment la sécurité est-elle gérée dans cette architecture ?"
14. "Explique comment le système gère probablement la mise en cache et la performance."
15. "Quelles technologies spécifiques sont mentionnées ou suggérées dans ce diagramme ?"
16. "Comment ce système gérerait-il une panne d'un de ses composants ?"

### Questions pour d'autres types d'images techniques

#### Pour une capture d'écran de code

17. "Analyse ce code et explique ce qu'il fait."
18. "Y a-t-il des bugs ou des problèmes potentiels dans ce code ?"
19. "Comment ce code pourrait-il être optimisé ou amélioré ?"
20. "Quel pattern de conception est utilisé dans ce code ?"

#### Pour une interface utilisateur

21. "Évalue cette interface utilisateur du point de vue de l'expérience utilisateur."
22. "Quels principes de design sont appliqués dans cette interface ?"
23. "Comment cette interface pourrait-elle être améliorée pour une meilleure accessibilité ?"
24. "Identifie les éléments clés de cette interface et leur fonction."

#### Pour un graphique ou une visualisation de données

25. "Interprète les tendances principales montrées dans ce graphique."
26. "Quelles conclusions peut-on tirer de ces données visualisées ?"
27. "Comment cette visualisation pourrait-elle être améliorée pour une meilleure clarté ?"
28. "Y a-t-il des anomalies ou des points de données intéressants dans ce graphique ?"

### Questions de suivi approfondies

Après la première analyse, posez des questions plus spécifiques :

29. "Peux-tu me donner plus de détails sur [composant spécifique mentionné dans la réponse] ?"
30. "Comment [technologie identifiée] s'intègre-t-elle avec le reste du système ?"
31. "Si nous devions moderniser cette architecture, quelles technologies recommanderais-tu ?"
32. "Explique le compromis entre [deux aspects mentionnés dans la réponse]."

## Exercices pratiques avancés

Pour une expérience plus interactive, essayez ces exercices :

### Exercice 1 : Analyse comparative
1. Montrez l'image à Roo
2. Demandez : "Quels sont les avantages et inconvénients de cette architecture par rapport à une architecture [alternative pertinente] ?"

### Exercice 2 : Évolution architecturale
1. Montrez l'image à Roo
2. Demandez : "Comment cette architecture pourrait-elle évoluer pour intégrer [nouvelle technologie ou tendance] ?"

### Exercice 3 : Diagnostic de problème
1. Montrez l'image à Roo
2. Proposez un scénario : "Si les utilisateurs se plaignent de lenteurs lors des pics d'utilisation, quels composants de cette architecture devraient être examinés en premier et pourquoi ?"

## Bonnes pratiques

- **Utilisez des images claires et nettes** pour de meilleurs résultats
- **Cadrez bien le sujet principal** de votre image
- **Posez des questions spécifiques** plutôt que générales
- **Fournissez du contexte** lorsque nécessaire
- **Combinez texte et image** pour une communication plus efficace
- **Soyez spécifique** dans vos questions
- **Commencez par des questions générales** avant de passer aux détails
- **Référencez des éléments visuels précis** ("le composant en haut à droite", "la section bleue")
- **Demandez des explications** sur les termes techniques que Roo utilise
- **Explorez différents angles** (sécurité, performance, maintenabilité)

## Limites actuelles

- Roo ne peut pas analyser de vidéos, seulement des images statiques
- La résolution et la qualité de l'image affectent la précision de l'analyse
- Certains détails très fins ou textes très petits peuvent être difficiles à interpréter
- Roo ne peut pas exécuter le code visible dans une image

## Ressources supplémentaires

Dans le répertoire `ressources`, vous trouverez :
- Des exemples d'images à utiliser pour vos tests
- Un guide détaillé sur les capacités de vision de Roo
- Des exemples de questions efficaces pour différents types d'images

## Guide pour les formateurs et agents

### Objectif de la démo pour les formateurs

Cette démo vise à présenter les capacités de vision de Roo, permettant aux utilisateurs de découvrir comment soumettre des images à l'assistant et obtenir des analyses pertinentes. Elle montre comment Roo peut "voir" et comprendre le contenu visuel, offrant ainsi une dimension supplémentaire à l'interaction.

### Déroulement suggéré de la démo

1. **Introduction** (2-3 minutes)
   - Présentez les capacités de vision de Roo
   - Expliquez l'objectif de la démo

2. **Première analyse d'image** (3-4 minutes)
   - Choisissez une image simple comme le diagramme UML dans les ressources
   - Posez une question comme "Peux-tu m'expliquer ce que représente ce diagramme ?"
   - Commentez la réponse et soulignez les points importants

3. **Démonstration de différents types d'analyses** (5-7 minutes)
   - Montrez l'analyse d'une capture d'écran de code
   - Montrez l'analyse d'une interface utilisateur
   - Montrez l'analyse d'un graphique ou tableau de données

4. **Questions de suivi et approfondissement** (3-4 minutes)
   - Sur une même image, posez des questions de suivi pour approfondir l'analyse
   - Montrez comment Roo peut se concentrer sur des parties spécifiques de l'image

5. **Conseils et bonnes pratiques** (2-3 minutes)
   - Partagez des conseils pour obtenir les meilleures analyses
   - Expliquez les limites actuelles des capacités de vision

6. **Questions du public** (5-10 minutes)
   - Invitez les participants à soumettre leurs propres images
   - Guidez-les pour formuler des questions efficaces

### Questions fréquemment posées

#### "Roo peut-il analyser des vidéos ?"
Réponse suggérée : "Actuellement, Roo ne peut analyser que des images statiques, pas des vidéos. Pour analyser une vidéo, vous devriez extraire des images clés et les soumettre individuellement."

#### "Quelle est la résolution d'image optimale pour l'analyse ?"
Réponse suggérée : "Roo fonctionne mieux avec des images claires et de résolution moyenne à élevée. Les images trop petites ou floues peuvent être difficiles à analyser avec précision."

#### "Roo peut-il exécuter le code qu'il voit dans une image ?"
Réponse suggérée : "Non, Roo peut analyser et comprendre le code visible dans une image, mais il ne peut pas l'exécuter directement. Il peut toutefois vous aider à retranscrire ce code pour que vous puissiez l'exécuter vous-même."

#### "Les images sont-elles stockées quelque part après l'analyse ?"
Réponse suggérée : "Les images sont traitées pour l'analyse mais ne sont pas stockées de manière permanente après la session. Comme pour toutes les interactions avec Roo, il est recommandé de ne pas partager d'informations sensibles ou confidentielles."

### Conseils pour une démo réussie

- **Préparez vos images à l'avance** et assurez-vous qu'elles sont de bonne qualité
- **Testez vos exemples** avant la démo pour éviter les surprises
- **Ayez plusieurs types d'images** prêtes pour montrer la polyvalence de Roo
- **Commentez les réponses de Roo** pour souligner les points importants
- **Gérez les attentes** en expliquant ce que Roo peut et ne peut pas faire avec les images

## Prochaines étapes

Après avoir exploré cette démo, vous pouvez :
- Revenir à la [Demo 1 - Conversation avec Roo](../demo-1-conversation/README.md) pour approfondir vos connaissances sur les interactions textuelles
- Passer à la [Demo 3 - Organisation et productivité](../demo-3-organisation/README.md) pour des cas d'usage plus spécifiques
- Explorer la [Demo 4 - Questions techniques et conceptuelles](../demo-4-questions/README.md) pour des sujets plus complexes

---

Ces instructions vous aideront à explorer efficacement les capacités de vision de Roo et à comprendre comment elles peuvent être appliquées à des tâches techniques réelles dans votre flux de travail de développement.