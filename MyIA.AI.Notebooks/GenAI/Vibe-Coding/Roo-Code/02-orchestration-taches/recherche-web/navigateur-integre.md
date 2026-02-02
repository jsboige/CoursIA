# 🌐 Utilisation du Navigateur Intégré dans Roo

## Introduction

Le navigateur intégré est l'un des outils les plus puissants de Roo, lui permettant de visualiser et d'interagir avec des pages web comme le ferait un utilisateur humain. Cette fonctionnalité est basée sur Puppeteer, une bibliothèque qui permet le contrôle automatisé d'un navigateur Chrome headless.

## Fonctionnalités principales

Le navigateur intégré permet à Roo de :

- Visiter des sites web et visualiser leur contenu
- Capturer des captures d'écran des pages visitées
- Cliquer sur des éléments interactifs (boutons, liens, etc.)
- Remplir des formulaires et soumettre des données
- Extraire des informations de pages web
- Surveiller les logs de la console du navigateur
- Tester des applications web

## Syntaxe d'utilisation

Pour utiliser le navigateur intégré, Roo utilise l'outil `browser_action` avec différentes actions :

```
<browser_action>
<action>TYPE_D'ACTION</action>
<paramètres_spécifiques>valeurs</paramètres_spécifiques>
</browser_action>
```

### Actions disponibles

| Action | Description | Paramètres |
|--------|-------------|------------|
| `launch` | Ouvre le navigateur à l'URL spécifiée | `<url>https://exemple.com</url>` |
| `click` | Clique à des coordonnées spécifiques | `<coordinate>x,y</coordinate>` |
| `hover` | Survole un élément à des coordonnées spécifiques | `<coordinate>x,y</coordinate>` |
| `type` | Saisit du texte | `<text>Texte à saisir</text>` |
| `scroll_down` | Fait défiler la page vers le bas | - |
| `scroll_up` | Fait défiler la page vers le haut | - |
| `resize` | Redimensionne la fenêtre du navigateur | `<size>largeur,hauteur</size>` |
| `close` | Ferme le navigateur | - |

## Exemples d'utilisation

### Exemple 1 : Recherche Google simple

```
# Lancement du navigateur sur Google
<browser_action>
<action>launch</action>
<url>https://www.google.com</url>
</browser_action>

# Clic sur le champ de recherche (coordonnées à adapter selon la capture d'écran)
<browser_action>
<action>click</action>
<coordinate>640,350</coordinate>
</browser_action>

# Saisie du texte de recherche
<browser_action>
<action>type</action>
<text>Roo Code Assistant documentation</text>
</browser_action>

# Fermeture du navigateur après consultation
<browser_action>
<action>close</action>
</browser_action>
```

### Exemple 2 : Consultation d'une documentation technique

```
# Lancement du navigateur sur la documentation
<browser_action>
<action>launch</action>
<url>https://docs.python.org/fr/3/</url>
</browser_action>

# Clic sur le champ de recherche (coordonnées à adapter)
<browser_action>
<action>click</action>
<coordinate>1100,120</coordinate>
</browser_action>

# Saisie du terme de recherche
<browser_action>
<action>type</action>
<text>list comprehension</text>
</browser_action>

# Défilement pour voir plus de contenu
<browser_action>
<action>scroll_down</action>
</browser_action>

# Fermeture du navigateur
<browser_action>
<action>close</action>
</browser_action>
```

### Exemple 3 : Test d'une application web locale

```
# Lancement du navigateur sur l'application locale
<browser_action>
<action>launch</action>
<url>http://localhost:3000</url>
</browser_action>

# Interaction avec l'interface (clic sur un bouton)
<browser_action>
<action>click</action>
<coordinate>500,300</coordinate>
</browser_action>

# Saisie dans un formulaire
<browser_action>
<action>click</action>
<coordinate>500,400</coordinate>
</browser_action>

<browser_action>
<action>type</action>
<text>Données de test</text>
</browser_action>

# Fermeture après vérification
<browser_action>
<action>close</action>
</browser_action>
```

## Bonnes pratiques

### Détermination des coordonnées

Pour déterminer les coordonnées précises pour les actions `click` et `hover` :

1. Analysez attentivement la capture d'écran fournie par Roo
2. Estimez le centre de l'élément avec lequel vous souhaitez interagir
3. Utilisez la résolution standard de 1280x800 pixels comme référence

### Séquence d'actions

- **Toujours commencer** par l'action `launch` pour ouvrir le navigateur
- **Toujours terminer** par l'action `close` pour fermer proprement le navigateur
- Effectuer une seule action à la fois et attendre la réponse (capture d'écran)
- Adapter les actions suivantes en fonction de ce qui est visible sur la capture d'écran

### Optimisation des performances

- Limitez le nombre d'actions pour éviter de consommer trop de ressources
- Utilisez des URL précises pour accéder directement au contenu souhaité
- Préférez Jinavigator ou SearXNG pour les recherches simples d'information

## Limitations

- Résolution fixe de 1280x800 pixels
- Une seule action possible par message
- Pas d'accès aux cookies ou au stockage local entre les sessions
- Certains sites peuvent bloquer l'accès via un navigateur automatisé
- Les éléments dynamiques peuvent changer de position, rendant les coordonnées obsolètes

## Intégration avec le mode Orchestrator

Le mode Orchestrator peut utiliser le navigateur intégré comme l'un des outils dans une séquence d'actions :

1. Rechercher des informations générales avec SearXNG
2. Visiter un site spécifique avec le navigateur intégré pour vérifier visuellement
3. Extraire le contenu structuré avec Jinavigator pour analyse
4. Utiliser ces informations pour générer du code ou résoudre un problème

## Cas d'usage avancés

- Vérification visuelle de sites web après déploiement
- Test d'interfaces utilisateur
- Capture de données dynamiques non accessibles via API
- Interaction avec des applications web complexes
- Démonstration visuelle de fonctionnalités