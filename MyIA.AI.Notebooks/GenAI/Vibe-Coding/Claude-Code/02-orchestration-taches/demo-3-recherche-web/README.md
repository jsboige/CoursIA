# Demo 3 - Recherche Web

## Objectif

Utiliser les outils WebSearch et WebFetch pour intégrer des informations externes dans votre workflow de développement.

## Durée estimée

**30 minutes**

## Concepts

### Outils de recherche web

Claude Code dispose de deux outils pour accéder au web :

| Outil | Description | Usage |
|-------|-------------|-------|
| **WebSearch** | Recherche sur le web | Trouver des informations, docs, actualités |
| **WebFetch** | Récupérer une page | Lire le contenu d'une URL spécifique |

### Cas d'usage

- **Documentation** : Trouver la doc officielle d'une bibliothèque
- **Comparaison** : Comparer des technologies
- **Veille** : Se tenir à jour sur les nouveautés
- **Débogage** : Chercher des solutions à des erreurs
- **Bonnes pratiques** : Trouver les recommandations actuelles

## Étapes

### Étape 1 : Recherche simple (5 min)

Lancez Claude Code et testez une recherche basique :

```
Recherche les meilleures pratiques pour sécuriser une API REST en 2026
```

Observez :
- Les sources citées
- La synthèse des informations
- Les recommandations concrètes

### Étape 2 : Recherche de documentation (10 min)

#### Trouver une documentation

```
Recherche la documentation officielle de FastAPI pour les dépendances (Depends)
```

#### Récupérer une page spécifique

```
Récupère et résume cette page : https://fastapi.tiangolo.com/tutorial/dependencies/
```

#### Extraire des exemples

```
Depuis la documentation FastAPI, montre-moi 3 exemples d'utilisation de Depends
pour l'injection de dépendances
```

### Étape 3 : Comparaison technologique (10 min)

#### Demander une comparaison

```
Recherche et compare SQLAlchemy vs Tortoise-ORM pour une application FastAPI :
- Performance
- Facilité d'utilisation
- Support async
- Communauté et maintenance
```

#### Approfondir un point

```
Recherche des benchmarks récents comparant les performances de SQLAlchemy 2.0
en mode async vs Tortoise-ORM
```

### Étape 4 : Veille et actualités (5 min)

#### Nouveautés technologiques

```
Quelles sont les nouveautés majeures de Python 3.13 ?
Recherche les annonces officielles.
```

#### Tendances

```
Recherche les tendances 2026 pour les architectures backend Python.
Quels frameworks et patterns émergent ?
```

## Exercice pratique

### Mission

Réalisez une veille technologique sur un sujet de votre choix et produisez un rapport.

### Étapes

1. Choisissez un sujet (suggestion : "Tests en Python 2026")

2. Recherchez les informations :
   ```
   Recherche les meilleures bibliothèques de test Python en 2026.
   Compare pytest, unittest, et les nouvelles options.
   ```

3. Approfondissez :
   ```
   Récupère la documentation de pytest sur les fixtures avancées
   ```

4. Synthétisez :
   ```
   Génère un rapport de veille technologique sur les tests Python
   incluant : état de l'art, recommandations, et ressources.
   ```

### Livrable

Fichier `veille-techno.md` avec :
- Résumé des recherches
- Sources utilisées
- Recommandations
- Liens utiles

## Bonnes pratiques

### Formuler des recherches efficaces

**Moins efficace :**
```
Recherche Python
```

**Plus efficace :**
```
Recherche les meilleures pratiques de gestion d'erreurs en Python 3.12+
pour les applications de production
```

### Vérifier les sources

Toujours demander :
```
Quelles sont tes sources pour ces informations ?
```

### Dater les informations

```
Recherche les changements dans Django depuis la version 4.0 jusqu'à aujourd'hui
```

### Combiner recherche et contexte projet

```
@src/models.py Recherche comment migrer ce code SQLAlchemy vers la syntaxe 2.0
```

## Exemples de prompts

### Documentation

```
Recherche la documentation de [bibliothèque] pour [fonctionnalité].
Montre-moi un exemple d'utilisation.
```

### Débogage

```
Je rencontre cette erreur : [message d'erreur]
Recherche les causes possibles et solutions.
```

### Comparaison

```
Compare [option1] et [option2] pour [cas d'usage].
Inclus : performance, facilité d'utilisation, communauté.
```

### Veille

```
Quelles sont les nouveautés de [technologie] en [année] ?
Quels changements impactent [type de projet] ?
```

### Bonnes pratiques

```
Recherche les recommandations [OWASP/Google/etc.] pour [sujet]
applicables à [contexte].
```

## Limitations

- **Informations datées** : Les résultats peuvent contenir des infos obsolètes
- **Qualité variable** : Toutes les sources ne sont pas fiables
- **Disponibilité** : Certains sites peuvent être inaccessibles
- **Langue** : Meilleurs résultats en anglais pour les sujets techniques

## Points clés à retenir

1. **WebSearch** pour découvrir, **WebFetch** pour approfondir

2. **Soyez spécifique** dans vos recherches

3. **Vérifiez les sources** et les dates

4. **Combinez** avec le contexte de votre projet

5. **Synthétisez** les informations en documentation

---

**Prochaine étape** : [Atelier 03 - Assistant Développeur](../../03-assistant-developpeur/)
