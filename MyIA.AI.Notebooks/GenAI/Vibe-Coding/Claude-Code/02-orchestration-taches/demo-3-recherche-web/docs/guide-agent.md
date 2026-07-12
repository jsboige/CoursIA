# Guide Agent - Demo 3 : Recherche Web

Ce guide est destiné aux formateurs et agents IA pour accompagner les apprenants.

## Objectifs de la démo

- Utiliser WebSearch pour trouver des informations
- Utiliser WebFetch pour récupérer du contenu spécifique
- Synthétiser des informations de sources multiples
- Vérifier la fiabilité des sources

## Points de vigilance

### Qualité des recherches

1. **Recherches trop vagues**
   - "Python" → Résultats trop larges
   - Encourager la précision : "gestion mémoire Python 3.12"

2. **Dépendance excessive**
   - Ne pas tout chercher sur le web
   - La connaissance intégrée de Claude est souvent suffisante

### Fiabilité des informations

1. **Sources non vérifiées**
   - Toujours demander les sources
   - Privilégier la documentation officielle

2. **Informations obsolètes**
   - Vérifier les dates
   - Demander des informations récentes explicitement

## Déroulé suggéré

### Phase 1 : Introduction (5 min)

Expliquer :
- Différence entre WebSearch et WebFetch
- Quand utiliser la recherche web vs connaissances intégrées
- Importance de vérifier les sources

### Phase 2 : Démo WebSearch (10 min)

Montrer plusieurs types de recherches :
1. Documentation technique
2. Comparaison de technologies
3. Recherche de solutions à un problème

### Phase 3 : Démo WebFetch (5 min)

Montrer :
1. Récupérer une page de documentation
2. Extraire des exemples de code
3. Résumer un article technique

### Phase 4 : Exercice (10 min)

Veille technologique sur un sujet au choix.

## Réponses aux questions fréquentes

### "Claude peut-il accéder à n'importe quel site ?"

La plupart des sites publics sont accessibles. Exceptions :
- Sites nécessitant authentification
- Contenu derrière paywall
- Sites bloquant les bots

### "Les recherches sont-elles en temps réel ?"

Oui, WebSearch utilise des résultats actuels. Cependant, le contenu des pages peut être mis en cache brièvement.

### "Comment savoir si l'information est fiable ?"

Critères de fiabilité :
- Source officielle (docs, blog officiel)
- Date récente
- Auteur identifié
- Cohérence avec d'autres sources

### "Puis-je chercher en français ?"

Oui, mais les résultats techniques sont souvent meilleurs en anglais. Claude peut traduire les résultats.

## Critères de validation

L'apprenant a réussi cette démo si :

- [ ] A effectué au moins 3 recherches différentes
- [ ] Comprend la différence WebSearch/WebFetch
- [ ] Sait demander les sources
- [ ] A créé un rapport de veille structuré
- [ ] Comprend les limitations de la recherche web

## Types de recherches utiles

### Documentation

```
Recherche la documentation officielle de [bibliothèque] sur [fonctionnalité]
```

### Comparaison

```
Compare [A] et [B] pour [cas d'usage] avec sources récentes
```

### Débogage

```
Recherche solutions pour l'erreur : "[message exact]"
```

### Veille

```
Nouveautés [technologie] [année], annonces officielles uniquement
```

### Bonnes pratiques

```
Recommandations [organisation] pour [sujet] en [année]
```

## Erreurs courantes

### Recherche trop large

**Cause** : Requête vague

**Exemple problématique** :
```
Recherche sur les APIs
```

**Solution** :
```
Recherche les bonnes pratiques de versioning d'API REST en 2026
```

### Pas de vérification des sources

**Cause** : Confiance aveugle

**Solution** : Toujours demander :
```
Quelles sont les sources de ces informations ?
Sont-elles de [année] ou plus récentes ?
```

### Informations contradictoires

**Cause** : Sources de qualité variable

**Solution** :
```
J'ai trouvé des informations contradictoires sur [sujet].
Recherche uniquement dans la documentation officielle.
```

## Exemples de résultats attendus

### Rapport de veille

```markdown
# Veille Technologique : Tests Python 2026

## Résumé
L'écosystème de test Python en 2026 est dominé par pytest,
avec des améliorations significatives dans le support async.

## État de l'art

### pytest (recommandé)
- Version actuelle : 8.x
- Points forts : fixtures, plugins, async natif
- Source : [pytest.org](https://pytest.org)

### Alternatives
- **unittest** : Intégré, moins flexible
- **hypothesis** : Tests property-based

## Tendances
- Tests async de plus en plus simples
- Intégration IA pour génération de tests
- Fixtures async-first

## Recommandations
1. Utiliser pytest pour nouveaux projets
2. Adopter pytest-asyncio pour code async
3. Explorer hypothesis pour edge cases

## Sources
- [Documentation pytest](https://docs.pytest.org)
- [PEP 123 - Testing](https://peps.python.org/...)
- [Article Real Python](https://realpython.com/...)

*Dernière mise à jour : Janvier 2026*
```

## Ressources pour le formateur

- [WebSearch Documentation](https://code.claude.com/docs/en/tools#websearch)
- [WebFetch Documentation](https://code.claude.com/docs/en/tools#webfetch)
