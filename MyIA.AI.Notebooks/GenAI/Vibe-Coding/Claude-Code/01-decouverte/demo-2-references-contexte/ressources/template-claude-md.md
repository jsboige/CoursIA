# Template CLAUDE.md

Utilisez ce template comme base pour créer votre propre CLAUDE.md.

---

# [Nom du Projet]

## Description

[Décrivez votre projet en 2-3 phrases. Quel est son but ? Quel problème résout-il ?]

## Stack technique

- **Langage** : [Python 3.11 / Node.js 20 / etc.]
- **Framework** : [FastAPI / Express / React / etc.]
- **Base de données** : [PostgreSQL / MongoDB / etc.]
- **Tests** : [pytest / Jest / etc.]
- **CI/CD** : [GitHub Actions / GitLab CI / etc.]

## Structure du projet

```
[Ajoutez l'arborescence de votre projet]
src/
├── api/           # Routes et endpoints
├── models/        # Modèles de données
├── services/      # Logique métier
└── utils/         # Utilitaires
tests/
├── unit/          # Tests unitaires
└── integration/   # Tests d'intégration
```

## Conventions de code

### Nommage

- **Classes** : PascalCase (`UserService`)
- **Fonctions** : snake_case (`get_user_by_id`)
- **Constantes** : UPPER_SNAKE_CASE (`MAX_RETRIES`)
- **Variables** : snake_case (`user_count`)

### Documentation

- Format de docstrings : [Google / NumPy / Sphinx]
- Type hints : [Obligatoires / Recommandés]
- Comments : [En français / En anglais]

### Tests

- Convention de nommage : `test_<fonction>_<scenario>`
- Couverture minimale : [80% / 90%]
- Framework : [pytest / Jest / etc.]

## Commandes utiles

```bash
# Installation des dépendances
[pip install -r requirements.txt / npm install]

# Lancer le serveur de développement
[uvicorn src.main:app --reload / npm run dev]

# Lancer les tests
[pytest / npm test]

# Lancer les tests avec couverture
[pytest --cov=src / npm run test:coverage]

# Formater le code
[black . / npm run format]

# Vérifier le linting
[flake8 src/ / npm run lint]

# Build production
[docker build -t myapp . / npm run build]
```

## Variables d'environnement

| Variable | Description | Défaut |
|----------|-------------|--------|
| `DATABASE_URL` | URL de connexion DB | - |
| `API_KEY` | Clé API externe | - |
| `DEBUG` | Mode debug | `false` |
| `LOG_LEVEL` | Niveau de log | `INFO` |

## Instructions pour Claude

Quand tu travailles sur ce projet :

1. **Style de code**
   - Utilise toujours des type hints
   - Ajoute des docstrings pour les fonctions publiques
   - Préfère les fonctions pures quand c'est possible

2. **Architecture**
   - Suis le pattern [Repository / Service / etc.]
   - Garde la logique métier dans `services/`
   - Les routes/controllers ne font que de la validation

3. **Tests**
   - Crée des tests pour chaque nouvelle fonction
   - Utilise des fixtures pour les données de test
   - Mock les dépendances externes

4. **Git**
   - Messages de commit en [français / anglais]
   - Format : `type(scope): description`
   - Types : feat, fix, refactor, docs, test

5. **À éviter**
   - [Liste des patterns/libs à éviter]
   - [Code copié de Stack Overflow sans compréhension]

## Ressources

- [Documentation du framework](https://...)
- [Guide de style interne](https://...)
- [Architecture Decision Records](./docs/adr/)

---

*Dernière mise à jour : [DATE]*
