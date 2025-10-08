# Procédure de Configuration Environnement GenAI Images

## ⚠️ SÉCURITÉ CRITIQUE

**JAMAIS de clés API dans les documents markdown ou git !**

## Étapes de Configuration

### 1. Création .env (Mode Code requis)
```bash
# Fichier: MyIA.AI.Notebooks/GenAI/.env
OPENROUTER_API_KEY=sk-or-v1-[clé-fournie-par-utilisateur]
```

### 2. Création .env.example (Template public)
```bash
# Fichier: MyIA.AI.Notebooks/GenAI/.env.example  
OPENROUTER_API_KEY=sk-or-v1-your-openrouter-api-key-here
```

### 3. Validation .gitignore
Vérifier que `.env` est dans `.gitignore`

## Changement de Mode Nécessaire

En mode Architect, je ne peux créer que des fichiers .md. 
Pour créer les fichiers .env, je dois passer en mode Code.

## Prochaines Étapes

1. Changement de mode → Code
2. Création des fichiers .env (SÉCURISÉS)
3. Test de la configuration OpenRouter
4. Création des premiers notebooks GenAI Images