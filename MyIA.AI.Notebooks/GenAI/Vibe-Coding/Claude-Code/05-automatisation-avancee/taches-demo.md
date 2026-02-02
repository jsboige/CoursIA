# Tâches de démonstration - Atelier 05

Ce document liste des tâches concrètes pour maîtriser les fonctionnalités avancées de Claude Code.

## Tâche 1 : Créer des Slash Commands de base

### Contexte
Vous voulez automatiser des tâches répétitives dans votre workflow quotidien.

### Instructions

1. Créez le dossier des commandes :
   ```bash
   mkdir -p .claude/commands
   ```

2. Créez une commande `/lint` :
   ```bash
   cat > .claude/commands/lint.md << 'EOF'
   Analyse tous les fichiers Python modifiés (git diff) et vérifie :

   1. Conformité PEP 8
   2. Présence de type hints sur les fonctions publiques
   3. Docstrings pour les classes et fonctions publiques
   4. Imports organisés (stdlib, third-party, local)

   Pour chaque problème trouvé :
   - Indique le fichier et la ligne
   - Explique le problème
   - Propose la correction

   À la fin, résume le nombre de problèmes par catégorie.
   EOF
   ```

3. Créez une commande `/test-file` :
   ```bash
   cat > .claude/commands/test-file.md << 'EOF'
   Pour le fichier actuellement ouvert :

   1. Identifie les fonctions et classes
   2. Génère des tests unitaires couvrant :
      - Cas normaux (happy path)
      - Cas limites
      - Cas d'erreur
   3. Utilise pytest et les conventions du projet
   4. Place les tests dans le dossier tests/ correspondant

   Montre-moi les tests générés et demande confirmation avant de les écrire.
   EOF
   ```

4. Créez une commande `/doc-function` :
   ```bash
   cat > .claude/commands/doc-function.md << 'EOF'
   Ajoute une docstring Google-style complète à la fonction sélectionnée.

   La docstring doit inclure :
   - Description courte (une ligne)
   - Description longue si nécessaire
   - Args avec types et descriptions
   - Returns avec type et description
   - Raises avec exceptions possibles
   - Example d'utilisation

   Ne modifie pas la logique de la fonction.
   EOF
   ```

5. Testez vos commandes :
   ```
   /lint
   /test-file
   /doc-function
   ```

### Livrable
3 Slash Commands fonctionnelles.

---

## Tâche 2 : Créer un Skill Python Reviewer

### Contexte
Vous voulez que Claude adopte un rôle d'expert pour les revues de code.

### Instructions

1. Créez la structure du skill :
   ```bash
   mkdir -p .claude/skills/python-reviewer
   ```

2. Créez le fichier SKILL.md :
   ```bash
   cat > .claude/skills/python-reviewer/SKILL.md << 'EOF'
   ---
   name: python-reviewer
   description: Expert en revue de code Python avec focus qualité et bonnes pratiques
   version: 1.0.0
   author: Votre Nom
   ---

   # Python Code Reviewer

   Tu es un expert senior en développement Python avec 15 ans d'expérience.
   Ta spécialité est la revue de code approfondie.

   ## Ton approche

   Quand tu revois du code, tu analyses systématiquement :

   ### 1. Correction fonctionnelle
   - Le code fait-il ce qu'il est censé faire ?
   - Y a-t-il des bugs logiques ?
   - Les cas limites sont-ils gérés ?

   ### 2. Qualité du code
   - Lisibilité et clarté
   - Nommage des variables et fonctions
   - Structure et organisation
   - Complexité (fonctions trop longues, imbrications profondes)

   ### 3. Bonnes pratiques Python
   - Idiomes Python (pythonic code)
   - PEP 8 et conventions
   - Type hints
   - Docstrings

   ### 4. Performance
   - Algorithmes efficaces
   - Utilisation mémoire
   - Opérations coûteuses dans les boucles

   ### 5. Sécurité
   - Injection
   - Gestion des secrets
   - Validation des entrées

   ### 6. Testabilité
   - Le code est-il facilement testable ?
   - Dépendances injectables ?

   ## Format de tes revues

   Structure ta revue ainsi :

   ## Résumé
   [Note globale /10 et résumé en 2-3 phrases]

   ## Points positifs
   - [Ce qui est bien fait]

   ## Problèmes critiques
   - [Bugs, failles de sécurité]

   ## Améliorations suggérées
   - [Suggestions classées par priorité]

   ## Exemples de correction
   [Code corrigé pour les problèmes majeurs]
   EOF
   ```

3. Testez le skill :
   ```
   @src/services.py Utilise ton expertise de python-reviewer
   pour faire une revue approfondie de ce code.
   ```

### Livrable
Skill python-reviewer fonctionnel.

---

## Tâche 3 : Créer un Skill de génération de tests

### Contexte
Vous voulez un skill spécialisé dans la génération de tests.

### Instructions

1. Créez le skill :
   ```bash
   mkdir -p .claude/skills/test-generator
   cat > .claude/skills/test-generator/SKILL.md << 'EOF'
   ---
   name: test-generator
   description: Expert en génération de tests Python avec pytest
   version: 1.0.0
   ---

   # Test Generator Expert

   Tu es un expert en testing Python. Ta mission est de générer
   des tests complets et maintenables.

   ## Principes

   1. **Couverture complète** : Chaque branche du code doit être testée
   2. **Tests isolés** : Chaque test est indépendant
   3. **Nommage clair** : test_<fonction>_<scenario>_<resultat>
   4. **AAA Pattern** : Arrange, Act, Assert

   ## Structure des tests

   ```python
   import pytest
   from unittest.mock import Mock, patch

   class TestNomFonction:
       """Tests pour nom_fonction."""

       def test_cas_normal(self):
           """Description du cas testé."""
           # Arrange
           input_data = ...

           # Act
           result = fonction(input_data)

           # Assert
           assert result == expected

       def test_cas_limite(self):
           """Test avec valeurs limites."""
           ...

       def test_erreur_attendue(self):
           """Test de gestion d'erreur."""
           with pytest.raises(ExpectedException):
               fonction(invalid_input)
   ```

   ## Cas à couvrir systématiquement

   - Valeurs normales
   - Valeurs limites (0, -1, max_int, chaînes vides)
   - Valeurs None
   - Collections vides
   - Exceptions attendues
   - Effets de bord

   ## Fixtures

   Crée des fixtures réutilisables dans conftest.py :

   ```python
   @pytest.fixture
   def sample_data():
       """Données de test standard."""
       return {...}
   ```
   EOF
   ```

2. Testez :
   ```
   @src/services.py Utilise le skill test-generator pour créer
   des tests complets pour ce module.
   ```

### Livrable
Skill test-generator fonctionnel.

---

## Tâche 4 : Configurer des serveurs MCP

### Contexte
Vous voulez étendre Claude Code avec des capacités de recherche web et d'accès à GitHub.

### Instructions

1. Créez le fichier de configuration MCP :
   ```bash
   cat > .mcp.json << 'EOF'
   {
     "mcpServers": {
       "searxng": {
         "url": "https://search.myia.io/",
         "transport": "http",
         "description": "Recherche web distribuée"
       },
       "github": {
         "command": "npx",
         "args": ["-y", "@modelcontextprotocol/server-github"],
         "env": {
           "GITHUB_TOKEN": "${GITHUB_TOKEN}"
         },
         "transport": "stdio",
         "description": "Accès API GitHub"
       }
     }
   }
   EOF
   ```

2. Configurez le token GitHub :
   ```bash
   cat > .claude/settings.local.json << 'EOF'
   {
     "env": {
       "GITHUB_TOKEN": "ghp_votre_token_ici"
     }
   }
   EOF
   ```

3. Ajoutez au .gitignore :
   ```bash
   echo ".claude/settings.local.json" >> .gitignore
   ```

4. Vérifiez la configuration :
   ```bash
   claude mcp list
   ```

5. Testez les MCPs :
   ```
   Recherche les meilleures pratiques pour FastAPI en 2026
   ```

   ```
   Liste mes 5 dernières pull requests sur GitHub
   ```

### Livrable
Configuration MCP fonctionnelle avec searxng et GitHub.

---

## Tâche 5 : Configurer des Hooks

### Contexte
Vous voulez automatiser le linting après chaque modification de fichier.

### Instructions

1. Créez ou modifiez settings.json :
   ```bash
   cat > .claude/settings.json << 'EOF'
   {
     "permissions": {
       "allow": ["Read", "Write", "Edit", "Bash", "Glob", "Grep"]
     },
     "hooks": {
       "PostToolUse": {
         "Edit": {
           "command": "echo 'Fichier modifié : ${file}' && python -m py_compile ${file} 2>&1 || echo 'Erreur de syntaxe'",
           "timeout": 5000
         },
         "Write": {
           "command": "echo 'Fichier créé : ${file}'",
           "timeout": 2000
         }
       },
       "UserPromptSubmit": {
         "command": "echo 'Nouvelle requête reçue'",
         "timeout": 1000
       }
     }
   }
   EOF
   ```

2. Testez le hook Edit :
   - Modifiez un fichier Python
   - Observez le message de confirmation

3. Créez un hook plus avancé (lint automatique) :
   ```json
   {
     "hooks": {
       "PostToolUse": {
         "Edit": {
           "command": "black ${file} --check --quiet || (black ${file} && echo 'Formaté avec Black')",
           "timeout": 10000
         }
       }
     }
   }
   ```

### Livrable
Hooks fonctionnels pour le linting automatique.

---

## Tâche 6 : Utiliser les Subagents

### Contexte
Vous avez une tâche complexe nécessitant plusieurs analyses parallèles.

### Instructions

1. Demandez une analyse multi-agents :
   ```
   J'ai besoin d'analyser ce projet sous plusieurs angles.
   Délègue à des agents spécialisés :

   1. Agent "sécurité" : Analyse les vulnérabilités potentielles
   2. Agent "performance" : Identifie les goulots d'étranglement
   3. Agent "qualité" : Évalue la maintenabilité du code

   Chaque agent doit produire un rapport indépendant.
   Synthétise ensuite les résultats.
   ```

2. Observez :
   - Claude crée plusieurs agents
   - Chaque agent travaille sur sa tâche
   - Les résultats sont agrégés

3. Essayez avec une tâche de documentation :
   ```
   Utilise des agents parallèles pour documenter ce projet :

   - Agent 1 : Génère le README
   - Agent 2 : Documente l'API
   - Agent 3 : Crée le guide de contribution

   Coordonne les résultats pour assurer la cohérence.
   ```

### Livrable
Comprendre le fonctionnement des subagents.

---

## Tâche 7 : Projet intégré - Pipeline automatisé

### Contexte
Vous voulez créer un pipeline complet de développement automatisé.

### Instructions

1. **Créez les commandes du pipeline** :
   ```
   /check    → Lint + Type check + Tests
   /release  → Bump version + Changelog + Tag
   /deploy   → Build + Push + Deploy
   ```

2. **Créez les skills nécessaires** :
   - `changelog-writer` : Génère le changelog à partir des commits
   - `release-manager` : Gère le versioning sémantique

3. **Configurez les hooks** :
   - Post-commit : Mise à jour du changelog
   - Pre-push : Validation complète

4. **Intégrez le MCP GitHub** :
   - Création automatique de PR
   - Labels automatiques

### Structure finale

```
.claude/
├── settings.json
├── commands/
│   ├── check.md
│   ├── release.md
│   └── deploy.md
└── skills/
    ├── changelog-writer/
    │   └── SKILL.md
    └── release-manager/
        └── SKILL.md
.mcp.json
```

### Livrable
Pipeline de développement automatisé complet.

---

## Récapitulatif des livrables

| Tâche | Livrable |
|-------|----------|
| 1 | 3 Slash Commands |
| 2 | Skill python-reviewer |
| 3 | Skill test-generator |
| 4 | Configuration MCP |
| 5 | Hooks de linting |
| 6 | Compréhension subagents |
| 7 | Pipeline automatisé |

---

## Pour aller plus loin

- Explorez le [marketplace de skills](https://skillsmp.com/)
- Consultez [Awesome Claude Code](https://github.com/hesreallyhim/awesome-claude-code)
- Créez vos propres serveurs MCP
