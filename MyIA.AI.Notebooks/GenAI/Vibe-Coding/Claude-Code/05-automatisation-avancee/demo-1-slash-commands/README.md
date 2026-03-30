# Demo 1 - Slash Commands Personnalisés

## Objectif

Créer des Slash Commands pour automatiser des tâches répétitives et standardiser votre workflow.

## Durée estimée

**45 minutes**

## Concepts

### Qu'est-ce qu'un Slash Command ?

Un Slash Command est un prompt sauvegardé dans un fichier Markdown, invoqué avec `/nom`.

```
/lint       → .claude/commands/lint.md
/test       → .claude/commands/test.md
/my-command → .claude/commands/my-command.md
```

### Structure d'un Slash Command

```markdown
# Fichier : .claude/commands/nom.md

[Instructions pour Claude]

Tu dois faire X, Y, Z...

Critères :
- Critère 1
- Critère 2

Format de sortie :
[Description du format attendu]
```

### Avantages

- **Consistance** : Même prompt à chaque fois
- **Rapidité** : Un mot au lieu d'un paragraphe
- **Partage** : Versionné avec le projet
- **Évolution** : Facile à améliorer

## Étapes

### Étape 1 : Créer la structure (5 min)

```bash
# Créer le dossier des commandes
mkdir -p .claude/commands

# Vérifier
ls -la .claude/
```

### Étape 2 : Première commande - /lint (10 min)

Créez `.claude/commands/lint.md` :

```markdown
Analyse les fichiers Python modifiés récemment et vérifie :

## Vérifications

### Style (PEP 8)
- Indentation (4 espaces)
- Longueur des lignes (< 88 caractères)
- Espaces autour des opérateurs
- Lignes vides appropriées

### Documentation
- Docstrings pour les fonctions publiques
- Type hints sur les signatures
- Commentaires pertinents (pas évidents)

### Qualité
- Pas de code mort
- Pas de variables inutilisées
- Pas de imports non utilisés
- Nommage clair et cohérent

## Format de sortie

Pour chaque problème :
```
📁 fichier.py
   L42: [STYLE] Ligne trop longue (95 > 88)
   L58: [DOC] Fonction sans docstring
   L73: [QUALITÉ] Variable 'x' mal nommée
```

Termine par un résumé :
```
✅ 3 fichiers analysés
⚠️ 7 problèmes trouvés (3 style, 2 doc, 2 qualité)
```
```

Testez :
```
/lint
```

### Étape 3 : Commande /test-this (10 min)

Créez `.claude/commands/test-this.md` :

```markdown
Génère des tests unitaires pour le code actuellement sélectionné ou le fichier ouvert.

## Analyse

1. Identifie les fonctions/classes à tester
2. Détermine les cas de test nécessaires :
   - Cas normal (happy path)
   - Cas limites (edge cases)
   - Cas d'erreur (exceptions)

## Génération

Utilise pytest avec ces conventions :
- Fichier : test_<nom_module>.py
- Classe : Test<NomFonction>
- Méthode : test_<scenario>_<resultat_attendu>

## Structure du test

```python
import pytest
from <module> import <fonction>

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

    def test_cas_erreur(self):
        """Test de gestion d'erreur."""
        with pytest.raises(ValueError):
            fonction(invalid_input)
```

## Demande de confirmation

Avant d'écrire les tests, montre-moi :
1. La liste des tests qui seront générés
2. Le chemin du fichier de destination

Attends ma confirmation.
```

### Étape 4 : Commande /commit-msg (10 min)

Créez `.claude/commands/commit-msg.md` :

```markdown
Analyse les changements staged (git diff --cached) et génère un message de commit.

## Format Conventional Commits

```
<type>(<scope>): <description>

<body optionnel>

<footer optionnel>
```

## Types

- feat: Nouvelle fonctionnalité
- fix: Correction de bug
- docs: Documentation
- style: Formatage (pas de changement logique)
- refactor: Refactoring
- test: Ajout/modification de tests
- chore: Maintenance

## Règles

1. Description < 50 caractères
2. Commence par un verbe à l'impératif
3. Pas de point final
4. Body : explique le "pourquoi" (si nécessaire)

## Processus

1. Exécute `git diff --cached`
2. Analyse les changements
3. Détermine le type et scope
4. Génère 3 propositions de messages
5. Attends mon choix

## Exemple de sortie

```
Changements détectés :
- src/auth.py : Ajout fonction validate_token
- tests/test_auth.py : Tests pour validate_token

Propositions :

1. feat(auth): add JWT token validation

2. feat(auth): implement validate_token function

   Add function to validate JWT tokens with:
   - Signature verification
   - Expiration check
   - Custom claims validation

3. feat: add token validation to auth module

Quel message préfères-tu ? (1/2/3 ou personnalisé)
```
```

### Étape 5 : Commande avec arguments (10 min)

Les Slash Commands peuvent recevoir des arguments via `$ARGUMENTS`.

Créez `.claude/commands/explain.md` :

```markdown
Explique le concept suivant de manière pédagogique : $ARGUMENTS

## Structure de l'explication

### 1. Définition simple
Une phrase claire et accessible.

### 2. Analogie
Compare avec quelque chose de la vie quotidienne.

### 3. Exemple concret
Code fonctionnel illustrant le concept.

### 4. Cas d'usage
Quand et pourquoi utiliser ce concept.

### 5. Pièges courants
Erreurs fréquentes à éviter.

### 6. Pour aller plus loin
Ressources et concepts liés.

## Ton

- Pédagogique et bienveillant
- Évite le jargon inutile
- Exemples progressifs en complexité
```

Testez :
```
/explain les décorateurs Python
/explain le pattern Observer
/explain async/await
```

## Exercice pratique

### Mission

Créez 3 Slash Commands utiles pour votre workflow.

### Suggestions

| Commande | Usage |
|----------|-------|
| `/security` | Audit de sécurité rapide |
| `/optimize` | Suggestions de performance |
| `/api-doc` | Génère documentation d'endpoint |
| `/migration` | Aide à la migration de version |
| `/debug` | Guide de débogage structuré |

### Template

```markdown
# .claude/commands/ma-commande.md

[Contexte optionnel]

## Objectif
[Ce que la commande doit accomplir]

## Étapes
1. [Étape 1]
2. [Étape 2]
3. [Étape 3]

## Critères de qualité
- [Critère 1]
- [Critère 2]

## Format de sortie
[Description du format]

## Exemple
[Exemple de résultat attendu]
```

### Livrable

3 Slash Commands personnalisées et testées.

## Bonnes pratiques

### DO

- Noms courts et mémorables
- Instructions claires et structurées
- Exemples de sortie attendue
- Demande de confirmation pour actions destructives

### DON'T

- Commandes trop complexes (découpez)
- Noms ambigus
- Instructions vagues
- Dépendances à des fichiers spécifiques

## Points clés à retenir

1. **Simplicité** : Une commande = une tâche

2. **Clarté** : Instructions précises

3. **Réutilisabilité** : Évitez les références spécifiques

4. **Évolution** : Améliorez itérativement

---

**Prochaine étape** : [Demo 2 - Skills et Subagents](../demo-2-skills-subagents/)
