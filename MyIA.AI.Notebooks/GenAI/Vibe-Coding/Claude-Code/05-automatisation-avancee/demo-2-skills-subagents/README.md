# Demo 2 - Skills et Subagents

## Objectif

Créer des Skills réutilisables et comprendre l'orchestration de Subagents pour des tâches complexes.

## Durée estimée

**60 minutes**

## Concepts

### Skills vs Slash Commands

| Aspect | Slash Commands | Skills |
|--------|---------------|--------|
| Format | Markdown simple | SKILL.md avec frontmatter |
| Scope | Prompt unique | Expertise complète |
| Métadonnées | Non | Oui (nom, version, description) |
| Découverte | Manuel (/commande) | Automatique |
| Persistance | Session | Projet/global |

### Structure d'un Skill

```
.claude/skills/
└── mon-skill/
    ├── SKILL.md       # Requis : instructions
    ├── examples/      # Optionnel : exemples
    └── templates/     # Optionnel : templates
```

### SKILL.md

```yaml
---
name: nom-du-skill
description: Description courte (< 1024 chars)
version: 1.0.0
author: Votre Nom
tags: [python, testing, quality]
---

# Instructions détaillées

[Contenu Markdown avec les instructions pour Claude]
```

### Subagents

Les Subagents sont des instances de Claude spécialisées :

- Contexte isolé
- Outils spécifiques
- Jusqu'à 10 en parallèle
- Pas de nesting (agents dans agents)

## Étapes

### Étape 1 : Créer un Skill simple (15 min)

#### Structure

```bash
mkdir -p .claude/skills/python-best-practices
```

#### SKILL.md

```bash
cat > .claude/skills/python-best-practices/SKILL.md << 'EOF'
---
name: python-best-practices
description: Guide des bonnes pratiques Python moderne avec focus sur la qualité et la maintenabilité
version: 1.0.0
author: Formation ECE
tags: [python, quality, best-practices]
---

# Python Best Practices Expert

Tu incarnes un expert Python senior spécialisé dans les bonnes pratiques modernes.

## Tes domaines d'expertise

### 1. Style et conventions
- PEP 8 et au-delà
- Nommage expressif
- Structure de code claire

### 2. Typing moderne
- Type hints (Python 3.9+)
- Generics et TypeVar
- Protocol et structural subtyping

### 3. Patterns Python
- Context managers
- Decorators
- Descriptors
- Metaclasses (avec parcimonie)

### 4. Performance
- Comprehensions vs loops
- Generators pour la mémoire
- Caching avec functools

### 5. Testing
- pytest idiomatique
- Fixtures et parametrize
- Mocking propre

## Ton approche

Quand on te demande conseil :

1. **Explique le "pourquoi"** avant le "comment"
2. **Montre l'évolution** : code naïf → code idiomatique
3. **Cite les sources** : PEPs, documentation officielle
4. **Préviens des pièges** : cas où la règle ne s'applique pas

## Exemples de transformation

### Avant (non-idiomatique)
```python
result = []
for item in items:
    if item.is_valid():
        result.append(item.value)
```

### Après (pythonique)
```python
result = [item.value for item in items if item.is_valid()]
```

## Format de tes réponses

1. Résumé de la recommandation
2. Code avant/après
3. Explication détaillée
4. Ressources pour approfondir
EOF
```

#### Test

```
J'ai ce code Python, applique les bonnes pratiques :

def get_data(items, filter_func, transform_func):
    result = []
    for item in items:
        if filter_func(item):
            result.append(transform_func(item))
    return result
```

### Étape 2 : Créer un Skill avec templates (15 min)

#### Structure avancée

```bash
mkdir -p .claude/skills/api-designer/templates
```

#### SKILL.md

```bash
cat > .claude/skills/api-designer/SKILL.md << 'EOF'
---
name: api-designer
description: Expert en conception d'API REST avec FastAPI
version: 1.0.0
tags: [api, rest, fastapi, design]
---

# API Designer Expert

Tu es un architecte API spécialisé dans la conception d'APIs REST modernes avec FastAPI.

## Principes de design

### 1. RESTful
- Resources, pas actions
- Verbes HTTP appropriés
- Status codes significatifs

### 2. Consistency
- Nommage : snake_case pour les champs
- Pagination : offset/limit ou cursor
- Erreurs : format standardisé

### 3. Documentation
- OpenAPI automatique
- Exemples dans les schémas
- Descriptions utiles

## Templates disponibles

Tu peux utiliser ces templates de référence :

### Endpoint CRUD standard
Voir `templates/crud_endpoint.py`

### Schema Pydantic
Voir `templates/pydantic_schema.py`

### Error handling
Voir `templates/error_handling.py`

## Ton workflow de design

1. Comprendre le domaine métier
2. Identifier les resources
3. Définir les relations
4. Concevoir les endpoints
5. Spécifier les schémas
6. Documenter
EOF
```

#### Templates

```bash
cat > .claude/skills/api-designer/templates/crud_endpoint.py << 'EOF'
"""Template pour endpoint CRUD standard."""

from fastapi import APIRouter, Depends, HTTPException, status
from sqlalchemy.orm import Session

from app.database import get_db
from app.schemas.resource import ResourceCreate, ResourceUpdate, ResourceResponse
from app.services.resource import ResourceService

router = APIRouter(prefix="/resources", tags=["resources"])


@router.get("/", response_model=list[ResourceResponse])
async def list_resources(
    skip: int = 0,
    limit: int = 100,
    db: Session = Depends(get_db)
):
    """Liste toutes les resources avec pagination."""
    service = ResourceService(db)
    return service.get_all(skip=skip, limit=limit)


@router.get("/{resource_id}", response_model=ResourceResponse)
async def get_resource(resource_id: int, db: Session = Depends(get_db)):
    """Récupère une resource par son ID."""
    service = ResourceService(db)
    resource = service.get_by_id(resource_id)
    if not resource:
        raise HTTPException(
            status_code=status.HTTP_404_NOT_FOUND,
            detail=f"Resource {resource_id} not found"
        )
    return resource


@router.post("/", response_model=ResourceResponse, status_code=status.HTTP_201_CREATED)
async def create_resource(data: ResourceCreate, db: Session = Depends(get_db)):
    """Crée une nouvelle resource."""
    service = ResourceService(db)
    return service.create(data)


@router.put("/{resource_id}", response_model=ResourceResponse)
async def update_resource(
    resource_id: int,
    data: ResourceUpdate,
    db: Session = Depends(get_db)
):
    """Met à jour une resource existante."""
    service = ResourceService(db)
    resource = service.update(resource_id, data)
    if not resource:
        raise HTTPException(
            status_code=status.HTTP_404_NOT_FOUND,
            detail=f"Resource {resource_id} not found"
        )
    return resource


@router.delete("/{resource_id}", status_code=status.HTTP_204_NO_CONTENT)
async def delete_resource(resource_id: int, db: Session = Depends(get_db)):
    """Supprime une resource."""
    service = ResourceService(db)
    if not service.delete(resource_id):
        raise HTTPException(
            status_code=status.HTTP_404_NOT_FOUND,
            detail=f"Resource {resource_id} not found"
        )
EOF
```

### Étape 3 : Comprendre les Subagents (15 min)

#### Types de Subagents intégrés

| Agent | Usage | Invocation |
|-------|-------|------------|
| Explore | Navigation codebase | Automatique ou explicite |
| Plan | Planification | `--permission-mode plan` |
| General | Tâches diverses | Task tool |

#### Invocation explicite

```
Délègue à un agent Explore l'analyse de la structure de ce projet.
Rapporte-moi les résultats.
```

#### Parallélisation

```
Lance 3 agents en parallèle :
1. Agent A : Analyse la qualité du code dans src/
2. Agent B : Vérifie la couverture des tests
3. Agent C : Documente l'architecture

Synthétise les résultats quand ils sont tous terminés.
```

### Étape 4 : Skill avec Subagent intégré (15 min)

Un Skill peut définir qu'il utilise des subagents :

```bash
cat > .claude/skills/full-audit/SKILL.md << 'EOF'
---
name: full-audit
description: Audit complet d'un projet avec agents spécialisés
version: 1.0.0
tags: [audit, quality, security]
---

# Full Project Audit

Ce skill orchestre un audit complet en utilisant des agents spécialisés.

## Workflow

Quand on me demande un audit complet :

### Phase 1 : Analyse parallèle

Je délègue à 4 agents spécialisés :

1. **Agent Qualité**
   - Complexité cyclomatique
   - Code smells
   - Maintenabilité

2. **Agent Sécurité**
   - Vulnérabilités OWASP
   - Gestion des secrets
   - Validation des entrées

3. **Agent Performance**
   - Algorithmes inefficaces
   - Requêtes N+1
   - Memory leaks potentiels

4. **Agent Tests**
   - Couverture de code
   - Qualité des tests
   - Tests manquants

### Phase 2 : Synthèse

Je compile les résultats en un rapport unifié :

```markdown
# Rapport d'Audit - [Projet]

## Score Global : [A-F]

## Résumé Exécutif
[Synthèse en 3 phrases]

## Qualité
[Résultats Agent Qualité]

## Sécurité
[Résultats Agent Sécurité]

## Performance
[Résultats Agent Performance]

## Tests
[Résultats Agent Tests]

## Plan d'Action Prioritaire
1. [Action critique]
2. [Action importante]
3. [Action souhaitable]
```

### Phase 3 : Recommandations

Je propose un plan d'action priorisé avec estimation d'effort.
EOF
```

## Exercice pratique

### Mission

Créez un Skill personnalisé pour votre domaine.

### Options suggérées

1. **Code Reviewer** : Expert en revue de code
2. **Test Writer** : Génération de tests
3. **Doc Generator** : Documentation automatique
4. **Migration Helper** : Aide à la migration

### Template

```yaml
---
name: votre-skill
description: Description concise
version: 1.0.0
author: Votre Nom
tags: [tag1, tag2]
---

# Titre du Skill

[Description de l'expertise]

## Principes

1. [Principe 1]
2. [Principe 2]

## Approche

[Comment vous abordez les problèmes]

## Format de sortie

[Structure des réponses]

## Exemples

[Exemples de cas d'usage]
```

### Livrable

Skill fonctionnel et testé.

## Points clés à retenir

1. **Skills = Expertise persistante** : Plus qu'un simple prompt

2. **Structure YAML** : Frontmatter obligatoire avec métadonnées

3. **Subagents = Parallélisation** : Pour les tâches complexes

4. **Composition** : Skills + Subagents = Workflows puissants

---

**Prochaine étape** : [Demo 3 - MCP et Hooks](../demo-3-mcp-hooks/)
