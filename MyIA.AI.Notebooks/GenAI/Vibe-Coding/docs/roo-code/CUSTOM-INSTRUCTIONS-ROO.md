# Roo Code - Custom Instructions et Contexte

Ce guide explique comment configurer le contexte global et local dans Roo Code pour personnaliser le comportement de l'assistant selon vos projets et preferences.

## Vue d'Ensemble

Roo Code charge et fusionne les instructions de plusieurs sources pour creer un ensemble unifie de "custom instructions" ajoutees au system prompt. Cela permet de :

- **Standardiser** les conventions de code au sein d'une equipe
- **Personnaliser** le style de reponse de Roo
- **Adapter** le comportement selon le contexte (projet, mode de travail)
- **Partager** des configurations via le controle de version

## Hierarchie et Priorite des Sources

Roo charge les instructions dans un ordre specifique. Les sources chargees en dernier ont priorite sur les precedentes en cas de conflit.

| Priorite | Source | Emplacement | Portee |
|----------|--------|-------------|--------|
| 1 (basse) | Global UI | Prompts tab (interface) | Tous projets |
| 2 | Global fichiers | `~/.roo/rules/` | Tous projets |
| 3 | Mode-specific global | `~/.roo/rules-{mode}/` | Mode specifique, tous projets |
| 4 | Projet fichiers | `.roo/rules/` | Projet courant |
| 5 (haute) | Mode-specific projet | `.roo/rules-{mode}/` | Mode specifique, projet |
| Variable | AGENTS.md | Racine projet | Equipe (si active) |

**Regle cle :** Les rules de niveau projet prennent toujours le dessus sur les rules globales en cas de conflit.

---

## Configuration Globale

Les instructions globales s'appliquent a tous vos projets.

### Via l'Interface Prompts (Recommande pour debuter)

1. Ouvrez Roo Code dans VS Code
2. Cliquez sur l'icone **Prompts** (en haut du panneau)
3. Dans la section **"Global Instructions"**, ajoutez vos instructions
4. Pour des instructions specifiques a un mode, selectionnez le mode et ajoutez-les

**Exemple :**

```
Toujours repondre en francais.
Utiliser des commentaires clairs dans le code.
Privilegier la lisibilite a la concision.
```

### Via Fichiers (~/.roo/rules/)

Pour une gestion plus avancee et versionnable :

**Windows :**
```powershell
# Creer le repertoire
New-Item -ItemType Directory -Force -Path "$env:USERPROFILE\.roo\rules"

# Ajouter une rule
@"
# Instructions globales

## Langue
Toujours repondre en francais.

## Style de code
- Privilegier la lisibilite
- Commenter les parties complexes
- Utiliser des noms de variables descriptifs
"@ | Out-File -FilePath "$env:USERPROFILE\.roo\rules\01-global.md" -Encoding utf8
```

**macOS / Linux :**
```bash
# Creer le repertoire
mkdir -p ~/.roo/rules

# Ajouter une rule
cat > ~/.roo/rules/01-global.md << 'EOF'
# Instructions globales

## Langue
Toujours repondre en francais.

## Style de code
- Privilegier la lisibilite
- Commenter les parties complexes
- Utiliser des noms de variables descriptifs
EOF
```

### Structure Recommandee (~/.roo/)

```
~/.roo/
├── rules/                    # Rules generales (tous modes)
│   ├── 01-langue.md         # Preferences de langue
│   ├── 02-style-code.md     # Conventions de code
│   └── 03-preferences.md    # Preferences personnelles
├── rules-code/              # Rules mode Code uniquement
│   └── typescript-rules.md  # Conventions TypeScript
└── rules-architect/         # Rules mode Architect uniquement
    └── design-patterns.md   # Patterns de conception preferes
```

---

## Configuration Projet

Les instructions projet s'appliquent uniquement au projet courant et peuvent etre versionnees avec Git.

### Structure Recommandee (.roo/)

Creez le repertoire `.roo/rules/` a la racine de votre projet :

```
mon-projet/
├── .roo/
│   ├── rules/                    # Rules generales projet
│   │   ├── 01-conventions.md    # Conventions du projet
│   │   ├── 02-architecture.md   # Regles architecturales
│   │   └── 03-tests.md          # Standards de tests
│   ├── rules-code/              # Rules mode Code
│   │   └── style-guide.md       # Guide de style specifique
│   └── rules-architect/         # Rules mode Architect
│       └── planning-rules.md    # Regles de planification
├── src/
├── package.json
└── README.md
```

### Exemple de Configuration Projet

**`.roo/rules/01-conventions.md` :**
```markdown
# Conventions du Projet

## Technologies
- Framework : React 18 avec TypeScript
- State management : Zustand
- Tests : Vitest + Testing Library

## Architecture
- Components dans `src/components/`
- Hooks personnalises dans `src/hooks/`
- Services API dans `src/services/`

## Conventions de nommage
- Components : PascalCase (ex: `UserProfile.tsx`)
- Hooks : camelCase avec prefix `use` (ex: `useAuth.ts`)
- Utilitaires : camelCase (ex: `formatDate.ts`)
```

**`.roo/rules-code/style-guide.md` :**
```markdown
# Guide de Style - Mode Code

## TypeScript
- Strict mode active
- Interfaces preferees aux types pour les objets
- Eviter `any`, utiliser `unknown` si necessaire

## React
- Functional components uniquement
- Hooks pour la logique reutilisable
- Props destructurees dans la signature

## Exemple de component
\`\`\`tsx
interface UserCardProps {
  user: User;
  onSelect?: (id: string) => void;
}

export function UserCard({ user, onSelect }: UserCardProps) {
  return (
    <div onClick={() => onSelect?.(user.id)}>
      {user.name}
    </div>
  );
}
\`\`\`
```

---

## Fichier .roorules (Legacy)

Pour une configuration simple ou pour la retrocompatibilite, vous pouvez utiliser un fichier `.roorules` a la racine du projet.

### .roorules (Generique)

```markdown
# .roorules

Ce projet utilise Python 3.11 avec FastAPI.

## Conventions
- Docstrings Google-style pour toutes les fonctions publiques
- Type hints obligatoires
- Tests avec pytest

## Architecture
- Routes dans `app/routes/`
- Modeles Pydantic dans `app/models/`
- Services dans `app/services/`
```

### .roorules-{mode} (Mode-specific)

Vous pouvez creer des fichiers specifiques a un mode :

**`.roorules-code` :**
```markdown
# Mode Code - Instructions specifiques

Lors de la generation de code :
- Ajouter les imports manquants automatiquement
- Inclure les type hints
- Generer les tests unitaires correspondants
```

**`.roorules-architect` :**
```markdown
# Mode Architect - Instructions specifiques

Lors de la planification :
- Toujours proposer un diagramme Mermaid
- Identifier les risques techniques
- Estimer la complexite (simple/moyenne/complexe)
```

---

## AGENTS.md

Le fichier `AGENTS.md` permet de standardiser les instructions pour une equipe entiere. Il est generalement versionne avec le code.

### Activation

Pour activer le support AGENTS.md :

1. Ouvrez les parametres VS Code (`Ctrl+,` / `Cmd+,`)
2. Recherchez "Roo"
3. Activez l'option **"Use AGENTS.md"**

Ou via les settings JSON :
```json
{
  "roo.useAgentsFile": true
}
```

### Format AGENTS.md

Creez le fichier `AGENTS.md` a la racine du projet :

```markdown
# AGENTS.md

## Instructions generales

Ce projet suit les principes SOLID et utilise une architecture hexagonale.

### Standards de qualite
- Couverture de tests minimum : 80%
- Documentation des APIs publiques obligatoire
- Code review requise avant merge

### Conventions Git
- Commits conventionnels (feat:, fix:, docs:, etc.)
- Branches : feature/, bugfix/, hotfix/
- Squash merge sur main

## Mode Code

### Generation de code
- Toujours inclure la gestion d'erreurs
- Logger les operations importantes
- Valider les inputs utilisateur

### Tests
- Un fichier de test par module
- Nommage : `test_*.py` ou `*.test.ts`
- Mocks pour les dependances externes

## Mode Architect

### Documentation
- Diagrammes C4 pour l'architecture
- ADR (Architecture Decision Records) pour les choix importants
- Schemas de donnees documentes

### Planification
- Decomposer en taches de max 4h
- Identifier les dependances
- Prevoir les points de validation
```

---

## Modes Disponibles

Roo propose plusieurs modes de travail, chacun pouvant avoir ses propres instructions.

| Mode | Slug | Description | Fichier rules |
|------|------|-------------|---------------|
| Code | `code` | Developpement et implementation | `.roo/rules-code/` |
| Architect | `architect` | Planification et conception | `.roo/rules-architect/` |
| Ask | `ask` | Questions et explications | `.roo/rules-ask/` |
| Docs Writer | `docs-writer` | Documentation | `.roo/rules-docs-writer/` |
| Debug | `debug` | Debug et diagnostic | `.roo/rules-debug/` |

### Creer des Rules Mode-Specific

```bash
# Mode Code
mkdir -p .roo/rules-code
echo "Toujours inclure des tests unitaires" > .roo/rules-code/testing.md

# Mode Architect
mkdir -p .roo/rules-architect
echo "Utiliser des diagrammes Mermaid" > .roo/rules-architect/diagrams.md

# Mode Docs Writer
mkdir -p .roo/rules-docs-writer
echo "Documentation en francais, technique mais accessible" > .roo/rules-docs-writer/style.md
```

---

## Ordre de Chargement Detaille

Voici l'ordre exact dans lequel Roo charge et fusionne les instructions :

```
1. Instructions globales (interface Prompts)
   ↓
2. Instructions mode-specific globales (interface Prompts)
   ↓
3. ~/.roo/rules/*.md (ordre alphabetique)
   ↓
4. ~/.roo/rules-{mode}/*.md (ordre alphabetique)
   ↓
5. .roo/rules/*.md (ordre alphabetique)
   ↓
6. .roo/rules-{mode}/*.md (ordre alphabetique)
   ↓
7. .roorules (si present, legacy)
   ↓
8. .roorules-{mode} (si present, legacy)
   ↓
9. AGENTS.md (si active)
```

**Conseil :** Utilisez des prefixes numeriques pour controler l'ordre de chargement :

```
.roo/rules/
├── 01-conventions.md      # Charge en premier
├── 02-architecture.md     # Charge en second
└── 99-overrides.md        # Charge en dernier (priorite haute)
```

---

## Bonnes Pratiques

### Organisation des Fichiers

1. **Prefixes numeriques** pour l'ordre : `01-`, `02-`, `10-`, `99-`
2. **Noms descriptifs** : `conventions-typescript.md` plutot que `rules.md`
3. **Un sujet par fichier** : facilite la maintenance et la comprehension
4. **Commentaires** : expliquez le "pourquoi" des regles

### Contenu des Rules

1. **Format Markdown** : titres, listes, exemples de code
2. **Instructions claires** : evitez l'ambiguite
3. **Exemples concrets** : montrez ce que vous attendez
4. **Contexte** : expliquez quand appliquer la regle

### Versionnement

1. **Committez `.roo/rules/`** : partagez avec l'equipe
2. **Ignorez les rules personnelles** : `~/.roo/` reste local
3. **Documentez les changements** : CHANGELOG pour les rules importantes

### Performance

1. **Evitez les fichiers trop longs** : impact sur le contexte
2. **Soyez specifiques** : instructions ciblees > instructions generiques
3. **Nettoyez regulierement** : supprimez les rules obsoletes

---

## Exemples Complets

### Projet Python Data Science

```
mon-projet-ml/
├── .roo/
│   ├── rules/
│   │   └── 01-python-ds.md
│   └── rules-code/
│       └── jupyter-rules.md
```

**`.roo/rules/01-python-ds.md` :**
```markdown
# Conventions Data Science

## Environnement
- Python 3.11+
- Conda pour la gestion des environnements
- Jupyter pour l'exploration

## Libraries standards
- pandas pour la manipulation de donnees
- scikit-learn pour le ML classique
- matplotlib/seaborn pour la visualisation

## Structure des notebooks
1. Imports et configuration
2. Chargement des donnees
3. Exploration (EDA)
4. Preprocessing
5. Modelisation
6. Evaluation
7. Conclusions

## Conventions
- Cellules courtes et documentees
- Reproductibilite : seeds fixes, versions documentees
- Noms de variables explicites
```

### Projet TypeScript/React

```
mon-app-react/
├── .roo/
│   ├── rules/
│   │   ├── 01-architecture.md
│   │   └── 02-conventions.md
│   ├── rules-code/
│   │   └── react-patterns.md
│   └── rules-architect/
│       └── component-design.md
├── AGENTS.md
```

**`.roo/rules/01-architecture.md` :**
```markdown
# Architecture React

## Structure
\`\`\`
src/
├── components/     # Composants reutilisables
│   ├── ui/        # Composants UI generiques
│   └── features/  # Composants metier
├── hooks/         # Hooks personnalises
├── services/      # Appels API
├── stores/        # State management (Zustand)
├── types/         # Types TypeScript
└── utils/         # Fonctions utilitaires
\`\`\`

## Regles
- Un composant par fichier
- Co-localiser tests et styles
- Exports nommes (pas de default export)
```

---

## Migration depuis .roorules

Si vous avez un fichier `.roorules` existant, migrez vers la nouvelle structure :

### Etape 1 : Creer la structure

```bash
mkdir -p .roo/rules
mkdir -p .roo/rules-code
mkdir -p .roo/rules-architect
```

### Etape 2 : Deplacer le contenu

Divisez le contenu de `.roorules` en fichiers thematiques :

```bash
# Extraire les conventions generales
# -> .roo/rules/01-conventions.md

# Extraire les regles de code
# -> .roo/rules-code/01-style.md

# Extraire les regles d'architecture
# -> .roo/rules-architect/01-design.md
```

### Etape 3 : Supprimer l'ancien fichier (optionnel)

```bash
rm .roorules
```

**Note :** Roo continue de supporter `.roorules` pour la retrocompatibilite.

---

## Resolution de Problemes

### Les rules ne sont pas appliquees

1. **Verifiez l'emplacement** : `.roo/rules/` doit etre a la racine du workspace ouvert
2. **Verifiez le format** : fichiers `.md` uniquement
3. **Rechargez VS Code** : parfois necessaire apres ajout de fichiers
4. **Consultez les logs** : Output > Roo Code

### Conflit entre rules

Les rules de priorite superieure ecrasent les inferieures. Pour debugger :

1. Identifiez les sources en conflit
2. Reorganisez les fichiers (prefixes numeriques)
3. Utilisez des rules plus specifiques (mode-specific)

### AGENTS.md non pris en compte

1. Verifiez que l'option est activee dans les settings
2. Le fichier doit etre a la racine du workspace
3. Le format doit etre Markdown valide

---

## Ressources

- [Documentation Roo Code - Custom Instructions](https://docs.roocode.com/features/custom-instructions)
- [Guide des Modes Roo](https://docs.roocode.com/basic-usage/using-modes)
- [Best Practices](https://docs.roocode.com/tips-and-tricks/effective-prompting)

---

*Pour l'installation de Roo Code, consultez [INSTALLATION-ROO.md](./INSTALLATION-ROO.md)*

*Pour le parcours d'apprentissage guide, consultez [ROO-GUIDED-PATH.md](./ROO-GUIDED-PATH.md)*
