# CoursIA - Project Memory

## Architecture Claude Code (Fevrier 2026)

Structure modernisee : 16 agents, 9 skills, 6 commands, 5 rules, CLAUDE.md allege (~160 lignes).
Details : [claude-config.md](claude-config.md)

### Skills vs Commands (lecon apprise)
- Frontmatter skills : SEULEMENT `name`, `description`, `compatibility`, `license`, `metadata`
- `user-invocable`, `disable-model-invocation`, `argument-hint` = NON SUPPORTES
- **Commands** (`.claude/commands/`) = raccourcis `/slash` pour l'utilisateur
- **Skills** (`.claude/skills/`) = documents de reference auto-charges par Claude
- Architecture : commands delegent aux skills pour le contenu detaille
- Preferer scripts locaux (`notebook_tools.py`, `notebook_helpers.py`) au MCP pour Python

## Nouveaux agents (Mars 2026) - Series Workflow

### series-improver (nouveau)
- **Role**: Orchestration de series de notebooks avec persistance de progression
- **Fichier**: `.claude/agents/series-improver.md`
- **Usage**: Amelioration batch avec reprise apres redemarrage VSCode
- **Progression**: `.claude/progress/*.json`
- **Script**: `scripts/series_progress_manager.py`

### Integration notebook-iterative-builder
- Ajout capacite de reprise (checkpoint par notebook)
- Integration avec series-improver pour workflows de serie

### Workflow serie type
```
1. series-improver -> orchester la serie
2. notebook-iterative-builder -> traiter chaque notebook
3. notebook-validator -> valider qualite
4. notebook-enricher -> ajouter contenu pedagogique
5. readme-updater -> mettre a jour README serie
```

### Commandes utiles
```bash
# Lister sessions actives
python scripts/series_progress_manager.py list

# Statut session
python scripts/series_progress_manager.py status search-part1-foundations

# Rapport
python scripts/series_progress_manager.py report search-part1-foundations
```

## Retours d'experience cles

### Notebooks - Enrichissement pedagogique
- Inserer les interpretations APRES la cellule de code (pas avant)
- Travailler du BAS vers le HAUT pour eviter le decalage d'indices
- Toujours re-lire le notebook apres chaque edit (les indices changent)
- Utiliser `cell_id` et non l'index pour NotebookEdit insertions
- Ratio cible : ~40% markdown / 60% code

### Notebooks - Execution
- .NET + `#!import` : cell-by-cell UNIQUEMENT (Papermill bloque)
- .NET cold start : premier demarrage timeout 30-60s, relancer une fois
- PyGad : reduire `num_generations` pour tests rapides (>300s sinon)
- `plt.close()` apres `plt.show()` pour mode batch (sinon bloque)
- BATCH_MODE=true pour notebooks avec widgets interactifs

### WSL Kernels
- Wrapper BASH obligatoire (pas Python) : backslashes consommes par WSL
- Regex reconstruction : `^c:Users([a-zA-Z0-9_]+)AppDataRoaming...`
- Logs debug : `/tmp/kernel-wrapper.log` dans WSL
- Heredoc dans bash -c : ecrire via fichier temp, pas inline

### Modeles et sous-agents
- haiku : taches simples (README, recherche rapide)
- sonnet : taches standard (execution, validation, enrichissement)
- opus/inherit : taches complexes (conception, construction iterative)
- Toujours verifier le travail des sous-agents haiku sur taches critiques

### Execution notebooks - TOUJOURS utiliser les scripts
- **Python** : `python scripts/notebook_tools.py execute [target]` (PAS papermill direct)
- **.NET** : Cell-by-cell via MCP Jupyter ou agent notebook-executor
- Scripts disponibles : `notebook_tools.py`, `notebook_helpers.py`
- Raison : gestion kernels, environnements, chemins configures correctement
- JAMAIS lancer papermill ou ipython directement sans passer par les scripts

### Git / Workflow
- Jamais `git push --force` sans approbation explicite
- Committer les enrichissements separement des outputs d'execution
- Preferer `git add <fichiers specifiques>` a `git add -A`

## Erreurs frequentes a eviter

| Erreur | Consequence | Prevention |
|--------|------------|------------|
| Oublier re-read apres NotebookEdit | Indices decales, edits au mauvais endroit | Re-lire systematiquement |
| Papermill sur .NET notebooks | Kernel bloque indefiniment | Toujours cell-by-cell pour .NET |
| Enrichissement avant le code | Rompt le flux pedagogique | Interpretation = APRES l'output |
| `cat << 'EOF'` dans bash -c WSL | Variables interpolees malgre quotes | Fichier temp + copie WSL |
| Prefixes "Enhanced/Advanced/Pure" | Nommage non professionnel | Noms descriptifs uniquement |

## Services GenAI

- Qwen Image Edit : VAE 16 canaux, scheduler=beta, cfg=1.0, shift=3.0
- Z-Image/Lumina : diffusers 0.34+, LuminaPipeline (pas LuminaText2ImgPipeline)
- Qdrant disponible : `qdrant.myia.io` (credentials dans .env)

## Liens vers fichiers detailles

- [claude-config.md](claude-config.md) - Architecture agents/skills/rules
- [series-workflows.md](memory/series-workflows.md) - Suivi series et patterns d'erreurs
- Agents : `.claude/agents/*.md` (16 fichiers)
- Skills : `.claude/skills/*/SKILL.md` (9 fichiers)
- Rules : `.claude/rules/*.md` (5 fichiers)
