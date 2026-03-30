# Continue - Resume Work

Resume work from GitHub issues OR local memory — reads context, checks state, picks next task, starts working.

## Workflow

### Phase 1 : Charger le contexte (30s)

1. Lire `MEMORY.md` (auto-memory) pour l'etat des sessions precedentes

2. **Option A - GitHub issues** (si applicable):

   - `git status` et `git log --oneline -5` pour l'etat du depot
   - `gh issue list --state open` pour les issues ouvertes

3. **Option B - Mémoires locales** (si pas d'issue GitHub):

   - Lire `.claude/memory/*.md` pour les taches en cours
   - Identifier les fichiers memoire pertinents (ex: `issue-XX-*.md`)

### Phase 2 : Identifier la prochaine tache (30s)

**Priorité GitHub** (si issues existent):

1. **Issue en cours** : Si une issue a un commentaire recent "IN_PROGRESS"
2. **BROKEN strategies** : Issues label `priority-high`
3. **NEEDS_IMPROVEMENT** : Issues label `priority-medium`
4. **Documentation/Infrastructure** : Quand le code est traite

**Priorité Mémoires Locales** (si pas d'issue GitHub):

1. Chercher `.claude/memory/*.md` avec des taches en cours
2. Identifier la taque `in_progress` ou la plus ancienne `pending`
3. Lire le fichier memoire pour le contexte complet

### Phase 3 : Presenter et commencer

Afficher un resume concis :

```text
## Session Resume
- Mode: {GITHUB / LOCAL_MEMORY}
- Source: {Issue #XX / Fichier memoire}
- Dernier commit: {hash} {message}
- Prochaine tache: {description}
- Etat: {in_progress / pending / completed}
```

Puis commencer a travailler :

**Si GitHub issue** :

- QuantConnect strategy : `/qc-iterative-improve #{XX}`
- README/Documentation : Lire et rediger
- Infrastructure : Mettre a jour fichiers skill/agent

**Si Mémoire locale** :

- Restaurer la todo list depuis le memoire
- Continuer depuis la tache `in_progress` ou `pending`
- Executer les commandes specifiees dans le memoire

### Phase 4 : Avant de terminer

1. **GitHub** : Commenter/fermer l'issue

2. **Local** : Mettre a jour le fichier memoire avec le progres

3. Mettre a jour `MEMORY.md` avec les lecons apprises

4. Si --commit demande : commit les changements

## Notes

- Cette commande est **sans parametre** : elle choisit automatiquement la tache suivante
- L'etat persiste via : issues GitHub + notebooks + MEMORY.md + .claude/memory/*.md
- Pour forcer une tache specifique, utiliser le skill approprie directement
- Utiliser pour reprendre apres saturation de contexte ou nouveau demarrage
