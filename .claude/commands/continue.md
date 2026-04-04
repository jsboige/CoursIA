# Continue - Resume Work

Resume work from GitHub issues OR local memory — reads context, checks state, picks next task, starts working.

## Workflow

### Phase 1 : Charger le contexte (30s)

1. Lire `MEMORY.md` (auto-memory) pour l'etat des sessions precedentes

2. **Option A - GitHub issues** (si applicable):

   - `git status` et `git log --oneline -5` pour l'etat du depot
   - `gh issue list --state open` pour les issues ouvertes

3. **Option B - Memoires locales** (si pas d'issue GitHub):

   - Lire `.claude/memory/*.md` pour les taches en cours
   - Identifier les fichiers memoire pertinents (ex: `issue-XX-*.md`)

### Phase 1.5 : Tour de coordination RooSync (obligatoire)

**TOUJOURS executer avant de commencer le travail**, pour detecter les nouvelles missions du coordinateur.

1. **Lire l'inbox RooSync** : `roosync_read` mode=inbox, status=unread
2. **Lire le dashboard workspace** : `roosync_dashboard` action=read, type=workspace, workspace=CoursIA
3. **Verifier le heartbeat** cluster : `roosync_heartbeat` action=status

**Si des missions ou messages HIGH/URGENT existent** :
- Lire le message complet avec `roosync_read` mode=message
- Les missions du coordinateur (ai-01) ont priorite sur les taches locales
- Repondre accusant reception sur le dashboard

**Presenter le statut coordination dans le resume** :
```text
## Coordination RooSync
- Messages non-lus: {N} (URGENT: {N}, HIGH: {N})
- Missions actives: {liste}
- Prochaine action coordinateur: {description ou "aucune"}
```

### Phase 2 : Identifier la prochaine tache (30s)

**Priorite 0 - Missions coordinateur** (si messages RooSync HIGH/URGENT):
1. Missions URGENT du coordinateur ai-01
2. Missions HIGH du coordinateur ai-01
3. Taches demandees via dashboard workspace

**Priorite 1 - GitHub** (si issues existent):

1. **Issue en cours** : Si une issue a un commentaire recent "IN_PROGRESS"
2. **BROKEN strategies** : Issues label `priority-high`
3. **NEEDS_IMPROVEMENT** : Issues label `priority-medium`
4. **Documentation/Infrastructure** : Quand le code est traite

**Priorite 2 - Memoires Locales** (si pas d'issue GitHub):

1. Chercher `.claude/memory/*.md` avec des taches en cours
2. Identifier la tache `in_progress` ou la plus ancienne `pending`
3. Lire le fichier memoire pour le contexte complet

### Phase 3 : Presenter et commencer

Afficher un resume concis :

```text
## Session Resume
- Mode: {COORDINATION / GITHUB / LOCAL_MEMORY}
- Source: {Mission RooSync / Issue #XX / Fichier memoire}
- Dernier commit: {hash} {message}
- Prochaine tache: {description}
- Etat: {in_progress / pending / completed}
```

Puis commencer a travailler :

**Si Mission coordinateur** :
- Executer les instructions du message RooSync
- Reporter les resultats sur le dashboard workspace
- Repondre au coordinateur via RooSync a la fin

**Si GitHub issue** :

- QuantConnect strategy : `/qc-iterative-improve #{XX}`
- README/Documentation : Lire et rediger
- Infrastructure : Mettre a jour fichiers skill/agent

**Si Memoire locale** :
- Restaurer la todo list depuis le memoire
- Continuer depuis la tache `in_progress` ou `pending`
- Executer les commandes specifiees dans le memoire

### Phase 4 : Avant de terminer

1. **Coordination** : Mettre a jour le dashboard workspace avec le progres
2. **GitHub** : Commenter/fermer l'issue
3. **Local** : Mettre a jour le fichier memoire avec le progres
4. Mettre a jour `MEMORY.md` avec les lecons apprises
5. Si --commit demande : commit les changements

## Notes

- Cette commande est **sans parametre** : elle choisit automatiquement la tache suivante
- **Phase 1.5 obligatoire** : toujours verifier RooSync avant de commencer
- L'etat persiste via : RooSync dashboard + issues GitHub + MEMORY.md + .claude/memory/*.md
- Pour forcer une tache specifique, utiliser le skill approprie directement
- Utiliser pour reprendre apres saturation de contexte ou nouveau demarrage
