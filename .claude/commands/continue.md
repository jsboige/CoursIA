Resume work from GitHub issues — reads memory, checks state, picks next task, starts working.

## Workflow

### Phase 1 : Charger le contexte (30s)

1. Lire `MEMORY.md` (auto-memory) pour l'etat des sessions precedentes
2. Lire le tracker GitHub issue #29 (dashboard global)
3. `git status` et `git log --oneline -5` pour l'etat du depot
4. `gh issue list --label quantconnect --state open` pour les issues QC
5. `gh issue list --state open` pour toutes les issues ouvertes

### Phase 2 : Identifier la prochaine tache (30s)

Ordre de priorite :

1. **Issue en cours** : Si une issue a un commentaire recent "IN_PROGRESS", la reprendre
2. **BROKEN strategies** (#17, #18, #19, #27) : Issues label `priority-high`
3. **NEEDS_IMPROVEMENT strategies** (#20-#25) : Issues label `priority-medium`
4. **Documentation** (#30 README, #31 email Jared) : Quand les strategies sont traitees
5. **HEALTHY strategies** (#26 Sector-Momentum) : Enrichissement notebook
6. **Infrastructure** (#28 workflow) : Si necessaire

### Phase 3 : Presenter et commencer

Afficher un resume concis :

```
## Session Resume
- Dernier commit: {hash} {message}
- Issues ouvertes: {N} ({broken}/{needs_improvement}/{other})
- Prochaine tache: #{XX} {title}
- Raison: {pourquoi cette issue}
```

Puis commencer a travailler sur l'issue choisie :

- **Si issue QC strategie (#17-#27)** : Invoquer le skill `qc-iterative-improve` avec le numero d'issue
  ```
  /qc-iterative-improve #{XX}
  ```
- **Si issue README (#30)** : Lire le README actuel, explorer les sous-repertoires, rediger
- **Si issue email (#31)** : Lire le draft Gmail, finaliser
- **Si issue infrastructure (#28)** : Mettre a jour les fichiers skill/agent

### Phase 4 : Avant de terminer

Quand le travail sur l'issue est termine ou que le contexte sature :

1. Commenter l'issue avec le progres :
   ```
   gh issue comment #XX --body "Progress: {description}. Sharpe: {before} -> {after}."
   ```
2. Si l'issue est terminee : la fermer
   ```
   gh issue close #XX --comment "Done. {summary}"
   ```
3. Mettre a jour MEMORY.md avec les lecons apprises
4. Si --commit demande : commit les changements

## Notes

- Cette commande est **sans parametre** : elle choisit automatiquement la tache suivante
- Relancer `/continue` apres chaque saturation de contexte ou nouveau demarrage
- L'etat persiste via : issues GitHub + notebooks + backtests cloud + MEMORY.md
- Pour forcer une issue specifique, utiliser `/qc-iterative-improve #XX` directement
- Utiliser `/debrief` en fin de session pour consolider les apprentissages
