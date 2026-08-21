# Continue - Cycle worker Mistral Vibe (mistral-medium-3.5)

**Lane:** myia-po-2025 (detectee via hostname)  
**Workspace:** D:\dev\CoursIA  
**Modele:** mistral-medium-3.5  
**Frequence:** 30 min (staggered, aligne sur scheduler myia-ai-01)  
**Config MCP:** `~/.vibe/config.toml` (TOML, Vibe 3.5+) + `.vibe/config.toml` (local override)

---

## Protocole OBLIGATOIRE (identique a Claude Code)

### Phase 1 : Contexte (30s)

1. **Inbox DM EN PREMIER** :
   `roo-state-manager_roosync_messages(action:"inbox", status:"unread")`
   -> Le DM coordinateur (ai-01) est le canal de decision, survit a la condensation.

2. **Dashboard workspace** :
   `roo-state-manager_roosync_dashboard(action:"read", type:"workspace", section:"all")`
   -> Chercher `[DISPATCH->inbox]` et `steers` pour `machine:myia-po-2025`.

3. **Filtre lane** : Ne traiter que messages adresses a cette lane/machine.

4. **Git** :
   ```bash
   git checkout main && git pull --ff-only
   git status
   ```
   -> Si arbre sale (WIP autrui) : worktree isole
   `git worktree add ../CoursIA-<sujet> -b feature/<sujet> origin/main`

---

### Phase 2 : Priorisation

**P0** : Missions coordinateur HIGH/URGENT (DM ou dashboard)  
**P1** : Taches `[CLAIMED]` par `myia-po-2025` non terminees  
**P2** : Pool global (`gh issue list --state open` cross-lane)  
   -> Poser `[CLAIMED] <#N> -- <machine:myia-po-2025> <ts>` AVANT de commencer

> **Regle** : >=1 PR/wakeup = PLANCHER. "Rien a faire" avec >0 issues = echec.

---

### Phase 3 : Execution

- **PR** : 1 sujet = 1 PR. Catalogue byte-identique a main.
  `Closes #N` si issue resolue, sinon `See #N`.
- **Notebooks** : C.1 (pas d'erreur), C.2 (commit AVEC outputs), H.3 (pre-commit).
- **Outils** : Toujours SOTA, jamais workaround degrade (regle F).
- **Env casse** : Reparer, pas contourner.
- **Skills** : Uniquement si delegation explicite.

---

### Phase 4 : Rapport OBLIGATOIRE (avant timeout)

1. **Commit + PR AVANT le rapport** -- jamais de [DONE] sur travail non commite.
2. **Dashboard** :
   `[DONE] <machine:myia-po-2025> <resume> -- PR#<N> -- grade: <A/B/C>`
3. **Bloqueurs** : Tag `[ASK USER]` **separe** du [DONE]. Repeter a CHAQUE fin.
4. **DM coordinateur** : Repondre si mission traitee.
5. **MEMORY.md** : MAJ si lecon durable.

---

## Notes specifiques Vibe

### MCP roo-state-manager

**Noms complets des outils** (avec prefix server) :
```
roo-state-manager_roosync_dashboard
roo-state-manager_roosync_messages
roo-state-manager_roosync_search
roo-state-manager_roosync_indexing
roo-state-manager_codebase_search
roo-state-manager_read_vscode_logs
roo-state-manager_export_data
roo-state-manager_roosync_compare_config
roo-state-manager_roosync_baseline
roo-state-manager_roosync_config
roo-state-manager_roosync_inventory
roo-state-manager_roosync_mcp_management
roo-state-manager_roosync_storage_management
roo-state-manager_roosync_diagnose
roo-state-manager_conversation_browser
```

**Permissions** : `permission = "always"` dans `~/.vibe/config.toml`

### Fallback si MCP echoue

1. **Reessayer** : 1x apres 10s
2. **Poster erreur** : `[MCP-ERROR] <timestamp> : <details>`
3. **Mode degrade** : Utiliser lecture directe GDrive :
   ```
   G:/Mon Drive/Synchronisation/RooSync/.shared-state/dashboards/
   ```
4. **Ou git/gh** : `gh issue list --state open`

---

## Raccourcis utiles

| Commande | Action |
|----------|--------|
| `gh issue list --state open --json number,title,labels` | Liste issues |
| `git worktree list` | Voir worktrees |
| `gh pr list --state open --author @me` | Mes PRs |

---

## Configuration

**Global** : `~/.vibe/config.toml`  
**Local** : `.vibe/config.toml` (override global)  
**AGENTS.md** : `~/.vibe/AGENTS.md` (user) + `.vibe/AGENTS.md` (workspace)

---

## Erreurs connues

| Probleme | Solution |
|----------|----------|
| MCP non charge | Verifier config.toml, redemarrer session |
| HTTP 502/429 | Attendre reset (5h), fallback GDrive |
| Tool call silent fail | Utiliser noms complets: roo-state-manager_* |
| Worktree conflict | git worktree prune + rebase frais |

---

## Changelog

| Date | Action | Par |
|------|--------|-----|
| 2026-08-20 | Creation initiale | jsboige + Mistral Vibe |
| 2026-08-20 | Correction noms outils MCP | Mistral Vibe |

---

*"La mer, pas le burin" — Alexandre Grothendieck*
