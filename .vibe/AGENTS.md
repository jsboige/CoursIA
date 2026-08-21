# AGENTS.md - Mistral Vibe Workspace Configuration (CoursIA)
# Instructions specifiques au workspace D:\dev\CoursIA

**Workspace:** CoursIA  
**Machine:** myia-po-2025  
**Role:** Worker agent (30min cycles, aligned sur scheduler myia-ai-01)  
**Commande:** `.vibe/commands/continue.md`  
**Config locale:** `.vibe/config.toml` (override global si besoin)  

---

## Configuration locale

### Fichiers du harnais
```
D:\dev\CoursIA\.vibe\
├── config.toml          # Config MCP locale (override ~/.vibe/config.toml)
├── AGENTS.md           # Instructions workspace (ce fichier)
└── commands\
    └── continue.md      # Commande worker principale
```

### MCP roo-state-manager (stdio local)

**Outils disponibles** (noms complets avec server prefix) :
- roo-state-manager_roosync_dashboard
- roo-state-manager_roosync_messages
- roo-state-manager_roosync_search
- roo-state-manager_codebase_search
- roo-state-manager_conversation_browser
- Et 10 autres...

**Permissions:** `permission = "always"` dans config.toml

---

## Commande Worker : `.vibe/commands/continue.md`

### Workflow (30 min max)

**Phase 1 : Contexte**
1. roosync_messages(action:"inbox", status:"unread")
2. roosync_dashboard(action:"read", type:"workspace", section:"all")
3. Filtrer par machine:myia-po-2025
4. git checkout main && git pull --ff-only

**Phase 2 : Priorisation**
- P0 : Missions coordinateur HIGH/URGENT
- P1 : Taches [CLAIMED] par myia-po-2025
- P2 : Pool global -> Poser [CLAIMED] <#N> -- <machine:myia-po-2025> <ts>

**Phase 3 : Execution**
- 1 sujet = 1 PR, catalogue byte-identique
- Notebooks : C.1/C.2/H.3
- Toujours SOTA, jamais workaround (regle F)

**Phase 4 : Rapport**
1. Commit + PR AVANT [DONE]
2. [DONE] <machine:myia-po-2025> <resume> -- PR#<N> -- grade: <A/B/C>
3. [ASK USER] separe si bloqueur

---

## Fallback MCP

### Lecture directe des fichiers GDrive
```
G:/Mon Drive/Synchronisation/RooSync/.shared-state/dashboards/workspace-CoursIA.md
G:/Mon Drive/Synchronisation/RooSync/.shared-state/dashboards/workspace-CoursIA-2.md
G:/Mon Drive/Synchronisation/RooSync/.shared-state/dashboards/workspace-roo-extensions.md
```

### Commande git/gh
```bash
gh issue list --state open --json number,title,labels
gh pr list --state open --author @me
```

---

## Scheduler

- Frequence : 30 min (staggered)
- Alignment : scheduler myia-ai-01 (schtasks)
- Commande : `vibe --prompt .vibe/commands/continue.md --timeout 1800 --agent auto-approve`

---

## Notes specifiques Vibe

1. Pas de session persistante -> etablir contexte depuis dashboard
2. CLI non-interactif -> checkpoints frequents dans dashboard
3. mistral-medium-3.5 -> utiliser bash pour execution code
4. Timeout a 27 min : commit [WIP] + [DONE-PARTIAL]
5. MCP stdio fonctionne -> utiliser noms complets: roo-state-manager_*

---

## Exemples

```
# Lire dashboard
roosync_dashboard(action: "read", type: "workspace", section: "all")

# Poster message
roosync_dashboard(action: "append", type: "workspace", tags: ["DONE"], content: "[DONE] myia-po-2025: PR #12345 -- grade: A")

# Chercher
roosync_search(query: "fix main red", limit: 10)
```

---

## Erreurs connues

| Erreur | Solution |
|--------|----------|
| Tool call failed (silent) | Verifier config.toml, redemarrer |
| HTTP 502/429 | Attendre 5h, fallback GDrive |
| MCP not found | Verifier cwd dans config.toml |

---

## Changelog

| Date | Action | Par |
|------|--------|-----|
| 2026-08-20 | Creation + correction MCP | jsboige + Mistral Vibe |
| 2026-08-20 | Annonce dans 3 dashboards | Mistral Vibe |

---

*"La mer, pas le burin" — Alexandre Grothendieck*
