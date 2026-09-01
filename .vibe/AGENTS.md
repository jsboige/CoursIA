# AGENTS.md - Mistral Vibe Workspace Configuration (CoursIA)
# Instructions specifiques au workspace D:\dev\CoursIA

**Workspace:** CoursIA  
**Machine:** myia-po-2025  
**Lane canonique:** myia-po-2025:Microsoft VS Code
**Role:** Worker autonome a cadence 4 h, livrables en relais humain (jamais de push/PR autonome)
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

### Cadence : feeder 4 h, probe `--wake` 1 h

- Le **feeder externe**, arme toutes les 4 h, envoie le payload de travail.
- La **schtask horaire** reste un probe `--wake` : no-op tant qu'aucun payload n'est en attente.
- Ce prompt ne s'exécute que lorsque le feeder/wake fournit un payload — aucun arbitrage de cadence in-prompt.

### Workflow d'un payload

**Phase 1 : Contexte**
1. roosync_messages(action:"inbox", status:"unread")
2. roosync_dashboard(action:"read", type:"workspace", section:"all")
3. Filtrer par lane : myia-po-2025:Microsoft VS Code
4. git fetch origin main ; travail en worktree isole `feature/<sujet>` depuis origin/main

**Phase 2 : Selection — le picker d'abord (P0 inclus)**
- **Premier geste de selection : le picker calibre**, apres lecture inbox/dashboard — jamais de scan manuel du pool avant lui :
  `python scripts/pick_idle_grain.py --lane "myia-po-2025:Microsoft VS Code" --prev-genre <genre> --json`
  (verification des claims active ; `--no-check-claims` interdit)
- Sortie `"mode": "repair"` : **P0** — le picker retourne le backlog rouge/review de la lane ; la reparation de la PR nommee EST le grain du cycle, preparee en relais humain comme tout livrable Vibe.
- Sinon : filtrer les candidats selon le **profil Vibe** : mono-sujet, CPU/local, verifiable textuellement. Exclus : GPU/vision, QuantConnect, Lean froid, notebooks a re-executer, travail relationnel/multi-fichiers, catalogue (enumeration des PRs de la lane via le tag `Grain:` du body, jamais `--author @me` : faux 0 silencieux sur cette machine multi-comptes).
- Avant d'editer : `check_lane_claim.py --lane "myia-po-2025:Microsoft VS Code" <N>`, puis `[CLAIMED]` en commentaire d'issue (tag `Grain:` et clause `paths:` sur deux lignes distinctes).

**Phase 3 : Execution**
- 1 sujet = 1 livrable, catalogue byte-identique a main
- Outils SOTA, jamais workaround (regle F) ; env casse : diagnostiquer et relayer
- Commit LOCAL uniquement (branche `feature/<sujet>`, message conventionnel) — JAMAIS de push

**Phase 4 : Rapport + relais humain**
1. Commit local AVANT tout rapport
2. `[REVIEW-NEEDED]` sur le dashboard : branche, commit, fichiers, resume du diff, preuves, tests, tag `Grain:` propose — l'humain relit puis pousse / ouvre la PR
3. `[DONE] myia-po-2025:Microsoft VS Code <resume> -- branche <nom> -- grade: <A/B/C>`
4. `[ASK USER]` separe si bloqueur

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
gh issue list --state open --limit 100 --json number,title,labels
# PRs ouvertes de la lane, via le tag Grain: du body (jamais --author @me)
gh pr list --state open --limit 100 --json number,title,body --jq '.[] | select(.body != null and (.body | contains("myia-po-2025:Microsoft VS Code"))) | "#\(.number) \(.title)"'
```

---

## Scheduler

- **Feeder externe** : arme toutes les 4 h, il envoie le payload de travail.
- **Schtask horaire** : probe `--wake`, no-op tant qu'aucun payload n'est en attente.
- Le prompt `.vibe/commands/continue.md` ne s'exécute que sur payload fourni par le feeder/wake — aucun arbitrage de cadence in-prompt.

---

## Notes specifiques Vibe

1. Pas de session persistante -> etablir contexte depuis dashboard
2. CLI non-interactif -> checkpoints frequents dans dashboard
3. mistral-medium-3.5 -> utiliser bash pour execution code
4. Echeance a ~25 min : cloturer (commit local + [REVIEW-NEEDED] + [DONE]), jamais de travail non commite a l'echeance
5. MCP stdio fonctionne -> utiliser noms complets: roo-state-manager_*
6. Push et ouverture de PR ne sont JAMAIS autonomes : relais humain [REVIEW-NEEDED]

---

## Exemples

```
# Lire dashboard
roosync_dashboard(action: "read", type: "workspace", section: "all")

# Poster un livrable en relais humain
roosync_dashboard(action: "append", type: "workspace", tags: ["ASK"],
  content: "[REVIEW-NEEDED] myia-po-2025:Microsoft VS Code -- issue #N : branche feature/<sujet>, commit <SHA>, diff/preuves/tests ci-dessous")

# Poster la fin de payload
roosync_dashboard(action: "append", type: "workspace", tags: ["DONE"], content: "[DONE] myia-po-2025:Microsoft VS Code : <resume> -- branche feature/<sujet> -- grade: A")

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
| 2026-09-01 | Alignement #14114 : picker calibre en premier geste de selection (P0 rouge/review via mode repair), relais humain [REVIEW-NEEDED] (plus de push/PR autonome), cadence feeder 4 h / probe `--wake` 1 h, retrait de `--author @me` | jsboige + Claude Code |

---

*"La mer, pas le burin" — Alexandre Grothendieck*
