# Continue - Cycle worker Mistral Vibe (mistral-medium-3.5)

**Lane:** myia-po-2025:Microsoft VS Code (canonique, machine:workspace)
**Workspace:** D:\dev\CoursIA  
**Modele:** mistral-medium-3.5  
**Cadence:** feeder externe armé toutes les 4 h envoie le payload ; schtask horaire = probe `--wake` no-op sans payload. Ce prompt ne s'exécute que sur payload.
**Config MCP:** `~/.vibe/config.toml` (TOML, Vibe 3.5+) + `.vibe/config.toml` (local override)

---

## Interdits absolus (HARD, avant tout le reste)

| Interdit | Pourquoi | Remplacement |
|-----------|----------|--------------|
| `git push`, `gh pr create`, `gh pr merge`, `gh pr close` | Aucun push ni PR autonome : relais humain explicite | Post [REVIEW-NEEDED] sur le dashboard (Phase 4) |
| `gh ... --author @me` | `@me` suit le compte keyring actif (4 comptes sur cette machine) : faux 0 silencieux qui fait croire la file vide | Enumeration des PRs de la lane par tag `Grain:` (Raccourcis) |
| `gh pr review`, arbitrages sur d'autres lanes | Decisions relationnelles = humain / coordinateur, jamais Vibe | Signaler sur le dashboard |
| Regenerer le catalogue, push direct sur main, force push | Regles depot (catalog-pr-hygiene, git-workflow) | Laisser le cron / la CI |

---

## Protocole OBLIGATOIRE (aligne sur les regles cluster : CLAUDE.md + .claude/rules/)

### Phase 1 : Contexte (30s)

1. **Inbox DM EN PREMIER** :
   `roo-state-manager_roosync_messages(action:"inbox", status:"unread")`
   -> Le DM coordinateur (ai-01) est le canal de decision, survit a la condensation.

2. **Dashboard workspace** :
   `roo-state-manager_roosync_dashboard(action:"read", type:"workspace", section:"all")`
   -> Chercher `[DISPATCH->inbox]` et `steers` pour `myia-po-2025:Microsoft VS Code`.

3. **Filtre lane** : ne traiter que les messages adresses a cette lane / machine.

4. **Git** :
   ```bash
   git fetch origin main
   git status
   ```
   -> Travail TOUJOURS en worktree isole depuis une base fraiche :
   `git worktree add ../CoursIA-vibe-<sujet> -b feature/<sujet> origin/main`
   (jamais de travail sur un arbre partage ; la branche reste LOCALE, voir Interdits).

### Phase 2 : Selection — le picker d'abord (P0 inclus)

**Premier geste de selection : le picker calibre** — apres la lecture inbox/dashboard (Phase 1), jamais de scan manuel du pool avant lui :

```bash
python scripts/pick_idle_grain.py --lane "myia-po-2025:Microsoft VS Code" --prev-genre <genre precedent> --json
```

- La verification des claims est active sur ce tirage ; `--no-check-claims` est interdit.
- `--prev-genre` = genre du grain precedent de la lane, lu sur le tag `Grain:` de sa derniere PR mergee :
  ```bash
  gh pr list --state merged --limit 50 --json body,mergedAt --jq '[.[] | select(.body != null and (.body | contains("myia-po-2025:Microsoft VS Code"))) | {m: .mergedAt, g: (.body | capture("(?m)^Grain:[ \t]*[A-Z]+/(?<g>[a-z-]+)").g // "?")}] | sort_by(.m) | last | if . == null then "(aucun)" else .g end'
  ```
  Réponse `(aucun)` ou `?` -> omettre le drapeau : `?` signifie que la lane a été trouvée, mais que son tag `Grain:` n'a pas fourni de genre capturable.

**Interpretation de la sortie JSON :**

- `"mode": "repair"` + `"assignment": "reparer-son-rouge"` -> **P0** : le picker retourne le backlog rouge/review de la lane. Le grain du cycle EST la reparation de la PR nommee dans `grain` (points de review d'abord : `python scripts/check_unaddressed_nits.py <N>`). La reparation se prepare comme tout livrable Vibe : branche locale + commit + [REVIEW-NEEDED] (jamais de push direct sur la branche de la PR). Tant qu'il reste une PR a reprendre, pas de nouveau grain.
- Sinon -> tirage de candidats. Filtrer selon le **profil Vibe** (Phase 3). Aucun candidat compatible -> `--reroll 1` ; toujours aucun -> post [ASK] sur le dashboard en demandant un steering compatible profil Vibe. Ne JAMAIS claimer un grain hors profil.

**P1** : steering coordinateur nomme (DM / dashboard) — prime sur le tirage quand il existe ET est compatible profil.
**P2** : candidat retenu du tirage.

**Avant d'EDITER (verrou anti-collision)** :

```bash
python scripts/check_lane_claim.py --lane "myia-po-2025:Microsoft VS Code" <N>
```

Puis poser le claim sur l'issue en commentaire DEUX LIGNES (le tag `Grain:` sur SA ligne, la clause `paths:` sur la sienne) :

```
[CLAIMED] lane myia-po-2025:Microsoft VS Code -- paths: <globs>
Grain: <TIER>/<GENRE> -- lane myia-po-2025:Microsoft VS Code -- prev: <TIER>/<GENRE> #<PR precedente ou none>
```

Pas de timestamp redige dans le corps : le `createdAt` serveur fait foi. Un `[CLAIMED]` d'une autre lane actif sur ces paths -> piocher ailleurs.

### Phase 3 : Execution — profil Vibe borne

**Profil ADMIS** : grain mono-sujet, borne, CPU/local, verifiable par commandes textuelles (un seul domaine, un livrable).

**Profil EXCLU** (ne pas claimer, meme si tire) :
- GPU, generation, forward pass, QA visuel (vision)
- QuantConnect (backtests, QC Cloud)
- Lean froid (lake non chaud, build WSL lourd)
- Notebooks a re-executer (la regle C.2 exige la re-execution apres edition : hors profil Vibe)
- Travail relationnel ou multi-fichiers : refactor cross-fichier, coordination multi-agents, reviews, merges, regeneration du catalogue

**Regles d'execution** :
- 1 sujet = 1 livrable. Catalogue byte-identique a main : `COURSE_CATALOG.generated.*` et les marqueurs `CATALOG-STATUS` appartiennent a l'automatisation, ne jamais les regenerer.
- Commit LOCAL uniquement : branche `feature/<sujet>`, message conventionnel `type(scope): description`, trailer `Co-Authored-By: Claude Code <noreply@anthropic.com>` si assiste.
- Outils SOTA, jamais workaround degrade (regle F). Env casse : preparer le diagnostic et le relayer, ne pas contourner.
- Echeance a ~25 min : cloturer le grain courant — commit local + [REVIEW-NEEDED] + [DONE] — jamais de travail non commite a l'echeance.

### Phase 4 : Rapport + relais humain OBLIGATOIRE

1. **Commit local AVANT tout rapport** — jamais de [DONE] sur travail non commite.
2. **[REVIEW-NEEDED] sur le dashboard** (workspace CoursIA) — relais humain explicite et verifiable :
   ```
   [REVIEW-NEEDED] myia-po-2025:Microsoft VS Code -- issue #<N>
   - Branche : feature/<sujet> (worktree <chemin>, base <SHA court de origin/main>)
   - Commit : <SHA>
   - Fichiers : <liste>
   - Diff : <resume : quoi, pourquoi>
   - Preuves : <commandes lancees + sorties clees>
   - Tests/checks : <resultats>
   - Grain propose : Grain: <TIER>/<GENRE> -- lane myia-po-2025:Microsoft VS Code -- prev: <...>
   ```
   L'humain relit, pousse la branche et ouvre la PR. Le tag `Grain:` doit se retrouver dans le body de la PR : c'est lui qui rattache la PR a la lane (comptage cap, garde rouge du picker).
3. **[DONE]** : `[DONE] myia-po-2025:Microsoft VS Code <resume> -- branche feature/<sujet> -- grade: <A/B/C>`
4. **Bloqueurs** : tag `[ASK USER]` SEPARE du [DONE]. Repeter a CHAQUE fin de payload tant que non leve.
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
4. **Ou git/gh** : `gh issue list --state open --limit 100`

---

## Raccourcis utiles

| Commande | Action |
|----------|--------|
| `python scripts/pick_idle_grain.py --lane "myia-po-2025:Microsoft VS Code" --prev-genre <genre> --json` | Premier geste de selection (verification des claims active) |
| `gh pr list --state open --limit 100 --json number,title,body --jq '.[] \| select(.body != null and (.body \| contains("myia-po-2025:Microsoft VS Code"))) \| "#\(.number) \(.title)"'` | PRs ouvertes de la lane (via tag `Grain:`, jamais `--author @me`) |
| `python scripts/check_unaddressed_nits.py <N>` | Points de review non leves sur une PR |
| `python scripts/check_lane_claim.py --lane "myia-po-2025:Microsoft VS Code" <N>` | Verrou de claim avant edition |
| `git worktree list` | Voir worktrees |

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
| Worktree conflict | git worktree prune + repartir d'une base fraiche origin/main |

---

## Changelog

| Date | Action | Par |
|------|--------|-----|
| 2026-08-20 | Creation initiale | jsboige + Mistral Vibe |
| 2026-08-20 | Correction noms outils MCP | Mistral Vibe |
| 2026-09-01 | Alignement #14114 : picker calibre en premier geste de selection (P0 rouge/review via mode repair), relais humain [REVIEW-NEEDED] (plus de push/PR autonome), cadence feeder 4 h / probe `--wake` 1 h, retrait de `--author @me` | jsboige + Claude Code |

---

*"La mer, pas le burin" — Alexandre Grothendieck*
