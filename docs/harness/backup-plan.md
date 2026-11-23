# Plan de sauvegarde des données hors-git — workspace `CoursIA-2`

> **Tenancier** : `myia-po-2027:CoursIA-2` (machine `myia-po-2027`, workspace `CoursIA-2`).
> **Mandat** : [jsboige/Maintenance#126](https://github.com/jsboige/Maintenance/issues/126) — « un plan de sauvegarde des configs et de tout ce qui n'est pas sous git […] tous les workspaces doivent avoir un plan de sauvegarde de leurs données critiques » (mandat user du 20/10/2026, incident po-2026).
> **Inventaire mesuré** : commentaire du 20/10/2026 sur #126 — 13 familles, 3 tests de restauration datés.
> **Doctrine de dépôt** : [jsboige/Maintenance#53](https://github.com/jsboige/Maintenance/issues/53) — archives 7z, jamais d'arbre brut sur DriveFS ; secrets chiffrés, jamais en clair.

## Périmètre

Ce plan couvre les données de la lane `myia-po-2027:CoursIA-2` qui **n'existent pas sous git** : mémoire de lane, secrets, définitions de tâches planifiées, transcripts, et le contenu non committé des worktrees. Les artefacts **versionnés** (notebooks, scripts, documentation) relèvent du canal git et ne sont pas repris ici.

Il ne couvre pas les familles machine partagées dont le propriétaire est une autre lane (`~/.claude.json`, `~/.roo-state-manager/.env`, coffre de clés partagé) : elles sont inventoriées et nommées, mais leur plan appartient à leur tenancier.

## Le patron : famille × canal × test de restauration

| Famille | Canal | Cadence | Rétention | Emplacement | Test de restauration |
|---|---|---|---|---|---|
| **Mémoire de lane** — `~/.claude/projects/d--dev-CoursIA-2/memory/**` (543 f, 2,76 Mo) | 7z **non chiffré** (convention du pilote, cf. scan de secrets ci-dessous) | quotidienne | 30 j | `G:\Mon Drive\Backups-Cloud\maintenance-lane-config\maint-lane-config-MYIA-PO-2027-<AAAAMMJJ>.7z` | T4 — à faire |
| **Secrets — source canonique** — `.secrets/master.env` (3 198 o) | 7z **chiffré** (mot de passe dans le coffre DPAPI, jamais dans l'archive ni dans le dépôt) | à chaque rotation + hebdomadaire | 90 j | `G:\Mon Drive\Backups-Cloud\maintenance-lane-config\maint-lane-config-MYIA-PO-2027-<AAAAMMJJ>.7z` (entrée `secrets/`) | **T1 — fait 20/10** |
| **Secrets — consommateurs** — 9 `.env` cibles déclarés (1 présent sur ce siège) | **re-génération** depuis `master.env` (`scripts/secrets/render_envs.py`) | à la demande | sans objet | local | **T1 — fait 20/10** |
| **Secrets hors périmètre de l'organe** — `.secrets/wsl_credentials`, `…/AI-Engine-WordPress/instance-jetable/.env` | à déclarer dans `TARGET_ENVS` → re-génération | idem | sans objet | local | à faire |
| **Coffre de clés DPAPI** — `scripts/secrets/agent_keyring.py` | **renvoi par la machine émettrice** — un blob DPAPI ne se restaure ni sur une autre machine ni sous un autre compte | sans objet | sans objet | `~/.fleet/` | déclaré non restaurable ailleurs |
| **Orchestration OS** — 7 tâches `Claude*` / `CoursIA*` / `RooSync*` | export XML (`Export-ScheduledTask`, non élevé) | quotidienne | 90 j | `G:\Mon Drive\Backups-Cloud\maintenance-lane-config\tasks-MYIA-PO-2027-<AAAAMMJJ>.xml` | **T3 — capture faite 20/10** ; re-création à prouver |
| **Transcripts** — 50 jsonl / 1,89 Go (ce projet), 403 / 4,34 Go (siège) | `ClaudeTranscriptArchive` (roo-extensions) : 7z vérifié `7z t` → copie offsite | quotidienne | 36 500 j (manifest) | `G:\Mon Drive\Backups-Cloud\claude-transcripts\myia-po-2027\` | **T2 — fait 20/10** |
| **Worktrees — contenu non committé** | **aucun canal** — trou ouvert, cf. §Trous | — | — | — | à faire |
| **Config RSM** — `~/.roo-state-manager/.env` (2 969 o) | **aucun sur ce siège** | — | — | — | à faire |

## Tests de restauration exécutés le 20/10/2026

Trois tests, exécutés et datés. La preuve de chacun est reproductible sur la machine qui l'a produit.

### T1 — Secrets : re-rend depuis la source canonique

Cible jetable (`…/scratchpad/restore-T1/`) : copie de `master.env` + des `.env` consommateurs + l'organe du dépôt, relancé à la racine jetable. Sortie de l'organe : `rc=0`.

| Fichier | SHA256 vivant | SHA256 restauré | Verdict |
|---|---|---|---|
| `MyIA.AI.Notebooks/SymbolicAI/Lean/.env` | `b3ba159502e98aec…` | `b3ba159502e98aec…` | **IDENTIQUE** |

→ la source canonique régénère byte-identiquement les `.env` consommateurs. C'est le **mode de restauration** de la famille « secrets », et il est démontré, pas supposé.

`--check` sur l'arbre vivant : `rc=1`, 3 clés du coffre divergent de `master.env` (`CIVITAI_TOKEN`, `DEMUCS_API_KEY`, `VLLM_API_KEY`). Dérive réelle, à traiter par rotation.

### T2 — Transcripts : restauration depuis la copie offsite

Archive offsite `G:\Mon Drive\Backups-Cloud\claude-transcripts\myia-po-2027\transcripts-myia-po-2027-2026-10-20T024103Z.7z` (22,7 Mo), fichier extrait **depuis la copie G:** — pas depuis l'archive locale.

| Fichier restauré | SHA256 | Vivant | Verdict |
|---|---|---|---|
| `d--dev-CoursIA-2\…\subagents\agent-aa86881a2df8aa5fe.jsonl` (1 172 998 o) | `1a2577c20e9ea0aa528b06044be2140acffba4c099dafd2fef8004f9e10c3a57` | identique | **IDENTIQUE** |

→ la chaîne archive locale → 7z vérifié → copie G: → restauration est prouvée de bout en bout. Les 27 archives locales et les 27 archives G: ont la même taille cumulée (602 547 791 o).

### T3 — Orchestration OS : fidélité de capture

`Export-ScheduledTask` non élevé : **7/7** exports XML réussis (1 277-2 089 o), chacun portant déclencheur, action et principal.

| Tâche | Dernier run | Résultat | XML |
|---|---|---|---|
| `ClaudeTranscriptArchive` | 20/10 04:41 | 0 | 1 583 o |
| `Claude-ApprovalStallDetector` | 20/10 11:37 | 0 | 1 674 o |
| `Claude-DashboardListener` | 20/10 13:19 | en cours | 1 949 o |
| `Claude-ListenerZombieWatchdog` | 20/10 13:11 | en cours | 2 089 o |
| `CoursIA-po2027-teacher-volume` | 10/10 00:33 | 0 | 1 277 o |
| `roo-rotate-scheduling-logs` | 20/10 04:53 | 0 | 2 016 o |
| `RooSync-Weekly-Seed` | 20/10 03:07 | 1 | 1 762 o |

**Ce que ce test ne prouve pas** : la re-création. Créer une tâche depuis un XML est un geste UAC ; il n'a pas été exécuté (pas de fenêtre user consommée sur un cycle automatisé). La capture est fidèle, la re-création reste à prouver sous fenêtre user.

## Trous ouverts, et qui les porte

| Rang | Trou | Pourquoi il compte | Geste | Porteur |
|---|---|---|---|---|
| 1 | **Mémoire de lane sans canal** — 543 éléments / 2,76 Mo, seule donnée portant l'historique de décisions de la lane (handover, `user-question-registry.md` à 77,6 Ko) | non reproductible : un disque mort la perd | export 7z quotidien vers `maintenance-lane-config`, puis test T4 | cette lane |
| 2 | **La seule tâche planifiée de la lane dépend d'un script hors git** — `CoursIA-po2027-teacher-volume` pointe vers `D:\dev\CoursIA-17578-volume\run_teacher_volume.ps1`, fichier `??` (non suivi) et **absent de tout ref** dans les deux clones du siège ; le même répertoire porte des données de teacher modifiées et non suivies (`…/data/teacher/`) | le payload de la tâche n'existe que sur ce disque — la leçon po-2026 à l'identique | commiter le script et les données de teacher dans le dépôt, ou documenter la reconstruction | cette lane |
| 3 | **Contenu non committé des worktrees** — 74 worktrees sur le clone `D:\dev\CoursIA` + 67 sur `D:\dev\CoursIA-2` ; `scripts/ci/prune_merged_worktrees.py` **refuse** de retirer un worktree sale | le contenu persiste sans canal : il ne survit ni à un nettoyage ni à une perte de disque | exporter le contenu des worktrees refusés avant tout `--apply`, ou le commiter | cette lane |
| 4 | **Secrets hors périmètre de l'organe** — `.secrets/wsl_credentials` (24 o) et l'`.env` de l'instance jetable AI-Engine-WordPress (1 450 o) | ni propagés, ni détectés, ni sauvegardés ; l'organe ne les voit pas | les déclarer dans `TARGET_ENVS` de `render_envs.py` | cette lane |
| 5 | **`~/.roo-state-manager/.env` (2 969 o) sans canal sur ce siège** | la tâche `RSM-backup-mcp-env-daily` que l'inventaire d'un autre siège déclare **n'existe pas ici** (relevé exhaustif : 218 tâches planifiées au total, 12 pertinentes après filtre, 0 nommée `RSM*` ou `*mcp-env*`) | créer le canal, ou renvoyer la donnée vers son propriétaire | tenancier de la famille RSM |

## Décisions de conception, et ce qu'elles coûtent

- **La mémoire de lane part non chiffrée**, comme l'archive du pilote (`maint-lane-config-MYIA-AI-01-20261020.7z`, extraite sans mot de passe le 20/10). Scan de la mémoire de cette lane avant de l'archiver : **aucune valeur de secret** — 3 correspondances, toutes des faux positifs (placeholders `<your_vllm_api_key>`, référence à `$GH_TOKEN` dans un extrait shell, prosa ordinaire). Le scan est à refaire à chaque export : la conclusion vaut pour l'état mesuré, pas pour l'avenir.
- **Les secrets partent chiffrés** dans la même archive. Le mot de passe vit dans le coffre DPAPI et ne part ni dans l'archive ni dans le dépôt.
- **Le coffre DPAPI n'est pas sauvegardé, il est re-fourni.** Un blob lié au compte et à la machine donne une fausse sécurité si on le copie : le fichier existe, il ne restaure pas ailleurs. Le mode déclaré est « renvoi par la machine émettrice ».
- **Un canal annoncé par un autre siège n'est pas un canal.** Le point 5 le montre par le négatif : le patron « canal / cadence / rétention / test » se mesure par machine.

## Comment reproduire les tests

- **T1** — `python scripts/secrets/render_envs.py --check` (drift, lecture seule) et, pour la preuve de re-rend, rejouer l'organe dans une arborescence jetable mirroring le dépôt puis comparer les SHA256.
- **T2** — `7z e "G:\Mon Drive\Backups-Cloud\claude-transcripts\myia-po-2027\<archive>.7z" -o<jetable> <fichier>` puis `Get-FileHash -Algorithm SHA256` sur le fichier extrait et sur le vivant.
- **T3** — `Export-ScheduledTask -TaskName <nom>` puis re-lecture des champs déclencheur / action / principal de l'export et de l'objet vivant.

## Voir aussi

- [jsboige/Maintenance#126](https://github.com/jsboige/Maintenance/issues/126) — mandat et inventaire de flotte.
- [jsboige/Maintenance#53](https://github.com/jsboige/Maintenance/issues/53) — doctrine Backups-Cloud (archives 7z, secrets chiffrés).
- `.claude/rules/secrets-hygiene.md` — centralisation `master.env`, coffre, canal privé.
- `scripts/secrets/render_envs.py` · `scripts/ci/prune_merged_worktrees.py` — instruments du dépôt cités ci-dessus.
