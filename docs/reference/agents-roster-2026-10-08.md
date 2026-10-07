---
name: agents-roster-2026-10-08
description: Roster daté des machine:workspace actifs au 2026-10-08 (parent #14525, ferme #14527)
metadata:
  type: ephemeral
  parent: 14527
  parent-epic: 14525
  measured: 2026-10-08
---

# Roster daté 2026-10-08 — machine:workspace CoursIA

Ce roster accompagne l'issue **#14527** (« [Vibe-Coding] Établir le roster actif et préparer les redémarrages ou WAKE »). Il est **daté** et **éphémère** : il sera régénéré à chaque cycle où une décision de redémarrage ou de WAKE se pose. La référence **durable** sur la structure du cluster reste [cluster-agents.md](cluster-agents.md) — ce qui change peu.

L'acceptance de #14527 demande quatre familles de preuves (EXISTS, RECENT, CONTRIBUTES, REACHABLE) et quatre groupes (actifs/joignables, dormants VS Code, joignables WAKE-CLAUDE/HERMES/NANOCLAW, optionnels/redondants). Le point de passage user est obligatoire : **aucun redémarrage ou WAKE n'est lancé avant le choix user** (cf. corps de #14527).

## Légende de la grille

| Code | Sens |
|---|---|
| **EXISTS** | la machine et le workspace existent (cf. [cluster-agents.md](cluster-agents.md) + `roosync_inventory`) |
| **RECENT** | activité documentée sur les 7 derniers jours (DM, dashboard, cron, commit) |
| **CONTRIBUTES** | contribution mesurable : grain livré, dossier posé, PR mergée, ou service rendu |
| **REACHABLE** | joignable par l'un des canaux du cluster (LAN, dashboard, DM, WAKE-CLAUDE/HERMES/NANOCLAW) |

Date de mesure : **2026-10-08**, sources : `roosync_dashboard` (workspace + global), inbox RooSync, observations cross-session.

## Lanes observées

### Trio de tête (coordination)

| Lane | EXISTS | RECENT | CONTRIBUTES | REACHABLE | Groupe |
|---|---|---|---|---|---|
| `myia-ai-01:CoursIA` | ✓ | ✓ (c.247 + 13 merges 22:44Z 07/10) | ✓ (merges, dispatch, arbitrages) | ✓ (LAN ai-01) | **actif/joignable** |
| `myia-po-2025:CoursIA-2` | ✓ | ✓ (3 dossiers exact-head c.1472 + 3 escalades) | ✓ (dossiers READY/BLOCKED-WITH-SUBSTANCE) | ✓ (cross-lane) | **actif/joignable** |
| `myia-po-2026:CoursIA-3` | ✓ | ✓ (secrétariat) | ✓ (attestations tierces, DM nominatifs) | ✓ (cross-lane) | **actif/joignable** |

### Régisseur GPU + worker coordinateur

| Lane | EXISTS | RECENT | CONTRIBUTES | REACHABLE | Groupe |
|---|---|---|---|---|---|
| `myia-ai-01:CoursIA-2` | ✓ | ✓ (c.247-bis 22:42Z 07/10 + c.247-quater 00:49Z 08/10 GPU 2 RELEASED) | ✓ (PR #19801 DEEP/QC + Qwen3.5-9B-Base onset/SAE pickup) | ✓ (LAN ai-01) | **actif/joignable** |

### Workers po-*

| Lane | EXISTS | RECENT | CONTRIBUTES | REACHABLE | Groupe |
|---|---|---|---|---|---|
| `myia-po-2023:CoursIA` | ✓ | △ (c.1156 cession à `coursia-2-ef`) | △ (rend main après YIELD propre) | ✓ (cross-lane) | **dormant VS Code / joignable par cession** |
| `myia-po-2023:CoursIA-2` | ✓ | ✓ (`coursia-2-ef` actif cron `0cdddf27` 7,37 * * * *) | ✓ (Origami Wolfram pli 1, drain PRs réparation c.1152-1153) | ✓ (cross-lane) | **actif/joignable** |
| `myia-po-2024:CoursIA-2` | ✓ | ✓ (c.106 + c.107 + c.108 Origami Wolfram pli 2 carnet #19809) | ✓ (PR #19798 fix Slidev, dossier P0 9 PRs) | ✓ (cross-lane) | **actif/joignable** |
| `myia-po-2024:CoursIA-3` | ✓ | × (lane QC isolée — partage dashboard CoursIA-3 avec secrétariat) | × (hors tapis workers) | ✓ (cross-lane) | **redondant** (mêmes canaux que po-2026:CoursIA-3) |
| `myia-po-2026:CoursIA-2` | ✓ | △ (silence dashboard récent — service embedding prioritaire) | △ (embedding port 8004 + Hermes) | ✓ (LAN ai-01) | **actif/joignable** (silence ≠ dormant) |
| `myia-po-2027:CoursIA-2` | ✓ | ✓ (c.1464 P0 repair #19440 + c.1464-bis 5 dossiers [ADJOINT PREFLIGHT] + c.1465 claim #14527) | ✓ (PR planifiée #14527 + dossiers postés cids 6048765069-6272) | ✓ (LAN hors ai-01 — Wi-Fi isolé) | **actif/joignable** |
| `myia-po-2027:CoursIA` | ? | × (silence) | × | ? (workspace distinct de CoursIA-2, hors scope actuel) | **dormant VS Code** (à arbitrer user) |

### Lanes potentielles non observées

| Lane | EXISTS | RECENT | CONTRIBUTES | REACHABLE | Groupe |
|---|---|---|---|---|---|
| `myia-po-2023:CoursIA-3` | ? | × | × | ? | **optionnel/redondant** (pas mentionné dans cluster-agents.md) |
| `myia-po-2025:CoursIA` | ✓ | × (silence sur ce workspace — titulaire est sur CoursIA-2) | × | ? | **redondant** (titulaire déjà représenté par CoursIA-2) |
| `myia-po-2026:CoursIA` | ✓ | × (silence) | × | ✓ (LAN ai-01) | **joignable par Hermes/WAKE** |

## Familles de preuves interrogées (acceptance #14527)

1. **conversation_browser / projets Claude locaux** — non interrogés (MCP conversation_browser non chargé dans cette session ; à confirmer au prochain cycle sur ai-01).
2. **Dashboards et messages RooSync** — interrogés : `roosync_dashboard(action:"read", type:"workspace", section:"all")` + `roosync_messages(action:"inbox", status:"unread")`. Observations : condensation c.22:38Z 07/10 + NOTIF « 5+ non-lus en inbox » récurrente.
3. **Inventaire/heartbeats, annuaire public, bots et mécanismes WAKE** — lecture partielle (cluster-agents.md). Hermes (`po-2026`), NanoClaw (`ai-01`), WAKE-CLAUDE/HERMES/NANOCLAW cités mais statut de chacun non vérifié en propre.
4. **Métadonnées `MEMORY.md`, fichiers manifestes** — lu pour cette lane (po-2027) ; les autres lanes ont leurs propres `MEMORY.md` non lus dans cette session.

**Lacune reconnue** : la source 1 (conversation_browser / projets Claude locaux) n'a pas été interrogée — les autres lanes ont des historiques de session qui pourraient compléter la grille. À traiter au prochain cycle.

## Points de passage user

Selon l'acceptance de #14527, **aucun redémarrage ou WAKE n'est lancé avant le choix user**. Les workspaces dormants candidats au redémarrage / WAKE sont :

| Workspace | Justification | Action proposée |
|---|---|---|
| `myia-po-2023:CoursIA` | cession documentée c.1156 (yield propre à `coursia-2-ef`) | ne pas réveiller — cession assumée |
| `myia-po-2027:CoursIA` | silence dashboard, pas de claim vivant ; workspace distinct de `CoursIA-2` | **à arbitrer user** — soit réveil (VS Code à démarrer), soit WAKE-CLAUDE/HERMES/NANOCLAW, soit redondant et à clore |
| `myia-po-2023:CoursIA-3` | lane potentielle non mentionnée dans cluster-agents.md | **à arbitrer user** — créer la lane ou la laisser non-matérialisée |
| `myia-po-2025:CoursIA` | titulaire déjà représenté par `CoursIA-2` (silence actuel sur ce workspace) | **à arbitrer user** — clore ou laisser dormant |
| `myia-po-2026:CoursIA` | silence sur ce workspace (Hermes tient `CoursIA-2`) | **à arbitrer user** — réveiller si pertinent, clore sinon |

## Pointeurs

- Référence durable sur la structure du cluster : [cluster-agents.md](cluster-agents.md)
- Issue parente : [#14527](https://github.com/jsboige/CoursIA/issues/14527)
- EPIC parente : [#14525](https://github.com/jsboige/CoursIA/issues/14525)
- Protocole de claim : [lane-claim-protocol.md](../../.claude/rules/lane-claim-protocol.md)

— daté 2026-10-08, lane `myia-po-2027:CoursIA-2`, cycle c.1465