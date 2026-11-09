# Roster des identités `machine:workspace` — mesure datée (#14527)

[← Vibe-Coding](../README.md) | [← docs](.) | [Carte des espaces (#14526)](CARTE-ESPACES.md) | [Orchestration cluster](CLUSTER-ORCHESTRATION.md)

**État mesuré au 2026-10-01T16:16Z** depuis le siège `myia-po-2024:CoursIA`. Ce roster est le livrable de [#14527](https://github.com/jsboige/CoursIA/issues/14527) : il dresse la liste datée des identités `machine:workspace` du cluster par faisceau de preuves, en préalable au point de passage utilisateur de l'EPIC [#14525](https://github.com/jsboige/CoursIA/issues/14525). **Aucun redémarrage ni WAKE n'a été lancé** — la clause de l'issue l'interdit avant le choix utilisateur. Ce document ne contient aucune donnée privée : uniquement des identifiants de machines/workspaces déjà publics, des dates et des compteurs de dashboards.

## Méthode — les quatre familles de preuves

| # | Famille | Source interrogée | Ce qu'elle prouve |
|---|---|---|---|
| 1 | Projets et mémoires locaux | `~/.claude/projects/` de po-2024 (métadonnées : noms de dossiers, horodatages) + worktrees enregistrés | `EXISTS` (le workspace a une session locale), densité d'usage |
| 2 | Activité conversationnelle | répertoires projet = métadonnées de conversations (contenu non lu) | `EXISTS`, `RECENT` local |
| 3 | Dashboards et messages RooSync | `roosync_dashboard list` — 63 clés, `lastModified`/`lastModifiedBy`/volume | `RECENT` (dernière écriture datée), `CONTRIBUTES` (volume de messages) — **flotte entière vue d'un seul siège** |
| 4 | Inventaire, heartbeats, annuaire, WAKE | `roosync_inventory` (avertissement #2318 : heartbeats locaux seulement), annuaire public [CLUSTER-ORCHESTRATION](CLUSTER-ORCHESTRATION.md), mécanismes WAKE du harnais global | `REACHABLE` (mécanisme de joignabilité), limite de mesure |

**Limites de mesure, dites honnêtement** : les heartbeats RooSync ne voient que la machine qui les émet (#2318) — la joignabilité inter-machines se lit par les **effets** (écritures de dashboard datées), pas par un état direct ; les identités qui n'ont jamais écrit ne sont distinguables des machines éteintes que par leur dashboard machine (posé par autrui). `REACHABLE` est donc **probable**, jamais prouvé, sauf à lancer un WAKE — ce que la clause user interdit ici.

## 1. Groupe A — actifs / joignables (écriture < 24 h)

Preuve : dernière écriture de dashboard le 2026-10-01. C'est la photo des lanes qui produisent aujourd'hui.

| Identité | Dernière écriture (Z) | Preuves croisées |
|---|---|---|
| `myia-ai-01` : `cluster-coordination`, `CoursIA-2`(coord), `roo-extensions`, `vllm`, `qdrant`, `2025-Epita-Intelligence-Symbolique`, `cluster-soul`, `nanoclaw`(via claudish), `myia-open-webui`, 1 espace personnel hors cluster | 09:02 → 16:16 | dashboard machine `machine-myia-ai-01` actif 15:26 |
| `myia-po-2023` : `CoursIA`, `Maintenance`, `IISManagement` | 10:57 → 16:10 | machine dashboard 11:29 |
| `myia-po-2024` : `CoursIA` (+ global), `claudish`, `Argumentum` | 14:23 → 16:06 | heartbeat local 16:11, machine dashboard 10:49 |
| `myia-po-2025` : `CoursIA-2`(lane), `CoursIA-issue-debt-ledger`, `Maintenance` | 10:51 → 15:48 | adjoint actif (dossiers préflight) |
| `myia-po-2026` : `CoursIA-3`, `Embeddings`, `hermes-agent`(30/09, 1 j) | 10:53 → 15:56 | secrétariat CoursIA-3 actif |
| `myia-po-2027` : `CoursIA-2`, `Maintenance` | 10:40 → 16:16 | — |
| `myia-web1` : `roo-extensions` | 16:04 | machine dashboard vivant |

**~27 identités actives** sur 8 machines. Le cluster CoursIA (3 têtes : coordination, titulaire, secrétariat) et l'infra (claudish, vllm, qdrant) tournent sans interruption mesurée ce jour.

## 2. Groupe B — pertinents mais dormants (workspace à redémarrer si choix user)

Preuve : dashboard existant avec volume, mais aucune écriture ≥ 3 j. Une workspace utile mais dormante reste candidate (clause de l'issue).

| Identité (machine : workspace) | Dernière écriture | Pourquoi pertinente |
|---|---|---|
| `po-2025` : `2026-MSMIN5IN52-GenAI` | 2026-09-18 | **cohortes d'enseignement** (EPF/MSMIN) — saison en cours |
| `po-2025` : `2025-MSMIN5IN52-GenAI` | 2026-09-08 | idem, année N-1 (archivage à arbitrer plutôt que redémarrage) |
| `po-2025` : `2026-Epita-Programmation-par-Contraintes` | 2026-09-05 | **cohortes d'enseignement** (EPITA-IS) |
| `po-2025` : `2026-Epita-Intelligence-Symbolique` | 2026-09-05 | idem |
| `po-2026` : `Epita-IS` | 2026-06-02 | historique EPITA-IS (36 messages) — probablement clos, à arbitrer |
| `po-2024` : `roo-state-manager` | 2026-09-30 | outil critique du cluster (MCP) — 1 j de silence seulement, à surveiller plutôt qu'à redémarrer |
| `po-2024` : `postgres` | 2026-09-21 | dépendance data du cluster (18 messages, worktree dédié) |
| `po-2025` : `g1-smt`, `g1-residu-petits-domaines-a` | 2026-09-17 | grains Vibe-Coding en worktree — liés à cet EPIC |
| `ai-01` : `jsboi-mcp-servers`, `mcp-servers` | 09-16 / 06-02 | historique outillage MCP (pré-roo-state-manager) |
| `po-2026` : `vllm-watchdog` | 2026-09-13 | surveillance vLLM (le watchdog vit aussi ailleurs — chevauchement à arbitrer) |
| `ai-01` : `Safari`, `LivresAgités`(x2), 1 espace personnel hors cluster, `Musique` | 04-09 → 05-16 | espaces personnels non cluster — candidats statut « loisirs » plutôt que production |
| `ai-01` : `agent`, `coordination`, `internal` | 04-09 → 28-03 | quasi vides (0-2 messages) — probablement des tests de mécanique, à retirer ou archiver |

## 3. Groupe C — joignables par WAKE (machine probablement up, session workspace absente)

Preuve : la machine a une activité récente mesurable **ou** a été provisionnée par autrui, mais le workspace visé n'écrit plus. Mécanisme de joignabilité : `[WAKE-CLAUDE]` / override du cap 3-IDLE (harnais global, §Multi-Machine Ping-Pong), bots Hermes/NanoClaw.

| Identité | État mesuré | Voie de joignabilité |
|---|---|---|
| `myia-web2` : `Argumentum` | dernière écriture machine 2026-09-29 (2 j) — machine vivante, silence court | WAKE direct ; dashboard machine à 3,6 % = peu servi |
| `myia-po-203` / `myia-po-204` | dashboards machine **posés par po-2025:claudish le 2026-09-29** (1 message chacun), aucune écriture propre depuis | provisionnés jamais éveillés — WAKE de test nécessaire pour trancher EXISTS vivant vs VM éteinte |
| `po-2026`(ancienne clé) / `po-2023`(ancienne clé) | clés machine obsolètes (mai), jamais migrées vers `myia-*` | artefacts de renommage — cf. groupe D |

## 4. Groupe D — optionnels / redondants (avec justification)

| Clé | Justification d'exclusion |
|---|---|
| `c--dev-CoursIA-2`, `c--dev-CoursIA`, `c--dev-Argumentum`, `d--claudish` | clés de migration `C:\dev`→`D:\Dev` (2026-09-17) — doublons des clés canoniques, dont une **forkée à 108 %** de plafond (c--dev-CoursIA-2, incident connu de fusion de dashboards) |
| `workspace-""` (vide), `scrub-selftest-3584`, `d--tmp-3345-probe-repo` (local) | mécanique de test / chemin vide — aucun rôle de production |
| `livresagites` vs `LivresAgités`, `iis-management` vs `IISManagement`, `machine-po-2023` vs `machine-myia-po-2023`, `machine-po-2026` vs `machine-myia-po-2026` | doublons de casse/renommage — la clé récente fait foi |
| `workspace-roo-extensions` (attribution `myia-ai-01`:`vllm`) | attribution croisée (écrite depuis le workspace vllm) — la lane roo-extensions vit, la clé reste ambiguë |
| ~35 clés worktree `D--Dev-*-worktrees-wt-*` (po-2024) | worktrees éphémères de sessions — objets de purge (`prune_merged_worktrees.py`), jamais du roster stable |

## Décisions soumises à l'utilisateur (point de passage obligatoire)

Aucune action lancée. Quatre questions, une par groupe :

1. **Groupe A** — rien à décider (actif). Confirmer la composition de la future galerie nominative (#14529) sur ces seules identités ?
2. **Groupe B** — lesquelles des workspaces dormantes faut-il **redémarrer** (VS Code workspace à rouvrir) ? Les cohortes d'enseignement (septembre = rentrée) sont les candidates les plus urgentes ; les espaces personnels (Safari, Musique, LivresAgités) relèvent d'un choix, pas d'une urgence.
3. **Groupe C** — faut-il lancer un **WAKE de test** sur web2 et les machines provisionnées jamais éveillées (po-203/po-204) pour trancher EXISTS vivant vs éteintes ?
4. **Groupe D** — archivage des clés de migration et doublons (merge vers la clé canonique ou retrait) : à conduire maintenant ou à la vague #14528 ?

## Suivi

- Dépendance amont [#14526](https://github.com/jsboige/CoursIA/issues/14526) : CLOSE (carte livrée par #16914, #15564).
- Aval : #14528 (protocole d'invitation) démarre après le choix utilisateur — ce roster est son entrée.
- Ce document se **re-mesure** à chaque passage user (les dates du groupe A périment en 24 h).
