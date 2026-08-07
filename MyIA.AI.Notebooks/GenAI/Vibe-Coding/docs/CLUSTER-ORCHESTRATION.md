# Orchestration Cluster — le vibe-coding à l'échelle d'une flotte

[← Vibe-Coding](../README.md) | [↑ docs](.) | [Topologie cluster](../../../../docs/reference/cluster-agents.md) | [Architecture MCP](../../../../docs/reference/architecture_mcp_roo.md)

Les ateliers [Claude Code](../Claude-Code/README.md) et [Roo Code](../Roo-Code/README.md) présentent le vibe-coding **à l'échelle d'une session** : un développeur, un IDE, un assistant qui écrit du code à la demande. Les [Claw Systems](../Claw-Systems/README.md) montrent des agents autonomes en conteneurs. Cette section documente la pièce la plus originale — et la moins visible — du harnais réellement utilisé pour produire ce dépôt : **l'orchestration d'une flotte d'agents de codage répartis sur plusieurs machines**, qui coordonnent leur travail, partagent une mémoire, et livrent du code sans intervention humaine continue.

Concrètement : la plupart des notebooks, preuves Lean, stratégies QuantConnect et corrections de ce dépôt ne sont pas écrits par un humain dans un IDE. Ils sont produits par un **cluster d'agents** (un coordinateur + plusieurs workers) qui tournent en cycles, se répartissent les tâches via des tableaux de bord partagés, et s'auto-alimentent dans un pool de tâches commun. C'est le vibe-coding poussé jusqu'à sa logique d'agentic engineering décrite par [Peter Steinberger](../Claw-Systems/docs/00-Philosophie-Agentic-Engineering.md) — non plus « je supervise un agent », mais « je supervise une flotte ».

## Pourquoi une section orchestration ?

| Aspect | Vibe-coding de session (Claude/Roo) | Orchestration cluster (cette section) |
|--------|-------------------------------------|----------------------------------------|
| **Échelle** | Un agent, une session, un humain présent | Une flotte d'agents, cycles persistants, humain distancié |
| **Mémoire** | Contexte de la session (volatile) | Mémoire sémantique persistante (Qdrant) + dashboards |
| **Coordination** | Aucune (agent unique) | Tableaux de bord partagés + messagerie inter-agents |
| **Répartition du travail** | L'humain donne la tâche | Les agents piochent dans un pool commun, se répartissent |
| **Vérification** | L'humain relit chaque sortie | Règles auto-chargées + relecture croisée agent ↔ agent |
| **Livrable** | Du code dans un fichier | Une PR mergée, sans action humaine directe |

Le saut n'est pas anecdotique. Passer d'un agent à une flotte change les problèmes : comment deux agents évitent-ils de travailler sur le même fichier ? comment un agent sait-il ce que les autres ont fait ? comment s'assurer qu'un agent n'affirme pas « fait » sans avoir vérifié ? Le harnais ci-dessous répond à ces questions avec un protocole de coordination explicite, pas avec de la confiance.

### Situation dans le parcours

Un atelier « découverte Claude Code » (module 01) apprend à démarrer une session, écrire un `CLAUDE.md`, utiliser les `@`-mentions. Le module 05 (Automatisation avancée) introduit skills, subagents et MCP **génériques** du marché. Cette section montre la **même composition poussée à l'échelle d'un cluster** : les `CLAUDE.md` deviennent un harnais de règles auto-chargées, les MCP génériques sont complétés par des MCP maison spécialisés, et la session unique devient un cycle coordonné parmi des dizaines. C'est le prolongement naturel des ateliers quand on veut automatiser non plus une tâche, mais tout un pipeline de développement continu.

## La brique centrale : `roo-state-manager` (RooSync)

`roo-state-manager` est un serveur MCP maison ([roo-extensions](https://github.com/jsboige/roo-extensions)) qui expose une trentaine d'outils de coordination. C'est le **système nerveux** du cluster : tout agent qui s'y connecte peut lire l'état de la flotte, poster son avancement, chercher dans l'historique des conversations, et synchroniser sa configuration. Les outils se regroupent en cinq familles :

| Famille | Outils représentatifs | Rôle |
|---------|----------------------|------|
| **Dashboards** | `roosync_dashboard` | Trois tableaux de bord partagés — `global` (cluster), `machine` (un nœud), `workspace` (un projet) — où chaque agent poste début/livraison/fin de cycle. Canal principal de coordination ; auto-condensation à 92 % pour ne pas croître indéfiniment. |
| **Messagerie** | `roosync_messages` | Messages directs inter-machines (dispatch, ACK, escalade). Le canal de décision : survit à la condensation du dashboard, là où un simple « post » serait perdu. |
| **Mémoire conversationnelle** | `conversation_browser` | Navigation dans l'historique des sessions (`list` → `view`/`tree`/`summarize`). Un agent reprend le travail d'un autre en lisant sa trace, pas en devinant. |
| **Recherche sémantique** | `codebase_search`, `roosync_search` | Indexation Qdrant du code et des conversations. La « mémoire long-terme » : retrouver qu'un problème a déjà été résolu, et comment. |
| **Inventaire & config** | `roosync_inventory`, `roosync_config`, `roosync_baseline` | État du cluster (machines, GPUs, heartbeats) et synchronisation de configuration entre nœuds. |

Le principe directeur : **aucune mémoire n'est implicite**. Un agent qui démarre un cycle lit d'abord le dashboard (`section:"all"`) et sa boîte de messages, reconstruit l'état à partir de ces sources persistantes, puis agit. Ce qui n'est pas écrit dans le dashboard ou un fichier ne compte pas — le contexte de session est volatile et sera résumé puis perdu.

## Les MCPs maison spécialisés

Les ateliers Claude Code / Roo Code introduisent les MCP (Model Context Protocol) avec des serveurs **génériques** du marché — recherche web, automation navigateur, gestion de dépôt. C'est nécessaire pour démarrer, mais ça laisse dans l'ombre la partie la plus originale : **nos propres serveurs MCP**, écrits (dans [roo-extensions](https://github.com/jsboige/roo-extensions)) pour les besoins spécifiques du cluster. Autour de `roo-state-manager`, ces serveurs maison donnent aux agents des capacités concrètes au-delà du code :

| MCP | Capacité apportée (exemple d'usage réel dans ce dépôt) | Documentation pérenne |
|-----|--------------------------------------------------------|----------------------|
| **jupyter-papermill** | Exécuter des notebooks Jupyter (cycle de vie kernel complet) ; re-exécuter un notebook modifié et capturer ses sorties avant commit (règle C.2) | [kernels-runtime.md](../../../../docs/reference/kernels-runtime.md) |
| **qc-mcp-lite** | Pilote QuantConnect Cloud (compile, backtest, lecture résultats) ; lire Sharpe/CAGR/MaxDD et les reporter dans le commit | [quantconnect.md](../../../../docs/qc/quantconnect.md) |
| **sk-agent** | Vision + multi-agent (analyse d'images, agents spécialisés) ; audit visuel de galeries de figures README | [common-commands.md](../../../../docs/reference/common-commands.md) |
| **searxng** | Recherche web (SearXNG) ; veille techno, vérification de versions de librairies | [common-commands.md](../../../../docs/reference/common-commands.md) |
| **markitdown** | Conversion PDF/DOCX → Markdown ; extraction de contenu de slides ou de documents pédagogiques | [common-commands.md](../../../../docs/reference/common-commands.md) |
| **playwright** | Automation web (navigateur headless) ; exécution de quantbooks QC Cloud en fallback, tests E2E | [common-commands.md](../../../../docs/reference/common-commands.md) |

Ces serveurs tournent en `stdio` et sont gérés par le client MCP (cycle de vie, restart au changement de fichier source). Le diagnostic de leur démarrage est documenté dans [Architecture MCP](../../../../docs/reference/architecture_mcp_roo.md). L'intérêt pédagogique : chacun est un **vrai outil SOTA branché**, pas une simulation — un agent qui en a besoin l'invoque réellement, obtient sa vraie sortie, et la commet.

Ces serveurs sont déclarés dans `.mcp.json` (configuration de projet) et `~/.claude.json` (configuration globale). **Aucun secret n'est committé** : les jetons vivent dans `.secrets/master.env` (gitignoré), source unique propagée vers les `.env` consommateurs par [`scripts/secrets/render_envs.py`](../../../../scripts/secrets/render_envs.py) (cf. [secrets-management.md](../../../../docs/genai/secrets-management.md)). Cette discipline — secrets hors-du-repo, jamais de littéral inline — est l'un des garde-fous les plus répétés du harnais.

## Le pattern coordinateur / workers

La flotte adopte une topologie à deux rôles (détails complets dans [Topologie cluster](../../../../docs/reference/cluster-agents.md)) :

```text
                     ┌─────────────────────────────┐
                     │   ai-01  (coordinateur)     │
                     │   - lit les 2 dashboards    │
                     │   - merge les PR propres    │
                     │   - dispatche par DM        │
                     │   - tranche les arbitrages  │
                     └──────────────┬──────────────┘
                                    │  DM (dispatch / ACK / steer)
               ┌────────────────────┼────────────────────┐
               │                    │                    │
       ┌───────▼──────┐     ┌───────▼──────┐     ┌───────▼──────┐
       │  po-2023     │     │  po-2024     │     │  po-2026     │  ...
       │  (worker)    │     │  (worker)    │     │  (worker)    │
       │  GenAI/audio │     │  QC/ML train │     │  Lean/Mathlib│
       └──────────────┘     └──────────────┘     └──────────────┘
               │                    │                    │
               └────────────────────┴────────────────────┘
                                    │
                          pool commun : gh issue list --state open
```

- **`ai-01` (coordinateur)** : ne produit peu de code lui-même. Il lit l'état des deux lanes (`workspace-CoursIA`, `workspace-CoursIA-2`), merge les PR propres et approuvées (via bascule de compte GitHub), dispatche les tâches par message direct, et tranche les arbitrages de design. Un cycle `/coordinate` typique : lire → merger ce qui est mûr → dispatcher un grain vérifié firsthand → acker les bloqueurs.
- **`po-*` (workers)** : chacun spécialisé par famille (GenAI, QuantConnect/ML, Lean, etc.) mais le pool de travail est **commun et cross-lane**. Un worker se réveille sur un cycle `/continue`, lit le dashboard + sa boîte DM, pioche une tâche, livre une PR atomique, rapporte, puis re-pioche. Une lane est une étiquette de *reporting*, pas une frontière de travail.

### Anatomie d'un cycle worker (`/continue`)

Un worker ne dépend d'aucun état en mémoire vive — tout est reconstruit depuis des sources persistantes :

1. **Contexte** : lire `MEMORY.md`, `git pull --ff-only`, vérifier l'arbre partagé (worktree isolé si sale).
2. **Tour de coordination** : boîte de messages (`inbox status:unread`) **en premier**, puis dashboard (`section:"all"`). Les missions du coordinateur priment sur le travail local.
3. **Choix de la tâche** : P0 mission coord > P1 travail en cours > P2 pool global (`gh issue list --state open`). `[CLAIMED]` sur le dashboard **avant** de commencer (anti-double-claim).
4. **Livraison** : une PR = un sujet atomique. Commit + PR **avant** le rapport.
5. **Fin** : `[DONE]` lane-specific sur le dashboard. Une PR livrée ne clôt pas la session : on re-pioche aussitôt.

Le point clé : ce protocole est **auto-alimenté**. Un worker qui se réveille sans directive ne s'arrête pas — il pioche dans le pool et produit quand même. « Rien à faire » alors que `gh issue list` renvoie des dizaines d'issues est traité comme un échec de méthode, pas un état légitime.

## Les garde-fous : règles auto-chargées et relecture croisée

Une flotte sans discipline produit du travail à grande échelle… et des régressions à grande échelle. Le harnais encode ses garde-fous dans des **règles markdown auto-chargées** à chaque session (`.claude/rules/*.md` + `CLAUDE.md`), pas dans la bonne volonté de l'agent. Quelques exemples concrets tirés du harnais réel :

- **Anti-régression** : remplacer une preuve formelle ou une implémentation par `sorry` / stub vide sous prétexte de « fix compilation » est interdit sans diagnostic écrit (incident fondateur : 9 preuves Lean remplacées par `sorry` en un commit).
- **Validation réelle, pas de complaisance** : un notebook est commis *avec* ses sorties exécutées ; « DONE » sans preuve post-fix relancée est un manquement. Un verdict « BEATS » sans multi-seed (≥4) est invalide.
- **Stop & Repair** : on ne maquille jamais une sortie de cellule (chemin machine, préfixe de clé) — on répare la cause et on ré-exécute.
- **Relecture croisée agent ↔ agent** : un coordinateur ne merge pas sur le titre seul. Il lit le diff, vérifie un claim par PR, et les bots reviewers postent `CHANGES_REQUESTED` sur les PRs composites ou dégénérées.

Cette discipline est aussi importante que les outils : c'est elle qui distingue une flotte qui produit du travail vérifiable d'un essaim qui génère du faux-semblant à grande échelle.

## Aller plus loin (doc pérenne)

Cette section est une **introduction pédagogique**. Pour le détail technique, ces documents sont la source autoritaire :

- [Topologie cluster](../../../../docs/reference/cluster-agents.md) — machines, GPUs, spécialisations par famille, dispatch par Epic GitHub.
- [Architecture MCP](../../../../docs/reference/architecture_mcp_roo.md) — cycle de vie des serveurs MCP `stdio`, diagnostic, restart.
- [Sous-agents & skills](../../../../docs/reference/subagents-reference.md) — catalogue des agents spécialistes et skills invoquables.
- [CLAUDE.md](../../../../CLAUDE.md) + [.claude/rules/](../../../../.claude/rules/) — les règles auto-chargées (anti-régression, validation, vigilance anti-complaisance).

Le code source des MCPs maison vit dans le dépôt dédié [roo-extensions](https://github.com/jsboige/roo-extensions).

---

*Section ajoutée pour présenter fidèlement le harnais de production réel (See #9735). Cette version consolide et remplace la proposition `NOTRE-STACK.md` de #9741 (framing générique-vs-maison, progression pédagogique modules 01→05→cluster, pointeur secrets-management) — voir #9741 pour la source absorbée (Consolider ≠ Archiver : les deltas uniques sont fusionnés ici avec citation, #9741 fermé en superseded). Les role-labels de machines (ai-01, po-*) sont publics dans cluster-agents.md ; aucun hostname sensible, token ou secret n'apparaît ici.*
