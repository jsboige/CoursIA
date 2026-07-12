# Orchestration et tâches planifiées avec Open WebUI v0.9.0

> Référentiel fonctionnel pour la série **GenAI / Texte**. Compare les trois piliers
> d'orchestration apportés par Open WebUI (OWUI) v0.9.0 — Automations planifiées,
> Task Management, Calendar — aux deux frameworks de référence côté code, **LangChain /
> LangGraph** et **CrewAI**. Objectif pédagogique : aider l'étudiant à **choisir son
> niveau d'abstraction** (produit GUI self-hosté vs librairie vs framework multi-agents)
> selon le besoin.
>
> Voir aussi : la série [`GenAI/Open-WebUI/Playwright-OWUI`](../../MyIA.AI.Notebooks/GenAI/Open-WebUI/Playwright-OWUI/README.md)
> couvre OWUI sous l'angle **tests E2E** (Playwright). Ce document est le référentiel
> **orchestration** ; il n'en duplique pas le contenu test.

**Fiabilité des sources.** Les capacités OWUI ci-dessous sont **vérifiées** contre les
sources officielles (tag de release GitHub, `docs.openwebui.com`, DeepWiki) — chaque
ligne cite sa source. Les lignes comparatives LangChain / CrewAI sont ancrées sur la
documentation de ces projets ; les points non confirmés par une source fraîche sont
explicitement marqués **« à vérifier »** plutôt qu'affirmés.

---

## 1. Positionnement du problème

Orchestrer des LLM (planifier des exécutions, décomposer une tâche complexe, suivre un
état) peut se faire à **trois niveaux d'abstraction** très différents :

| Philosophie | Exemple | Ce qu'écrit l'utilisateur |
|---|---|---|
| **Produit GUI self-hosté** | Open WebUI | Rien (formulaires + prompts en langage naturel) |
| **Librairie / framework de graphes** | LangChain / LangGraph | Du code (chaînes, agents, graphes d'états) |
| **Framework multi-agents par rôles** | CrewAI | Du code (Agents role/goal, Tasks, Crew) |

OWUI v0.9.0 fait passer le **produit** d'un simple front de chat à une plateforme
d'orchestration : on peut désormais y planifier des prompts, donner à un modèle une
structure de suivi de tâches, et tenir un calendrier — **sans écrire de code**.

---

## 2. Les trois piliers d'orchestration d'OWUI v0.9.0

### 2.1 Scheduled Automations (axe temporel)

Une *automation* planifie un prompt qui s'exécute automatiquement. Chaque exécution
**crée un chat** et passe par le pipeline `chat_completion` normal — donc les mêmes
filtres, outils et modèle qu'un chat lancé à la main.

- **Pas de cron.** La planification utilise des intervalles prédéfinis
  (Once / Hourly / Daily / Weekly / Monthly) ou la syntaxe **RRULE** (iCalendar).
- **Pilotable depuis le chat.** En mode *Native Function Calling*, le modèle gère ses
  propres automations via les outils `create_automation`, `update_automation`,
  `list_automations`, `toggle_automation`, `delete_automation`.
- **Limites configurables** par l'administrateur sur la planification.

Sources : [docs Automations](https://docs.openwebui.com/features/chat-conversations/chat-features/automations/) ·
[release v0.9.0](https://github.com/open-webui/open-webui/releases/tag/v0.9.0)

### 2.2 Task Management (axe structurel / agentique)

Outil **chat-time** : il donne à un modèle agent une structure pour **planifier et
suivre un travail multi-étapes** — une liste de tâches vivante avec des statuts
explicites (créer / mettre à jour / suivre, statut temps réel).

À ne pas confondre avec les Automations : Task Management est **structurel** (décomposer
un travail en sous-tâches suivies), les Automations sont **temporelles** (déclencher une
exécution à une date). Les deux sont complémentaires.

Source : [docs Task Management](https://docs.openwebui.com/features/chat-conversations/chat-features/task-management/)

### 2.3 Calendar + overlay des tâches planifiées

OWUI v0.9.0 ajoute un **espace calendrier** complet : vues jour / semaine / mois,
création / modification d'événements (manuelle ou assistée par l'IA en langage naturel),
invitations avec suivi de statut, récurrences, et alertes (toasts in-app, pop-ups
navigateur, **webhooks** personnalisés).

Par-dessus, un **« Scheduled Tasks calendar »** : un calendrier **virtuel, en lecture
seule, non persisté en base**, synthétisé au moment de la réponse API. Il projette les
exécutions d'automations à venir et relie chaque run passé à son log de chat. C'est une
distinction pédagogique forte : **événement réel persisté** vs **projection runtime**.

Sources : [docs Calendar](https://docs.openwebui.com/features/calendar/) ·
[DeepWiki Automations & Calendar](https://deepwiki.com/open-webui/open-webui/20-automations-and-calendar)

---

## 3. Sous le capot : comment OWUI exécute une automation

Détail d'architecture utile à montrer en cours (le « produit » repose sur des patterns
classiques de backend) :

- Un unique process d'arrière-plan `scheduler_worker_loop` (sur le backend FastAPI)
  gère **à la fois** l'exécution des automations dues **et** la dispatch des alertes
  calendrier.
- Pour exécuter une automation, il construit une *mock* `Request` ASGI
  (`_build_request`) afin d'invoquer le pipeline interne `chat_completion` — d'où le fait
  qu'un run est un **vrai chat**, traçable, soumis aux mêmes filtres/outils.
- Les runs sont journalisés dans la table `automation_run` (statut success/error + `chat_id`).
- Les alertes calendrier utilisent `CALENDAR_ALERT_LOOKAHEAD_MINUTES` + Socket.IO pour
  les notifications temps réel.

Source : [DeepWiki Automations & Calendar](https://deepwiki.com/open-webui/open-webui/20-automations-and-calendar)

---

## 4. Migration 0.8.x → 0.9.0 : le passage en asynchrone (breaking change)

v0.9.0 marque la couche base de données comme **asynchrone** pour éviter de bloquer
l'event loop (ce qui tuerait la concurrence). Concrètement, les extensions
(Tools / Functions / Pipes / Filters / Actions) gardent leurs signatures mais doivent
devenir asynchrones :

- handlers en `async def`, `await` sur tout accès DB ;
- SQLAlchemy 2.0 : `select()` + `AsyncSession` (au lieu de `Session` + `query()`) ;
- driver async (`aiosqlite` / `asyncpg`) ;
- `anyio.to_thread.run_sync(...)` pour envelopper les librairies bloquantes restantes.

Deux autres changements notables de v0.9.0 : le *passthrough* OpenAI devient **opt-in**
(plus actif par défaut), et le timeout des serveurs d'outils **MCP** devient configurable.

Sources : [guide de migration 0.9.0](https://docs.openwebui.com/features/extensibility/plugin/migration/to-0.9.0/) ·
[release v0.9.0](https://github.com/open-webui/open-webui/releases/tag/v0.9.0)

---

## 5. Comparatif : OWUI vs LangChain / LangGraph vs CrewAI

| Axe | **OWUI v0.9.0** | **LangChain / LangGraph** | **CrewAI** |
|---|---|---|---|
| **Modèle d'orchestration** | Produit GUI + outils chat : Automations (chat-completion planifié) + Task Management (liste de tâches agentique). Aucun code côté utilisateur. | Librairie : chaînes/agents (LangChain) + **graphes d'états cycliques** (LangGraph). Code développeur. | Framework **multi-agents par rôles** : Agents (role/goal/backstory), Tasks, Crew, Flows. Code Python. |
| **Planification (scheduling)** | **Natif** : Automations RRULE/intervalles (**pas de cron**). Outils chat `create_automation`, etc. | **Aucun scheduler natif** — à apporter en externe (cron, Temporal, Celery). | **Pas de scheduler cron natif** *(à vérifier)* — scheduling généralement délégué au cron OS/cloud ; les Flows orchestrent mais ne sont pas un calendrier. |
| **Persistance d'état** | Automations persistées + table `automation_run` (statut + `chat_id`) ; Task Management = liste vivante **dans la session de chat** ; overlay calendrier **virtuel/runtime, non persisté**. | LangGraph : **checkpointing** (état de graphe persistant) + abstractions mémoire LangChain. | Module **mémoire** (court/long terme) ; état surtout **intra-run**. |
| **Facilité pour étudiants** | **Très haute** : zéro code, GUI, prompts en langage naturel. Idéal en introduction. | **Moyenne à raide** : nombreuses abstractions (chains, agents, retrievers, graphes), orienté code. | **Moyenne** : Python lisible, mais la conception par rôles ajoute une charge conceptuelle. |
| **Auto-hébergeable** | **Oui, produit clé en main** (Docker `ghcr.io/open-webui/open-webui`). | **Librairie** : on héberge sa propre application (pas un produit). Exécutable partout. | **OSS exécutable partout** (framework) ; existe aussi en offre cloud commerciale. |

Sources des lignes LangChain / CrewAI :
[LangGraph vs Temporal (langchain.com)](https://www.langchain.com/resources/langgraph-vs-temporal) ·
[CrewAI Flows](https://docs.crewai.com/en/concepts/flows). Les cellules **« à vérifier »**
(notamment l'absence de scheduler cron natif chez CrewAI, déduite de l'existence de
tutoriels externes « comment scheduler un agent CrewAI » plutôt que d'une fonctionnalité
produit documentée) restent à confirmer avant d'en faire un point d'évaluation.

**Lecture pédagogique.** Le bon choix dépend du besoin :

- **Chatbot avec tâches récurrentes, déployé pour des non-développeurs** → OWUI (zéro code,
  scheduling natif).
- **Pipeline RAG / workflow conditionnel à état** → LangChain / LangGraph (contrôle fin,
  checkpointing).
- **Équipe d'agents spécialisés collaborant sur un livrable** → CrewAI (rôles, délégation).

---

## 6. Exercices proposés (≥ 3, convention 3-exercices/notebook)

Ces exercices supposent l'accès à l'instance OWUI de cours référencée par
`MyIA.AI.Notebooks/GenAI/Open-WebUI/Playwright-OWUI/.env` (`OWUI_URL`). Ils restent des **stubs**
(objectif + indices), à compléter par l'étudiant.

1. **Automation RRULE.** Créer une automation « résume mes notes chaque matin » via une
   règle RRULE, déclencher un run, et retrouver le `chat_id` du run dans le log.
   *Indice : observer la différence entre l'intervalle prédéfini et la RRULE équivalente.*
2. **Décomposition de tâche.** Donner une même tâche complexe (a) via un prompt naïf,
   (b) en activant Task Management ; comparer la traçabilité des sous-étapes et des statuts.
3. **(Ouvert) Choix d'architecture.** Pour un use-case donné, argumenter par écrit le
   choix OWUI vs LangGraph vs CrewAI en s'appuyant sur le tableau §5 (livrable = note
   justifiée, pas de code requis).

---

## Annexe — note de version (à réconcilier)

La source canonique (le **tag de release GitHub `v0.9.0`**) attribue **Automations,
Task Management, Calendar et Desktop App à la version v0.9.0**. Le README de la série
`GenAI/Open-WebUI/Playwright-OWUI` (validé contre une instance **v0.9.1**) parle de « v0.9.1 ajoute
Calendar, Automations, Desktop app ». Ces fonctionnalités ont été **introduites en
v0.9.0** et **persistent** en v0.9.1 ; la formulation « ajoute » du README est imprécise.
Réconciliation à faire dans une PR distincte sur la série Playwright-OWUI (sujet séparé).
