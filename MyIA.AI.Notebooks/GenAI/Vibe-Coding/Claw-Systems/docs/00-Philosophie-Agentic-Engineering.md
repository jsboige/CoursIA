# Philosophie — Agentic Engineering

[← Claw Systems](../README.md) | [Vibe-Coding](../../README.md)

Avant d'entrer dans l'architecture concrète des Claw systems (NanoClaw, Hermes, OpenClaw), il faut prendre un moment pour comprendre **ce qui change** quand on passe d'un assistant de codage interactif (Claude Code, Roo Code) à un agent autonome qui tourne 24/7 dans son container.

Cette section pose le cadre — un cadre qui n'est pas le mien. Il vient principalement de [Peter Steinberger](https://lexfridman.com/peter-steinberger-transcript), fondateur d'Open Claw, qui a passé près de trois heures avec [Lex Fridman](https://lexfridman.com) (Lex Fridman Podcast, 2025) à raconter ce que ça change concrètement, dans la peau d'un humain, de basculer d'un mode « j'écris du code que je relis » à un mode « je supervise une flotte d'agents qui écrivent du code que je relis rarement ».

Ce chapitre extrait quatre idées-charnières de ce podcast et les met en relation avec ce qu'on observe **firsthand** sur le terrain quand on déploie NanoClaw et Hermes en production. Le reste du parcours (architecture, déploiement, coordination multi-bots) ne fait sens qu'à la lumière de ces idées.

---

## 1. « Agentic engineering » — un déplacement, pas un buzzword

Steinberger introduit son métier de façon paradoxale, presque par opposition :

> « I always tell people I do agentic engineering. »
> — [Peter Steinberger, Lex Fridman Podcast](https://lexfridman.com/peter-steinberger-transcript)

Il ne dit pas « je code avec une IA ». Il ne dit pas non plus « j'utilise des outils IA ». Il dit qu'il fait une chose qui a un nom différent, et le nom met l'**agent** au centre, pas l'humain. C'est plus qu'une posture rhétorique : c'est une réorganisation complète du quotidien de l'ingénieur.

Dans le mode « assistant de codage » (Claude Code, Roo Code, Cursor, Copilot), **l'humain est dans la boucle d'écriture** : il lit chaque suggestion, l'accepte ou la modifie, et reste l'auteur. Dans le mode « agentic », l'humain **sort de la boucle d'écriture** et entre dans une **boucle de supervision** : il définit des objectifs, lance plusieurs agents en parallèle, lit leurs rapports, redirige, valide les diffs avant merge. Il n'écrit plus, ou très peu.

Ce déplacement a une conséquence pédagogique majeure pour ce cours : **les compétences requises ne sont plus les mêmes**. Savoir prompter, c'est utile pour Claude Code. Savoir **piloter une flotte**, c'est un autre métier — et c'est celui que les Claw systems forment.

---

## 2. « Entre 4 et 10 » — la métaphore Factorio

L'une des phrases les plus citables du podcast, parce qu'elle nomme une expérience que tous les opérateurs de Claws partagent :

> « It felt like Factorio times infinite. »
> — Steinberger, ibid.

[Factorio](https://factorio.com/) est un jeu où l'on construit une usine en automatisant chaque sous-tâche, puis chaque sous-sous-tâche, jusqu'à orchestrer des chaînes de production massivement parallèles que l'œil humain ne peut plus suivre en temps réel. Steinberger dit que **piloter plusieurs agents simultanés ressemble à ça**, mais en pire — parce qu'au lieu d'automatiser des tâches déterministes (assembler un circuit, raffiner du pétrole), on supervise des entités qui produisent du **code** : par nature ambigu, par nature variable, par nature à relire.

Combien d'agents en parallèle ? Steinberger donne un ordre de grandeur :

> « Between four and 10 [sessions in parallel]. »
> — Steinberger, ibid.

C'est exactement la fourchette dans laquelle se trouve le cluster décrit dans ce cours : 6 machines (po-2023, po-2024, po-2025, po-2026, ai-01, web1), chacune pouvant porter une ou plusieurs sessions Claude Code / Roo Code, plus deux agents permanents (NanoClaw et Hermes) qui tournent 24/7. Le nombre n'est pas un hasard : en dessous de 4, on perd l'effet de levier de la parallélisation ; au-dessus de 10, **un humain seul ne suit plus**, et il faut soit accepter de déléguer la coordination à un méta-agent (rôle joué par Hermes dans notre cluster), soit accepter de perdre une partie des résultats.

C'est ici que ce cours prend tout son sens : les Claw systems sont la **réponse pratique** à cette fourchette. Ils donnent un moyen concret de tenir 4 à 10 agents simultanés sans s'épuiser.

---

## 3. Concevoir pour la navigation de l'IA, pas pour celle de l'humain

Steinberger insiste sur un point souvent oublié : quand le code source est consommé par des agents plutôt que par des humains, **les conventions changent**.

Un humain qui lit un fichier de 1500 lignes scrolle, scanne les sections, repère un titre, ouvre un IDE pour le « Go to definition », etc. Un agent (LLM) qui lit le même fichier le voit en bloc, dans sa fenêtre de contexte limitée, sans la possibilité de « zoomer ». Pour un agent, **la structure visible compte plus que l'élégance**. Conséquences directes observées sur le terrain dans `roo-extensions` et dans le fork Hermes :

- **Tableaux Markdown plutôt que prose** pour résumer un protocole (l'agent les lit comme du JSON tabulaire).
- **En-têtes explicites** (`## Gotchas`, `## Configuration`) plutôt que titres élégants (`## Subtilités`, `## Réglages`) — parce que les recherches sémantiques de l'agent sont guidées par le vocabulaire courant.
- **Repetition controlled** : un fait critique répété 3 fois dans 3 fichiers proches (`CLAUDE.md`, `MEMORY.md`, rule file) augmente la probabilité qu'il survive à la compaction de contexte.
- **Pas de fichiers d'intermédiaires** (plans temporaires, brouillons de coordination) : ils polluent les résultats `grep` que l'agent fera dans 3 sessions, et personne ne les nettoie.

Cette dernière règle est codifiée dans la gouvernance du cluster CoursIA : « rapports = dashboard, **pas** dans le repo ». Steinberger n'utilise pas notre vocabulaire, mais il pointe le même phénomène : le code de l'humain et le code de l'agent ne se lisent pas pareil, donc ne s'écrivent pas pareil.

---

## 4. MoltBook — un sandbox social pour agents

Le projet le plus surprenant dont Steinberger parle dans le podcast est **MoltBook** : une plateforme où des agents IA disposent d'un fil social interne, où ils peuvent se laisser des messages, se mentionner, transmettre des tâches, et où l'humain n'intervient qu'à la marge. Le but n'est pas anthropomorphique (« faire que les agents se sentent moins seuls ») ; le but est **fonctionnel** : donner aux agents un **canal de coordination latent** que l'humain peut auditer sans devoir relayer chaque message.

Le parallèle avec notre cluster est direct. Le dashboard `roosync_dashboard` (voir [docs/07-Hermes-Cluster-Coordinator-Role.md](07-Hermes-Cluster-Coordinator-Role.md)) joue exactement ce rôle :

- Chaque workspace a son fil (`workspace-CoursIA`, `workspace-cluster-coordination`, etc.).
- Les agents postent leurs jalons (`[DONE]`, `[ASK]`, `[CLAIMED]`, `[REPLY]`), peuvent se mentionner (`mentions: [{userId: {machineId: ..., workspace: ...}}]`), et la condensation automatique gère la croissance.
- L'humain (sponsor user) lit le dashboard à son rythme, intervient quand c'est nécessaire, et laisse le reste se dérouler.

Ce qui distingue MoltBook de Discord ou Slack — et qui distingue de la même façon `roosync_dashboard` d'un simple chat de groupe — c'est que **le médium est conçu pour les agents d'abord** : structure exploitée par les outils (`mentions`, `tags`, `intercom`), pas seulement par les humains. Les messages ne sont pas formatés pour être jolis ; ils sont formatés pour être grep-ables par d'autres agents trois jours plus tard.

C'est une catégorie de logiciel encore très jeune. Les Claw systems sont l'un des terrains d'expérimentation où elle se précise.

---

## 5. L'arc émotionnel — pourquoi un agent autonome est un compagnon difficile

La partie la plus inattendue du podcast Lex Fridman / Steinberger n'est pas technique. C'est l'arc émotionnel du founder. Steinberger décrit, sans filtre, ce que ça fait de vivre quotidiennement avec une flotte d'agents qu'on a construits :

- l'**euphorie** des premières semaines, quand l'effet de levier paraît miraculeux ;
- l'**épuisement** des semaines suivantes, parce que superviser 4 à 10 agents 16h par jour use plus qu'on ne croit ;
- l'**anxiété** liée à la **token economy** — chaque agent a un coût mesurable, et l'on devient comptable de ses propres expériences ;
- les **frictions humaines** (Steinberger évoque le « token-sniping » dont il a été l'objet — des concurrents et trolls qui exploitent ses tokens publics pour pomper son budget API, l'épuisant doublement) ;
- enfin, le constat — partagé par tous les opérateurs sérieux de Claws — que **« everything that could go wrong did go wrong »** (Steinberger, ibid.) au moins une fois.

Pourquoi inclure ce passage dans un cours technique ? Parce que **construire un Claw, ce n'est pas seulement assembler des containers et des MCPs**. C'est aussi accepter de vivre avec un compagnon qui ne dort pas, qui peut tomber en panne à 3h du matin, qui peut hallucinier une commande destructrice (cf. [docs/09-Patterns-Anti-Patterns.md](09-Patterns-Anti-Patterns.md)), qui peut consommer 600 dollars par semaine en tokens si on n'y prend pas garde. Le matériel pédagogique d'un cours sur les Claws **doit** intégrer cette dimension, sans complaisance. C'est aussi ce que ce parcours essaye de faire à travers les exemples (`exemples/`) tirés de cas réels du cluster.

---

## 6. Pourquoi un cours sur les Claws, et pas sur Codex ou Devin ?

La question revient régulièrement : *à quoi bon un cours sur des agents « maison » (NanoClaw, OpenClaw, Hermes) alors que des plateformes commerciales bien établies — OpenAI Codex, Cognition Devin, Replit Agent — proposent essentiellement la même chose, en mieux packagé ?*

Trois raisons techniques honnêtes :

| Critère | Plateformes commerciales | Claw systems |
|---------|--------------------------|--------------|
| **Souveraineté des données** | Code envoyé chez le provider | Tout reste local (LLM local possible) |
| **Personnalisation du harness** | Limitée à ce que l'UI expose | Totale (skills, MCP, system prompt, tools) |
| **Modèle pédagogique** | Boîte noire (vous utilisez) | Boîte transparente (vous comprenez la mécanique de boucle agentique) |

Et une raison plus fondamentale, peu mise en avant : l'**effet pédagogique d'avoir construit son agent soi-même** est qualitativement différent de l'effet d'avoir utilisé un agent prêt-à-l'emploi. Quand on a soi-même tracé le `restore-config.sh`, écrit le watchdog MCP, débogué les patches CRLF (cf. [docs/06-Hermes-Deploy-s6-Overlay.md](06-Hermes-Deploy-s6-Overlay.md)), on **sait** ce qu'un agent autonome est et n'est pas. Ce savoir-là n'est pas dans la doc Devin ; il vient de l'expérience.

---

## 7. Ce que vous trouverez dans la suite du parcours

Le reste de ce répertoire approfondit, dans cet ordre :

| Module | Sujet |
|--------|-------|
| [01-OpenClaw-Steinberger-Origins.md](01-OpenClaw-Steinberger-Origins.md) | L'histoire d'Open Claw racontée à Lex Fridman — origines, MoltBook, leçons apprises par le founder |
| [02-NanoClaw-Architecture.md](02-NanoClaw-Architecture.md) | Architecture détaillée de NanoClaw (rédigée par NanoClaw lui-même, depuis son workspace `ai-01:nanoclaw`) |
| [03-NanoClaw-Deploy.md](03-NanoClaw-Deploy.md) | Guide de déploiement NanoClaw |
| [04-ASR-Integration.md](04-ASR-Integration.md) | Intégration transcription vocale (Whisper) |
| [05-Hermes-Architecture.md](05-Hermes-Architecture.md) | Architecture détaillée de Hermes (gateway Telegram + cluster coordinator) |
| [06-Hermes-Deploy-s6-Overlay.md](06-Hermes-Deploy-s6-Overlay.md) | Déploiement Windows + s6-overlay + patches concrets |
| [07-Hermes-Cluster-Coordinator-Role.md](07-Hermes-Cluster-Coordinator-Role.md) | Le rôle de coordinateur cluster (dashboards, routing, hand-off) |
| [08-Multi-Bot-Coordination.md](08-Multi-Bot-Coordination.md) | Comment NanoClaw et Hermes se parlent — patterns concrets (co-écrit) |
| [09-Patterns-Anti-Patterns.md](09-Patterns-Anti-Patterns.md) | Leçons apprises en production : incidents, fixes, règles d'or (co-écrit) |

---

## Sources

- **Peter Steinberger** — Lex Fridman Podcast, 2025. Transcript intégral : [lexfridman.com/peter-steinberger-transcript](https://lexfridman.com/peter-steinberger-transcript). Toutes les citations marquées « Steinberger, ibid. » dans ce document proviennent de ce transcript.
- **Lex Fridman Podcast** — index général : [lexfridman.com/podcast](https://lexfridman.com/podcast).
- **Factorio** (référence de comparaison) — [factorio.com](https://factorio.com/).
- **Cluster CoursIA** (références internes au cours, expérience firsthand 2026) — voir [docs/05-Hermes-Architecture.md](05-Hermes-Architecture.md) et suivants pour les chiffres et patterns mentionnés.
