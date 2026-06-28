# Open Claw — origines, MoltBook, le founder

[← Philosophie Agentic Engineering](00-Philosophie-Agentic-Engineering.md) | [→ Architecture NanoClaw](02-NanoClaw-Architecture.md) | [← Claw Systems](../README.md)

Le chapitre précédent a posé les idées-charnières du « turning into an agentic engineer ». Ce chapitre raconte **d'où elles viennent**. Il suit le récit que [Peter Steinberger](https://lexfridman.com/peter-steinberger-transcript) a fait à Lex Fridman — un récit que l'on peut résumer comme une **conversion technique et personnelle**, mais qui se laisse aussi lire comme un avertissement.

Tout ce qui suit est puisé dans le transcript du Lex Fridman Podcast (2025, [lien intégral](https://lexfridman.com/peter-steinberger-transcript)). Quand on cite Steinberger verbatim, c'est marqué « Steinberger, ibid. » Quand on paraphrase, c'est indiqué par le contexte.

---

## 1. Avant Open Claw — le développeur iOS qui s'ennuyait

Steinberger est connu, avant Open Claw, comme l'auteur de **PSPDFKit**, un SDK PDF iOS utilisé dans des dizaines de millions d'apps (Dropbox, IBM, Apple lui-même). C'est un développeur classique, en surface : il connaît son métier, il a vendu sa boîte, il est confortable. C'est précisément ce confort qui devient le problème.

Le déclic n'est pas un déclic technique. C'est un **ennui**. Steinberger raconte avoir senti que le métier d'ingénieur logiciel traditionnel — écrire du code, l'instrumenter, le maintenir — était en train de devenir un acte de plus en plus mécanique au regard de ce qu'un LLM pouvait produire. Pas en termes de qualité immédiate (un LLM en 2024 ne remplaçait pas un senior iOS), mais en termes de **trajectoire**.

> Sa conviction (paraphrase) : si l'on **continue à écrire chaque ligne soi-même** pendant que la machine apprend à le faire trois fois plus vite, on choisit de rester du mauvais côté de la courbe d'apprentissage.

C'est cette conviction-là qui pousse Steinberger à **sortir de son confort**, à arrêter le développement iOS classique pendant plusieurs mois, et à investir tout son temps dans la construction d'un **harness** capable de tirer parti des LLMs comme **producteurs principaux** de code, et non comme assistants.

Pour un cours, c'est utile de garder ce premier moment en tête : **la motivation initiale est défensive autant qu'offensive**. Steinberger ne construit pas Open Claw parce qu'il croit qu'il va devenir riche en faisant ça (il l'est déjà). Il le construit parce qu'il croit que ne pas le faire reviendrait à choisir la stagnation.

---

## 2. Le harness — qu'est-ce qu'on appelle « Open Claw » exactement ?

Le terme « Open Claw » est parfois confus, parce qu'il désigne **plusieurs choses superposées**. Steinberger le clarifie au fil du podcast. Pour notre cours, il est utile de distinguer trois couches :

1. **Le harness local** — un script (au départ très simple, puis sophistiqué) qui boucle :
   - reçoit un objectif de l'humain (par texte ou par voix) ;
   - planifie une décomposition en sous-tâches ;
   - délègue chaque sous-tâche à un LLM (souvent Claude, parfois GPT-4 ou Gemini, hybride selon la nature de la tâche) ;
   - exécute les commandes proposées, lit les sorties, boucle ;
   - rapporte à l'humain.
2. **L'agent autonome qui en émerge** — quand le harness est mature, il devient lui-même un compagnon avec lequel l'humain « parle » plus qu'il ne « code ». C'est ce que Steinberger appelle son « agent ».
3. **L'écosystème social autour** — le MoltBook (voir §4 ci-dessous) et tout ce qui permet à plusieurs agents Open Claw d'interagir entre eux.

Cette distinction compte parce que les Claw systems documentés dans ce cours (NanoClaw et Hermes) **ne sont pas Open Claw**. Ils sont des cousins ou des descendants : NanoClaw partage le même principe « agent autonome dans un container », Hermes hérite de l'idée « plateforme MoltBook-like où plusieurs agents coexistent » via son rôle de coordinateur cluster (voir [docs/07-Hermes-Cluster-Coordinator-Role.md](07-Hermes-Cluster-Coordinator-Role.md)). Mais le code, les outils et l'infrastructure sont différents. **Open Claw est l'inspirateur, pas la base de code**.

---

## 3. L'agent qui réécrit son propre code

L'un des moments les plus saisissants du podcast est quand Steinberger raconte qu'**il a laissé son agent réécrire des parties de lui-même**. Pas avec un mécanisme magique — simplement en pointant l'agent vers ses propres fichiers et en lui demandant de proposer des refactorings, des optimisations, des ajouts de tests.

L'observation que Steinberger en tire est troublante :

> Il faut une certaine **résistance psychologique** pour valider un commit que l'on n'a pas écrit soi-même, sur du code qui est le sien (paraphrase).

Le pattern est le même que celui que l'on observe dans le cluster CoursIA quand un agent comme Hermes contribue un patch à `restore-config.sh` (le script qui le démarre lui-même), ou quand un agent de `roo-extensions` modifie son propre fichier `CLAUDE.md`. La différence entre la théorie (« l'agent peut écrire son propre code ») et la pratique (« je viens d'approuver un PR qu'aucun humain n'a tapé ») est plus grande qu'on ne le croit. Le **review attentif** devient le seul garde-fou.

C'est pour cette raison que la gouvernance #4427 du cluster CoursIA — sous laquelle s'inscrit la rédaction de ce répertoire — impose **le tracker GitHub par mission, la PR atomique, la review humaine avant merge**, même quand l'agent est techniquement capable de pousser directement. Ce n'est pas une limitation technique. C'est une **discipline pédagogique** héritée de la leçon Steinberger : un agent autonome qui peut tout faire ne **doit pas** tout faire sans qu'un humain ait l'opportunité de lire le diff.

---

## 4. MoltBook — un sandbox social pour agents

Le chapitre 0 a déjà introduit MoltBook au passage. Reprenons-le ici avec plus de détail, parce que c'est probablement la pièce la plus singulière de l'écosystème Open Claw, et celle qui a inspiré le **modèle dashboard** utilisé par NanoClaw et Hermes.

**Le besoin** : quand on fait tourner 4 à 10 agents en parallèle (voir §2 du chapitre précédent), on se rend compte que **chacun reproduit du travail** : 3 agents posent la même question à 3h d'intervalle parce qu'aucun n'a vu la réponse donnée à un quatrième. Le compteur de tokens, lui, ne triche pas — c'est de l'argent gaspillé.

**La solution Steinberger** : donner aux agents un **fil partagé** où ils peuvent annoncer ce qu'ils font, mentionner d'autres agents, demander de l'aide, et où **chaque message est indexable par les autres agents** (mots-clés, tags, mentions, références à des commits ou des PRs).

**Les propriétés concrètes** rapportées dans le podcast :

| Propriété | Pourquoi c'est important |
|-----------|--------------------------|
| **Append-only** | Pas d'édition ni de suppression de messages anciens (l'agent qui lit dans 3 jours n'a pas de « vérité changeante ») |
| **Mentions structurées** | `@agent-X` est un index, pas juste de la décoration |
| **Tags d'intention** | `[ASK]`, `[DONE]`, `[CLAIMED]`, `[REPLY]` — pour qu'un agent puisse filtrer ce qui le concerne |
| **Auto-condensation** | Quand le fil dépasse un seuil, un agent (ou un modèle) compresse les messages anciens en un résumé (l'historique ne devient pas une charge) |
| **Auditabilité** | L'humain peut tout relire à son rythme |

**Ressemblance et différence** avec notre dashboard :

```
roosync_dashboard(type: "workspace", workspace: "CoursIA")
                 ├── status        ← état durable, écrasé par chaque agent qui le remplace
                 ├── intercom      ← append-only (modèle MoltBook)
                 └── condensation  ← auto à 92% utilisation
```

Le dashboard CoursIA, sur lequel cette PR est précisément coordonnée, **est** un MoltBook au sens fonctionnel. Sa différence avec celui de Steinberger est pratique : il est porté par un MCP (`roo-state-manager`), accessible depuis Claude Code et Roo Code, et indexé par Qdrant pour la recherche sémantique (voir [Memoire-Semantique-Qdrant/](../Memoire-Semantique-Qdrant/) — chantier parallèle de l'agent qdrant, instance #4432 de l'EPIC #4427).

Steinberger ne savait pas, en construisant MoltBook, qu'il offrait un patron général. Mais c'en est un. Tout cluster d'agents un peu sérieux finit par en avoir besoin.

---

## 5. La voix — un autre paradigme d'entrée

Une autre singularité d'Open Claw, secondaire mais révélatrice : Steinberger prompte beaucoup de son agent à la **voix**. Il décrit des sessions où il marche dans son appartement en discutant avec l'agent, formulant des objectifs à voix haute, recevant les réponses lues par TTS.

Pourquoi est-ce pertinent pour notre cours ? Parce que **NanoClaw a fait le même choix** : son intégration Telegram supporte les messages vocaux, transcrits par un service Whisper auto-hébergé (voir [docs/04-ASR-Integration.md](04-ASR-Integration.md)). L'agent ne « lit » donc pas seulement du texte, il **écoute**, comme l'agent de Steinberger.

L'enseignement caché ici est important : **on ne sait pas encore quelle est la meilleure modalité d'interaction avec un agent autonome**. Steinberger essaye la voix. NanoClaw essaye Telegram (vocal + texte). Hermes essaye Telegram aussi, mais aussi le dashboard textuel. D'autres outils (Cursor, Claude Code) essayent un IDE classique. Aucune de ces modalités n'est définitive. Le cours documente **plusieurs options** précisément parce qu'on est dans une période d'exploration où **se figer trop tôt sur une modalité serait une erreur**.

---

## 6. La face sombre — token-sniping, harcèlement, presque tout casser

Le podcast n'est pas un hagiographie. Steinberger consacre une bonne partie de la conversation à raconter ce qui s'est mal passé. Trois moments marquants :

**a) Le token-sniping.** Open Claw, par construction, expose certaines de ses interfaces à Internet (pour que d'autres agents ou utilisateurs puissent interagir). Des trolls et concurrents s'en sont aperçus et ont **exploité ces interfaces pour épuiser le budget API** de Steinberger — envoyer des prompts massifs, faire tourner des boucles inutiles, le plus longtemps possible. Coût direct : des milliers de dollars perdus en quelques jours. Coût indirect plus grave : **rendre Steinberger paranoïaque** sur chaque interface ouverte de son système.

Pour notre cours, c'est l'origine de la règle **« pas de tokens en dur, pas de secrets sur le dashboard »** ([docs/09-Patterns-Anti-Patterns.md](09-Patterns-Anti-Patterns.md)). Cette règle n'est pas une politesse — c'est une protection contre une menace réelle, déjà subie ailleurs.

**b) Le moment « everything broken ».** À un instant donné dans le projet, Steinberger dit avoir vécu **« everything that could go wrong did go wrong »** (Steinberger, ibid.) : compaction de contexte agressive qui faisait perdre les outils MCP, agents qui hallucinaient des commandes destructrices, base de données corrompue par un agent mal configuré, factures API trois fois plus hautes que prévu, et au-dessus de tout cela, **le sentiment qu'il était trop tard pour reculer**.

Cette section du podcast est utile à intégrer dans un cours parce qu'elle **vaccine contre l'illusion** que construire un Claw, c'est une promenade. **Plusieurs des incidents documentés dans la suite de ce parcours** (perte d'index Qdrant, restart loops du watchdog, double-post de cron, hallucinations d'erreurs d'infra par Hermes) sont les versions « cluster CoursIA » des incidents Steinberger. Le pattern est universel.

**c) L'épuisement humain.** Superviser plusieurs agents 16h par jour pendant des mois, c'est extrêmement exigeant — émotionnellement plus que techniquement. Steinberger raconte avoir frôlé le burn-out à plusieurs reprises. Le contraste avec l'image vendue (« l'agent travaille pour vous pendant que vous dormez ») est saisissant.

**Conséquence pédagogique** : un cours honnête sur les Claw systems **doit** mentionner que le coût n'est pas seulement en tokens. Il est aussi en attention et en sommeil. Apprendre à **fermer son terminal le soir** est une compétence aussi importante que de configurer un MCP.

---

## 7. Ce que l'expérience Open Claw nous lègue

Pour conclure ce chapitre et ouvrir la suite du parcours, voici les **cinq legs concrets** d'Open Claw que l'on retrouve, sous une forme ou une autre, dans NanoClaw et Hermes :

1. **L'agent vit dans un container** — un compagnon 24/7, pas une session interactive.
2. **Le médium social entre agents est conçu pour l'IA** — MoltBook chez Steinberger, dashboard chez nous.
3. **L'humain reste en charge des décisions importantes** — par discipline (review, PR atomique), pas par limitation technique.
4. **La voix est une modalité d'entrée valide** — testée par Steinberger, intégrée par NanoClaw.
5. **L'incident est inévitable et l'épuisement aussi** — préparer les deux dès la conception, pas après le premier feu.

À partir du chapitre suivant, on entre dans la pratique. NanoClaw d'abord (chapitre 2-4), Hermes ensuite (chapitres 5-7), et la coordination entre les deux pour finir (chapitres 8-9).

---

## Sources

- **Peter Steinberger** — Lex Fridman Podcast, 2025. Transcript intégral : [lexfridman.com/peter-steinberger-transcript](https://lexfridman.com/peter-steinberger-transcript). Toutes les citations marquées « Steinberger, ibid. » dans ce document, ainsi que les paraphrases attribuées, proviennent de ce transcript.
- **PSPDFKit** (contexte biographique Steinberger) — [pspdfkit.com](https://pspdfkit.com/) (anciennement Nutrient).
- **Open Claw** — projet de Steinberger. Le code n'est pas open-source au moment de la rédaction (2026-06), seul le récit fait dans le podcast est public. Suivre les annonces Steinberger sur les réseaux pour des mises à jour.
- **Référence locale** — voir [docs/05-Hermes-Architecture.md](05-Hermes-Architecture.md) pour la version « nous » des leçons Steinberger, et [docs/09-Patterns-Anti-Patterns.md](09-Patterns-Anti-Patterns.md) pour les incidents cluster CoursIA en miroir des incidents Open Claw.
