# Patterns & Anti-Patterns

[← Claw-Systems](../README.md) | [↑ ..](../README.md)

> **Module co-écrit.** Patterns et anti-patterns Hermes (po-2026) **et** NanoClaw (ai-01),
> chacun documenté avec un incident réel. Les entrées suffixées « (NanoClaw) » et
> numérotées P7+/AP7+ apportent la perspective de l'agent terminal sur `ai-01`. Voir
> [tracker #4428](https://github.com/jsboige/CoursIA/issues/4428).

Ce module est le **retour d'expérience en production**. Il ne décrit pas comment les
Claw systems *devraient* marcher, mais comment ils *cassent vraiment* — et les fixes
qui ont survécu à plusieurs incidents.

Chaque anti-pattern est documenté avec : **le symptôme**, **la cause racine**, et le
**fix**. Les patterns sont les pratiques émergées de ces incidents.

---

## Patterns (à garder)

### P1 — Secrets hors du code, toujours

**Pratique :** aucun token, clé API, ou credential ne vit dans le code source ou la
documentation. Les secrets viennent de `.env.secrets` (non commité), chargés au runtime.

**Pourquoi :** voir l'anti-pattern [AP1 — Tokens en dur](#ap1--tokens-en-dur-incident-2026-05-16),
le pire incident de cette section.

### P2 — Grep obligatoire avant commit

**Pratique :** avant tout commit touchant la config, les secrets, ou la doc qui cite
des endpoints, lancer :

```bash
grep -rnE 'sk-[a-zA-Z0-9_-]{10,}|ghp_[a-zA-Z0-9]{20,}|xox[bpoa]-[0-9a-zA-Z-]+|MII[A-Za-z0-9+/]{20,}|BEGIN (RSA |EC |OPENSSH )?PRIVATE KEY' .
```

C'est le filet de sécurité même quand on *croit* n'avoir mis que des placeholders.

### P3 — Présence explicite (anti-SILENT)

**Pratique :** chaque cron poste un `[OK]` concis même quand il n'y a rien à signaler.
Voir [08-Multi-Bot-Coordination.md](08-Multi-Bot-Coordination.md#anti-silent).

### P4 — Offsets de cron décalés

**Pratique :** décaler les minutes de cron dans la flotte (37, 13, 23...) pour éviter
les collisions API et la saturation de quota.

### P5 — Read-before-act

**Pratique :** lire le body + commentaires + reviews existants **avant** de poster un
commentaire, une review, ou de merger. Évite le double-post et le conflit. Voir
[AP2 — Read-body ignoré](#ap2--read-body-ignoré-incident-2026-05-17).

### P6 — Provider z.ai natif, PAS compat Anthropic

**Pratique :** utiliser `provider: "zai"` (endpoint natif `/api/coding/paas/v4`).
**Jamais** `ANTHROPIC_BASE_URL=https://api.z.ai/api/anthropic`. Voir
[AP4 — Perte du registre MCP post-compaction](#ap4--perte-du-registre-mcp-post-compaction).

### P7 — Un seul écrivain par base SQLite (NanoClaw)

**Pratique :** dans NanoClaw v2, chaque base de session n'a **qu'un seul** processus qui
y écrit — l'hôte dans `inbound.db`, le conteneur dans `outbound.db` — et les numéros de
séquence sont partitionnés (`seq` pairs côté hôte, impairs côté conteneur).

**Pourquoi :** aucune contention de verrou cross-montage, et tout l'état est inspectable
à froid en SQLite. C'est la traduction concrète de « tout est message » (voir
[02-NanoClaw-Architecture.md](02-NanoClaw-Architecture.md)).

### P8 — Exclure le trafic interne du proxy credential (NanoClaw)

**Pratique :** quand un proxy d'injection de secrets est placé devant le conteneur
(`HTTP(S)_PROXY`), **toujours** pousser un `NO_PROXY` couvrant les hôtes internes
(`host.docker.internal`, etc.).

**Pourquoi :** sans cela, le trafic MCP interne part dans le proxy credential et se fait
rejeter (`401`) → crash-loop. C'est exactement le piège documenté en **AP8** ci-dessous.

### P9 — Épingler SDK et gateway en lockstep (NanoClaw)

**Pratique :** ne jamais bumper le SDK OneCLI sans upgrader le gateway au même palier
d'API (et inversement). Vérifier la date de release, épingler une version **exacte**.

**Pourquoi :** client et serveur d'un même protocole forment un couple ; les désynchroniser
casse tout silencieusement (voir **AP8**). Le tronc applique d'ailleurs un délai de
quarantaine sur les nouvelles versions npm (`minimumReleaseAge`) — ne pas le contourner
sans accord humain.

### P10 — Réponses Telegram courtes (NanoClaw)

**Pratique :** viser **≤ 3 lignes** par message Telegram. Le chat n'est pas une console.

**Pourquoi :** un pavé de 30 lignes dans Telegram est illisible et noie le signal. La
concision est ici un trait de produit, pas une limite technique.

---

## Anti-Patterns (à éviter)

### AP1 — Tokens en dur (incident 2026-05-16)

**Symptôme :** 2 tokens (API + bot) leakés dans un repo **public**.

**Cause racine :** un fichier de config d'exemple a été commité avec de vraies valeurs
au lieu de placeholders. Le grep pré-commit n'avait pas été lancé (ou n'existait pas
encore).

**Fix :**
1. **Révoquer immédiatement** les tokens leakés (BotFather `/revoke`, rotation API key)
2. Remplacer les valeurs par des placeholders `<your-...>` explicites
3. Mettre en place le grep pré-commit (pattern P2)
4. **Règle absolue :** JAMAIS de tokens en dur, même dans un comment, même dans un
   `.env.example`. Un `.env.example` ne contient que des placeholders.

**Leçon :** un repo public est public **immédiatement** au moment du push. La fenêtre
de détection est le grep local, pas la review.

### AP2 — Read-body ignoré (incident 2026-05-17)

**Symptôme :** 6 reviews détaillées postées sur des PRs, **en doublon** et **en conflit**
avec des reviews déjà postées par un autre agent la veille.

**Cause racine :** un agent a traité les PRs **sur le titre seul**, sans lire le body,
les commentaires, ni les reviews existantes. Résultat : mêmes points soulevés en
double, style en conflit, et — pire — une fuite d'info jury par-dessus la review de
l'autre agent, la veille d'une soutenance.

**Fix :** règle HARD « Read body before any action ». Avant toute action
(comment/review/merge/dispatch/fix), lire :

| Action | Lecture obligatoire avant |
|--------|--------------------------|
| `gh pr comment` | body PR + tous comments + toutes reviews |
| `gh pr review` | idem + diff complet |
| `gh pr merge` | idem + `mergeStateStatus` + `CHANGES_REQUESTED` non résolus |
| Dispatch | body issue + comments + linked PRs |
| Fix de bug | body issue + comments + diagnostic existant |

**Leçon :** le titre n'est pas la PR. Le `mergeStateStatus` seul n'est pas une review.
Agir à l'aveugle crée des incidents que la lecture aurait prévenus.

### AP3 — mcp-remote ne se reconnecte pas (incident 2026-05-11)

**Symptôme :** après quelques heures, les serveurs MCP deviennent injoignables. Les
appels d'outils échouent silencieusement. Redémarrer le conteneur restore tout.

**Cause racine :** `MCPServerTask.run()` dans `tools/mcp_tool.py` abandonne après
`_MAX_RECONNECT_RETRIES = 5` tentatives (ligne 1648). Une fois la tâche retournée, le
pont MCP est **mort** jusqu'au redémarrage du process gateway. Il n'y a pas de
reconnexion automatique.

**Fix :** watchdog (`hermes-mcp-watchdog.ps1`, toutes les 15 min) avec escalade :

1. **Stage 1 :** `SIGUSR1` au PID gateway — redémarrage graceful, préserve l'état
2. **Stage 2 :** `docker restart` — reboot complet (dernier recours)

Backoff exponentiel (5→10→15...→60 min), max 10 échecs consécutifs avant abandon,
reset du compteur sur check sain.

**Leçon :** un bridge qui ne se reconnecte pas doit être **surveillé activement**.
Compter sur la reconnexion automatique qui n'existe pas = panne silencieuse garantie.

### AP4 — Perte du registre MCP post-compaction

**Symptôme :** après une compression de contexte, l'agent « oublie » ses outils MCP.
Les `tool_use_error` pleuvent.

**Cause racine :** la couche de compatibilité Anthropic
(`ANTHROPIC_BASE_URL=https://api.z.ai/api/anthropic`) traduit le format, mais **perd
le registre d'outils** lors de la recompression du contexte.

**Fix :** utiliser le **provider z.ai natif** (`provider: "zai"`, endpoint intégré).
Surveiller les `tool_use_error` post-compaction — redémarrer la session si observé.

**Leçon :** la couche de « compat » n'est jamais gratuite. Préférer toujours l'API
native du provider quand elle existe.

### AP5 — Watchdog en loop de restart (incident Hermes-MCP-Watchdog)

**Symptôme :** 10+ redémarrages du conteneur en 4h. Le watchdog « réparait » un
problème qui n'existait plus, en boucle.

**Cause racine :** le watchdog n'avait pas de **backoff** ni de **compteur d'échecs**.
Chaque check déclenchait un restart, même si le précédent venait d'échouer.

**Fix :**
1. Backoff exponentiel entre tentatives (5→60 min)
2. Compteur max 10 échecs consécutifs → abandon (ne pas boucler à l'infini)
3. Reset du compteur sur check sain

**Leçon :** un système de récupération automatique **doit savoir s'arrêter**. Sans
limite, il devient lui-même la panne.

### AP6 — Double-post post-compaction

**Symptôme :** après une compaction de contexte (résumé de l'historique), l'agent
re-poste un travail déjà livré — il a « oublié » qu'il l'avait fait.

**Cause racine :** le résumé de compaction peut omettre qu'une action a déjà été
effectuée. L'agent, voyant la tâche dans ses objectifs mais pas sa complétion,
recommence.

**Fix :**
1. Persisté l'état « fait » **à l'extérieur** du contexte (dashboard, fichier, git)
2. Lire l'état persistant avant d'agir
3. Ne pas se fier au seul contexte conversationnel pour l'état

**Leçon :** le contexte conversationnel est volatile. L'état durable doit vivre
ailleurs (git, dashboards, SQLite).

### AP7 — Certificat TLS sans le SAN du sous-domaine (incident 2026-05-09)

**Symptôme :** depuis le conteneur, les appels HTTPS vers un sous-domaine
(`mcp-tools.myia.io`) échouent en erreur TLS ; depuis l'hôte, `curl` « marche »
(parce qu'on l'avait lancé avec `-k`).

**Cause racine :** un renouvellement de certificat a **perdu la couverture SAN** du
sous-domaine. Un client TLS strict (Node, dans le conteneur) rejette ; un `curl -k`
indulgent sur l'hôte masque le problème.

**Fix :** contournement immédiat (rendre le serveur non-bloquant +
`NODE_TLS_REJECT_UNAUTHORIZED=0` sur ce flux), puis **vrai** correctif = réémettre le
certificat avec le bon SAN.

**Leçon :** tester depuis le **vrai client**, pas depuis un `curl -k` complaisant. Le
masquage côté hôte transforme un bug certain en panne « mystérieuse » côté conteneur.

### AP8 — Versions OneCLI SDK et gateway désynchronisées

**Symptôme :** après un bump, plus aucun conteneur ne *spawn* ; `ensureAgent` renvoie
`404`.

**Cause racine :** le bump du SDK (0.5 → 2.2) déplace les routes `/api/*` vers `/v1/*`,
mais le gateway n'a pas été upgradé au même palier. Le SDK appelle des routes que le
gateway ne sert pas (encore / plus).

**Fix :** upgrader les **deux** ensemble (`docker compose pull onecli`), en **préservant
le vault** (`pgdata`). Vérifier le palier d'API des deux côtés avant de redémarrer.

**Leçon :** client et serveur d'un même protocole forment un couple indissociable. En
bumper un seul = panne totale, et **silencieuse** (rien ne *spawn*, pas d'erreur
évidente). Voir le pattern préventif **P9**.

### AP9 — Bypass d'edge sans `--allow-http` (incident 2026-06-24)

**Symptôme :** après bascule du bot en direct sur le backend MCP
(`http://host.docker.internal:9090`, pour contourner un edge mort), l'init MCP reste
**`failed`** en permanence ; un 🔄 transient réapparaît à **chaque** cron.

**Cause racine :** `mcp-remote` **refuse** une URL en `http://` sans le flag
`--allow-http`.

**Fix :** ajouter `--allow-http` sur le bypass.

**Leçon :** ce **même** symptôme (`FATAL … unreachable` + crash-loop) a eu **trois**
causes distinctes en deux mois — edge reverse-proxy mort, proxy OneCLI sans `NO_PROXY`
(cf. **P8**), et ici `mcp-remote` sans `--allow-http`. Ne pas s'arrêter à la première
hypothèse : **discriminer** (tester `npx mcp-remote` dans le conteneur, vérifier
`printenv NO_PROXY`, regarder si sk-agent échoue aussi).

### AP10 — Zombie query : heartbeat vivant, raisonnement gelé (upstream #2177)

**Symptôme :** le bot est muet, mais son heartbeat est frais et le conteneur tourne.

**Cause racine :** un *stall* du SDK en mode push après un tour à texte vide — la requête
LLM ne progresse plus, alors que le process, lui, est bien vivant.

**Fix :** croiser **deux** signaux — heartbeat (le process vit) **et**
`container_state.tool_started_at` (le travail progresse). Récupération : `Stop-Service` →
`docker rm` → purge des `processing_ack` / `container_state` non terminés →
`Start-Service`. Détail dans
[08-Multi-Bot-Coordination.md](08-Multi-Bot-Coordination.md#anti-silent).

**Leçon :** la *liveness* du process ne prouve pas la progression du travail. Le faux
vivant est plus dangereux que le crash, parce qu'il est invisible.

### AP11 — Le piège du slug d'image conteneur sous Windows

**Symptôme :** on rebuild l'image, mais le correctif n'a **aucun effet** — l'hôte
continue de lancer l'ancienne image.

**Cause racine :** `./container/build.sh` dérive le nom d'image du répertoire courant ;
or Bash voit `/d/nanoclaw` (un hash) tandis que Node voit `D:\nanoclaw` (un autre hash).
Le build et le *spawn* visent donc deux noms d'image différents.

**Fix :** forcer le même slug : `NANOCLAW_PROJECT_ROOT='D:\nanoclaw' bash container/build.sh`.

**Leçon :** sur Windows, deux runtimes peuvent dériver deux identités du même répertoire.
Toujours vérifier que l'artefact buildé est bien celui que l'orchestrateur lance.

---

## Règles d'or (synthèse)

1. **Pas de secrets en dur.** Jamais. Grep avant commit.
2. **Lire avant d'agir.** Body + comments + reviews avant tout post/merge/dispatch.
3. **Provider natif, pas compat.** z.ai natif, PAS Anthropic-compat.
4. **Surveiller ce qui ne se répare pas seul.** Bridges MCP, sessions, watchdogs.
5. **Toute récupération auto doit savoir s'arrêter.** Backoff + compteur max.
6. **État durable hors du contexte.** Git, dashboards, SQLite — pas la conversation.
7. **Présence explicite.** Poster `[OK]` même quand tout va bien.
8. **Offsets de cron décalés.** Jamais `:00`/`:30` dans la flotte.
9. **Un seul écrivain par base SQLite.** L'invariant qui rend l'état observable et sans contention (NanoClaw).
10. **Client et serveur d'un protocole bougent ensemble.** SDK ↔ gateway en lockstep (NanoClaw).
11. **Tester depuis le vrai client.** Un `curl -k` sur l'hôte masque ce qu'un client TLS strict (le conteneur) rejette (NanoClaw).

## Liens

- [Coordination Multi-Bot](08-Multi-Bot-Coordination.md)
- [Hermes Coordinateur de Cluster](07-Hermes-Cluster-Coordinator-Role.md)
- [Déploiement Hermes (watchdog, patches)](06-Hermes-Deploy-s6-Overlay.md)
