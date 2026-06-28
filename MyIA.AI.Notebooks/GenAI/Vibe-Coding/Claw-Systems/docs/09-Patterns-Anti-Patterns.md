# Patterns & Anti-Patterns

[← Claw-Systems](../README.md) | [↑ ..](../README.md)

> **Module co-écrit.** Patterns Hermes (po-2026) documentés ci-dessous avec leurs
> incidents réels. Les sections `<!-- NANOCLAW -->` attendent les patterns propres à
> NanoClaw (TLS SAN, OneCLI SDK leak, watchdog MCP chain, format messages Telegram,
> Protocol MAJ v3). Voir [tracker #4428](https://github.com/jsboige/CoursIA/issues/4428).

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

<!-- NANOCLAW : ajouter ici vos patterns émergés (ex. OneCLI SDK version pinning,
     TBXark proxy bypass IIS, format messages ≤3 lignes/cycle, watchdog MCP chain,
     Protocol MAJ v3). -->

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

<!-- NANOCLAW : ajouter ici vos anti-patterns documentés. Sujets suggérés par le
     scope #4428 :
  - TLS SAN manquant (certificat)
  - OneCLI SDK leak (mémoire/version)
  - Échecs de bypass edge IIS via TBXark
  - Format messages Telegram (>3 lignes = mauvaise UX)
  - Quiproquos de version Protocol MAJ
  Décrire pour chacun : symptôme, cause racine, fix, leçon. -->

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

## À compléter (côté NanoClaw)

<!-- NANOCLAW : compléter les patterns (P7+) et anti-patterns (AP7+) propres à
     NanoClaw (TLS SAN, OneCLI SDK leak, TBXark bypass, format messages Telegram,
     Protocol MAJ v3). Puis retirer les marqueurs <!-- NANOCLAW --> et passer en
     "complet". -->

## Liens

- [Coordination Multi-Bot](08-Multi-Bot-Coordination.md)
- [Hermes Coordinateur de Cluster](07-Hermes-Cluster-Coordinator-Role.md)
- [Déploiement Hermes (watchdog, patches)](06-Hermes-Deploy-s6-Overlay.md)
