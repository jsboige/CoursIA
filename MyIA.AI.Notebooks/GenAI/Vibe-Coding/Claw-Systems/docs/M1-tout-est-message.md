# M1 · Le modèle « tout est message »

> Module 1 du parcours **NanoClaw v2** (Claw Systems). Niveau : débutant+ · Durée indicative : ~2 h
> Pré-requis : notions de conteneurs (Docker) et de bases de données relationnelles.

## Objectifs

À l'issue de ce module, vous saurez :

1. Expliquer le **principe fondateur** de NanoClaw v2 — *tout est message* — et pourquoi il n'y a **aucun IPC** entre l'hôte et les agents.
2. Décrire le **modèle d'entités** (utilisateurs → groupes de messagerie → groupes d'agents → sessions) qui achemine un message jusqu'au bon conteneur.
3. Comprendre la **conséquence directe** de ce principe : deux bases SQLite par session, avec un seul écrivain par fichier.

## Le problème : faire dialoguer un hôte et des agents jetables

Quand on construit un assistant autonome qui tourne 24/7 et reçoit des messages de plusieurs personnes, sur plusieurs canaux (Telegram, Slack…), une question revient vite : **comment l'orchestrateur parle-t-il à l'agent qui réfléchit ?**

Les réflexes classiques — un pipe sur `stdin`/`stdout`, un *watcher* de fichiers, un socket, un appel RPC — partagent le même défaut : ils **couplent** l'hôte et l'agent dans le temps. Si l'agent redémarre, le pipe se casse. Si deux messages arrivent en même temps, il faut gérer la concurrence sur le canal. Si l'agent plante en plein traitement, l'état est perdu et difficile à rejouer.

NanoClaw v2 prend le parti inverse.

## Le principe : tout est message

> **Il n'y a ni IPC, ni *watcher* de fichiers, ni piping `stdin` entre l'hôte et le conteneur. Deux bases SQLite par session sont la _seule_ surface d'entrée/sortie.**

Concrètement :

- L'**hôte** est un unique processus Node qui orchestre des **conteneurs d'agents par session**.
- Un message d'une plateforme (ex. Telegram) arrive via un **adaptateur de canal**, est routé par le modèle d'entités, **écrit dans la base entrante** de la session, puis **réveille** un conteneur.
- L'**agent-runner** à l'intérieur du conteneur *interroge* (poll) sa base entrante, appelle le LLM (Claude), puis **écrit la réponse dans la base sortante**.
- L'hôte *interroge* la base sortante et **délivre** la réponse via le même adaptateur.

```
Telegram ──▶ Adaptateur ──▶ [Hôte Node] ──écrit──▶ inbound.db ──┐
                                                                 │ (réveil)
                                                                 ▼
                                                        [Conteneur agent]
                                                         poll inbound.db
                                                         appel LLM (Claude)
                                                         écrit outbound.db
                                                                 │
  Telegram ◀── Adaptateur ◀── [Hôte Node] ◀──poll── outbound.db ┘
```

Le message est la **seule unité d'échange**. Un agent qui démarre n'a rien à « reconnecter » : il lit sa base, fait son travail, écrit sa réponse. Un agent qui meurt en cours de route laisse l'état **intact et rejouable** dans les bases.

## Le modèle d'entités : du « qui parle » au « quel conteneur »

Avant qu'un message n'atteigne une base, NanoClaw doit décider **quel agent** doit le traiter, et **dans quelle session**. C'est le rôle du modèle d'entités :

| Entité | Rôle |
|--------|------|
| **users** (`<canal>:<handle>`) | Une identité de plateforme, ex. `telegram:emerjesse`. |
| **messaging_groups** | Un salon/canal sur **une** plateforme (un chat Telegram, un canal Slack…). |
| **agent_groups** | Un agent logique : son workspace, sa mémoire, son `CLAUDE.md`, sa personnalité, sa configuration de conteneur. |
| **sessions** | L'intersection `agent_group × messaging_group × thread` → **un conteneur dédié**. |

Le câblage `messaging_group → agent_group` (le « wiring ») détermine quel agent répond dans quel salon. Une même session = un même conteneur, avec sa propre paire de bases.

```
users ──┐
        ├──▶ messaging_groups ──(wiring)──▶ agent_groups
        │                                        │
        └─────────────────────────────────────── ┤
                                                  ▼
                                              sessions ──▶ 1 conteneur + 2 bases
```

En production sur le cluster (machine `ai-01`), l'agent Telegram « ClusterManager » est exactement cela : un *agent_group* câblé à un *messaging_group* Telegram, dont chaque fil de discussion (thread) devient une *session* isolée avec son conteneur.

## La conséquence : deux bases, un seul écrivain par fichier

Le principe « tout est message » impose une discipline simple et robuste sur les entrées/sorties. Chaque session possède **deux** fichiers SQLite (sous `data/v2-sessions/<session_id>/`) :

| Fichier | Écrivain | Lecteur | Contenu |
|---------|----------|---------|---------|
| `inbound.db`  | **hôte**      | conteneur | messages entrants, routage, questions en attente |
| `outbound.db` | **conteneur** | hôte      | messages sortants, état de session |

**Exactement un écrivain par fichier** : aucune contention de verrou entre deux montages. Pour éviter les collisions de numéros de séquence, l'hôte utilise des `seq` **pairs**, le conteneur des `seq` **impairs**. Le battement de cœur (*heartbeat*) n'est même pas une écriture en base : c'est un simple *touch* de fichier sur `/workspace/.heartbeat`.

> Le **détail** de ces deux bases (schémas, accusés de traitement, reprise après crash) fait l'objet du **module M2**. Ici, retenez seulement que la séparation **découle** du principe : si tout passe par des messages persistés, alors chaque sens de circulation a son propre fichier et son propre écrivain.

## Pourquoi ce design (et ce qu'il offre « gratuitement »)

- **Conteneurs jetables** : l'agent n'a pas d'état en mémoire à préserver. On peut le tuer, le relancer, le reconstruire sans rien perdre — l'état vit dans les bases.
- **Reprise et rejouabilité** : un message non traité reste dans `inbound.db` ; au prochain réveil, l'agent le reprend.
- **Pas de course sur le canal** : deux messages simultanés sont deux lignes en base, pas deux écritures concurrentes sur un pipe.
- **Observabilité** : pour diagnostiquer, on lit les bases — *« le message est-il arrivé dans `inbound.db` ? »*, *« l'agent a-t-il produit une réponse dans `outbound.db` ? »*.

## À retenir

1. **Tout est message** : l'hôte et l'agent ne se parlent **que** via deux bases SQLite par session.
2. Le **modèle d'entités** achemine un message du « qui parle » jusqu'au « quel conteneur ».
3. **Un seul écrivain par fichier** (hôte = `inbound`/`seq` pairs, conteneur = `outbound`/`seq` impairs) : robustesse et zéro contention.

## Pour aller plus loin

- **M2 · Architecture v2** — l'hôte Node, les conteneurs par session, le détail des deux bases et de la base centrale.
- Modules suivants (à venir) : déploiement Windows réel · vivre en production (la chaîne de patches) · coordination multi-bots.

---

*Module M1 — parcours NanoClaw v2 · Claw Systems · juin 2026*
