# Claudish — Proxy Multi-Provider pour Assistants de Code

[← Vibe-Coding](../README.md) | [↑ ..](../README.md)

**Claudish** est le proxy/routeur qui rend les assistants de vibe-coding — **Claude Code**, les bots autonomes (Hermes, NanoClaw), les clients **OpenAI** (notebooks, SDK) — **agnostiques du fournisseur de modèles**. Au lieu de parler en dur à `api.anthropic.com`, le client s'adresse à Claudish, qui traduit la requête vers le fournisseur choisi selon le coût, la capacité et le quota : **Anthropic natif**, **z.ai GLM**, **MiniMax**, **Qwen** (forfait et self-hosté), **DeepSeek** (paiement à l'usage), **Kimi**, **Mistral**, **OpenAI Codex**, et des modèles **self-hostés via vLLM**.

> **Sources** : [MadAppGang/claudish](https://github.com/MadAppGang/claudish) (upstream open-source) · [jsboige/claudish](https://github.com/jsboige/claudish) (fork opérationnel du cluster MyIA) · [claudish.com](https://claudish.com)

## Pourquoi une section Claudish ?

Les assistants de code modernes parlent le **wire Anthropic** : ils adressent toujours `https://api.anthropic.com`. Quand on veut tirer parti d'autres fournisseurs — un modèle local illimité (GPU maison), un forfait de code économique (z.ai GLM), ou garder Anthropic pour le raisonnement lourd — on se heurte à un mur : le client ne sait parler qu'à Anthropic.

| Sans Claudish | Avec Claudish |
|---------------|---------------|
| Client bridé à `api.anthropic.com` | Client pointe sur Claudish, qui route |
| Pas d'accès aux modèles non-Anthropic | GLM, MiniMax, Qwen, DeepSeek accessibles sans toucher au code |
| Coût = tarif Anthropic pour tout | Arbitrage coût/capacité **par rôle** (opus, sonnet, haiku, fable) |
| Forfait épuisé = agent mort | Cascade de substituts, **toujours annoncée** |

Claudish est la **couche routage-provider** du vibe-coding MyIA. Elle complète les autres sections de `Vibe-Coding/` :

| Section | Rôle |
|---------|------|
| [Claude-Code/](../Claude-Code/), [Roo-Code/](../Roo-Code/) | Les assistants (front-ends de codage) |
| [Claw-Systems/](../Claw-Systems/) | Les bots autonomes (front-ends Telegram) |
| Claudish/ (cette section) | **Le proxy qui route les assistants vers les fournisseurs** |

## Ce qu'il faut retenir en 5 points (état au 2026-10-21)

1. **Un hub, des relais.** Le service central (le *hub*) tourne sur une machine du cluster ; plusieurs postes font tourner leur propre conteneur Claudish en **relais** (*sidecar*), les autres passent par la passerelle HTTPS. Si le hub tombe, le relais bascule en **mode autonome** et sert localement, puis revient au hub après des preuves de santé répétées. Le hub cesse ainsi d'être un point de panne unique.
2. **Un rôle, une cascade.** Chaque rôle Claude Code (`opus`, `sonnet`, `haiku`, `fable`) a un modèle **nominal** et une **liste ordonnée de substituts**. Quand un forfait est épuisé, le rôle descend la liste ; chaque marche a son propre délai de remise à l'essai (`10 min → 30 min → 1 h → 4 h → 24 h`), et la dernière marche (paiement à l'usage) sert toujours.
3. **Jamais de bascule silencieuse.** Chaque substitution est annoncée au client (bloc de texte sur `/v1/messages`, en-tête `x-claudish-failover-notice` sur `/v1/chat/completions`). Une notice décrit des **faits**, jamais des consignes.
4. **Ne jamais bloquer l'agent.** Le proxy est dans une boucle agentique : un flux se termine *toujours* (`message_stop`), un flux muet est coupé après un délai, un refus de politique est réessayé puis étiqueté, une recherche web ratée devient du texte.
5. **Mesurer avant de croire.** Le fork s'est doté d'instruments (captures, compteurs par machine et par session, outil MCP de lecture du trafic) parce que plusieurs « évidences » se sont révélées fausses à la mesure — voir les récits du [guide §7](docs/Claudish-Proxy.md#7-war-stories--leçons-du-fork-en-production).

## Pipeline de production

```text
Client (Claude Code / bot / client OpenAI)
  → parle le wire Anthropic (/v1/messages) OU OpenAI (/v1/chat/completions)
  → relais Claudish local (sidecar) → hub Claudish   [ou passerelle HTTPS models.myia.io → hub]
    → authentifie (clé proxy, ou clé « scopée » limitée à une liste de modèles)
    → résout le rôle → modèle nominal ou marche de cascade
    → traduit vers le wire du fournisseur cible
    → annonce toute substitution
  → Fournisseur (Anthropic natif / GLM / MiniMax / Qwen / DeepSeek / vLLM / …)
  → réponse retraduite vers le wire du client
```

## Documentation

| Document | Description |
|----------|-------------|
| [Claudish-Proxy.md](docs/Claudish-Proxy.md) | Le proxy en détail : wires, topologie hub/relais, cascade par rôle, connecter un agent ou un bot, avancées du fork, **récits de production et leçons transférables**, mesures de la flotte, variables d'environnement (**§8 : quel consommateur lit quelle variable**), dépannage |
| [MCP-Capability-Negotiation.md](docs/MCP-Capability-Negotiation.md) | Proposition d'août 2026 : laisser l'agent négocier ses capacités à la condensation — et ce que le fork en a construit depuis (§0) |
| [claudish.env.secrets.example](configs/claudish.env.secrets.example) | Gabarit de configuration (placeholders uniquement — remplir avec vos valeurs) |
| [01-claude-code-via-claudish.ipynb](notebooks/01-claude-code-via-claudish.ipynb) | Carnet pédagogique : interroger Claudish depuis Python |

## Leçon fondatrice — le trick du nom Claude

Le pattern réutilisable pour connecter n'importe quel bot au cluster : **lui faire envoyer un nom de modèle Claude** (ex. `claude-sonnet-4-6`). Claudish remappe ce nom vers le modèle budgété du rôle via le `modelMap` du profil actif. Une seule ligne de config côté bot, **aucun patch de wire**. Voir le détail et la leçon Hermes dans [docs/Claudish-Proxy.md §5](docs/Claudish-Proxy.md#5-connecter-un-bot--le-trick-du-nom-claude-leçon-hermes).

## Ce qui a changé depuis la refonte d'août 2026

| Sujet | Août 2026 (#11555) | Octobre 2026 |
|-------|--------------------|--------------|
| Hub | po-2023, derrière la passerelle IIS | **po-2025** depuis la bascule du 2026-09-05 ; la passerelle pointe directement sur le hub |
| Relais | un sidecar (ai-01) | un relais sur plusieurs postes, avec détection de boucle par identité de processus |
| Rôles | 3 tiers (Opus / Sonnet / Haiku) | 4 rôles : **Fable** s'ajoute (servi par Astra, voie OpenAI Codex) ; **Haiku différencié par poste** — MiniMax M3.1-Flash en nominal, deux postes armés en permanence sur le modèle vLLM local par un armement limité à la machine (détail : [§3](docs/Claudish-Proxy.md#3-la-cascade-par-rôle--substitution-ordonnée-bascule-annoncée)) |
| Cascade | marches ordonnées + délai par marche | + mur **par fournisseur** (pas par rôle), délégation d'une marche à un autre rôle, saut d'une marche qui ne peut pas prendre la requête, maintien d'une session sur sa marche (10 min) |
| Version servie | le client choisissait la version Anthropic | le `modelMap` **épingle** la version sur la voie native |
| Accès externes | une seule clé proxy | + **clés scopées** : liste blanche de modèles, plafond de requêtes simultanées, attribution par clé |
| Garde-fous | — | refus étiqueté d'une clé non-Anthropic sur la voie native, plafond de tokens par session (alerte), refus de politique étiqueté |
| Négociation de capacités | proposition (E0) | vocabulaire câblé côté fork, désactivé par défaut (voir [§0 du ledger](docs/MCP-Capability-Negotiation.md)) |

Historique des refontes : juin 2026 (création de la section, #4453) · 2026-08-18 (état du fork opérationnel, #11555) · 2026-09-10 (réconciliation du guide avec le déploiement, #15418) · 2026-10-21 (cette mise à jour).

---

*Section Claudish — mise à jour du 2026-10-21. Le proxy multi-provider du cluster MyIA : deux wires en entrée (Anthropic et OpenAI), un hub et des relais par poste, quatre rôles routés en cascade **annoncée**, et un principe directeur : ne jamais bloquer l'agent.*
