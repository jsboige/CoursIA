# Claudish — Proxy Multi-Provider pour Assistants de Code

[← Vibe-Coding](../README.md) | [↑ ..](../README.md)

**Claudish** est le proxy/routeur qui rend les assistants de vibe-coding — **Claude Code**, **Roo Code**, les bots autonomes (Hermes, NanoClaw) — **agnostiques du fournisseur de modèles**. Au lieu de parler en dur à `api.anthropic.com`, le client s'adresse à Claudish, qui traduit la requête vers le provider choisi selon le coût, la capacité et le quota : **Anthropic natif**, **MiniMax-M3** (Anthropic-compatible), **z.ai/GLM Coding Plan**, **Qwen self-hosté**, **DeepSeek PAYG**.

> **Sources** : [MadAppGang/claudish](https://github.com/MadAppGang/claudish) (upstream open-source) · [jsboige/claudish](https://github.com/jsboige/claudish) (fork opérationnel du cluster MyIA) · [claudish.com](https://claudish.com)

## Pourquoi une section Claudish ?

Les assistants de code modernes (Claude Code, Roo Code) parlent le **wire Anthropic** : ils adressent toujours `https://api.anthropic.com`. Quand on veut tirer parti d'autres fournisseurs — un modèle local illimité (Qwen sur GPU maison), un plan coding économique (z.ai GLM), ou garder Anthropic pour le raisonnement lourd — on se heurte à un mur : le client ne sait parler qu'à Anthropic.

| Sans Claudish | Avec Claudish |
|---------------|---------------|
| Client bridé à `api.anthropic.com` | Client pointe sur Claudish, qui route |
| Pas d'accès aux modèles non-Anthropic | GLM, Qwen, Gemini accessibles sans toucher au code |
| Coût = tarif Anthropic pour tout | Arbitrage coût/capacité **par tier** |
| Panne Anthropic = agent mort | Provider alternatif, **sans bascule silencieuse** |

Claudish est la **couche routage-provider** du vibe-coding MyIA. Elle complète les autres sections de `Vibe-Coding/` :

| Section | Rôle |
|---------|------|
| [Claude-Code/](../Claude-Code/), [Roo-Code/](../Roo-Code/) | Les assistants (front-ends de codage) |
| [Claw-Systems/](../Claw-Systems/) | Les bots autonomes (front-ends Telegram) |
| Claudish/ (cette section) | **Le proxy qui route les assistants vers les providers** |

## Écosystème à 3 tiers — cascade ordonnée

Le déploiement MyIA budgete **un provider nominal par tier** + une **cascade de bascule ordonnée** entre providers de même direction (`degraded>degraded>degraded` ou `improved>improved`). Chaque step de la cascade a un **TTL indépendant** (`[10m, 30m, 1h, 4h, 24h]`) qui survit à l'armement du rôle — un quota wall hebdomadaire (Qwen) n'est pas re-probé toutes les 10 min pendant que la fenêtre GLM 5h se ré-initialise.

| Tier | Provider nominal | Cascade (état au 2026-08-18) | Direction |
|------|------------------|--------------------------------|-----------|
| **Opus** | Anthropic natif | `qwen-token-plan@qwen3.8-max > gc@glm-5.3 > ds@deepseek-v4-flash` | degraded |
| **Sonnet** | z.ai GLM Coding Plan (GLM-5.3) | `ds@deepseek-v4-flash` (PAYG direct, latéral) | lateral |
| **Haiku** | MiniMax-M3 (Anthropic-compatible) | `qwen-token-plan@qwen3.8-max > ds@deepseek-v4-flash` | improved |

Sur un burst (rate-limit), Claudish **backoff** sur le step courant et passe au suivant quand le TTL expire. Sur une panne franche, le step suivant prend la main **avec notice de dégradation explicite** (3 canaux : log proxy, dashboard `workspace-claudish`, client via en-tête SSE). Le step final (PAYG direct) est **toujours servi** quand tout le reste est épuisé — l'agent ne meurt jamais, il dégrade avec notification.

## Pipeline de production

```
Client (Claude Code / Roo Code / bot)
  → parle le wire Anthropic (/v1/messages) OU OpenAI (/v1/chat/completions)
  → Claudish (proxy, po-2023:3000, derrière IIS models.myia.io)
    → route selon le modèle demandé (tier + cascade)
    → authentifie via x-api-key OU x-proxy-key (clé obligatoire depuis fork 2026-08)
    → traduit vers le wire du provider cible
    → publie des notices de dégradation sur 3 canaux si bascule
  → Provider (Anthropic natif / MiniMax-M3 / z.ai GLM / Qwen vLLM / DeepSeek PAYG)
  → réponse traduite en retour vers le wire Anthropic OU OpenAI
```

Claudish expose **deux formats wire** côté client :
- `/v1/messages` — wire Anthropic historique (Claude Code, Roo Code, bots Anthropic-natifs).
- `/v1/chat/completions` — wire OpenAI (GPT-5, Codex, routeurs tiers).

Côté sortie, il traduit vers le wire du provider cible (Anthropic natif, Anthropic-compatible comme MiniMax-M3, OpenAI-compatible comme z.ai GLM). Le **sidecar ai-01** (`192.168.0.46:3000`) relaie en LAN pour les agents distants.

L'authentification client→Claudish utilise `x-api-key` ou `x-proxy-key` (clé obligatoire, fork 2026-08). Aucune connexion anonyme tolérée.

## Documentation

| Document | Description |
|----------|-------------|
| [Claudish-Proxy.md](docs/Claudish-Proxy.md) | Le proxy en détail : principe wire, topologie hub + sidecars, router par rôle et substitution budgétaire annoncée, connecter un agent, avancées du fork, variables d'environnement, troubleshooting |
| [claudish.env.secrets.example](configs/claudish.env.secrets.example) | Template de configuration (placeholders uniquement — remplir avec vos valeurs) |

## Leçon fondatrice — le trick du nom Claude

Le pattern réutilisable pour connecter n'importe quel bot au cluster : **lui faire envoyer un nom de modèle Claude** (ex. `claude-sonnet-4-6`). Claudish remappe ce nom vers le modèle budgeté du tier (`glm-5.2` via le `modelMap` du profil actif). Une seule ligne de config côté bot, **aucun patch de wire**. Voir le détail et la leçon Hermes dans [docs/Claudish-Proxy.md §5](docs/Claudish-Proxy.md).

---

*Section Claudish — refonte 2026-08-18 (PR **#11555**). Le proxy multi-provider du cluster MyIA : un format wire en entrée (Anthropic ou OpenAI), trois tiers routés en cascade ordonnée (Anthropic / GLM-5.3 / MiniMax-M3 / Qwen / DeepSeek), bascule **notifiée** plutôt que silencieuse depuis le commit `823e614` (2026-08-12).*

## Écarts avec la version précédente (juin 2026)

Cette refonte corrige 8 écarts entre le README de juin et l'état réel du fork opérationnel au 2026-08-18 :

| Sujet | Ancienne lecture (juin) | État réel (fork 2026-08) |
|-------|--------------------------|--------------------------|
| Politique de bascule | « no-fallback », fail-hard | Cascade ordonnée + TTL `[10m,30m,1h,4h,24h]` + notices 3 canaux (commit `823e614`) |
| Tier Haiku | Qwen vLLM self-hosté | MiniMax-M3 nominal (Anthropic-compatible), cascade Qwen > DeepSeek |
| Tier Sonnet | z.ai GLM Coding Plan | GLM-5.3 (migration 14/08, commit `7b6db38`), DeepSeek PAYG en step 0 de failover |
| Tier Opus | Anthropic natif | Inchangé (natif, AUTO), cascade Qwen > GLM > DeepSeek |
| Auth | Non mentionnée | Clé obligatoire : `x-api-key` OU `x-proxy-key` (fork 2026-08) |
| Ingress | `/v1/messages` seul | `/v1/messages` ET `/v1/chat/completions` (wire OpenAI en entrée) |
| Topologie | Hub po-2023 derrière IIS | + sidecar ai-01 (`192.168.0.46:3000`) en relay LAN |
| Catalogue modèles | `glm-5.2`, Qwen | `MiniMax-M3`, `glm-5.3`, `deepseek-v4-flash`, `qwen3.8-max`, `claude-opus-5` |

Issue de référence : **#11555**.
