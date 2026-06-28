# Claudish — Proxy Multi-Provider pour Assistants de Code

[← Vibe-Coding](../README.md) | [↑ ..](../README.md)

**Claudish** est le proxy/routeur qui rend les assistants de vibe-coding — **Claude Code**, **Roo Code**, les bots autonomes (Hermes, NanoClaw) — **agnostiques du fournisseur de modèles**. Au lieu de parler en dur à `api.anthropic.com`, le client s'adresse à Claudish, qui traduit la requête vers le provider choisi selon le coût, la capacité et le quota : **Anthropic natif**, **z.ai/GLM**, ou **Qwen self-hosté**.

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

## Écosystème à 3 tiers (no-fallback)

Le déploiement MyIA budgete **un provider unique par tier** — pas de bascule silencieuse entre providers en plein milieu d'une conversation (ce qui dégraderait la qualité et le coût de façon imprévisible).

| Tier | Usage | Provider réel | Raison du choix |
|------|-------|---------------|-----------------|
| **Opus** | Réflexion lourde, architecture | Anthropic natif | Meilleur raisonnement |
| **Sonnet** | Usage courant, code | z.ai GLM Coding Plan | Coût/capacité optimisé |
| **Haiku** | Rapide, léger, illimité | Qwen vLLM self-hosté | Gratuit, local, sur GPU maison |

Sur un burst (rate-limit), Claudish **backoff** puis réessaie le **même** provider. Sur une panne franche, il **fail-hard** (erreur explicite) — il ne bascule **jamais** vers un autre provider en silence. Mieux vaut une erreur visible qu'une dérive cachée.

## Pipeline de production

```
Client (Claude Code / Roo Code / bot)
  → parle le wire Anthropic (/v1/messages)
  → Claudish (proxy, po-2023:3000, derrière IIS models.myia.io)
    → route selon le modèle demandé (tier)
    → traduit vers le wire du provider cible
  → Provider (Anthropic / z.ai GLM / Qwen vLLM)
  → réponse traduite en retour vers le wire Anthropic
```

Claudish expose l'API Anthropic à l'identique (`/v1/messages`) côté client — **rien ne change** dans le code de l'assistant. Côté sortie, il traduit vers le wire du provider cible (OpenAI, Gemini, Anthropic natif, Ollama).

## Documentation

| Document | Description |
|----------|-------------|
| [Claudish-Proxy.md](docs/Claudish-Proxy.md) | Le proxy en détail : principe wire, topologie de déploiement, router 3 tiers, connecter un agent, avancées du fork, variables d'environnement, troubleshooting |
| [claudish.env.secrets.example](configs/claudish.env.secrets.example) | Template de configuration (placeholders uniquement — remplir avec vos valeurs) |

## Leçon fondatrice — le trick du nom Claude

Le pattern réutilisable pour connecter n'importe quel bot au cluster : **lui faire envoyer un nom de modèle Claude** (ex. `claude-sonnet-4-6`). Claudish remappe ce nom vers le modèle budgeté du tier (`glm-5.2` via le `modelMap` du profil actif). Une seule ligne de config côté bot, **aucun patch de wire**. Voir le détail et la leçon Hermes dans [docs/Claudish-Proxy.md §5](docs/Claudish-Proxy.md).

---

*Section Claudish — Juin 2026. Le proxy multi-provider du cluster MyIA : un format wire en entrée, trois providers budgetés en sortie, jamais de bascule silencieuse.*
