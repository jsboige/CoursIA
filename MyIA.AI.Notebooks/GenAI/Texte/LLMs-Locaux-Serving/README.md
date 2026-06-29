# LLMs Locaux en Production — Journal de bord d'un fork vLLM

[← Texte](../README.md) | [↑ ..](../README.md)

**Cette section raconte l'histoire du backend d'inférence** qui héberge les modèles de langage locaux du parcours : un fork de [vLLM](https://docs.vllm.ai) tournant sur 3 cartes RTX 4090, qui expose des endpoints compatibles OpenAI pour les notebooks Texte, les assistants de code, et l'orchestration multi-agents. Quatorze mois d'évolution — la valse des modèles, les batailles de quantification, une saga de cache KV, des impasses documentées — condensés en un récit d'ingénierie de production.

> **Sources** : [vllm-project/vllm](https://github.com/vllm-project/vllm) (moteur d'inférence amont, Apache 2.0) · [Qwen](https://qwen.ai) (famille de modèles Qwen3.x) · [Sandermage/genesis-vllm-patches](https://github.com/Sandermage/genesis-vllm-patches) (arbre de patches downstream *Genesis* v7.72.x, auteur **Sandermage**, mai 2026 — adopté pour débloquer TurboQuant sur architecture hybride). Confirmation croisée du correctif par l'utilisateur `xyehya` dans [vllm#41726](https://github.com/vllm-project/vllm/issues/41726).

## Pourquoi ce chapitre ?

Tout le parcours GenAI parle de *modèles* : générer une image, raisonner avec un LLM, orchestrer des agents. Mais derrière les notebooks « LLMs locaux » de cette série Texte, derrière l'intégration des assistants de code en mode auto-hébergé, il y a une **machine** et un **serveur d'inférence** qui doivent tenir la charge d'une classe entière. Ce serveur ne tombe pas du ciel : il est le produit de quatorze mois de choix, de mesures, et — surtout — d'échecs documentés.

L'idée directrice, répétée à chaque étape : **un endpoint LLM de production auto-hébergé est un arbitrage permanent entre quatre grandeurs en tension — débit, longueur de contexte, qualité, et VRAM.** On ne maximise jamais les quatre à la fois. Tout le métier consiste à choisir, mesurer, et documenter le compromis.

| Sans ce backend | Avec ce backend |
|-----------------|-----------------|
| Dépendance à une API tierce payante par token | Modèle illimité sur GPU maison, coût marginal nul |
| Données envoyées hors site | Inférence 100 % locale, rien ne sort |
| Pas de contrôle sur le modèle / la version | Choix du modèle, de la quantification, du contexte |
| Capacité figée | Arbitrage débit/contexte ajusté au workload réel |

## Place dans l'écosystème

Ce backend est le **fournisseur de modèles locaux** du cluster. Il complète les autres briques du parcours :

| Brique | Rôle | Lien |
|--------|------|------|
| Notebooks Texte (LocalLlama, Quantization, Production Patterns) | *Démontrent* l'usage d'un LLM local | [9](../9_Production_Patterns.ipynb) · [10](../10_LocalLlama.ipynb) · [11](../11_Quantization.ipynb) |
| [Claudish](../../Vibe-Coding/Claudish/README.md) | Route le tier « Haiku » des assistants de code vers… ce backend vLLM | wire Anthropic → OpenAI |
| [Open WebUI](../../Open-WebUI/README.md) | Expose le modèle aux utilisateurs finaux (multi-tenant) | UI + RAG |
| Ce backend (cette section) | **Sert le modèle qui alimente les trois précédents** | endpoints OpenAI-compat |

Autrement dit : quand un notebook Texte interroge un « LLM local », quand Claudish route une requête de code vers son tier gratuit, ou quand un étudiant chatte dans Open WebUI, c'est *ce serveur* qui répond.

## Documentation

| Document | Description |
|----------|-------------|
| [docs/journal-de-bord.md](docs/journal-de-bord.md) | Le récit complet : le décor matériel, les origines et un incident de sécurité, la valse des modèles et le cimetière des rejetés, les batailles d'ingénierie (quantification, cache KV, graphes CUDA, échantillonnage), la saga TurboQuant→Genesis, les impasses documentées, et les leçons transférables. |

## Leçon fondatrice — les quatre grandeurs en tension

Le réflexe à emporter de tout ce chapitre : **débit, contexte, qualité, VRAM ne se maximisent pas ensemble.** Sur du matériel grand public (Ada Lovelace, pas du datacenter), la VRAM est la ressource rare et la génération de la carte décide de ce qui est *possible*, pas seulement de ce qui est *rapide*. Le bon compromis dépend du **workload réel** — beaucoup d'utilisateurs en contexte long n'appelle pas les mêmes leviers qu'un mono-utilisateur qui décode vite. Et documenter une configuration *rejetée* vaut autant que documenter celle qui tourne : elle empêche de refaire dix fois la même expérience.

---

*Section LLMs Locaux en Production — Juin 2026. Le backend d'inférence du cluster MyIA : un fork vLLM sur 3× RTX 4090, quatorze mois d'arbitrages débit/contexte/qualité/VRAM, et un serveur qui répond aujourd'hui en MoE quantifié avec deux millions de tokens de contexte.*
