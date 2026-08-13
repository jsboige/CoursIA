# Plateformes conversationnelles — choisir son interface GenAI

[← Documentation GenAI](../README.md)

> **Catégorie fonctionnelle.** Ce dossier regroupe les **plateformes GenAI
> réelles** — des produits déployables, pas des démonstrations jouet — qui
> apportent une couche de conversation (chat, RAG, outils, agents) par-dessus
> des modèles de langage. Toutes les autres sous-séries de `GenAI/` sont
> nommées par **fonction** (`Image`, `Audio`, `Texte`, `RAG-et-Memoire-Semantique`…) ;
> celle-ci suit la même convention : elle est nommée par ce qu'elle *fait*
> (héberger des plateformes conversationnelles), pas par un produit.

---

## Pourquoi une catégorie plutôt qu'un produit

Les plateformes conversationnelles ne se réduisent pas à Open WebUI. Selon le
terrain — un serveur auto-hébergé, un site WordPress existant, une boutique
WooCommerce — l'interface GenAI la plus adaptée diffère. Cette catégorie
présente **deux plateformes** comme **sœurs**, chacune détaillée dans son propre
dossier ; le [`comparatif-owui-vs-ai-engine.md`](comparatif-owui-vs-ai-engine.md)
vit **au niveau catégorie** parce qu'un comparatif ne doit pas être rangé à
l'intérieur de l'un des deux objets qu'il compare.

## Les deux plateformes

| Plateforme | Terrain | Angle | Dossier |
|------------|---------|-------|---------|
| **Open WebUI** | Serveur auto-hébergé, multi-tenant | Comment *utiliser* et *tester* une plateforme GenAI de bout en bout | [`Open-WebUI/`](Open-WebUI/README.md) |
| **AI-Engine (WordPress)** | Site de contenu WordPress existant | Ajouter la couche GenAI *dans* un CMS plutôt qu'à côté | [`AI-Engine-WordPress/`](AI-Engine-WordPress/README.md) |

### [Open WebUI](Open-WebUI/README.md)

Interface de chat LLM open-source, auto-hébergée, multi-tenant : authentification
et rôles, streaming, RAG sur bases de connaissances, outils et serveurs MCP,
génération d'images, synthèse et reconnaissance vocale. Deux parcours la
couvrent : un **tour guidé** de la plateforme et une **série QA Playwright**
qui la teste de bout en bout.

➡️ **[Ouvrir le dossier Open-WebUI](Open-WebUI/README.md)**

### [AI-Engine (WordPress)](AI-Engine-WordPress/README.md)

L'extension WordPress de Jordy Meow, présentée comme **presqu'équivalente d'Open
WebUI côté site de contenu**. Plutôt que de poser Open WebUI *à côté* d'un
WordPress existant, AI-Engine ajoute la couche GenAI directement dans le CMS —
chatbots, Copilot pour l'éditeur Gutenberg, AI Forms, RAG sur le contenu du
site, et **WordPress comme serveur MCP**. Le projet **livresagités** sert de
terrain d'observation (sans contenu privé reproduit).

➡️ **[Ouvrir le dossier AI-Engine-WordPress](AI-Engine-WordPress/README.md)**

---

## Comparatif

Le tableau structuré [`comparatif-owui-vs-ai-engine.md`](comparatif-owui-vs-ai-engine.md)
synthétise les différences fonctionnelles (chat, RAG, multi-provider, MCP,
extensions). Il ne **classe pas** un produit au-dessus de l'autre — OWUI et
AI-Engine ciblent des usages différents et cohabitent souvent — mais aide à
décider **quand l'un est plus adapté que l'autre** pour un projet donné.

---

## Conception

Une fois la plateforme choisie, les deux mêmes questions se posent de part et
d'autre, et elles forment une paire : **ce que chaque assistant a le droit de
faire**, et **qui il est réellement**.

### Ce qu'il a le droit de faire

[`cadrer-les-agents.md`](cadrer-les-agents.md) distingue les trois couches qu'on
confond habituellement — l'intention (prompt système), la portée (catalogue
attaché) et l'autorité (vérification au moment de l'appel) — montre pourquoi le
cloisonnement par persona n'est **pas** une frontière de sécurité, et donne le
critère de décision : on apparie le mécanisme à la **réversibilité de l'action**.
Le document compare ce que chaque plateforme prend en charge nativement de la
troisième couche, et fournit la manipulation permettant de le vérifier sur son
propre déploiement.

### Qui il est

[`differencier-les-assistants.ipynb`](differencier-les-assistants.ipynb) traite
l'autre moitié. Déclarer quatre assistants spécialisés ne les rend pas
distincts : le prompt porte une intention, la spécialisation est une propriété
des sorties. Le notebook construit la mesure — une batterie de sondes ambiguës,
puis un test de discriminabilité qui demande si l'on peut retrouver l'auteur
d'une réponse dont on a caché l'étiquette.

Il est monté autour de deux contrôles placés exprès dans l'atelier, et le second
donne le résultat le plus utile : une paraphrase stricte s'effondre — les deux
assistants sont systématiquement pris l'un pour l'autre — tandis qu'un assistant
partageant le **même terrain** mais adoptant une **posture** différente reste
largement distinguable. Ce qu'un modèle restitue le plus fidèlement d'un prompt
système est la position adoptée, pas le domaine annoncé.

---

## Étendre la catégorie

La catégorie est nommée pour accueillir sans réécriture un troisième membre :
une interface comme **LibreChat**, **AnythingLLM** ou **Flowise** trouverait sa
place ici comme nouveau dossier sœur, avec le comparatif mis à jour au niveau
catégorie.
