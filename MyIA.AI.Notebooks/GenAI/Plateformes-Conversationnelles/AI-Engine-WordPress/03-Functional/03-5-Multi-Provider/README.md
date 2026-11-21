# Multi-provider — le socle de la série et le choix du moteur

[← Les fonctionnalités par l'API](../README.md) | [↑ AI Engine (WordPress)](../../README.md) | [Instance jetable →](../../instance-jetable/README.md)

Derrière un chatbot, il y a un moteur de langage, et ce moteur se choisit. Cette sous-série montre où le plugin range ses branchements vers les moteurs, comment on en déclare un second sans abîmer le premier, et comment décider lequel mettre en service. Elle ouvre aussi la chaîne « AI Engine par son API » : son premier carnet fait le tour du plugin en quelques appels et pose la méthode que tous les autres reprennent — appeler une route, lire le JSON rendu, en tirer une leçon réutilisable.

Elle s'adresse à qui administre ou intègre un site WordPress équipé d'AI Engine, et à qui veut comprendre une plateforme conversationnelle par ce qu'elle répond plutôt que par ses écrans. Il suffit de savoir lire du JSON et envoyer une requête HTTP en Python ; aucune pratique de WordPress n'est supposée.

## Comment lire ce README

Les séries du dépôt se lisent à plusieurs vitesses, selon le principe décrit dans [« Choisir sa vitesse de lecture »](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture).

- Vous **découvrez** : lisez le parcours principal, en commençant par la présentation du plugin.
- Vous **creusez un palier** : la section « Approfondissements » prolonge le branchement d'un moteur par la question du choix du modèle.
- Vous cherchez **ce qui reste ouvert** : « Pour aller plus loin » dit ce que la version gratuite ne laisse pas mesurer et où la série reprend la question.

## Parcours principal

*Niveau Découverte.* Les numéros sont les rangs des carnets dans la chaîne « AI Engine par son API », dont l'ordre complet figure dans le [README parent](../README.md) ; les rangs intermédiaires se lisent dans les sous-séries voisines.

| # | Notebook | Ce qu'on y apprend | Public | Pour approfondir |
|---|---|---|---|---|
| 1 | [Présenter AI Engine par son API](presenter-ai-engine-par-son-api.ipynb) | Faire le tour du plugin en six appels : identité du site, catalogue des routes `mwai/v1` rangé par famille, chatbots configurés, une complétion réelle avec son décompte de tokens, outils exposés aux agents par MCP, formulaires. Lire une réponse vide (`forms: []`) comme « rien en service » et non comme une panne. | Tout lecteur de la série : c'est le point d'entrée de la chaîne | Chaque famille de routes a sa sous-série : [chatbots](../03-1-Chatbots/README.md), [formulaires](../03-2-Forms/README.md), [serveur MCP](../03-4-MCP-Server/README.md) |
| 5 | [Brancher plusieurs providers](brancher-plusieurs-providers-par-l-api.ipynb) | Lire la configuration du plugin comme un seul document : les environnements (`ai_envs`, dont le type `custom` pour tout serveur compatible OpenAI) et la matrice qui associe à chaque usage — chat, vision, images, audio, JSON, embeddings — un environnement et un modèle. Interroger un provider (catalogue de modèles, poignée de main, échec propre sur un environnement inexistant). Déclarer un environnement de secours, y basculer l'usage chat, vérifier, puis tout rétablir. | Administrateur ou intégrateur qui doit ajouter ou changer un moteur | [Choisir le modèle derrière son chatbot](eval-choisir-son-modele.ipynb) |

Le carnet 5 porte la leçon la plus coûteuse de la série : la route `settings/update` ne met pas à jour, elle **remplace**. Un envoi partiel efface ce qu'il ne nomme pas. Le carnet le démontre sans risque (instantané, envoi partiel, constat du dégât, restauration) et en tire le geste que tous les carnets d'écriture reprennent : lire l'ensemble, modifier la copie, renvoyer l'ensemble. Il ne lance aucune complétion ; ses sorties mesurent une structure, pas un texte généré.

## Approfondissements

*Niveau Approfondissement.*

### Autour de 5 — choisir le moteur qu'on branche

[Choisir le modèle derrière son chatbot](eval-choisir-son-modele.ipynb) remplace l'impression laissée par trois questions posées à la main par un banc de conformité fonctionnelle. Quatre propriétés qu'un chatbot de site exige sont mesurées : refuser quand la réponse n'est pas dans le contexte fourni, rendre un JSON strict, rester dans la langue de la question, émettre un appel d'outil structuré plutôt que d'en parler. Chaque scénario porte une assertion vérifiable par code et se rejoue plusieurs fois, ce qui distingue une propriété acquise d'une propriété instable.

Le carnet ajoute deux choses au parcours principal. D'abord une mise en garde de méthode : un budget de tokens partagé avec le raisonnement du modèle peut rendre des réponses vides, et un verdict qui accusait le modèle venait alors du banc lui-même. Ensuite une table de transposition, qui fait correspondre à chaque verdict le levier de plateforme qui le corrige. Ce n'est ni un benchmark de performance ni une évaluation complète : quelques scénarios et des validateurs heuristiques donnent un premier filtre, rejouable quand le modèle change.

Prérequis en plus : un endpoint compatible OpenAI. Sans réglage particulier, le banc vise le moteur que sert l'instance jetable ; les variables `EVAL_BASE_URL`, `EVAL_API_KEY` et `EVAL_MODEL` (gabarit : [`.env.example`](../../.env.example)) le dirigent vers un autre.

## Installation et prérequis

*Niveau Découverte.*

- **L'instance jetable « Maison Valmont »** : un WordPress local sous Docker, avec le plugin en version gratuite et un contenu synthétique. Son [README](../../instance-jetable/README.md) donne le montage pas à pas, le port et les variables du fichier `instance-jetable/.env` que les carnets chargent. Aucune adresse ni clé n'est écrite dans un carnet.
- **Un moteur de langage local compatible OpenAI**, déclaré dans ce même `.env` : la présentation obtient une complétion réelle, et le banc d'évaluation l'interroge à répétition.
- **Python 3.10 ou plus récent** avec `requests` et `python-dotenv` ; le banc d'évaluation demande en plus `openai` et `pandas`.
- **Aucun GPU n'est requis par les carnets eux-mêmes** : le besoin en calcul est celui du moteur local que vous choisissez de servir.

Le carnet 5 écrit dans la configuration de l'instance puis la rétablit. Exécutez-le sur l'instance jetable, jamais sur un site en service.

## Pour aller plus loin

*Niveau Recherche.*

- **Ce que l'instance ne branche pas.** Un seul environnement sert réellement le chat sur l'instance jetable ; pour les autres usages, la matrice affiche le repli du plugin, pas un branchement. Les environnements d'embeddings sont déclarés, mais la version gratuite n'ouvre aucune route pour indexer ou chercher : la sous-série [RAG et embeddings](../03-3-RAG-et-Embeddings/README.md) mesure cette frontière et travaille la question avec un moteur d'embeddings interrogé directement.
- **La case JSON de la matrice** est vide au départ ; le carnet [Obtenir des données structurées](../03-1-Chatbots/obtenir-des-donnees-structurees-par-l-api.ipynb) la remplit par le même geste d'écriture et mesure ce que la route rend.
- **Choisir un modèle ne dit pas quoi lui laisser faire.** La note [Cadrer les agents](../../../cadrer-les-agents.md) sépare l'intention, la portée et l'autorité d'un assistant, sur les deux plateformes de la famille.

## Ressources

- [Architecture en modules](../../01-Architecture/architecture-en-modules.md) — où se place le branchement des moteurs dans le plugin.
- [Comparatif Open WebUI et AI Engine](../../02-Comparatif/comparatif-owui-vs-ai-engine.md) — la même question du multi-provider vue des deux plateformes.
- [Les fonctionnalités par l'API](../README.md) — l'ordre complet de la chaîne et les autres sous-séries.
