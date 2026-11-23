# Les fonctionnalités d'AI Engine, explorées par l'API

[← AI Engine (WordPress)](../README.md) | [↑ Plateformes conversationnelles](../../README.md) | [Instance jetable →](../instance-jetable/README.md)

Une plateforme conversationnelle se présente par ses écrans : une bulle de dialogue, un panneau de réglages, une liste d'outils. Ce niveau prend le plugin AI Engine par l'autre bout. Chaque carnet appelle réellement l'API d'une instance WordPress jetable, lit ce qu'elle répond et en tire une leçon réutilisable : où vit la configuration, qui a le droit d'appeler quoi, ce que le plugin fait vraiment d'une requête, et où s'arrête la version gratuite.

Les carnets s'adressent à qui administre ou intègre un site équipé d'AI Engine, à qui développe un agent ou une extension qui s'y branche, et à qui doit en auditer la sécurité. Il suffit de savoir lire du JSON et envoyer une requête HTTP en Python. L'instance est synthétique de bout en bout (la « Maison Valmont », maison d'édition fictive) et ses identifiants se lisent dans un fichier `.env` qui n'est jamais versionné.

Deux lectures cohabitent. Une **chaîne continue**, « AI Engine par son API », où chaque carnet reprend la question laissée ouverte par le précédent ; et des **compagnons autonomes**, qui approfondissent un point et se lisent seuls. Les sous-dossiers rangent les mêmes carnets par thème.

## Comment lire ce README

Les séries du dépôt se lisent à plusieurs vitesses, selon le principe décrit dans [« Choisir sa vitesse de lecture »](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture).

- Vous **découvrez** : suivez le parcours principal dans l'ordre des numéros ; les rangs 1 à 4 donnent déjà une vue complète du plugin.
- Vous **creusez un palier** : la section « Approfondissements » donne, pour chaque rang qui en a un, le compagnon qui le prolonge.
- Vous cherchez **un thème précis ou ce qui reste ouvert** : la section « Sous-séries » range les carnets par fonctionnalité, et « Pour aller plus loin » rassemble les frontières que les mesures ont tracées.

## Parcours principal

*Niveau Découverte pour les rangs 1 à 4, Approfondissement ensuite.* La chaîne se lit de haut en bas. Chaque ligne renvoie au README de la sous-série qui détaille le carnet.

| # | Notebook | Ce qu'on y apprend | Public | Pour approfondir |
|---|---|---|---|---|
| 1 | [Présenter AI Engine par son API](03-5-Multi-Provider/presenter-ai-engine-par-son-api.ipynb) | Le tour du plugin en quelques appels : routes par famille, chatbots, une première complétion réelle, outils MCP, formulaires. | Tout lecteur | [Multi-provider](03-5-Multi-Provider/README.md) |
| 2 | [Configurer et interroger des chatbots](03-1-Chatbots/configurer-chatbots-par-l-api.ipynb) | Le chatbot est un document JSON : le lire, le dupliquer, l'écrire sans écraser les autres, et mesurer ce que les instructions d'un persona changent réellement. | Administrateur, intégrateur | [Chatbots](03-1-Chatbots/README.md) |
| 3 | [Administrer les formulaires par l'API](03-2-Forms/administrer-les-formulaires-par-l-api.ipynb) | L'autre style d'API du plugin : le formulaire est un contenu WordPress, de la coquille en brouillon au rendu public, avec la frontière de la version gratuite mesurée sur ce rendu. | Administrateur, intégrateur | [Formulaires](03-2-Forms/README.md) |
| 4 | [Piloter WordPress par MCP](03-4-MCP-Server/piloter-wordpress-par-mcp.ipynb) | La face agent : WordPress comme serveur MCP, son catalogue d'outils, des appels réels en lecture puis en écriture, et le refus de tout appel non authentifié. | Développeur d'agents | [Serveur MCP](03-4-MCP-Server/README.md) |
| 5 | [Brancher plusieurs providers](03-5-Multi-Provider/brancher-plusieurs-providers-par-l-api.ipynb) | La régie des moteurs : environnements, matrice des usages, déclaration d'un moteur de secours, bascule et rétablissement. Et le piège de la série : une mise à jour partielle des réglages remplace tout. | Administrateur, intégrateur | [Multi-provider](03-5-Multi-Provider/README.md) |
| 6 | [Parler au chatbot en visiteur](03-1-Chatbots/parler-au-chatbot-en-visiteur-par-l-api.ipynb) | La face navigateur : une conversation sans compte, amorcée par un nonce. Un nonce n'est pas une authentification. | Développeur front, auditeur | [Chatbots](03-1-Chatbots/README.md) |
| 7 | [Obtenir des données structurées](03-1-Chatbots/obtenir-des-donnees-structurees-par-l-api.ipynb) | La case JSON que le rang 5 a laissée vide dans la matrice : la remplir, obtenir un JSON exploitable, puis mesurer l'honnêteté du résultat. | Intégrateur | [Chatbots](03-1-Chatbots/README.md) |
| 8 | [Le serveur MCP et son autorisation](03-4-MCP-Server/autour-du-consent-oauth-du-serveur-mcp.ipynb) | La question laissée par le rang 4 : comment un client tiers se connecte-t-il sans les clés de l'administrateur ? Le parcours OAuth complet, du premier refus à la révocation. | Administrateur, auditeur | [Serveur MCP](03-4-MCP-Server/README.md) |
| 9 | [L'assistant de l'éditeur](03-1-Chatbots/interroger-lassistant-de-lediteur-par-l-api.ipynb) | La quatrième face, celle de qui rédige : une route dont le contrat se découvre par les refus, et dont la réponse porte elle-même la frontière de la version gratuite. | Développeur d'extension | [Chatbots](03-1-Chatbots/README.md) |
| 10 | [Les fichiers du chatbot — une mémoire éphémère](03-1-Chatbots/donner-une-memoire-ephemere-au-chatbot-par-l-api.ipynb) | La surface des pièces jointes : dépôt, fiche, expiration, propriété par utilisateur, suppression. Le stockage est acquis ; reste son usage. | Intégrateur, auditeur | [Chatbots](03-1-Chatbots/README.md) |
| 11 | [Joindre un fichier au chatbot](03-1-Chatbots/joindre-un-fichier-au-chatbot-par-l-api.ipynb) | Ce qu'une complétion fait d'un fichier joint : ignoré, annoté puis écarté, ou réellement vu. | Intégrateur | [Chatbots](03-1-Chatbots/README.md) |

Au terme de la chaîne, le plugin apparaît sous quatre faces qui ne partagent ni leurs routes ni leurs clés : l'administrateur prouve une identité, l'agent prouve une délégation, le visiteur ne prouve rien et se trouve borné autrement, le rédacteur passe par la session de l'éditeur. Trois gestes reviennent d'un carnet à l'autre et valent au-delà de ce plugin : écrire par lecture-modification-écriture, découvrir un contrat par ses refus, mesurer par l'effet observable plutôt que par le code de retour.

## Approfondissements

*Niveau Approfondissement.* Les compagnons se lisent seuls ; chacun est rattaché ici au rang qu'il prolonge.

### Autour de 3 — la logique d'un formulaire

[Auditer un formulaire conditionnel](03-2-Forms/auditer-un-formulaire-conditionnel.ipynb) traite un formulaire dont les champs dépendent des réponses comme une machine à états : il en énumère les chemins, repère ceux qui appellent un modèle et détecte les champs qu'aucun chemin n'atteint. Il ne dépend d'aucun service, et déclare que la logique conditionnelle relève de l'offre payante du plugin.

### Autour de 4 — la qualité d'un catalogue d'outils

[Auditer un serveur MCP](03-4-MCP-Server/auditer-un-serveur-mcp.ipynb) mesure si un serveur expose les verbes du métier ou les tables de la base, sur le catalogue réel de l'instance et sur un catalogue d'atelier. Bibliothèque standard seule ; hors ligne sur le catalogue d'atelier.

### Autour de 5 — le choix du moteur

[Choisir le modèle derrière son chatbot](03-5-Multi-Provider/eval-choisir-son-modele.ipynb) remplace l'essai à la main par un banc de conformité rejouable : scénarios à assertion vérifiable, répétitions, verdicts. Prérequis en plus : un endpoint compatible OpenAI, par défaut le moteur de l'instance.

### Autour de 8 — deux serveurs devant un même agent

[Consommer et exposer le MCP](03-4-MCP-Server/consommer-vs-exposer-le-mcp.ipynb) fusionne le catalogue du site et celui d'un second serveur réel, puis mesure sur un modèle réel, avec répétitions et intervalles de confiance, quel outil l'agent choisit pour une tâche située à la frontière. Prérequis en plus : Node.js, le paquet Python `mcp`, deux moteurs locaux.

### Autour de 9 — la dérive d'une chaîne de réécritures

[Mesurer la dérive d'un copilot](03-1-Chatbots/mesurer-la-derive-dun-copilot.ipynb) montre qu'une validation humaine à chaque étape ne protège pas une chaîne de transformations : la dérive est cumulative. Modèle déterministe d'abord, mesure sur l'instance ensuite. Prérequis en plus : pour la dernière section, un moteur local qui sert la réécriture et les embeddings.

### Hors chaîne — préparer et cloisonner un corpus

Deux compagnons ne se rattachent à aucun rang, parce que la version gratuite du plugin n'ouvre aucune route pour indexer ou chercher des vecteurs. [Ingestion RAG d'un corpus long structuré](03-3-RAG-et-Embeddings/ingestion-corpus-long-rag.ipynb) montre que le découpage du corpus détermine la qualité de la recherche, quel que soit le modèle d'embeddings. [Séparer les environnements de vecteurs](03-3-RAG-et-Embeddings/separer-les-environnements-de-vecteurs.ipynb) montre que la séparation des vecteurs par environnement est un contrôle d'accès, et mesure sur un modèle déclaré la fuite et l'écrasement qu'entraîne son oubli.

## Sous-séries

*Niveau Découverte.* Chaque sous-série a son README, écrit dans la même forme que celui-ci.

- **[Chatbots](03-1-Chatbots/README.md)** — la bulle de dialogue démontée pièce par pièce : le chatbot comme document de configuration, les routes distinctes de l'administrateur, du visiteur et du rédacteur, les sorties structurées, et le cycle de vie des pièces jointes. Elle porte la plus grande part de la chaîne, et le compagnon sur la dérive.
- **[Formulaires](03-2-Forms/README.md)** — deux réalités d'un formulaire piloté par un modèle : un contenu WordPress qu'on administre de la création à la suppression, et une machine à états dont les chemins s'énumèrent.
- **[RAG et embeddings](03-3-RAG-et-Embeddings/README.md)** — les deux décisions que l'interface ne met pas en avant : comment découper le corpus avant de le vectoriser, et dans quel espace ranger les vecteurs. Les carnets séparent ce qui est démontré sur données synthétiques de ce qui est lu sur l'instance.
- **[Serveur MCP](03-4-MCP-Server/README.md)** — WordPress comme catalogue d'outils pour agents, pris par quatre côtés : le protocole, l'autorisation OAuth, la qualité de ce qui est exposé, et la cohabitation avec un second serveur.
- **[Multi-provider](03-5-Multi-Provider/README.md)** — le socle de la chaîne et la régie des moteurs : présentation du plugin, environnements et matrice d'usages, puis choix argumenté d'un modèle.

## Installation et prérequis

*Niveau Découverte.* Le montage de l'instance est décrit pas à pas dans son [README](../instance-jetable/README.md) : Docker, un WordPress local avec le plugin en version gratuite, un contenu synthétique, et un fichier `instance-jetable/.env` qui porte le port, les identifiants de test et l'adresse du moteur de langage. Aucune adresse ni clé n'est écrite dans un carnet.

| Ce qu'il faut | Pour quels carnets |
|---|---|
| L'instance jetable démarrée, Python 3.10 ou plus récent, `requests` et `python-dotenv` | Toute la chaîne, et les sections « instance » des compagnons |
| Un moteur de langage local compatible OpenAI | Rangs 1, 2, 6, 7, 9 et 11 ; le banc d'évaluation ; la dernière section de la mesure de dérive |
| Un modèle capable de lire une image | Rang 11, pour l'état « réellement vu » |
| Un moteur d'embeddings compatible OpenAI | La comparaison sur embeddings réels du carnet d'ingestion ; la dernière section de la mesure de dérive |
| Deux moteurs locaux, Node.js, le paquet `mcp` | [Consommer et exposer le MCP](03-4-MCP-Server/consommer-vs-exposer-le-mcp.ipynb) |
| `openai` et `pandas` | Le banc d'évaluation |
| `numpy`, `scikit-learn` | Les carnets RAG ; `numpy` pour la mesure de dérive |
| Aucun service | L'audit de formulaire conditionnel ; l'audit de serveur MCP sur son catalogue d'atelier ; les parties déterministes des carnets RAG et de la mesure de dérive |

Deux précautions. Suivez l'ordre de la chaîne à la première exécution : le rang 8 crée les comptes de test que les rangs 9 et 10 réutilisent. Et n'exécutez ces carnets que sur l'instance jetable : plusieurs écrivent dans la configuration, créent des contenus ou déposent des fichiers, puis remettent l'instance dans son état initial. Aucun GPU n'est requis par les carnets eux-mêmes ; le besoin en calcul est celui des moteurs que vous choisissez de servir.

## Pour aller plus loin

*Niveau Recherche.*

- **La frontière de la version gratuite** est mesurée, jamais supposée : le rendu des champs de formulaire, les actions de l'assistant de l'éditeur, l'indexation et la recherche de vecteurs relèvent de l'offre payante. Les carnets décrivent ce que l'API rend et s'arrêtent là ; le [cas d'usage éditorial](../04-Cas-Usage-livresagites/livresagites-parcours.md) décrit, sans exécution, une installation qui dispose de ces fonctions.
- **Ce que l'API ne voit pas.** Une valeur écrite par l'API peut être défaite par la simple ouverture d'un écran d'administration : le [parcours QA au navigateur](../05-Playwright-AI-Engine/README.md) le mesure, et l'[audit de conformité visuelle](../06-Securite-et-Methode/README.md) montre ce qu'un test de bon fonctionnement laisse passer.
- **Cadrer ce qu'un assistant a le droit de faire** ne se règle ni dans son prompt ni dans son catalogue seul : voir la note [Cadrer les agents](../../cadrer-les-agents.md) et le carnet [Différencier plusieurs assistants](../../differencier-les-assistants.ipynb).

## Ressources

- [Architecture en modules](../01-Architecture/architecture-en-modules.md) — la carte du plugin que ces carnets parcourent.
- [Comparatif Open WebUI et AI Engine](../02-Comparatif/comparatif-owui-vs-ai-engine.md) — les mêmes fonctions vues des deux plateformes.
- [Tour de la plateforme](../00-Tour-Plateforme/README.md) — les écrans d'administration correspondant à ces routes.
- [Instance jetable](../instance-jetable/README.md) — montage, maintenance et destruction de l'instance.
