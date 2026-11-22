# Open WebUI — la plateforme et son assurance qualité

[← Plateformes conversationnelles](../README.md) | [↑ Documentation GenAI](../../README.md) | [AI Engine (WordPress) →](../AI-Engine-WordPress/README.md)

Open WebUI est une application web libre qui pose une interface de conversation unique par-dessus des modèles de langage, qu'ils soient servis localement ou par un fournisseur distant. C'est une plateforme autonome, pas un composant ajouté à un site : elle porte ses propres comptes et ses propres rôles, affiche les réponses en flux, interroge des bases de connaissances, donne des outils aux modèles par le protocole MCP, ouvre des canaux de discussion partagés, et s'administre pour faire cohabiter plusieurs organisations sur une même infrastructure. Cette série l'aborde par deux côtés : comment on s'en sert, et comment on en garantit la qualité.

Elle s'adresse à qui découvre la plateforme — étudiant d'un cours qui y est hébergé, futur administrateur d'une instance — et à qui veut apprendre à tester de bout en bout une application d'IA générative. Le tour se lit sans prérequis technique ; la série de tests demande de savoir lire du TypeScript et du Python.

## Comment lire ce README

Les séries du dépôt se lisent à plusieurs vitesses, selon le principe décrit dans [« Choisir sa vitesse de lecture »](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture).

- Vous **découvrez** : suivez le parcours principal dans l'ordre ; le tour se lit sans rien installer.
- Vous **creusez un palier** : la section « Approfondissements » ajoute les schémas d'administration, la fabrication des captures, et les guides de la série de tests.
- Vous cherchez **ce qui reste ouvert** : « Pour aller plus loin » rassemble les questions que les deux parcours laissent au lecteur.

## Parcours principal

*Niveau Découverte pour l'étape 1, Découverte puis Approfondissement pour l'étape 2.* Chaque étape est un dossier, avec son propre README.

| # | Étape | Ce qu'on y apprend | Public | Pour approfondir |
|---|---|---|---|---|
| 1 | [Tour de la plateforme](00-Tour-Plateforme/README.md) | À quoi sert Open WebUI et comment on s'en sert, section par section : la connexion et la première vue, le chat avec ses modèles, son affichage en flux et ses pièces jointes, l'espace de travail où l'on crée des assistants, des prompts, des outils et des bases de connaissances, les canaux, les notes et les réglages, puis l'administration et le multi-tenant. Des exercices de manipulation jalonnent le parcours. | Toute personne qui découvre la plateforme ; la dernière section suppose un compte administrateur | [Architecture — administration et multi-tenant](00-Tour-Plateforme/architecture.md) |
| 2 | [Tests de bout en bout avec Playwright](Playwright-OWUI/README.md) | Tester cette même plateforme : choisir des sélecteurs robustes, réutiliser une session authentifiée, attendre et vérifier une réponse générée, écrire des tests conditionnels pour des fonctions que l'instance n'a pas toujours, tester l'API sans navigateur et l'isolation entre instances, puis trancher pour ou contre une mise en production. | Étudiant, développeur, testeur | [Carnet chapeau de la mission](Playwright-OWUI/00-Parcours-QA-OWUI.ipynb) |

Les deux étapes se répondent : le tour montre comment se servir d'une fonction, la série de tests vérifie qu'elle marche.

## Approfondissements

*Niveau Approfondissement.*

### Autour de 1 — l'administration par ses schémas, les captures par leur script

La page [Architecture — administration et multi-tenant](00-Tour-Plateforme/architecture.md) présente la face d'administration par des diagrammes plutôt que par des captures de panneaux réels : le déploiement multi-tenant, où chaque organisation a son application et sa base de données sur une infrastructure en partie mutualisée ; le contrôle d'accès, qui passe par des groupes plutôt que par des droits individuels ; le trajet d'un document jusqu'à sa citation par le modèle ; l'appel d'un outil par le protocole MCP. Tous les noms y sont génériques.

Les images du tour ne sont pas faites à la main. Le dossier [`capture/`](00-Tour-Plateforme/capture/README.md) contient le script Playwright qui les génère, avec un compte non administrateur et le masquage des zones sensibles ; le dossier [`assets/`](00-Tour-Plateforme/assets/README.md) dit quelle image illustre quelle section. Le script ne capture par défaut que les surfaces sans contenu réel, et se met en pause de lui-même tant que ses variables ne sont pas renseignées. Les surfaces qui exposeraient le contenu d'un établissement — listes de modèles, bases de connaissances, canaux — restent schématisées plutôt que capturées.

Prérequis en plus : pour régénérer les captures, Node.js, une instance et un compte non administrateur, déclarés par les variables `DEMO_OWUI_*` du gabarit `capture/.env.example`.

### Autour de 2 — lire un test rouge, suivre les versions

La série de tests s'accompagne de guides qui se lisent pour eux-mêmes. Le [guide de triage](Playwright-OWUI/TRIAGE-INFRA-VS-TEST.md) apprend à distinguer, devant un test qui échoue, une régression de l'application, une dérive du test et une panne d'infrastructure. Les notes de version — [v0.9.1](Playwright-OWUI/WHATS-NEW-v0.9.1.md), [v0.10](Playwright-OWUI/WHATS-NEW-v0.10.md), [v0.11](Playwright-OWUI/WHATS-NEW-v0.11.md) — disent pour chaque montée ce qui ne change pas, ce qui casse une suite de tests, et ce qu'on peut tester de nouveau.

Prérequis en plus : aucun pour ces lectures.

## Sous-séries

*Chaque dossier porte son propre niveau, rappelé dans son README.*

**[Tour de la plateforme](00-Tour-Plateforme/README.md).** Le parcours de découverte, côté utilisateur. Chaque section suit le même rythme : ce qu'est la fonction, comment s'en servir, une capture, et parfois un exercice. Le tour signale au fil des sections les apports de la ligne v0.10 — raisonnement affiché en direct, compaction du contexte, dossiers d'équipe, mémoire de l'assistant — que la série de tests reprend dans son module bonus. Sa dernière section, consacrée à l'administration, est volontairement schématisée.

**[Tests de bout en bout avec Playwright](Playwright-OWUI/README.md).** Une mission en plusieurs étapes : tenir le rôle d'ingénieur qualité d'une flotte d'instances, de la prise en main de l'outillage au verdict d'une montée de version. Chaque module réunit un fichier de tests TypeScript, qui est le moteur, et un carnet Jupyter, qui en est la couche pédagogique et s'exécute sans navigateur ni instance. Un carnet chapeau donne la carte de la mission et la grille de lecture d'un résultat.

La plateforme voisine de la famille est [AI Engine (WordPress)](../AI-Engine-WordPress/README.md), qui ajoute la couche conversationnelle à un site de contenu au lieu de la poser à côté. Le [comparatif](../AI-Engine-WordPress/02-Comparatif/comparatif-owui-vs-ai-engine.md) aligne les deux produits critère par critère.

## Installation et prérequis

*Niveau Découverte.*

| Ce qu'il faut | Pour quoi |
|---|---|
| Rien | Lire le tour, la page d'architecture, le guide de triage et les notes de version |
| Un compte sur une instance Open WebUI, celle du cours ou une instance locale | Refaire les manipulations et les exercices du tour |
| Python 3 et Jupyter | Lire et exécuter les carnets de la série de tests, qui n'utilisent que la bibliothèque standard |
| Node.js, le navigateur Chromium de Playwright, et un fichier `.env` copié de son gabarit | Exécuter les tests contre une instance ; le [README de la série](Playwright-OWUI/README.md#installation-et-prérequis) donne les commandes et les variables |
| Une seconde instance | Les tests d'isolation et le projet de certification de la série |

Aucun GPU n'est requis par ces supports : le besoin en calcul est celui du moteur de langage que sert l'instance.

## Sécurité — pas de secret dans les supports

*Niveau Découverte.* La règle vaut pour tout le dossier, comme pour le dossier AI Engine voisin.

- **Aucun secret exposé** : ni adresse sensible d'une instance réelle, ni adresse électronique nominative, ni clé d'API, ni jeton, ni mot de passe.
- **Des captures sans contenu réel** : elles sont produites par script, avec un compte non administrateur neuf, sur des invites fictives, avec le masquage des zones sensibles, et chaque image est relue avant d'être versionnée.
- **Aucun fichier `.env` versionné** : seuls les fichiers `.env.example` documentent les variables attendues, avec des valeurs neutres. L'état de session que Playwright sauvegarde, qui contient un jeton, est lui aussi ignoré par Git.

## Pour aller plus loin

*Niveau Recherche.*

- **Une plateforme autonome, ou une couche dans un site ?** Le [comparatif](../AI-Engine-WordPress/02-Comparatif/comparatif-owui-vs-ai-engine.md) ne désigne pas de vainqueur : il aide à dire quand l'une convient mieux que l'autre, et quand elles cohabitent.
- **Garantir la qualité d'une application non déterministe.** La série de tests pose la question sans la fermer : où s'arrête une assertion tolérante, et que vaut un test sauté ? Ses pistes sont dans la section « Pour aller plus loin » de [son README](Playwright-OWUI/README.md#pour-aller-plus-loin).
- **Ce qu'un assistant personnalisé a le droit de faire.** L'espace de travail permet de créer des assistants spécialisés par un prompt ; la note [Cadrer ce qu'un agent a le droit de faire](../cadrer-les-agents.md) explique pourquoi ce prompt n'est pas une frontière de sécurité.
- **L'infrastructure qui sert les modèles.** Le chapitre [LLMs locaux et serving](../../Texte/LLMs-Locaux-Serving/README.md) décrit ce qui tourne derrière le sélecteur de modèles.

## Ressources

- [Plateformes conversationnelles](../README.md) — la famille, et la plateforme voisine.
- [Parcours QA d'AI Engine](../AI-Engine-WordPress/05-Playwright-AI-Engine/README.md) — le pendant de la série de tests sur l'autre plateforme.
- [Dépôt d'Open WebUI](https://github.com/open-webui/open-webui) — le code et les notes de version de la plateforme.
- [Documentation de Playwright](https://playwright.dev/) — la référence de l'outil de test.
- [Spécification du protocole MCP](https://modelcontextprotocol.io) — la référence du protocole.
