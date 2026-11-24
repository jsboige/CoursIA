# Plateformes conversationnelles — choisir son interface GenAI

[← Documentation GenAI](../README.md) | [Open WebUI →](Open-WebUI/README.md) | [AI Engine (WordPress) →](AI-Engine-WordPress/README.md)

Une plateforme conversationnelle est un produit déployable qui pose une couche de conversation — chat, recherche sur un corpus, outils, assistants — par-dessus des modèles de langage. Cette famille en présente deux, qui répondent à deux terrains : Open WebUI, une plateforme autonome qu'on héberge soi-même, et AI Engine, une extension qui ajoute cette couche à l'intérieur d'un site WordPress. Elle enseigne à s'en servir, à les piloter et à les tester, à choisir entre elles, puis à concevoir les assistants qu'on y déclare : ce que chacun a le droit de faire, et s'il se distingue réellement des autres.

Elle s'adresse à qui doit choisir, administrer ou intégrer une telle plateforme, à qui veut apprendre à tester une application d'IA générative, et à qui conçoit un catalogue d'assistants. Les tours, le comparatif et la note de conception se lisent sans prérequis technique ; les carnets demandent de savoir lire du Python, du JSON et une requête HTTP.

La famille est nommée par ce qu'elle fait, comme les autres séries de la documentation GenAI, et non par un produit : le bon choix dépend du terrain, pas d'un classement.

## Comment lire ce README

Les séries du dépôt se lisent à plusieurs vitesses, selon le principe décrit dans [« Choisir sa vitesse de lecture »](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture).

- Vous **découvrez** : suivez le parcours principal dans l'ordre ; chaque plateforme commence par un tour qui se lit sans rien installer.
- Vous **creusez un palier** : la section « Approfondissements » ajoute le comparatif des deux plateformes et le détail des deux questions de conception.
- Vous cherchez **ce qui reste ouvert** : « Pour aller plus loin » rassemble ce que la famille mesure sans le trancher.

## Parcours principal

*Niveau Découverte pour les étapes 1 et 2, par leurs tours ; Approfondissement pour les étapes 3 et 4.* Les deux premières étapes sont des dossiers, avec leur propre README.

| # | Étape | Ce qu'on y apprend | Public | Pour approfondir |
|---|---|---|---|---|
| 1 | [Open WebUI](Open-WebUI/README.md) | Une plateforme autonome, vue par ses deux côtés : comment on s'en sert, dans un tour guidé de ses fonctions, et comment on en garantit la qualité, dans une série de tests de bout en bout avec Playwright. | Utilisateur, futur administrateur, testeur | [Tests de bout en bout avec Playwright](Open-WebUI/Playwright-OWUI/README.md) |
| 2 | [AI Engine (WordPress)](AI-Engine-WordPress/README.md) | La couche conversationnelle ajoutée à un site de contenu : le tour de l'interface, la carte du plugin, son pilotage par l'API sur une instance jetable, puis ce qu'un navigateur constate et que l'API ne voit pas. | Administrateur ou intégrateur d'un site, développeur d'agents | [Les fonctionnalités par l'API](AI-Engine-WordPress/03-Functional/README.md) |
| 3 | [Cadrer ce qu'un agent a le droit de faire](cadrer-les-agents.md) | Séparer trois questions qu'on confond — à quoi l'assistant sert, ce qu'il peut proposer d'appeler, si l'appel a le droit d'aboutir — et apparier le mécanisme de cadrage à ce que coûte une erreur. | Concepteur d'assistants, administrateur | [Comparatif des deux plateformes](AI-Engine-WordPress/02-Comparatif/comparatif-owui-vs-ai-engine.md) |
| 4 | [Différencier plusieurs assistants](differencier-les-assistants.ipynb) | Mesurer si des assistants déclarés comme spécialisés le sont dans leurs réponses : un protocole de sondes, une métrique naïve et ce qu'elle ne permet pas de décider, puis un test qui demande si l'on retrouve l'auteur d'une réponse dont on a caché l'étiquette. | Concepteur d'assistants | [Cadrer ce qu'un agent a le droit de faire](cadrer-les-agents.md) |

Les étapes 3 et 4 forment une paire, et se posent à l'identique sur les deux plateformes : ce que chaque assistant a le droit de faire, et qui il est réellement.

## Approfondissements

*Niveau Approfondissement.*

### Autour de 2 — choisir entre les deux plateformes

Le [comparatif](AI-Engine-WordPress/02-Comparatif/comparatif-owui-vs-ai-engine.md) aligne les deux produits critère par critère : positionnement, fonctionnalités, RAG et embeddings, protocole MCP, extensibilité, sécurité et déploiement, coût. Il ne classe pas un produit au-dessus de l'autre — ils visent des usages différents et cohabitent souvent — mais aide à dire quand l'un convient mieux à un projet donné, avec trois cas : choisir l'un, choisir l'autre, les faire cohabiter. Il se termine par ses limites connues.

Prérequis en plus : aucun.

### Autour de 3 — trois couches, et une seule qui tient

La note [Cadrer ce qu'un agent a le droit de faire](cadrer-les-agents.md) part d'une situation courante : un catalogue d'outils, plusieurs assistants, et la volonté qu'un assistant spécialisé ne déclenche pas les opérations d'un autre domaine. Elle distingue l'intention, portée par le prompt système ; la portée, fixée par le catalogue d'outils attaché ; l'autorité, vérifiée au moment de l'appel. Sa règle : ne jamais faire porter à une couche une garantie qui appartient à une couche plus profonde. Le cloisonnement par persona n'est donc pas une frontière de sécurité.

La note compare ce que chaque plateforme prend en charge nativement de la troisième couche, donne un critère de décision — une action réversible se cadre par l'intention, une action irréversible par l'autorité — et fournit la manipulation qui permet de le vérifier sur son propre déploiement : comparer ce qu'un assistant déclare à ce que le point d'accès expose réellement.

Prérequis en plus : aucun pour la lecture ; un accès d'administration à une plateforme pour refaire le relevé.

### Autour de 4 — ce que la mesure montre

Le carnet [Différencier plusieurs assistants](differencier-les-assistants.ipynb) travaille sur un atelier d'écriture fictif. Parmi ses assistants, deux sont des contrôles placés exprès : une paraphrase d'un autre assistant, et un assistant du même terrain qui adopte une posture différente. Les sondes sont volontairement ambiguës, pour que chaque assistant puisse y révéler son angle.

- **Le recouvrement lexical classe, mais ne décide pas.** Il place bien la paire redondante en tête ; faute de valeur de référence, il ne dit pas si cet écart est grand.
- **La discriminabilité vient avec son repère.** On retire une réponse, on demande à quel assistant elle ressemble le plus, et on compare au hasard. Dans la sortie enregistrée, l'exactitude vaut 0,47 contre 0,17 pour le hasard.
- **Un score agrégé ne suffit pas.** La matrice de confusion montre que la paraphrase et son modèle sont systématiquement pris l'un pour l'autre : deux étiquettes, un assistant. Le second contrôle n'est pas reconnu non plus, mais ses réponses se dispersent : ce n'est pas un échange, c'est une absence de signature propre.
- **La distance entre prompts n'est pas la distance entre réponses.** La paire dont les prompts n'ont presque aucun mot commun est celle dont les réponses se ressemblent le plus. On n'audite pas un catalogue d'assistants en relisant leurs prompts : il faut les faire parler.

Le carnet précise que ses valeurs ne se transportent pas d'un modèle à l'autre : ce qu'il transmet est le protocole et la forme des signaux.

Prérequis en plus : un point d'accès compatible OpenAI servant un modèle de chat, et les paquets `openai` et `numpy`. La collecte des réponses prend quelques minutes.

## Sous-séries

*Chaque dossier porte son propre niveau, rappelé dans son README.*

**[Open WebUI](Open-WebUI/README.md).** Une application web libre qui porte ses propres comptes et ses propres rôles, affiche les réponses en flux, interroge des bases de connaissances, donne des outils aux modèles par le protocole MCP et s'administre pour plusieurs organisations. Le dossier l'aborde par un tour de la plateforme, côté utilisateur, puis par une série de tests où chaque module réunit un fichier de tests et un carnet qui en est la couche pédagogique ; la série suit une mission d'ingénieur qualité et se termine par le verdict d'une montée de version. La règle « pas de secret dans les supports » y est posée pour tout le dossier.

**[AI Engine (WordPress)](AI-Engine-WordPress/README.md).** Plutôt que de poser une plateforme de chat à côté d'un site, on ajoute la couche conversationnelle dans le site lui-même. Le dossier enseigne à quoi ressemble le plugin, comment il est découpé, ce que son API répond réellement, ce qu'un navigateur constate et que l'API ne voit pas, et ce qu'une installation en service en fait. Ses carnets partagent un terrain commun, une instance jetable au contenu entièrement synthétique ; aucun ne s'adresse à un site en service.

## Installation et prérequis

*Niveau Découverte.*

| Ce qu'il faut | Pour quoi |
|---|---|
| Rien | Lire les tours, le comparatif et la note de conception |
| Python 3.10 ou plus récent, avec `openai` et `numpy` | Exécuter le carnet [Différencier plusieurs assistants](differencier-les-assistants.ipynb) |
| Un point d'accès compatible OpenAI servant un modèle de chat, déclaré par les variables d'environnement `COURSIA_LLM_BASE_URL`, `COURSIA_LLM_API_KEY` et `COURSIA_LLM_MODEL` | Ce même carnet : aucune clé n'y est écrite |
| Une instance Open WebUI et Node.js | Les tests de la série Open WebUI ; son [README](Open-WebUI/README.md#installation-et-prérequis) détaille les besoins |
| Docker, et l'instance jetable du dossier AI Engine | Les carnets de ce dossier ; son [README](AI-Engine-WordPress/README.md#installation-et-prérequis) détaille les besoins |

Aucun GPU n'est requis par les supports eux-mêmes : le besoin en calcul est celui du moteur de langage que vous servez. Aucun fichier `.env` n'est versionné ; seuls les gabarits `.env.example` documentent les variables attendues.

## Pour aller plus loin

*Niveau Recherche.*

- **Distinguable ne veut pas dire bon.** Le carnet de l'étape 4 le dit lui-même : des assistants distincts et tous médiocres obtiendraient un excellent score. La distinctivité est une condition nécessaire, jamais suffisante.
- **Une mesure lexicale.** Le test de discriminabilité voit des mots, pas du sens. Le carnet indique la suite : remplacer la pondération lexicale par des embeddings, sans changer le protocole.
- **L'autorité, plateforme par plateforme.** La note de l'étape 3 relève ce que chaque plateforme impose nativement et ce qu'elle laisse à l'auteur d'un outil. Refaire ce relevé sur son propre déploiement est la seule façon de s'en servir.
- **Des vérifications vertes qui ne prouvent rien.** Les deux plateformes en donnent des exemples, par leurs tests de navigateur ; l'étude de cas [Quand la vérification est verte et le système est cassé](../../../docs/reference/verification-verte-systeme-casse.md) en catalogue les classes.
- **Étendre la famille.** Elle est nommée pour accueillir une troisième plateforme sans réécriture : un nouveau dossier voisin, et un comparatif étendu.

## Ressources

- [Documentation GenAI](../README.md) — les autres séries d'IA générative du dépôt.
- [Catalogue du cours](../../../COURSE_CATALOG.generated.md) — l'inventaire à jour des carnets, série par série.
- [Comparatif des deux plateformes](AI-Engine-WordPress/02-Comparatif/comparatif-owui-vs-ai-engine.md) — le tableau structuré.
- [Spécification du protocole MCP](https://modelcontextprotocol.io) — la référence du protocole que les deux plateformes parlent.
