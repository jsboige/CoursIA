# Formulaires — un contenu qu'on administre, une machine à états qu'on audite

[← Les fonctionnalités par l'API](../README.md) | [↑ AI Engine (WordPress)](../../README.md) | [Instance jetable →](../../instance-jetable/README.md)

Un formulaire piloté par un modèle de langage paraît simple : des champs, une réponse générée. Cette sous-série en montre deux réalités moins visibles. Côté administration, le formulaire n'est pas une ligne dans une table mais un contenu WordPress, avec son brouillon, sa publication et son rendu public. Côté conception, un formulaire dont les champs dépendent des réponses précédentes se comporte comme une machine à états, dont les chemins ne se lisent pas sur le schéma : ils s'énumèrent.

Elle s'adresse à qui administre des formulaires sur un site équipé d'AI Engine, et à qui en conçoit ou en audite. Le premier carnet de la chaîne, [Présenter AI Engine par son API](../03-5-Multi-Provider/presenter-ai-engine-par-son-api.ipynb), est le prérequis du parcours principal ; l'approfondissement se lit seul, avec des bases de Python.

## Comment lire ce README

Les séries du dépôt se lisent à plusieurs vitesses, selon le principe décrit dans [« Choisir sa vitesse de lecture »](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture).

- Vous **découvrez** : lisez le parcours principal, qui suit un formulaire de sa création à sa suppression.
- Vous **creusez un palier** : la section « Approfondissements » passe de l'administration à l'audit de la logique conditionnelle.
- Vous cherchez **ce qui reste ouvert** : « Pour aller plus loin » dit ce que la version gratuite ne permet pas de mesurer sur l'instance.

## Parcours principal

*Niveau Découverte.* Le numéro est le rang du carnet dans la chaîne « AI Engine par son API », dont l'ordre complet figure dans le [README parent](../README.md).

| # | Notebook | Ce qu'on y apprend | Public | Pour approfondir |
|---|---|---|---|---|
| 3 | [Administrer les formulaires par l'API](administrer-les-formulaires-par-l-api.ipynb) | Le cycle de vie d'un formulaire par les routes `forms` : la création rend une coquille en brouillon, le contenu s'écrit ensuite, la publication se vérifie par relecture. Le rendu public passe par un shortcode posé sur une page, contrôlé en visiteur anonyme. La mesure situe la frontière de la version gratuite : elle rend du contenu, pas des champs de saisie. Le carnet supprime ce qu'il a créé. | Administrateur ou intégrateur | [Auditer un formulaire conditionnel](auditer-un-formulaire-conditionnel.ipynb) |

Le carnet distingue deux choses qu'un code de retour confond : une écriture acceptée et un état obtenu. Chaque écriture est suivie d'une relecture, et le rendu public se mesure dans le fragment de page que le shortcode a produit, pas dans la page entière. Aucun modèle de langage n'est appelé.

## Approfondissements

*Niveau Approfondissement.*

### Autour de 3 — la logique conditionnelle comme machine à états

[Auditer un formulaire conditionnel](auditer-un-formulaire-conditionnel.ipynb) prend un formulaire synthétique de dépôt de manuscrit dont la visibilité des champs dépend des réponses, et le traite comme un graphe d'états. Il énumère les chemins réellement atteignables, repère ceux qui déclenchent un appel au modèle — le coût caché du formulaire — et détecte les champs qu'aucun chemin n'atteint. Les trois grandeurs s'obtiennent par énumération, pas par simulation, et aucune ne se lit sur la liste des champs.

Le carnet ne dépend d'aucun service : ni réseau, ni modèle, ni clé. Il le dit d'emblée, parce que les champs conditionnels relèvent de l'offre payante du plugin : le formulaire étudié est une transcription déclarée, et ce qui est enseigné est la structure du comportement, pas une mesure prise sur l'instance. Il prolonge le parcours 4 du [cas d'usage éditorial](../../04-Cas-Usage-livresagites/livresagites-parcours.md).

Prérequis en plus : aucun service ; savoir lire un dictionnaire Python et suivre une énumération de cas.

## Installation et prérequis

*Niveau Découverte.*

- **Pour le rang 3** : l'instance jetable « Maison Valmont » démarrée et son fichier `instance-jetable/.env` renseigné ([README de l'instance](../../instance-jetable/README.md)) ; Python 3.10 ou plus récent avec `requests` et `python-dotenv`. Aucun moteur de langage n'est sollicité.
- **Pour l'approfondissement** : Python seul, sans instance ni réseau.

Le rang 3 crée un formulaire et une page, puis les supprime : l'instance se retrouve dans l'état où elle était. Exécutez-le sur l'instance jetable, jamais sur un site en service.

## Pour aller plus loin

*Niveau Recherche.*

- **Les champs générés par un modèle** (saisie dynamique, validation, conditions) ne sont pas rendus par la version gratuite. La série mesure cette absence par le rendu public et ne décrit pas ce qu'elle n'a pas pu observer.
- **Transposer l'audit à un formulaire réel** suppose d'en extraire le schéma des conditions : le carnet d'approfondissement liste les limites à garder en tête avant cette transposition.
- **Un formulaire qui appelle un modèle pose la question du format de sortie** : voir [Obtenir des données structurées](../03-1-Chatbots/obtenir-des-donnees-structurees-par-l-api.ipynb).

## Ressources

- [Les fonctionnalités par l'API](../README.md) — l'ordre complet de la chaîne et les autres sous-séries.
- [Architecture en modules](../../01-Architecture/architecture-en-modules.md) — la place des formulaires dans le plugin.
- [Cas d'usage éditorial](../../04-Cas-Usage-livresagites/livresagites-parcours.md) — le formulaire comme machine à états, observé sur une installation réelle.
