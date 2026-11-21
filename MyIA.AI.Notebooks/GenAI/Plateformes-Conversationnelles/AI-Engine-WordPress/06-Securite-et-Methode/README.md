# Sécurité et méthode

[← AI Engine (WordPress)](../README.md) | [↑ Plateformes conversationnelles](../../README.md) | [Instance jetable →](../instance-jetable/README.md)

La sécurité n'est pas ici un chapitre de plus : c'est une contrainte de méthode qui s'applique à tous les supports consacrés à AI Engine. Ce dossier en tient les deux volets. Le premier est une règle de publication : aucun secret, aucune donnée réelle, aucune capture d'une installation réelle. Le second est un carnet qui enseigne à se méfier d'une vérification qui passe : il mesure ce qu'un test de structure ne voit pas quand un agent a modifié le rendu d'une page.

Il s'adresse à qui déploie ou relit des pages qu'un assistant a générées ou retouchées, et à qui contribue à ces supports. Il faut savoir lire du Python et avoir une notion de HTML et de CSS ; aucune pratique préalable de Playwright n'est supposée.

## Comment lire ce README

Les séries du dépôt se lisent à plusieurs vitesses, selon le principe décrit dans [« Choisir sa vitesse de lecture »](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture).

- Vous **découvrez** : lisez la règle de publication, puis le parcours principal.
- Vous **creusez un palier** : la section « Approfondissements » détaille les détecteurs du carnet et ce que chacun voit.
- Vous cherchez **ce qui reste ouvert** : « Pour aller plus loin » reprend les exercices du carnet et la question de l'auto-certification.

## Pas de secret dans les supports

*Niveau Découverte.* La règle vaut pour tout le dossier AI Engine, comme pour le dossier Open WebUI voisin.

- **Aucun secret exposé** : ni adresse d'administration, ni clé d'API, ni jeton, ni identifiant WordPress. Les fichiers `.env` ne sont jamais versionnés ; seuls les fichiers `.env.example` documentent les variables attendues.
- **Aucune capture d'une installation réelle.** Un écran d'administration expose son contexte — compte connecté, domaines, extensions installées — quelle que soit la page affichée, et une capture retouchée n'est pas vérifiable par le lecteur. Les seules captures du dossier sont celles du [tour de la plateforme](../00-Tour-Plateforme/README.md), produites par script sur l'instance jetable, dont le contenu est entièrement synthétique. La [note de méthode du cas d'usage éditorial](../04-Cas-Usage-livresagites/livresagites-parcours.md#note-de-méthode--pourquoi-il-ny-a-aucune-capture) détaille l'arbitrage.
- **Aucun contenu privé** : le cas d'usage éditorial est décrit à un niveau architectural (structures, comptages, familles d'outils), jamais avec les contenus du site observé — ni texte, ni nom de personne, ni titre d'ouvrage.
- **Aucune donnée personnelle** : le dossier applique la posture du dépôt public décrite dans [`PRIVACY.md`](../../../../../PRIVACY.md).

## Parcours principal

*Niveau Approfondissement.* Le dossier tient en un carnet.

| # | Notebook | Ce qu'on y apprend | Public | Pour approfondir |
|---|---|---|---|---|
| 1 | [Auditer la conformité visuelle](auditer-la-conformite-visuelle.ipynb) | Écrire une charte graphique comme des données, puis montrer sur des pages publiques de l'instance qu'un test de structure — la page répond, son contenu principal n'est pas vide, un élément d'action existe — reste vert sur des pages au rendu cassé. Bâtir un détecteur par classe de défaut, sur le style que le navigateur calcule réellement, et croiser les sondes dans une matrice : quelle sonde voit quel défaut. | Intégrateur, testeur, relecteur de pages générées par un assistant | [Parcours QA — ce que l'API ne voit pas](../05-Playwright-AI-Engine/00-Parcours-QA-AI-Engine.ipynb) |

La question du carnet n'est pas « ces pages sont-elles conformes ? » : leur conformité est connue d'avance. C'est la sonde qui est la variable, et la leçon tient en une phrase : un test de structure mesure le contenant, pas la conformité du rendu.

## Approfondissements

*Niveau Approfondissement.*

### Autour de 1 — un détecteur par classe de défaut

Le corpus mêle deux familles de pages : des pages publiques de l'instance telles que le thème les rend, et des pages que le carnet crée lui-même par l'API REST de WordPress — une référence conforme, et des pages portant chacune un seul défaut délibéré. Les défauts sont injectés là où les styles vivent, dans les attributs de style des blocs, comme les poserait un assistant qui régénère un gabarit. Les détecteurs ne lisent jamais le HTML source : ils interrogent le rendu calculé par un vrai navigateur.

Trois détecteurs répondent chacun à une classe de défaut.

- **Le contraste**, selon le ratio de luminance défini par les règles d'accessibilité WCAG et son seuil AA de 4,5 pour du texte courant. Le doré d'accent de la charte, employé pour un paragraphe sur fond blanc, donne 2,24 : nettement sous le seuil.
- **La dominance des couleurs par défaut d'un framework**, témoin d'un style importé plutôt que tiré de la charte. Le détecteur compare les couleurs réellement affichées à une liste de couleurs guettées, et le carnet discute ce que ce choix laisse passer.
- **L'affordance des appels à l'action** : un lien qui devrait se présenter comme un bouton et n'en a ni la classe ni le fond.

La matrice finale montre que le test de structure passe sur toutes les pages, que chaque page défectueuse est attrapée par un seul des trois détecteurs, et qu'aucun détecteur ne suffit seul. Le carnet rattache ce résultat à l'étude de cas [Quand la vérification est verte et le système est cassé](../../../../../docs/reference/verification-verte-systeme-casse.md), dont il met en forme exécutable la classe de « la sonde qui mesure le contenant ». Il accompagne le parcours 1 du [cas d'usage éditorial](../04-Cas-Usage-livresagites/livresagites-parcours.md), consacré à l'assistant de l'éditeur, et fait pendant au carnet [Mesurer la dérive d'un copilot](../03-Functional/03-1-Chatbots/mesurer-la-derive-dun-copilot.ipynb), qui mesure la perte d'information là où celui-ci mesure le rendu.

Prérequis en plus : aucun au-delà de ceux du carnet.

## Installation et prérequis

*Niveau Découverte.*

- **L'instance jetable « Maison Valmont »** démarrée et son fichier `instance-jetable/.env` renseigné : le [README de l'instance](../instance-jetable/README.md) donne le montage, le port et la création du mot de passe d'application que le carnet lit dans ce fichier.
- **Python 3.10 ou plus récent** avec `requests`, `python-dotenv` et `playwright`, puis le navigateur piloté : `playwright install chromium`.
- **Aucun moteur de langage, aucun GPU** : le carnet mesure des styles calculés, pas une réponse générée.

Le carnet crée des pages publiques sur l'instance pour constituer son corpus. Exécutez-le sur l'instance jetable, jamais sur un site en service.

## Pour aller plus loin

*Niveau Recherche.*

- **Un agent peut-il certifier son propre rendu ?** Le carnet répond non, pour deux raisons : un agent optimise ce qu'on mesure, et la conformité visuelle suppose une charte déclarée et des détecteurs que l'agent n'embarque pas. La note [Cadrer les agents](../../cadrer-les-agents.md) reprend la question du côté de l'autorité qu'on délègue.
- **Les trois exercices du carnet** prolongent les détecteurs : situer chaque couleur fautive dans son contexte, produire un rapport agrégé par page, et nommer le défaut que masque un test de structure vert.
- **Transposer la matrice à un projet réel** : écrire la charte en données, dénombrer les classes de défaut observées, nommer la question exacte à laquelle chaque sonde existante répond, puis écrire une sonde par classe. Le carnet déroule cette transposition dans sa dernière section.
- **Les autres classes de vérification trompeuse** sont cataloguées dans l'[étude de cas](../../../../../docs/reference/verification-verte-systeme-casse.md) ; le [Parcours QA](../05-Playwright-AI-Engine/README.md) en explore une autre, celle de l'observation unique d'un phénomène qui dépend d'une course.

## Ressources

- [Tour de la plateforme](../00-Tour-Plateforme/README.md) — les captures reproductibles de l'instance jetable, et la section de sécurité qui les accompagne.
- [Cas d'usage éditorial](../04-Cas-Usage-livresagites/livresagites-parcours.md) — les parcours observés sur une installation réelle, décrits sans capture.
- [Règles pour l'accessibilité des contenus web (WCAG)](https://www.w3.org/TR/WCAG22/) — la référence du seuil de contraste.
- [Documentation de Playwright pour Python](https://playwright.dev/python/) — la référence de l'outil.
