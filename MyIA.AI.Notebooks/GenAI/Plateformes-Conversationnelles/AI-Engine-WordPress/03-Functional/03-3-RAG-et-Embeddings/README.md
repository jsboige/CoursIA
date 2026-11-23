# RAG et embeddings — découper un corpus, cloisonner ses vecteurs

[← Les fonctionnalités par l'API](../README.md) | [↑ AI Engine (WordPress)](../../README.md) | [Instance jetable →](../../instance-jetable/README.md)

Faire répondre un chatbot à partir des documents d'un site suppose deux décisions que l'interface ne met pas en avant : comment on découpe le corpus avant de le vectoriser, et dans quel espace on range les vecteurs obtenus. Cette sous-série traite les deux. Elle montre qu'un découpage aveugle à la structure des ouvrages dégrade la recherche quel que soit le modèle d'embeddings, et qu'une séparation des vecteurs par environnement est un contrôle d'accès, pas un rangement.

Elle s'adresse à qui prépare un corpus pour un assistant documentaire, et à qui doit garantir qu'un visiteur ne reçoit pas un contenu réservé. Il faut savoir lire du Python et avoir une idée de ce qu'est une recherche par similarité ; la série [RAG et mémoire sémantique](../../../../RAG-et-Memoire-Semantique/README.md) du dépôt en pose les bases.

## Comment lire ce README

Les séries du dépôt se lisent à plusieurs vitesses, selon le principe décrit dans [« Choisir sa vitesse de lecture »](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture).

- Vous **découvrez** : lisez le parcours principal ; le premier carnet se suit sans aucun service.
- Vous **creusez un palier** : la section « Approfondissements » relie chaque carnet à ce qui le prolonge ailleurs dans le dépôt.
- Vous cherchez **ce qui reste ouvert** : « Pour aller plus loin » dit ce que la version gratuite du plugin ne laisse pas exécuter sur l'instance.

## Parcours principal

*Niveau Approfondissement.* Les deux carnets sont autonomes : ils ne font pas partie de la chaîne numérotée « AI Engine par son API » présentée dans le [README parent](../README.md). Les numéros ci-dessous donnent seulement l'ordre de lecture conseillé dans ce dossier.

| # | Notebook | Ce qu'on y apprend | Public | Pour approfondir |
|---|---|---|---|---|
| 1 | [Ingestion RAG d'un corpus long structuré](ingestion-corpus-long-rag.ipynb) | Comparer, sur un catalogue synthétique d'ouvrages découpés en chapitres, un découpage à taille fixe avec recouvrement et un découpage qui suit la structure et attache à chaque fragment son ouvrage, son chapitre et sa position. Le découpage naïf mélange des thèmes aux frontières et interdit tout filtrage ; le découpage structuré n'en mélange aucun. La comparaison se joue d'abord en TF-IDF, puis se rejoue sur des embeddings réels : changer de modèle d'embeddings ne répare pas un mauvais découpage. | Qui prépare un corpus pour un assistant documentaire | Le découpage d'un texte continu, dans [le carnet RAG de la série Texte](../../../../Texte/05_RAG_Modern.ipynb) |
| 2 | [Séparer les environnements de vecteurs](separer-les-environnements-de-vecteurs.ipynb) | Deux défaillances d'un magasin de vecteurs partagé entre plusieurs régimes d'accès, rendues mesurables sur un modèle déclaré : la fuite (une recherche sans filtre d'environnement ramène des fragments d'un autre régime) et l'écrasement silencieux (une réindexation lancée sans environnement cible remplace un corpus voisin). Deux métriques à surveiller en découlent : le taux de fuite et le compte de fragments par environnement avant et après réindexation. | Administrateur, auditeur de sécurité | La recherche et le filtrage par métadonnées sur un magasin de vecteurs, dans [le premier carnet de RAG et mémoire sémantique](../../../../RAG-et-Memoire-Semantique/01-Hands-On-Grounding.ipynb) |

Les deux carnets séparent nettement deux niveaux de preuve. Ce qui tient à la méthode — le découpage, la fuite, l'écrasement — est démontré sur des données synthétiques, de façon déterministe. Ce qui tient à la plateforme est lu sur l'instance jetable et affiché tel quel, y compris quand le résultat est une absence.

## Approfondissements

*Niveau Approfondissement.*

### Autour de 1 — d'où viennent les vecteurs

Le carnet d'ingestion consacre une section à la jonction entre le plugin et le moteur : ce que le plugin déclare (module d'embeddings, environnements), ce que l'API gratuite expose, et ce que le moteur sait encoder. Ces trois réponses ne se confondent pas, et la section les mesure une à une. Elle reprend la frontière constatée par [Brancher plusieurs providers](../03-5-Multi-Provider/brancher-plusieurs-providers-par-l-api.ipynb) : des environnements d'embeddings déclarés, mais aucune route gratuite pour y indexer ou y chercher.

Prérequis en plus : pour cette section et pour la comparaison sur embeddings réels, l'instance jetable et un moteur qui répond sur une route d'embeddings compatible OpenAI. Sans eux, la comparaison en TF-IDF reste la référence du carnet.

### Autour de 2 — une séparation qui est un contrôle d'accès

Le carnet sur les environnements ouvre par trois lectures réelles de l'instance (les environnements listés dans les options, la bascule du module d'embeddings et son rétablissement, l'identifiant d'environnement par défaut) et par une absence mesurée : la version gratuite n'offre aucune route pour créer, indexer ou interroger un environnement. Le reste du carnet est donc un modèle déclaré, construit avec `numpy` et une graine fixe, où chaque chiffre cité figure dans une sortie enregistrée. Il prolonge le parcours 2 du [cas d'usage éditorial](../../04-Cas-Usage-livresagites/livresagites-parcours.md), où ces deux défaillances ont été observées sur une installation réelle.

Prérequis en plus : l'instance jetable pour les trois lectures d'ouverture ; `numpy` seul pour le modèle.

## Installation et prérequis

*Niveau Découverte.*

- **Python 3.10 ou plus récent** avec `numpy` et `scikit-learn` : c'est tout ce qu'il faut pour la comparaison des découpages en TF-IDF et pour le modèle de fuite et d'écrasement.
- **L'instance jetable « Maison Valmont »** pour les lectures de plateforme : son [README](../../instance-jetable/README.md) donne le montage, le port et les variables du fichier `instance-jetable/.env`. Les carnets affichent quel fichier `.env` ils ont chargé.
- **Un moteur d'embeddings compatible OpenAI** pour rejouer la comparaison sur des vecteurs réels. Son adresse se lit dans les fichiers `.env` de la série, jamais dans un carnet.
- **Aucun GPU n'est requis par les carnets eux-mêmes** : le besoin en calcul est celui du moteur d'embeddings que vous servez.

Le carnet sur les environnements bascule un réglage du plugin puis le rétablit. Exécutez-le sur l'instance jetable, jamais sur un site en service.

## Pour aller plus loin

*Niveau Recherche.*

- **L'indexation et la recherche par le plugin lui-même** ne sont pas exécutables par l'API gratuite : la série mesure cette frontière et ne décrit pas le comportement de l'offre payante. Les deux métriques du carnet 2 sont proposées comme instrumentation à poser sur une installation qui dispose de ces fonctions.
- **Le filtrage a posteriori** que les métadonnées rendent possible est l'objet du troisième exercice du carnet d'ingestion ; le [premier carnet de RAG et mémoire sémantique](../../../../RAG-et-Memoire-Semantique/01-Hands-On-Grounding.ipynb) en est le pendant sur un magasin de vecteurs.
- **Un fichier joint n'est pas un corpus indexé** : le carnet [Joindre un fichier au chatbot](../03-1-Chatbots/joindre-un-fichier-au-chatbot-par-l-api.ipynb) montre qu'un texte joint à une conversation n'entre pas dans le prompt.

## Ressources

- [Les fonctionnalités par l'API](../README.md) — l'ordre de la chaîne et les autres sous-séries.
- [Comparatif Open WebUI et AI Engine](../../02-Comparatif/comparatif-owui-vs-ai-engine.md#rag-et-embeddings) — le RAG vu des deux plateformes.
- [Cas d'usage éditorial](../../04-Cas-Usage-livresagites/livresagites-parcours.md) — le RAG sur corpus et le piège du multi-environnement.
