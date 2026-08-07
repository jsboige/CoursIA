# Cas d'usage livresagités — AI-Engine en contexte éditorial

[← README AI-Engine-WordPress](README.md) | [← Comparatif OWUI vs AI-Engine](comparatif-owui-vs-ai-engine.md)

> Le projet **livresagités** est une installation WordPress de
> **maison d'édition** : soumission de manuscrits, comité de lecture,
> catalogue de livres vendus, et une couche GenAI (chatbots + RAG +
> serveur MCP) posée par-dessus. Il sert ici de **terrain
> d'observation réel** pour AI-Engine, à un niveau architectural et
> fonctionnel.
>
> **Aucune donnée du site n'est reproduite** : ni contenu de
> manuscrit, ni nom de personne, ni titre d'ouvrage, ni identifiant,
> ni capture d'écran. Ce qui est transmis ici, ce sont les *formes
> d'intégration* et les *chiffres de structure* — voir la
> [note de méthode](#note-de-méthode--pourquoi-il-ny-a-aucune-capture)
> qui explique pourquoi il n'y a pas d'illustration.

---

## Contexte

L'erreur d'intuition la plus commune sur AI-Engine est de le ranger
au rayon « plugin de blog ». L'installation observée ici est
l'inverse d'un blog personnel : c'est un **système multi-rôles avec
un workflow métier**.

- Plusieurs **rôles distincts** : autrices qui déposent un
  manuscrit, comité de lecture qui l'évalue, éditrices qui
  arbitrent, clients qui achètent.
- Un **pipeline documentaire** : dépôt d'un fichier, extraction du
  texte, découpage en chunks, indexation vectorielle, pré-lecture
  assistée par LLM, notification.
- Un **catalogue e-commerce** (WooCommerce) adossé au même
  WordPress, donc des produits, des commandes, des stocks.
- Des **agents conversationnels** différenciés selon la surface du
  site où ils apparaissent.

L'enjeu GenAI n'est donc pas « assister un auteur qui rédige » mais
**outiller une chaîne de production éditoriale** — ce qui déplace
complètement le centre de gravité du parcours. C'est pour cette
raison que le cas est intéressant pédagogiquement : il montre
AI-Engine là où on ne l'attend pas.

**Ordres de grandeur mesurés sur l'installation** (relevés
directement sur l'instance, voir [Métriques](#métriques-relevées)) :
AI-Engine Pro 3.4.1, **88 outils MCP exposés**, **6 environnements
d'embeddings** coexistants, ~1600 vecteurs indexés.

---

## Parcours 0 — L'architecture en modules

Avant les parcours fonctionnels, un point de structure qui n'est
documenté nulle part clairement et qui conditionne la lecture du
reste : **AI-Engine n'est pas un bloc**. Son tableau de bord
présente trois familles de modules activables indépendamment.

| Famille | Modules | Ce qu'elle décide |
|---------|---------|-------------------|
| **Client** | Chatbot, Forms, Search | Ce que voit le **visiteur** du site |
| **Server** | Insights, Knowledge, Orchestration, Finetunes, Moderation, Assistants | Ce que le **serveur** sait faire (RAG, MCP sortant, logs, modération) |
| **Admin** | Advisor, AI Assistant, Generators (texte / image / vidéo), Playground, Utilities, Transcription | Ce que voit l'**administrateur** dans `wp-admin` |

Deux conséquences pratiques :

1. Un déploiement minimal (chatbot public seul) n'active qu'un
   module Client — l'empreinte du plugin est modulable, contrairement
   à ce que suggère la longue liste de fonctionnalités commerciales.
2. Le module **Orchestration** est la face *cliente* de MCP :
   c'est lui qui permet à AI-Engine de **consommer** des serveurs MCP
   externes. Le serveur MCP *exposé* par WordPress est une mécanique
   distincte (voir Parcours 3). Les deux sens du protocole ne se
   configurent pas au même endroit — confusion fréquente.

---

## Parcours 1 — Copilot pour l'éditeur WordPress

### Ce que c'est

AI-Engine ajoute un panneau **Copilot** dans l'éditeur Gutenberg de
WordPress. Le rédacteur écrit un brouillon ; le Copilot propose :

- **Résumé** d'un texte long en un paragraphe (meta description,
  Open Graph).
- **Enhancement** stylistique (clarifier, reformuler, ton).
- **Traduction** avec préservation du registre.
- **Rewriting** d'un paragraphe en plusieurs variantes, sans
  remplacer l'original.
- **Génération d'image d'en-tête** à partir d'un prompt court.
- **Alt text automatique** pour les images insérées.

### Comment ça marche

Le rédacteur écrit dans Gutenberg comme d'habitude ; le panneau
Copilot appelle AI-Engine qui route vers le provider sélectionné.
Le résultat apparaît dans une zone de prévisualisation ; le
rédacteur *valide* ou *rejette* l'insertion. Aucune réécriture
automatique — le brouillon reste sous contrôle humain.

### Comparaison OWUI

Open WebUI **n'a pas d'équivalent** : il n'intègre aucun CMS. Le
parcours équivalent supposerait d'exporter le texte, de le coller
dans OWUI, puis de réimporter le résultat à la main. Sur ce *type
d'usage précis*, l'intégration au CMS est l'avantage décisif.

### Ce que l'installation observée en fait

Peu de choses, et c'est un enseignement en soi. Dans une maison
d'édition, le texte de valeur est le **manuscrit**, qui n'entre pas
par Gutenberg mais par un formulaire de dépôt, et qui n'a pas
vocation à être réécrit par un LLM. Le Copilot y sert pour les
contenus *périphériques* (pages de présentation, descriptions de
catalogue), pas pour le cœur éditorial.

> **Leçon transposable.** La fonctionnalité la plus mise en avant
> par un éditeur de plugin n'est pas nécessairement celle qui porte
> la valeur dans un déploiement donné. Cartographier les *flux de
> texte réels* avant de choisir les modules à activer.

---

## Parcours 2 — RAG sur corpus, et le piège du multi-environnement

### Ce que c'est

AI-Engine ingère du contenu dans un vector store, puis permet à un
chatbot de répondre en s'appuyant sur ce corpus. Cinq backends sont
supportés (Chroma, Qdrant, Pinecone, OpenAI Vector Store, **base
WordPress interne**).

### Comment ça marche

**Ingestion** (déclenchée par bouton admin, par cron, ou par un hook
sur la sauvegarde d'un contenu) :

1. Extraction du contenu principal (hors menus, sidebars, footer).
2. Découpage en chunks.
3. Génération d'un embedding par chunk.
4. Stockage embedding + métadonnées dans le vector store.

**Requête** (à chaque message du chatbot) :

1. La question est embedée avec le même modèle.
2. Top-K chunks les plus proches (K paramétrable par chatbot).
3. Mode de recherche sélectionné (Simple, Context-Aware, Smart).
4. Le contexte enrichi part au LLM avec une consigne de type
   « réponds à partir du contexte ; si l'information n'y est pas,
   dis-le ».

### Le point non documenté : plusieurs environnements coexistent

Sur l'installation observée, les vecteurs ne forment **pas** un
corpus unique. Ils sont répartis en **six environnements
d'embeddings** distincts, séparés par une colonne d'identifiant
d'environnement en base. Chaque chatbot pointe vers l'environnement
qui le concerne.

C'est la bonne façon de faire, et elle est contre-intuitive : le
réflexe est d'indexer « tout le site » dans un seul index. Or les
corpus n'ont ni le même public ni le même régime de confidentialité
— du contenu catalogue destiné aux visiteurs ne doit pas cohabiter
dans le même espace de recherche que du contenu réservé à un comité
interne. **La séparation par environnement est un contrôle d'accès,
pas une commodité d'organisation.**

Corollaire opérationnel, appris à ses dépens : une réindexation
lancée sans préciser l'environnement cible écrase un corpus voisin.
Sur une instance servant du contenu en ligne, la perte est immédiate
et silencieuse.

### Comparaison OWUI

Open WebUI a une pile RAG équivalente (**Knowledge** : upload de
documents, hybrid search, injection dans le prompt système). La
différence est l'**intégration native au contenu** : AI-Engine
resynchronise ses chunks quand un contenu est modifié, via les hooks
WordPress ; OWUI demanderait un re-upload.

En revanche, la notion d'**environnements multiples** au sein d'une
même instance est plus explicite côté AI-Engine, où elle est un
champ de configuration de premier niveau.

---

## Parcours 3 — WordPress comme serveur MCP métier

C'est le parcours le plus intéressant du dossier, et celui qu'on
sous-estime le plus.

### Ce que c'est

AI-Engine expose l'installation WordPress comme **serveur MCP**, sur
un endpoint REST authentifié par jeton Bearer. Un agent externe
(Claude Code, Claude Desktop, ChatGPT, OpenClaw) reçoit le catalogue
d'outils et pilote le site par conversation, sans glue code.

### Le catalogue réellement exposé

Relevé sur l'installation, l'endpoint retourne **88 outils**, qui se
répartissent en deux couches très différentes :

| Couche | Nombre | Préfixe | Nature |
|--------|--------|---------|--------|
| Natifs WordPress | 37 | `wp_*` | Posts, users, comments, media, taxonomies, options |
| Natifs WooCommerce | 25 | `wc_*` | Produits, commandes, stocks, clients, avis, rapports de vente |
| Natifs AI-Engine | 2 | `mwai_*` | Vision, génération d'image |
| **Métier, développés pour le site** | **24** | `livresagites_*` | **Verbes du domaine éditorial** |

Les 64 outils natifs sont du **CRUD générique** : ils décrivent
WordPress, pas le métier. Un agent qui n'aurait qu'eux devrait
reconstituer la logique éditoriale à coups de requêtes sur des
tables et des métadonnées — fragile, verbeux, et dangereux.

Les 24 outils métier sont d'une autre nature. Ils portent des
**verbes du domaine**, dont voici des représentants :

```
<domaine>_get_manuscripts            <domaine>_submit_manuscript
<domaine>_update_manuscript_status   <domaine>_assign_manuscript
<domaine>_submit_reading_report      <domaine>_get_pending_decisions
<domaine>_get_processing_status      <domaine>_query_rag_manuscripts
```

Chacun encapsule une règle métier : quels statuts sont atteignables
depuis quel statut, qui a le droit d'assigner, quel corpus une
recherche a le droit d'interroger. L'agent n'a pas à connaître le
schéma de la base ; il n'a même pas la possibilité de le contourner.

### La leçon d'architecture

> **Un serveur MCP utile expose les verbes du métier, pas les tables
> de la base.**
>
> Le CRUD générique donne à l'agent un pouvoir maximal et une
> compréhension minimale. Les outils métier font l'inverse : ils
> restreignent le geste possible et y attachent le sens. Le
> deuxième régime est à la fois plus sûr *et* plus performant en
> pratique, parce que l'agent choisit mieux quand le catalogue parle
> sa langue.

C'est le point transposable à n'importe quel projet MCP, quel que
soit le CMS ou le langage : la valeur d'un serveur MCP se mesure à
la distance entre ses outils et le schéma de persistance.

### Comparaison OWUI

C'est ici qu'AI-Engine se distingue le plus franchement. Open WebUI
peut *consommer* des outils MCP ; il n'en *expose* pas. AI-Engine
joue **dans les deux sens** : il consomme des serveurs MCP externes
(module Orchestration, Parcours 0) et expose WordPress comme serveur
MCP. C'est un terrain pédagogique de choix pour comprendre le
protocole des deux côtés du fil, sur une seule installation.

### Sécurité de l'endpoint

Deux remarques valables pour tout déploiement :

- L'authentification par **jeton Bearer** unique donne à son
  porteur l'intégralité du catalogue. Il n'y a pas de granularité
  par outil au niveau du jeton — la granularité vient des
  *capabilities* WordPress de l'utilisateur auquel le jeton est
  rattaché. Choisir cet utilisateur avec soin ; ne pas le prendre
  administrateur par défaut.
- Un jeton MCP est un **secret d'infrastructure** : il ne va ni dans
  un dépôt, ni dans une capture d'écran, ni dans un fichier de
  configuration versionné. Voir la note de méthode ci-dessous.

---

## Note de méthode — pourquoi il n'y a aucune capture

Ce dossier ne contient **aucune capture d'écran**, et c'est un choix
documenté, pas un manque.

La posture du dépôt ([`PRIVACY.md`](../../../../PRIVACY.md) §1)
exclut déjà « aucune capture d'écran, aucun log, aucune sortie nommant
une personne ». Elle y est formulée pour les données d'étudiants ; ce
dossier l'applique à un cas voisin — l'**environnement de travail d'un
tiers** — et le retour d'expérience ci-dessous explique pourquoi la
règle y est encore plus difficile à tenir qu'il n'y paraît.

La tentation initiale était d'illustrer les parcours avec des écrans
de l'administration AI-Engine de l'installation observée. La
première capture a suffi à trancher : un écran de `wp-admin` affiche
simultanément le **nom du compte connecté** dans la barre
d'administration, le **titre du site**, ses **noms de domaine**, et
la **liste complète des extensions installées** dans le menu latéral.
Ces éléments ne sont pas dans le contenu de la page : ils sont dans
son cadre, et le cadre est présent sur *toutes* les pages.

Deux issues seulement, et les deux sont fermées :

- **Retoucher la capture** (flouter, masquer) est proscrit. Une
  retouche est invérifiable par le lecteur, elle rate régulièrement
  une occurrence, et elle donne une fausse assurance. La règle
  d'hygiène applicable ici impose de corriger la *cause* — le
  contenu affiché — puis de recapturer.
- **Modifier l'installation** pour neutraliser le cadre (renommer le
  site, créer un compte au nom neutre) reviendrait à altérer un
  environnement de travail réel pour les besoins d'une illustration.
  Hors de question.

La conclusion vaut au-delà de ce dossier :

> **Une capture d'écran n'est pas un extrait de contenu, c'est un
> extrait de contexte.** On ne l'assainit pas en cachant ce qu'on y
> a repéré ; on la produit sur une instance dédiée, ou on ne la
> produit pas.

Illustrer correctement ces parcours suppose donc de monter une
**instance jetable** — WordPress neuf, nom neutre, compte
d'administration neutre, corpus synthétique, extensions réduites au
nécessaire — et de n'y capturer que des écrans construits pour être
publiés. C'est un travail à part entière, sans lien avec le site
observé ; il n'est pas fait ici.

En attendant, ce dossier privilégie une contrainte simple : **tout
ce qu'il affirme est vérifiable par le lecteur sur sa propre
installation**, puisqu'il ne s'agit que de structures et de
comptages, pas de contenus.

---

## Ce que ce parcours ne montre pas

- **Aucun contenu du site** : ni texte de manuscrit (sous droits
  d'auteur), ni nom de personne, ni titre d'ouvrage, ni extrait de
  corpus indexé.
- **Aucun identifiant** : ni URL d'administration, ni adresse
  e-mail, ni clé d'API, ni jeton MCP, ni mot de passe. Les chemins
  d'API sont donnés sous forme générique
  (`https://VOTRE-INSTALL/wp-json/...`).
- **Aucun nom d'outil métier réel** : les huit exemples du
  Parcours 3 sont donnés avec un préfixe substitué `<domaine>_`.
  Ce qui compte pédagogiquement est le *verbe*, pas le préfixe.
- **Aucune capture d'écran**, pour la raison exposée ci-dessus.

---

## Métriques relevées

Relevés directement sur l'installation observée. Ce sont des
**chiffres de structure** (comptages de configuration), pas des
mesures de performance : aucun benchmark n'a été conduit, et aucune
latence n'est publiée ici.

| Grandeur | Valeur relevée |
|----------|----------------|
| Version AI-Engine | Pro 3.4.1 |
| Outils MCP exposés au total | 88 |
| dont natifs WordPress (`wp_*`) | 37 |
| dont natifs WooCommerce (`wc_*`) | 25 |
| dont natifs AI-Engine (`mwai_*`) | 2 |
| dont **outils métier** développés pour le site | **24** |
| Environnements d'embeddings coexistants | 6 |
| Vecteurs indexés, tous environnements confondus | ~1600 |
| Familles de modules AI-Engine | 3 (Client, Server, Admin) |

> **Ce que ces chiffres ne disent pas.** Ni la latence, ni le coût
> par requête, ni la qualité du retrieval. Ces grandeurs-là dépendent
> du modèle choisi, du volume du corpus et du provider ; les publier
> depuis une seule installation, sans protocole de mesure, n'aurait
> aucune valeur. Elles feront l'objet d'un travail séparé s'il est
> mené.

---

## Voir aussi

- [README AI-Engine-WordPress](README.md) — point d'entrée
- [Comparatif OWUI vs AI-Engine](comparatif-owui-vs-ai-engine.md) —
  tableau structuré
- [Tour OWUI](../00-Tour-Plateforme/README.md) — pendant Open WebUI
- Issue [#9734](https://github.com/jsboige/CoursIA/issues/9734) —
  mandat user à l'origine
- Epic [#4433](https://github.com/jsboige/CoursIA/issues/4433) —
  refonte GenAI (extension)
