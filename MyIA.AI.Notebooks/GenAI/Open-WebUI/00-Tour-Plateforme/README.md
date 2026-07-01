# Tour de la plateforme Open WebUI

[← Documentation GenAI](../../README.md) | [↑ Open-WebUI](../README.md) | [Série QA Playwright-OWUI](../Playwright-OWUI/README.md)

> **Parcours découverte.** Ce tour guidé présente, fonctionnalité par
> fonctionnalité, *à quoi sert Open WebUI et comment on l'utilise*. Il est le
> pendant « utilisateur » de la [série QA Playwright-OWUI](../Playwright-OWUI/README.md)
> qui, elle, *teste* la même plateforme de bout en bout. On apprend ici à se
> servir de l'outil ; on apprend là-bas à en garantir la qualité.

---

## À qui s'adresse ce tour ?

À toute personne qui découvre Open WebUI : étudiant·e d'un cours hébergé sur la
plateforme, futur·e administrateur·rice d'une instance, ou ingénieur·e qui veut
comprendre les surfaces du produit avant d'écrire des tests dessus. Aucun
prérequis technique pour les sections 1 à 5 ; la section 6 (administration et
multi-tenant) suppose un compte administrateur et une curiosité pour
l'architecture.

## Comment lire ce tour

Chaque section suit le même rythme :

1. **Ce que c'est** — la fonctionnalité en deux phrases.
2. **Comment s'en servir** — la séquence de gestes concrets.
3. **Capture** — une image annotée du résultat (voir la note ci-dessous).
4. **Exercice** *(certaines sections)* — une manipulation à faire soi-même.

> **Note sur les captures.** Les images de ce tour sont produites de façon
> **reproductible** par un script Playwright ([`capture/`](capture/)) exécuté
> contre une **instance réelle** avec un **compte non-administrateur**, sur des
> **données fictives ou fraîches**, et avec le **masquage** (`mask`) des zones
> sensibles. Chaque image passe une **revue anti-fuite** avant d'être commitée.
> Les captures de surfaces qui exposeraient du contenu réel d'un établissement
> (listes de modèles ou de bases internes, canaux) restent volontairement
> indiquées par `📷 Capture à venir` et **schématisées** dans
> [`architecture.md`](architecture.md). **Aucune capture ne montre d'URL réelle de
> tenant, d'e-mail nominatif, de clé ni de jeton.**

---

## Sommaire

| # | Section | Ce qu'on y découvre |
|---|---------|---------------------|
| 1 | [Connexion & première vue](#1--connexion--première-vue) | Se connecter, la fenêtre de chat |
| 2 | [Le chat IA](#2--le-chat-ia--modèles-streaming-multimodal) | Modèles, streaming, pièces jointes |
| 3 | [Le Workspace](#3--le-workspace--modèles-prompts-outils-rag) | Modèles personnalisés, prompts, outils, RAG |
| 4 | [Canaux & collaboration](#4--canaux--collaboration) | Échanges en équipe, bots |
| 5 | [Notes & autres surfaces](#5--notes--autres-surfaces) | Prise de notes, historique, paramètres |
| 6 | [Administration & multi-tenant](#6--administration--multi-tenant) | Panneau admin, RBAC, isolation des tenants |

> **Nouveautés de la v0.10 (juillet 2026).** Cette édition du tour intègre les
> apports marquants de la version 0.10 d'Open WebUI, signalés par la mention
> ***(nouveau — v0.10)*** au fil des sections :
> - **Raisonnement affiché en direct** et **compaction automatique du contexte** (section 2) ;
> - **Dossiers d'équipe partageables** et **téléversement de dossier** vers une base de connaissances (section 3) ;
> - **Mémoire** de l'assistant, sortie de bêta (section 5) ;
> - **Configuration de l'authentification** déplacée dans le panneau d'administration (section 6).
>
> Ces mêmes fonctionnalités sont *testées* par le **module 06** de la
> [série QA Playwright-OWUI](../Playwright-OWUI/README.md) : le tour montre *comment
> s'en servir*, la série QA vérifie *qu'elles marchent*.

---

## 1 — Connexion & première vue

**Ce que c'est.** Le point d'entrée de la plateforme : une page de connexion,
puis l'espace de conversation où tout se passe.

**Comment s'en servir.**

1. Ouvrez l'URL de votre instance dans un navigateur (par ex.
   `https://votre-instance.exemple`).
2. Saisissez votre e-mail et votre mot de passe, puis validez. Selon la
   configuration, l'inscription peut être ouverte, sur invitation, ou déléguée à
   un fournisseur d'identité (LDAP, OAuth, SAML).
3. Vous arrivez sur l'écran de chat : une zone de saisie au centre, l'historique
   des conversations à gauche, le sélecteur de modèle en haut.

> 📷 Capture à venir — `01-connexion.png` (page de connexion, champs masqués) et
> `01-premiere-vue.png` (écran de chat vide), générées via [`capture/`](capture/).

---

## 2 — Le chat IA : modèles, streaming, multimodal

**Ce que c'est.** Le cœur du produit : converser avec un modèle de langage. Open
WebUI unifie derrière une seule interface des modèles très différents — locaux
(Ollama, vLLM) ou distants (OpenAI, Mistral, Anthropic, OpenRouter…).

**Comment s'en servir.**

1. Dans le sélecteur en haut, choisissez un modèle. Son nom indique souvent le
   fournisseur (préfixe) et la taille.
2. Tapez votre message et envoyez. La réponse s'affiche **en streaming**,
   mot à mot, plutôt que d'un bloc — utile pour les longues réponses.
3. Joignez un fichier (icône trombone) : image pour un modèle *vision*, document
   pour le résumer ou l'interroger.
4. Reprenez une réponse, régénérez-la, ou comparez deux modèles côte à côte selon
   les options offertes par votre instance.

**Raisonnement affiché en direct *(nouveau — v0.10)*.** Avec les modèles dits
« thinking » (Claude, Qwen, o-series…), la plateforme affiche désormais **en
temps réel** les étapes de raisonnement du modèle, dans un bloc repliable placé
au-dessus de la réponse finale. On voit le modèle « réfléchir » pendant qu'il
génère, puis on peut replier ce bloc pour ne garder que la conclusion. C'est un
appui pédagogique précieux : on rend visible le *cheminement*, pas seulement le
résultat.

**Compaction automatique du contexte *(nouveau — v0.10)*.** Sur les conversations
longues, la plateforme **résume et compacte** automatiquement les échanges les
plus anciens pour rester dans la fenêtre de contexte du modèle, sans qu'on ait à
démarrer une nouvelle conversation. La discussion se prolonge donc sans perdre le
fil ni provoquer d'erreur de dépassement de contexte.

> 📷 Capture à venir — `02-chat-streaming.png` (réponse en cours de streaming) et
> `02-selecteur-modele.png` (liste des modèles), masquage du nom d'utilisateur.
> `02-raisonnement-direct.png` illustre le bloc de raisonnement en direct
> *(nouveau — v0.10)*.

### Exercice 1 — Prendre le chat en main

Ouvrez une conversation, posez une question ouverte, puis **changez de modèle en
cours de conversation** et reposez la même question. Comparez : longueur,
ton, vitesse de streaming. Notez quel modèle vous semble le mieux adapté à votre
besoin et pourquoi. *(Objectif : comprendre que le choix du modèle change le
résultat, et que l'interface rend ce choix immédiat.)*

---

## 3 — Le Workspace : modèles, prompts, outils, RAG

**Ce que c'est.** L'atelier où l'on *personnalise* la plateforme sans écrire de
code : créer ses propres assistants, ses prompts réutilisables, brancher des
outils, et constituer des bases de connaissances interrogeables (RAG).

**Comment s'en servir.**

- **Modèles personnalisés.** Partez d'un modèle de base, ajoutez un *system
  prompt*, une description, une icône : vous obtenez un assistant spécialisé
  (« Tuteur Python », « Relecteur juridique »…) réutilisable et partageable.
- **Prompts.** Enregistrez des invites fréquentes sous un raccourci (`/resume`,
  `/plan`…) pour les rappeler en un mot dans le chat.
- **Outils & serveurs MCP.** Donnez au modèle la capacité d'agir : appeler une
  API, exécuter du code, consulter une source externe via le protocole MCP.
- **Bases de connaissances (RAG).** Téléversez des documents ; la plateforme les
  découpe, les vectorise et les rend interrogeables. Le modèle cite alors vos
  documents dans ses réponses. *(nouveau — v0.10)* Le **téléversement d'un dossier
  entier** préserve désormais son **arborescence** : la structure des sous-dossiers
  est conservée dans la base, ce qui aide à organiser de gros corpus.
- **Dossiers d'équipe partageables *(nouveau — v0.10)*.** On peut regrouper des
  conversations (et le travail associé) dans des **dossiers**, puis **partager un
  dossier avec un groupe**. Tous les membres du groupe y accèdent avec les droits
  accordés — pratique pour un binôme de TP ou une promotion entière. Le partage
  s'appuie sur le même modèle d'octroi d'accès que les modèles et les bases (voir
  le [modèle RBAC](architecture.md)).

> 📷 Capture à venir — `03-workspace-modele.png`, `03-base-connaissances.png`
> (données fictives uniquement) ; `03-dossier-equipe.png` pour le partage de
> dossier *(nouveau — v0.10)*.

### Exercice 2 — Créer un assistant RAG

1. Créez une **base de connaissances** et téléversez-y 2 ou 3 documents fictifs
   (notes de cours, fiche produit imaginaire…).
2. Créez un **modèle personnalisé** avec un *system prompt* du type « Tu réponds
   uniquement à partir des documents fournis et tu cites tes sources ».
3. Rattachez la base au modèle, puis posez-lui une question dont la réponse est
   dans un document. Vérifiez qu'il **cite** le bon document.

*(Objectif : relier modèle, prompt et RAG — la chaîne qui transforme un chat
généraliste en assistant ancré sur vos données.)*

---

## 4 — Canaux & collaboration

**Ce que c'est.** Des espaces de discussion partagés, façon messagerie d'équipe,
où des humains et des **bots** (assistants automatiques) échangent dans un fil
commun.

**Comment s'en servir.**

1. Ouvrez la section *Canaux* et rejoignez (ou créez) un canal.
2. Écrivez dans le fil ; les membres voient les messages en temps réel.
3. Mentionnez un bot configuré pour lui poser une question : il répond dans le
   canal, visible de tous.

> 📷 Capture à venir — `04-canal.png` (fil de discussion, avatars et noms
> masqués).

---

## 5 — Notes & autres surfaces

**Ce que c'est.** Autour du chat, la plateforme offre des surfaces utilitaires :
prise de **notes**, historique et recherche des conversations, dossiers, et
**paramètres** personnels (langue, thème, raccourcis, voix).

**Comment s'en servir.**

- **Notes** — rédigez et conservez des notes, éventuellement assistées par le
  modèle.
- **Historique** — retrouvez, renommez, classez en dossiers et archivez vos
  conversations.
- **Paramètres** — changez la langue de l'interface (multilingue), le thème
  clair/sombre, activez la synthèse ou la reconnaissance vocale.
- **Mémoire *(nouveau — v0.10)*.** L'assistant peut **retenir des informations**
  d'une conversation à l'autre (mémoire à long terme) ou au sein d'une conversation
  donnée. On garde la **main** : la mémoire se gère depuis *Paramètres >
  Personnalisation*, où l'on consulte, modifie ou supprime chaque souvenir. Sortie
  de bêta en v0.10, elle permet par exemple à un tuteur de se rappeler le niveau ou
  les préférences d'un·e étudiant·e sans qu'on ait à les répéter.

> 📷 Capture à venir — `05-parametres.png` (panneau de paramètres, identité
> masquée) ; `05-memoire.png` pour la gestion de la mémoire *(nouveau — v0.10)*.

### Exercice 3 — Personnaliser son espace

Changez la **langue** de l'interface, basculez le **thème**, créez un **dossier**
et rangez-y une conversation. Puis enregistrez un **prompt** réutilisable et
rappelez-le par son raccourci dans le chat. *(Objectif : se rendre maître de son
environnement de travail — l'ergonomie fait partie de la qualité perçue d'une
plateforme.)*

---

## 6 — Administration & multi-tenant

**Ce que c'est.** La face cachée : le **panneau d'administration** (utilisateurs,
groupes, rôles, connecteurs de modèles, réglages globaux) et l'architecture
**multi-tenant** qui permet de faire cohabiter plusieurs établissements sur une
même infrastructure, chacun isolé des autres.

> **Cette section est volontairement *schématisée*.** Pour ne rien divulguer
> d'une instance réelle, l'administration et le multi-tenant sont présentés par
> des **diagrammes** plutôt que par des captures de panneaux réels. Voir
> **[`architecture.md`](architecture.md)** pour :
> - le schéma de **déploiement multi-tenant** (tenants isolés, infrastructure
>   partagée) ;
> - le modèle de **contrôle d'accès (RBAC)** : utilisateurs → groupes → droits ;
> - le **flux RAG** (document → extraction → vectorisation → récupération) ;
> - le **flux outils/MCP**.

**Comment s'en servir (côté admin).**

1. Le panneau d'administration liste les **utilisateurs** (rôle : admin, user,
   pending) et permet de les promouvoir, suspendre ou supprimer.
2. Les **groupes** rassemblent des utilisateurs pour leur accorder des droits
   collectifs (accès à tel modèle, telle base de connaissances).
3. Les **connecteurs** déclarent les fournisseurs de modèles (URL, type) ; les
   secrets associés ne vivent **jamais** dans un support pédagogique — voir la
   section sécurité ci-dessous.
4. *(nouveau — v0.10)* La **configuration de l'authentification** (OAuth, LDAP,
   SAML, inscription ouverte ou sur invitation) se règle désormais **dans le
   panneau d'administration** plutôt que par des variables d'environnement au
   démarrage — un·e admin peut donc ajuster ces réglages sans redéployer l'instance.

### Exercice 4 — Cartographier les accès (sur schéma)

À partir du diagramme RBAC de [`architecture.md`](architecture.md), décrivez le
chemin d'autorisation qui permet à un·e étudiant·e du « Tenant A » d'accéder à un
modèle réservé à son groupe, **sans** pouvoir accéder aux données du « Tenant B ».
Identifiez le point exact où l'isolation est garantie. *(Objectif : comprendre
que le multi-tenant n'est pas « plusieurs serveurs » mais une isolation
logique — c'est précisément ce que la [série QA](../Playwright-OWUI/README.md)
module 5 vérifie par des tests.)*

---

## Sécurité — aucun secret dans ce tour

Conformément à la [politique du dossier ombrelle](../README.md#sécurité--pas-de-secret-dans-les-supports) :
pas d'URL de tenant réel, pas d'e-mail nominatif, pas de clé d'API ni de jeton,
pas de mot de passe. Les captures sont produites contre une **instance réelle**
via un **compte non-administrateur neuf** (aucune donnée réelle visible), avec
**masquage Playwright** et **revue anti-fuite de chaque image**. Les identifiants
et l'URL de capture vivent dans un `.env` **non commité** ; seuls les
`*.env.example` documentent les variables attendues. Voir
[`capture/README.md`](capture/README.md).

---

## Et ensuite ?

- Pour **tester** ce que vous venez de découvrir, passez à la
  [série QA Playwright-OWUI](../Playwright-OWUI/README.md) : vous y écrirez des
  tests end-to-end qui vérifient automatiquement chacune de ces surfaces.
- Pour **comprendre l'infrastructure** qui sert les modèles de cette plateforme,
  voir le chapitre [LLMs locaux & serving](../../Texte/LLMs-Locaux-Serving/README.md).

---

*Tour de la plateforme — parcours découverte (Epic #4433, sous #4427). FR-first.
Édition **v0.10** (contenu validé contre Open WebUI 0.10.2, juillet 2026).
Statut : narratif complet ; script de capture reproductible prêt (voir la
[note sur les captures](#comment-lire-ce-tour)).*
