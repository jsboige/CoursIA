# L'architecture en modules

[← README Architecture](README.md) | [← README AI-Engine-WordPress](../README.md)

> Extrait du [cas d'usage éditorial](../04-Cas-Usage-livresagites/livresagites-parcours.md)
> dont il constituait le « Parcours 0 », relogé ici (réorganisation #12127)
> avec les parcours fonctionnels restés en place.

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
   distincte (voir le [Parcours 3 — WordPress comme serveur MCP métier](../04-Cas-Usage-livresagites/livresagites-parcours.md)). Les deux sens du protocole ne se
   configurent pas au même endroit — confusion fréquente.

> **Notebook compagnon.** [`consommer-vs-exposer-le-mcp.ipynb`](../consommer-vs-exposer-le-mcp.ipynb)
> rend exécutable cette distinction : il monte les **deux côtés du fil** sur un
> même fixture synthétique (Maison Valmont) — un mini-serveur MCP exposé et un
> mini-client MCP consommé — et mesure le chevauchement fonctionnel
> cross-catalogue. La question opérationnelle qu'il formalise : *faut-il
> brancher ce serveur MCP externe, ou ses outils sont-ils déjà couverts par le
> catalogue interne ?* Indice de Jaccard sur les signatures `(verbe, cible)`,
> avec un accent sur le sous-ensemble écriture (le double-écrit, risque réel
> même sous un chevauchement global faible).

> **Notebook compagnon (module Client).**
> [`configurer-chatbots-par-l-api.ipynb`](../configurer-chatbots-par-l-api.ipynb)
> ouvre la face exécutable du module Chatbot : dans AI-Engine, un chatbot
> est un **document JSON** (54 champs — identité, instructions, modèle,
> présentation) que l'API REST lit et réécrit. Le `POST
> /mwai/v1/settings/chatbots` **remplace toute la liste**, d'où le
> pattern read-modify-write pour créer ou modifier un bot. Le notebook
> duplique le chatbot d'accueil d'une maison synthétique (Maison Valmont)
> en comité de lecture, vérifie la persistance par relecture, puis pose la
> même question aux deux personas et **mesure** leur recouvrement
> lexical : les instructions orientent la réponse, elles ne la garantissent
> pas. Exécuté contre l'instance jetable locale (`instance-jetable/`),
> corpus 100 % synthétique, aucun contenu privé.

> **Notebook compagnon (module Client, face visiteur).**
> [`parler-au-chatbot-en-visiteur-par-l-api.ipynb`](../parler-au-chatbot-en-visiteur-par-l-api.ipynb)
> ouvre la troisième face du plugin — celle du **navigateur d'un visiteur
> anonyme**, dans un namespace propre (`mwai-ui/v1`). Le cycle démontré :
> la page publique du chatbot n'embarque **aucun jeton** (`restNonce` et
> `sessionId` explicitement `null` dans le conteneur — un design
> anti-cache : un nonce figé dans du HTML caché expirerait, un sessionId
> figé fusionnerait les limites de tous les visiteurs) ; le navigateur
> amorce par `POST /mwai/v1/start_session` (le seul endpoint à
> permission `__return_true`), qui délivre nonce frais et cookie de
> session ; puis la conversation passe par `chats/submit` au header
> `X-WP-Nonce`. Frontière mesurée : **401 sans le nonce** — mais un nonce
> n'est pas une authentification, c'est un anti-CSRF délivré à quiconque
> charge le site ; le contrôle d'accès réel de cette face vit aux
> limites de débit.

> **Notebook compagnon (module Client, face pièces jointes).**
> [`donner-une-memoire-ephemere-au-chatbot-par-l-api.ipynb`](../donner-une-memoire-ephemere-au-chatbot-par-l-api.ipynb)
> ouvre la cinquième surface de la série — la famille
> `mwai-ui/v1/files/*`, celle qui donne au chatbot ses pièces
> jointes : un manuscrit à relire, un extrait audio, une image. Le
> trait le plus caractéristique y est **mesuré par calcul** : la
> fiche du fichier porte `created` et `expires`, et la soustraction
> rend exactement **une heure** — la mémoire fichiers est éphémère
> par architecture, pas par configuration, un choix lisible dans la
> réponse même de l'API. Autour : le contrat d'upload découvert par
> refus (400 « Purpose is required. » nomme le champ obligatoire),
> l'URL publique servie par la médiathèque WordPress (contenu vérifié
> octet pour octet), la partition par utilisateur — table
> `mwai_files`, deux auteurs ne voient ni n'effacent les pièces
> jointes de l'autre, jusqu'aux sessions anonymes qui ont chacune la
> leur —, le delete par refus (400 « No valid files to delete » pour
> `{id}` : le contrat veut `{"files": [refId]}`), et le miroir admin
> `mwai/v1/openai/files/*` où les mêmes fichiers reviennent, augmentés
> de `download` et `finetune`. Le fichier téléversé est synthétique
> et détruit en fin de parcours — cleanup mesuré, total 0 → 1 → 0.

> **Notebook compagnon (module Client, consommation des pièces jointes).**
> [`joindre-un-fichier-au-chatbot-par-l-api.ipynb`](../joindre-un-fichier-au-chatbot-par-l-api.ipynb)
> pose la question qui suit le stockage : **comment un fichier
> téléversé entre-t-il dans une completion ?** La réponse mesurée
> donne à une pièce jointe trois destins possibles, aucun lisible sur
> le code de statut. *Ignorée* : la route `chats/submit` lit
> `newFileId`, et un `fileId` à sa place rend un 200 silencieux — le
> fichier n'est même pas regardé. *Annotée puis jetée* : avec le bon
> nom, le plugin traite le fichier (`purpose` → `analysis`,
> métadonnées de session) mais le contenu d'un fichier texte n'entre
> jamais dans le prompt — compte de tokens identique à un tour sans
> fichier, canary absent, le modèle le dit honnêtement. *Vraiment
> vue* : une image, elle, traverse — encodée `image_url` base64, le
> format de fil standard — et un PNG bicolore construit par le
> notebook (stdlib `struct` + `zlib`, couleurs connues par
> construction) est correctement décrit sur l'endpoint auto-hébergé :
> **la frontière du multimodal est le format, pas le provider**. Le
> contrôle négatif (même question sans image → aucune couleur citée)
> ferme la porte à la devinette.

---

## Voir aussi

- [`README.md`](README.md) — vue d'ensemble, fonctionnalités cœur,
  multi-provider : la surface fonctionnelle du plugin
- [`../04-Cas-Usage-livresagites/livresagites-parcours.md`](../04-Cas-Usage-livresagites/livresagites-parcours.md)
  — le cas d'usage complet dont cette page est issue
- [`../02-Comparatif/comparatif-owui-vs-ai-engine.md`](../02-Comparatif/comparatif-owui-vs-ai-engine.md)
  — le même plugin vu par le tableau comparatif
