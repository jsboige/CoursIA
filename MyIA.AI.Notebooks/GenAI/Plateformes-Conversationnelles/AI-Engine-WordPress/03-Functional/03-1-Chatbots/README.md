# Chatbots — configurer, interroger, joindre

[← Les fonctionnalités par l'API](../README.md) | [↑ AI Engine (WordPress)](../../README.md) | [Instance jetable →](../../instance-jetable/README.md)

Un chatbot de site se présente comme une bulle de dialogue. Vu par l'API, c'est autre chose : un document de configuration, des routes distinctes selon que l'on est administrateur, visiteur ou rédacteur, et des pièces jointes qui ont leur propre cycle de vie. Cette sous-série démonte la bulle pièce par pièce, sur l'instance jetable « Maison Valmont », et mesure à chaque fois ce que le plugin fait réellement de ce qu'on lui envoie.

Elle s'adresse à qui doit configurer, intégrer ou auditer un chatbot AI Engine. Le premier carnet de la chaîne, [Présenter AI Engine par son API](../03-5-Multi-Provider/presenter-ai-engine-par-son-api.ipynb), en est le prérequis : il pose l'instance, les helpers et la manière de lire une réponse.

## Comment lire ce README

Les séries du dépôt se lisent à plusieurs vitesses, selon le principe décrit dans [« Choisir sa vitesse de lecture »](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture).

- Vous **découvrez** : lisez le parcours principal dans l'ordre des numéros ; les deux premières lignes suffisent pour configurer un chatbot et lui parler comme le ferait un visiteur.
- Vous **creusez un palier** : la section « Approfondissements » prolonge l'assistant de l'éditeur par une mesure de dérive.
- Vous cherchez **ce qui reste ouvert** : « Pour aller plus loin » dit où passe la frontière de la version gratuite et quelles questions la série laisse à d'autres carnets.

## Parcours principal

*Niveau Découverte pour les deux premières lignes, Approfondissement ensuite.* Les numéros sont les rangs des carnets dans la chaîne « AI Engine par son API », dont l'ordre complet figure dans le [README parent](../README.md) ; les rangs absents se lisent dans les sous-séries voisines.

| # | Notebook | Ce qu'on y apprend | Public | Pour approfondir |
|---|---|---|---|---|
| 2 | [Configurer et interroger des chatbots](configurer-chatbots-par-l-api.ipynb) | Un chatbot est un document JSON dans la configuration du plugin. Lire la liste, l'écrire par lecture-modification-écriture (l'envoi remplace toute la liste), créer un second persona par duplication, poser la même question aux deux. Les instructions orientent la réponse, elles ne la garantissent pas ; un plafond de tokens inscrit dans le document n'est pas une borne stricte. | Administrateur ou intégrateur | [Cadrer les agents](../../../cadrer-les-agents.md), [Différencier plusieurs assistants](../../../differencier-les-assistants.ipynb) |
| 6 | [Parler au chatbot en visiteur](parler-au-chatbot-en-visiteur-par-l-api.ipynb) | La face navigateur de l'API (`mwai-ui/v1`) : la page publique ne contient aucun secret, un amorçage de session délivre un nonce, et ce nonce suffit pour converser sans compte. Un nonce n'est pas une authentification : le contrôle d'accès réel tient au chatbot autorisé et aux limites de débit par session. | Développeur front, auditeur de sécurité | [Le serveur MCP et son autorisation](../03-4-MCP-Server/autour-du-consent-oauth-du-serveur-mcp.ipynb), qui compare les trois clés de la plateforme |
| 7 | [Obtenir des données structurées](obtenir-des-donnees-structurees-par-l-api.ipynb) | La route `ai/json` refuse l'appel à froid : la case JSON de la matrice d'usages est vide. La remplir par écriture du bloc complet, structurer un catalogue synthétique, puis mesurer l'honnêteté du résultat : JSON valide ou `null` silencieux, contrainte portée par le prompt ou par le protocole. Restaurer l'état initial. | Intégrateur qui alimente un traitement aval | [Choisir le modèle derrière son chatbot](../03-5-Multi-Provider/eval-choisir-son-modele.ipynb), propriété « respect du format » |
| 9 | [L'assistant de l'éditeur](interroger-lassistant-de-lediteur-par-l-api.ipynb) | La quatrième face du plugin : la route de l'éditeur répond en version gratuite par une complétion réelle, avec un champ `actions` vide. Le nonce du visiteur y est refusé, celui de l'administration y est accepté ; le contrat se découvre par les refus ; la mémoire de la conversation est portée par le client. | Développeur d'extension, rédacteur technique | [Mesurer la dérive d'un copilot](mesurer-la-derive-dun-copilot.ipynb) |
| 10 | [Les fichiers du chatbot — une mémoire éphémère](donner-une-memoire-ephemere-au-chatbot-par-l-api.ipynb) | La surface fichiers (`upload`, `list`, `delete`) : un envoi exige de déclarer son usage (champ `purpose`), la fiche rendue porte une expiration une heure après la création, l'adresse rendue sert le contenu à qui la connaît, et un fichier appartient à l'utilisateur qui l'a déposé. Aucun appel au modèle. | Intégrateur, auditeur de sécurité | Le rang 11, qui montre ce qu'une complétion fait du fichier |
| 11 | [Joindre un fichier au chatbot](joindre-un-fichier-au-chatbot-par-l-api.ipynb) | Les trois états d'une pièce jointe : ignorée (mauvais nom de paramètre, réponse 200 sans erreur), annotée puis écartée (un fichier texte n'entre jamais dans le prompt), réellement vue (une image, décrite par le moteur). La preuve tient à un contrôle négatif sur une image construite par le carnet. | Intégrateur qui promet « envoyez-nous votre document » | [Brancher plusieurs providers](../03-5-Multi-Provider/brancher-plusieurs-providers-par-l-api.ipynb), usage vision de la matrice |

Deux gestes reviennent d'un carnet à l'autre. Le premier est de découvrir un contrat par ses refus : un code 400 qui nomme le champ attendu renseigne mieux qu'une documentation absente. Le second est de mesurer par l'effet observable — un compte de tokens identique avec et sans fichier, une relecture après écriture — plutôt que par le code de retour.

## Approfondissements

*Niveau Approfondissement.*

### Autour de 9 — quand l'assistant enchaîne les transformations

[Mesurer la dérive d'un copilot](mesurer-la-derive-dun-copilot.ipynb) part d'une question que l'assistant de l'éditeur pose dès qu'on enchaîne ses opérations : résumer, enrichir, traduire, réécrire. À chaque étape un humain valide, et pourtant le texte final peut s'être éloigné du texte de départ. Le carnet montre pourquoi : la validation par étape est locale, la dérive est cumulative.

Il procède en deux temps. Les premières sections modélisent un document par un vecteur de fréquences de termes et les transformations par des opérations sur ce vecteur ; tout y est déterministe et ne demande que `numpy`. La dernière section rejoue une chaîne de réécritures sur l'instance et mesure la dérive par similarité cosinus sur des embeddings réels : elle donne la forme du profil, pas des valeurs à retenir. La conclusion est un critère de conception : un contrôle utile se souvient de la chaîne, pas seulement de la dernière étape.

Prérequis en plus : pour la dernière section, l'instance jetable et un moteur local qui sert à la fois la réécriture et les embeddings, déclaré dans le fichier `.env` de l'instance. Le carnet prolonge le parcours 1 du [cas d'usage éditorial](../../04-Cas-Usage-livresagites/livresagites-parcours.md).

## Installation et prérequis

*Niveau Découverte.*

- **L'instance jetable « Maison Valmont »** démarrée, et son fichier `instance-jetable/.env` renseigné : le [README de l'instance](../../instance-jetable/README.md) donne le montage, le port et les variables. Aucune adresse ni clé n'est écrite dans un carnet.
- **Un moteur de langage local compatible OpenAI** : les rangs 2, 6, 7, 9 et 11 lancent de vraies complétions. Avec un modèle à raisonnement, chacune peut prendre plusieurs dizaines de secondes, et le rang 9 en enchaîne une dizaine.
- **Un modèle capable de lire une image** pour le troisième état du rang 11 : c'est lui qui décrit l'image jointe.
- **Un compte de test au rôle éditeur** pour les rangs 9 et 10 : il est créé par le carnet [OAuth du serveur MCP](../03-4-MCP-Server/autour-du-consent-oauth-du-serveur-mcp.ipynb) (rang 8 de la chaîne), et son mot de passe se lit dans la variable `VALMONT_EDITOR_PASSWORD`.
- **Des envois de fichiers fonctionnels** pour les rangs 10 et 11 : si l'envoi rend une erreur 500 « Could not move the file. », la note de maintenance du README de l'instance donne la correction.
- **Python 3.10 ou plus récent** avec `requests` et `python-dotenv` ; `numpy` pour la mesure de dérive.

Les carnets qui écrivent dans la configuration ou déposent des fichiers remettent l'instance dans son état initial en fin de parcours. Exécutez-les sur l'instance jetable, jamais sur un site en service.

## Pour aller plus loin

*Niveau Recherche.*

- **La frontière de la version gratuite.** L'assistant de l'éditeur répond, mais son champ `actions` reste vide : les opérations qui modifient directement le contenu relèvent de l'offre payante, et la série ne les mesure pas. Elle décrit ce que l'API gratuite rend, sans extrapoler.
- **Le persona n'est pas une frontière de sécurité.** Le rang 2 le constate sur deux chatbots ; la note [Cadrer les agents](../../../cadrer-les-agents.md) en fait un critère de conception, et le carnet [Différencier plusieurs assistants](../../../differencier-les-assistants.ipynb) mesure si des prompts distincts produisent des réponses réellement distinguables.
- **Le texte joint qui n'entre pas dans le prompt** renvoie à la question du RAG : faire lire un document à un chatbot passe par une ingestion, traitée dans [RAG et embeddings](../03-3-RAG-et-Embeddings/README.md).

## Ressources

- [Les fonctionnalités par l'API](../README.md) — l'ordre complet de la chaîne et les autres sous-séries.
- [Architecture en modules](../../01-Architecture/architecture-en-modules.md) — où se placent le chatbot, l'assistant de l'éditeur et les fichiers dans le plugin.
- [Comparatif Open WebUI et AI Engine](../../02-Comparatif/comparatif-owui-vs-ai-engine.md) — la même fonction vue des deux plateformes.
- [Parcours QA — ce que l'API ne voit pas](../../05-Playwright-AI-Engine/README.md) — ce qu'il faut un navigateur pour observer.
