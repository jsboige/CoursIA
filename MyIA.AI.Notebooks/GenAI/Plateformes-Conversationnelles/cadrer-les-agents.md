# Cadrer ce qu'un agent a le droit de faire

[← Plateformes conversationnelles](README.md) | [← Comparatif OWUI vs AI-Engine](comparatif-owui-vs-ai-engine.md)

> **Document de conception, au niveau catégorie.** La question traitée ici se pose
> à l'identique sur Open WebUI et sur AI-Engine, avec des réponses natives
> différentes. Elle ne se range donc pas à l'intérieur de l'un des deux dossiers.

---

## La question

Un premier assistant ne pose pas de problème : on lui donne les outils dont il a
besoin, on écrit son prompt, c'est fini. La question arrive au deuxième.

Vous avez un catalogue d'outils et plusieurs assistants — un généraliste, et des
spécialistes par domaine. Comment faites-vous pour que l'assistant « atelier
d'écriture » ne déclenche pas d'opérations de boutique ?

Deux mécanismes existent, et on les traite souvent comme deux styles au choix.
Ce ne sont pas deux styles. Ils ne garantissent pas la même chose, et l'un des
deux ne garantit rien du tout contre un acteur déterminé.

---

## Trois choses qu'on confond

Le vocabulaire courant ne distingue pas trois questions qui ont trois réponses
différentes, à trois endroits différents du système.

| Question | Nom | Où elle se règle | Ce qu'elle tient |
|----------|-----|------------------|------------------|
| À quoi cet assistant sert-il ? | **Intention** | Prompt système | Le comportement habituel du modèle |
| Que peut-il proposer d'appeler ? | **Portée** | Catalogue d'outils attaché | Le contenu de la requête envoyée au modèle |
| Cet appel a-t-il le droit d'aboutir ? | **Autorité** | Vérification au moment de l'appel | Tout le monde, y compris hors assistant |

La règle qui en découle tient en une phrase : **ne jamais faire porter à une
couche une garantie qui appartient à une couche plus profonde.** Un prompt ne
tient pas une portée. Une portée ne tient pas une autorité.

---

## Mécanisme 1 — cadrer par le catalogue

Chaque assistant reçoit un sous-ensemble d'outils. Sur Open WebUI, on attache
des Tools à un preset de modèle (Workspace, puis Models, puis la section Tools
de l'entrée à éditer). Sur AI-Engine, chaque chatbot déclare sa propre liste de
fonctions.

**Ce que ça garantit vraiment.** Ce qui n'est pas dans le catalogue n'est pas
dans la requête envoyée au modèle. Aucune formulation ne le contourne, parce
qu'il n'y a rien à contourner : le schéma de l'outil est simplement absent. La
garantie est dure — *dans cette couche*.

**Ce que ça coûte.**

- *Une configuration qui grandit en produit.* M assistants fois N outils. Le jour
  où vous ajoutez un outil, il faut trancher pour chacun des M. Personne ne le
  refait jamais entièrement : le nouvel outil finit disponible chez l'assistant
  qui a motivé son écriture, et nulle part ailleurs. La configuration dérive en
  silence, et la dérive ne déclenche aucune alerte.
- *Un échec illisible.* Le modèle ne sait pas que l'outil existe. Sollicité sur
  une capacité qu'il n'a pas, il ne répond pas « ce n'est pas mon rôle » — il
  improvise une réponse plausible, ou refuse sans pouvoir expliquer pourquoi.
  L'utilisateur voit un assistant incompétent là où il y avait un assistant hors
  périmètre. C'est la même dégradation que celle d'un système cassé, ce qui la
  rend indistinguable d'un bug.
- *Une frontière invisible.* La personne ne peut pas découvrir que la capacité
  existe ailleurs. Le cloisonnement empêche l'orientation autant que l'action.

---

## Mécanisme 2 — cadrer par le prompt

Un seul catalogue pour tout le monde ; le rôle vit dans le prompt système.

**Ce que ça donne.** Une seule surface de configuration, un seul catalogue à
maintenir : un nouvel outil est disponible partout d'un coup. Et surtout, le
modèle *sait* que l'outil existe, donc la dégradation devient lisible — « cette
demande relève de l'assistant X, je vous y renvoie ». La frontière devient
navigable au lieu d'être un mur aveugle.

**Ce que ça ne garantit pas.** C'est une contrainte molle. Une formulation
insistante, une injection dans un document récupéré par le RAG, ou simplement
une conversation assez longue pour que le prompt système s'éloigne dans le
contexte — et l'appel part.

Le piège n'est pas qu'elle échoue. C'est qu'elle **fonctionne la plupart du
temps**, ce qui est pire que jamais : une contrainte statistique observée cent
fois produit la conviction d'une frontière qui n'existe pas.

---

## Le piège central — la couche persona n'est pas une frontière

Les deux mécanismes ci-dessus vivent dans la couche assistant. Or, dès qu'une
plateforme expose aussi ses outils par un **endpoint destiné aux machines** —
un serveur MCP, une API d'outils — cet endpoint est une **seconde porte**, et
elle ne passe par aucun assistant.

Relevé sur une installation AI-Engine 3.4.1 : six assistants configurés
déclarent respectivement 0, 5, 5, 5, 5 et 12 fonctions. Le même déploiement
expose **88 outils** sur son endpoint MCP à qui présente un jeton valide.

Restreindre un assistant change donc ce que **le modèle** se propose
spontanément de faire. Cela ne change rien pour **qui détient le jeton**.

D'où le test à s'appliquer avant de considérer un cloisonnement comme une
protection :

> Si la personne à qui je refuse cet outil obtenait le jeton de l'endpoint,
> est-ce que ce serait un problème ?

Si la réponse est oui, le persona n'a jamais été la protection — il en avait
seulement l'apparence.

---

## Ce que les deux plateformes font de la troisième couche

C'est là que le choix de plateforme cesse d'être une affaire de goût.

**Open WebUI vérifie l'autorité nativement.** L'attachement d'un outil à un
preset de modèle ne suffit pas à le rendre appelable : la documentation indique
que, lorsqu'un utilisateur dialogue avec le modèle, la plateforme vérifie si
**cet utilisateur précis** a accès en lecture à chacun des outils attachés
(*« Open WebUI checks whether that specific user has read access to each
attached tool »*, [docs Open WebUI, Tools][owui-tools]). La portée et l'autorité
sont deux étages distincts, et le second est appliqué par la plateforme.

**Sur AI-Engine et WordPress, la troisième couche existe mais n'est pas
imposée.** WordPress fournit tout l'appareil de capacités (`current_user_can()`)
— mais rien n'oblige l'auteur d'un outil à l'appeler. Un outil écrit sans
vérification de capacité s'exécute avec l'autorité de l'identité attachée à
l'appel, quelle qu'elle soit. La garantie est donc à la charge de celui qui
écrit l'outil, pas de la plateforme.

Ce qui déplace la question critique : **quelle identité est attachée à un appel
machine ?** Un endpoint qui associe tout jeton valide à un utilisateur par
défaut fait de ce jeton une identité. Si cet utilisateur par défaut est un
administrateur, alors le jeton *est* un identifiant d'administrateur, et une
vérification `current_user_can('manage_options')` répondra oui — la garde est
présente et vide de sens. Attacher le jeton machine à un compte de service à
moindre privilège est ce qui donne du sens à toutes les gardes écrites en aval.

**Question voisine, souvent oubliée : qui peut *créer* un outil ?** Elle est
distincte de qui peut l'appeler, et la réponse est plus grave. La documentation
Open WebUI est explicite : *« Granting a user the ability to create or import
Tools is equivalent to giving them shell access to the server »*
([docs Open WebUI, Tools][owui-tools]). La même chose vaut par construction sur
WordPress, où un outil est du code d'extension. Le droit de définir un outil
n'est pas un cran au-dessus du droit de l'appeler : c'est un autre ordre de
grandeur.

---

## Le critère de décision — la réversibilité de l'action

On n'apparie pas le mécanisme au confort de configuration, mais à ce que coûte
une erreur. Une action réversible se cadre par l'intention ; une action
irréversible se cadre par l'autorité.

| Type d'action | Prompt | Catalogue | Garde à l'appel |
|---------------|--------|-----------|-----------------|
| Lecture de contenu public | suffit | inutile | inutile |
| Lecture de données d'un utilisateur | oui | selon l'ergonomie | **obligatoire** — filtrer sur l'identité, pas sur la demande |
| Écriture réversible (brouillon, statut interne) | oui | selon l'ergonomie | recommandée |
| Envoi ou publication vers un tiers | oui | **retirer du catalogue** | **obligatoire** |
| Suppression, débit, action non annulable | oui | **retirer du catalogue** | **obligatoire**, plus une confirmation qui ne passe pas par le modèle |

Les deux dernières lignes portent deux barrières indépendantes, et ce n'est pas
de la ceinture-bretelles : la barrière du catalogue est dure mais locale à la
couche assistant, la garde à l'appel est la seule qui tienne face à quelqu'un
qui court-circuite cette couche. Aucune des deux ne couvre le trou de l'autre.

---

## Vérifier sur votre propre déploiement

Rien de ce qui précède ne se croit sur parole. Le contrôle tient en deux
mesures à comparer, sur votre installation.

1. **Compter ce qu'un assistant déclare.** Dans l'interface d'administration de
   la plateforme, ouvrir la configuration de l'assistant et relever le nombre
   d'outils cochés.
2. **Compter ce que l'endpoint expose.** Interroger le catalogue d'outils avec
   un jeton valide et compter les entrées :

   ```bash
   curl -s -H "Authorization: Bearer $JETON" \
     "https://<votre-site>/wp-json/mcp/v1/tools" \
     | python -c "import sys,json; print(len(json.load(sys.stdin)['tools']))"
   ```

3. **Comparer.** L'écart est exactement ce que le cadrage par persona ne
   protège pas.

**Un piège à connaître avant d'interpréter le résultat.** Quand on écrit
soi-même les routes qui exposent un catalogue, il est tentant de les déclarer
publiques : le catalogue n'est jamais que des métadonnées, et le rendre libre
simplifie la découverte. Conséquence directe : cette route répond alors `200` à
n'importe quel jeton, y compris un jeton révoqué. **Sonder le catalogue ne teste
donc pas l'authentification** — il teste seulement que le serveur répond. Pour
vérifier qu'un jeton est bien refusé, il faut interroger une route qui applique
réellement l'authentification, et constater le `401`.

C'est une instance du motif décrit dans
[`docs/reference/verification-verte-systeme-casse.md`](../../../docs/reference/verification-verte-systeme-casse.md) :
une sonde qui répond vert parce qu'elle mesure autre chose que ce qu'on croit.

---

## Ce que ce document ne dit pas

- **Il ne classe pas les deux plateformes.** Qu'Open WebUI applique nativement
  la vérification par utilisateur ne la rend pas supérieure : sur un site de
  contenu existant, l'appareil de capacités du CMS est déjà là et bien connu de
  l'équipe. Le point est qu'il faut alors l'appeler explicitement.
- **Il ne traite pas l'authentification elle-même** (comment un jeton est émis,
  transporté, tourné). Il traite ce qui se passe une fois qu'un appel est
  authentifié.
- **Il ne remplace pas une revue de sécurité.** Les trois couches sont un cadre
  de conception, pas une liste de contrôle exhaustive.
- **La mesure citée** (six assistants face à 88 outils) est un relevé sur une
  installation, pas une propriété du produit. Elle illustre l'écart ; la section
  précédente donne le moyen de la refaire chez soi, ce qui est la seule façon
  honnête de s'en servir.

---

## Pour aller plus loin

- [`comparatif-owui-vs-ai-engine.md`](comparatif-owui-vs-ai-engine.md) — quand
  l'une des deux plateformes est plus adaptée que l'autre.
- [`AI-Engine-WordPress/livresagites-parcours.md`](AI-Engine-WordPress/livresagites-parcours.md)
  — section « Sécurité de l'endpoint », côté jeton et capacités.
- [`Open-WebUI/`](Open-WebUI/README.md) — la plateforme et sa série de tests.

[owui-tools]: https://docs.openwebui.com/features/extensibility/plugin/tools/
