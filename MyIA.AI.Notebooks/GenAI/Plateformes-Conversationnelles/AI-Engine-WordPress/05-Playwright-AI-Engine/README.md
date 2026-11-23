# Parcours QA — ce que l'API ne voit pas

[← AI Engine (WordPress)](../README.md) | [↑ Plateformes conversationnelles](../../README.md) | [Instance jetable →](../instance-jetable/README.md)

La série [« AI Engine par son API »](../03-Functional/README.md) mesure le plugin par ses interfaces machine : l'API d'administration, la route des visiteurs, le serveur MCP. Toutes ces sondes partagent un angle mort : aucune ne charge l'application d'administration que le navigateur exécute. Or cette application n'est pas un afficheur passif, elle écrit. Ce dossier enseigne ce qu'un test d'interface constate et qu'un test d'API ne peut pas voir : une valeur posée par l'API peut être défaite par le seul fait qu'une personne ouvre une page de réglages, sans cliquer sur quoi que ce soit.

Il s'adresse à qui écrit ou relit des tests automatisés sur une plateforme dont l'interface vit sa propre vie, et à qui administre un site en s'appuyant sur des scripts. Il faut savoir lire du Python et avoir suivi le premier carnet de la chaîne, [Présenter AI Engine par son API](../03-Functional/03-5-Multi-Provider/presenter-ai-engine-par-son-api.ipynb) ; aucune pratique préalable de Playwright n'est supposée.

## Comment lire ce README

Les séries du dépôt se lisent à plusieurs vitesses, selon le principe décrit dans [« Choisir sa vitesse de lecture »](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture).

- Vous **découvrez** : lisez le parcours principal ; le carnet se suit palier par palier, sorties enregistrées à l'appui.
- Vous **creusez un palier** : la section « Approfondissements » détaille la course entre les deux écritures et la leçon de méthode qu'elle porte.
- Vous cherchez **ce qui reste ouvert** : « Pour aller plus loin » reprend les trois exercices du carnet et les prolongements dans le dépôt.

## Parcours principal

*Niveau Découverte.* Le dossier tient en un carnet, qui se lit après la chaîne « AI Engine par son API ».

| # | Notebook | Ce qu'on y apprend | Public | Pour approfondir |
|---|---|---|---|---|
| 1 | [Parcours QA — ce que l'API ne voit pas](00-Parcours-QA-AI-Engine.ipynb) | Suivre un indicateur témoin, `module_workspace`, sur un escalier où chaque palier ajoute un acteur : lire l'état par l'API ; l'écrire par l'API et obtenir une relecture concordante ; ouvrir une page de réglages dans un vrai navigateur sans rien toucher, et écouter ce qu'elle envoie ; relire ce que le serveur a gardé. Rejouer la manipulation, compter, puis dater les requêtes pour comprendre ce qui décide de l'issue. | Testeur, intégrateur, administrateur | [Auditer la conformité visuelle](../06-Securite-et-Methode/auditer-la-conformite-visuelle.ipynb) |

Les paliers du carnet, et ce que chacun établit :

| Palier | Ce qu'on fait | Ce qu'on observe |
|---|---|---|
| 0 | Lire l'état par l'API | Le serveur répond sans ambiguïté : c'est la photographie qu'un tableau de bord ou un script verrait. |
| 1 | Écrire `True` par l'API | Réponse favorable et relecture concordante : un test qui ne parle qu'à l'API s'arrête ici, au vert, et il a raison sur ce qu'il vérifie. |
| 2 | Ouvrir la page de réglages, ne toucher à rien | Le navigateur émet de lui-même deux écritures `settings/update` contradictoires : la première répète l'état du serveur, la seconde applique la règle de l'application. |
| 3 | Relire | Une seule valeur a été retenue par le serveur, et aucune des deux écritures n'a été signalée comme une erreur. |

## Approfondissements

*Niveau Approfondissement.*

### Autour de 1 — une course entre deux écritures

Le carnet date les envois et les réponses. Les deux écritures partent à quelques dizaines de millisecondes d'intervalle, chacune relit l'ensemble des réglages, le modifie et le réécrit en entier : celle qui arrive en dernier efface l'autre. C'est la forme classique de la mise à jour perdue, et le serveur répond favorablement aux deux requêtes. En mettant tous les indicateurs à `True` avant d'ouvrir la page, la différence entre les deux envois donne la liste de ceux que l'application rabat à `False` : elle se reconstitue sans lire une ligne de code, uniquement d'après ce qui passe sur le réseau, et elle dépasse l'indicateur témoin. Un test qui ne surveille que son témoin resterait vert pendant que d'autres réglages changent.

Trois constats en découlent.

1. **Le verrou est côté client.** Le serveur accepte ces réglages ; c'est l'application d'administration qui, au montage, en renvoie une version rabattue.
2. **Aucune sonde d'API ne pouvait le voir.** Le désaccord n'existe qu'à l'instant où un navigateur charge la page. Une suite de tests REST reste verte pendant que la fonctionnalité est éteinte pour l'utilisateur.
3. **Une sonde de navigateur ne suffit pas non plus si elle n'observe qu'une fois.** L'issue dépend de l'ordre d'arrivée de deux requêtes. La contre-mesure n'est pas une meilleure assertion sur un tour, c'est un taux : répéter, compter, publier la proportion. Le carnet rejoue la manipulation et affiche cette proportion ; elle se lit dans sa sortie enregistrée, et une série courte et homogène ne prouve pas que la course a toujours le même vainqueur.

Le carnet se termine en rendant l'instance à son état de référence, et sur une observation : plusieurs des modules que le script d'installation [`seed-valmont.php`](../instance-jetable/seed-valmont.php) déclare actifs figurent dans la liste que l'application rabat. L'état documenté de l'instance n'est donc pas un état stable : il suffit de consulter les réglages pour qu'il commence à s'en écarter.

Prérequis en plus : aucun au-delà de ceux du carnet ; la lecture gagne à avoir vu, dans [Brancher plusieurs providers](../03-Functional/03-5-Multi-Provider/brancher-plusieurs-providers-par-l-api.ipynb), que la route `settings/update` remplace l'ensemble des réglages au lieu de le mettre à jour.

## Installation et prérequis

*Niveau Découverte.*

- **L'instance jetable « Maison Valmont »** démarrée et son fichier `instance-jetable/.env` renseigné : le [README de l'instance](../instance-jetable/README.md) donne le montage, le port et la création du mot de passe d'application. Aucune adresse ni clé n'est écrite dans le carnet.
- **Python 3.10 ou plus récent** avec `requests`, `python-dotenv` et `playwright` (`pip install requests python-dotenv playwright`), puis le navigateur piloté : `playwright install chromium`.
- **Aucun moteur de langage, aucun GPU** : le carnet mesure des réglages et des requêtes, pas une réponse générée.

Depuis ce dossier, le carnet s'exécute en place par :

```bash
python -m nbconvert --execute --to notebook --inplace 00-Parcours-QA-AI-Engine.ipynb
```

Le carnet pilote un vrai processus navigateur. Un noyau Jupyter tourne déjà dans une boucle asynchrone ; le pilotage est donc confié à un fil dédié par la fonction `en_arriere_plan()` de la cellule de configuration, qui rétablit le réglage d'origine en sortant.

Le carnet bascule des indicateurs `module_*` du plugin. Sa dernière cellule les remet dans l'état que le script d'installation déclare, et le vérifie par l'API ; aucun contenu, aucun utilisateur, aucun chatbot n'est touché. Exécutez-le sur l'instance jetable, jamais sur un site en service.

### Périmètre publiable — vérifications avant contribution

Ce dossier vit dans un dépôt public. La cible est unique : l'instance jetable locale, corpus entièrement synthétique — jamais une instance réelle, jamais de données réelles. Aucune valeur sensible ne doit entrer dans les fichiers committés : les adresses, identifiants et clés viennent de `instance-jetable/.env`, gitignoré, et seul son `.env.example` documente les variables attendues. Les sorties sont committées telles qu'exécutées, jamais retouchées à la main. Vérification rapide avant toute contribution à ce dossier :

```bash
# le .env ne doit jamais entrer dans l'index
git check-ignore -v ../instance-jetable/.env

# aucune valeur sensible dans le notebook
grep -nE "Bearer |password|localhost:80(8|9)[0-9]" 00-Parcours-QA-AI-Engine.ipynb
```

## Pour aller plus loin

*Niveau Recherche.*

- **À partir de combien de tours un taux devient-il une mesure ?** Le premier exercice du carnet demande de rendre le taux observé avec de quoi juger sa fiabilité, par un intervalle de confiance.
- **Quelles pages d'administration écrivent ?** Le deuxième exercice cartographie les pages qui émettent ces écritures au chargement.
- **Écrire la sonde qu'on aurait voulu avoir** : le troisième exercice demande un test qui échoue de façon fiable sur un défaut qui ne se montre pas à chaque fois, le point dur de tout test de concurrence.
- **D'autres vérifications vertes sur un système qui ne l'est pas** : l'étude de cas [Quand la vérification est verte et le système est cassé](../../../../../docs/reference/verification-verte-systeme-casse.md) en catalogue les classes ; le carnet [Auditer la conformité visuelle](../06-Securite-et-Methode/auditer-la-conformite-visuelle.ipynb) traite celle du rendu que personne ne regarde.

## Ressources

- [Tour de la plateforme](../00-Tour-Plateforme/README.md) — les écrans d'administration dont ce parcours écoute le trafic.
- [Les fonctionnalités par l'API](../03-Functional/README.md) — la chaîne dont ce dossier couvre l'angle mort.
- [Tests de bout en bout pour Open WebUI](../../Open-WebUI/Playwright-OWUI/README.md) — le dossier symétrique sur l'autre plateforme de la famille.
- [Documentation de Playwright pour Python](https://playwright.dev/python/) — la référence de l'outil.
