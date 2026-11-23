# Playwright-OWUI - Tests E2E pédagogiques pour Open WebUI

<!-- CATALOG-STATUS
series: GenAI-Open-WebUI
pedagogical_count: 0
breakdown: 
maturity: 
-->

[← Open WebUI](../README.md) | [↑ Plateformes conversationnelles](../../README.md) | [AI Engine (WordPress) →](../../AI-Engine-WordPress/README.md)

Cette série enseigne le test de bout en bout avec Playwright sur une application réelle : Open WebUI, une plateforme de chat d'IA générative. Le sujet change la nature de l'exercice. On n'y teste pas un formulaire ou une liste de tâches, mais une application dont les réponses arrivent en flux, varient d'un essai à l'autre, prennent un temps imprévisible et dépendent de ce que chaque instance a configuré. La série suit une mission : tenir le rôle d'ingénieur qualité d'une flotte d'instances partagées entre plusieurs écoles, de la prise en main de l'outillage jusqu'à la question d'un jour de mise en production — peut-on livrer, oui ou non ?

Elle s'adresse aux étudiants et aux développeurs qui veulent apprendre à tester une application d'IA générative, et aux testeurs qui connaissent le test d'interface classique et découvrent ce que le non-déterminisme lui fait. Il faut savoir lire du TypeScript et du Python ; aucune pratique préalable de Playwright n'est supposée.

Chaque module réunit deux artefacts. Le fichier TypeScript `.spec.ts`, exécuté par Playwright, est le moteur de test : il contient les tests commentés qui servent de matière. Le carnet Jupyter du même module en est la couche pédagogique : il raconte l'étape, lit le fichier de tests, en dresse l'inventaire sans lancer de test, et propose des exercices en Python. Les carnets s'exécutent donc sans navigateur ni instance en ligne ; les tests, eux, demandent une instance.

## Comment lire ce README

Les séries du dépôt se lisent à plusieurs vitesses, selon le principe décrit dans [« Choisir sa vitesse de lecture »](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture).

- Vous **découvrez** : suivez le parcours principal dans l'ordre, en commençant par le carnet chapeau ; les carnets se lisent sans rien installer.
- Vous **creusez un palier** : la section « Approfondissements » ajoute le projet de certification, le triage d'un test rouge et le suivi des versions de la plateforme ; « Pièges courants » rassemble ce qui fait échouer un premier test.
- Vous cherchez **ce qui reste ouvert** : « Pour aller plus loin » rassemble les questions que la série pose sans les fermer.

## Parcours principal

*Niveau Découverte pour les étapes 0 à 2, Approfondissement ensuite.* La mission se déroule des modules 01 à 05 ; le module 06 la prolonge en bonus.

| # | Notebook | Ce qu'on y apprend | Public | Pour approfondir |
|---|---|---|---|---|
| 0 | [Parcours QA-OWUI — carnet chapeau](00-Parcours-QA-OWUI.ipynb) | La carte de la mission, l'inventaire de la suite tel que Playwright le collecte quand l'outillage Node est installé, et la grille de lecture d'un résultat : succès, échec réel, test sauté pour une raison légitime, test instable. Les exercices mènent à une règle de verdict qu'on sait défendre. | Tout lecteur de la série | [Cadrage de la mission](00-Parcours-QA-OWUI.md) |
| 1 | [Découverte de Playwright et d'Open WebUI](01-decouverte/01-Decouverte-QA-OWUI.ipynb) | L'architecture d'un projet de tests, la façon dont Playwright observe la page et attend de lui-même, et le choix d'un sélecteur qui résiste aux changements d'interface. | Débutant en test d'interface | [Module 01](01-decouverte/README.md) |
| 2 | [Navigation et authentification](02-navigation-authentification/02-Navigation-Auth-QA-OWUI.ipynb) | La session authentifiée, sauvegardée une fois et réutilisée ; la différence entre un refus d'authentification et une limite de débit ; les rôles ; les routes d'administration, d'espace de travail et de canaux, dont les libellés changent selon la langue. | Débutant en test d'interface | [Module 02](02-navigation-authentification/README.md) |
| 3 | [Chat et streaming](03-chat-streaming/03-Chat-Streaming-QA-OWUI.ipynb) | Tester une réponse générée : saisir dans un éditeur de texte riche, attendre la fin d'un flux, écrire des assertions tolérantes sur un contenu qui varie, sauter proprement un test quand un service manque. | Testeur, développeur d'applications d'IA | [Triage d'un test rouge](TRIAGE-INFRA-VS-TEST.md) |
| 4 | [RAG, outils MCP et canaux](04-rag-tools-avances/04-RAG-Tools-QA-OWUI.ipynb) | Écrire un test conditionnel pour une fonction que l'instance n'a pas forcément configurée, suivre un parcours d'interface qui change d'une version à l'autre, préférer un sélecteur sémantique à un sélecteur de position, combiner l'API et le navigateur. | Testeur, intégrateur | [Module 04](04-rag-tools-avances/README.md) |
| 5 | [Multi-tenant, API et intégration continue](05-multi-tenant-ci/05-Multi-Tenant-CI-QA-OWUI.ipynb) | Tester une API sans navigateur, partager un jeton entre les tests pour ne pas buter sur la limite de débit, vérifier ce qui est isolé et ce qui est partagé entre deux instances, puis installer la suite dans un pipeline. | Testeur, ingénieur d'exploitation | [Module 05](05-multi-tenant-ci/README.md) |
| 6 | [Nouveautés de la ligne v0.10](06-nouveautes-v0.10/06-Nouveautes-v0.10-QA-OWUI.ipynb) | Tester des surfaces récentes et mouvantes — mémoire, dossiers d'équipe, raisonnement affiché en direct, compaction des longues conversations — en prouvant une version par la présence d'un champ, et en nettoyant ce que le test a créé. | Qui a suivi les étapes 3 et 5 | [Nouveautés v0.10](WHATS-NEW-v0.10.md) |

La progression est délibérée : on part de l'interface visible, on descend vers les fonctions transverses, puis on bascule vers l'API. C'est le chemin que suit un test exploratoire quand il devient une suite industrialisée, capable de tourner sans navigateur en intégration continue.

## Approfondissements

*Niveau Approfondissement.*

### Autour de 0 — le projet de certification

Le [cadrage de la mission](00-Parcours-QA-OWUI.md) décrit le livrable final, que l'étudiant produit lui-même : lancer la suite contre deux instances, interpréter les résultats, et rédiger un rapport qui tranche pour ou contre la mise en production d'une nouvelle version. Le rapport attendu couvre le périmètre testé, les résultats bruts avec la raison de chaque test sauté, l'analyse du non-déterminisme, les dérives d'interface et le verdict argumenté. Le carnet chapeau y prépare : il apprend à lire ce qu'une exécution produit avant de demander d'en lancer une.

Prérequis en plus : une seconde instance, déclarée par les variables `OWUI_TENANT2_*`.

### Autour de 3 — un test rouge n'est pas toujours un bug

Un test qui échoue dit qu'une attente n'a pas été satisfaite ; il ne dit pas pourquoi. Le guide [Triage — un test rouge n'est pas toujours un bug](TRIAGE-INFRA-VS-TEST.md) sépare trois causes qui produisent le même rouge : une régression de l'application, une dérive du test quand l'interface a bougé, une panne d'infrastructure. Il déroule des cas d'étude tirés d'incidents réels, montre comment inscrire ce triage dans le code de la suite — une sonde d'infrastructure exécutée une fois, plutôt qu'une série de tests qui rougissent ensemble — et se termine par une liste de contrôle. Sa règle : on ne conclut pas sans avoir mesuré la couche du dessous.

Prérequis en plus : aucun ; le guide se lit à partir du module 03.

### Autour de 6 — suivre les versions de la plateforme

Une suite de tests d'interface vieillit avec l'application qu'elle teste. Des notes de version accompagnent les montées successives et répondent chacune aux mêmes questions : ce qui ne change pas, ce qui est nouveau ou cassant, ce qu'on peut tester en bonus.

- [Nouveautés v0.9.1](WHATS-NEW-v0.9.1.md) : de nouvelles pages — calendrier, tâches planifiées — et de nouvelles routes d'API.
- [Nouveautés v0.10](WHATS-NEW-v0.10.md) : la mémoire repensée, les dossiers d'équipe, le raisonnement affiché en direct, la compaction automatique. L'appel d'outils natif y devient le comportement par défaut : un modèle conversationnel interrogé par l'API sans streaming peut alors renvoyer un contenu vide.
- [Nouveautés v0.11](WHATS-NEW-v0.11.md) : la refonte de l'interface. Les réglages d'administration deviennent des onglets, et la note détaille ce que ce changement a cassé dans la suite, avec les pièges mesurés au passage : un état transitoire sur lequel il ne faut pas asserter, un libellé devenu ambigu.

La suite elle-même a été revalidée sur la flotte v0.11.0 (campagne #9854) : les carnets des modules 01 à 05 le rappellent dans leur note de reproductibilité, et aucun claim de compatibilité n'est porté au-delà de cette version. Le [module 06](06-nouveautes-v0.10/README.md), qui démontre la ligne v0.10, cible v0.10.2.

Prérequis en plus : une instance dans la version concernée, pour rejouer les exemples.

## Sous-séries

*Mêmes niveaux que le parcours principal.* Chaque module porte son propre README : objectifs, théorie, exercices, et la présentation de son carnet.

**[Module 01 — Découverte](01-decouverte/README.md).** Installer Playwright et comprendre son architecture, écrire un premier test sur une application réelle, comprendre la structure d'un projet de tests, naviguer avec des sélecteurs robustes, et lancer les tests avec le navigateur visible pour déboguer.

**[Module 02 — Navigation et authentification](02-navigation-authentification/README.md).** Le mécanisme d'authentification par état de session sauvegardé, le test d'un formulaire de connexion complet, la navigation entre les sections de la plateforme, l'écriture d'une préparation réutilisable, et la gestion des redirections et des états de chargement.

**[Module 03 — Chat et streaming](03-chat-streaming/README.md).** Le module le plus riche, consacré à ce que le test d'une IA générative a de propre : une interface de chat dont la zone de saisie est un éditeur de texte riche, une réponse qui arrive jeton par jeton, des attentes adaptées, des assertions sur un contenu non déterministe, et le saut d'un test quand un service est indisponible.

**[Module 04 — RAG, outils MCP et fonctions avancées](04-rag-tools-avances/README.md).** Tester le RAG avec des bases de connaissances, interagir avec les outils MCP, tester les canaux de discussion de groupe, combiner navigation et interactions, gérer les éléments optionnels. Plusieurs tests dépendent de la configuration de l'instance et se sautent d'eux-mêmes quand la fonction est absente.

**[Module 05 — Multi-tenant, API et intégration continue](05-multi-tenant-ci/README.md).** Tester des API REST sans navigateur, comprendre l'architecture multi-tenant de la plateforme, vérifier l'isolation des données entre instances et le partage de ressources, intégrer la suite dans un pipeline. Les tests à deux instances s'activent par les variables `OWUI_TENANT2_*`.

**[Module 06 — Nouveautés v0.10](06-nouveautes-v0.10/README.md).** Module bonus, à lire après les modules 03 et 05 dont il réutilise les deux familles de tests, par l'API et par l'interface. Il montre comment écrire des tests pour la mémoire repensée, les dossiers d'équipe partageables, le raisonnement affiché en direct et la compaction automatique des longues conversations.

## Structure du dossier

*Niveau Découverte.*

```
Playwright-OWUI/
├── 00-Parcours-QA-OWUI.ipynb      # carnet chapeau
├── 00-Parcours-QA-OWUI.md         # cadrage de la mission, projet de certification
├── 01-decouverte/                 # un dossier par module, de 01 à 06 :
│   ├── README.md                  #   objectifs, théorie, exercices
│   ├── 01-Decouverte-QA-OWUI.ipynb    # couche pédagogique
│   └── 01-decouverte.spec.ts      #   moteur de test
├── helpers/
│   ├── selectors.ts               # sélecteurs centralisés
│   ├── chat.ts                    # interactions de chat : modales, envoi, attente de réponse
│   └── api.ts                     # client de l'API REST
├── fixtures/
│   └── auth.setup.ts              # authentification, exécutée une fois avant les tests
├── playwright.config.ts           # projets, délais, session réutilisée
├── package.json
├── package-lock.json
├── tsconfig.json
├── .env.example                   # gabarit de configuration
├── TRIAGE-INFRA-VS-TEST.md        # guide de triage
└── WHATS-NEW-v0.9.1.md, WHATS-NEW-v0.10.md, WHATS-NEW-v0.11.md
```

Le dépôt versionne le code des tests, les utilitaires, la configuration avec son fichier de verrouillage, les carnets, la documentation et le gabarit `.env.example`, qui ne contient que des valeurs neutres. Il ne versionne jamais :

| Motif | Pourquoi |
|---|---|
| `.env` | Secret : l'adresse et les identifiants de votre instance. |
| `.auth/*.json` | Secret : l'état de session sauvegardé par Playwright contient un jeton d'authentification. |
| `storage-state*.json` (racine), `playwright/.auth/` (racine) | Secret : mêmes cookies de session, scope global du dépôt. |
| `node_modules/`, `dist/` | Régénérables par `npm install` et par la compilation TypeScript. |
| `playwright-report/`, `test-results/`, `blob-report/`, `playwright/.cache/` | Régénérables : sorties de chaque exécution et téléchargements de navigateurs. |

Le gabarit [`.env.example`](.env.example) est le seul fichier de configuration committé : il porte des valeurs vides ou des exemples neutres, jamais une adresse ni un identifiant réels. Son inventaire actuel se lit directement dans le fichier : les clés actives couvrent l'instance (`OWUI_URL`, `OWUI_EMAIL`, `OWUI_PASSWORD`), le modèle de chat (`OWUI_CLOUD_MODEL`) et les réglages Playwright (`PLAYWRIGHT_TIMEOUT`, `PLAYWRIGHT_HEADLESS`, `PLAYWRIGHT_BROWSER`, `PLAYWRIGHT_LOCALE`) ; les clés commentées, toutes optionnelles, couvrent la seconde instance (`OWUI_TENANT2_*`), les modèles local et persona (`OWUI_LOCAL_MODEL`, `OWUI_PERSONA_MODEL`) et le modèle de raisonnement (`OWUI_REASONING_MODEL`).

Ce périmètre publiable a été tranché par [#10025](https://github.com/jsboige/CoursIA/issues/10025) (livrable 1 — périmètre publiable ; le livrable 2, les patterns `.gitignore` globaux, est dans la PR [#10057](https://github.com/jsboige/CoursIA/pull/10057)). Vérifications à rejouer avant toute contribution à ce dossier :

```bash
# 1. Check-ignore sur les 3 chemins sensibles
git check-ignore -v <racine>/.auth/owui.json          # → ignoré
git check-ignore -v <racine>/playwright-report/index.html  # → ignoré
git check-ignore -v <racine>/test-results/.last-run.json  # → ignoré

# 2. git add -An (dry-run) doit ne rien proposer de sensible
git add -An -- MyIA.AI.Notebooks/GenAI/Plateformes-Conversationnelles/Open-WebUI/Playwright-OWUI/
# (vide)

# 3. Aucun fichier credential-class dans l'index
git ls-files | grep -ciE '\.auth/|storage[-_]?state'
# 0
```

(``<racine>`` désigne la racine du clone.) Décisions et constats voisins : [#10021](https://github.com/jsboige/CoursIA/issues/10021) — même défaut de fond, un harnais de calcul non committé donne des sorties invérifiables ; [#16](https://github.com/jsboige/CoursIA/issues/16) — provisioning des services OWUI/auth de la flotte.

## Installation et prérequis

*Niveau Découverte.*

**Pour lire et exécuter les carnets** : Python 3 et Jupyter. Leurs cellules n'utilisent que la bibliothèque standard, et s'exécutent sans navigateur ni instance. Si l'outillage Node est installé, le carnet chapeau affiche l'inventaire réel de la suite ; sinon, un inventaire de fichiers.

**Pour exécuter les tests** :

- [Node.js](https://nodejs.org) 18 ou plus récent ;
- une instance Open WebUI : celle du cours, fournie par l'enseignant, ou une instance locale ;
- un compte sur cette instance, administrateur de préférence pour la suite complète ;
- au moins un modèle de chat branché sur l'instance, pour les tests qui obtiennent une réponse générée.

Aucun GPU n'est requis par la série elle-même : le besoin en calcul est celui du moteur que sert l'instance.

```bash
# Depuis ce dossier
npm install
npx playwright install chromium
cp .env.example .env
```

Complétez ensuite le fichier `.env` :

| Variable | Rôle | Nécessaire pour |
|---|---|---|
| `OWUI_URL` | Adresse de l'instance à tester | Tous les tests |
| `OWUI_EMAIL`, `OWUI_PASSWORD` | Compte de connexion | Tous les tests |
| `OWUI_CLOUD_MODEL` | Modèle rapide pour les tests de chat. Le nom doit être exactement celui qu'affiche le sélecteur de modèles ; sur une instance à plusieurs connecteurs, il est souvent préfixé par le connecteur. | Les tests de chat |
| `OWUI_LOCAL_MODEL` | Modèle local, s'il en existe un sur l'instance | Optionnelle |
| `OWUI_PERSONA_MODEL` | Modèle personnalisé, pour les tests de personas | Optionnelle, module 03 |
| `OWUI_TENANT2_URL`, `OWUI_TENANT2_EMAIL`, `OWUI_TENANT2_PASSWORD` | Seconde instance | Optionnelles, module 05 |
| `OWUI_REASONING_MODEL` | Modèle qui affiche son raisonnement ; sans lui, le test correspondant est sauté | Optionnelle, module 06 |
| `PLAYWRIGHT_TIMEOUT`, `PLAYWRIGHT_LOCALE` | Réglages lus par la configuration de Playwright : délai par test, en millisecondes, et langue du navigateur | Valeurs par défaut fournies |

Pour une instance locale, l'image publique de la plateforme suffit ; l'adresse à déclarer est alors `http://localhost:3000`, et il reste à y créer un compte administrateur :

```bash
docker run -d -p 3000:8080 --add-host=host.docker.internal:host-gateway ghcr.io/open-webui/open-webui:main
```

Vérifiez l'installation en trois temps :

```bash
npm run typecheck       # le TypeScript compile
npm run test:list       # la suite se collecte, sans instance
npm run test:module1    # le premier module s'exécute contre l'instance
```

Les deux premières commandes ne demandent aucune instance : ce sont elles que l'intégration continue du dépôt exécute sur la suite.

### Commandes utiles

```bash
npm test                        # toute la suite
npm run test:module3            # un module, de test:module1 à test:module6
npx playwright test --headed    # navigateur visible
npm run test:debug              # inspecteur de Playwright
npm run test:ui                 # interface graphique de Playwright
npm run report                  # rapport HTML de la dernière exécution
```

La suite tourne avec un seul exécutant à la fois, pour ne pas charger le moteur de langage de requêtes concurrentes, et l'authentification est faite une fois, avant les tests, par un projet de préparation dont dépend le projet principal.

## Pièges courants

*Niveau Approfondissement.* Ces quatre pièges relèvent du test lui-même. Une suite peut aussi rougir sans qu'aucun test ait de défaut : avant de corriger un test rouge, identifiez la cause avec le [guide de triage](TRIAGE-INFRA-VS-TEST.md).

### La fenêtre des nouveautés intercepte les clics

Au premier chargement, ou après une mise à jour, la plateforme affiche une fenêtre modale qui présente les nouveautés. Elle recouvre toute la page et intercepte tous les clics. Elle peut aussi apparaître avec un léger retard : une vérification immédiate la manquerait. La fonction `dismissModals()` sonde la page pendant quelques secondes et ferme toute fenêtre qui apparaît.

```typescript
import { dismissModals } from '../helpers/chat';

await page.goto('/');
await dismissModals(page);
```

### La zone de saisie n'est pas un champ de texte

La zone de saisie du chat est un éditeur de texte riche, pas un `<textarea>`. La méthode `fill()` de Playwright ne déclenche pas les événements que cet éditeur attend ; il faut cliquer puis taper au clavier.

```typescript
// Ne fonctionne pas :
await page.locator('#chat-input').fill('Bonjour');
// Fonctionne :
await page.locator('#chat-input').click();
await page.keyboard.type('Bonjour', { delay: 10 });
```

### La route de connexion limite le débit

La route `/api/v1/auths/signin` tolère peu de connexions rapprochées. Si chaque test s'authentifie, la suite reçoit une réponse 429 avant la fin, et ce 429 n'est pas un échec fonctionnel de l'application. On s'authentifie une fois, dans `beforeAll()`, et on réutilise le jeton.

```typescript
let token = '';
test.beforeAll(async ({ request }) => {
  token = await apiLogin(request, baseUrl, email, password);
});
test('lister les modèles', async ({ request }) => {
  const models = await getModels(request, baseUrl, token);
});
```

### Une API répond en HTML

Derrière un serveur mandataire, certaines routes d'API renvoient la page HTML de l'application au lieu de JSON, notamment quand le chemin ne se termine pas par une barre oblique. Les fonctions de `helpers/api.ts` terminent ces chemins par la barre oblique, et celle qui liste les fonctions installées vérifie que la réponse n'est pas du HTML avant de la lire ; dans les tests, une API indisponible conduit à un saut, avec sa raison.

## Questions fréquentes

*Niveau Découverte.*

**`npm install` échoue, ou Playwright ne trouve pas Chromium.** Vérifiez la version de Node par `node --version`, puis installez le navigateur par `npx playwright install chromium`. Sous Linux, `npx playwright install-deps chromium` installe les bibliothèques système qui manqueraient. Derrière un proxy ou un pare-feu, le téléchargement du navigateur peut être dirigé vers un miroir : `PLAYWRIGHT_DOWNLOAD_HOST=https://proxy.example.com npx playwright install chromium`.

**Les tests de chat dépassent leur délai.** Ils attendent la réponse d'un moteur de langage réel, qui peut être lent ou chargé. Vérifiez d'abord que l'instance répond et que le modèle déclaré dans `.env` existe sous ce nom exact ; allongez ensuite le délai, globalement par `PLAYWRIGHT_TIMEOUT` ou pour un test par `test.setTimeout()`. Le module 03 explique les stratégies d'attente et d'assertion sur un contenu non déterministe.

**Peut-on suivre la série sans instance ?** Les carnets, oui, intégralement. Les tests demandent une instance ; sans elle, on peut encore vérifier que la suite compile et se collecte.

**Les tests du module 04 sont presque tous sautés.** C'est attendu sur une instance où ces fonctions ne sont pas configurées : il faut au moins une base de connaissances, des outils MCP configurés et au moins un canal. Chaque test sauté donne sa raison. Lisez-la : un test sauté parce que la fonction est absente est sain, un test sauté parce que son sélecteur est devenu obsolète masque une dérive de l'interface.

**Comment adapter la suite à une autre version de la plateforme ?** Les mécanismes que teste la suite — authentification, éditeur de chat, streaming — sont restés stables de la v0.8 à la v0.11, mais chaque refonte d'interface a cassé des sélecteurs ; la suite est aujourd'hui revalidée sur la flotte v0.11.0 (campagne #9854). Si votre instance diffère :

1. **Sélecteurs** : vérifiez avec le mode debug (`npx playwright test --debug`) que les sélecteurs de [`helpers/selectors.ts`](helpers/selectors.ts) correspondent à votre version.
2. **Libellés multilingues** : la ligne v0.9 a changé certains libellés. Adaptez les tests ou préférez `getByRole()`, plus robuste que `getByText()`.
3. **Nouvelles fonctionnalités** : la v0.9.1 ajoute calendrier et tâches planifiées (voir [Nouveautés v0.9.1](WHATS-NEW-v0.9.1.md)) ; la v0.10 ajoute la mémoire persistante, les dossiers d'équipe et le raisonnement streamé (voir [Nouveautés v0.10](WHATS-NEW-v0.10.md) et le [module 06](06-nouveautes-v0.10/README.md)) ; la v0.11 refond l'interface, dont les réglages d'administration devenus des onglets (voir [Nouveautés v0.11](WHATS-NEW-v0.11.md)). Ce sont de bons candidats pour des exercices bonus.
4. **Changement de comportement v0.10** : l'appel d'outils natif devient le comportement par défaut. Les modèles conversationnels sans outils qui répondaient normalement peuvent renvoyer des réponses vides s'ils héritent de ce mode — à surveiller lors de l'adaptation des tests de chat.

Le [module 01](01-decouverte/README.md) enseigne les sélecteurs robustes (`getByRole`, `getByTestId`), qui résistent aux changements d'interface.

## Pour aller plus loin

*Niveau Recherche.*

- **Certifier une montée de version.** Le projet final demande un verdict, pas une liste de tests verts : il faut dire ce qui a été testé, ce qui ne l'a pas été, et pourquoi on livre quand même, ou pas.
- **Que vaut un test sauté ?** Le carnet du module 05 donne l'exemple d'un verdict honnête : sans seconde instance, le tenant principal est validé, mais l'isolation n'est pas certifiée — elle est remise à plus tard. Décider quand un saut est une information et quand il est un angle mort reste un jugement.
- **Où s'arrête une assertion tolérante ?** Une assertion assez souple pour accepter toutes les réponses d'un modèle n'en refuse plus aucune. Trouver la formulation qui tolère la variation sans devenir vide est la difficulté propre au test d'une IA générative.
- **Ce que l'API ne voit pas.** Sur l'autre plateforme de la famille, le [parcours QA d'AI Engine](../../AI-Engine-WordPress/05-Playwright-AI-Engine/README.md) montre un état que seule l'ouverture d'une page dans un navigateur modifie ; l'étude de cas [Quand la vérification est verte et le système est cassé](../../../../../docs/reference/verification-verte-systeme-casse.md) catalogue les classes de vérifications trompeuses.

## Ressources

- [Open WebUI — tour de la plateforme](../00-Tour-Plateforme/README.md) — l'interface que cette série teste, vue par ses écrans.
- [Vibe-Coding](../../../Vibe-Coding/README.md) — le développement assisté par IA, dont cette série est le pendant côté validation.
- [Documentation de Playwright](https://playwright.dev/) — la référence de l'outil.
- [Dépôt d'Open WebUI](https://github.com/open-webui/open-webui) — le code et les notes de version de la plateforme.
- [TipTap](https://tiptap.dev/) — l'éditeur de texte riche de la zone de saisie du chat, que le module 03 apprend à piloter au clavier.
- [Spécification du protocole MCP](https://modelcontextprotocol.io) — la référence du protocole que teste le module 04.
