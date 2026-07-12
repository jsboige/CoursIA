# Playwright-OWUI - Tests E2E pédagogiques pour Open WebUI

<!-- CATALOG-STATUS
series: GenAI-Open-WebUI
pedagogical_count: 7
breakdown: Open-WebUI=7
maturity: PRODUCTION=6, BETA=1
-->

[← Documentation GenAI](../../README.md) | [↑ Open-WebUI](../README.md) | [→ Vibe-Coding](../../Vibe-Coding/README.md)

> **Refonte pédagogique en cours (#4433).** Cette série évolue d'un banc de tests vers un **parcours QA narratif** : fil rouge « QA Engineer d'une flotte GenAI multi-tenant », format hybride notebook + tests E2E réels conservés en backend, et projet de certification final. Point d'entrée : **[00-Parcours-QA-OWUI.md](./00-Parcours-QA-OWUI.md)** (cadrage de la mission). La flotte multi-tenant est passée en **Open WebUI v0.10.2** (1er juillet 2026) : le nouveau **module [06](06-nouveautes-v0.10/)** en démontre les nouveautés (mémoire, dossiers d'équipe, raisonnement streamé). Les modules 01-05, rédigés sur la base v0.9.x, seront revalidés dans le cadre de la refonte.

Série pédagogique complète pour apprendre **Playwright** (framework de tests E2E) en testant une application réelle : **Open WebUI**, une plateforme de chat IA générative.

> **Format particulier** : Contrairement aux autres sous-domaines GenAI qui utilisent des Jupyter Notebooks (.ipynb), cette série utilise des **fichiers TypeScript (.spec.ts)** exécutés par Playwright. Chaque module contient un `README.md` avec la théorie et les explications, et un fichier `.spec.ts` avec les tests commentés qui servent d'exercices pratiques. Les tests sont auto-documentés : chaque test contient des commentaires pédagogiques expliquant les concepts, et des exercices supplémentaires à compléter par l'étudiant.

## Pourquoi cette série ?

Cette série se distingue des tutoriels Playwright classiques par son sujet :
- On ne teste pas un simple formulaire ou une todo-list
- On teste une **vraie application de production** avec des **modèles d'IA générative**
- Les défis sont réels : streaming, non-déterminisme, latence variable, multi-tenant

## Structure

```
Playwright-OWUI/
├── 01-decouverte/                    # Premier contact avec Playwright
│   ├── README.md                     # Théorie + exercices
│   └── 01-decouverte.spec.ts         # 4 tests : navigation, sélecteurs, screenshots
├── 02-navigation-authentification/   # Auth & navigation dans OWUI
│   ├── README.md
│   └── 02-navigation-auth.spec.ts    # 8 tests : login, admin, workspace, channels
├── 03-chat-streaming/                # Le coeur : tester le chat IA
│   ├── README.md
│   └── 03-chat-streaming.spec.ts     # 7 tests : chat, streaming, markdown, edit
├── 04-rag-tools-avances/             # RAG, MCP tools, channels
│   ├── README.md
│   └── 04-rag-tools.spec.ts          # 7 tests : KBs, outils MCP, canaux
├── 05-multi-tenant-ci/               # API tests, multi-tenant, CI/CD
│   ├── README.md
│   └── 05-api-multi-tenant.spec.ts   # 8 tests : API REST, isolation, partage
├── 06-nouveautes-v0.10/              # Nouveautés v0.10 (mémoire, dossiers, raisonnement)
│   ├── README.md
│   └── 06-nouveautes.spec.ts         # 7 tests : mémoire, dossiers, raisonnement, compaction
├── helpers/                          # Fonctions utilitaires réutilisables
│   ├── selectors.ts                  # Sélecteurs CSS centralisés (+ REASONING/FOLDER/MEMORY)
│   ├── chat.ts                       # Helpers d'interaction chat
│   └── api.ts                        # Client API REST (+ mémoire & dossiers v0.10)
├── fixtures/                         # Setup et configuration
│   └── auth.setup.ts                 # Authentification automatique
├── .auth/                            # Sessions sauvegardées (gitignore)
├── .env.example                      # Template de configuration
├── .gitignore
├── package.json
├── tsconfig.json                     # Typecheck CI (tsc --noEmit)
├── playwright.config.ts
├── WHATS-NEW-v0.9.1.md               # Nouveautés v0.9.1 (historique)
├── WHATS-NEW-v0.10.md                # Nouveautés v0.10 (côté étudiant)
└── README.md                         # Ce fichier
```

## Modules

### Module 01 — Découverte de Playwright & OWUI (2-3h)
*Niveau Débutant*

- Installation et configuration de Playwright
- Premier test : vérifier le chargement de la page
- Sélecteurs CSS, ARIA, et sémantiques
- Mode headed et screenshots
- **4 tests + exercices**

### Module 02 — Navigation & Authentification (2-3h)
*Niveau Débutant+*

- Pattern d'authentification par storageState
- Navigation entre les sections d'OWUI (admin, workspace, channels)
- Gestion des labels multilingues (FR/EN)
- Routes SvelteKit
- **8 tests + exercices**

### Module 03 — Chat & Streaming LLM (3h)
*Niveau Intermédiaire*

- L'éditeur TipTap : `keyboard.type()` vs `fill()`
- Gestion du streaming (polling, waitForFunction)
- Assertions sur du contenu non-déterministe
- Skip gracieux pour services indisponibles
- Actions sur les messages (régénérer, éditer)
- **7 tests + exercices**

### Module 04 — RAG, Outils MCP & Fonctionnalités avancées (3h)
*Niveau Intermédiaire+*

- RAG : attacher une Knowledge Base via le raccourci #
- Outils MCP (Model Context Protocol) : recherche web
- Channels : canaux de discussion collaborative
- Tests conditionnels sur la configuration
- **7 tests + exercices**

### Module 05 — Multi-tenant, API Testing & CI/CD (3-4h)
*Niveau Expert*

- Tests API avec APIRequestContext (sans navigateur)
- Architecture multi-tenant : isolation et partage
- Comparaison cross-instance de données
- Intégration CI/CD (GitHub Actions)
- **8 tests + exercices**

### Module 06 — Les nouveautés v0.10 (3h)
*Niveau Expert*

- **Mémoire** persistante : CRUD via API + preuve du champ `type` (nouveauté v0.10)
- **Dossiers** et partage d'équipe (permissions lecture/écriture)
- **Raisonnement streamé** : afficher le bloc « réflexion » d'un modèle thinking (skip gracieux)
- **Compaction automatique** du contexte : vérifier que le fil de conversation tient sur plusieurs tours
- Détection de fonctionnalité (feature-detection) et nettoyage systématique via `finally`
- **7 tests + exercices** — voir aussi [WHATS-NEW-v0.10.md](./WHATS-NEW-v0.10.md)

## Installation rapide (5 minutes)

### 1. Prerequisites

- **Node.js 18+** installé ([nodejs.org](https://nodejs.org))
- Une **instance Open WebUI** accessible :
  - Instance de cours fournie par l'enseignant, OU
  - Instance locale via Docker : `docker run -p 3000:8080 ghcr.io/open-webui/open-webui:main`

### 2. Installation

```bash
# Se placer dans le répertoire
cd GenAI/Playwright-OWUI

# Installer les dépendances
npm install

# Installer le navigateur Chromium (télécharge ~200 Mo)
npx playwright install chromium
```

### 3. Configuration

```bash
# Copier le template de configuration
cp .env.example .env

# Editer .env avec vos identifiants
# (Utilisez votre éditeur préféré)
```

**Variables minimales à remplir dans `.env` :**

| Variable | Description | Exemple |
|----------|-------------|---------|
| `OWUI_URL` | URL de l'instance Open WebUI | `https://open-webui.myia.io` |
| `OWUI_EMAIL` | Email de connexion | `etudiant@ecole.fr` |
| `OWUI_PASSWORD` | Mot de passe | `monMotDePasse` |

**Variables optionnelles :**

| Variable | Description | Module |
|----------|-------------|--------|
| `OWUI_CLOUD_MODEL` | Modèle cloud pour les tests de chat | 03 |
| `OWUI_LOCAL_MODEL` | Modèle local (vLLM/Ollama) | 03 |
| `OWUI_PERSONA_MODEL` | Modèle persona/custom | 03 |
| `OWUI_TENANT2_*` | Instance secondaire (multi-tenant) | 05 |
| `OWUI_REASONING_MODEL` | Modèle « thinking » affichant son raisonnement (sinon test sauté) | 06 |

### 4. Vérification

```bash
# Lancer le module 01 pour vérifier que tout fonctionne
npm run test:module1

# En mode visible (pour voir le navigateur)
npx playwright test --grep "01" --headed
```

## Commandes utiles

```bash
# Lancer tous les tests
npm test

# Lancer un module spécifique
npm run test:module1    # Module 01
npm run test:module2    # Module 02
npm run test:module3    # Module 03
npm run test:module4    # Module 04
npm run test:module5    # Module 05
npm run test:module6    # Module 06 (nouveautés v0.10)

# Mode visible (navigateur affiche)
npx playwright test --headed

# Mode debug (inspecteur Playwright)
npm run test:debug

# Interface graphique Playwright
npm run test:ui

# Vérifier que tout compile et se collecte (sans instance live, comme la CI)
npm run typecheck       # tsc --noEmit
npm run test:list       # énumère les tests sans les exécuter

# Voir le rapport HTML des derniers tests
npm run report
```

## Concepts clés appris

| Concept | Module | Description |
|---------|--------|-------------|
| Sélecteurs | 01 | IDs, ARIA, getByRole, getByText |
| storageState | 01-02 | Session authentifiée réutilisable |
| Auto-wait | 01 | Playwright attend automatiquement |
| TipTap/fill() | 03 | keyboard.type() pour éditeurs rich text |
| Streaming | 03 | Polling et waitForFunction |
| test.skip() | 03-04 | Skip gracieux pour services indisponibles |
| API testing | 05 | APIRequestContext sans navigateur |
| Multi-tenant | 05 | Isolation et partage de données |
| CI/CD | 05 | GitHub Actions, rapports, artefacts |
| Feature-detection | 06 | Prouver une nouveauté via un champ de réponse (ex. `type` sur la mémoire) |
| Nettoyage (`finally`) | 06 | Toujours supprimer les données de test créées (mémoire, dossiers) |
| Comportement observable | 06 | Tester la compaction/le raisonnement par leur effet, pas leur implémentation |

## Pièges courants et solutions

Ces pièges ont été découverts lors de la validation initiale de la suite de tests.
Ils sont documentés ici car ils sont représentatifs de vrais problèmes
rencontrés lors du test E2E d'applications web modernes.

### 1. Modal "Quoi de neuf" (Changelog)

**Problème** : Open WebUI affiche un dialogue modal au premier chargement (changelog des mises à jour). Ce modal a un overlay plein écran (`z-index: 9999`) qui intercepte TOUS les clics.

**Solution** : Le helper `dismissModals()` ferme automatiquement ces dialogues avant chaque interaction. Il essaie plusieurs stratégies : bouton de fermeture, touche Échap, clic en dehors.

```typescript
import { dismissModals } from '../helpers/chat';
// Dans beforeEach :
await page.goto('/');
await dismissModals(page);
```

### 2. Éditeur TipTap (fill() ne fonctionne pas)

**Problème** : Open WebUI utilise TipTap/ProseMirror au lieu d'un `<textarea>`. La méthode `fill()` de Playwright ne déclenche pas les événements nécessaires.

**Solution** : Toujours utiliser `keyboard.type()` pour saisir du texte dans le chat :

```typescript
// FAUX :
await page.locator('#chat-input').fill('Bonjour');
// CORRECT :
await page.locator('#chat-input').click();
await page.keyboard.type('Bonjour', { delay: 10 });
```

### 3. Rate limiting de l'API d'authentification

**Problème** : L'endpoint `/api/v1/auths/signin` a un rate limit strict (~2 min entre appels). Si chaque test fait son propre login, on atteint rapidement le 429.

**Solution** : S'authentifier UNE FOIS dans `beforeAll()` et réutiliser le token :

```typescript
let token = '';
test.beforeAll(async ({ request }) => {
  token = await apiLogin(request, baseUrl, email, password);
});
test('...', async ({ request }) => {
  // Reutiliser 'token' directement
  const models = await getModels(request, baseUrl, token);
});
```

### 4. APIs retournant du HTML (reverse proxy)

**Problème** : Certaines APIs (knowledge bases, functions) retournent du HTML au lieu de JSON quand le reverse proxy intercepte la requête ou la redirige.

**Solution** : Vérifier le Content-Type avant de parser, et utiliser `test.skip()` si l'API n'est pas disponible en JSON.

## Liens utiles

- [Documentation Playwright](https://playwright.dev/)
- [Open WebUI](https://github.com/open-webui/open-webui)
- [TipTap Editor](https://tiptap.dev/)
- [Model Context Protocol (MCP)](https://modelcontextprotocol.io/)

## Origine

Cette série pédagogique a été créée dans le cadre du cycle GenAI CoursIA,
en complement des ateliers Vibe-Coding (Claude Code et Roo Code).
Elle utilise les tests E2E réels du projet Open WebUI comme base pédagogique.

## FAQ

### `npm install` echoue ou Playwright ne trouve pas Chromium

Playwright (utilise dans les modules [01](01-decouverte/) a [05](05-multi-tenant-ci/)) requiert Node.js 18+ et télécharge Chromium (~200 Mo). Si erreur :

```bash
# Verifier Node.js
node --version  # doit afficher v18+

# Installer Playwright browsers
npx playwright install chromium

# Si erreur de permissions (Linux/Mac)
npx playwright install-deps chromium
```

Si vous êtes derrière un proxy ou firewall, télécharger manuellement : `PLAYWRIGHT_DOWNLOAD_HOST=https://proxy.example.com npx playwright install chromium`. Le module [01](01-decouverte/) couvre la configuration pas-à-pas.

### Les tests échouent avec "Timeout exceeded" sur le chat

Le module [03](03-chat-streaming/) teste le chat avec un LLM réel via streaming. Les timeouts sont allongés (30-60s) mais les LLM lents ou surchargés peuvent les dépasser. Mitigation :

```typescript
// Augmenter le timeout pour un test spécifique
test('chat réponse', { tag: '@slow' }, async ({ page }) => {
  test.setTimeout(120_000); // 2 minutes
  // ...
});
```

- Vérifier que l'instance OWUI est accessible : `curl $OWUI_URL/api/v1/models`
- Le streaming utilise `page.waitForFunction()` — si le modèle ne stream pas, le poll tourne en boucle.
- Le module [03](03-chat-streaming/) explique les stratégies d'assertion sur du contenu non-déterministe.

### Peut-on utiliser cette série sans instance Open WebUI ?

Partiellement. Les modules [01](01-decouverte/) (navigation, sélecteurs) et [05](05-multi-tenant-ci/) (API testing) fonctionnent sur toute application web. Les modules [02](02-navigation-authentification/) à [04](04-rag-tools-avances/) sont spécifiques à OWUI (auth, chat, RAG).

Pour une instance locale rapide :

```bash
# OWUI avec modèles Ollama (local, pas de clé API)
docker run -d -p 3000:8080 --add-host=host.docker.internal:host-gateway ghcr.io/open-webui/open-webui:main

# Ou avec vLLM (GPU requis)
# Configurer OWUI_LOCAL_MODEL dans .env
```

Le module [01](01-decouverte/) explique comment pointer Playwright vers votre instance via `.env`.

### Les tests du module 04 (RAG/MCP) sont tous skip

Le module [04](04-rag-tools-avances/) teste les Knowledge Bases, les outils MCP et les channels. Les 5 skips dans les résultats de validation viennent de fonctionnalités non configurées sur l'instance OWUI :

- **Knowledge Bases** : nécessitent un upload préalable de documents via l'interface OWUI.
- **Outils MCP** : le serveur MCP doit être configuré dans les paramètres OWUI (Admin > Tools).
- **Channels** : fonctionnalité collaborative qui requiert plusieurs utilisateurs actifs.

Pour activer ces tests, configurer les fonctionnalités correspondantes dans OWUI et décommenter les `test.skip()` dans [04-rag-tools.spec.ts](04-rag-tools-avances/04-rag-tools.spec.ts).

### Quelle différence entre cette série et les ateliers Vibe-Coding ?

| Critère | Playwright-OWUI | Vibe-Coding |
|---------|-----------------|-------------|
| **Focus** | Tests E2E automatisés | Développement assisté par IA |
| **Langage** | TypeScript (.spec.ts) | Naturel (prompt engineering) |
| **Outil** | Playwright | Claude Code / Roo Code |
| **Public** | Testeurs QA, dev backend | Développeurs, débutants |
| **Non-déterminisme** | Gère (streaming, LLM) | N/A |

Les deux séries sont complémentaires : Vibe-Coding ([README](../../Vibe-Coding/README.md)) couvre le développement assisté par IA, tandis que Playwright-OWUI couvre la validation automatisée des interfaces générées.

### Comment adapter les tests a une autre application OWUI (version ou config différente) ?

Les sélecteurs CSS et les patterns d'auth sont stables entre OWUI v0.8.x et v0.10.x. Si votre instance diffère :

1. **Sélecteurs** : vérifier avec le mode debug (`npx playwright test --debug`) que les sélecteurs dans [helpers/selectors.ts](helpers/selectors.ts) correspondent a votre version.
2. **Labels multilingues** : OWUI v0.9+ a changé certains labels. Adapter dans les tests ou utiliser `getByRole()` (plus robuste que `getByText()`).
3. **Nouvelles fonctionnalités** : OWUI v0.9.1 ajoute Calendar, Automations, Desktop app (voir `WHATS-NEW-v0.9.1.md`) ; OWUI v0.10 ajoute la mémoire persistante, les dossiers d'équipe et le raisonnement streamé (voir `WHATS-NEW-v0.10.md` et le module [06](06-nouveautes-v0.10/)). Ce sont de bons candidats pour des exercices bonus.
4. **Changement de comportement v0.10** : le *native tool calling* devient le défaut. Les modèles conversationnels (sans outils) qui répondaient normalement peuvent renvoyer des réponses vides s'ils héritent de ce mode — à surveiller lors de l'adaptation des tests de chat.

Le module [01](01-decouverte/) enseigne les sélecteurs robustes (`getByRole`, `getByTestId`) qui resistent aux changements d'UI.

---

*Version 1.2.0 — Juillet 2026 (module 06 ajouté, validé sur OWUI v0.10.2)*
