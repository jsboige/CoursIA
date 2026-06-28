# Playwright-OWUI - Tests E2E pédagogiques pour Open WebUI

<!-- CATALOG-STATUS
series: GenAI-Playwright-OWUI
pedagogical_count: 0
breakdown: 
maturity: 
-->

[← Documentation GenAI](../../README.md) | [↑ Open-WebUI](../README.md) | [→ Vibe-Coding](../../Vibe-Coding/README.md)

> **Refonte pédagogique en cours (#4433).** Cette série évolue d'un banc de tests vers un **parcours QA narratif** : fil rouge « QA Engineer d'une flotte GenAI multi-tenant », format hybride notebook + tests E2E réels conservés en backend, et projet de certification final. Point d'entrée : **[00-Parcours-QA-OWUI.md](./00-Parcours-QA-OWUI.md)** (cadrage de la mission). La revalidation cible **Open WebUI v0.9.6** (Phase 3, en cours) ; la mention « v0.9.1 » plus bas est périmée et sera reprise à ce moment-là.

Serie pédagogique complète pour apprendre **Playwright** (framework de tests E2E) en testant une application réelle : **Open WebUI**, une plateforme de chat IA générative.

> **Format particulier** : Contrairement aux autres sous-domaines GenAI qui utilisent des Jupyter Notebooks (.ipynb), cette série utilise des **fichiers TypeScript (.spec.ts)** exécutés par Playwright. Chaque module contient un `README.md` avec la théorie et les explications, et un fichier `.spec.ts` avec les tests commentés qui servent d'exercices pratiques. Les tests sont auto-documentés : chaque test contient des commentaires pédagogiques expliquant les concepts, et des exercices supplémentaires a compléter par l'étudiant.

## Pourquoi cette série ?

Cette série se distingue des tutoriels Playwright classiques par son sujet :
- On ne teste pas un simple formulaire ou une todo-list
- On teste une **vraie application de production** avec des **modèles d'IA générative**
- Les defis sont réels : streaming, non-determinisme, latence variable, multi-tenant

## Structure

```
Playwright-OWUI/
├── 01-decouverte/                    # Premier contact avec Playwright
│   ├── README.md                     # Theorie + exercices
│   └── 01-decouverte.spec.ts         # 4 tests : navigation, selecteurs, screenshots
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
├── helpers/                          # Fonctions utilitaires reutilisables
│   ├── selectors.ts                  # Selecteurs CSS centralises
│   ├── chat.ts                       # Helpers d'interaction chat
│   └── api.ts                        # Client API REST
├── fixtures/                         # Setup et configuration
│   └── auth.setup.ts                 # Authentification automatique
├── .auth/                            # Sessions sauvegardees (gitignore)
├── .env.example                      # Template de configuration
├── .gitignore
├── package.json
├── playwright.config.ts
└── README.md                         # Ce fichier
```

## Modules

### Module 01 — Découverte de Playwright & OWUI (2-3h)
*Niveau Débutant*

- Installation et configuration de Playwright
- Premier test : vérifier le chargement de la page
- Sélecteurs CSS, ARIA, et semantiques
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
- Assertions sur du contenu non-deterministe
- Skip gracieux pour services indisponibles
- Actions sur les messages (régénérer, éditer)
- **7 tests + exercices**

### Module 04 — RAG, Outils MCP & Fonctionnalites avancées (3h)
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
- Comparaison cross-instance de donnees
- Integration CI/CD (GitHub Actions)
- **8 tests + exercices**

## Installation rapide (5 minutes)

### 1. Prerequisites

- **Node.js 18+** installe ([nodejs.org](https://nodejs.org))
- Une **instance Open WebUI** accessible :
  - Instance de cours fournie par l'enseignant, OU
  - Instance locale via Docker : `docker run -p 3000:8080 ghcr.io/open-webui/open-webui:main`

### 2. Installation

```bash
# Se placer dans le repertoire
cd GenAI/Playwright-OWUI

# Installer les dependances
npm install

# Installer le navigateur Chromium (telecharge ~200 Mo)
npx playwright install chromium
```

### 3. Configuration

```bash
# Copier le template de configuration
cp .env.example .env

# Editer .env avec vos identifiants
# (Utilisez votre editeur prefere)
```

**Variables minimales a remplir dans `.env` :**

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

### 4. Verification

```bash
# Lancer le module 01 pour verifier que tout fonctionne
npm run test:module1

# En mode visible (pour voir le navigateur)
npx playwright test --grep "01" --headed
```

## Commandes utiles

```bash
# Lancer tous les tests
npm test

# Lancer un module specifique
npm run test:module1    # Module 01
npm run test:module2    # Module 02
npm run test:module3    # Module 03
npm run test:module4    # Module 04
npm run test:module5    # Module 05

# Mode visible (navigateur affiche)
npx playwright test --headed

# Mode debug (inspecteur Playwright)
npm run test:debug

# Interface graphique Playwright
npm run test:ui

# Voir le rapport HTML des derniers tests
npm run report
```

## Concepts cles appris

| Concept | Module | Description |
|---------|--------|-------------|
| Sélecteurs | 01 | IDs, ARIA, getByRole, getByText |
| storageState | 01-02 | Session authentifiee réutilisable |
| Auto-wait | 01 | Playwright attend automatiquement |
| TipTap/fill() | 03 | keyboard.type() pour éditeurs rich text |
| Streaming | 03 | Polling et waitForFunction |
| test.skip() | 03-04 | Skip gracieux pour services indisponibles |
| API testing | 05 | APIRequestContext sans navigateur |
| Multi-tenant | 05 | Isolation et partage de donnees |
| CI/CD | 05 | GitHub Actions, rapports, artefacts |

## Pieges courants et solutions

Ces pieges ont été découverts lors de la validation initiale de la suite de tests.
Ils sont documentés ici car ils sont representatifs de vrais problemes
rencontres lors du test E2E d'applications web modernes.

### 1. Modal "Quoi de neuf" (Changelog)

**Probleme** : Open WebUI affiche un dialogue modal au premier chargement (changelog des mises a jour). Ce modal a un overlay plein ecran (`z-index: 9999`) qui intercepte TOUS les clics.

**Solution** : Le helper `dismissModals()` ferme automatiquement ces dialogues avant chaque interaction. Il essaie plusieurs strategies : bouton de fermeture, touche Escape, clic en dehors.

```typescript
import { dismissModals } from '../helpers/chat';
// Dans beforeEach :
await page.goto('/');
await dismissModals(page);
```

### 2. Éditeur TipTap (fill() ne fonctionne pas)

**Probleme** : Open WebUI utilise TipTap/ProseMirror au lieu d'un `<textarea>`. La methode `fill()` de Playwright ne déclenche pas les evenements necessaires.

**Solution** : Toujours utiliser `keyboard.type()` pour saisir du texte dans le chat :

```typescript
// FAUX :
await page.locator('#chat-input').fill('Bonjour');
// CORRECT :
await page.locator('#chat-input').click();
await page.keyboard.type('Bonjour', { delay: 10 });
```

### 3. Rate limiting de l'API d'authentification

**Probleme** : L'endpoint `/api/v1/auths/signin` a un rate limit strict (~2 min entre appels). Si chaque test fait son propre login, on atteint rapidement le 429.

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

**Probleme** : Certaines APIs (knowledge bases, functions) retournent du HTML au lieu de JSON quand le reverse proxy intercepte la requete ou la redirige.

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

Si vous êtes derrière un proxy ou firewall, télécharger manuellement : `PLAYWRIGHT_DOWNLOAD_HOST=https://proxy.example.com npx playwright install chromium`. Le module [01](01-decouverte/) couvre la configuration pas-a-pas.

### Les tests échouent avec "Timeout exceeded" sur le chat

Le module [03](03-chat-streaming/) teste le chat avec un LLM reel via streaming. Les timeouts sont elonges (30-60s) mais les LLM lents ou surcharges peuvent les depasser. Mitigation :

```typescript
// Augmenter le timeout pour un test specifique
test('chat reponse', { tag: '@slow' }, async ({ page }) => {
  test.setTimeout(120_000); // 2 minutes
  // ...
});
```

- Vérifier que l'instance OWUI est accessible : `curl $OWUI_URL/api/v1/models`
- Le streaming utilise `page.waitForFunction()` — si le modèle ne stream pas, le poll tourne en boucle.
- Le module [03](03-chat-streaming/) explique les strategies d'assertion sur du contenu non-deterministe.

### Peut-on utiliser cette série sans instance Open WebUI ?

Partiellement. Les modules [01](01-decouverte/) (navigation, sélecteurs) et [05](05-multi-tenant-ci/) (API testing) fonctionnent sur toute application web. Les modules [02](02-navigation-authentification/) a [04](04-rag-tools-avances/) sont spécifiques a OWUI (auth, chat, RAG).

Pour une instance locale rapide :

```bash
# OWUI avec modeles Ollama (local, pas de cle API)
docker run -d -p 3000:8080 --add-host=host.docker.internal:host-gateway ghcr.io/open-webui/open-webui:main

# Ou avec vLLM (GPU requis)
# Configurer OWUI_LOCAL_MODEL dans .env
```

Le module [01](01-decouverte/) explique comment pointer Playwright vers votre instance via `.env`.

### Les tests du module 04 (RAG/MCP) sont tous skip

Le module [04](04-rag-tools-avances/) teste les Knowledge Bases, les outils MCP et les channels. Les 5 skips dans les résultats de validation viennent de fonctionnalités non configurées sur l'instance OWUI :

- **Knowledge Bases** : nécessitent un upload prealable de documents via l'interface OWUI.
- **Outils MCP** : le serveur MCP doit être configure dans les parametres OWUI (Admin > Tools).
- **Channels** : fonctionnalite collaborative qui requiert plusieurs utilisateurs actifs.

Pour activer ces tests, configurer les fonctionnalités correspondantes dans OWUI et decommenter les `test.skip()` dans [04-rag-tools.spec.ts](04-rag-tools-avances/04-rag-tools.spec.ts).

### Quelle différence entre cette série et les ateliers Vibe-Coding ?

| Critère | Playwright-OWUI | Vibe-Coding |
|---------|-----------------|-------------|
| **Focus** | Tests E2E automatises | Développement assiste par IA |
| **Langage** | TypeScript (.spec.ts) | Naturel (prompt engineering) |
| **Outil** | Playwright | Claude Code / Roo Code |
| **Public** | Testeurs QA, dev backend | Developeurs, débutants |
| **Non-determinisme** | Gère (streaming, LLM) | N/A |

Les deux series sont complementaires : Vibe-Coding ([README](../../Vibe-Coding/README.md)) couvre le développement assiste par IA, tandis que Playwright-OWUI couvre la validation automatisee des interfaces generees.

### Comment adapter les tests a une autre application OWUI (version ou config différente) ?

Les sélecteurs CSS et les patterns d'auth sont stables entre OWUI v0.8.x et v0.9.x. Si votre instance diffère :

1. **Sélecteurs** : vérifier avec le mode debug (`npx playwright test --debug`) que les sélecteurs dans [helpers/selectors.ts](helpers/selectors.ts) correspondent a votre version.
2. **Labels multilingues** : OWUI v0.9+ a change certains labels. Adapter dans les tests ou utiliser `getByRole()` (plus robuste que `getByText()`).
3. **Nouvelles fonctionnalités** : OWUI v0.9.1 ajoute Calendar, Automations, Desktop app. Ce sont de bons candidats pour des exercices bonus (voir `WHATS-NEW-v0.9.1.md`).

Le module [01](01-decouverte/) enseigne les sélecteurs robustes (`getByRole`, `getByTestId`) qui resistent aux changements d'UI.

---

*Version 1.1.0 — Avril 2026 (revalidee sur OWUI v0.9.1)*
