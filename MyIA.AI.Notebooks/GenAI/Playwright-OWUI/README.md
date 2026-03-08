# Playwright-OWUI - Tests E2E pedagogiques pour Open WebUI

[← Retour GenAI](../README.md)

Serie pedagogique complete pour apprendre **Playwright** (framework de tests E2E) en testant une application reelle : **Open WebUI**, une plateforme de chat IA generative.

## Vue d'ensemble

| Statistique | Valeur |
|-------------|--------|
| Modules | 5 |
| Tests | 30+ |
| Duree totale | ~13-16h |
| Technologies | Playwright, TypeScript, Open WebUI |
| Niveau | Debutant a Expert |

## Pourquoi cette serie ?

Cette serie se distingue des tutoriels Playwright classiques par son sujet :
- On ne teste pas un simple formulaire ou une todo-list
- On teste une **vraie application de production** avec des **modeles d'IA generative**
- Les defis sont reels : streaming, non-determinisme, latence variable, multi-tenant

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

### Module 01 — Decouverte de Playwright & OWUI (2-3h)
*Niveau Debutant*

- Installation et configuration de Playwright
- Premier test : verifier le chargement de la page
- Selecteurs CSS, ARIA, et semantiques
- Mode headed et screenshots
- **4 tests + exercices**

### Module 02 — Navigation & Authentification (2-3h)
*Niveau Debutant+*

- Pattern d'authentification par storageState
- Navigation entre les sections d'OWUI (admin, workspace, channels)
- Gestion des labels multilingues (FR/EN)
- Routes SvelteKit
- **8 tests + exercices**

### Module 03 — Chat & Streaming LLM (3h)
*Niveau Intermediaire*

- L'editeur TipTap : `keyboard.type()` vs `fill()`
- Gestion du streaming (polling, waitForFunction)
- Assertions sur du contenu non-deterministe
- Skip gracieux pour services indisponibles
- Actions sur les messages (regenerer, editer)
- **7 tests + exercices**

### Module 04 — RAG, Outils MCP & Fonctionnalites avancees (3h)
*Niveau Intermediaire+*

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
| `OWUI_CLOUD_MODEL` | Modele cloud pour les tests de chat | 03 |
| `OWUI_LOCAL_MODEL` | Modele local (vLLM/Ollama) | 03 |
| `OWUI_PERSONA_MODEL` | Modele persona/custom | 03 |
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
| Selecteurs | 01 | IDs, ARIA, getByRole, getByText |
| storageState | 01-02 | Session authentifiee reutilisable |
| Auto-wait | 01 | Playwright attend automatiquement |
| TipTap/fill() | 03 | keyboard.type() pour editeurs rich text |
| Streaming | 03 | Polling et waitForFunction |
| test.skip() | 03-04 | Skip gracieux pour services indisponibles |
| API testing | 05 | APIRequestContext sans navigateur |
| Multi-tenant | 05 | Isolation et partage de donnees |
| CI/CD | 05 | GitHub Actions, rapports, artefacts |

## Liens utiles

- [Documentation Playwright](https://playwright.dev/)
- [Open WebUI](https://github.com/open-webui/open-webui)
- [TipTap Editor](https://tiptap.dev/)
- [Model Context Protocol (MCP)](https://modelcontextprotocol.io/)

## Origine

Cette serie pedagogique a ete creee dans le cadre du cycle GenAI CoursIA,
en complement des ateliers Vibe-Coding (Claude Code et Roo Code).
Elle utilise les tests E2E reels du projet Open WebUI comme base pedagogique.

---

*Version 1.0.0 — Mars 2026*
