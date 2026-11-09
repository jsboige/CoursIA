# Module 01 - Découverte de Playwright & Open WebUI

> **Format** : Ce module combine deux artefacts. Le fichier `01-decouverte.spec.ts` est le **moteur de test** (TypeScript, exécuté par Playwright) : il contient les tests commentés qui servent d'exercices pratiques. Le notebook `01-Decouverte-QA-OWUI.ipynb` en est la **couche pédagogique** (voir la section ci-dessous). Ouvrez le `.spec.ts` dans VS Code, lisez les commentaires, puis lancez les tests pour les voir s'exécuter.

## Objectifs pédagogiques

À la fin de ce module, vous serez capable de :

- Installer Playwright et comprendre son architecture
- Écrire un premier test E2E sur une application web réelle
- Comprendre la structure d'un projet de tests Playwright
- Naviguer dans Open WebUI avec des sélecteurs robustes
- Lancer les tests en mode headed (avec navigateur visible) pour déboguer

## Prérequis

- Node.js 18+ installé
- Une instance Open WebUI accessible (fournie par l'enseignant ou locale)
- VS Code avec l'extension Playwright recommandée
- Fichier `.env` configuré (voir `.env.example` à la racine)

## Durée estimée

**2 à 3 heures**

## Contenu du module

### Partie théorique

**Pourquoi Playwright ?**
- Framework de test E2E par Microsoft, multi-navigateurs (Chromium, Firefox, WebKit)
- Auto-wait intelligent : attend automatiquement que les éléments soient visibles/cliquables
- Mode trace et video pour le débogage
- API simple et TypeScript-native

**Architecture d'un projet Playwright :**
```
projet/
├── playwright.config.ts    # Configuration globale
├── fixtures/               # Setup (auth, donnees)
├── helpers/                # Fonctions reutilisables
├── scenarios/              # Fichiers de tests (.spec.ts)
└── .auth/                  # Etat authentifie sauvegarde
```

**Sélecteurs — par ordre de préférence :**
1. **IDs** : `#chat-input` — Les plus stables
2. **Roles ARIA** : `button[aria-label="..."]` — Accessibles et résilients
3. **getByRole/getByText** : Sémantiques, recommandés par Playwright
4. **Classes CSS** : `.chat-user` — Fragiles, dernier recours

### Partie pratique

Le fichier `01-decouverte.spec.ts` contient 4 exercices progressifs :

| Test | Description | Concepts |
|------|-------------|----------|
| Connexion réussie | Vérifier qu'on arrive sur la page principale | `goto()`, `toBeVisible()`, storageState |
| Sélecteur de modèles | Ouvrir le dropdown et compter les modèles | `click()`, `locator()`, `count()` |
| Menu utilisateur | Ouvrir le menu et vérifier les options | `getByRole()`, regex multilingue |
| Premier screenshot | Capturer la page pour documentation | `screenshot()`, artefacts |

### Exercices supplémentaires

1. **Modifier un sélecteur** : Remplacez un sélecteur CSS par un `getByRole()` équivalent
2. **Ajouter un test** : Vérifiez que le bouton "Nouveau Chat" est visible
3. **Mode debug** : Lancez `npm run test:debug` et utilisez le Playwright Inspector

## Couche pédagogique (notebook)

Le notebook [`01-Decouverte-QA-OWUI.ipynb`](01-Decouverte-QA-OWUI.ipynb) est la première étape de la mission « QA Engineer d'une flotte GenAI multi-tenant ». Le notebook chapeau [`00-Parcours-QA-OWUI.ipynb`](../00-Parcours-QA-OWUI.ipynb) en donne le fil rouge. Il présente l'architecture d'un projet Playwright, explique comment Playwright observe la page (auto-wait, sélecteurs), lit le fichier `01-decouverte.spec.ts` et en dresse l'inventaire. Il appelle `npx playwright test --list` seulement si les dépendances Node sont installées, et ne lance aucun test. Il propose ensuite des exercices en Python : classer un sélecteur, relier un test à son concept, écrire une assertion de titre. Ses cellules tournent sans navigateur ni instance Open WebUI.

## Commandes

```bash
# Installer les dépendances
npm install

# Installer les navigateurs Playwright
npx playwright install chromium

# Lancer ce module uniquement
npm run test:module1

# Lancer en mode visible (headed)
npx playwright test --grep "01" --headed

# Lancer avec le debugger Playwright
PWDEBUG=1 npx playwright test --grep "01" --headed

# Voir le rapport HTML
npm run report
```

## Points clés à retenir

- Playwright attend automatiquement les éléments (auto-wait) — pas besoin de `sleep()`
- `storageState` permet de réutiliser une session authentifiée sans se reconnecter à chaque test
- Préférez les sélecteurs sémantiques (roles, labels) aux sélecteurs CSS fragiles
- Le mode `--headed` est indispensable pour comprendre ce que fait le test visuellement
