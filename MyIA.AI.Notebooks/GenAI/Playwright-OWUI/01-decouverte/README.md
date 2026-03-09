# Module 01 - Decouverte de Playwright & Open WebUI

> **Format** : Ce module utilise des fichiers TypeScript `.spec.ts` (pas des Jupyter Notebooks). Le fichier `01-decouverte.spec.ts` contient les tests commentes qui servent d'exercices pratiques. Ouvrez-le dans VS Code, lisez les commentaires, puis lancez les tests pour les voir s'executer.

## Objectifs pedagogiques

A la fin de ce module, vous serez capable de :

- Installer Playwright et comprendre son architecture
- Ecrire un premier test E2E sur une application web reelle
- Comprendre la structure d'un projet de tests Playwright
- Naviguer dans Open WebUI avec des selecteurs robustes
- Lancer les tests en mode headed (avec navigateur visible) pour deboguer

## Prerequis

- Node.js 18+ installe
- Une instance Open WebUI accessible (fournie par l'enseignant ou locale)
- VS Code avec l'extension Playwright recommandee
- Fichier `.env` configure (voir `.env.example` a la racine)

## Duree estimee

**2 a 3 heures**

## Contenu du module

### Partie theorique

**Pourquoi Playwright ?**
- Framework de test E2E par Microsoft, multi-navigateurs (Chromium, Firefox, WebKit)
- Auto-wait intelligent : attend automatiquement que les elements soient visibles/cliquables
- Mode trace et video pour le debogage
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

**Selecteurs — par ordre de preference :**
1. **IDs** : `#chat-input` — Les plus stables
2. **Roles ARIA** : `button[aria-label="..."]` — Accessibles et resilients
3. **getByRole/getByText** : Semantiques, recommandes par Playwright
4. **Classes CSS** : `.chat-user` — Fragiles, dernier recours

### Partie pratique

Le fichier `01-decouverte.spec.ts` contient 4 exercices progressifs :

| Test | Description | Concepts |
|------|-------------|----------|
| Connexion reussie | Verifier qu'on arrive sur la page principale | `goto()`, `toBeVisible()`, storageState |
| Selecteur de modeles | Ouvrir le dropdown et compter les modeles | `click()`, `locator()`, `count()` |
| Menu utilisateur | Ouvrir le menu et verifier les options | `getByRole()`, regex multilingue |
| Premier screenshot | Capturer la page pour documentation | `screenshot()`, artefacts |

### Exercices supplementaires

1. **Modifier un selecteur** : Remplacez un selecteur CSS par un `getByRole()` equivalent
2. **Ajouter un test** : Verifiez que le bouton "Nouveau Chat" est visible
3. **Mode debug** : Lancez `npm run test:debug` et utilisez le Playwright Inspector

## Commandes

```bash
# Installer les dependances
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

## Points cles a retenir

- Playwright attend automatiquement les elements (auto-wait) — pas besoin de `sleep()`
- `storageState` permet de reutiliser une session authentifiee sans se reconnecter a chaque test
- Preferez les selecteurs semantiques (roles, labels) aux selecteurs CSS fragiles
- Le mode `--headed` est indispensable pour comprendre ce que fait le test visuellement
