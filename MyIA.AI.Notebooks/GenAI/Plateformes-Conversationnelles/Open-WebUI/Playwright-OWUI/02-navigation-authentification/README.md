# Module 02 - Navigation & Authentification

> **Format** : deux artefacts. Le fichier TypeScript `02-navigation-auth.spec.ts` (tests commentés) est le **moteur de test**, lancé avec `npm run test:module2`. Le notebook `02-Navigation-Auth-QA-OWUI.ipynb` (section ci-dessous) en est la **couche pédagogique**. Ouvrez le `.spec.ts` dans VS Code et lisez ses commentaires pédagogiques.

## Objectifs pédagogiques

A la fin de ce module, vous serez capable de :

- Comprendre le mecanisme d'authentification par storageState
- Tester un formulaire de login complet (email + mot de passe)
- Naviguer entre les differentes sections d'Open WebUI
- Écrire un setup fixture réutilisable
- Gérer les redirections et les états de chargement

## Durée estimée

**2 a 3 heures**

## Contenu du module

### Partie théorique

**Authentification dans Playwright :**
Le pattern standard est de s'authentifier UNE SEULE FOIS, puis de sauvegarder
l'état du navigateur (cookies, localStorage, sessionStorage) dans un fichier JSON.
Tous les tests suivants chargent cet état — pas besoin de se re-connecter.

```
1. auth.setup.ts  →  Login via formulaire  →  Sauvegarde .auth/owui.json
2. *.spec.ts      →  Charge .auth/owui.json →  Deja connecte !
```

**Navigation dans Open WebUI :**
```
/               → Page de chat (nouvelle conversation)
/c/{id}         → Conversation existante
/admin          → Panneau d'administration (admin only)
/admin/settings → Configuration globale
/workspace/*    → Knowledge bases, modeles, prompts, fonctions
/channels       → Canaux de discussion
```

### Partie pratique

| Test | Description | Concepts |
|------|-------------|----------|
| Login UI complet | Remplir le formulaire et vérifier la redirection | `fill()`, `waitForURL()` |
| Session persistante | Vérifier que le storageState fonctionne | storageState, cookies |
| Navigation admin | Acceder au panneau admin | `goto()`, assertions localisees |
| Navigation workspace | Parcourir les sections workspace | Routes SvelteKit |
| Page de settings | Acceder aux reglages | `getByRole('link')` |

## Couche pédagogique (notebook)

Le notebook [`02-Navigation-Auth-QA-OWUI.ipynb`](02-Navigation-Auth-QA-OWUI.ipynb) est la deuxième étape de la mission (voir le notebook chapeau [`00-Parcours-QA-OWUI.ipynb`](../00-Parcours-QA-OWUI.ipynb)). Il suit la prise en main de l'outillage du module 01 et précède le module 03. Il explique le pattern `storageState` (s'authentifier une seule fois, car l'endpoint de connexion limite le nombre d'appels), le contrôle d'accès par rôle et les routes SvelteKit d'Open WebUI, ainsi que la différence entre un `429` (rate-limiting) et une régression réelle. Il lit `02-navigation-auth.spec.ts` et en dresse l'inventaire (`npx playwright test --list`, sans lancer les tests, et seulement si les dépendances Node sont installées). Ses exercices en Python (zone d'accès d'une route, relier un test à son concept, assertion d'URL) tournent sans navigateur.

## Commandes

```bash
npm run test:module2
npx playwright test --grep "02" --headed
```
