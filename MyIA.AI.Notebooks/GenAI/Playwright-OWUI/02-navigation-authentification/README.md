# Module 02 - Navigation & Authentification

> **Format** : Fichier TypeScript `.spec.ts` avec tests commentes. Ouvrez `02-navigation-auth.spec.ts` dans VS Code, lisez les commentaires pedagogiques, puis lancez avec `npm run test:module2`.

## Objectifs pedagogiques

A la fin de ce module, vous serez capable de :

- Comprendre le mecanisme d'authentification par storageState
- Tester un formulaire de login complet (email + mot de passe)
- Naviguer entre les differentes sections d'Open WebUI
- Ecrire un setup fixture reutilisable
- Gerer les redirections et les etats de chargement

## Duree estimee

**2 a 3 heures**

## Contenu du module

### Partie theorique

**Authentification dans Playwright :**
Le pattern standard est de s'authentifier UNE SEULE FOIS, puis de sauvegarder
l'etat du navigateur (cookies, localStorage, sessionStorage) dans un fichier JSON.
Tous les tests suivants chargent cet etat — pas besoin de se re-connecter.

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
| Login UI complet | Remplir le formulaire et verifier la redirection | `fill()`, `waitForURL()` |
| Session persistante | Verifier que le storageState fonctionne | storageState, cookies |
| Navigation admin | Acceder au panneau admin | `goto()`, assertions localisees |
| Navigation workspace | Parcourir les sections workspace | Routes SvelteKit |
| Page de settings | Acceder aux reglages | `getByRole('link')` |

## Commandes

```bash
npm run test:module2
npx playwright test --grep "02" --headed
```
