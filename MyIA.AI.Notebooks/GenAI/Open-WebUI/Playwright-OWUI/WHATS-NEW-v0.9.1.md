# Nouveautes Open WebUI v0.9.1 (avril 2026)

[← Retour Playwright-OWUI](./README.md)

> **Pour qui ?** Etudiants qui suivent la serie Playwright-OWUI sur une instance mise a jour en v0.9.1 (myia et les 6 ecoles partenaires). Ce document explique ce qui a change depuis v0.8.x et ce que vous pouvez tester en bonus.

## Contexte de mise a jour

L'instance de cours (et toutes les instances partenaires : EPF, EPF-GenAI, ECE, ESG, EPITA, Pauwels) a ete migree de **v0.8.12** vers **v0.9.1** le **24 avril 2026**. Si vous avez teste auparavant, la plupart des selecteurs et flux d'authentification restent inchanges — mais plusieurs nouvelles surfaces sont apparues dans l'interface.

## Ce qui ne change PAS (rassurant pour vos tests existants)

- **Authentification** : meme endpoint `/api/v1/auths/signin`, meme rate limit (~2 min), meme pattern `storageState`
- **Editeur de chat** : toujours TipTap/ProseMirror, donc `keyboard.type()` obligatoire (pas `fill()`)
- **Selecteurs principaux** : `#chat-input`, les boutons admin, la sidebar des chats — inchanges
- **Streaming** : meme mecanisme (Server-Sent Events), meme API `/api/chat/completions`
- **Modele de permissions** : memes AccessGrants, memes roles user/admin

## Nouveautes UI visibles (opportunites de tests bonus)

### 1. Page `/calendar` — Nouveau workspace Calendrier

Un **calendrier complet** est maintenant integre dans OWUI. Les utilisateurs peuvent :
- Creer et gerer des evenements
- Definir des rappels (in-app, browser notifications, webhooks)
- Voir leurs automations a cote de leurs evenements

**Selecteurs a explorer** (bonus exercice) :
```typescript
await page.goto('/calendar');
// Le composant CalendarView.svelte gere la vue principale
await expect(page.getByRole('heading', { name: /calendar/i })).toBeVisible();
```

**Idee d'exercice Module 02** : ecrire un test qui navigue vers `/calendar`, cree un evenement, verifie qu'il apparait dans la vue, puis le supprime.

### 2. Page `/automations` — Taches planifiees

Les utilisateurs peuvent demander a l'IA d'**executer des taches de maniere recurrente** (digest quotidien, rapport hebdomadaire, etc.).

**Variables admin associees** :
- `AUTOMATION_MAX_COUNT` : nombre max d'automations par utilisateur
- `AUTOMATION_MIN_INTERVAL` : intervalle minimum entre executions
- `SCHEDULER_POLL_INTERVAL` : frequence de verification du planificateur

**Idee d'exercice Module 04** : creer une automation via le chat ("rappelle-moi demain a 10h"), verifier qu'elle apparait dans `/automations`.

### 3. Desktop app officielle

OWUI est maintenant disponible comme **app native Mac / Windows / Linux**, avec :
- Pas de Docker requis pour les utilisateurs finaux
- Connexion a une instance distante (comme l'instance de cours)
- Floating chat bar systeme (Shift+Cmd+I sur Mac, Shift+Ctrl+I sur Win/Linux)
- Push-to-talk systeme

**Note** : les tests Playwright continuent de cibler le navigateur — la Desktop app n'entre pas dans le perimetre des modules 01-05. C'est une option d'usage pour les etudiants, pas un sujet de test.

### 4. Task management tool integre

Les IA peuvent maintenant **creer et suivre des taches** dans une conversation. Une conversation complexe est decomposee en etapes avec statut en temps reel.

### 5. Indicateurs et UX

- **Unread chat indicators** : badge sur les chats avec nouveaux messages
- **Pinned notes** : notes epinglees dans la sidebar, creation rapide
- **Emoji shortcodes** : `:wave:` dans le chat ouvre un selecteur d'emoji
- **Swipe-to-reply** : geste swipe-droit sur mobile pour repondre a un message
- **WebSocket feedback** : notifications visibles si la connexion temps-reel tombe / reconnecte

## Nouveautes backend (pertinentes pour Module 05 — API testing)

### Nouvelles routes API

- `POST /api/v1/calendar/events` — creer un evenement
- `GET /api/v1/calendar/events` — lister ses evenements
- `POST /api/v1/automations` — creer une automation
- `GET /api/v1/automations/runs` — historique d'executions

**Idee d'exercice Module 05** : ecrire un test API qui cree 3 evenements via POST, liste via GET, verifie la pagination, puis nettoie.

### Anthropic x-api-key

Les clients Anthropic-compatibles peuvent maintenant s'authentifier avec le header `x-api-key` sur toutes les routes pertinentes (plus besoin de `Authorization: Bearer`). Utile si vous testez avec un wrapper OpenAI-compat.

### Responses API (OpenAI + Ollama)

Les connecteurs Azure OpenAI et Ollama supportent maintenant `/openai/v1/responses` directement. Cela change si votre client SDK pointe sur cet endpoint — a tester.

## Perf : ce que vous allez ressentir en testant

- **Chat plus fluide sur les longues conversations** : les anciens messages sont decharges automatiquement et rechargeres au scroll (memory culling). Vos tests qui scrollent dans un chat long seront plus stables.
- **Streaming plus fluide** : optimisation single-step du traitement de chaque ligne. Attendez-vous a moins de latence entre tokens.
- **Sidebar plus rapide** : les listes de chats/folders ne chargent que les champs necessaires. Vos tests de navigation seront plus rapides aussi.

## Securite : ce qui a ete renforce (bon a savoir, pas un test)

Plusieurs failles ont ete corrigees en v0.9.x :
- **OAuth 2.1 PKCE** par defaut (S256)
- **IPv6 SSRF** bloque (URL validation uniforme)
- **API key endpoint restriction** appliquee sur tous les transports (Authorization, Cookie, x-api-key)
- **SCIM token checks** : comparison en temps constant
- **LDAP empty-password** rejete avant le bind
- **First-user admin race** : plus possible de creer plusieurs admins via OAuth/LDAP simultane
- **Redis cache** isole par prefix (si plusieurs instances OWUI partagent un Redis)

Pour vos tests : aucune modification a apporter si vous ne testez pas ces surfaces.

## Pieges qui n'ont PAS change

Les 4 pieges documentes dans le README principal restent valides en v0.9.1 :
1. Modal "Quoi de neuf" (overlay z-index 9999)
2. Editeur TipTap (toujours `keyboard.type()` obligatoire)
3. Rate limiting `/api/v1/auths/signin`
4. APIs retournant du HTML via reverse proxy

## Un nouveau piege v0.9.1 a garder en tete

### 5. Async DB + middleware cancellation

La v0.9.0 a reecrit une grosse partie du backend en **async** (DB, file processing, vector search). Consequence : **les requetes longues ne sont plus annulees par le middleware** quand la connexion HTTP se ferme tot. C'est GENERALEMENT un bienfait (les embeddings ne s'interrompent plus), mais :

**Probleme potentiel** : si votre test declenche un traitement long (upload PDF, creation KB) et quitte brutalement, le backend continue. Le prochain test peut voir des donnees non-consommees.

**Solution** : utiliser `test.step()` et laisser les operations se terminer avant d'abandonner. Exemple :
```typescript
test('upload and wait', async ({ request }) => {
  await test.step('upload file', async () => {
    await request.post('/api/v1/files', { multipart: { file: ... } });
  });
  // Attendre le traitement, ne pas passer au test suivant trop vite
  await page.waitForTimeout(2000);
});
```

## Ou lire les details techniques

- **Changelog upstream** : https://github.com/open-webui/open-webui/blob/main/CHANGELOG.md (sections 0.9.0 et 0.9.1)
- **Migration notes (interne)** : `memory/upgrade-v0.9.1-2026-04-24.md` dans le repo `myia-open-webui`
- **Issue GitHub suivant l'audit transverse** : https://github.com/jsboige/open-webui/issues/11

---

*Mise a jour : 24 avril 2026. Applique a l'instance de cours et aux 6 ecoles partenaires.*
