# Nouveautes Open WebUI v0.10 (juin-juillet 2026)

[← Retour Playwright-OWUI](./README.md)

> **Pour qui ?** Etudiants qui suivent la serie Playwright-OWUI sur une instance
> mise a jour en **v0.10.2** (myia et les 6 ecoles partenaires). Ce document
> explique ce qui a change depuis la v0.9.x et ce que vous pouvez tester en bonus.
> Le **module 06** met ces nouveautes en pratique.

## Contexte de mise a jour

La ligne **v0.10** est arrivee en trois temps :

- **v0.10.0** (29 juin 2026) — « plateforme agentique » : la plus grosse
  evolution depuis la v0.8.
- **v0.10.1** (29 juin 2026) — correctif (chats en lecture seule dans des dossiers
  partages ne forcent plus la deconnexion).
- **v0.10.2** (1er juillet 2026) — raisonnement affiche en direct, uploads de
  bases de connaissances qui preservent l'arborescence, memoire plus fine.

L'instance de cours et les instances partenaires (EPF, EPF-GenAI, ECE, ESG, EPITA,
Pauwels) sont sur **v0.10.2**.

## Ce qui ne change PAS (rassurant pour vos tests existants)

- **Authentification** : meme endpoint `/api/v1/auths/signin`, meme rate limit
  (~2 min), meme pattern `storageState`.
- **Editeur de chat** : toujours TipTap/ProseMirror → `keyboard.type()` obligatoire
  (jamais `fill()`).
- **Selecteurs principaux** : `#chat-input`, la sidebar, le selecteur de modèles —
  inchanges.
- **Streaming** : meme mecanisme Server-Sent Events, meme API `/api/chat/completions`.

## Nouveautes majeures (opportunites de tests)

### 1. Memoire (memory) — refonte complete, sortie de beta

La memoire distingue desormais le **long terme** et le **par-conversation**.
Chaque souvenir porte un champ **`type`** (ex. `"context"`) et un `path` optionnel.

**A tester (module 06, API)** :
```typescript
const created = await addMemory(request, OWUI_URL, token, 'ma preference');
expect(created.type).toBeTruthy();      // champ v0.10
await deleteMemory(request, OWUI_URL, token, created.id);  // toujours nettoyer !
```
Endpoints : `GET /api/v1/memories/`, `POST /api/v1/memories/add`,
`DELETE /api/v1/memories/{id}`.

> **v0.10.2** ajoute une **capture memoire plus fine** (privilegie les preferences
> durables plutot que les evenements ponctuels) et un **reglage admin** pour garder
> les outils memoire actifs sans injecter le contexte stocke dans les prompts.

### 2. Dossiers d'equipe (folders) — partageables

Les dossiers peuvent etre **partages** avec des permissions **lecture / ecriture**
pour des utilisateurs ou des groupes.

**A tester (module 06, API)** : CRUD via `GET/POST /api/v1/folders/` et
`DELETE /api/v1/folders/{id}` ; le **partage** entre deux comptes est propose en
exercice (variables `OWUI_TENANT2_*`).

### 3. Raisonnement streame (v0.10.2)

Les modèles "thinking" affichent leurs **étapes de raisonnement en direct** dans
l'interface (bloc repliable). **A tester (module 06, UI)** : selectionner un
modèle de raisonnement (`OWUI_REASONING_MODEL`), poser une question, verifier
l'apparition du bloc de raisonnement — avec **skip gracieux** si le modèle n'en
emet pas.

### 4. Compaction automatique du contexte

Quand une conversation approche de la limite de contexte, elle est **resumee
automatiquement** au lieu d'etre tronquee. **A tester (module 06, UI)** : plusieurs
tours d'affilee, le modèle **garde le fil** (test de non-regression conversation
longue).

### 5. Uploads de connaissances qui preservent l'arborescence (v0.10.2)

Les imports de fichiers dans une base de connaissances **conservent la structure
des sous-dossiers** au lieu de tout aplatir. **Idee d'exercice (Module 04/06)** :
uploader une arborescence et verifier que les chemins relatifs sont preserves.

## Nouveautes backend utiles (Module 05 — API)

- **Recherche hybride native** (base de données) pour des requetes KB nettement
  plus rapides.
- **Sources de recuperation externes** : interroger des systemes tiers directement
  depuis le chat.
- **Systeme d'evenements + webhooks** : les activites de la plateforme peuvent
  declencher des webhooks sortants.
- **Administration centralisee de l'authentification** (LDAP et OAuth/OIDC sur une
  page admin dediee — voir piege n°3 plus bas).
- **Config via variables d'environnement** des connexions Ollama/OpenAI (v0.10.2),
  et modèles d'arene definissables par variables d'environnement.

## Changements BREAKING (a connaitre)

| Changement | Impact pour vous |
|------------|------------------|
| **Native tool calling par defaut** (remplace le mode "legacy") | Un modèle conversationnel appele en API non-streaming peut renvoyer `tool_calls` + `content` vide. Testez le texte via l'UI (streaming), ou ciblez des modèles sans outils. |
| **Python cote client en iframe sandbox** | L'execution Python cote navigateur tourne dans une iframe isolee → ciblez le `frameLocator`, pas le document principal. |
| **Config d'authentification deplacee** sur une page admin dediee | Les tests qui cherchaient les reglages auth dans les paramètres generaux doivent viser la nouvelle page admin. |
| **Migration BDD irreversible** (backup serveur obligatoire) | Pas d'impact test ; explique pourquoi on ne "revient pas en arriere" sur une instance. |
| Renommage `ENABLE_RAG_LOCAL_WEB_FETCH` → `ENABLE_LOCAL_WEB_FETCH` | Cote deploiement uniquement. |
| Cle You.com : `YOUCOM_API_KEY` → `YDC_API_KEY` | Cote deploiement uniquement. |

## Pieges qui n'ont PAS change

Les 4 pieges du README principal restent valides :
1. Modal "Quoi de neuf" (overlay) — `dismissModals()` la ferme.
2. Editeur TipTap — `keyboard.type()` obligatoire.
3. Rate limiting `/api/v1/auths/signin` (~2 min) — login unique en `beforeAll`.
4. APIs renvoyant du HTML via reverse proxy — **slash final** obligatoire.

## Ou lire les details techniques

- **Changelog upstream** : https://github.com/open-webui/open-webui/blob/main/CHANGELOG.md (sections 0.10.0 → 0.10.2)
- **Module pratique** : [`06-nouveautes-v0.10/`](./06-nouveautes-v0.10/README.md)

---

*Mise a jour : 1er juillet 2026. Applique a l'instance de cours et aux 6 ecoles partenaires (v0.10.2).*
