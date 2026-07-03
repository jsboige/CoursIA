# Nouveautés Open WebUI v0.10 (juin-juillet 2026)

[← Retour Playwright-OWUI](./README.md)

> **Pour qui ?** Étudiants qui suivent la série Playwright-OWUI sur une instance
> mise à jour en **v0.10.2** (myia et les 6 écoles partenaires). Ce document
> explique ce qui a changé depuis la v0.9.x et ce que vous pouvez tester en bonus.
> Le **module 06** met ces nouveautés en pratique.

## Contexte de mise à jour

La ligne **v0.10** est arrivée en trois temps :

- **v0.10.0** (29 juin 2026) — « plateforme agentique » : la plus grosse
  évolution depuis la v0.8.
- **v0.10.1** (29 juin 2026) — correctif (chats en lecture seule dans des dossiers
  partagés ne forcent plus la déconnexion).
- **v0.10.2** (1er juillet 2026) — raisonnement affiché en direct, uploads de
  bases de connaissances qui préservent l'arborescence, mémoire plus fine.

L'instance de cours et les instances partenaires (EPF, EPF-GenAI, ECE, ESG, EPITA,
Pauwels) sont sur **v0.10.2**.

## Ce qui ne change PAS (rassurant pour vos tests existants)

- **Authentification** : même endpoint `/api/v1/auths/signin`, même rate limit
  (~2 min), meme pattern `storageState`.
- **Éditeur de chat** : toujours TipTap/ProseMirror → `keyboard.type()` obligatoire
  (jamais `fill()`).
- **Sélecteurs principaux** : `#chat-input`, la sidebar, le sélecteur de modèles —
  inchangés.
- **Streaming** : même mécanisme Server-Sent Events, même API `/api/chat/completions`.

## Nouveautés majeures (opportunités de tests)

### 1. Mémoire (memory) — refonte complète, sortie de beta

La mémoire distingue désormais le **long terme** et le **par-conversation**.
Chaque souvenir porte un champ **`type`** (ex. `"context"`) et un `path` optionnel.

**A tester (module 06, API)** :
```typescript
const created = await addMemory(request, OWUI_URL, token, 'ma preference');
expect(created.type).toBeTruthy();      // champ v0.10
await deleteMemory(request, OWUI_URL, token, created.id);  // toujours nettoyer !
```
Endpoints : `GET /api/v1/memories/`, `POST /api/v1/memories/add`,
`DELETE /api/v1/memories/{id}`.

> **v0.10.2** ajoute une **capture mémoire plus fine** (privilégie les préférences
> durables plutôt que les événements ponctuels) et un **réglage admin** pour garder
> les outils mémoire actifs sans injecter le contexte stocké dans les prompts.

### 2. Dossiers d'équipe (folders) — partageables

Les dossiers peuvent être **partagés** avec des permissions **lecture / écriture**
pour des utilisateurs ou des groupes.

**A tester (module 06, API)** : CRUD via `GET/POST /api/v1/folders/` et
`DELETE /api/v1/folders/{id}` ; le **partage** entre deux comptes est proposé en
exercice (variables `OWUI_TENANT2_*`).

### 3. Raisonnement streamé (v0.10.2)

Les modèles "thinking" affichent leurs **étapes de raisonnement en direct** dans
l'interface (bloc repliable). **A tester (module 06, UI)** : sélectionner un
modèle de raisonnement (`OWUI_REASONING_MODEL`), poser une question, vérifier
l'apparition du bloc de raisonnement — avec **skip gracieux** si le modèle n'en
émet pas.

### 4. Compaction automatique du contexte

Quand une conversation approche de la limite de contexte, elle est **résumée
automatiquement** au lieu d'être tronquée. **A tester (module 06, UI)** : plusieurs
tours d'affilée, le modèle **garde le fil** (test de non-régression conversation
longue).

### 5. Uploads de connaissances qui préservent l'arborescence (v0.10.2)

Les imports de fichiers dans une base de connaissances **conservent la structure
des sous-dossiers** au lieu de tout aplatir. **Idée d'exercice (Module 04/06)** :
uploader une arborescence et vérifier que les chemins relatifs sont préservés.

## Nouveautes backend utiles (Module 05 — API)

- **Recherche hybride native** (base de données) pour des requêtes KB nettement
  plus rapides.
- **Sources de récupération externes** : interroger des systèmes tiers directement
  depuis le chat.
- **Système d'événements + webhooks** : les activités de la plateforme peuvent
  déclencher des webhooks sortants.
- **Administration centralisée de l'authentification** (LDAP et OAuth/OIDC sur une
  page admin dédiée — voir piège n°3 plus bas).
- **Config via variables d'environnement** des connexions Ollama/OpenAI (v0.10.2),
  et modèles d'arène définissables par variables d'environnement.

## Changements BREAKING (à connaître)

| Changement | Impact pour vous |
|------------|------------------|
| **Native tool calling par défaut** (remplace le mode "legacy") | Un modèle conversationnel appelé en API non-streaming peut renvoyer `tool_calls` + `content` vide. Testez le texte via l'UI (streaming), ou ciblez des modèles sans outils. |
| **Python côté client en iframe sandbox** | L'exécution Python côté navigateur tourne dans une iframe isolée → ciblez le `frameLocator`, pas le document principal. |
| **Config d'authentification déplacée** sur une page admin dédiée | Les tests qui cherchaient les réglages auth dans les paramètres généraux doivent viser la nouvelle page admin. |
| **Migration BDD irréversible** (backup serveur obligatoire) | Pas d'impact test ; explique pourquoi on ne "revient pas en arrière" sur une instance. |
| Renommage `ENABLE_RAG_LOCAL_WEB_FETCH` → `ENABLE_LOCAL_WEB_FETCH` | Côté déploiement uniquement. |
| Cle You.com : `YOUCOM_API_KEY` → `YDC_API_KEY` | Côté déploiement uniquement. |

## Pièges qui n'ont PAS changé

Les 4 pièges du README principal restent valides :
1. Modal "Quoi de neuf" (overlay) — `dismissModals()` la ferme.
2. Éditeur TipTap — `keyboard.type()` obligatoire.
3. Rate limiting `/api/v1/auths/signin` (~2 min) — login unique en `beforeAll`.
4. APIs renvoyant du HTML via reverse proxy — **slash final** obligatoire.

## Où lire les détails techniques

- **Changelog upstream** : https://github.com/open-webui/open-webui/blob/main/CHANGELOG.md (sections 0.10.0 → 0.10.2)
- **Module pratique** : [`06-nouveautes-v0.10/`](./06-nouveautes-v0.10/README.md)

---

*Mise à jour : 1er juillet 2026. Appliqué à l'instance de cours et aux 6 écoles partenaires (v0.10.2).*
