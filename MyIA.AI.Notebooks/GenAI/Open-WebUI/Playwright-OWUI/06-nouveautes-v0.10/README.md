# Module 06 — Tester les nouveautés v0.10 ("l'ère agentique")

[← Retour Playwright-OWUI](../README.md) | [Nouveautés v0.10](../WHATS-NEW-v0.10.md)

> **Pré-requis.** Avoir fait les modules 03 (chat & streaming) et 05 (API testing).
> Ce module réutilise les deux familles de tests vues précédemment : **API** (rapide,
> déterministe) et **UI** (rendu et interaction).

La ligne **v0.10** (juin-juillet 2026) est la plus grosse évolution d'Open WebUI
depuis la v0.8. Elle transforme la plateforme en **environnement agentique** :
mémoire repensée, dossiers d'équipe partageables, raisonnement affiché en direct,
compaction automatique des longues conversations. Ce module montre **comment
écrire des tests** pour ces surfaces.

## Ce qu'on teste ici

| # | Fonctionnalité | Version | Famille | Fichier |
|---|----------------|---------|---------|---------|
| 1-2 | **Mémoire** (refonte, champ `type`) | v0.10.0 | API | `06-nouveautes.spec.ts` (06a) |
| 3-4 | **Dossiers** (CRUD) | v0.10.0 | API | 06a |
| 5 | **Dossiers d'équipe** (partage) | v0.10.0 | API | 06a (exercice, 2e compte) |
| 6 | **Raisonnement streamé** | v0.10.2 | UI | 06b |
| 7 | **Compaction automatique** | v0.10.0 | UI | 06b |

## Concepts pédagogiques nouveaux

### 1. Tester une donnée qui s'injecte ailleurs — la mémoire

La **mémoire** est particulière : un souvenir créé est ensuite **injecté dans les
prompts** des conversations. Un test qui crée un souvenir et l'oublie **pollue les
vraies conversations** de l'instance. D'où la règle de ce module :

> **Tout test d'écriture nettoie derrière lui.** On utilise un bloc `finally`
> pour garantir la suppression, même si une assertion échoue avant.

```typescript
const created = await addMemory(request, OWUI_URL, token, `${TAG} ...`);
let cleaned = false;
try {
  // ... assertions ...
  cleaned = await deleteMemory(request, OWUI_URL, token, created.id);
} finally {
  if (!cleaned) await deleteMemory(request, OWUI_URL, token, created.id).catch(() => {});
}
```

C'est un pattern général en tests d'intégration : **isolation par nettoyage**.
On marque aussi chaque objet créé d'un tag unique (`[pw-module06]`) pour le
repérer facilement si un nettoyage échoue.

### 2. Feature detection vs assertion stricte

La refonte mémoire v0.10 ajoute un champ **`type`** (ex. `"context"`) à chaque
souvenir. On s'en sert comme **preuve de version** :

```typescript
expect(created.type, 'le champ "type" (v0.10) doit être présent').toBeTruthy();
```

Sur une instance antérieure à v0.10, ce champ serait absent : le test le
détecterait. C'est une façon de **documenter une différence de version dans le
test lui-même**.

### 3. Le raisonnement streamé — un contenu qui n'existe pas toujours

Depuis **v0.10.2**, les modèles "thinking" affichent leurs étapes de raisonnement
en direct. Mais **tous les modèles n'en émettent pas**. Un bon test ne doit donc
pas échouer sur l'absence de raisonnement : il **skip proprement** si la
fonctionnalité n'est pas exercée (modèle non configuré, ou modèle sans
raisonnement visible). C'est la différence entre *"le test a échoué"* et *"la
pré-condition n'était pas réunie"*.

### 4. Tester la compaction sans saturer le contexte

La **compaction automatique** résume la conversation quand on approche de la
limite de contexte. Impossible de saturer le contexte dans un test rapide : on
teste donc le **comportement observable** — plusieurs tours d'affilée continuent
de répondre et le modèle **garde le fil** (il retrouve une info du 1er tour).
C'est un test de **non-régression de la conversation longue**.

## Exécuter ce module

```bash
# depuis le dossier Playwright-OWUI/
cp .env.example .env         # puis renseigner OWUI_URL / OWUI_EMAIL / OWUI_PASSWORD
npm install
npx playwright install chromium

# tout le module 06
npm run test:module6
# ou un seul test
npx playwright test 06-nouveautes-v0.10 --grep "memoire"
```

Variables `.env` utiles pour ce module :

| Variable | Rôle | Obligatoire |
|----------|------|-------------|
| `OWUI_URL` / `OWUI_EMAIL` / `OWUI_PASSWORD` | Instance + compte | Oui (06a) |
| `OWUI_CLOUD_MODEL` | Modèle rapide pour la compaction | Non (défaut `gpt-5.1`) |
| `OWUI_REASONING_MODEL` | Modèle "thinking" pour le test de raisonnement | Non (skip si absent) |
| `OWUI_TENANT2_EMAIL` / `OWUI_TENANT2_PASSWORD` | 2e compte pour le partage | Non (exercice) |

> **Sans configuration**, les tests API se connectent, les tests dépendant d'un
> modèle de raisonnement ou d'un 2e compte se mettent **en pause** (`skip`) — le
> module ne produit jamais de faux échec.

## Pièges spécifiques v0.10

1. **Native tool calling par défaut.** En v0.10, l'appel d'outils "natif" devient
   le comportement par défaut. Pour un modèle purement conversationnel appelé via
   l'API en mode non-streaming, une réponse peut revenir avec `tool_calls` et un
   `content` vide. Ce n'est pas un bug : c'est le modèle qui choisit d'appeler un
   outil. Testez le contenu **via l'UI (streaming)** ou ciblez des modèles sans
   outils pour les assertions de texte.
2. **Python côté client en iframe sandbox.** L'exécution Python côté navigateur
   tourne désormais dans une iframe isolée (origine opaque). Si vous testez une
   fonction qui exécute du Python côté client, le contenu vit dans un `iframe` —
   il faut cibler le `frameLocator`, pas le document principal.
3. **Migration BDD irréversible.** La montée en v0.10 applique des migrations non
   réversibles (backup obligatoire côté serveur). Sans impact sur vos tests, mais
   explique pourquoi on ne peut pas "revenir en arrière" sur une instance de cours.

## Pour aller plus loin

- Nouveautés détaillées, côté étudiant : [`../WHATS-NEW-v0.10.md`](../WHATS-NEW-v0.10.md)
- Changelog upstream : https://github.com/open-webui/open-webui/blob/main/CHANGELOG.md (sections 0.10.0 → 0.10.2)

---

*Module 06 — Série Playwright-OWUI (CoursIA GenAI). Cible : Open WebUI v0.10.2.*
