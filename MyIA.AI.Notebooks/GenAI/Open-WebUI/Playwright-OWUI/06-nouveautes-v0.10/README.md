# Module 06 — Tester les nouveautes v0.10 ("l'ere agentique")

[← Retour Playwright-OWUI](../README.md) | [Nouveautes v0.10](../WHATS-NEW-v0.10.md)

> **Pre-requis.** Avoir fait les modules 03 (chat & streaming) et 05 (API testing).
> Ce module reutilise les deux familles de tests vues precedemment : **API** (rapide,
> deterministe) et **UI** (rendu et interaction).

La ligne **v0.10** (juin-juillet 2026) est la plus grosse evolution d'Open WebUI
depuis la v0.8. Elle transforme la plateforme en **environnement agentique** :
memoire repensee, dossiers d'equipe partageables, raisonnement affiche en direct,
compaction automatique des longues conversations. Ce module montre **comment
ecrire des tests** pour ces surfaces.

## Ce qu'on teste ici

| # | Fonctionnalite | Version | Famille | Fichier |
|---|----------------|---------|---------|---------|
| 1-2 | **Memoire** (refonte, champ `type`) | v0.10.0 | API | `06-nouveautes.spec.ts` (06a) |
| 3-4 | **Dossiers** (CRUD) | v0.10.0 | API | 06a |
| 5 | **Dossiers d'equipe** (partage) | v0.10.0 | API | 06a (exercice, 2e compte) |
| 6 | **Raisonnement streame** | v0.10.2 | UI | 06b |
| 7 | **Compaction automatique** | v0.10.0 | UI | 06b |

## Concepts pedagogiques nouveaux

### 1. Tester une donnée qui s'injecte ailleurs — la memoire

La **memoire** est particuliere : un souvenir cree est ensuite **injecte dans les
prompts** des conversations. Un test qui cree un souvenir et l'oublie **pollue les
vraies conversations** de l'instance. D'ou la regle de ce module :

> **Tout test d'ecriture nettoie derriere lui.** On utilise un bloc `finally`
> pour garantir la suppression, meme si une assertion echoue avant.

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

C'est un pattern general en tests d'integration : **isolation par nettoyage**.
On marque aussi chaque objet cree d'un tag unique (`[pw-module06]`) pour le
reperer facilement si un nettoyage echoue.

### 2. Feature detection vs assertion stricte

La refonte memoire v0.10 ajoute un champ **`type`** (ex. `"context"`) a chaque
souvenir. On s'en sert comme **preuve de version** :

```typescript
expect(created.type, 'le champ "type" (v0.10) doit etre present').toBeTruthy();
```

Sur une instance anterieure a v0.10, ce champ serait absent : le test le
detecterait. C'est une facon de **documenter une difference de version dans le
test lui-meme**.

### 3. Le raisonnement streame — un contenu qui n'existe pas toujours

Depuis **v0.10.2**, les modèles "thinking" affichent leurs étapes de raisonnement
en direct. Mais **tous les modèles n'en emettent pas**. Un bon test ne doit donc
pas echouer sur l'absence de raisonnement : il **skip proprement** si la
fonctionnalite n'est pas exercee (modèle non configure, ou modèle sans
raisonnement visible). C'est la difference entre *"le test a echoue"* et *"la
pre-condition n'etait pas reunie"*.

### 4. Tester la compaction sans saturer le contexte

La **compaction automatique** resume la conversation quand on approche de la
limite de contexte. Impossible de saturer le contexte dans un test rapide : on
teste donc le **comportement observable** — plusieurs tours d'affilee continuent
de repondre et le modèle **garde le fil** (il retrouve une info du 1er tour).
C'est un test de **non-regression de la conversation longue**.

## Executer ce module

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

| Variable | Role | Obligatoire |
|----------|------|-------------|
| `OWUI_URL` / `OWUI_EMAIL` / `OWUI_PASSWORD` | Instance + compte | Oui (06a) |
| `OWUI_CLOUD_MODEL` | Modèle rapide pour la compaction | Non (defaut `gpt-5.1`) |
| `OWUI_REASONING_MODEL` | Modèle "thinking" pour le test de raisonnement | Non (skip si absent) |
| `OWUI_TENANT2_EMAIL` / `OWUI_TENANT2_PASSWORD` | 2e compte pour le partage | Non (exercice) |

> **Sans configuration**, les tests API se connectent, les tests dependant d'un
> modèle de raisonnement ou d'un 2e compte se mettent **en pause** (`skip`) — le
> module ne produit jamais de faux echec.

## Pieges spécifiques v0.10

1. **Native tool calling par defaut.** En v0.10, l'appel d'outils "natif" devient
   le comportement par defaut. Pour un modèle purement conversationnel appele via
   l'API en mode non-streaming, une reponse peut revenir avec `tool_calls` et un
   `content` vide. Ce n'est pas un bug : c'est le modèle qui choisit d'appeler un
   outil. Testez le contenu **via l'UI (streaming)** ou ciblez des modèles sans
   outils pour les assertions de texte.
2. **Python cote client en iframe sandbox.** L'execution Python cote navigateur
   tourne desormais dans une iframe isolee (origine opaque). Si vous testez une
   fonction qui execute du Python cote client, le contenu vit dans un `iframe` —
   il faut cibler le `frameLocator`, pas le document principal.
3. **Migration BDD irreversible.** La montee en v0.10 applique des migrations non
   reversibles (backup obligatoire cote serveur). Sans impact sur vos tests, mais
   explique pourquoi on ne peut pas "revenir en arriere" sur une instance de cours.

## Pour aller plus loin

- Nouveautes detaillees, cote etudiant : [`../WHATS-NEW-v0.10.md`](../WHATS-NEW-v0.10.md)
- Changelog upstream : https://github.com/open-webui/open-webui/blob/main/CHANGELOG.md (sections 0.10.0 → 0.10.2)

---

*Module 06 — Serie Playwright-OWUI (CoursIA GenAI). Cible : Open WebUI v0.10.2.*
