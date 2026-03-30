# Module 04 - RAG, Outils MCP & Fonctionnalites avancees

> **Format** : Fichier TypeScript `.spec.ts` avec tests commentes. Ouvrez `04-rag-tools.spec.ts` dans VS Code. Certains tests dependent de la configuration de l'instance (KBs, outils MCP, canaux) — les tests non-applicables seront automatiquement skipped.

## Objectifs pedagogiques

A la fin de ce module, vous serez capable de :

- Tester l'integration RAG (Retrieval-Augmented Generation) avec des knowledge bases
- Interagir avec les outils MCP (Model Context Protocol) via Playwright
- Tester la fonctionnalite Channels (canaux de discussion de groupe)
- Ecrire des tests plus complexes combinant navigation et interactions
- Gerer les interactions conditionnelles (elements optionnels)

## Duree estimee

**3 heures**

## Contenu du module

### Partie theorique

**RAG dans Open WebUI :**
Le RAG (Retrieval-Augmented Generation) enrichit les reponses du LLM avec des documents.
Dans OWUI (v0.8.8+), on "attache" une Knowledge Base (KB) au chat via le bouton `+`
puis "Joindre une connaissance" :

```
Clic sur le bouton "+" dans la barre de chat
  → Menu avec "Joindre une connaissance"
  → Clic → Liste des KBs disponibles
  → Clic sur "Bibliographie IA"
  → La KB est attachee au chat
  → Les questions suivantes utilisent les documents de la KB
```

> **Note historique** : Avant v0.8.8, le raccourci `#` dans le chat input
> declenchait un popup de selection de KB. Ce raccourci a ete remplace.

**Outils MCP :**
Le Model Context Protocol (MCP) permet d'etendre les capacites du LLM
avec des outils externes (recherche web, execution de code, etc.).
Depuis v0.8.8+, les outils sont accessibles via un bouton icone (engrenages)
dans la barre de chat, qui ouvre un menu avec : Outils, Recherche Web, Image, Code.

**Channels :**
Les canaux sont des espaces de discussion collaboratifs, similaires a Slack.
Il n'y a pas de page `/channels` — les canaux sont accessibles via la sidebar
ou par URL directe `/channels/{id}`.

### Partie pratique

| Test | Description | Concepts |
|------|-------------|----------|
| RAG — menu "+" | Attacher une KB via "Joindre une connaissance" | Menus, selecteurs |
| RAG — chat avec KB | Poser une question avec KB attachee | Workflow multi-etapes |
| MCP — menu outils | Verifier la presence des outils (bouton engrenages) | Selecteurs positionnels |
| MCP — activer outils | Ouvrir le selecteur d'outils | Dialogs, menus |
| MCP — recherche web | Declencher une recherche via outil | Toggles, tests fonctionnels |
| Channels — naviguer | Acceder a un canal via API + URL directe | API + navigateur combines |
| Channels — poster | Envoyer un message dans un canal | TipTap dans un autre contexte |

## Commandes

```bash
npm run test:module4
npx playwright test --grep "04" --headed
```

## Points cles a retenir

- Les KBs s'attachent via le bouton `+` → "Joindre une connaissance" (v0.8.8+)
- Les outils MCP sont optionnels — utilisez `test.skip()` si absents
- Les canaux utilisent le meme editeur TipTap que le chat principal
- Combiner API (pour obtenir les IDs) + navigateur (pour tester l'UI) = tests robustes en headless
- Les selecteurs positionnels (`nth(1)`) sont un dernier recours quand il n'y a pas d'aria-label stable
