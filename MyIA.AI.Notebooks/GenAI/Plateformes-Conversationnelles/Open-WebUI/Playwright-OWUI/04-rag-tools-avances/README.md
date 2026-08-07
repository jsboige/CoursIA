# Module 04 - RAG, Outils MCP & Fonctionnalités avancées

> **Format** : Fichier TypeScript `.spec.ts` avec tests commentés. Ouvrez `04-rag-tools.spec.ts` dans VS Code. Certains tests dépendent de la configuration de l'instance (KBs, outils MCP, canaux) — les tests non-applicables seront automatiquement skipped.

## Objectifs pédagogiques

À la fin de ce module, vous serez capable de :

- Tester l'intégration RAG (Retrieval-Augmented Génération) avec des knowledge bases
- Interagir avec les outils MCP (Model Context Protocol) via Playwright
- Tester la fonctionnalité Channels (canaux de discussion de groupe)
- Écrire des tests plus complexes combinant navigation et interactions
- Gérer les interactions conditionnelles (éléments optionnels)

## Durée estimée

**3 heures**

## Contenu du module

### Partie théorique

**RAG dans Open WebUI :**
Le RAG (Retrieval-Augmented Génération) enrichit les réponses du LLM avec des documents.
Dans OWUI (v0.8.8+), on "attache" une Knowledge Base (KB) au chat via le bouton `+`
puis "Joindre une connaissance" :

```
Clic sur le bouton "+" dans la barre de chat
  → Menu avec "Joindre une connaissance"
  → Clic → Liste des KBs disponibles
  → Clic sur "Bibliographie IA"
  → La KB est attachée au chat
  → Les questions suivantes utilisent les documents de la KB
```

> **Note historique** : Avant v0.8.8, le raccourci `#` dans le chat input
> déclenchait un popup de sélection de KB. Ce raccourci a été remplacé.

**Outils MCP :**
Le Model Context Protocol (MCP) permet d'étendre les capacités du LLM
avec des outils externes (recherche web, exécution de code, etc.).
Depuis v0.8.8+, les outils sont accessibles via un bouton icône (engrenages)
dans la barre de chat, qui ouvre un menu avec : Outils, Recherche Web, Image, Code.

**Channels :**
Les canaux sont des espaces de discussion collaboratifs, similaires à Slack.
Il n'y a pas de page `/channels` — les canaux sont accessibles via la sidebar
ou par URL directe `/channels/{id}`.

### Partie pratique

| Test | Description | Concepts |
|------|-------------|----------|
| RAG — menu "+" | Attacher une KB via "Joindre une connaissance" | Menus, sélecteurs |
| RAG — chat avec KB | Poser une question avec KB attachée | Workflow multi-étapes |
| MCP — menu outils | Vérifier la présence des outils (bouton engrenages) | Sélecteurs positionnels |
| MCP — activer outils | Ouvrir le sélecteur d'outils | Dialogs, menus |
| MCP — recherche web | Déclencher une recherche via outil | Toggles, tests fonctionnels |
| Channels — naviguer | Accéder à un canal via API + URL directe | API + navigateur combinés |
| Channels — poster | Envoyer un message dans un canal | TipTap dans un autre contexte |

## Commandes

```bash
npm run test:module4
npx playwright test --grep "04" --headed
```

## Points clés à retenir

- Les KBs s'attachent via le bouton `+` → "Joindre une connaissance" (v0.8.8+)
- Les outils MCP sont optionnels — utilisez `test.skip()` si absents
- Les canaux utilisent le même éditeur TipTap que le chat principal
- Combiner API (pour obtenir les IDs) + navigateur (pour tester l'UI) = tests robustes en headless
- Les sélecteurs positionnels (`nth(1)`) sont un dernier recours quand il n'y a pas d'aria-label stable
