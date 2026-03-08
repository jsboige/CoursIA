# Module 04 - RAG, Outils MCP & Fonctionnalites avancees

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
Dans OWUI, on "attache" une Knowledge Base (KB) au chat via le raccourci `#`.

```
Utilisateur tape : #
  → Popup avec la liste des KBs
  → Clic sur "Bibliographie IA"
  → La KB est attachee au chat
  → Les questions suivantes utilisent les documents de la KB
```

**Outils MCP :**
Le Model Context Protocol (MCP) permet d'etendre les capacites du LLM
avec des outils externes (recherche web, execution de code, etc.).

**Channels :**
Les canaux sont des espaces de discussion collaboratifs, similaires a Slack.

### Partie pratique

| Test | Description | Concepts |
|------|-------------|----------|
| RAG — raccourci # | Declencher la selection de KB | Evenements clavier, popups |
| RAG — chat avec KB | Poser une question avec KB attachee | Workflow multi-etapes |
| MCP — bouton outils | Verifier la presence des outils | Visibilite conditionnelle |
| MCP — activer outils | Ouvrir le selecteur d'outils | Dialogs, menus |
| MCP — recherche web | Declencher une recherche via outil | Tests fonctionnels integres |
| Channels — naviguer | Acceder aux canaux | Navigation conditionnelle |
| Channels — poster | Envoyer un message dans un canal | TipTap dans un autre contexte |

## Commandes

```bash
npm run test:module4
npx playwright test --grep "04" --headed
```

## Points cles a retenir

- Le raccourci `#` dans le chat ouvre un popup de selection de KB
- Les outils MCP sont optionnels — utilisez `test.skip()` si absents
- Les canaux utilisent le meme editeur TipTap que le chat principal
- Combiner navigation + interaction = tests plus realistes mais plus fragiles
