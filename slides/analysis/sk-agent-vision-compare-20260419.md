# Vision Comparison - sk-agent GLM-4.6v - 2026-04-19

## Methodology

- Tool: `mcp__sk-agent__call_agent` with agent `glm-4.6v` (vision-analyst)
- Sources: PPTX reference PNGs (`pptx-reference/slide-NN.png`) vs Slidev export pages (extracted via `pdftoppm -r 150` from `export-current.pdf`)
- Prompt: "Compare these two slides [...] Return concise verdict: MATCH / PARTIAL / DIFFERENT + 1 sentence explanation."
- All slides selected are tagged EXACT in their respective `mapping-20260419.md`

## Results Table

| Deck | PPTX # | PPTX Title | Slidev # | sk-agent Verdict | Notes |
|------|--------|-----------|----------|-----------------|-------|
| 01 | 11 | Les fondements de l'IA | 12 | **DIFFERENT** | Same title and disciplines but different text content, missing neural diagram in Slidev, different bullet symbols |
| 01 | 15 | Dans la vie de tous les jours | 18 | **DIFFERENT** | Different titles, different number/naming of categories, extra categories in Slidev (Transport, Sante, Quotidien), different formatting |
| 01 | 37 | Agent fonde sur des buts | 40 | **DIFFERENT** | Different bullet text and phrasing, more detailed bullets in Slidev, diagram structurally similar but different background |
| 02 | 38 | Exploration A* | 34 | **PARTIAL** | Core textual content identical, but Slidev adds a diagram, has accent differences ("Idee" vs "Idee"), lacks PPTX footer/page number |
| 02 | 60 | Minimax | 57 | **PARTIAL** | Shares Minimax concepts, decision tree, formula, but differs in language rendering, bullet styles, formula layout, title color, no footer in Slidev |
| 02 | 70 | Problemes a satisfaction de contraintes (CSPs) | 62 | **DIFFERENT** | Both cover CSPs but PPTX focuses on formal representation with diagrams, Slidev shows map coloring example with Australia map - different content focus |
| 03 | 46 | Definition d'un domaine de planification | 31 | **PARTIAL** | Both cover PDDL/action schema, but PPTX includes "Domaine de planification" section and footer with PDDL plan example missing in Slidev; Slidev reorganizes to 3 sections instead of 4 |
| 03 | 57 | Ontologies | 45 | **PARTIAL** | Same section headings and core concepts, but different diagrams (hierarchical tree vs network graph), different detail level, simplified text in Slidev |
| 03 | 61 | Smart Contracts | 49 | **PARTIAL** | Same core topics (cryptography, blockchain, complex contracts) but different formatting, structure, no image in Slidev, some terminology variations |

## Summary by Verdict

| Verdict | Count | Decks |
|---------|-------|-------|
| MATCH | 0 / 9 | - |
| PARTIAL | 5 / 9 | D02x2, D03x3 |
| DIFFERENT | 4 / 9 | D01x3, D02x1 |

## Analysis

### Red Flags Critiques

1. **Deck 01 - 3/3 DIFFERENT**: Les 3 slides selectionnees dans le mapping EXACT de deck 01 sont jugees DIFFERENT par vision. Cela indique un probleme systematique : le mapping text-based "EXACT" ne signifie pas "contenu identique" pour deck 01. En particulier, les images/diagrammes (schema neuronal slide 11, categories illustrees slide 15) sont absents dans Slidev.

2. **Deck 02 - CSP slide (PPTX#70 vs Slidev#62) DIFFERENT**: Le mapping indique EXACT mais la vision detecte un changement de contenu majeur (representation formelle vs exemple Australie). Erreur de mapping probable, ou slide Slidev 62 correspond a un autre slide PPTX.

3. **Aucun MATCH parmi 9 comparaisons**: Meme les PARTIAL presentent des differences notables (diagrammes differents, sections manquantes, images absentes). La qualite de conversion PPTX->Slidev est systematiquement en dessous de l'etiquette EXACT.

### Pattern General

- Les pertes les plus frequentes : images/diagrammes absents dans Slidev, reformulations de texte, sections tronquees ou reorganisees
- Deck 01 (introduction) est le plus degrade - slides riches en images PPTX converties en texte pur
- Deck 03 (logique) est le moins mauvais avec 3/3 PARTIAL (contenu present mais incomplet)

## Recommendations

1. **Requalifier les EXACT de deck 01** : Passer en revue toutes les 29 slides EXACT de deck 01, au moins celles avec images dans le PPTX - elles sont probablement PARTIAL ou DIFFERENT
2. **Verifier specifiquement PPTX#70 vs Slidev#62 dans deck 02** : Possible mauvais appariement dans le mapping
3. **Priorite de correction** : Deck 01 > Deck 02 (CSP section) > Deck 03 (manques mineurs)
4. **Critere qualite** : Viser 0 DIFFERENT et PARTIAL < 20% avant prochain cours EPITA
