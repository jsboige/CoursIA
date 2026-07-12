# Visual Audit - Deck 02 Resolution-Problemes (Post-Fix)

**Date**: 2026-04-19
**Branch**: fix/slides-02-visual-audit-strict
**Method**: sk-agent glm-4.6v vision comparison with correct PPTX-Slidev pairing
**Screenshots**: analysis/screenshots-v2/ (captured after accent fixes)

---

## Summary

| Metric | Count | Percentage |
|--------|-------|------------|
| Total mapped pairs | 68 | — |
| MATCH | 0 | 0% |
| PARTIAL | 61 | 90% |
| DIFFERENT | 7 | 10% |
| EXTRA (section headers) | 12 | — |
| MISSING (PPTX-only) | 26 | — |
| Target: MATCH rate | >=80% | NOT MET |
| Target: DIFFERENT | 0 | NOT MET (7 remaining) |

## Verdict Scale

- **MATCH**: Content faithfully reproduced, minor visual style differences acceptable
- **PARTIAL**: Content preserved but notable differences (accent issues, layout changes, minor rephrasing)
- **DIFFERENT**: Missing content, wrong content, or critical visual loss

---

## Detailed Audit Table

| # | Slidev | PPTX | Title | Verdict | Notes |
|---|--------|------|-------|---------|-------|
| 1 | 01 | 01 | Resolution de problemes | PARTIAL | Accents stripped from title |
| 2 | 02 | 02 | Plan du cours | PARTIAL | Visual style differences |
| 3 | 03 | 03 | Sommaire | PARTIAL | Visual style differences |
| 4 | 05 | 04 | Agent fonde sur des buts | PARTIAL | Accent lost, extra panel added |
| 5 | 06 | 05 | Resolution de problemes | PARTIAL | Accents stripped, diagram restyled |
| 6 | 07 | 06 | Agents de resolution | PARTIAL | Content on slide 07 (04 is section header) |
| 7 | 08 | 07 | Exemple: Itineraire | PARTIAL | Accent lost |
| 8 | 09 | 08 | Types de problemes | PARTIAL | Accents lost |
| 9 | 10 | 09 | Formulation de problemes | PARTIAL | Accents fixed (a->a), pseudocode OK |
| 10 | 11 | 10 | Selection espace des etats | PARTIAL | Accents fixed (tres->tres, detours->detours) |
| 11 | 12 | 11 | Exemple Abstraction | PARTIAL | Accents fixed (assemble->assemble, detachees->detachees) |
| 12 | 13 | 12 | Le taquin | PARTIAL | Accents fixed (pieces->pieces, moitie->moitie) |
| 13 | 14 | 13 | Les 8 reines | PARTIAL | Visual style differences |
| 14 | 16 | 16 | Arbre d'exploration | PARTIAL | Visual style differences |
| 15 | 17 | 17 | Arbre d'exploration: exemple | PARTIAL | Tree diagram replaced by text |
| 16 | 18 | 18 | Exploration de graphe | PARTIAL | Accents fixed (Idee->Idee, Frontiere->Frontiere) |
| 17 | 19 | 19 | Infrastructure: Etats vs Noeuds | PARTIAL | Visual style differences |
| 18 | 20 | 20 | Strategies d'exploration | PARTIAL | Accents lost |
| 19 | 22 | 21 | Strategies non informee | PARTIAL | Accents lost |
| 20 | 23 | 22 | BFS | PARTIAL | Diagram preserved, node shapes differ |
| 21 | 24 | 23 | Proprietes de l'exploration en largeur | PARTIAL | Visual style differences |
| 22 | 25 | 24 | UCS | PARTIAL | Visual style differences |
| 23 | 26 | 25 | DFS | PARTIAL | Visual style differences |
| 24 | 27 | 26 | DLS | PARTIAL | Visual style differences |
| 25 | 28 | 27 | IDS | PARTIAL | Visual style differences |
| 26 | 29 | 28 | Exploration Bidirectionnelle | PARTIAL | Visual style differences |
| 27 | 30 | 29 | Resume non informee | PARTIAL | Visual style differences |
| 28 | 31 | 30 | Missionnaires et cannibales | PARTIAL | Visual style differences |
| 29 | 33 | 36 | Exploration gloutonne | PARTIAL | Visual style differences |
| 30 | 34 | 38 | Exploration A* | PARTIAL | Visual style differences |
| 31 | 35 | 39 | Caracteristiques de A* | PARTIAL | Visual style differences |
| 32 | 36 | 40 | Variations | PARTIAL | Visual style differences |
| 33 | 37 | 41 | Effet heuristique | PARTIAL | Visual style differences |
| 34 | 38 | 42 | Production d'heuristiques | PARTIAL | Visual style differences |
| 35 | 40 | 43 | Algorithmes exploration locale | PARTIAL | Chessboard diagrams missing |
| 36 | 41 | 44 | Paysage espace des etats | PARTIAL | Visual style differences |
| 37 | 42 | 45 | HCS | PARTIAL | Visual style differences |
| 38 | 43 | 46 | Recuit simule | PARTIAL | Visual style differences |
| 39 | 44 | 47 | LBS | PARTIAL | Visual style differences |
| 40 | 45 | 48 | Algorithmes genetiques | PARTIAL | Visual style differences |
| 41 | 46 | 49 | Genetique pour les 8 reines | PARTIAL | Visual style differences |
| 42 | 48 | 51 | Espaces continus | PARTIAL | Visual style differences |
| 43 | 50 | 52 | Actions non deterministes | PARTIAL | Diagram added (ET-OU tree), content preserved |
| 44 | 51 | 53 | Observations partielles | PARTIAL | Belief state diagram added, content preserved |
| 45 | 52 | 54 | Exploration en ligne | PARTIAL | LRTA* pseudocode added, content preserved |
| 46 | 53 | 55 | Resume informee | PARTIAL | Visual style differences |
| 47 | 54 | 58 | Jeux vs Exploration | PARTIAL | Visual style differences |
| 48 | 56 | 59 | Arbre de jeu | PARTIAL | Visual style differences |
| 49 | 57 | 60 | Minimax | PARTIAL | Decision tree preserved, accents lost |
| 50 | 58 | 61 | Algorithme Minimax | PARTIAL | Pseudocode preserved, accents lost |
| 51 | 59 | 62 | Elagage Alpha-Beta | PARTIAL | Visual style differences |
| 52 | 60 | 63 | Decisions imparfaites | PARTIAL | Visual style differences |
| 53 | 65 | 70 | CSPs intro (section) | DIFFERENT | Slidev is section header only; PPTX has full content with diagrams |
| 54 | 66 | 70 | CSPs intro (content) | PARTIAL | Different structure but core CSP topic preserved |
| 55 | 69 | 81 | Backtracking | DIFFERENT | PPTX has commutativity, inference, strategies; Slidev has BACKTRACK code only |
| 56 | 70 | 79 | Propagation contraintes | PARTIAL | AC-3 preserved, PPTX more comprehensive |
| 57 | 71 | 82 | Heuristiques variables/valeurs | PARTIAL | MRV, LCV preserved; extras missing |
| 58 | 72 | 85 | Structure des problemes | DIFFERENT | PPTX has detailed algorithms; Slidev has simplified overview |
| 59 | 73 | 84 | Exploration locale CSPs | DIFFERENT | PPTX has full 2-column layout; Slidev has min-conflicts only |
| 60 | 74 | 73 | Techniques resolution CSPs | PARTIAL | Content preserved, visual differences |
| 61 | 75 | 74 | Domaines des CSPs | PARTIAL | Core content preserved |
| 62 | 76 | 75 | Graphe de contraintes | PARTIAL | Diagrams preserved |
| 63 | 77 | 76 | Types de contraintes | PARTIAL | Hypergraph diagram missing |
| 64 | 78 | 77 | CSPs courants | DIFFERENT | Same title but completely different content |
| 65 | 79 | 87 | Applications modernes | PARTIAL | Content preserved, accent errors |
| 66 | 80 | 88 | Resume CSPs (1/2) | PARTIAL | Split from PPTX, missing section |
| 67 | 81 | 88 | Resume CSPs (2/2) | PARTIAL | Split from PPTX, rephrased |
| 68 | 82 | 90 | TP | DIFFERENT | Content stripped, essentially empty |

## EXTRA Slides (Slidev-only, no PPTX equivalent)

| Slidev # | Title | Type |
|----------|-------|------|
| 04 | Agents de resolution de Problemes | Section header |
| 15 | Resolution de Problemes par Exploration | Section header |
| 21 | Exploration Non Informee | Section header |
| 32 | Exploration Informee | Section header |
| 39 | Algorithmes d'Exploration Locale | Section header |
| 47 | Exploration Locale - Espaces Continus | Section header |
| 49 | Extensions | Section header |
| 55 | Jeux vs Exploration (duplicate) | Duplicate/variant |
| 61 | Problemes a Satisfaction de Contraintes | Section header |
| 63 | CSP: Exemple cryptarithme | New example |
| 64 | Resolution de CSPs: Generation et test | New content |
| 83 | TP (duplicate) | Duplicate |

## MISSING Slides (PPTX-only, intentionally removed)

| PPTX # | Title | Reason |
|--------|-------|--------|
| 14 | Questions? | Inter-section separator |
| 15 | Sommaire | Inter-section separator |
| 31 | Questions? | Inter-section separator |
| 32 | TP | Mid-section removed |
| 33 | Sommaire | Inter-section separator |
| 34 | Strategies d'exploration informee | Section intro removed |
| 35 | Exploration par le meilleur d'abord | Content removed |
| 37 | Heuristiques admissibles | Content removed |
| 50 | TP | Mid-section removed |
| 56 | Questions? | Inter-section separator |
| 57 | Sommaire | Inter-section separator |
| 64 | Techniques avancees | Content removed |
| 65 | Exploration Monte-Carlo | Content removed |
| 66 | Classes de Jeux complexes | Content removed |
| 67 | Resume Jeux | Content removed |
| 68 | Questions? | Inter-section separator |
| 69 | Sommaire | Inter-section separator |
| 71 | Exemple: coloration de carte | Replaced by cryptarithme |
| 72 | Solutions d'un CSP | Content merged |
| 78 | Formulation standard | Content removed |
| 80 | Contraintes globales | Content merged |
| 83 | Verification avant | Content merged |
| 86 | Solveurs modernes | Content removed |
| 89 | Questions? | Inter-section separator |
| 91 | Sommaire | Inter-section separator |
| 92 | Plan du cours | Final separator |

## DIFFERENT Slides - Detail and Assessment

| Pair | Root Cause | Fixable? | Priority |
|------|-----------|----------|----------|
| #53 Slidev-65 / PPTX-70 | Section header replaces content slide | Needs full content restore | HIGH |
| #55 Slidev-69 / PPTX-81 | Backtracking content significantly reduced | Needs content restore | HIGH |
| #58 Slidev-72 / PPTX-85 | Structure problemes simplified | Needs algorithm details | MEDIUM |
| #59 Slidev-73 / PPTX-84 | Exploration locale CSPs truncated | Needs min-conflicts + extras | HIGH |
| #64 Slidev-78 / PPTX-77 | CSPs courants has different content | Content mismatch, not just visual | HIGH |
| #68 Slidev-82 / PPTX-90 | TP slide essentially empty | Needs content restore | LOW |

## Changes Made in This Fix Cycle

1. **Accent fixes** (slides 10-13, 18, 23): a->a, tres->tres, detours->detours, Idee->Idee, Frontiere->Frontiere, pieces->pieces, moitie->moitie, assemble->assemble, detachees->detachees
2. **Diagram additions** (slides 50-52): ET-OU tree for non-deterministic actions, belief state diagram, LRTA* pseudocode
3. **Image positioning fixes**: All overlay images use `position:absolute` instead of side-by-side layout
4. **Overflow fixes**: Text reflow on dense slides to prevent content clipping
