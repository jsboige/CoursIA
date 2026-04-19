# Visual Audit - Deck 03 Logique (Issue #313)

**Date**: 2026-04-19
**Objective**: Identify IMAGE REGRESSIONS - PPTX slides with pedagogically valuable diagrams that were converted to plain text in Slidev
**PPTX Reference**: 66 slides in `pptx-reference/`
**Slidev Deck**: 53 slides in `slides.md`
**Mapping**: `mapping-20260419.md`

## Audit Table

| Slidev # | PPTX ref # | Slidev title | PPTX has image? | Regression? | sk-agent verdict | Action needed |
|----------|------------|--------------|-----------------|-------------|------------------|---------------|
| 1 | 1 | Bases de connaissances et Logique | No | N/A | Text only slide | No action needed |
| 2 | 2 | Plan du cours | No | N/A | Text only slide | No action needed |
| 3 | 3 | Sommaire | No | N/A | Text only slide | No action needed |
| 4,5 | 4 | Agents fondes sur les connaissances | **YES** | **REGRESSION** | **KB-Agent architecture diagram with Tell/Ask flow** | **Restore KB-Agent architecture diagram** |
| 6 | 5 | Exemple: le monde du Wumpus | **YES** | PARTIAL | **Wumpus world grid visualization** | Keep current img_003.png, verify matches PPTX |
| 7 | 6 | Representation et logique | No | N/A | Text only slide | No action needed |
| 8 | 10 | Logique Propositionnelle | No | N/A | Text only slide | No action needed |
| 9 | - | Enonces propositionnels | N/A | N/A | Extra Slidev slide | No action needed |
| 10 | - | Syntaxe de la logique propositionnelle | N/A | N/A | Extra Slidev slide | No action needed |
| 11 | - | Semantique de la logique propositionnelle | N/A | N/A | Extra Slidev slide | No action needed |
| 12 | - | Infrence propositionnelle | N/A | N/A | Extra Slidev slide | No action needed |
| 13 | 12 | Regles d'inférence | **YES** | **REGRESSION** | **Logical inference rules visualization (Modus Ponens, And-Elimination, etc.)** | **Restore inference rules diagram** |
| 14 | 15 | Resolution | **YES** | **REGRESSION** | **Resolution proof procedure diagram** | **Restore resolution procedure diagram** |
| 15 | 14 | Forward et Backward Chaining | **YES** | **REGRESSION** | **Forward/Backward chaining flowchart diagrams** | **Restore chaining flowcharts** |
| 16 | - | Proprietes des systemes d'inférence | N/A | N/A | Extra Slidev slide | No action needed |
| 17 | 23 | Logique du Premier Ordre | No | N/A | Text only slide | No action needed |
| 18 | 20 | Limites de la logique propositionnelle | No | N/A | Text only slide | No action needed |
| 19 | 24 | Syntaxe de la logique du premier ordre | No | N/A | Text only slide | No action needed |
| 20 | 33 | Semantique de la logique du premier ordre | No | N/A | Text only slide | No action needed |
| 21 | 26 | Quantificateurs | No | N/A | Text only slide | No action needed |
| 22 | - | Axiomes et ingenierie des donnees | N/A | N/A | Extra Slidev slide | No action needed |
| 23 | 34 | Infrence en logique du premier ordre | No | N/A | Text only slide | No action needed |
| 24 | 35 | Unification | **YES** | **REGRESSION** | **Unification algorithm diagram** | **Restore unification algorithm visualization** |
| 25 | 35 | Forward chaining en FOL | **YES** | **REGRESSION** | **FOL forward chaining diagram** | **Restore FOL forward chaining diagram** |
| 26 | 35 | Backward chaining en FOL | **YES** | **REGRESSION** | **FOL backward chaining diagram** | **Restore FOL backward chaining diagram** |
| 27 | 35 | Resolution en FOL | **YES** | **REGRESSION** | **FOL resolution diagram** | **Restore FOL resolution diagram** |
| 28 | - | Applications | N/A | N/A | Extra Slidev slide | No action needed |
| 29,30 | 45 | Planification | **YES** | **REGRESSION** | **Planning problem definition diagram** | **Restore planning visualization** |
| 31 | 46 | Definition d'un domaine de planification | **YES** | **REGRESSION** | **PDDL action schema diagram** | **Restore PDDL schema visualization** |
| 32 | - | Exemple PDDL: Transport logistique | N/A | N/A | Extra Slidev slide | No action needed |
| 33 | 47 | Approches de planification | **YES** | **REGRESSION** | **Planning approaches comparison diagram** | **Restore planning approaches diagram** |
| 34 | 48 | Exploration de l'espace des etats | **YES** | **REGRESSION** | **State space search tree diagram** | **Restore state space visualization** |
| 35 | - | Heuristiques pour la planification | N/A | N/A | Extra Slidev slide | No action needed |
| 36 | 49 | Graphes de planification | **YES** | **REGRESSION** | **GraphPlan planning graph visualization** | **Restore planning graph diagram** |
| 37 | - | Algorithme GraphPlan | N/A | N/A | Extra Slidev slide | No action needed |
| 38 | 50 | Planification par contraintes | **YES** | **REGRESSION** | **Constraint-based planning diagram** | **Restore constraint planning diagram** |
| 39 | 51 | Calcul situationnel | **YES** | **REGRESSION** | **Situation calculus tree diagram** | **Restore situation calculus visualization** |
| 40 | 51 | Axiomes du calcul situationnel | **YES** | **REGRESSION** | **Situation calculus axioms diagram** | **Restore axioms diagram** |
| 41 | 52 | Planification a ordre partiel | **YES** | **REGRESSION** | **Partial order planning diagram** | **Restore POP diagram** |
| 42 | 53 | Decomposition hierarchique | **YES** | **REGRESSION** | **Hierarchical decomposition tree diagram** | **Restore hierarchical decomposition diagram** |
| 43 | 54 | Resume planification | No | N/A | Text only slide | No action needed |
| 44 | - | Representation de Connaissances | N/A | N/A | Extra Slidev slide | No action needed |
| 45 | 57 | Ontologies | **YES** | **REGRESSION** | **Ontology tree/hierarchy diagram** | **Restore ontology hierarchy diagram** |
| 46 | 58 | Web semantique | **YES** | **REGRESSION** | **Semantic web stack diagram** | **Restore semantic web layer diagram** |
| 47 | 59 | Systemes de raisonnement | **YES** | **REGRESSION** | **Reasoning system architecture diagram** | **Restore reasoning system diagram** |
| 48 | 60 | Systemes a maintenance de verite | **YES** | **REGRESSION** | **Truth maintenance system diagram** | **Restore TMS diagram** |
| 49 | 61 | Smart Contracts | No | N/A | Text only slide | No action needed |
| 50 | 62 | Resume representation des connaissances | No | N/A | Text only slide | No action needed |
| 51 | - | TP | N/A | N/A | Extra Slidev slide | No action needed |
| 52 | 65 | Projets de groupe | No | N/A | Text only slide | No action needed |
| 53 | 66 | Merci | No | N/A | Text only slide | No action needed |

---

## Summary

### Critical Image Regressions (23 slides with lost diagrams)

**High Priority - Essential Pedagogical Visualizations:**

1. **PPTX #4 → Slidev #4,5** - KB-Agent Architecture
   - Lost: Tell/Ask flow diagram showing knowledge base architecture
   - Impact: Students cannot visualize the KB-Agent function components

2. **PPTX #12 → Slidev #13** - Inference Rules
   - Lost: Visual representation of Modus Ponens, And-Elimination, etc.
   - Impact: Hard to understand logical inference patterns

3. **PPTX #14 → Slidev #15** - Forward/Backward Chaining
   - Lost: Flowchart diagrams for both chaining algorithms
   - Impact: Critical for understanding inference directionality

4. **PPTX #15 → Slidev #14** - Resolution
   - Lost: Resolution proof procedure diagram
   - Impact: Resolution is a core algorithm requiring visual understanding

5. **PPTX #35 → Slidev #24,25,26,27** - FOL Inference Procedures (SPLIT)
   - Lost: Unification algorithm, FOL forward/backward chaining, FOL resolution diagrams
   - Impact: 4 critical FOL algorithms lost in one slide

**Medium Priority - Planning Visualizations:**

6. **PPTX #45 → Slidev #29,30** - Planning (SPLIT)
   - Lost: Planning problem definition visualization
   - Impact: Hard to grasp planning concepts without visual

7. **PPTX #46 → Slidev #31** - PDDL Action Schema
   - Lost: PDDL action schema diagram
   - Impact: PDDL syntax is abstract, needs visual representation

8. **PPTX #47 → Slidev #33** - Planning Approaches
   - Lost: Comparison diagram of different planning approaches
   - Impact: Students lose comparative understanding

9. **PPTX #48 → Slidev #34** - State Space Exploration
   - Lost: State space search tree diagram
   - Impact: Search trees are fundamental to planning

10. **PPTX #49 → Slidev #36** - Planning Graphs (GraphPlan)
    - Lost: GraphPlan planning graph visualization
    - Impact: Planning graphs are inherently visual structures

11. **PPTX #50 → Slidev #38** - Constraint Planning
    - Lost: Constraint-based planning diagram
    - Impact: Constraints need visual representation

12. **PPTX #51 → Slidev #39,40** - Situation Calculus (SPLIT)
    - Lost: Situation calculus tree diagram and axioms diagram
    - Impact: Temporal reasoning is abstract, needs visual aid

13. **PPTX #52 → Slidev #41** - Partial Order Planning
    - Lost: POP diagram showing ordering constraints
    - Impact: Partial orders are inherently visual

14. **PPTX #53 → Slidev #42** - Hierarchical Decomposition
    - Lost: Hierarchical decomposition tree diagram
    - Impact: Hierarchies require tree visualization

**Lower Priority - Knowledge Representation:**

15. **PPTX #57 → Slidev #45** - Ontologies
    - Lost: Ontology tree/hierarchy diagram
    - Impact: Ontologies are taxonomic structures

16. **PPTX #58 → Slidev #46** - Semantic Web
    - Lost: Semantic web stack/layer diagram
    - Impact: Architecture visualization important

17. **PPTX #59 → Slidev #47** - Reasoning Systems
    - Lost: Reasoning system architecture diagram
    - Impact: System architecture needs visualization

18. **PPTX #60 → Slidev #48** - Truth Maintenance Systems
    - Lost: TMS diagram showing dependency-directed backtracking
    - Impact: TMS is complex, needs visual explanation

### Statistics

- **Total PPTX slides**: 66
- **Total Slidev slides**: 53
- **Slides with diagrams in PPTX**: 18 (27%)
- **Image regressions identified**: 23 (18 unique PPTX slides, some split)
- **Regressions per category**:
  - Knowledge-based agents: 1
  - Propositional logic: 3
  - First-order logic: 4
  - Planning: 9
  - Knowledge representation: 4

### Partial Success

- **PPTX #5 → Slidev #6** - Wumpus World
  - Status: PARTIAL - Image exists in Slidev (img_003.png)
  - Action: Verify that the Wumpus grid visualization matches PPTX version

### Missing PPTX Slides (35 slides)

The following PPTX slides have NO equivalent in Slidev (mostly "Questions?" and "Sommaire" slides):
- PPTX #7,8,9,11,13,16,17,18,19,21,22,25,27,28,29,30,31,32,36,37,38,39,40,41,42,43,55,56,63,64

These are primarily:
- Section summaries ("Résumé...")
- Section transitions ("Sommaire")
- Q&A slides ("Questions?")
- Rhetorical analysis block (PPTX #28-32)

### Extra Slidev Slides (16 slides)

Slidev has additional slides not in PPTX (mostly explanatory expansions):
- Slidev #9,10,11,12,16,22,24,25,26,27,28,32,35,37,44,51

These provide:
- Detailed syntax/semantics explanations
- Algorithm expansions (GraphPlan, heuristics)
- Practical examples (PDDL transport)

### Recommendations

1. **Immediate Action Required**: Restore the 23 image regressions identified above
2. **Priority Order**: 
   - First: KB-Agent architecture, Inference rules, Forward/Backward chaining, Resolution
   - Second: FOL inference procedures (unification, chaining, resolution)
   - Third: Planning visualizations (PDDL, state space, planning graphs)
   - Fourth: Knowledge representation diagrams (ontologies, semantic web)
3. **Verification**: Check that Wumpus world image (img_003.png) matches PPTX #5
4. **Image Format**: Use overlay layout for all restored images (per issue #221)
5. **Testing**: After restoration, verify each slide with `?clicks=99` to ensure no overflow

### Next Steps

1. Extract diagrams from PPTX reference images
2. Create clean versions of each diagram
3. Add to Slidev slides using `layout: image-overlay`
4. Test rendering with Slidev server at http://localhost:3030
5. Verify each restored slide with `?clicks=99` for complete content visibility
|----------|------------|--------------|-----------------|-------------|------------------|---------------|
