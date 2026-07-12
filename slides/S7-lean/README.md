# S7-lean — Deck Slidev Lean 4

Deck de presentation pour la serie de 14 notebooks **Lean 4** (`SymbolicAI/Lean/`).

## Contenu

20 slides couvrant :
- Fondations : types dependants, Curry-Howard, propositions
- Logique formelle : quantificateurs, arithmetique, tactiques
- Mathlib4 : ring, linarith, omega, norm_num
- Integration LLM : LeanCopilot, AlphaProof
- Agents autonomes : APOLLO, Semantic Kernel multi-agents
- LeanDojo : extraction de donnees, benchmark, RL
- Verification de reseaux de neurones : IBP, CROWN, TorchLean
- Theoreme de sensibilite (Huang 2019)

## Utilisation

```bash
# Depuis le dossier slides/
./node_modules/.bin/slidev S7-lean/slides.md --port 3047 --no-open
```

## Notebooks correspondants

`MyIA.AI.Notebooks/SymbolicAI/Lean/` — 14 notebooks, ~11h

### Partie 1 : Fondations

| Notebook | Theme | Duree |
|----------|-------|-------|
| Lean-1-Setup | Installation elan, kernel Jupyter | 15 min |
| Lean-2-Dependent-Types | CIC, types dependants | 35 min |
| Lean-3-Propositions-Proofs | Prop, Curry-Howard | 45 min |
| Lean-4-Quantifiers | ∀, ∃, arithmetique Nat | 40 min |
| Lean-5-Tactics | Mode tactique | 50 min |

### Partie 2 : Integration IA

| Notebook | Theme | Duree |
|----------|-------|-------|
| Lean-6-Mathlib-Essentials | Mathlib4, tactiques avancees | 45 min |
| Lean-7-LLM-Integration | LeanCopilot, AlphaProof | 50 min |
| Lean-7b-Examples | Exemples progressifs, benchmarks | 40 min |
| Lean-8-Agentic-Proving | Agents autonomes, APOLLO | 55 min |
| Lean-9-SK-Multi-Agents | Semantic Kernel multi-agents | 45 min |
| Lean-10-LeanDojo | LeanDojo, tracing, RL | 45 min |
| Lean-11-TorchLean | Verification NNs (IBP, CROWN) | 90-120 min |
| Lean-12-Sensitivity-Theorem | Theoreme de sensibilite | 60 min |

## References

- Epic #1240 (refonte slides IA 101)
- Issue #1242 (creation decks S6-tweety + S7-lean)
- `GameTheory/social_choice_lean/` : Arrow/Sen/Voting en Lean
