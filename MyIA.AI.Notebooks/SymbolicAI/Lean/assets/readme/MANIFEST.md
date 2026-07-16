# Manifeste des figures — SymbolicAI/Lean

Provenance de chaque figure (convention d'indexation **all-cells** du module `extract_readme_figures.py` : `cellule` = indice de cellule dans le notebook, `output` = indice de sortie de cette cellule). Sources vérifiées sur `origin/main`.

| Figure | Fichier | Dimensions | Poids | Source (notebook · cellule · output) | Sujet |
|--------|---------|------------|-------|--------------------------------------|-------|
| Performance LLM | `lean-llm-examples.png` | 1389×985 | 99 Ko | `Lean-7b-Examples.ipynb` · cellule 24 · output 0 | Analyse de performance de la génération de preuves LLM : succès, itérations, temps, tokens sur 10 théorèmes (§7.5) |
| TorchLean (IBP) | `lean-torchlean.png` | 1188×985 | 57 Ko | `Lean-11-TorchLean-Python.ipynb` · cellule 23 · output 1 | Propagation IBP pour la vérification de réseaux de neurones (§3.6) |
| Conway Game of Life | `lean-conway-gol.png` | 884×499 | 20 Ko | `Lean-16b-Conway-Game-of-Life-Lean.ipynb` · cellule 24 · output 1 | Self-replicator Gemini (Andrew Wade, 2010) — Acte III |
| Trois premiers nœuds | `lean-knot-conway.png` | 1604×515 | 62 Ko | `Lean-17-Knots-a-Conway-and-Proofs.ipynb` · cellule 2 · output 0 | Les trois premiers nœuds par nombre de croisements : unknot, trèfle (3₁), nœud de huit (4₁) (§1) |
| Conway ↔ K-T (mutants) | `lean-knot-piccirillo.png` | 1389×617 | 112 Ko | `Lean-17-Knots-a-Conway-and-Proofs.ipynb` · cellule 8 · output 0 | Mutants Conway (11n34) ↔ Kinoshita-Terasaka (11n42) : même Alexander (= 1), sliceness lisse différente (§2) |
| Polynômes d'Alexander | `lean-knot-invariants.png` | 1590×425 | 48 Ko | `Lean-17-Knots-b-Invariants-Companion.ipynb` · cellule 11 · output 0 | Polynômes d'Alexander Δ(t) : trèfle, nœud de huit, et Conway/K-T trivial (= 1) (§5) |

**Total** : 6 figures, 402 Ko. **Politique** (#5654) : ≤200 Ko/fichier, downscale ≤1200 px max. Diagrammes et line-art (nœuds, automates Cellulaire, réseaux de neurones) → **PNG lossless natif** (netteté ; tous sous le seuil sans downscale, max 112 Ko). Arc : performance de la génération de preuves LLM → vérification formelle de réseaux de neurones → automate de Conway (Game of Life) → théorie des nœuds (trois premiers nœuds, mutants Conway 11n34 / Kinoshita-Terasaka 11n42, polynôme d'Alexander trivial).
