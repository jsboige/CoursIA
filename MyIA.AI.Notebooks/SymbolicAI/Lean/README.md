# Lean - Solveur mathématique et Vérification Formelle

<!-- CATALOG-STATUS
series: SymbolicAI-Lean
pedagogical_count: 28
breakdown: Lean=28
maturity: PRODUCTION=23, BETA=5
-->

[← SemanticWeb](../SemanticWeb/README.md) | [↑ SymbolicAI](../README.md) | [Planners →](../Planners/README.md)

Cette série introduit **Lean 4**, un assistant de preuves et langage de programmation fonctionnel basé sur la théorie des types dépendants. Le fil rouge va des fondations (types dépendants, mode tactique, Mathlib) vers l'état de l'art : assistance aux preuves par LLM et vérification formelle de réseaux de neurones, ports de théorèmes phares (théorème de Kochen-Specker / 18 vecteurs Cabello ; théorème du libre arbitre de Conway-Kochen ; finitude des dérivées symboliques de Brzozowski), théorie des nœuds (mouvements de Reidemeister, tricolorabilite de Fox, noeud de Conway et preuve de Piccirillo), et hommages aux mathématiciens (Grothendieck et le langage grothendieckien dans Mathlib 4 ; John Conway, l'homme et l'oeuvre).

## Navigation

Tous les notebooks incluent une **barre de navigation** en haut et en bas permettant de passer facilement d'un notebook a l'autre. Chaque notebook contient également un **Plan** avec des liens ancres vers chaque section.

## Modes d'exécution suggeres

| Mode | Notebooks | Temps | Description |
|------|-----------|-------|-------------|
| **Fondations** | 1-5 | ~3h | Base théorique complète (types, logique, tactiques) |
| **Avec Mathlib** | 1-6 | ~3h45 | Ajoute les tactiques Mathlib |
| **Intégration IA** | 1-7, 7b | ~5h | Ajoute LLMs, exemples et benchmarks |
| **Complet** | 1-12 | ~11h | Toutes les fonctionnalites incluant LeanDojo et théorème de sensibilite |
| **Avec Pilier 1.B** | 1-12, 13 | ~12h | Inclut le port Kochen-Specker (Cabello 18-vecteurs) - contextuality quantique |
| **Avec hommages** | 1-12, 13, 15, 16a, 16b, 16c, 16d, 16e, 16f | ~17h20 | Ajoute Lean-15 (Grothendieck), Lean-16a (Conway, l'homme et l'oeuvre), Lean-16b (Conway, Game of Life), Lean-16d (Conway, Game of Life sur kernel Lean natif), Lean-16e (Conway, FRACTRAN sur kernel Lean natif) et Lean-16f (Conway, théorème du libre arbitre - adosse a Lean-13) |
| **Avec théorie des nœuds** | 1-12, 13, 15, 16a-c, 16f, 17a, 17b | ~17h30 | Ajoute Lean-17a (Conway, les nœuds et la preuve de Piccirillo) et Lean-17b (invariants : PD-codes, tricolorabilite de Fox, mouvements de Reidemeister) - companion `knot_lean`, Epic #2874 |

## Structure

### Partie 1 : Fondations (basé sur PDF de référence)

| # | Notebook | Contenu | Durée |
|---|----------|---------|-------|
| 1 | [Lean-1-Setup](Lean-1-Setup.ipynb) | Installation elan, kernel Jupyter, vérification | 15 min |
| 2 | [Lean-2-Dependent-Types](Lean-2-Dependent-Types.ipynb) | Calcul des Constructions, types, polymorphisme | 35 min |
| 3 | [Lean-3-Propositions-Proofs](Lean-3-Propositions-Proofs.ipynb) | Prop, connecteurs, Curry-Howard, preuves par termes | 45 min |
| 4 | [Lean-4-Quantifiers](Lean-4-Quantifiers.ipynb) | forall, exists, egalite, arithmetique Nat | 40 min |
| 5 | [Lean-5-Tactics](Lean-5-Tactics.ipynb) | Mode tactique, apply/exact/intro/rw/simp | 50 min |

### Partie 2 : État de l'art et intégration IA

| # | Notebook | Contenu | Durée |
|---|----------|---------|-------|
| 6 | [Lean-6-Mathlib-Essentials](Lean-6-Mathlib-Essentials.ipynb) | Mathlib4, tactiques ring/linarith/omega, recherche | 45 min |
| 7 | [Lean-7-LLM-Intégration](Lean-7-LLM-Integration.ipynb) | LeanCopilot, AlphaProof, patterns LLM-Lean | 50 min |
| 7b | [Lean-7b-Examples](Lean-7b-Examples.ipynb) | Exemples progressifs, benchmarks, cas pratiques | 40 min |
| 8 | [Lean-8-Agentic-Proving](Lean-8-Agentic-Proving.ipynb) | Agents autonomes, APOLLO, problèmes Erdos | 55 min |
| 9 | [Lean-9-SK-Multi-Agents](Lean-9-SK-Multi-Agents.ipynb) | Agent Framework (Microsoft), orchestration multi-agents | 45 min |
| 10 | [Lean-10-LeanDojo](Lean-10-LeanDojo.ipynb) | LeanDojo: tracing, theorems, Dojo interactif | 45 min |
| 11 | [Lean-11-TorchLean](Lean-11-TorchLean.ipynb) | TorchLean: réseaux de neurones vérifies, IBP, CROWN | 1h30-2h |
| 11a | [Lean-11-TorchLean-Python](Lean-11-TorchLean-Python.ipynb) | Implémentation Python des algorithmes de vérification (IBP, CROWN) | 1h30-2h |
| 12 | [Lean-12-Sensitivity-Theorem](Lean-12-Sensitivity-Theorem.ipynb) | théorème de sensibilite (Huang 2019), hypercube, signing matrix, port Lean 4 | 60 min |
| 12b | [Lean-12b-Lean-Sensitivity-Theorem](Lean-12b-Lean-Sensitivity-Theorem.ipynb) | Companion **natif** (kernel Lean) : preuve formelle 0-sorry de Huang dans le lake `sensitivity_lean`, `#check` + `#print axioms` rendus in-kernel (UNLOCK c.127, jonction Mathlib #2611) | 45 min |

### Partie 3 : théorèmes phares (ports complets)

| # | Notebook | Contenu | Durée |
|---|----------|---------|-------|
| 13 | [Lean-13-Kochen-Specker](Lean-13-Kochen-Specker.ipynb) | théorème de Kochen-Specker (1967), preuve Cabello 18 vecteurs, parite, contextuality quantique - Pilier 1.B Epic #1651 | 60 min |
| 14 | [Lean-14-Finiteness-Derivatives](Lean-14-Finiteness-Derivatives.ipynb) | Dérivées symboliques de Brzozowski : la finitude des dérivées qui garantit le matching linéaire (langages rationnels, automates) | 25 min |

### Partie 4 : Hommages mathématiciens

| # | Notebook | Contenu | Durée |
|---|----------|---------|-------|
| 15 | [Lean-15-Grothendieck-Tribute](Lean-15-Grothendieck-Tribute.ipynb) | Langage grothendieckien dans Mathlib 4 : categories/foncteurs, cribles et topologies de Grothendieck, faisceaux, schémas, site de Zariski, morphismes etales/lisses - Epic #1646 | 45 min |
| 15b | [Lean-15b-Lean-Grothendieck](Lean-15b-Lean-Grothendieck.ipynb) | Atelier pratique Grothendieck : cribles, topologies et faisceaux en exercices (compagnon `grothendieck_lean`, fait suite a Lean-15) - Epic #1646 | 50 min |
| 16a | [Lean-16a-Conway-Man-and-Work](Lean-16a-Conway-Man-and-Work.ipynb) | Conway, l'homme et l'oeuvre : biographie et style singulier (le jeu comme méthode) ; panorama des grands résultats (nombres surreels, groupes de Conway & Monstrous Moonshine, réseau de Leech, polynome de Conway, Doomsday, Look-and-Say, FRACTRAN, problème de l'Ange, Sprouts, théorème du libre arbitre) ; premières noix crackees exécutées depuis conway_lean (Doomsday, Look-and-Say, Nim, Angel, Life - 0 sorry) - Epic #1647 / #2154 | 50 min |
| 16b | [Lean-16b-Conway-Game-of-Life-Lean](Lean-16b-Conway-Game-of-Life-Lean.ipynb) | Hommage a John Conway : Game of Life as Computation, Doomsday, FRACTRAN, Look-and-Say, Nim, Angel - Epic #1647 | 60 min |
| 16c | [Lean-16c-Conway-Game-of-Life-Golly](Lean-16c-Conway-Game-of-Life-Golly.ipynb) | Game of Life : les 3 piliers en images (compagnon Golly, intégration CLI `bgolly` pour simulation certifiee) - Epic #1647 | 45 min |
| 16d | [Lean-16d-Conway-Game-of-Life-Lean-Native](Lean-16d-Conway-Game-of-Life-Lean-Native.ipynb) | Game of Life sur **kernel Lean natif** (`lean4-wsl`) : grille, règle B3/S23, moteur `step`/`evolve`, motifs (bloc, clignoteur, planeur) et faits certifiés par `decide`/`native_decide`, sans axiome `sorry` - Epic #1647 / #3294 | 40 min |
| 16e | [Lean-16e-Conway-FRACTRAN-Lean-Native](Lean-16e-Conway-FRACTRAN-Lean-Native.ipynb) | FRACTRAN sur **kernel Lean natif** (`lean4-wsl`) : type `Frac` (preuve `den > 0`), moteur `fracMulNat`/`fractranStep`/`fractranRun`, programmes (doubler, diviser) et le générateur de nombres premiers de Conway (14 fractions), faits certifiés par `decide` sans axiome `sorry` - Epic #1647 / #3294 | 40 min |
| 16f | [Lean-16f-Conway-Free-Will-Theorem](Lean-16f-Conway-Free-Will-Theorem.ipynb) | théorème du libre arbitre (Conway-Kochen) : les trois axiomes SPIN/TWIN/MIN en profondeur, argument en deux temps (1 particule via Kochen-Specker, puis 2 particules via TWIN), ce que le théorème dit et NE dit PAS, port formel adosse a `FreeWillTheorem.lean` (chaine de reduction `free_will_theorem -> fwt_single_particle -> kochen_specker`, 0 sorry), registre d'extensibilite - Epic #2162 / #2156 | 40 min |

### Partie 5 : Théorie des noeuds

| # | Notebook | Contenu | Durée |
|---|----------|---------|-------|
| 17a | [Lean-17-Knots-a-Conway-and-Proofs](Lean-17-Knots-a-Conway-and-Proofs.ipynb) | Conway, les nœuds et la preuve de Piccirillo : le noeud de Conway (11n34), slice-genre et nombre de denouement, contexte de la preuve (Piccirillo 2020, le noeud de Conway n'est pas slice) - hommage narratif, Epic #2874 | 40 min |
| 17b | [Lean-17-Knots-b-Invariants-Companion](Lean-17-Knots-b-Invariants-Companion.ipynb) | Invariants de nœuds : PD-codes, mouvements de Reidemeister, tricolorabilite de Fox, diagrammes bien formes - companion `knot_lean` (Epic #2874, transfer forward #3000 sorry-free + backward #3124 partiel) | 60 min |

### Partie 6 : Recherche pondérée et optimalité (A*)

| # | Notebook | Contenu | Durée |
|---|----------|---------|-------|
| 18 | [Lean-18-Search-AStar-Optimality](Lean-18-Search-AStar-Optimality.ipynb) | Optimalité de A* sous heuristique admissible : graphe pondéré ℝ≥0 et coût additif `pathCost`, prédicats `Admissible`/`Consistent`, théorème phare `admissible_implies_optimal` (borne en f), téléscopage `consistent_implies_path_bound` + monotonie de f - companion `astar_lean` (lake `Search/`, 0 sorry, registre #3801 prong B) | 35 min |

**Durée totale** : ~18h05

## Acquis d'apprentissage

A l'issue de la série, vous saurez :

- **Modéliser** un raisonnement mathématique dans le Calcul des Constructions : types dépendants, univers, propositions comme types (Curry-Howard). Notebooks 2-3 ancrent ces objets sur des exemples concrets (Vector, propositions logiques) plutôt que sur de l'abstraction nue.
- **Prouver** un théorème en mode tactique avec les briques Mathlib : `intro`/`apply`/`exact`/`rfl` pour la structure, `ring`/`linarith`/`omega`/`simp` pour l'arithmetique et la simplification, `induction`/`cases`/`rcases` pour l'analyse de cas. Notebooks 4-6.
- **Intégrer un LLM** au workflow de preuve : patterns LeanCopilot et AlphaProof (n-best, MCTS), prompts goal-aware, comparaison ND-search vs CoT, agents APOLLO/Erdos — fiables surtout sur les preuves courtes, limites persistantes sur les preuves longues et la couverture Mathlib (usage en assistant, pas en oracle). Notebooks 7-9.
- **Tracer et explorer** une basé de preuves a grande echelle : LeanDojo (parsing AST, theorem extraction, interaction Dojo), réseaux de neurones vérifies via IBP/CROWN (TorchLean). Notebooks 10-11.
- **Porter** un théorème de recherche en Lean 4 : théorème de sensibilite (Huang 2019, hypercube et signing matrix), théorème de Kochen-Specker (Cabello 18 vecteurs, argument de parite, contextuality quantique). Notebooks 12, 13.
- **Lire le langage grothendieckien** dans Mathlib 4 : categories et foncteurs, cribles et topologies de Grothendieck, faisceaux, schémas et sites, morphismes etales/lisses — comme entree vers la geometrie algebrique formalisee. Notebook 15.
- **Situer l'oeuvre de Conway** dans sa largeur : des nombres surreels au Monstrous Moonshine, du réseau de Leech au théorème du libre arbitre, en executant les premières noix formalisees (Doomsday, Look-and-Say, Nim, Angel, Life) directement depuis le projet conway_lean (0 sorry). Notebook 16a.
- **Explorer les noix de Conway** en Lean 4 : Game of Life as Computation, Doomsday, FRACTRAN, Look-and-Say, Nim, Angel — port formel de résultats combinatoires iconiques. Notebooks 16a-16e.
- **Comprendre le théorème du libre arbitre** (Conway-Kochen) : les axiomes SPIN/TWIN/MIN, l'argument en deux temps qui reduit le cas a deux particules au théorème de Kochen-Specker (Notebook 13), et la lecture honnete de sa portee (ce qu'il dit et ne dit pas) — adosse a `FreeWillTheorem.lean` (0 sorry). Notebook 16f.
- **Formaliser les invariants de nœuds** : PD-codes, mouvements de Reidemeister et tricolorabilite de Fox, en s'appuyant sur le companion `knot_lean` (transfert de tricolorabilite le long d'un twist R1 connecte, preuve forward sorry-free + backward partielle). Notebooks 17a, 17b.

Pour l'état formel detaille des modules support (preuves resolues vs `sorry` résiduels), voir [LEAN_INVENTORY.md](../../GameTheory/LEAN_INVENTORY.md), le [README du projet conway_lean](conway_lean/README.md), et le [README du projet grothendieck_lean](grothendieck_lean/README.md).

## Statut de maturite

| # | Notebook | Cellules | Exercices | Solutions | Statut |
|---|----------|----------|-----------|-----------|--------|
| 1 | Setup | ~17 | - | - | **COMPLET** |
| 2 | Dependent-Types | ~50 | 3 | 3 | **COMPLET** |
| 3 | Propositions-Proofs | ~50 | 3 | 3 | **COMPLET** |
| 4 | Quantifiers | ~46 | 3 | 3 | **COMPLET** |
| 5 | Tactics | ~70 | 3 | 3 | **COMPLET** |
| 6 | Mathlib-Essentials | ~45 | 3 | 3 | **COMPLET** |
| 7 | LLM-Intégration | ~50 | 2 | 2 | **COMPLET** |
| 7b | Examples | ~40 | 3 | 3 | **COMPLET** |
| 8 | Agentic-Proving | ~70 | 2 | 2 | **COMPLET** |
| 9 | SK-Multi-Agents | ~50 | 2 | 2 | **COMPLET** |
| 10 | LeanDojo | ~100 | 2 | 0 | **COMPLET** |
| 11 | TorchLean | ~40 | 3 | Oui | **COMPLET** |
| 11a | TorchLean Python | ~45 | 3 | Oui | **COMPLET** |
| 12 | Sensitivity-Theorem | ~31 | 4 | Non | **NOUVEAU** |
| 13 | Kochen-Specker | ~25 | 1 | 0 | **NOUVEAU** |
| 14 | Finiteness-Derivatives | ~12 | 1 | - | **NOUVEAU** |
| 15 | Grothendieck-Tribute | ~23 | 0 | - | **NOUVEAU** (hommage) |
| 15b | Lean-Grothendieck (atelier) | ~40 | 4 | Oui | **NOUVEAU** |
| 16a | Conway-Man-and-Work | ~39 | 3 | 0 | **NOUVEAU** (hommage) |
| 16b | Conway-Game-of-Life-Lean | ~26 | 0 | - | **NOUVEAU** (hommage) |
| 16c | Conway-Game-of-Life-Golly | ~47 | 5 | - | **NOUVEAU** (hommage) |
| 16f | Conway-Free-Will-Theorem | ~28 | 3 | 0 | **NOUVEAU** (hommage) |
| 17a | Knots-a-Conway-and-Proofs | ~13 | 0 | - | **NOUVEAU** (hommage) |
| 17b | Knots-b-Invariants-Companion | ~19 | 3 | - | **NOUVEAU** |

Tous les notebooks incluent :
- Navigation header/footer avec liens vers notebooks précédent/suivant
- Plan de ce Notebook avec liens ancres (notebooks 2-4)
- Tableaux recapitulatifs en fin de section
- Exercices avec solutions complètes

## Quick Start

```bash
# 1. Installer elan (gestionnaire Lean)
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
elan default leanprover/lean4:stable

# 2. vérifier l'installation
lean --version    # Lean 4.x.x
elan show         # toolchain active

# 3. Ouvrir le premier notebook (WSL requis)
wsl -d Ubuntu -- bash -c "jupyter notebook Lean-1-Setup.ipynb"
```

Pour les notebooks 7-10 (LLM), configurer `.env` avec `OPENAI_API_KEY`. Pour le prover daemon, voir section "Prover daemon".

---

## Prerequisites

- Connaissances de basé en logique mathématique
- Familiarite avec la programmation fonctionnelle (utile mais non obligatoire)
- Pour notebooks 7-8 : compte OpenAI/Anthropic pour APIs LLM (optionnel)

## Installation

### 1. Installer elan (gestionnaire de versions Lean)

```bash
# Linux/macOS
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# Windows (PowerShell)
Invoke-WebRequest -Uri https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | Invoke-Expression
```

### 2. Installer Lean 4

```bash
elan default leanprover/lean4:stable
```

### 3. Installer le kernel Jupyter (optionnel)

```bash
# Creer un environnement conda
conda create -n lean4-jupyter python=3.10
conda activate lean4-jupyter

# Installer lean4_jupyter
pip install lean4_jupyter

# vérifier l'installation
jupyter kernelspec list
```

### 4. Configuration API pour notebooks LLM (optionnel)

```bash
cd MyIA.AI.Notebooks/SymbolicAI/Lean
cp .env.example .env
# Editer .env et ajouter OPENAI_API_KEY ou ANTHROPIC_API_KEY
```

## Ressources externes

### Documentation Lean
- [Theorem Proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/)
- [Lean 4 Documentation](https://leanprover.github.io/lean4/doc/)
- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)
- [lean4_jupyter GitHub](https://github.com/utensil/lean4_jupyter)

### Mathlib
- [Mathlib4 Documentation](https://leanprover-community.github.io/mathlib4_docs/)
- [Mathlib4 GitHub](https://github.com/leanprover-community/mathlib4)
- [Loogle - Recherche syntaxique](https://loogle.lean-lang.org/)
- [Moogle - Recherche semantique](https://www.moogle.ai/)

### LLM et Preuves Automatiques
- [LeanCopilot](https://github.com/lean-dojo/LeanCopilot)
- [LeanDojo](https://leandojo.readthedocs.io/) - ML/LLM theorem proving
- [AlphaProof Paper Analysis](https://www.julian.ac/blog/2025/11/13/alphaproof-paper/)
- [APOLLO System](https://arxiv.org/html/2505.05758v1)
- [Erdos Problems Formalization](https://xenaproject.wordpress.com/2025/12/05/formalization-of-erdos-problems/)

### LeanDojo

- [LeanDojo Documentation](https://leandojo.readthedocs.io/)
- [LeanDojo Paper](https://arxiv.org/abs/2306.15626) (NeurIPS 2023)
- [lean4-example Repository](https://github.com/yangky11/lean4-example)

### TorchLean

- [TorchLean Documentation](https://leandojo.org/torchlean.html)
- [TorchLean GitHub](https://github.com/lean-dojo/TorchLean)
- [Papers: IBP, CROWN, LiRPA](https://github.com/lean-dojo/TorchLean#references)

### Références académiques

| Référence | Couverture |
|-----------|------------|
| de Moura & Ullrich, "The Lean 4 Theorem Prover and Programming Language" (2021) | système Lean 4 |
| The Mathlib Community, "The Mathlib Library" (2020), arXiv:1910.09436 | Mathlib4 |
| Avigad, "Mathematics and Programming" (2024) — *Mathematics in Lean* | Fondations notebooks 1-5 |
| Jiang et al., "LeanDojo: Theorem Proving with Retrieval-Augmented Language Models" (NeurIPS 2023) | LeanDojo, notebooks 10 |
| First et al., "AlphaProof: Formal Math Reasoning" (DeepMind, 2024) | Notebook 7 |
| Song et al., "Towards Counting Forall: Neural Network Vérification via IBP, CROWN, and LiRPA" | TorchLean, notebooks 11 |
| Geanakoplos, "Three Brief Proofs of Arrow's Impossibility Theorem" (2005) | Cross-séries GameTheory |
| Sen, "Collective Choice and Social Welfare" (1970) | Cross-séries GameTheory |

## Document source

- Notebooks 1-5 bases sur : `D:\Dropbox\IA101\TPs\TP - Z3 - Tweety - Lean.pdf` (Section VI)
- Notebooks 6-8 bases sur : Recherches état de l'art 2025-2026

## Validation

```bash
# vérifier la structure des notebooks
python scripts/verify_notebooks.py MyIA.AI.Notebooks/SymbolicAI/Lean --quick

# vérifier l'installation Lean
lean --version
elan show
```

## Percees recentes (2024-2026)

| système | Accomplissement |
|---------|-----------------|
| **AlphaProof** (DeepMind) | Medaille d'argent IMO 2024 |
| **Harmonic Aristotle** | Resolution Erdos #124 variant (~30 ans ouvert) en 6h |
| **DeepSeek-Prover** | Resolution de problèmes Erdos 379, 987, 730, 198 |
| **Mathlib4** v4.27.0-rc1 | 4M+ lignes, utilise par Terry Tao |

## Notes techniques

- **Lean 4** (pas Lean 3) - syntaxe moderne
- Preuves constructives + logique classique (via `open Classical`)
- Progression : termes -> tactiques -> Mathlib -> LLMs -> agents
- Kernel Jupyter : lean4_jupyter (recommande)

## Structure des fichiers

```
Lean/
├── Lean-1-Setup.ipynb              # Python kernel - diagnostics
├── Lean-2-Dependent-Types.ipynb    # Lean4 kernel
├── Lean-3-Propositions-Proofs.ipynb
├── Lean-4-Quantifiers.ipynb
├── Lean-5-Tactics.ipynb
├── Lean-6-Mathlib-Essentials.ipynb
├── Lean-7-LLM-Integration.ipynb    # Python kernel - APIs LLM
├── Lean-7b-Examples.ipynb          # Python kernel - benchmarks
├── Lean-8-Agentic-Proving.ipynb    # Python kernel - orchestration
├── Lean-9-SK-Multi-Agents.ipynb    # Python kernel - Agent Framework
├── Lean-10-LeanDojo.ipynb          # Python kernel - LeanDojo
├── Lean-11-TorchLean.ipynb         # Lean4 kernel - NN verification
├── Lean-11-TorchLean-Python.ipynb  # Python kernel - Implementation algorithmes
├── Lean-12-Sensitivity-Theorem.ipynb # Python kernel - theoreme de sensibilite (Huang 2019, hypercube, signing matrix)
├── Lean-15-Grothendieck-Tribute.ipynb # Python kernel - hommage Grothendieck (langage grothendieckien Mathlib)
├── Lean-15b-Lean-Grothendieck.ipynb # Python kernel - atelier pratique Grothendieck (compagnon grothendieck_lean)
├── Lean-16a-Conway-Man-and-Work.ipynb # Python kernel - hommage Conway (l'homme et l'oeuvre, noix executees depuis conway_lean)
├── Lean-16b-Conway-Game-of-Life-Lean.ipynb   # Python kernel - hommage Conway (Game of Life as Computation)
├── Lean-16c-Conway-Game-of-Life-Golly.ipynb  # Python kernel - hommage Conway (Game of Life en images, compagnon Golly)
├── Lean-16d-Conway-Game-of-Life-Lean-Native.ipynb  # Lean4 (WSL) kernel - Game of Life natif (grille, B3/S23, decide/native_decide, 0 sorry)
├── Lean-16e-Conway-FRACTRAN-Lean-Native.ipynb      # Lean4 (WSL) kernel - FRACTRAN natif (machine universelle de Conway, générateur de premiers)
├── Lean-13-Kochen-Specker.ipynb    # Lean4 kernel - théorème de Kochen-Specker (Pilier 1.B)
├── Lean-14-Finiteness-Derivatives.ipynb # Python kernel - dérivées symboliques de Brzozowski (finitude, matching linéaire)
├── Lean-16f-Conway-Free-Will-Theorem.ipynb # Python kernel - hommage Conway (théorème du libre arbitre, adosse a FreeWillTheorem.lean)
├── Lean-17-Knots-a-Conway-and-Proofs.ipynb # Python kernel - Conway, les nœuds et la preuve de Piccirillo (noeud de Conway)
├── Lean-17-Knots-b-Invariants-Companion.ipynb # Python kernel - invariants de nœuds (PD-codes, Reidemeister, Fox tricolorability), compagnon knot_lean
├── _run_lean_snippet.sh            # Helper WSL : run Lean snippet avec cache Mathlib
├── lean_runner.py                  # Module Python multi-backend
├── README.md
├── .env.example
├── conway_lean/                    # Conway tribute workspace (0 sorry, Lake build)
├── grothendieck_lean/              # Grothendieck tribute workspace (0 sorry, Lake build)
├── knot_lean/                      # Knot theory workspace (theorie des noeuds, companion Lean-17a/b, sorries residuels documentes, Lake build)
├── agent_tests/                    # Prover daemon (autonomous Lean proof)
│   ├── multi_agent_proof.py        # CLI principal
│   ├── lean_server.py              # Serveur Lean LSP
│   └── prover/                     # Package prover (Microsoft Agent Framework)
│       ├── __init__.py             # Exports: MultiAgentSorryProver, AutonomousProver
│       ├── provers.py              # Multi-agent + Autonomous prover classes
│       ├── workflow.py             # WorkflowBuilder graph (4 agents)
│       ├── agents.py               # Agent factory (Search/Tactic/Critic/Coordinator)
│       ├── tools.py                # Per-agent tools (file ops, compile, tactics)
│       ├── state.py                # ProofState, SorryContext
│       ├── config.py               # Providers (z.ai GLM-5.1, local Qwen), demos
│       ├── instructions.py         # Agent system prompts
│       ├── lean_utils.py           # Sorry extraction, goal state, verification
│       ├── trace.py                # Conversation trace logger
│       └── vérifier.py             # Lean verification backend
├── examples/
│   ├── basic_logic.lean
│   ├── quantifiers.lean
│   ├── tactics_demo.lean
│   ├── mathlib_examples.lean
│   └── llm_assisted_proof.lean
└── tests/
    ├── test_leandojo_basic.py      # Tests rapides (sans tracing)
    ├── test_leandojo_repos.py      # Tests complets sur repos
    └── test_wsl_lean4_jupyter.py   # Tests backend WSL
```

## Prover daemon

Le package `agent_tests/prover/` implémente un prouveur autonome Lean 4 utilisant le Microsoft Agent Framework.

### Architecture

4 agents spécialisés dans un workflow conditionnel :

1. **SearchAgent** : analyse le contexte, detecte les sorry, identifie les helpers
2. **TacticAgent** : génère des tactiques de preuve (avec outils de compilation)
3. **VerifyExecutor** : vérifie les tactiques via `lake build` (non-LLM)
4. **CriticAgent** : analyse les erreurs et route vers le bon agent

### Usage

```bash
# Prouver un sorry dans un fichier .lean
python agent_tests/multi_agent_proof.py --lean path/to/File.lean --sorry-line 128

# Mode autonome (1 agent avec tous les outils)
python agent_tests/multi_agent_proof.py --lean path/to/File.lean --mode autonomous

# Mode multi-agent (4 agents spécialisés)
python agent_tests/multi_agent_proof.py --lean path/to/File.lean --mode multi

# Batch sur des demos
python agent_tests/multi_agent_proof.py --batch --demos 1,2,3
```

### Configuration

Le fichier `.env` dans `agent_tests/` ou le repertoire parent configure :
- `ZAI_API_KEY` : clé API z.ai pour GLM-5.1 (raisonnement)
- `ZAI_BASE_URL` : endpoint API z.ai
- `LEAN_PROJECT_DIR` : repertoire du projet Lean (pour `lake build`)

## Connections cross-séries

Les concepts de vérification formelle et de preuve assistee par LLM presentes dans cette série se retrouvent dans d'autres séries du curriculum :

### Lean et Théorie des Jeux (GameTheory)

Les notebooks GameTheory side tracks (16b-16f) formalisent en Lean 4 des résultats fondamentaux de théorie des jeux et de choix social :

| résultat | Fichier Lean | Notebook GameTheory | Statut |
|----------|-------------|---------------------|--------|
| théorème d'Arrow (impossibilite) | `social_choice_lean/SocialChoice/Arrow.lean` | 16d | 0 sorry (Geanakoplos 2005) |
| théorème de Sen (liberalisme) | `social_choice_lean/SocialChoice/Sen.lean` | 16e | 0 sorry (bidirectionnel) |
| Valeur de Shapley | `cooperative_games_lean/CooperativeGames/Shapley.lean` | 16b | 1 sorry (en cours) |
| Modèles de vote (Banks, STV) | `social_choice_lean/SocialChoice/Voting.lean` | 16f | 4 sorry (open problems) |
| Gale-Shapley (stable marriage) | `stable_marriage_lean/StableMarriage/GaleShapley.lean` | (pas de notebook dedie) | 2 sorry / 5 théorèmes. `gale_shapley_stable` CLOSED via mmaaz upstream (PR #1181). `man_optimal` + `woman_pessimal` OPEN (Knuth 1976 lattice, Wu-Roth 2018 — ~5-8j Mathlib). |

Le notebook Lean-5 (tactiques) et Lean-6 (Mathlib) sont des prérequis directs pour les side tracks Lean de GameTheory.

### Lean et SmartContracts

La vérification formelle en Lean (type theory, Curry-Howard) est conceptuellement liee a la vérification formelle des smart contracts :

- **SC-14 Formal Verification** : Certora/SMTChecker vs. Lean -- la même idée de preuve mathématique de correction, mais sur des cibles différentes (Solidity vs. mathématiques). Les méthodes différent : SMT solving (automatique, borne) vs. tactiques interactives (expressif, guidable).
- **SC-11 LLM-Assisted Contracts** : Le même paradigme d'assistance LLM que les notebooks Lean-7/8/9, applique a la génération de smart contracts au lieu de preuves.
- **SC-17 E2E Vérifiable Voting** : Les résultats de `Voting.lean` (théorème du median voter, proprietes Banks/STV) eclairent les proprietes théoriques des systemes de vote vérifiable.

### Lean et Théorie des Nœuds

Le notebook Lean-17b (Invariants de Nœuds) est le pendant pédagogique du projet formel `knot_lean/` : les invariants introduits en cours (PD-codes, mouvements de Reidemeister, tricolorabilite de Fox) y sont portes en Lean 4, avec un accent sur le théorème de transfert -- la tricolorabilite est preservee par un twist R1 connecte (Epic #2874).

| résultat | Fichier Lean | Notebook | Statut |
|----------|-------------|----------|--------|
| Transfert forward (R1 connecte préserve la tricolorabilité) | `knot_lean/Knots/Invariant.lean` | 17b | 0 sorry (#3000, sorry-free) |
| Transfert backward (partiel) | `knot_lean/Knots/Invariant.lean` | 17b | Path B shipped (#3003/#4035) : invariant de Fox classique restauré (arc-égalité c₂=c₄) + pont GF(3) `triColorFoxCondition_iff_sum_mod_three` prouvé ; `num` prouvé #3163 ; 2 résiduels §9.1 (fox/col all-distinct) OPEN research-HOLD (BG-prover #2874) |
| Tricolorabilité du noeud de Conway (11n34) | `knot_lean/Knots/Conway.lean` | 17a | scaffolding |
| Théorème d'invariance par Reidemeister (PL topology) | `knot_lean/Knots/Reidemeister.lean` | 17b | 2 sorry (out-of-scope PL) |

Le notebook Lean-17a donne le contexte historique (noeud de Conway, slice-genre, preuve de Piccirillo 2020) qui motive le formalisme. Voir [LEAN_INVENTORY.md](../../GameTheory/LEAN_INVENTORY.md) pour l'état detaille par module.

### Lecture transversale

[La mer qui monte](../../../docs/grothendieckian-lens.md) : une grille de lecture grothendieckienne du depot (changement de representation, certification A/B/C).

## FAQ

### Le kernel lean4-wsl ne demarre pas (timeout après 60s)

**Cause** : le wrapper Python (`~/.lean4-kernel-wrapper.py`) ne trouve pas le venv Lean ou le REPL. vérifier :

```bash
# Dans WSL
test -f ~/.lean4-venv/bin/python3 && echo "venv OK" || echo "venv MISSING"
test -f ~/.elan/bin/repl && echo "repl OK" || echo "repl MISSING"
test -d ~/lean-projects/notebook_context && echo "context OK" || echo "context MISSING"
```

Si un element manque, relancer le setup : `bash MyIA.AI.Notebooks/GameTheory/scripts/setup_wsl_lean4.sh`. Si le kernel.json pointe vers l'ancien wrapper bash (`~/lean4-jupyter-wrapper.sh`), le mettre a jour pour pointer vers `~/.lean4-kernel-wrapper.py` (incident 2026-05-27).

### `lake build` échoue avec des erreurs Mathlib inattendues

**Cause fréquente** : la toolchain Lean locale est désynchronisée du `lean-toolchain` du projet. Lean 4 évolue rapidement et Mathlib suit.

```bash
# vérifier la toolchain requise par le projet
cat lean-toolchain    # ex: leanprover/lean4:v4.x.0

# vérifier la toolchain installee
elan show

# Forcer la reinstallation de la bonne version
elan toolchain install leanprover/lean4:v4.x.0
lake exe cache get    # Telecharger les artifacts Mathlib precompiles
lake build            # Doit passer
```

### Comment installer Lean 4 sous Windows ?

Lean 4 ne tourne pas nativement sous Windows pour les notebooks. La configuration recommandee utilise **WSL 2 (Ubuntu)** :

1. `wsl --install -d Ubuntu` (si pas encore fait)
2. Dans WSL : `curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh`
3. `elan default leanprover/lean4:stable`
4. Installer le kernel Jupyter via `scripts/setup_wsl_lean4.sh` (cree le venv, le wrapper, et enregistre le kernel)

Le notebook [Lean-1-Setup](Lean-1-Setup.ipynb) guide l'installation complète et vérifie chaque composant.

### Comment lire les erreurs `type mismatch` ?

Lean 4 signale `type mismatch` quand le type attendu et le type fourni ne coïncident pas. Les causes les plus frequentes :

- **Universe level** : `Type u` vs `Type` — ajouter `universe u` ou utiliser `Sort _`.
- **Implicit arguments** : Lean ne peut pas inferrer un argument implicite. Essayer `@nom_fonction` pour rendre tous les arguments explicites.
- **Definitional equality** : `Nat` vs `Int`, `List` vs `Array` — utiliser les conversions explicites (`Int.ofNat`, `List.toArray`).
- **Motive mismatch** dans `induction`/`cases` : le motif (motive) ne généralise pas correctement. Essayer `generalizing h` ou restructurer le but avec `have` avant l'induction.

### `sorry` dans un notebook pédagogique, c'est grave ?

**Non** dans les cellules d'exercice (stub pour l'étudiant). **Oui** dans le code de production (preuves formelles). La convention CoursIA :

- Cellules d'exercice : `sorry` = placeholder étudiant, normal et attendu.
- Preuves certifiees (ex: `conway_lean/`, `grothendieck_lean/`, `social_choice_lean/`) : `sorry` = axiome implicite = trou dans la chaine de certification. Le compteur `grep -c sorry` est suivi par les agents du depot.

Voir [LEAN_INVENTORY.md](../../GameTheory/LEAN_INVENTORY.md) pour l'état detaille des preuves par module.

### Quelle est la différence entre Lean-17a et Lean-17b ?

Les deux notebooks couvrent la théorie des nœuds sous des angles complementaires :

- **Lean-17a (Conway, les nœuds et la preuve de Piccirillo)** : hommage narratif. Le contexte mathématique et historique -- le noeud de Conway (11n34), le slice-genre, le nombre de denouement, et la preuve de Piccirillo (2020) que le noeud de Conway n'est pas slice. Aucun exercice : c'est une lecture.
- **Lean-17b (Invariants de Nœuds)** : atelier pratique et companion du projet formel `knot_lean/`. On y manipule les PD-codes, les mouvements de Reidemeister et la tricolorabilite de Fox, avec des exercices de calcul et de vérification d'invariants.

Lean-17a donne le *pourquoi* (motivation historique) ; Lean-17b donne le *comment* (calcul des invariants, port formel).

## Conclusion / Prochaines étapes

### Ce que vous avez appris

Lean n'est pas un langage de programmation de plus : c'est le point où **le code devient une preuve**. En parcourant cette série, vous avez traversé le spectre de la vérification formelle :

- **Les fondations** (Lean-1 Setup à Lean-6) : installer l'outil, manipuler les types dépendants, comprendre l'isomorphisme de Curry-Howard — un programme *est* une preuve, un type *est* une proposition.
- **Prouver en pratique** (Lean-7 à Lean-12) : tactiques, lemmes, induction, l'art de *réduire* un énoncé jusqu'à ce que `rfl` ou `decide` le closent. Vous avez vu qu'une preuve formelle n'est pas une invention — c'est un dialogue avec un vérificateur qui n'accepte rien sur confiance.
- **Les mathématiques vivantes** (Lean-15 à Lean-17b) : Game of Life (Hashlife), théorie des jeux sociaux (Arrow, Sen, Shapley), topologie (Grothendieck), théorie des nœuds (Piccirillo, tricolorabilité de Fox). Chaque domaine porté en Lean devient une *certification* — le `sorry` résiduel y est tracé comme une dette, pas caché.

### Prochaines étapes

- **Poussez un port jusqu'au bout** : le projet [`knot_lean/`](knot_lean/) est le companion formel de Lean-17b. Les invariants de nœuds (PD-codes, Reidemeister, Fox) y sont portés avec quelques `sorry` résiduels documentés — un terrain concret où une preuve formelle est *en cours*, pas achevée.
- **Croisez avec la théorie des jeux** : les résultats formels d'Arrow/Sen/Shapley/Voting (notebooks 16b-16f) rencontrent la série **[GameTheory](../../GameTheory/)** — où le choix social est étudié à la fois formellement et computationnellement.
- **Appliquez au monde réel** : la vérification formelle n'est pas qu'abstraite. La série **[SmartContracts](../SmartContracts/)** (SC-14) applique les mêmes principes aux smart contracts — SMT solvers automatiques bornés d'un côté, Lean interactif expressif de l'autre, même ambition : certifier la correction d'un programme exécuté.
- **Élargissez au Web Sémantique** : les shapes SHACL sont des invariants sur les données, analogues aux spécifications Lean. La série **[SemanticWeb](../SemanticWeb/)** (SW-7 OWL, SW-8 SHACL) explore une autre face de la certification — valider la cohérence d'une basé de connaissances plutôt que prouver un théorème.
- **Relisez la série sous l'angle de la certification** : la [Lecture transversale](#lecture-transversale) relie ce geste — *certifier par changement de représentation* — à l'ensemble du dépôt CoursIA.

### Le fil rouge

Le titre annonce un solveur mathématique et de la vérification formelle. Mais le geste que cette série enseigne est plus profond : **ne rien laisser sur confiance**. Un `theorem` en Lean n'est pas une affirmation, c'est un objet vérifié mécaniquement ; un `sorry` n'est pas un raccourci, c'est un trou dans la chaîne de certification que l'on trace explicitement. Les domaines changent (topologie, choix social, nœuds, cellular automata), les tactiques changent (`induction`, `native_decide`, `aesop`), mais l'exigence reste — *prouver, pas supposer*. C'est elle que vous emportez au-delà de cette série.

---

## Licence

Voir la licence du repository principal.
