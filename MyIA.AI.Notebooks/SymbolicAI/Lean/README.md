# Lean - Solveur Mathematique et Verification Formelle

<!-- CATALOG-STATUS
series: SymbolicAI-Lean
pedagogical_count: 0
breakdown: 
maturity: 
-->

Cette serie de **21 notebooks** introduit **Lean 4**, un assistant de preuves et langage de programmation fonctionnel base sur la theorie des types dependants, avec un focus sur les techniques modernes d'utilisation de LLMs pour l'assistance aux preuves, la verification formelle de reseaux de neurones, le port de theoremes phares (theoreme de Kochen-Specker, 18 vecteurs Cabello ; theoreme du libre arbitre de Conway-Kochen), et des hommages aux mathematiciens (Grothendieck, langage grothendieckien dans Mathlib 4 ; John Conway, l'homme et l'oeuvre).

## Navigation

Tous les notebooks incluent une **barre de navigation** en haut et en bas permettant de passer facilement d'un notebook a l'autre. Chaque notebook contient egalement un **Plan** avec des liens ancres vers chaque section.

## Modes d'execution suggeres

| Mode | Notebooks | Temps | Description |
|------|-----------|-------|-------------|
| **Fondations** | 1-5 | ~3h | Base theorique complete (types, logique, tactiques) |
| **Avec Mathlib** | 1-6 | ~3h45 | Ajoute les tactiques Mathlib |
| **Integration IA** | 1-7, 7b | ~5h | Ajoute LLMs, exemples et benchmarks |
| **Complet** | 1-12 | ~11h | Toutes les fonctionnalites incluant LeanDojo et theoreme de sensibilite |
| **Avec Pilier 1.B** | 1-12, 15 | ~12h | Inclut le port Kochen-Specker (Cabello 18-vecteurs) - contextuality quantique |
| **Avec hommages** | 1-12, 13, 14a, 14b, 14c, 15, 16 | ~16h | Ajoute Lean-13 (Grothendieck), Lean-14a (Conway, l'homme et l'oeuvre), Lean-14b (Conway, Game of Life) et Lean-16 (Conway, theoreme du libre arbitre - adosse a Lean-15) |

## Structure

### Partie 1 : Fondations (base sur PDF de reference)

| # | Notebook | Contenu | Duree |
|---|----------|---------|-------|
| 1 | [Lean-1-Setup](Lean-1-Setup.ipynb) | Installation elan, kernel Jupyter, verification | 15 min |
| 2 | [Lean-2-Dependent-Types](Lean-2-Dependent-Types.ipynb) | Calcul des Constructions, types, polymorphisme | 35 min |
| 3 | [Lean-3-Propositions-Proofs](Lean-3-Propositions-Proofs.ipynb) | Prop, connecteurs, Curry-Howard, preuves par termes | 45 min |
| 4 | [Lean-4-Quantifiers](Lean-4-Quantifiers.ipynb) | forall, exists, egalite, arithmetique Nat | 40 min |
| 5 | [Lean-5-Tactics](Lean-5-Tactics.ipynb) | Mode tactique, apply/exact/intro/rw/simp | 50 min |

### Partie 2 : Etat de l'art et integration IA

| # | Notebook | Contenu | Duree |
|---|----------|---------|-------|
| 6 | [Lean-6-Mathlib-Essentials](Lean-6-Mathlib-Essentials.ipynb) | Mathlib4, tactiques ring/linarith/omega, recherche | 45 min |
| 7 | [Lean-7-LLM-Integration](Lean-7-LLM-Integration.ipynb) | LeanCopilot, AlphaProof, patterns LLM-Lean | 50 min |
| 7b | [Lean-7b-Examples](Lean-7b-Examples.ipynb) | Exemples progressifs, benchmarks, cas pratiques | 40 min |
| 8 | [Lean-8-Agentic-Proving](Lean-8-Agentic-Proving.ipynb) | Agents autonomes, APOLLO, problemes Erdos | 55 min |
| 9 | [Lean-9-SK-Multi-Agents](Lean-9-SK-Multi-Agents.ipynb) | Agent Framework (Microsoft), orchestration multi-agents | 45 min |
| 10 | [Lean-10-LeanDojo](Lean-10-LeanDojo.ipynb) | LeanDojo: tracing, theorems, Dojo interactif | 45 min |
| 11 | [Lean-11-TorchLean](Lean-11-TorchLean.ipynb) | TorchLean: reseaux de neurones verifies, IBP, CROWN | 1h30-2h |
| 11a | [Lean-11-TorchLean-Python](Lean-11-TorchLean-Python.ipynb) | Implementation Python des algorithmes de verification (IBP, CROWN) | 1h30-2h |
| 12 | [Lean-12-Sensitivity-Theorem](Lean-12-Sensitivity-Theorem.ipynb) | Theoreme de sensibilite (Huang 2019), hypercube, signing matrix, port Lean 4 | 60 min |

### Partie 3 : Theoremes phares (ports complets)

| # | Notebook | Contenu | Duree |
|---|----------|---------|-------|
| 15 | [Lean-15-Kochen-Specker](Lean-15-Kochen-Specker.ipynb) | Theoreme de Kochen-Specker (1967), preuve Cabello 18 vecteurs, parite, contextuality quantique - Pilier 1.B Epic #1651 | 60 min |

### Partie 4 : Hommages mathematiciens

| # | Notebook | Contenu | Duree |
|---|----------|---------|-------|
| 13 | [Lean-13-Grothendieck-Tribute](Lean-13-Grothendieck-Tribute.ipynb) | Langage grothendieckien dans Mathlib 4 : categories/foncteurs, cribles et topologies de Grothendieck, faisceaux, schemas, site de Zariski, morphismes etales/lisses - Epic #1646 | 45 min |
| 14a | [Lean-14a-Conway-Man-and-Work](Lean-14a-Conway-Man-and-Work.ipynb) | Conway, l'homme et l'oeuvre : biographie et style singulier (le jeu comme methode) ; panorama des grands resultats (nombres surreels, groupes de Conway & Monstrous Moonshine, reseau de Leech, polynome de Conway, Doomsday, Look-and-Say, FRACTRAN, probleme de l'Ange, Sprouts, theoreme du libre arbitre) ; premieres noix crackees executees depuis conway_lean (Doomsday, Look-and-Say, Nim, Angel, Life - 0 sorry) - Epic #1647 / #2154 | 50 min |
| 14b | [Lean-14b-Conway-Game-of-Life-Lean](Lean-14b-Conway-Game-of-Life-Lean.ipynb) | Hommage a John Conway : Game of Life as Computation, Doomsday, FRACTRAN, Look-and-Say, Nim, Angel - Epic #1647 | 60 min |
| 16 | [Lean-16-Conway-Free-Will-Theorem](Lean-16-Conway-Free-Will-Theorem.ipynb) | Theoreme du libre arbitre (Conway-Kochen) : les trois axiomes SPIN/TWIN/MIN en profondeur, argument en deux temps (1 particule via Kochen-Specker, puis 2 particules via TWIN), ce que le theoreme dit et NE dit PAS, port formel adosse a `FreeWillTheorem.lean` (chaine de reduction `free_will_theorem -> fwt_single_particle -> kochen_specker`, 0 sorry), registre d'extensibilite - Epic #2162 / #2156 | 40 min |

**Duree totale** : ~16h

## Acquis d'apprentissage

A l'issue de la serie, vous saurez :

- **Modeliser** un raisonnement mathematique dans le Calcul des Constructions : types dependants, univers, propositions comme types (Curry-Howard). Notebooks 2-3 ancrent ces objets sur des exemples concrets (Vector, propositions logiques) plutot que sur de l'abstraction nue.
- **Prouver** un theoreme en mode tactique avec les briques Mathlib : `intro`/`apply`/`exact`/`rfl` pour la structure, `ring`/`linarith`/`omega`/`simp` pour l'arithmetique et la simplification, `induction`/`cases`/`rcases` pour l'analyse de cas. Notebooks 4-6.
- **Integrer un LLM** au workflow de preuve : patterns LeanCopilot et AlphaProof (n-best, MCTS), prompts goal-aware, comparaison ND-search vs CoT, agents APOLLO/Erdos. Notebooks 7-9.
- **Tracer et explorer** une base de preuves a grande echelle : LeanDojo (parsing AST, theorem extraction, interaction Dojo), reseaux de neurones verifies via IBP/CROWN (TorchLean). Notebooks 10-11.
- **Porter** un theoreme de recherche en Lean 4 : theoreme de sensibilite (Huang 2019, hypercube et signing matrix), theoreme de Kochen-Specker (Cabello 18 vecteurs, argument de parite, contextuality quantique). Notebooks 12, 15.
- **Lire le langage grothendieckien** dans Mathlib 4 : categories et foncteurs, cribles et topologies de Grothendieck, faisceaux, schemas et sites, morphismes etales/lisses — comme entree vers la geometrie algebrique formalisee. Notebook 13.
- **Situer l'oeuvre de Conway** dans sa largeur : des nombres surreels au Monstrous Moonshine, du reseau de Leech au theoreme du libre arbitre, en executant les premieres noix formalisees (Doomsday, Look-and-Say, Nim, Angel, Life) directement depuis le projet conway_lean (0 sorry). Notebook 14a.
- **Explorer les noix de Conway** en Lean 4 : Game of Life as Computation, Doomsday, FRACTRAN, Look-and-Say, Nim, Angel — port formel de resultats combinatoires iconiques. Notebook 14.
- **Comprendre le theoreme du libre arbitre** (Conway-Kochen) : les axiomes SPIN/TWIN/MIN, l'argument en deux temps qui reduit le cas a deux particules au theoreme de Kochen-Specker (Notebook 15), et la lecture honnete de sa portee (ce qu'il dit et ne dit pas) — adosse a `FreeWillTheorem.lean` (0 sorry). Notebook 16.

Pour l'etat formel detaille des modules support (preuves resolues vs `sorry` residuels), voir [LEAN_INVENTORY.md](../../GameTheory/LEAN_INVENTORY.md), le [README du projet conway_lean](conway_lean/README.md), et le [README du projet grothendieck_lean](grothendieck_lean/README.md).

## Statut de maturite

| # | Notebook | Cellules | Exercices | Solutions | Statut |
|---|----------|----------|-----------|-----------|--------|
| 1 | Setup | ~17 | - | - | **COMPLET** |
| 2 | Dependent-Types | ~50 | 3 | 3 | **COMPLET** |
| 3 | Propositions-Proofs | ~50 | 3 | 3 | **COMPLET** |
| 4 | Quantifiers | ~46 | 3 | 3 | **COMPLET** |
| 5 | Tactics | ~70 | 3 | 3 | **COMPLET** |
| 6 | Mathlib-Essentials | ~45 | 3 | 3 | **COMPLET** |
| 7 | LLM-Integration | ~50 | 2 | 2 | **COMPLET** |
| 7b | Examples | ~40 | 3 | 3 | **COMPLET** |
| 8 | Agentic-Proving | ~70 | 2 | 2 | **COMPLET** |
| 9 | SK-Multi-Agents | ~50 | 2 | 2 | **COMPLET** |
| 10 | LeanDojo | ~100 | 2 | 0 | **COMPLET** |
| 11 | TorchLean | ~40 | 3 | Oui | **COMPLET** |
| 11a | TorchLean Python | ~45 | 3 | Oui | **COMPLET** |
| 12 | Sensitivity-Theorem | ~31 | 4 | Non | **NOUVEAU** |
| 13 | Grothendieck-Tribute | ~23 | 0 | - | **NOUVEAU** (hommage) |
| 14a | Conway-Man-and-Work | ~39 | 3 | 0 | **NOUVEAU** (hommage) |
| 14b | Conway-Game-of-Life-Lean | ~26 | 0 | - | **NOUVEAU** (hommage) |
| 15 | Kochen-Specker | ~25 | 1 | 0 | **NOUVEAU** |
| 16 | Conway-Free-Will-Theorem | ~28 | 3 | 0 | **NOUVEAU** (hommage) |

Tous les notebooks incluent :
- Navigation header/footer avec liens vers notebooks precedent/suivant
- Plan de ce Notebook avec liens ancres (notebooks 2-4)
- Tableaux recapitulatifs en fin de section
- Exercices avec solutions completes

## Quick Start

```bash
# 1. Installer elan (gestionnaire Lean)
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
elan default leanprover/lean4:stable

# 2. Verifier l'installation
lean --version    # Lean 4.x.x
elan show         # toolchain active

# 3. Ouvrir le premier notebook (WSL requis)
wsl -d Ubuntu -- bash -c "jupyter notebook Lean-1-Setup.ipynb"
```

Pour les notebooks 7-10 (LLM), configurer `.env` avec `OPENAI_API_KEY`. Pour le prover daemon, voir section "Prover daemon".

---

## Prerequisites

- Connaissances de base en logique mathematique
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

# Verifier l'installation
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

### References academiques

| Reference | Couverture |
|-----------|------------|
| de Moura & Ullrich, "The Lean 4 Theorem Prover and Programming Language" (2021) | Systeme Lean 4 |
| The Mathlib Community, "The Mathlib Library" (2020), arXiv:1910.09436 | Mathlib4 |
| Avigad, "Mathematics and Programming" (2024) — *Mathematics in Lean* | Fondations notebooks 1-5 |
| Jiang et al., "LeanDojo: Theorem Proving with Retrieval-Augmented Language Models" (NeurIPS 2023) | LeanDojo, notebooks 10 |
| First et al., "AlphaProof: Formal Math Reasoning" (DeepMind, 2024) | Notebook 7 |
| Song et al., "Towards Counting Forall: Neural Network Verification via IBP, CROWN, and LiRPA" | TorchLean, notebooks 11 |
| Geanakoplos, "Three Brief Proofs of Arrow's Impossibility Theorem" (2005) | Cross-series GameTheory |
| Sen, "Collective Choice and Social Welfare" (1970) | Cross-series GameTheory |

## Document source

- Notebooks 1-5 bases sur : `D:\Dropbox\IA101\TPs\TP - Z3 - Tweety - Lean.pdf` (Section VI)
- Notebooks 6-8 bases sur : Recherches etat de l'art 2025-2026

## Validation

```bash
# Verifier la structure des notebooks
python scripts/verify_notebooks.py MyIA.AI.Notebooks/SymbolicAI/Lean --quick

# Verifier l'installation Lean
lean --version
elan show
```

## Percees recentes (2024-2026)

| Systeme | Accomplissement |
|---------|-----------------|
| **AlphaProof** (DeepMind) | Medaille d'argent IMO 2024 |
| **Harmonic Aristotle** | Resolution Erdos #124 variant (~30 ans ouvert) en 6h |
| **DeepSeek-Prover** | Resolution de problemes Erdos 379, 987, 730, 198 |
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
├── Lean-13-Grothendieck-Tribute.ipynb # Python kernel - hommage Grothendieck (langage grothendieckien Mathlib)
├── Lean-14a-Conway-Man-and-Work.ipynb # Python kernel - hommage Conway (l'homme et l'oeuvre, noix executees depuis conway_lean)
├── Lean-14b-Conway-Game-of-Life-Lean.ipynb   # Python kernel - hommage Conway (Game of Life as Computation)
├── Lean-15-Kochen-Specker.ipynb    # Lean4 kernel - theoreme de Kochen-Specker (Pilier 1.B)
├── Lean-16-Conway-Free-Will-Theorem.ipynb # Python kernel - hommage Conway (theoreme du libre arbitre, adosse a FreeWillTheorem.lean)
├── _run_lean_snippet.sh            # Helper WSL : run Lean snippet avec cache Mathlib
├── lean_runner.py                  # Module Python multi-backend
├── README.md
├── .env.example
├── conway_lean/                    # Conway tribute workspace (0 sorry, Lake build)
├── grothendieck_lean/              # Grothendieck tribute workspace (0 sorry, Lake build)
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
│       └── verifier.py             # Lean verification backend
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

Le package `agent_tests/prover/` implemente un prouveur autonome Lean 4 utilisant le Microsoft Agent Framework.

### Architecture

4 agents specialises dans un workflow conditionnel :

1. **SearchAgent** : analyse le contexte, detecte les sorry, identifie les helpers
2. **TacticAgent** : genere des tactiques de preuve (avec outils de compilation)
3. **VerifyExecutor** : verifie les tactiques via `lake build` (non-LLM)
4. **CriticAgent** : analyse les erreurs et route vers le bon agent

### Usage

```bash
# Prouver un sorry dans un fichier .lean
python agent_tests/multi_agent_proof.py --lean path/to/File.lean --sorry-line 128

# Mode autonome (1 agent avec tous les outils)
python agent_tests/multi_agent_proof.py --lean path/to/File.lean --mode autonomous

# Mode multi-agent (4 agents specialises)
python agent_tests/multi_agent_proof.py --lean path/to/File.lean --mode multi

# Batch sur des demos
python agent_tests/multi_agent_proof.py --batch --demos 1,2,3
```

### Configuration

Le fichier `.env` dans `agent_tests/` ou le repertoire parent configure :
- `ZAI_API_KEY` : cle API z.ai pour GLM-5.1 (raisonnement)
- `ZAI_BASE_URL` : endpoint API z.ai
- `LEAN_PROJECT_DIR` : repertoire du projet Lean (pour `lake build`)

## Connections cross-series

Les concepts de verification formelle et de preuve assistee par LLM presentes dans cette serie se retrouvent dans d'autres series du curriculum :

### Lean et Theorie des Jeux (GameTheory)

Les notebooks GameTheory side tracks (16b-16f) formalisent en Lean 4 des resultats fondamentaux de theorie des jeux et de choix social :

| resultat | Fichier Lean | Notebook GameTheory | Statut |
|----------|-------------|---------------------|--------|
| Theoreme d'Arrow (impossibilite) | `social_choice_lean/SocialChoice/Arrow.lean` | 16d | 0 sorry (Geanakoplos 2005) |
| Theoreme de Sen (liberalisme) | `social_choice_lean/SocialChoice/Sen.lean` | 16e | 0 sorry (bidirectionnel) |
| Valeur de Shapley | `cooperative_games_lean/CooperativeGames/Shapley.lean` | 16b | 1 sorry (en cours) |
| Modeles de vote (Banks, STV) | `social_choice_lean/SocialChoice/Voting.lean` | 16f | 4 sorry (open problems) |
| Gale-Shapley (stable marriage) | `stable_marriage_lean/StableMarriage/GaleShapley.lean` | (pas de notebook dedie) | 2 sorry / 5 theoremes. `gale_shapley_stable` CLOSED via mmaaz upstream (PR #1181). `man_optimal` + `woman_pessimal` OPEN (Knuth 1976 lattice, Wu-Roth 2018 — ~5-8j Mathlib). |

Le notebook Lean-5 (tactiques) et Lean-6 (Mathlib) sont des prerequis directs pour les side tracks Lean de GameTheory.

### Lean et SmartContracts

La verification formelle en Lean (type theory, Curry-Howard) est conceptuellement liee a la verification formelle des smart contracts :

- **SC-14 Formal Verification** : Certora/SMTChecker vs. Lean -- la meme idee de preuve mathematique de correction, mais sur des cibles differentes (Solidity vs. mathematiques). Les methodes different : SMT solving (automatique, borne) vs. tactiques interactives (expressif, guidable).
- **SC-11 LLM-Assisted Contracts** : Le meme paradigme d'assistance LLM que les notebooks Lean-7/8/9, applique a la generation de smart contracts au lieu de preuves.
- **SC-17 E2E Verifiable Voting** : Les resultats de `Voting.lean` (theoreme du median voter, proprietes Banks/STV) eclairent les proprietes theoriques des systemes de vote verifiable.

### Lecture transversale

[La mer qui monte](../../../docs/grothendieckian-lens.md) : une grille de lecture grothendieckienne du depot (changement de representation, certification A/B/C).

## FAQ

### Le kernel lean4-wsl ne demarre pas (timeout apres 60s)

**Cause** : le wrapper Python (`~/.lean4-kernel-wrapper.py`) ne trouve pas le venv Lean ou le REPL. Verifier :

```bash
# Dans WSL
test -f ~/.lean4-venv/bin/python3 && echo "venv OK" || echo "venv MISSING"
test -f ~/.elan/bin/repl && echo "repl OK" || echo "repl MISSING"
test -d ~/lean-projects/notebook_context && echo "context OK" || echo "context MISSING"
```

Si un element manque, relancer le setup : `bash MyIA.AI.Notebooks/GameTheory/scripts/setup_wsl_lean4.sh`. Si le kernel.json pointe vers l'ancien wrapper bash (`~/lean4-jupyter-wrapper.sh`), le mettre a jour pour pointer vers `~/.lean4-kernel-wrapper.py` (incident 2026-05-27).

### `lake build` echoue avec des erreurs Mathlib inattendues

**Cause frequente** : la toolchain Lean locale est desynchronisee du `lean-toolchain` du projet. Lean 4 evolue rapidement et Mathlib suit.

```bash
# Verifier la toolchain requise par le projet
cat lean-toolchain    # ex: leanprover/lean4:v4.x.0

# Verifier la toolchain installee
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

Le notebook [Lean-1-Setup](Lean-1-Setup.ipynb) guide l'installation complete et verifie chaque composant.

### Mes preuves passent en mode terme mais pas en mode tactique

C'est un pattern courant en Lean 4. Le mode terme (style `theorem foo : X := by exact h`) et le mode tactique utilisent parfois des mecanismes de synthese differents. En general :

- Le mode tactique offre plus de controle (`rw`, `simp`, `ring`) et des messages d'erreur plus lisibles.
- Si une preuve terme echoue, essayer le mode tactique avec les memes etapes decomposees.
- `simp?` suggere les lemmes que `simp` utilise — utile pour comprendre pourquoi `simp` seul ne passe pas.

### Comment lire les erreurs `type mismatch` ?

Lean 4 signale `type mismatch` quand le type attendu et le type fourni ne coincident pas. Les causes les plus frequentes :

- **Universe level** : `Type u` vs `Type` — ajouter `universe u` ou utiliser `Sort _`.
- **Implicit arguments** : Lean ne peut pas inferrer un argument implicite. Essayer `@nom_fonction` pour rendre tous les arguments explicites.
- **Definitional equality** : `Nat` vs `Int`, `List` vs `Array` — utiliser les conversions explicites (`Int.ofNat`, `List.toArray`).
- **Motive mismatch** dans `induction`/`cases` : le motif (motive) ne generalise pas correctement. Essayer `generalizing h` ou restructurer le but avec `have` avant l'induction.

### `sorry` dans un notebook pedagogique, c'est grave ?

**Non** dans les cellules d'exercice (stub pour l'etudiant). **Oui** dans le code de production (preuves formelles). La convention CoursIA :

- Cellules d'exercice : `sorry` = placeholder etudiant, normal et attendu.
- Preuves certifiees (ex: `conway_lean/`, `grothendieck_lean/`, `social_choice_lean/`) : `sorry` = axiome implicite = trou dans la chaine de certification. Le compteur `grep -c sorry` est suivi par les agents du depot.

Voir [LEAN_INVENTORY.md](../../GameTheory/LEAN_INVENTORY.md) pour l'etat detaille des preuves par module.

### LLM + Lean : quelles limites actuelles ?

Les LLMs (GPT-4o, Claude, DeepSeek) sont capables de generer des tactiques Lean 4 pour des preuves de niveau undergraduate, mais :

- **Preuves longues** (> 20 etapes) : le taux de succes chute significativement.
- **Mathlib avancee** : les LLMs ne connaissent pas toujours les lemmes disponibles — LeanCopilot et la recherche semantique (Loogle/Moogle) compensent.
- **Agents autonomes** (APOLLO, AlphaProof) : prometteurs pour les competitions (IMO, Erdos) mais pas encore fiables pour des preuves de recherche originales sans supervision.
- **Bon usage pedagogique** : utiliser les LLMs comme assistant (suggestions, exploration), pas comme oracle (accepter sans verifier). Les notebooks 7-9 illustrent ce workflow.

## Licence

Voir la licence du repository principal.
