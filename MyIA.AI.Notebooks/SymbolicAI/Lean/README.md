# Lean - Solveur Mathematique et Verification Formelle

Cette serie de **11 notebooks** introduit **Lean 4**, un assistant de preuves et langage de programmation fonctionnel base sur la theorie des types dependants, avec un focus sur les techniques modernes d'utilisation de LLMs pour l'assistance aux preuves.

## Navigation

Tous les notebooks incluent une **barre de navigation** en haut et en bas permettant de passer facilement d'un notebook a l'autre. Chaque notebook contient egalement un **Plan** avec des liens ancres vers chaque section.

## Modes d'execution suggeres

| Mode | Notebooks | Temps | Description |
|------|-----------|-------|-------------|
| **Fondations** | 1-5 | ~3h | Base theorique complete (types, logique, tactiques) |
| **Avec Mathlib** | 1-6 | ~3h45 | Ajoute les tactiques Mathlib |
| **Integration IA** | 1-7, 7b | ~5h | Ajoute LLMs, exemples et benchmarks |
| **Complet** | 1-10 | ~8h | Toutes les fonctionnalites incluant LeanDojo |

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
| 9 | [Lean-9-SK-Multi-Agents](Lean-9-SK-Multi-Agents.ipynb) | Semantic Kernel, orchestration multi-agents | 45 min |
| 10 | [Lean-10-LeanDojo](Lean-10-LeanDojo.ipynb) | LeanDojo: tracing, theorems, Dojo interactif | 45 min |

**Duree totale** : ~8h

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
| 10 | LeanDojo | ~100 | Demo | - | **COMPLET** |

Tous les notebooks incluent :
- Navigation header/footer avec liens vers notebooks precedent/suivant
- Plan de ce Notebook avec liens ancres (notebooks 2-4)
- Tableaux recapitulatifs en fin de section
- Exercices avec solutions completes

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
├── Lean-9-SK-Multi-Agents.ipynb    # Python kernel - Semantic Kernel
├── Lean-10-LeanDojo.ipynb          # Python kernel - LeanDojo
├── lean_runner.py                  # Module Python multi-backend
├── README.md
├── .env.example
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

## Licence

Voir la licence du repository principal.
