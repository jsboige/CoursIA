---
theme: ../theme-ia101
title: "Verification Formelle - Lean 4"
info: IA 101 - Verification formelle et assistants de preuves avec Lean 4
paginate: true
drawings:
  persist: false
transition: slide-left
mdc: true
layout: cover
---

# Lean 4 — Verification Formelle et Preuves Assistees par IA

- Fondements : types dependants, Curry-Howard
- Logique formelle : propositions, quantificateurs, tactiques
- Mathlib4 : la plus grande bibliotheque de mathematiques formalisees
- Integration LLM : LeanCopilot, AlphaProof
- Agents autonomes et verification de reseaux de neurones

---
layout: section
---

# Plan

---

# Sommaire

## Objectifs pedagogiques

- Comprendre les **types dependants** et le **calcul des constructions** (Lean 4 / CIC)
- Rediger des **preuves formelles** : termes, tactiques, mode interactif
- Utiliser **Mathlib4** : tactiques `ring`, `linarith`, `omega`, `decide`
- Explorer l'**integration LLM** pour l'assistance aux preuves
- Implementer des **agents autonomes** de preuves avec Semantic Kernel
- Verifier formellement des **reseaux de neurones** (IBP, CROWN)

## Prerequis

- Logique propositionnelle et du premier ordre
- Programmation fonctionnelle (optionnel)
- Python 3.10+ pour les notebooks d'integration IA

## Duree totale estimee

**~11 heures** (14 notebooks, 15 min a 2h chacun)

---
layout: section
---

# Partie 1 : Fondations

---

# Lean 1 — Setup et Ecosysteme

## Installation

```bash
# Installer elan (gestionnaire de versions Lean)
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
elan default leanprover/lean4:stable

lean --version  # Lean 4.x.x
```

## Kernel Jupyter pour Lean 4

- **lean4jupyter** : execution cellule-par-cellule dans Jupyter
- **Lake** : systeme de build et de gestion de packages
- **Mathlib** : ajout dans `lakefile.lean` via `require mathlib`

## Verification de l'installation

```lean
-- Hello Lean 4
#check Nat.add_comm  -- Nat.add_comm : ∀ (n m : ℕ), n + m = m + n
#eval 2 + 2          -- 4
```

> **Notebook** : `Lean-1-Setup.ipynb` — 15 min

---

# Lean 2 — Types Dependants

## Calcul des Constructions (CIC)

- **Types comme termes** : `Nat : Type`, `List Nat : Type`
- **Types dependants** : `Vector α n` (liste de longueur exactement `n`)
- **Propositions = Types** (isomorphisme de Curry-Howard)

## Polymorphisme et univers

```lean
-- Type polymorphe
def myId {α : Type} (a : α) : α := a

-- Type dependant : longueur garantie par le type
def head : {n : Nat} → Vector α (n + 1) → α
  | _, ⟨a :: _, _⟩ => a

-- Univers : Type 0, Type 1, ...
#check @List.map  -- List.map : (α → β) → List α → List β
```

> **Notebook** : `Lean-2-Dependent-Types.ipynb` — 35 min

---

# Lean 3 — Propositions et Preuves

## Prop et les connecteurs logiques

```lean
-- Preuves comme termes
theorem and_comm (h : P ∧ Q) : Q ∧ P :=
  ⟨h.2, h.1⟩

-- Curry-Howard : implication = type fonction
example (h : P → Q) (hp : P) : Q := h hp

-- Negation : ¬P = P → False
theorem not_not (h : ¬¬P) : P := h (fun np => np (h np))  -- EM requis
```

## Preuves constructives vs classiques

- **Intuitionniste** : toute preuve = programme (Curry-Howard direct)
- **Classique** : `Classical.em : ∀ P, P ∨ ¬P` (Law of Excluded Middle)
- **Propext** : `propext : P ↔ Q → P = Q`

> **Notebook** : `Lean-3-Propositions-Proofs.ipynb` — 45 min

---

# Lean 4 — Quantificateurs et Arithmetique

## Forall et Exists

```lean
-- Universal : ∀ preuve directe
theorem forall_and : (∀ x, P x ∧ Q x) → (∀ x, P x) ∧ (∀ x, Q x) :=
  fun h => ⟨fun x => (h x).1, fun x => (h x).2⟩

-- Existential : ⟨witness, proof⟩
theorem exists_intro : P a → ∃ x, P x := fun h => ⟨a, h⟩
```

## Arithmetique des naturels

```lean
-- Induction
theorem add_zero : ∀ n : Nat, n + 0 = n
  | 0 => rfl
  | n + 1 => congrArg (· + 1) (add_zero n)

-- Egalite : rfl, symm, trans, congrArg
theorem eq_symm {a b : α} (h : a = b) : b = a := h.symm
```

> **Notebook** : `Lean-4-Quantifiers.ipynb` — 40 min

---

# Lean 5 — Tactiques

## Mode interactif : `by`

```lean
theorem de_morgan (h : ¬(P ∨ Q)) : ¬P ∧ ¬Q := by
  constructor
  · intro hp; exact h (Or.inl hp)
  · intro hq; exact h (Or.inr hq)
```

## Repertoire des tactiques essentielles

| Tactique | Effet |
|---------|-------|
| `intro h` | Introduit une hypothese |
| `apply f` | Applique un lemme/fonction |
| `exact h` | Ferme le goal avec `h` |
| `rw [h]` | Reecrit avec une egalite |
| `simp` | Simplification automatique |
| `omega` | Arithmetique lineaire ℤ/ℕ |
| `tauto` | Tautologies propositionnelles |

> **Notebook** : `Lean-5-Tactics.ipynb` — 50 min

---
layout: section
---

# Partie 2 : Etat de l'Art et Integration IA

---

# Lean 6 — Mathlib4

## La plus grande bibliotheque de maths formalisees

- **150 000+ theoremes** : algebre, topologie, theorie des nombres, analyse
- **Tactiques avancees** : `ring`, `linarith`, `norm_num`, `decide`, `field_simp`

```lean
import Mathlib

-- Tactique ring : ferme automatiquement les egalites d'anneaux
example (a b : ℤ) : (a + b)^2 = a^2 + 2*a*b + b^2 := by ring

-- Tactique omega : arithmetique lineaire entiere
example (n : ℕ) (h : n > 5) : n ≥ 6 := by omega

-- Recherche de theoremes
#check Nat.Prime.two_le  -- ∀ (p : ℕ), Nat.Prime p → 2 ≤ p
example? (a b c : ℕ) : a * (b + c) = a * b + a * c  -- suggest: mul_add
```

> **Notebook** : `Lean-6-Mathlib-Essentials.ipynb` — 45 min

---

# Lean 7 — Integration LLM

## LeanCopilot : LLM comme assistant de preuves

```lean
-- Suggestion automatique de preuves (GPT-4, Claude, etc.)
theorem fermat_last_n2 : ∀ a b c : ℕ, a^2 + b^2 = c^2 → ... := by
  suggest  -- appelle le LLM pour proposer des tactiques
```

## AlphaProof (DeepMind 2024)

- Premier systeme a resoudre des problemes IMO avec Lean
- **Reinforcement learning** sur l'espace des preuves Lean
- Certaines preuves verificables mais **non interpretables par un humain**

## Patterns d'integration

| Outil | Approche | Statut |
|-------|---------|--------|
| **LeanCopilot** | In-context completion | Prod |
| **AlphaProof** | RL + Monte Carlo tree search | Research |
| **Draft-Sketch-Prove** | LLM + formal verification | Research |

> **Notebook** : `Lean-7-LLM-Integration.ipynb` — 50 min

---

# Lean 8 — Agents Autonomes de Preuves

## Architecture APOLLO

- **Orchestrateur** : decompose un theoreme complexe en sous-buts
- **Prouver** : tente chaque sous-but avec tactiques + LLM
- **Verifier** : Lean verifie formellement chaque etape

```python
from prover.agents import MultiAgentSorryProver

prover = MultiAgentSorryProver(
    model="claude-opus-4-6",
    max_attempts=10
)
result = prover.prove(lean_file, target_theorem="Arrow_theorem")
```

## Problemes emblematiques (benchmarks)

- **Arrow's impossibility** : theoreme de choix social
- **Erdős problèmes** : nombre de Ramsey R(4,4) = 18
- **Competition IMO** : problèmes olympiques

> **Notebook** : `Lean-8-Agentic-Proving.ipynb` — 55 min

---

# Lean 9 — Multi-Agents avec Semantic Kernel

## Framework Microsoft Semantic Kernel

```python
from semantic_kernel import Kernel
from semantic_kernel.connectors.ai.anthropic import AnthropicChatCompletion

kernel = Kernel()
kernel.add_service(AnthropicChatCompletion("claude-sonnet-4-6"))

# Plugin Lean : execute lean dans un process
lean_plugin = LeanExecutorPlugin()
kernel.add_plugin(lean_plugin, "Lean")
```

## Architecture multi-agents pour les preuves

- **Orchestrateur** : planifie la strategie de preuve globale
- **Tactician** : selectionne les tactiques locales
- **Checker** : verifie la validite formelle
- **Explainer** : traduit la preuve en prose mathematique

> **Notebook** : `Lean-9-SK-Multi-Agents.ipynb` — 45 min

---

# Lean 10 — LeanDojo

## Extraction de donnees depuis Mathlib

```python
from lean_dojo import LeanGitRepo, trace

# Tracer Mathlib4 pour extraire theoremes et preuves
repo = LeanGitRepo("leanprover-community/mathlib4", "v4.x.x")
traced = trace(repo)

# Acces a tous les theoremes
theorem = traced.get_theorem("Nat.add_comm")
print(theorem.full_name, theorem.proof_steps)
```

## Benchmark ProofNet / miniF2F

- **miniF2F** : 488 problemes mathematiques (AIME, AMC, IMO)
- **ProofNet** : 371 theoremes universitaires
- **LeanDojo** : environnement RL pour entrainer des prouveurs

> **Notebook** : `Lean-10-LeanDojo.ipynb` — 45 min

---

# Lean 11 — TorchLean : Verification de Reseaux de Neurones

## Pourquoi verifier formellement les NNs ?

- **Safety critical** : autonome, medical, finance → pas de tolerance d'erreur
- **Robustesse formelle** : prouver `‖x - x'‖ < ε → ‖f(x) - f(x')‖ < δ`

## IBP et CROWN

```lean
-- Propriete de robustesse formalisee en Lean
theorem network_robust (x : Vector ℝ n) (ε : ℝ) (hε : ε > 0) :
    ∀ x', ‖x - x'‖ ≤ ε → classify network x = classify network x' := by
  -- Preuve via propagation des bornes (IBP)
  apply ibp_bound_propagation
```

- **IBP** (Interval Bound Propagation) : bornes sur chaque couche
- **CROWN** : bornes plus precises via relaxation lineaire
- **α-CROWN** : variante optimisee (champion CAV 2021)

> **Notebooks** : `Lean-11-TorchLean.ipynb` + `Lean-11-TorchLean-Python.ipynb` — 1h30-2h

---

# Lean 12 — Theoreme de Sensibilite

## Le theoreme (Huang 2019)

**Tout** circuit booleen de profondeur `d` calcule une fonction de sensibilite ≤ `2^(d-1)`.
Preuve utilisant les **graphes d-dimensionnels et les matrices signing**.

```lean
-- Theoreme principal (port Lean 4 du papier Huang 2019)
theorem sensitivity_theorem (f : BoolFunc n) (C : Circuit n) :
    (∀ x, C.eval x = f x) →
    C.depth ≥ Real.log2 (sensitivity f) + 1 := by
  -- Preuve via hypercube et matrice signing
  apply signing_matrix_lower_bound
```

## Significance

- Resout une **conjecture ouverte depuis 30 ans**
- Premiere preuve formelle en Lean 4 dans ce repo

> **Notebook** : `Lean-12-Sensitivity-Theorem.ipynb` — 60 min

---
layout: section
---

# Synthese et Ressources

---

# Ecosysteme Lean 4

## Vue d'ensemble

```
Lean 4
├── Fondations         NB 1-5  : types, preuves, tactiques
├── Mathlib4           NB 6    : 150k+ theoremes
├── Integration LLM    NB 7-9  : LeanCopilot, SK multi-agents
├── LeanDojo           NB 10   : extraction donnees + RL
├── TorchLean          NB 11   : verification NNs (IBP/CROWN)
└── Recherche          NB 12   : theoreme de sensibilite
```

## Liens avec les autres series CoursIA

| Serie | Lien |
|-------|------|
| **S1-argumentation** | Argumentation formelle (Tweety ↔ Lean) |
| **S6-tweety** | Preferences → Arrow's impossibility prouvee en Lean |
| **03-logique** | Cours magistral logique propositionnelle + FOL |
| **GameTheory** | `social_choice_lean/` : Arrow/Sen/Voting formels |

---

# Pour aller plus loin

## Ressources essentielles

- **Lean 4 Manual** : https://leanprover.github.io/lean4/doc/
- **Mathlib4 Docs** : https://leanprover-community.github.io/mathlib4_docs/
- **Theorem Proving in Lean 4** (Avigad et al.) — livre officiel gratuit
- **LeanDojo** : https://leandojo.org/ (dataset + benchmark + RL env)
- **LeanCopilot** : https://github.com/lean-prover/LeanCopilot

## Conferences et competitions

- **ITP** (Interactive Theorem Proving) — conference annuelle
- **CAV** (Computer Aided Verification) — benchmark α-CROWN
- **IMO 2024** : AlphaProof resout 4/6 problemes avec Lean

## Extensions dans CoursIA

```
GameTheory/social_choice_lean/   # Arrow, Sen, Voting formels
SymbolicAI/Lean/                 # Cette serie
docs/lean/                       # Historique iterations prouver
```

---
layout: section
---

# Questions?

---
layout: end
---

# Merci

Serie Lean 4 — IA 101

`MyIA.AI.Notebooks/SymbolicAI/Lean/`
