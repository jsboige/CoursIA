"""Generate GameTheory-16e-SocialChoiceLean-Tour.ipynb as a Lean 4 kernel notebook."""
import json
import sys

cells = []

def md(source, cell_id):
    cells.append({
        "cell_type": "markdown",
        "id": cell_id,
        "metadata": {},
        "source": [source]
    })

def lean4(source, cell_id):
    cells.append({
        "cell_type": "code",
        "execution_count": None,
        "id": cell_id,
        "language": "lean4",
        "metadata": {},
        "outputs": [],
        "source": [source]
    })

# ===== Cell 1: Title + Navigation =====
md("""# GameTheory 16e - Tour de SocialChoiceLean (DominikPeters)

**Navigation** : [16b-Lean-SocialChoice](GameTheory-16b-Lean-SocialChoice.ipynb) | [16c-Python](GameTheory-16c-SocialChoice-Python.ipynb) | [16d-SAT](GameTheory-16d-SocialChoice-SAT.ipynb) | **16e-PetersTour**

**Kernel** : Lean 4 (WSL)

---

## Introduction

Ce notebook presente les resultats principaux formalises dans le depot [DominikPeters/SocialChoiceLean](https://github.com/DominikPeters/SocialChoiceLean), la plus grande bibliotheque de theorie du choix social en Lean 4.

Les definitions utilisent un **cadre simplifie** compatible avec le kernel Lean 4 (pas de Mathlib). Les preuves completes, utilisant Mathlib, se trouvent dans le projet Lake `social_choice_lean_peters/`.

### Objectifs d'apprentissage

1. Comprendre le cadre de DominikPeters (profils stricts, regles de vote, marges)
2. Explorer les axiomes de vote (Pareto, Condorcet, manipulabilite)
3. Decouvrir les theoremes d'impossibilite (Gibbard-Satterthwaite, Condorcet)
4. Analyser la regle Split Cycle et ses proprietes

### Duree estimee : 60 minutes

### Framework vs notre port (16b)

| Aspect | Notre port (16b) | DominikPeters (16e) |
|--------|-------------------|---------------------|
| Preferences | `Preference A` (faible, R) | `StrictPref A` (strict, lt) |
| Profils | `Profile I A := I -> Preference A` | `VotingProfile V A := V -> StrictPref A` |
| Regles | `SocialWelfareFunction` (ranking) | `VotingRule` (winner set) |
| Resultats | Arrow, Sen, Electeur Median | Gibbard-Satterthwaite, Split Cycle |
| Preuves | Manuelles (Geanakoplos 2005) | GPT-5.2 + verification Lean |""", "c01")

# ===== Cell 2: Section 1 intro =====
md("""---

## 1. Cadre Formel

DominikPeters utilise un cadre base sur les **preferences strictes** (ordres lineaires stricts), ou chaque electeur a un classement sans ex aequo. Ce choix simplifie les definitions des marges et des axiomes par rapport aux preferences faibles (16b).""", "c02")

# ===== Cell 3: Core types =====
lean4("""-- Simplified framework inspired by DominikPeters/SocialChoiceLean
-- Full formalization (with Mathlib): social_choice_lean_peters/PetersTour.lean

-- Strict preference: total strict order
-- Replaces Mathlib's LinearOrder for kernel compatibility
structure StrictPref (A : Type) where
  lt : A → A → Prop
  irrefl : ∀ x, ¬ lt x x
  trans : ∀ x y z, lt x y → lt y z → lt x z
  conn : ∀ x y, x ≠ y → lt x y ∨ lt y x

-- Voting profile: each voter has a strict preference
def VotingProfile (V A : Type) := V → StrictPref A

-- Voting rule: maps profile to a set of winners (as predicate)
def VotingRule (V A : Type) := VotingProfile V A → (A → Prop)

-- A rule is resolute if it always selects exactly one winner
def IsResolute {V A : Type} (f : VotingRule V A) : Prop :=
  ∀ P, ∃ c : A, f P c ∧ ∀ d, f P d → d = c

#check @StrictPref
#check @VotingProfile
#check @VotingRule
#check @IsResolute""", "c03")

# ===== Cell 4: Interpretation =====
md("""### Interpretation

| Concept | Peters (Mathlib) | Ce notebook (simplifie) |
|---------|-------------------|-------------------------|
| Preference stricte | `LinearOrder A` (classe) | `StrictPref A` (structure) |
| Profil | `Profile V A [Fintype V]` | `VotingProfile V A = V -> StrictPref A` |
| Regle | `VotingRule` (polymorphe Fintype) | `VotingRule V A = Profile -> (A -> Prop)` |
| Resolutude | `Resolute f` | `IsResolute f` |

Dans Peters, `LinearOrder` fournit `lt` automatiquement. Ici, on le definit explicitement avec `irrefl`, `trans`, et `conn` (totalite pour les elements distincts).""", "c04")

# ===== Cell 5: Section 2 intro =====
md("""---

## 2. Marges et Vainqueur de Condorcet

La **marge** d'un candidat sur un autre mesure l'ecart de votes : combien d'electeurs preferent a a b, moins combien preferent b a a. Un **vainqueur de Condorcet** bat tous les autres par marge positive.""", "c05")

# ===== Cell 6: Margin + Condorcet =====
lean4("""-- Margin function: pairwise difference
-- In Peters: (Finset.univ.filter (fun v => Prefers P v a b)).card
--   minus the reverse. Here: abstract signature.
abbrev MarginFun (A : Type) := A → A → Int

-- Condorcet winner: beats every other by positive margin
def IsCondorcetWinner {A : Type} (m : MarginFun A) (c : A) : Prop :=
  ∀ d, d ≠ c → m c d > 0

-- Condorcet consistency: the rule selects the Condorcet winner uniquely
def CondorcetConsistent {V A : Type} (f : VotingRule V A)
    (margin : VotingProfile V A → MarginFun A) : Prop :=
  ∀ P c, IsCondorcetWinner (margin P) c →
    f P c ∧ ∀ d, d ≠ c → ¬ f P d

#check @MarginFun
#check @IsCondorcetWinner
#check @CondorcetConsistent""", "c06")

# ===== Cell 7: Interpretation =====
md("""### Interpretation

La **marge** est l'outil central du framework de Peters. Elle permet de definir :

- **Condorcet winner** : candidat avec marge positive sur tous les autres
- **Condorcet consistency** : la regle Selectionne toujours le Condorcet winner

Le concept de marge est intuitif : si 7 electeurs preferent A a B et 3 preferent B a A, la marge de A sur B est +4. Un Condorcet winner a une marge positive contre chaque adversaire.

> **Note technique** : dans la formalisation complete, la marge utilise `Finset.card` (nombre d'electeurs preferant a a b). Notre version simplifiee prend la marge comme fonction abstraite.""", "c07")

# ===== Cell 8: Section 3 intro =====
md("""---

## 3. Axiomes de Vote

DominikPeters definit et utilise 15+ axiomes pour classifier les regles de vote. Chaque axiome exprime une propriete desirable : equite, robustesse, non-manipulabilite.""", "c08")

# ===== Cell 9: Axioms =====
lean4("""-- Pareto Efficiency: if all prefer c to d, d cannot win
def SatisfiesPareto {V A : Type} (f : VotingRule V A) : Prop :=
  ∀ P c d, (∀ v, (P v).lt c d) → ¬ f P d

-- Unanimity: if all rank c first, c must win
def SatisfiesUnanimity {V A : Type} (f : VotingRule V A) : Prop :=
  ∀ P c, (∀ v d, d ≠ c → (P v).lt c d) → f P c

-- Strategyproof (resolute): no voter can improve outcome by misreporting
-- The voter's true preferences are P v, but they report 'fake' instead
def IsStrategyproof {V A : Type} [DecidableEq A] (f : VotingRule V A) : Prop :=
  ∀ (P : VotingProfile V A) (v : V) (fake : StrictPref A),
    let P' := fun w : V => if w = v then fake else P w
    ¬ ∃ cr cf : A,
      f P cr ∧ f P' cf ∧ (P v).lt cf cr

#check @SatisfiesPareto
#check @SatisfiesUnanimity
#check @IsStrategyproof""", "c09")

# ===== Cell 10: Interpretation =====
md("""### Interpretation des axiomes

| Axiome | Intuition | Exigence |
|--------|-----------|----------|
| **Pareto** | Unanimite : si tous preferent c a d, d est exclu | Minimal pour toute regle raisonnable |
| **Unanimite** | Si tous classent c premier, c doit gagner | Plus fort que Pareto |
| **Non-manipulabilite** | Aucun electeur ne peut ameliorer le resultat en mentant | Equilibre strategique |

Ces trois axiomes semblent naturels et faibles. Pourtant, le theoreme de Gibbard-Satterthwaite montre qu'ils sont **incompatibles** avec la non-dictature pour >= 3 candidats.""", "c10")

# ===== Cell 11: Section 4 intro =====
md("""---

## 4. Theoreme de Gibbard-Satterthwaite

Le resultat central de la theorie du choix social : toute regle de vote resolutive, unanime et non-manipulable (pour >= 3 candidats) doit etre une dictature. Ce theoreme montre que **toute election est manipulable** (sauf dictature).

La preuve formelle dans Peters fait 5 fichiers Lean (BaseCase + Common + InductionStepCase1 + InductionStepCase2 + Main), avec une induction forte sur le nombre d'electeurs.""", "c11")

# ===== Cell 12: Gibbard-Satterthwaite =====
lean4("""-- Dictatorial (for resolute rules): one voter's preference determines the winner
def IsDictatorialRule {V A : Type} (f : VotingRule V A) : Prop :=
  ∃ d : V, ∀ P c, f P c → ∀ d' : A, d' ≠ c → (P d).lt c d'

/-- **Gibbard-Satterthwaite (1973/1975)**
    Toute regle resolutive, unanime et non-manipulable (>= 3 candidats)
    est dictatoriale.

    Preuve par induction forte sur le nombre d'electeurs :
    - Base (1 electeur) : trivialement dictatorial
    - Induction : clonage d'un electeur, application de l'hypothese de recurrence
    - Full proof: SocialChoice.Impossibilities.GibbardSatterthwaite -/
theorem gibbard_satterthwaite_sketch
    {V A : Type} [DecidableEq A] [Inhabited V] [Inhabited A]
    (f : VotingRule V A)
    (hf_res : IsResolute f)
    (hf_unan : SatisfiesUnanimity f)
    (hf_sp : IsStrategyproof f)
    (h_three : ∃ a b c : A, a ≠ b ∧ b ≠ c ∧ a ≠ c) :
    IsDictatorialRule f := by
  sorry

#check @gibbard_satterthwaite_sketch""", "c12")

# ===== Cell 13: Interpretation =====
md("""### Interpretation

Le theoreme de Gibbard-Satterthwaite a des implications profondes :

1. **Toute election est manipulable** : si la regle n'est pas une dictature, il existe toujours une situation ou un electeur a interet a mentir sur ses preferences
2. **La non-manipulabilite est une chimere** : meme les regles les plus sophistiquees (IRV, Borda, Copeland...) sont manipulables
3. **Le choix du systeme de vote est un compromis** : on choisit quelles proprietes sacrifier

### Structure de la preuve (Peters)

La preuve formelle suit l'approche classique par contraposition :
1. On suppose la regle resolutive, unanime, non-manipulable et non-dictatoriale
2. On montre l'existence d'un "pivot" (electeur dont le vote est critique)
3. Par induction sur le nombre d'electeurs, on construit une contradiction

> **Preuve complete** : `SocialChoice.Impossibilities.GibbardSatterthwaite.Main` dans `social_choice_lean_peters/`""", "c13")

# ===== Cell 14: Section 5 intro =====
md("""---

## 5. Impossibilites de Condorcet

DominikPeters formalise 4 theoremes d'impossibilite lies a Condorcet. Chacun montre que la coherence de Condorcet entre en conflit avec un autre axiome naturel :

1. **Condorcet + Participation** => Impossible (Moulin 1988)
2. **Condorcet + Renforcement** => Impossible (Young 1975)
3. **Condorcet + Non-manipulabilite** => Impossible
4. **Anonymat + Neutralite + Resolutude** => Impossible (nombre pair)""", "c14")

# ===== Cell 15: Condorcet impossibilities =====
lean4("""-- Condorcet impossibilities: Condorcet consistency + natural axiom => contradiction
-- All formalized in SocialChoice.Impossibilities.* (Peters project)

-- Key result: if a rule is Condorcet consistent, resolute and strategyproof,
-- it cannot exist (for >= 3 alternatives)
theorem condorcet_strategyproof_impossible_sketch
    {V A : Type} [DecidableEq A]
    (f : VotingRule V A)
    (margin : VotingProfile V A → MarginFun A)
    (hf_res : IsResolute f)
    (hf_cc : CondorcetConsistent f margin)
    (hf_sp : IsStrategyproof f)
    (h_three : ∃ a b c : A, a ≠ b ∧ b ≠ c ∧ a ≠ c) :
    False := by
  sorry

-- No-show paradox: adding voters who rank c first can make c lose
-- Formalized in SocialChoice.Impossibilities.CondorcetParticipation
-- (Moulin 1988)

-- Reinforcement: if disjoint electorates agree, the union should agree
-- Incompatible with Condorcet consistency
-- Formalized in SocialChoice.Impossibilities.CondorcetReinforcement
-- (Young 1975)

#check @condorcet_strategyproof_impossible_sketch""", "c15")

# ===== Cell 16: Interpretation =====
md("""### Interpretation des impossibilites de Condorcet

| Impossibilite | Axiomes | Resultat | Reference |
|---------------|---------|----------|-----------|
| Moulin 1988 | Condorcet + Participation | No-show paradox | `CondorcetParticipation` |
| Young 1975 | Condorcet + Renforcement | Incoherence inter-groupes | `CondorcetReinforcement` |
| General | Condorcet + Strategyproof | Manipulable | `CondorcetStrategyproofness` |
| ANR | Anonymat + Neutralite + Resolutude | Impossible (pair) | `AnonymousNeutralResolute` |

Le **no-show paradox** (Moulin 1988) est particulierement frappant : ajouter des electeurs qui classent votre candidat en tete peut le faire perdre ! Cela signifie que ne pas voter peut etre une meilleure strategie que de voter.

Ces resultats montrent que la **coherence de Condorcet** est une condition forte qui exclut de nombreuses proprietes desiderables.""", "c16")

# ===== Cell 17: Section 6 intro =====
md("""---

## 6. Split Cycle (Holliday & Pacuit 2023)

La regle Split Cycle est un cas particulier dans la theorie du choix social : c'est la regle la plus fine qui soit coherente avec Condorcet et acyclique. Elle resout le probleme des cycles de Condorcet en "affaiblissant" les marges dans les cycles.""", "c17")

# ===== Cell 18: Split Cycle =====
lean4("""-- Split Cycle (Holliday & Pacuit 2023)
-- The finest Condorcet-consistent, acyclic voting rule

-- Simplified: x defeats y if margin(x,y) > 0
-- and no blocking cycle exists (simplified to 3-cycles here)
-- In Peters: arbitrary-length cycles via List A

variable {A : Type}

-- Blocking cycle (simplified to 3-cycles)
-- A 3-cycle z -> x -> y -> z blocks x -> y if margins are >= margin(x,y)
def HasNoBlockingCycle (m : MarginFun A) (x y : A) : Prop :=
  ¬ ∃ z : A, m z x ≥ m x y ∧ m y z ≥ m x y ∧ z ≠ x ∧ z ≠ y

-- Split Cycle defeat: positive margin + no blocking cycle
def SCSimpleDefeat (m : MarginFun A) (x y : A) : Prop :=
  m x y > 0 ∧ HasNoBlockingCycle m x y

-- Split Cycle winners: undefeated alternatives
def SplitCycleWinners (m : MarginFun A) : A → Prop :=
  fun x => ∀ y, ¬ SCSimpleDefeat m y x

#check @HasNoBlockingCycle
#check @SCSimpleDefeat
#check @SplitCycleWinners""", "c18")

# ===== Cell 19: Interpretation =====
md("""### Interpretation de Split Cycle

L'idee cle de Split Cycle est d'**affaiblir les relations de defaite** : on ne retient la defaite de x sur y que si aucune marge dans un cycle contenant x et y n'est >= la marge de x sur y.

**Intuition** : si la marge de x sur y est 3, mais qu'il existe un cycle x -> y -> z -> x avec des marges >= 3, alors la defaite de x sur y est "bloquee" par le cycle. On ne peut pas affirmer que x bat y sans affirmer simultanement que y bat z et z bat x.

### Axiomes verifiees pour Split Cycle (Peters)

| Axiome | Statut | Fichier |
|--------|--------|---------|
| Condorcet Consistency | Prouve | `SplitCycle/Condorcet.lean` |
| Monotonicite | Prouve | `SplitCycle/Monotonicity.lean` |
| Pareto | Prouve | `SplitCycle/Pareto.lean` |
| Neutrite | Prouve | `SplitCycle/Neutrality.lean` |
| Smith | Prouve | `SplitCycle/Smith.lean` |
| Clones | Prouve | `SplitCycle/Clones.lean` |
| Independance | Prouve | `SplitCycle/Independence.lean` |
| Renversement | Prouve | `SplitCycle/Reversal.lean` |

Split Cycle est unique : c'est la regle la plus fine satisfaisant Condorcet + acyclicite + une autre propriete naturelle (voir Holliday & Pacuit 2023 pour les details).""", "c19")

# ===== Cell 20: Rules comparison table =====
md("""---

## 7. Regles de Vote Formalisees

DominikPeters verifie systematiquement les axiomes pour 15+ regles de vote, grace au meta-framework `@[scAxiom]` / `@[scRule]`.

### Tableau comparatif des regles

| Regle | Axiomes verifiees |
|-------|-------------------|
| **Split Cycle** | Condorcet, Monotonicity, Pareto, Neutrality, Smith, Clones, Reversal, Independence |
| **Schulze** | Condorcet, Monotonicity, Neutrality, Smith, Clones, Reversal, Transitivity |
| **Black** | Condorcet, Monotonicity, Neutrality, Pareto, Reversal, Smith |
| **Copeland** | Condorcet, Monotonicity, Neutrality, Pareto, Reversal, Smith |
| **Minimax** | Condorcet, Monotonicity, Neutrality, Pareto, Reversal, Majority |
| **Borda** | Monotonicity, Neutrality, Pareto, Participation, Reinforcement |
| **Plurality** | Monotonicity, Majority |
| **IRV** | CondorcetLoser, Majority, MutualMajority, Clones |
| **Baldwin** | Condorcet, CondorcetLoser, Smith |
| **Coombs** | Condorcet, CondorcetLoser, Majority |
| **Top Cycle** | Condorcet, Monotonicity, Smith, MutualMajority |
| **Uncovered Set** | Condorcet, Monotonicity, Neutrality, Smith, Clones |

**12 regles, 14 axiomes distincts**. Chaque verification est une preuve formelle en Lean 4.""", "c20")

# ===== Cell 21: Section 8 intro =====
md("""---

## 8. Theoreme de Duggan-Schwartz

Le theoreme de Duggan-Schwartz etend Gibbard-Satterthwaite aux **regles multi-gagnants** (qui peuvent selectionner plusieurs candidats). Il utilise deux notions de non-manipulabilite : optimiste et pessimiste.""", "c21")

# ===== Cell 22: Duggan-Schwartz =====
lean4("""-- Duggan-Schwartz: extension to multi-winner rules

-- Optimist strategyproof: can't improve best possible outcome
def IsOptimistSP {V A : Type} [DecidableEq A] (f : VotingRule V A) : Prop :=
  ∀ (P : VotingProfile V A) (v : V) (fake : StrictPref A),
    let P' := fun w : V => if w = v then fake else P w
    ¬ ∃ y, f P' y ∧ ∀ x, f P x → (P v).lt y x

-- Pessimist strategyproof: can't improve worst possible outcome
def IsPessimistSP {V A : Type} [DecidableEq A] (f : VotingRule V A) : Prop :=
  ∀ (P : VotingProfile V A) (v : V) (fake : StrictPref A),
    let P' := fun w : V => if w = v then fake else P w
    ¬ ∃ x, f P x ∧ ∀ y, f P' y → (P v).lt y x

/-- **Duggan-Schwartz (2000)**: A non-trivial, surjective voting rule
    satisfying both optimist and pessimist strategyproofness
    has a "nominating set" (coalition of <= 3 voters controlling outcome).
    Full proof: SocialChoice.Impossibilities.DugganSchwartz -/
theorem duggan_schwartz_sketch
    {V A : Type} [DecidableEq A] [Inhabited V] [Inhabited A]
    (f : VotingRule V A)
    (hf_opt : IsOptimistSP f)
    (hf_pess : IsPessimistSP f)
    (h_three : ∃ a b c : A, a ≠ b ∧ b ≠ c ∧ a ≠ c) :
    ∃ (G : V → Prop), True := by sorry

#check @IsOptimistSP
#check @IsPessimistSP
#check @duggan_schwartz_sketch""", "c22")

# ===== Cell 23: Interpretation =====
md("""### Interpretation de Duggan-Schwartz

Le theoreme de Duggan-Schwartz montre que meme les regles multi-gagnants sont vulnerables :

- **Manipulation optimiste** : un electeur peut ameliorer le **meilleur** candidat elu en mentant
- **Manipulation pessimiste** : un electeur peut ameliorer le **pire** candidat elu en mentant
- Si une regle est non-triviale et surjective, elle doit avoir un "nominating set" (petite coalition controlant le resultat)

Ce theoreme est plus general que Gibbard-Satterthwaite : il s'applique meme aux regles qui peuvent eligir plusieurs candidats.""", "c23")

# ===== Cell 24: Synthesis =====
md("""---

## 9. Synthese

### Contributions de DominikPeters/SocialChoiceLean

1. **Couverture** : La plus grande bibliotheque de theorie du choix social en Lean 4
2. **Praticite** : 15+ regles de vote directement testables avec des marges calculables
3. **Meta-framework** : `@[scAxiom]` et `@[scRule]` permettent une verification systematique
4. **Preuves constructives** : Les impossibilites exhibent des contre-exemples

### Integration avec notre travail (16b)

| Notre depot (16b) | DominikPeters (16e) | Relation |
|-------------------|---------------------|----------|
| Arrow.lean (Geanakoplos 2005) | Pas de preuve d'Arrow directe | Complementaire |
| Sen.lean (1970) | Pas de preuve de Sen | Complementaire |
| Voting.lean (Median voter, Condorcet) | Condorcet axioms, Split Cycle | Complementaire |
| - | Gibbard-Satterthwaite | Reference |
| - | 15+ voting rules | Reference |

### Definitions cles

| Concept | Definition Lean |
|---------|----------------|
| Preference stricte | `StrictPref A` avec `lt`, `irrefl`, `trans`, `conn` |
| Profil | `VotingProfile V A := V -> StrictPref A` |
| Regle | `VotingRule V A := Profile -> (A -> Prop)` |
| Condorcet winner | `IsCondorcetWinner m c` : marge positive sur tous |
| Split Cycle | `SplitCycleWinners m` : undefeated |

### References

- DominikPeters, *SocialChoiceLean*, https://github.com/DominikPeters/SocialChoiceLean (MIT)
- Gibbard, A. (1973). "Manipulation of Voting Schemes"
- Satterthwaite, M. (1975). "Strategy-proofness and Arrow's conditions"
- Holliday, W. & Pacuit, E. (2023). "Split Cycle: A New Condorcet Consistent Voting Method"
- Schulze, M. (2011). "A new monotonic, clone-independent, reversal symmetric, and Condorcet-consistent single-winner election method"
- Moulin, H. (1988). "Condorcet's principle implies the no show paradox"
- Young, H.P. (1975). "Social choice scoring functions"
- Duggan, J. & Schwartz, T. (2000). "Strategic manipulability without resoluteness"

---

**Navigation** : [16b-Lean-SocialChoice](GameTheory-16b-Lean-SocialChoice.ipynb) | [16c-Python](GameTheory-16c-SocialChoice-Python.ipynb) | [16d-SAT](GameTheory-16d-SocialChoice-SAT.ipynb) | **16e-PetersTour**""", "c24")

# Build notebook
nb = {
    "cells": cells,
    "metadata": {
        "kernelspec": {
            "display_name": "Lean 4 (WSL)",
            "language": "lean4",
            "name": "lean4-wsl"
        },
        "language_info": {
            "name": "lean4",
            "version": "4.28.0"
        }
    },
    "nbformat": 4,
    "nbformat_minor": 5
}

output_path = sys.argv[1] if len(sys.argv) > 1 else "GameTheory-16e-SocialChoiceLean-Tour.ipynb"
with open(output_path, 'w', encoding='utf-8') as f:
    json.dump(nb, f, indent=1, ensure_ascii=False)

print(f"Generated {len(cells)} cells -> {output_path}")
