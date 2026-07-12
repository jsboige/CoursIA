# Chapter 19 — Knowledge in Learning

**Reference**: Russell & Norvig, *Artificial Intelligence: A Modern Approach*, 3rd Edition, Chapter 19, pp. 768-801.

---

## Key Concepts

### 19.1 Learning as Logical Inference

In the logical framework for learning, examples and hypotheses are both expressed as logical sentences. An example is described by a conjunction of attribute predicates (e.g., `Alternate(X1) ∧ ¬Bar(X1) ∧ ...`), and classified by a goal predicate (e.g., `WillWait(X1)` or `¬WillWait(X1)`). A hypothesis maps descriptions to classifications via an equivalence: `∀x Goal(x) ⇔ Cj(x)`, where `Cj` is a candidate definition.

The hypothesis space H contains all candidates the learning algorithm considers. Two key types of inconsistency arise:
- **False negative**: the hypothesis excludes a positive example (too specific).
- **False positive**: the hypothesis includes a negative example (too general).

#### Current-Best-Hypothesis (CBH) Search

Maintain a single hypothesis and adjust it incrementally:
- On a **false negative** → **generalize** (e.g., drop a condition from the candidate definition).
- On a **false positive** → **specialize** (e.g., add a condition or remove a disjunct).

The algorithm backtracks when no consistent modification exists. The main difficulty is combinatorial explosion: the hypothesis space can be doubly exponential.

#### Version-Space Learning (Candidate Elimination)

Instead of committing to one hypothesis, maintain **all** consistent hypotheses using two boundary sets:
- **G-set** (most general): the most general hypotheses still consistent with observations.
- **S-set** (most specific): the most specific hypotheses still consistent with observations.

Every consistent hypothesis lies between S and G. Updates shrink the boundaries as new examples arrive. The version space collapses if noise or insufficient attributes make consistency impossible. May grow exponentially in the number of attributes.

### 19.2 Three Paradigms for Knowledge-Based Learning

The core entailment constraint for learning is: `Hypothesis ∧ Descriptions |= Classifications`. Three paradigms add background knowledge differently:

- **Explanation-Based Learning (EBL)**: The hypothesis is *deduced entirely from prior knowledge*. The agent constructs a proof explaining why an observation holds, then generalizes the proof structure. EBL converts first-principles reasoning into efficient special-purpose rules. It does not learn factually new information — it speeds up what the agent already knows in principle.

- **Relevance-Based Learning (RBL)**: Prior knowledge specifies *which features are relevant* (via determinations). For example, knowing that nationality determines language lets the agent generalize from a single example. RBL is deductive and cannot produce genuinely novel knowledge.

- **Knowledge-Based Inductive Learning (KBIL)**: Background knowledge and a new hypothesis *jointly* explain the observations: `Background ∧ Hypothesis ∧ Descriptions |= Classifications`. This is the most powerful paradigm — it requires genuine induction constrained by prior knowledge.

### 19.3 Explanation-Based Learning in Detail

EBL proceeds in three steps:
1. Construct a **proof tree** showing that the goal predicate applies to the example, using background knowledge.
2. In parallel, construct a **generalized proof tree** by replacing constants with variables (variabilization).
3. Extract a new rule from the leaves of the generalized proof tree, dropping conditions that are always satisfied.

The tradeoff is between **operationality** (rules easy to evaluate) and **generality** (rules covering more cases). Adding too many derived rules can slow reasoning by increasing the branching factor.

### 19.4 Relevance-Based Learning and Determinations

A **determination** `A > B` states that predicate A fully determines predicate B (e.g., `Nationality > Language`). This exponentially reduces the number of examples needed: if only d out of n attributes are relevant, the sample complexity drops from O(2^n) to O(2^d).

The **RBDTL** algorithm combines learning a determination (finding the minimal consistent attribute subset) with decision-tree learning, yielding faster convergence than pure DTL when many attributes are irrelevant.

### 19.5 Inductive Logic Programming (ILP)

ILP represents hypotheses as **logic programs** (sets of Horn clauses), combining inductive learning with the expressiveness of first-order logic. Key advantages over attribute-based learners:
- Can learn **relational** concepts (e.g., family trees, molecular structure).
- Produces human-readable hypotheses.
- Can **invent new predicates** not present in the original vocabulary.

#### Top-down: FOIL

Start with a very general clause and **specialize** by adding literals one at a time, selecting the literal with the highest information gain. Supports recursive definitions (the goal predicate can appear in the clause body). Uses Ockham's razor to penalize overly complex clauses.

#### Bottom-up: Inverse Resolution

Run the resolution proof **backward**: from the observed classification, reconstruct the Hypothesis that would produce it via resolution with the background knowledge. Each inverse resolution step is nondeterministic (many possible inverse clauses), requiring search-control heuristics.

**Predicate invention**: A literal eliminated during inverse resolution may contain a predicate absent from the resolvent — reconstructing it requires creating a new predicate, effectively allowing the system to invent theoretical terms.

### 19.6 Summary of Algorithms

| Approach | Direction | Key Idea |
|----------|-----------|----------|
| CBH Search | Incremental | Adjust single hypothesis (generalize/specialize) |
| Version Space | Boundary maintenance | Track all consistent hypotheses via G-set and S-set |
| EBL | Deductive | Generalize proof trees from single examples |
| RBL / Determinations | Relevance filtering | Reduce hypothesis space using prior knowledge about relevant features |
| FOIL | Top-down ILP | Specialize clauses by adding literals with info gain |
| Inverse Resolution | Bottom-up ILP | Reconstruct hypotheses by inverting resolution steps |

---

## Connections to the Notebooks

- **SL-1 (Logical Learning)**: Implements CBH search and version-space learning on the restaurant dataset (WillWait).
- **SL-2 (Knowledge-Based Learning)**: Explores EBL and KBIL paradigms, demonstrating how background knowledge accelerates learning.
