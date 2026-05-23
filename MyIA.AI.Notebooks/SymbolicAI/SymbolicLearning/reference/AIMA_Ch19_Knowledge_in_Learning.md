# Chapter 19 — Knowledge in Learning

**Source**: Artificial Intelligence: A Modern Approach, 3rd Edition (Russell & Norvig), Chapter 19, pp. 768-801.

---

## 19.1 A Logical Formulation of Learning

Chapter 18 defined pure inductive learning as a process of finding a hypothesis that agrees with the observed examples. Here, we specialize this definition to the case where the hypothesis is represented by a set of logical sentences. Example descriptions and classifications will also be logical sentences, and a new example can be classified by inferring a classification sentence from the hypothesis and the example description.

### 19.1.1 Examples and hypotheses

Recall from Chapter 18 the restaurant learning problem: learning a rule for deciding whether to wait for a table. Examples were described by attributes such as `Alternate`, `Bar`, `Fri/Sat`, and so on. In a logical setting, an example is described by a logical sentence; the attributes become unary predicates. Let us generically call the ith example Xi. For instance, the first example from Figure 18.3 (page 700) is described by the sentences:

```
Alternate(X1) ∧ ¬Bar(X1) ∧ ¬Fri/Sat(X1) ∧ Hungry(X1) ∧ ...
```

We will use the notation Di(Xi) to refer to the description of Xi, where Di can be any logical expression taking a single argument. The classification of the example is given by a literal using the goal predicate, in this case `WillWait(X1)` or `¬WillWait(X1)`.

The aim of inductive learning in general is to find a hypothesis that classifies the examples well and generalizes well to new examples. Here we are concerned with hypotheses expressed in logic; each hypothesis hj will have the form:

```
∀x Goal(x) ⇔ Cj(x)
```

where Cj(x) is a candidate definition — some expression involving the attribute predicates. For example, the decision tree in Figure 18.6 (page 702) expresses:

```
∀r WillWait(r) ⇔ Patrons(r,Some)
    ∨ Patrons(r,Full) ∧ Hungry(r) ∧ Type(r,French)
    ∨ Patrons(r,Full) ∧ Hungry(r) ∧ Type(r,Thai) ∧ Fri/Sat(r)
    ∨ Patrons(r,Full) ∧ Hungry(r) ∧ Type(r,Burger)       ... (19.1)
```

Each hypothesis predicts that a certain set of examples — namely, those that satisfy its candidate definition — will be examples of the goal predicate. This set is called the **extension** of the predicate. Two hypotheses with different extensions are therefore logically inconsistent with each other.

The hypothesis space H is the set of all hypotheses {h1, ..., hn} that the learning algorithm is designed to entertain. The learning algorithm believes that one of the hypotheses is correct:

```
h1 ∨ h2 ∨ h3 ∨ ... ∨ hn                          ... (19.2)
```

An example can be inconsistent with a hypothesis in two ways:

- **False negative**: The hypothesis says it should be negative but in fact it is positive. E.g., `Patrons(X13,Full) ∧ ¬Hungry(X13) ∧ ... ∧ WillWait(X13)` would be a false negative for hypothesis hr.
- **False positive**: The hypothesis says it should be positive but in fact it is negative.

If an example is a false positive or false negative for a hypothesis, then the example and the hypothesis are logically inconsistent. Assuming the example is correct, the hypothesis can be ruled out.

### 19.1.2 Current-best-hypothesis search

The idea behind current-best-hypothesis (CBH) search is to maintain a **single hypothesis**, and to adjust it as new examples arrive in order to maintain consistency. The basic algorithm was described by John Stuart Mill (1843).

When a **false negative** arrives, we must **generalize** the hypothesis (increase its extension to include the new positive example). When a **false positive** arrives, we must **specialize** the hypothesis (decrease its extension to exclude the new negative example).

**Algorithm: CURRENT-BEST-LEARNING**

```
function CURRENT-BEST-LEARNING(examples, h) returns a hypothesis or fail
    if examples is empty then return h
    e ← FIRST(examples)
    if e is consistent with h then
        return CURRENT-BEST-LEARNING(REST(examples), h)
    else if e is a false positive for h then
        for each h' in specializations of h consistent with examples seen so far do
            h'' ← CURRENT-BEST-LEARNING(REST(examples), h')
            if h'' ≠ fail then return h''
    else if e is a false negative for h then
        for each h' in generalizations of h consistent with examples seen so far do
            h'' ← CURRENT-BEST-LEARNING(REST(examples), h')
            if h'' ≠ fail then return h''
    return fail
```

**Generalization** means finding a definition C1 that is logically implied by C2. The simplest method is **dropping conditions**: e.g., `Alternate(x) ∧ Patrons(x,Some)` → `Patrons(x,Some)` (drop the Alternate condition).

**Specialization** means adding extra conditions or removing disjuncts to exclude a false positive.

**Worked example on restaurant data:**

- X1 positive → h1: `WillWait(x) ⇔ Alternate(x)`
- X2 negative, false positive → specialize: h2: `WillWait(x) ⇔ Alternate(x) ∧ Patrons(x,Some)`
- X3 positive, false negative → generalize (drop Alternate): h3: `WillWait(x) ⇔ Patrons(x,Some)`
- X4 positive, false negative → generalize (add disjunct): h4: `WillWait(x) ⇔ Patrons(x,Some) ∨ (Patrons(x,Full) ∧ Fri/Sat(x))`

**Difficulties:**
1. Checking all previous examples for each modification is expensive.
2. The search may involve a great deal of backtracking. Hypothesis space can be doubly exponentially large.

### 19.1.3 Least-commitment search (Version Space / Candidate Elimination)

Backtracking arises because CBH has to choose a particular hypothesis as its best guess even though it does not have enough data. Instead, we keep around **all and only those hypotheses that are consistent** with all the data so far.

The set of remaining hypotheses is called the **version space**. The algorithm is called the **candidate elimination** algorithm.

```
function VERSION-SPACE-LEARNING(examples) returns a version space
    V ← the set of all hypotheses
    for each example e in examples do
        if V is not empty then V ← VERSION-SPACE-UPDATE(V, e)
    return V
```

We represent the version space using two **boundary sets**:
- **G-set** (most general boundary): hypotheses consistent with all observations, with no consistent hypotheses more general.
- **S-set** (most specific boundary): hypotheses consistent with all observations, with no consistent hypotheses more specific.

Initial state: G = {True}, S = {False}.

**Key properties:**
1. Every consistent hypothesis is more specific than some G member and more general than some S member (no "stragglers").
2. Every hypothesis between S and G is consistent (no "holes").

**Update rules for each new example:**

1. **False positive for Si**: Si is too general → throw it out of S-set.
2. **False negative for Si**: Si is too specific → replace by all its immediate generalizations that are more specific than some G member.
3. **False positive for Gi**: Gi is too general → replace by all its immediate specializations that are more general than some S member.
4. **False negative for Gi**: Gi is too specific → throw it out of G-set.

**Termination:**
1. Exactly one hypothesis left → return it.
2. Version space collapses (S or G empty) → no consistent hypotheses.
3. Run out of examples with multiple hypotheses → disjunction; take majority vote if they disagree.

**Drawbacks:**
- Noise or insufficient attributes → version space always collapses.
- Unlimited disjunction → S-set = disjunction of positive examples, G-set = negation of disjunction of negative examples.
- S-set or G-set may grow exponentially in the number of attributes.

---

## 19.2 Knowledge in Learning

The modern approach: agents that already know something and are trying to learn some more (cumulative/incremental learning).

A Hypothesis that "explains the observations" must satisfy:

```
Hypothesis ∧ Descriptions |= Classifications                    ... (19.3)
```

This is an **entailment constraint**. Pure inductive learning = solving this constraint where Hypothesis is drawn from a predefined hypothesis space.

### 19.2.1 Some simple examples

- **Explanation-based learning (EBL)**: Leap to general conclusions after one observation (e.g., Zog's pointed stick). The entailment constraints are:
  ```
  Hypothesis ∧ Descriptions |= Classifications
  Background |= Hypothesis
  ```
  EBL doesn't learn factually new things — it converts first-principles theories into useful, special-purpose knowledge.

- **Relevance-based learning (RBL)**: Prior knowledge about relevance of features (e.g., nationality determines language). Constraints:
  ```
  Hypothesis ∧ Descriptions |= Classifications
  Background ∧ Descriptions ∧ Classifications |= Hypothesis    ... (19.4)
  ```
  RBL is deductive, cannot create genuinely new knowledge.

- **Knowledge-based inductive learning (KBIL)**: Background knowledge and new hypothesis combine to explain examples:
  ```
  Background ∧ Hypothesis ∧ Descriptions |= Classifications    ... (19.5)
  ```

---

## 19.3 Explanation-Based Learning (EBL)

EBL extracts general rules from **individual observations** by:
1. Constructing an explanation using prior knowledge
2. Establishing a definition of the class of cases where the same explanation structure applies

**Example**: Simplifying `1 × (0 + X)`. The knowledge base includes:
```
Rewrite(u, v) ∧ Simplify(v, w) ⇒ Simplify(u, w)
Primitive(u) ⇒ Simplify(u, u)
ArithmeticUnknown(u) ⇒ Primitive(u)
Rewrite(1 × u, u)
Rewrite(0 + u, u)
```

The EBL method constructs two proof trees simultaneously: one for the original goal, one with constants replaced by variables (variabilized). From the generalized proof tree, extract:

```
ArithmeticUnknown(z) ⇒ Simplify(1 × (0 + z), z)
```

**EBL process summary:**
1. Construct a proof that the goal predicate applies to the example.
2. In parallel, construct a generalized proof tree for the variabilized goal.
3. Construct a new rule from the leaves of the proof tree.
4. Drop conditions that are true regardless of variable values.

**Efficiency considerations**: Adding rules can slow reasoning (increased branching factor). Derived rules must offer significant speedup. Tradeoff between operationality (easy to solve) and generality (covers more cases).

---

## 19.4 Learning Using Relevance Information

**Determinations** express strict relevance: given one set of predicates, another is fully determined. Notation:

```
Nationality(x, n) > Language(x, l)
```

This means nationality determines language. From this and an observation about Fernando, one can deduce:

```
Nationality(x, Brazil) ⇒ Language(x, Portuguese)
```

**Effect on hypothesis space**: If determination has d predicates out of n total attributes, examples required drop from O(2^n) to O(2^d) — an exponential reduction.

**Learning determinations**: Find the simplest determination consistent with observations. Algorithm: MINIMAL-CONSISTENT-DET (search through subsets of attributes of increasing size).

**RBDTL** (Relevance-Based Decision Tree Learning): Combines MINIMAL-CONSISTENT-DET with DECISION-TREE-LEARNING. Learns faster than pure DTL when many attributes are irrelevant.

---

## 19.5 Inductive Logic Programming (ILP)

ILP combines inductive methods with the power of first-order representations, representing hypotheses as **logic programs**.

Advantages:
1. Rigorous approach to knowledge-based inductive learning
2. Can learn in domains where attribute-based algorithms fail (e.g., protein folding, relational problems)
3. Produces human-readable hypotheses

### 19.5.1 Example: Family relationships

Given a family tree with Mother, Father, Married, Male, Female relations, learn Grandparent:

```
Grandparent(x, y) ⇔ ∃z Parent(x, z) ∧ Parent(z, y)
```

With background knowledge `Parent(x,y) ⇔ Mother(x,y) ∨ Father(x,y)`, the hypothesis is much more compact.

**Constructive induction**: ILP algorithms can invent new predicates (e.g., "Parent") to simplify definitions.

### 19.5.2 Top-down methods: FOIL

FOIL starts with a very general rule and specializes it:
1. Begin with empty body: `⇒ Grandfather(x, y)`
2. Add literals one at a time to the body
3. Choose the literal that best separates positive from negative examples
4. Continue until the clause is consistent

Types of literals that can be added:
1. Predicates (existing or goal predicate — allows recursive definitions)
2. Equality/inequality literals
3. Arithmetic comparisons

Uses information gain heuristic + Ockham's razor to eliminate overcomplex clauses.

### 19.5.3 Bottom-up methods: Inverse resolution

If `Background ∧ Hypothesis ∧ Descriptions |= Classifications`, then one can prove this by resolution. **Inverse resolution** runs the proof backward to find the Hypothesis.

Each inverse resolution step is **nondeterministic** — many possible clauses C1, C2 that resolve to a given C. Search control strategies:
1. Eliminate redundant choices
2. Restrict proof strategy (e.g., linear resolution)
3. Restrict representation (Horn clauses, PROGOL with inverse entailment)
4. Model checking instead of theorem proving
5. Translate to propositional logic (LINUS)

### 19.5.4 Discoveries with ILP

Inverse resolution can **invent new predicates** — a literal eliminated during resolution may contain a predicate not in the resolvent. Working backward, one generates a new predicate to reconstruct it.

Notable applications:
- Protein folding rules (PROGOL, published in Journal of Molecular Biology)
- Mutagenicity of nitroaromatic compounds
- Functional genomics of yeast (robot scientist)
- Natural language processing

---

## 19.6 Summary

- **Prior knowledge** in learning → cumulative learning: agents improve their learning ability as they acquire more knowledge.
- Prior knowledge helps by eliminating consistent hypotheses and "filling in" explanations → shorter hypotheses, faster learning from fewer examples.
- **EBL**: Extracts general rules from single examples by explaining and generalizing. Deductive method for turning first-principles knowledge into efficient special-purpose expertise.
- **RBL**: Uses determinations to identify relevant attributes → reduced hypothesis space → faster learning.
- **KBIL/ILP**: Finds inductive hypotheses that explain observations with background knowledge. Can learn relational knowledge not expressible in attribute-based systems.
- ILP approaches: **top-down** (FOIL: refine general rules) or **bottom-up** (inverse resolution: invert deductive process).
- ILP methods naturally generate **new predicates** → show promise as general-purpose scientific theory formation systems.

---

## Key Algorithms Summary

| Algorithm | Type | Maintains | Key Operation |
|-----------|------|-----------|---------------|
| Current-Best-Learning | CBH search | Single hypothesis | Generalize/Specialize with backtracking |
| Version-Space-Learning | Candidate Elimination | G-set + S-set | Update boundaries for each example |
| EBL | Explanation-based | Proof trees | Generalize proof, extract rule |
| MINIMAL-CONSISTENT-DET | RBL | Minimal attribute set | Search subsets by size |
| FOIL | Top-down ILP | Horn clauses | Add literals to clause body |
| Inverse Resolution | Bottom-up ILP | Resolution proof | Invert resolution steps |
