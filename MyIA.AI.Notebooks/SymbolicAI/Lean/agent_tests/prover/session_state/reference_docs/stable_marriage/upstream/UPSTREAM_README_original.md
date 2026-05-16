# Stable Marriage Problem in Lean

Formalizing the stable marriage problem and the Gale-Shapley algorithm in Lean.

The stable marriage problem asks for a matching between two sets of agents (say, men and women) that respects their preferences, in a precise sense ("stability"). The algorithm for it, the _deferred acceptance_ algorithm, developed by Gale and Shapley, is perhaps one of the most successful examples of market design in the real world, and is today used to, e.g., match medical residents, students to high schools, etc.

The famous paper [College admissions and the stability of marriage](https://sites.math.washington.edu/~billey/classes/562.winter.2018/articles/Gale.Shapley.pdf) by Gale and Shapley (1962) introduced the problem and is extremely readable. They also develop the deferred acceptance algorithm in it.

For a rigorous theoretical treatment of the problem and its many extensions, see _Two-Sided Matching: A Study in Game-Theoretic Modeling and Analysis_ by Roth and Sotomayor (1990) (e.g., Gale-Shapley do not consider incomplete preferences, whereas this is covered in Roth-Sotomayor, and indeed this formalization uses that setup).

## Project organization

- `StableMarriageLean/Basic.lean`: core definitions (preferences, matchings, stability).
- `StableMarriageLean/GaleShapley.lean`: Gale-Shapley state machine and algorithm.
- `StableMarriageLean/Lemmas.lean`: supporting lemmas and invariants.
- `StableMarriageLean/Properties.lean`: main results about termination and stability.
- `StableMarriageLean.lean`: root module that re-exports the library.
- `Main.lean`: small entry point for the executable.

## Theory

### 1. Agents and Preferences

We have two disjoint finite sets:

- $M$: men
- $W$: women

Each agent $a \in M \cup W$ has a **strict preference ordering** over a _subset_ of the opposite side (i.e., preferences are incomplete -- in other words, it is not a total order). Each man $m$ has a preference ordering $P_m$ and each woman $w$ has a preference ordering $P_w$. We will denote "prefers to" by $\succ$, indexed by the agent when needed. We do not consider ties here, although there is a generalization to ties in the literature.

### 2. Acceptability

A pair $(m, w) \in M \times W$ is **acceptable** iff:

$$
w \in P_m \quad \text{and} \quad m \in P_w
$$

If either side does not list the other, the pair is **unacceptable**.

Unacceptable partners are treated as **worse than being unmatched**.

### 3. Matchings

A **matching** $\mu$ is a partial function:

$$
\mu : M \cup W \to M \cup W \cup \{\varnothing\}
$$

such that:

- $\mu(m) \in W \cup \{\varnothing\}$
- $\mu(w) \in M \cup \{\varnothing\}$
- $\mu(m) = w \iff \mu(w) = m$ (consistency)
- Each agent is matched with **at most one** partner

Agents mapped to $\varnothing$ are **unmatched**.

In Lean, we represent a matching as two functions (menMatches and womenMatches),
and add a consistency predicate to recover this single-function view.

### 4. Individual Rationality

A matching $\mu$ is **individually rational** iff:

$$
\forall a,\; \mu(a) \in P_a \cup \{\varnothing\}
$$

In other words, no agent is matched to an unacceptable partner.

### 5. Preference Over Being Unmatched

For every agent $a$:

$$
\text{any acceptable partner } \succ \varnothing
$$

Being unmatched is worse than any acceptable match.

### 6. Blocking Pairs

A pair $(m, w)$ is a **blocking pair** for a matching $\mu$ iff:

1. $(m, w)$ is acceptable
2. $m$ prefers $w$ to $\mu(m)$
3. $w$ prefers $m$ to $\mu(w)$

Formally:

$$
w \succ_m \mu(m) \quad \text{and} \quad m \succ_w \mu(w)
$$

This includes cases where one or both agents are currently unmatched.

### 7. Stability

A matching $\mu$ is **stable** iff:

1. It is **consistent**,
2. It is **individually rational**, and
3. It has **no blocking pairs**

### 8. Gale-Shapley algorithm

Gale and Shapley (1962) gave a beautiful algorithm, the deferred acceptance algorithm, which they prove yields a stable matching. The proof is quite short and extremely intuitive. (The formalization is of course much more difficult than their elegant proof.)
