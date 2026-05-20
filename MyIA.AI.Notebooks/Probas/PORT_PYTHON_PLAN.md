# Infer.NET → Python Port Plan

**Issue**: #297
**Status**: Research phase
**Author**: po-2025 (Cycle 22, Track 3)
**Date**: 2026-05-11

## Context

20 Infer.NET (.NET Interactive / C#) notebooks covering probabilistic programming from fundamentals to decision theory. Goal: create Python equivalents using modern probabilistic programming libraries, making the content accessible without .NET dependency.

An existing Python notebook `Pyro_RSA_Hyperbole.ipynb` (13/13 exec) demonstrates Pyro usage in this repo.

## Library Recommendation

| Library | Strengths | Weaknesses | Verdict |
|---------|-----------|------------|---------|
| **PyMC v5+** | NUTS sampler, intuitive `Model()` context, ArviZ viz, best docs | Slow for large models, no VI-native feel | **Primary** for notebooks 1-8, 14-20 |
| **NumPyro** | JAX-fast HMC/NUTS + SVI, scales well, Pyro-compatible | JAX complexity, less intuitive API | **Primary** for notebooks 9-12 (LDA, HMM, large models) |
| **pgmpy** | Bayesian network primitives (CPT, D-separation, inference) | Limited to discrete BNs | Supplementary for notebook 4 |
| **hmmlearn** | HMM fit/predict/score out of the box | No Bayesian treatment of params | Supplementary for notebook 11 |
| **Pyro** | General PPL, SVI, guide architecture | Lower-level than PyMC | Existing dependency, used for RSA notebook |

**Recommendation**: **PyMC v5+** as primary (covers 16/20 notebooks natively), **NumPyro** for advanced models (LDA, HMM), **pgmpy** for BN foundations.

## Notebook Mapping

### Phase 1: Fundamentals (Notebooks 1-3) — PyMC

| # | Infer Notebook | Pattern | Python Lib | Effort | Key API Translation |
|---|---------------|---------|-----------|--------|---------------------|
| 1 | Setup (Two Coins) | Beta-Bernoulli conjugate | PyMC | 2h | `Variable.Bernoulli` → `pm.Bernoulli`, `InferenceEngine` → `pm.sample()` |
| 2 | Gaussian Mixtures | GMM, conjugate priors, `Variable.Switch` | PyMC + sklearn | 4h | `Variable.Switch` → `pm.Mixture` or `pm.Categorical` weight indexing |
| 3 | Factor Graphs | Discrete inference, Monty Hall | PyMC | 3h | `Variable.If/Case` → `pm.math.switch`, `pt.where` |

### Phase 2: Classical Models (Notebooks 4-6) — PyMC + pgmpy

| # | Infer Notebook | Pattern | Python Lib | Effort | Key API Translation |
|---|---------------|---------|-----------|--------|---------------------|
| 4 | Bayesian Networks | CPT, D-separation, do-calculus | pgmpy + PyMC | 5h | `Variable.Case` CPT → `pgmpy.factors.discrete.TabularCPD`, D-sep → `pgmpy.independence` |
| 5 | Skills IRT | IRT, DINA, Q-matrix | PyMC | 5h | `Variable.Gaussian` for ability → `pm.Normal`, DINA → `pm.Deterministic` with `pt.prod` |
| 6 | TrueSkill | Gaussian ranking, online learning | PyMC | 4h | `ConstrainBetween` → `pm.Potential` or `pm.Normal` with ordered transform |

### Phase 3: Classification & Selection (Notebooks 7-8) — PyMC

| # | Infer Notebook | Pattern | Python Lib | Effort | Key API Translation |
|---|---------------|---------|-----------|--------|---------------------|
| 7 | Classification | Bayes Point Machine, A/B test | PyMC + scipy | 4h | BPM → `pm.Bernoulli` with `pm.math.invprobit`, A/B → `pm.Beta` comparison |
| 8 | Model Selection | Evidence, Bayes Factor, ARD | PyMC + ArviZ | 4h | Evidence → `pm.compute_log_marginal_likelihood`, ARD → `pm.Horseshoe` or sparse prior |

### Phase 4: Advanced Models (Notebooks 9-12) — NumPyro

| # | Infer Notebook | Pattern | Python Lib | Effort | Key API Translation |
|---|---------------|---------|-----------|--------|---------------------|
| 9 | Topic Models (LDA) | Dirichlet-Multinomial, VMP | NumPyro | 6h | `Variable.Dirichlet` → `numpyro.distributions.Dirichlet`, SVI + guide |
| 10 | Crowdsourcing | Worker models, communities | NumPyro | 5h | Biased Worker confusion matrix → `numpyro.plates` + categorical |
| 11 | Sequences (HMM) | HMM, Forward-Backward | hmmlearn + NumPyro | 5h | Manual Forward-Backward with `numpyro.scan` or `hmmlearn.GaussianHMM` |
| 12 | Recommenders | Matrix factorization, Click Model | NumPyro | 5h | `Variable.Array` traits → `numpyro.sample` with `numpyro.plate` |

### Phase 5: Reference (Notebook 13) — PyMC/NumPyro

| # | Infer Notebook | Pattern | Python Lib | Effort | Key API Translation |
|---|---------------|---------|-----------|--------|---------------------|
| 13 | Debugging | Diagnostics, EP vs VMP comparison | ArviZ + PyMC | 3h | EP/VMP → NUTS/ADVI comparison, `arviz.plot_trace`, `az.summary` |

### Phase 6: Decision Theory (Notebooks 14-20) — PyMC + numpy

| # | Infer Notebook | Pattern | Python Lib | Effort | Key API Translation |
|---|---------------|---------|-----------|--------|---------------------|
| 14 | Decision Foundations | Lotteries, VNM axioms, utility | numpy + scipy | 3h | Mostly numpy/math, `scipy.optimize` for calibration |
| 15 | Utility of Money | St-Petersburg, CARA/CRRA | numpy + scipy | 3h | Utility functions as numpy arrays, Monte Carlo |
| 16 | Multi-Attribute | MAUT, SMART, swing weights | numpy + scipy | 3h | Weighted sum, sensitivity analysis |
| 17 | Decision Networks | Influence diagrams | pgmpy + numpy | 4h | `pgmpy.models.BayesianNetwork` + decision nodes |
| 18 | Value of Information | EVPI, EVSI | PyMC + numpy | 3h | Pre-posterior analysis via `pm.sample_posterior_predictive` |
| 19 | Expert Systems | Minimax, regret | numpy + scipy | 3h | Decision matrix operations |
| 20 | Sequential Decisions | MDPs, Value/Policy iteration | numpy | 3h | Bellman equation iteration (pure numpy) |

## Effort Summary

| Phase | Notebooks | Estimated Hours | Library |
|-------|-----------|----------------|---------|
| 1: Fundamentals | 1-3 | 9h | PyMC |
| 2: Classical | 4-6 | 14h | PyMC + pgmpy |
| 3: Classification | 7-8 | 8h | PyMC |
| 4: Advanced | 9-12 | 21h | NumPyro |
| 5: Reference | 13 | 3h | ArviZ |
| 6: Decision Theory | 14-20 | 22h | numpy + PyMC |
| **Total** | **20** | **~77h** | |

## Key API Translation Reference

### Infer.NET → PyMC

| Infer.NET | PyMC v5+ | Notes |
|-----------|----------|-------|
| `Variable.Bernoulli(p)` | `pm.Bernoulli('x', p=p)` | Direct |
| `Variable.GaussianFromMeanAndVariance(m, v)` | `pm.Normal('x', mu=m, sigma=pt.sqrt(v))` | Note sigma vs variance |
| `Variable.GaussianFromMeanAndPrecision(m, p)` | `pm.Normal('x', mu=m, tau=p)` | PyMC supports tau param |
| `Variable.Beta(a, b)` | `pm.Beta('x', alpha=a, beta=b)` | Direct |
| `Variable.Dirichlet(a)` | `pm.Dirichlet('x', a=a)` | Direct |
| `Variable.Gamma(s, r)` | `pm.Gamma('x', alpha=s, beta=r)` | Note rate vs scale |
| `Variable.Discrete(probs)` | `pm.Categorical('x', p=probs)` | Discrete → Categorical |
| `Variable.Switch(idx, values)` | `pm.Mixture('x', w=w, comp=components)` | Or `pt.switch` |
| `Variable.If(cond) { ... }` | `pm.math.switch(cond, then, else)` | PyTensor op |
| `VariableArray<T>(range)` | `pm.Normal('x', ..., shape=N)` | shape parameter |
| `observed.ObservedValue(data)` | `pm.Normal('x', ..., observed=data)` | observed kwarg |
| `InferenceEngine(EP)` | `pm.sample(draws=1000)` | NUTS by default |
| `InferenceEngine(VMP)` | `pm.fit(method='advi')` | ADVI approximation |
| `engine.Infer<Gaussian>(x)` | `trace.posterior['x']` | ArviZ InferenceData |

### Infer.NET → NumPyro

| Infer.NET | NumPyro | Notes |
|-----------|---------|--------|
| `Variable.Dirichlet` in plate | `numpyro.sample('theta', dist.Dirichlet(a), sample_intermediates=True)` | |
| `Variable.Discrete` with plate | `numpyro.sample('z', dist.Categorical(probs), with numpyro.plate(...))` | |
| VMP iteration | `numpyro.infer.SVI(model, guide, optim, loss=Trace_ELBO())` | |
| `Range` | `numpyro.plate('name', size)` | Context manager |

## Scaffolding Priority

**Sprint 1** (easiest wins, builds foundation):
1. `Infer-1-Setup` → `PyMC-1-Setup` (2h)
2. `Infer-3-Factor-Graphs` → `PyMC-3-Factor-Graphs` (3h)

These two cover the fundamental workflow (model → sample → posterior) and discrete inference (Monty Hall), providing a template for all subsequent notebooks.

**Sprint 2** (highest pedagogical value):
3. `Infer-4-Bayesian-Networks` → `PyMC-4-Bayesian-Networks` (5h)
4. `Infer-2-Gaussian-Mixtures` → `PyMC-2-Gaussian-Mixtures` (4h)

## Dependencies

```
# requirements-python-port.txt
pymc>=5.10           # Primary PPL (NUTS, ADVI, posterior predictive)
arviz>=0.17          # Visualization + diagnostics
numpyro>=0.13        # JAX backend for advanced models
jax>=0.4             # NumPyro backend
pgmpy>=0.9           # Bayesian network primitives
hmmlearn>=0.3        # HMM fit/predict
scipy>=1.11          # Optimization, stats
matplotlib>=3.7      # Plotting
seaborn>=0.13        # Statistical viz
numpy>=1.24          # Core
pandas>=2.0          # Data handling
```

All CPU-only, no GPU required.

## Naming Convention

- Directory: `MyIA.AI.Notebooks/Probas/_python_port/`
- Files: `PyMC-{N}-{Title}.ipynb` for PyMC-based, `NumPyro-{N}-{Title}.ipynb` for NumPyro-based
- Data: reuse `Infer/data/` CSV/JSON files directly (same datasets)
- Kernel: `python3`

## Open Questions

1. **Decision theory notebooks (14-20)**: These are mostly math/numpy, not PPL. Should they use PyMC at all, or stay pure numpy? Recommendation: numpy + scipy for 14-16,19-20; PyMC for 17 (decision networks) and 18 (EVPI/EVSI).
2. **LDA (notebook 9)**: NumPyro SVI is complex. Alternative: use `gensim` or `sklearn.decomposition.LatentDirichletAllocation` for comparison, then show NumPyro for Bayesian treatment.
3. **Exercise parity**: Should Python notebooks have exact same exercises as C# originals, or adapt to Python idioms? Recommendation: same concepts, Python-idiomatic implementations.
