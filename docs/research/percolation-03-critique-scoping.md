# Percolation-03 critique — scoping du palier 3 (*finite-size scaling*)

> **Suite directe de [#19494](https://github.com/jsboige/CoursIA/issues/19494)** (plan de croissance 03 critique / 04 sharpness ×2). Scoping du carnet `Percolation-03-Critique-Python.ipynb` au pin `70ece81334` (main HEAD c.1103). L'exécution reste à arbitrer — voir §10.

## Sections (10)

1. Cible — quantifier le seuil fini `p_c(T_n)` et la loi de taille au point critique
2. Théorie de référence — exposants critiques 2D (`β/ν = 5/36`, `γ/ν = 43/18`, `1/ν = 3/4`) et universalité
3. Architecture pipeline — sweep `L × p × seeds`, instrument `networkx` (héritée de 01)
4. Budget runtime — ~30 min mono-thread pour `L ∈ {8, 16, 32, 64}` × `p ∈ {0.45, 0.48, 0.50, 0.52, 0.55}` × `seeds = 32`
5. **RÈGLE F** — NTL absente (Python pur, pas de Lean build), `networkx` installé OK
6. 4 smells — non-convergence BFS, dépassement mémoire `L=128`, ambiguïté seuil fini/infini, seed-fluctuation asymétrique
7. Comparaison vs vanilla — `networkx.connected_components` BFS + log-bin histogram, pas de dépendance hors-`networkx`
8. Livrable — `Percolation-03-Critique-Python.ipynb` (Carnet d'application), `docs/research/percolation-03-critique-results.md` (~250 l.), `example_results/p03_critique_validation.json`
9. Plan d'exécution 4 phases — A design cellules (15 min) + B exécution papermill (30 min) + C validation (10 min) + D rapport + PR (15 min). Total ~70 min wall-clock sur 1-2 cycles.
10. Recommandation — auto-suffisant localement (networkx OK, pas de NTL requise), peut être livré sans routage cross-machine.

---

## 1. Cible — quantifier le seuil fini `p_c(T_n)` et la loi de taille au point critique

Le carnet `Percolation-Supercritique.ipynb` (01) couvre les régimes `p < p_c` et `p > p_c` sur un **tore fini** `T_n = ℤ²/nℤ²`, avec un seuil de liens exact `p_c(bond, ℤ²) = 1/2` (Kesten). Il annonce le théorème de *supercritical sharpness* (Diskin-Easo-Radhakrishnan-Sudakov-Tassion, arXiv:2603.03257 §3.0) sans toutefois le **mesurer au point critique** lui-même.

**Ce que 03 doit établir :**

1. **Le seuil fini dérive** : pour un tore `T_n` de côté `L = n`, le seuil effectif `p_c(L)` (où la fraction du géant passe un seuil fixé, par exemple 1/2) **n'est pas exactement 1/2** : il varie avec `L`, et converge vers `1/2` comme `L → ∞`.
2. **Loi d'échelle finie** : à `p = p_c(ℤ²) = 1/2`, la fraction du géant `M(L, p_c) / L²` décroît comme `L^{-β/ν}`, où `β/ν = 5/36 ≈ 0.139` est l'exposant critique de la percolation 2D (Kesten, Saleur). Mesure : `log-log plot` de `M(L, 1/2)` vs `L` doit avoir un exposant `-0.139 ± 0.01`.
3. **Loi de taille des composantes** : au point critique, la distribution de tailles des composantes connexes suit une loi de puissance `P(s) ~ s^{-τ}` où `τ' = 187/91 ≈ 2.055` en 2D (Stauffer, computer-experiment measurement). Mesure : histogramme log-binned sur les composantes non-géantes, exposant `τ' ≈ 2.05 ± 0.05`.

**Ce qui distingue 03 de 01** : 01 mesure le *géant* en régime `p > p_c` (où il existe de manière stable). 03 mesure le *géant* en régime `p ≈ p_c` (où il est critique et fluctue), et la **distribution des tailles de composantes** — c'est la **physique du point critique**, qui complète le triptyque.

## 2. Théorie de référence — exposants critiques 2D

La percolation de Bernoulli sur `ℤ²` (bond) est **exactement résoluble** (Kesten 1980) — les exposants critiques sont des rationnels. Voici les valeurs de référence pour 03 :

| Exposant | Valeur | Signification |
|---------|--------|---------------|
| `p_c` | 1/2 (exact, Kesten 1980) | Seuil de liens sur `ℤ²` |
| `β` | 5/36 ≈ 0.139 | `M(L) ~ (p - p_c)^β` pour `p > p_c` |
| `ν` | 4/3 (exact) | `ξ ~ |p - p_c|^{-ν}` |
| `γ` | 43/18 ≈ 2.389 | `χ ~ |p - p_c|^{-γ}` |
| `τ'` | 187/91 ≈ 2.055 | `P(s) ~ s^{-τ'}` au point critique |
| `β/ν` | 5/36 ≈ 0.139 | Exposant de la fraction du géant à `p_c` |
| `γ/ν` | 43/18 · 3/4 = 43/24 ≈ 1.792 | Exposant de la susceptibilité à `p_c` |
| `1/ν` | 3/4 | Exposant de la longueur de corrélation à `p_c` |

**Vérifications à effectuer** :
- `M(L, 1/2) / L^2 ~ L^{-5/36}` — pente `log-log` ≈ `-0.139`.
- Distribution de tailles `P(s)` au point critique — exposant `τ' ≈ 2.055` sur le **bulk** (entre `s_min ~ L^{d_f/2}` et `s_max ~ L^d`), pas sur les queues.
- **Convention honnête** : ces exposants sont **prédits par la théorie conforme** (CFT) et **vérifiés numériquement** depuis 30 ans. Les exposants mesurés sur des tores `L ≤ 256` peuvent dévier de `2-5 %` des valeurs exactes — c'est attendu, et la mesure doit le **dire** plutôt que `converger à 1 %` par cherry-picking.

## 3. Architecture pipeline — sweep `L × p × seeds`, instrument `networkx`

### Instruments (hérités de 01)
- `numpy.random.default_rng(seed)` — RNG déterministe, réplicable.
- `networkx.grid_2d_graph(L, L, periodic=True)` — tore carré degré 4.
- `networkx.connected_components` — composantes connexes (BFS).
- `matplotlib.pyplot` — figures.

### Variables de sweep
| Paramètre | Plage | Cardinal |
|-----------|-------|----------|
| `L` (côté du tore) | {8, 16, 32, 64} | 4 valeurs |
| `p` (probabilité de lien ouvert) | {0.45, 0.48, 0.50, 0.52, 0.55} | 5 valeurs |
| `seeds` | {0, 1, 7, 42, 99} (5 seeds principaux) + 27 seeds auxiliaires | 32 seeds par cellule `(L, p)` |
| **Total** | | **4 × 5 × 32 = 640 simulations** |

### Structure d'une simulation
```python
def sample_at_p_c(L, p, seed):
    rng = np.random.default_rng(seed)
    G = nx.grid_2d_graph(L, L, periodic=True)
    edges = list(G.edges())
    mask = rng.random(len(edges)) < p
    G_open = nx.Graph()
    G_open.add_nodes_from(G.nodes())
    G_open.add_edges_from([e for e, m in zip(edges, mask) if m])
    sizes = sorted((len(c) for c in nx.connected_components(G_open)), reverse=True)
    giant = sizes[0] if sizes else 0
    bulk = sizes[1:]  # excluant le géant
    return giant, bulk
```

### Estimateurs
- **Géant** : `M(L, p) = E[|C_max|]` (moyenne sur seeds).
- **Fraction du géant** : `M(L, p) / L²`.
- **Bulk mean size** : `Σ_s s² · n(s) / Σ_s s · n(s)` (estimateur de `χ`).
- **Distribution de tailles** : histogramme log-binned (≥ 10 bins par décade) sur `s ∈ [s_min, s_max]`.

## 4. Budget runtime — ~30 min mono-thread

| Cellule | Opération | Coût estimé |
|---------|-----------|-------------|
| 2 | Setup RNG, helpers | 1 |
| 3 | `sample_at_p_c(L, p, seed)` × 640 | **25 min** (L=64 dominant) |
| 4 | Calcul M(L, p) / L² + incertitude | < 1 |
| 5 | Histogrammes de tailles × 4 L | 2 |
| 6 | Plot log-log M vs L | < 1 |
| 7 | Plot loi de tailles (P(s) vs s) | < 1 |
| 8 | Régressions (β/ν et τ') | < 1 |
| **Total** | | **~30 min mono-thread** |

**Smell dominant** : `L=64 × p = 5 × 32 seeds = 160 simulations` — chacune fait un BFS sur ~4000 nœuds. Le BFS est O(N+E) avec `N = L² = 4096` et `E = 2L² = 8192`, soit ~12 000 ops/simulation × 160 = 1.9M ops ≈ 0.3 s. Mais Python sur `networkx.connected_components` est notoirement lent pour les graphes denses (~10× plus lent qu'un BFS C). Estimation réaliste : ~25 min pour 640 simulations.

**Optimisation possible** : `scipy.sparse.csgraph.connected_components` sur matrice d'adjacence creuse, ~5× plus rapide que `networkx`. Si budget serré : migrer vers scipy.

## 5. **RÈGLE F** — pas de dépendance hors-`networkx`

| Composant | Statut local |
|-----------|-------------|
| Python 3.13 | OK (installed, c.1089 ML.Net) |
| `numpy` | OK |
| `networkx` | OK (utilisé en 01, installé) |
| `matplotlib` | OK |
| `scipy.sparse` (option optimisation) | OK (utilisé ailleurs) |
| **NTL 11.5.1** | **N/A** (03 n'est pas un lake Lean, pas de NTL requise) |
| **Sage 10.8** | **N/A** |

**Verdict RÈGLE F** : **SOTA-OK auto-suffisant.** Pas de dépendance hors-`networkx` + `numpy`. Pas de routage RECOVERABLE-MACHINE nécessaire.

## 6. 4 smells

1. **BFS non-convergent sur `L=128`** : la mémoire requise pour `networkx` à `L=128` (`N=16384`, `E=32768`) est ~50 MB par simulation × 32 seeds × 5 p = 8 GB cumulés en mémoire (les simulations séquentielles n'ont pas ce problème, mais c'est le **goulot d'étranglement CPU**). Mitigation : limiter `L_max = 64` ; passer à `L=128` dans un cycle ultérieur si `networkx` est remplacé par scipy.

2. **Distribution de tailles bruitées à petit L** : pour `L=8`, le nombre total de nœuds est 64 — la distribution de tailles est trop petite pour des bins log-decade stables. Mitigation : présenter les histogrammes à partir de `L=16`, noter `L=8` comme régime asymptotique.

3. **Seuil fini vs seuil infini** : la confusion pedagogique entre `p_c(L)` (fini) et `p_c(ℤ²)` (infini). Le carnet doit **dire explicitement** que `p_c(L) ≠ 1/2` pour `L < ∞`, et que la **convergence** est l'objet — pas le seuil fini.

4. **Seed-fluctuation asymétrique à petit L** : à `L=8`, les fluctuations entre seeds peuvent atteindre ±30 % de la moyenne. À `L=64`, les fluctuations tombent à ±5 %. Le carnet doit **afficher les barres d'erreur** et **dire la limite** des fluctuations aux petits L.

## 7. Comparaison vs vanilla — instrument canonique

`networkx.connected_components` est l'API canonique pour les composantes connexes d'un graphe non-orienté. Comparaison vs alternatives :

| Outil | Avantage | Inconvénient |
|-------|----------|-------------|
| `networkx.connected_components` | API standard, BFS Cython interne | Lent (10× vs scipy) |
| `scipy.sparse.csgraph.connected_components` | Rapide (5× C) | API moins lisible |
| `igraph.Graph.connected_components()` | Très rapide (~10× scipy) | Pas installé localement |
| Manuel BFS | Contrôle total | Réinventer la roue |

**Choix** : `networkx.connected_components` pour la **lisibilité pédagogique** (03 est un carnet de la série Probas — le code doit être **clair** avant d'être rapide). Si la série devient critique sur `perf`, une migration vers scipy est simple (signature identique `csgraph.connected_components(csgraph)`).

## 8. Livrable

| Fichier | Description | Lignes |
|---------|-------------|--------|
| `MyIA.AI.Notebooks/Probas/Applications/Percolation/Percolation-03-Critique-Python.ipynb` | Carnet d'application | ~700 l. |
| `docs/research/percolation-03-critique-results.md` | Rapport ground truth : mesures, fits β/ν et τ', comparaison vs théorie | ~250 l. |
| `example_results/p03_critique_validation.json` | JSON machine-readable (4 L × 5 p × 32 seeds) | ~600 l. |
| `MyIA.AI.Notebooks/Probas/Applications/Percolation/README.md` | Update : ajouter ligne 03 dans le tableau | +5/-2 |

## 9. Plan d'exécution 4 phases

| Phase | Activité | Durée |
|-------|----------|-------|
| A | Design des cellules (sections 1-7) | 15 min |
| B | Exécution papermill + collecte 640 simulations | 30 min |
| C | Validation : vérification `β/ν ∈ [-0.13, -0.15]` et `τ' ∈ [2.0, 2.1]` | 10 min |
| D | Rédaction rapport + README + PR | 15 min |
| **Total** | | **~70 min wall-clock sur 1-2 cycles** |

## 10. Recommandation

**Auto-suffisant localement (pas de RECOVERABLE-MACHINE)** : 03 ne dépend que de `networkx`, `numpy`, `matplotlib` — tous installés. Pas de NTL, pas de Sage, pas de GPU. Le seul goulot est CPU (~30 min), gérable dans une session.

**Calendrier proposé** :
- **c.1103 (en cours)** : ce scoping (livré en 1 PR).
- **c.1104+** : exécution effective (papermill sur les 640 simulations) + rapport + update README.

**Acceptance pour c.1103+** (à vérifier dans le PR d'exécution) :
- [ ] `M(L, 1/2) / L² ~ L^{-β/ν}` avec `β/ν ∈ [-0.13, -0.15]` (fit log-log, `R² > 0.95`).
- [ ] `P(s)` au point critique suit `s^{-τ'}` avec `τ' ∈ [2.0, 2.1]` (fit log-log, `R² > 0.95`).
- [ ] `p_c(L) → 1/2` comme `L^{-1/ν}` (Schröder, simple universal check).
- [ ] README mis à jour avec ligne 03.
- [ ] Tests : aucune erreur, aucune cellule `NotImplementedError` (C.1), outputs présents (C.2), pre-commit H.3 PASS.

---

## Annexes — état mesuré de la sous-série

### État des carnets (mesuré au commit `70ece81334`)

| # | Carnet | Statut | Lignes |
|---|--------|--------|--------|
| 01 | `Percolation-Supercritique.ipynb` | Livré (c.1089 canonisation) | voir carnet |
| 02 | `Percolation-Lean.ipynb` | Livré (c.1089 canonisation) | n/a, lake mature |
| 03 | `Percolation-03-Critique-Python.ipynb` | **À créer (c.1103 scoping)** | ~700 l. (estimé) |

### État du lake `percolation_lean`

Modules FR (`Basic`, `Connectivity`, `Components`, `Boundary`, `Examples`) + modules EN (convention i18n #4980), `proof-integrity` câblé en CI. Le lake porte les **primitives finies** : configurations d'arêtes, Harris-Kleitman, connexité croissante, composantes, frontière isopérimétrique `C₃`/`C₄`.

Le **seuil critique `p_c`** et la **loi de taille des composantes** sont **hors-portée** du lake (no agenda claims these as targets in `grounding.md`). 03 (Python) **mesure** ce que le lake ne prouve pas.

### État des issues parentes

- `#19494` (ce plan, OPEN) : aucune autre lane n'a claimé.
- `#16231` (chantier C : padding/suffixe) : claim `myia-po-2023:CoursIA-2` actif depuis 2026-09-04.
- `#14873` (Probas series hierarchy) : claim actif depuis 2026-09-25.

### Chevauchement de claims (vérifié)

`check_lane_claim.py --lane myia-po-2023:CoursIA-2 19494` : **CLEAR, aucune lane bloquante**, `my_active_claim: true` (claim posée au c.1103 par moi-même avant édition).

---

## Sources naturelles (acceptées, à archiver GDrive au moment du livrage)

- **Diskin, Easo, Radhakrishnan, Sudakov & Tassion**, *Supercritical sharpness of percolation*, arXiv:2603.03257 (math.PR, v1, CC-BY 4.0) — déjà archivée par 01 (cf. note README).
- **Stauffer, D. & Aharony, A.**, *Introduction to Percolation Theory*, 2ᵉ éd., Taylor & Francis 1994 — référence standard des exposants critiques (pas open-access, déjà au gisement cluster).

---

**Cycle c.1103, lane `myia-po-2023:CoursIA-2`** : scoping livré. Exécution à arbitrer pour c.1104+.