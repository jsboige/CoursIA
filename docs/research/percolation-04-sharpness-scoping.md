# Percolation-04 Sharpness — scoping (palier 4, c.1107)

> **Suite directe de [#19494](https://github.com/jsboige/CoursIA/issues/19494)** (plan de croissance Percolation 03 critique / 04 sharpness ×2). Mémo de cadrage pour le **palier 4** : la mesure de la **vitesse de disparition** du géant en régime supercritique, à la lumière du théorème de *supercritical sharpness* de Diskin–Easo–Radhakrishnan–Sudakov–Tassion (arXiv:2603.03257, Theorem 1 §1).

## Sections (10)

1. **Cible théorique** — inégalité de supercritical sharpness
2. **Carnets amont** — 01 supercritique, 03 critique, 03b/03c extensions
3. **Architecture pipeline** — sweep L × p > p_c × seeds
4. **Mesures attendues** — `Q(n; p) = P_p(n ≤ |C_o| < ∞)` en fonction de `p - p_c`
5. **Runtimes** — budget et seuils
6. **Smells anticipés** — pièges à éviter
7. **Acceptance** — critères d'arrêt
8. **Compar upstream** — outils et concurrence
9. **Livrable** — carnet 04-Sharpness-Python.ipynb + mémo
10. **Plan 4 phases** — calendrier d'exécution

---

## 1. Cible théorique

**Théorème 1** (S. Diskin, P. Easo, R. R. Radhakrishnan, B. Sudakov, V. Tassion, *Supercritical sharpness of percolation*, arXiv:2603.03257, §1 ; consulté le 2026-10-09) :

Pour la percolation de Bernoulli sur un graphe transitif infini connexe, au-dessus du point critique, il existe `c = c(p, graphe) > 0` tel que pour tout `n ≥ 1` :

```
P_p(n ≤ |C_o| < ∞) ≤ exp(-c · Φ_iso(n))
```

où `Φ_iso(n) := min{ |∂S| : S ⊂ V, n ≤ |S| < ∞ }` est la **fonction isopérimétrique** du graphe (eq. (4) du papier : le plus petit bord d'un ensemble fini de taille au moins `n`).

Sur `ℤ^d` (`d ≥ 2`), l'inégalité isopérimétrique donne `Φ_iso(n) ≍ n^{(d-1)/d}` — soit `√n` en `d = 2`. La loi retenue est donc une décroissance **d'ordre surfacique**, `exp(-c · n^{(d-1)/d})`, **pas** une décroissance exponentielle en `n`.

**Correction (c.1207b, lane `myia-po-2023:CoursIA-2`).** L'énoncé antérieur de cette section portait `≤ exp(-c · (p - p_c)^{d-1} · n)`. Il était faux sur deux plans, et la cause est une **collision de notations** : le papier nomme `Φ(n)` la fonction *isopérimétrique*, alors que ce mémo nommait `Φ(n; p)` la *probabilité de queue*. La phrase du papier — « decays exponentially in `Φ(n)` » — a été transcrite comme si `Φ` y était la probabilité. Corrigé : (a) l'argument de l'exponentielle est `Φ_iso(n) ≍ n^{(d-1)/d}`, pas `n` ; (b) `c` **dépend de `p`**, mais l'énoncé lu **ne donne aucune puissance de l'écart `(p - p_c)`** — l'ancien `(p - p_c)^{d-1}` n'était pas dans la source. La probabilité de queue est **renommée `Q`** dans tout le mémo, pour que `Φ` n'y désigne plus que la fonction isopérimétrique (§6 Smell 5).

**Portée du vérifié.** Énoncé lu depuis l'abstract et le Theorem 1 du papier (HTML arXiv, §1). La mention « §3.0 » de la version antérieure **ne renvoyait pas au papier** : les renvois internes du papier visent §1, §1.1, §2, §4, §6, §7, §8, et le Theorem 1 vit en §1. Le « §3.0 » était la **section 3.0 de `Percolation-01-Supercritique`** (« Le théorème du papier — énoncé exact »), qui porte le même énoncé avec `Φ` = fonction isopérimétrique — d'où la reprise fautive du symbole. La dépendance de `c` à l'écart `(p - p_c)` **n'est pas postulée ici** — c'est un objet de **mesure** pour le palier 4 (`RAPPORTE` : les résultats classiques d'ordre surfacique en régime surcritique — Alexander–Chayes–Chayes 1990, Kesten–Zhang 1990, Grimmett–Marstrand 1990 — sont cités par la relecture coordinateur et restent à épingler par le mémo de résultats avant d'être affirmés).

**Conséquence** : la queue **s'épaissit** quand `p ↓ p_c` — le taux de décroissance `c(p)` tend vers zéro, la décroissance ralentit et la queue devient **plus lourde**. C'est la transition de phase au point critique. (La version antérieure disait à la fois que « la queue raidit » et qu'elle « devient plus épaisse » : deux formulations opposées ; seule la seconde est juste.)

**Pourquoi `n ≤ |C_o| < ∞` et non `|C_o| < n`** : `P(|C_o| < n)` est la fonction de répartition (croissante en `n`, minorée par `P(|C_o| = 1) > 0`, convergente vers `1 - θ(p) > 0`), elle **ne peut pas** être majorée par une exponentielle décroissante. La quantité qui décroît est la queue **finie** `P(n ≤ |C_o| < ∞)` — c'est la définition utilisée par `Percolation-01-Supercritique` (c.1089), et c'est celle que palier 4 conserve.

**Ce que mesure le palier 4** : l'exposant empirique de la queue sur des **tores finis** en fonction de `p - p_c` et de `L`. Vérifier que la queue **s'épaissit** quand `p ↓ p_c` et identifier le **régime asymptotique** où l'inégalité devient presque-égalitaire (la queue domine en `n → ∞`).

## 2. Carnets amont (ce que le palier 4 reçoit)

| Carnet | Cycle | Ce qu'il établit pour palier 4 |
|--------|-------|--------------------------------|
| `Percolation-01-Supercritique` | c.1089 canonisation | Énonce le théorème en §3.0 (`Φ` = fonction **isopérimétrique**, `Φ_iso(n) ~ √n` en `d = 2`) et mesure la queue finie `P_p(n ≤ \|C_o\| < ∞)` sur tores carrés et hexagonaux, en **deep supercritique** (`p = 0.7`) |
| `Percolation-03-Critique-Python` | c.1104 exécution | Loi d'échelle finie au point critique, `p_c(L) → 1/2` monotone (convergence conforme) |
| `Percolation-03b-Critique-L128-L256` | c.1105 extension | β/ν = 0.1065, τ' = 2.188 sur 6 L — convergence β/ν bloquée |
| `Percolation-03c-Critique-L512` | c.1106 extension | β/ν = 0.1062, R²=0.977 sur 7 L — convergence asymptotique **structurellement bloquée** |

**Continuité** : palier 4 exploite la convergence `p_c(L) → 1/2` (PASS conforme) du palier 03 pour **définir le paramètre de contrôle** `(p - p_c(L))` sans dépendre de la valeur exacte de `p_c(ℤ²) = 1/2`.

**Note sur la duplication** : la mesure de `Q(n) = P_p(n ≤ |C_o| < ∞)` est conceptuellement similaire à celle de `Percolation-01` (carnet 1, queue finie), et palier 4 la systématise sur une **grille de p > p_c** et identifie le **régime de transition** près du seuil. Le **mesurande** est exactement celui de palier 01 ; le **symbole** diffère (`Q` ici, `P_p(n ≤ |C_o| < ∞)` écrit en clair là-bas) parce que `Φ` y désigne la fonction isopérimétrique. Toute déviation du mesurande invalide la comparaison.

## 3. Architecture pipeline

**Cible de mesure** : `Q(n; p, L) = P_p(n ≤ |C_o| < ∞)` (queue finie) pour une grille de `(p, L)`.

**Sweep proposé** :
- **L ∈ {64, 128, 256, 512}** (4 valeurs — `L = 32` trop petit, le régime `p - p_c` petit ne se développe pas)
- **p ∈ {0.50, 0.52, 0.54, 0.56, 0.58, 0.60, 0.65, 0.70}** (8 valeurs : 6 près du seuil + 2 deep supercritique pour caler la baseline)
- **seeds = 32 par cellule `(L, p)`** : 5 canoniques `{0, 1, 7, 42, 99}` + 27 auxiliaires `range(100, 127)` (cohérent avec paliers 03b, 03c)
- **Total** : 4 × 8 × 32 = **1024 simulations** (vs 580 c.1104, 320 c.1105, 160 c.1106 — croissance linéaire avec le nombre de `(L, p)`)

**Wall-clock estimé** (basé sur les paliers précédents) :
- L=64 : ~17 ms/sim × 32 seeds × 8 p = ~4.4 s
- L=128 : ~70 ms/sim × 32 × 8 = ~18 s
- L=256 : ~280 ms/sim × 32 × 8 = ~72 s
- L=512 : ~1.2 s/sim × 32 × 8 = ~5 min (limite haute)
- **Total** : ~6-7 min wall-clock mono-thread

**Instrument** : `networkx.grid_2d_graph(L, L, periodic=True)` + `nx.connected_components`, identiques aux paliers 03/03b/03c (RÈGLE F SOTA-OK). Pour L=1024+ il faudrait basculer sur `scipy.sparse.csgraph.connected_components`.

## 4. Mesures attendues

Pour chaque cellule `(L, p)` :
- **Distribution de la taille de la composante de l'origine** : `P(|C_o| = k)` pour `k ∈ {1, ..., L²}`
- **Queue finie** : `Q(n) = P_p(n ≤ |C_o| < ∞)` pour `n ∈ {1, 2, 4, 8, ..., L²}` (la queue qui décroît)
- **Décroissance empirique** : `log Q(n) ~ -α(L, p) · n^{(d-1)/d}` — en `d = 2`, fit **linéaire de `log Q(n)` contre `√n`**, dont la pente est `α(L, p)`. **PAS** un fit contre `n` (l'ancien protocole fittait `exp(-α · n)`, c'est-à-dire la mauvaise loi) et **PAS** sur la CDF (croissante, ne porte pas le taux)

**Forme de la loi (la pente reste à mesurer)** :
- La loi retenue s'écrit sur le **logarithme** : `-log Q(n) ~ α(p) · n^{(d-1)/d}` (`√n` en 2D) — le fit doit être **linéaire en `√n`**, pas en `n`. (Pas de `≍` sur `Q` elle-même : `Q` décroît vers zéro, l'équivalence asymptotique porte sur son exposant.)
- `α(p)` **décroît** quand `p ↓ p_c` (la queue s'épaissit) et `α(p) → 0` au seuil, où la queue devient **polynomiale** (`τ' = 187/91 ≈ 2.055` — palier 03)
- **La dépendance de `α` à l'écart `(p - p_c)` n'est pas donnée par la source lue** : elle est **mesurée**, puis affichée en log-log — le carnet **ne postule pas** de puissance

**Sortie visuelle** : 3 figures
1. `Q(n) vs √n` sur log-y pour 8 valeurs de p, 4 L (32 courbes) — la loi retenue doit y être une **droite**
2. `α(p) vs p - p_c` pour 4 L (4 courbes) — **sans droite théorique postulée** : la source lue ne donne pas la puissance de l'écart
3. `α_mesuré vs p - p_c` en **log-log** : la **pente empirique** est le résultat ; la comparer aux valeurs classiques d'ordre surfacique n'est légitime qu'une fois celles-ci épinglées par le mémo de résultats

## 5. Runtimes et seuils

| L | Wall-clock / `(L, p)` × 32 seeds | Total pour 8 p |
|---|-----------------------------------|-----------------|
| 64 | ~0.55 s | ~4.4 s |
| 128 | ~2.2 s | ~18 s |
| 256 | ~9 s | ~72 s |
| 512 | ~37 s | ~5 min |
| **Total** | | **~6-7 min** |

**Seuils d'arrêt** :
- Si après 2 valeurs de `L` (e.g. 64 et 128) la décroissance de `α` est **clairement mesurable** (`R² > 0.95` sur le fit linéaire `log Q(n)` vs `n^{(d-1)/d}`, soit `√n` en 2D) : on garde le sweep complet
- Si le fit ne passe pas le seuil R² : on **élargit** à 64 seeds par cellule (× 2 wall-clock)
- Si L=512 dépasse 10 min : on **tronque** à L ∈ {64, 128, 256}

## 6. Smells anticipés

**Smell 1 : queue non-asymptotique à petit L** — pour L=64, le régime `p - p_c = 0.02` peut être dominé par les **fluctuations** de l'origine (la proba que `o` soit dans le géant vs hors géant reste ~50/50 même à `p = 0.52`). À L=64, la queue n'est **pas encore** dans le régime asymptotique. **Atténuation** : comparer L=64 à L=512 pour identifier le régime de transition.

**Smell 2 : confusion `|C_o| < n` vs `n ≤ |C_o| < ∞`** — la queue **décroissante**, celle qui porte le taux `α(p)`, est `Q(n) = P_p(n ≤ |C_o| < ∞)`. La CDF `P(|C_o| < n)` est croissante et ne porte pas le taux. **Atténuation** : palier 4 **réutilise exactement le mesurande** de palier 01 (`P(n ≤ |C_o| < ∞)`, écrit en clair là-bas), ne dévie jamais de cette clause ; toute régression sur ce smell annule la comparaison palier 01 ↔ palier 04.

**Smell 3 : `p_c(L)` ≠ `1/2` exactement** — palier 03 a montré `p_c(L)` converge vers 1/2 mais reste à 0.4984 à L=256, 0.4987 à L=512. Pour le paramètre `(p - p_c)`, il faut choisir entre `p_c(ℤ²) = 1/2` (limite théorique) et `p_c(L)` mesuré (limite finie). **Atténuation** : utiliser `p - p_c(ℤ²) = p - 1/2` pour la théorie, et `p - p_c(L)` pour les comparaisons empiriques (cite §7 c.1103).

**Smell 4 : `|C_o|` mesuré sur tore ≠ sur `ℤ²`** — sur le tore, la composante de l'origine peut être cyclique (retour à l'origine par periodicité). La définition reste la même (taille de la composante connexe contenant o), mais la **métrique** peut différer aux bords. **Atténuation** : noter dans le mémo que les mesures sont sur tore, pas sur `ℤ²` ; la convergence au tore `ℤ²` est un théorème classique mais reste à vérifier empiriquement.

**Smell 5 : collision de notations sur `Φ`** — `Φ` désigne la **fonction isopérimétrique** chez **deux** sources distinctes : le papier (Theorem 1, eq. (4)) *et* `Percolation-01-Supercritique` (§3.0). Lire « la probabilité décroît exponentiellement en `Φ(n)` » avec un `Φ` qui serait la probabilité produit un énoncé faux (vécu en c.1107, corrigé en c.1207b ; c'est aussi ce qui a fait naître le renvoi « §3.0 » attribué au papier alors qu'il désignait la section de palier 01). **Atténuation** : nommer la fonction isopérimétrique `Φ_iso` **et** nommer la probabilité de queue `Q`, de sorte que `Φ` seul renvoie toujours à la géométrie ; vérifier la formule contre l'énoncé du papier avant de la recopier, pas contre une paraphrase.

## 7. Acceptance

**Acceptance §8 (c.1103 amendé pour palier 4)** :

1. `Q(n; L, p)` mesuré sur la grille (4 L × 8 p × 32 seeds = 1024 sims) — **PASS** : sweep exécuté
2. `α(L, p)` extrait par fit **linéaire de `log Q(n)` contre `n^{(d-1)/d}`** (`√n` en 2D), pour `n ∈ {1, 2, 4, 8, ...}` — **R² > 0.90** sur au moins 75% des cellules `(L, p)` avec `p ≥ 0.55`
3. La pente de `log α(p)` contre `log(p - 1/2)` pour L fixé est **rapportée** — **R² > 0.85** sur la régression, **sans puissance postulée** : la source lue ne donne pas la dépendance de `α` à l'écart, donc le livrable est la pente mesurée, pas son écart à `(p - 1/2)^{d-1}`
4. Visualisation : 3 figures, pentes lisibles, `α` mesuré **monotone décroissant** quand `p ↓ p_c`, pour `p ≥ 0.55`
5. Mémo résultats (substantiel, structuré en sections) avec interprétation physique
6. Notebook C.1 (0 `NotImplementedError`), C.2 (outputs présents), H.3 (pre-commit PASS)

**Verdict honnête** : la source lue ne fixe pas la dépendance de `α` à `(p - p_c)`. Si la pente mesurée n'est pas celle qu'un lecteur attend, le carnet **documente** la pente obtenue et son domaine de validité — il ne l'ajuste pas à une loi postulée.

## 8. Comparaison upstream / outils

| Outil | Usage | Justification |
|-------|-------|----------------|
| `networkx.connected_components` | Calcul de `|C_o|` sur le tore | Canonique, RÈGLE F SOTA-OK, déjà utilisé paliers 03/03b/03c |
| `scipy.optimize.curve_fit` | Fit `log Q(n)` **linéaire en `n^{(d-1)/d}`** (soit `√n` en 2D) | SciPy stack standard, déjà disponible |
| `matplotlib` | Visualisation 3 figures | Standard notebook Python |
| `numpy.random.default_rng` | PRNG stable, seeds canoniques | Cohérence inter-paliers |

**Pas de dépendance nouvelle** : tout est déjà installé (paliers précédents). RÈGLE F respectée (RÈGLE F = réparer, JAMAIS contourner).

## 9. Livrable

- **`MyIA.AI.Notebooks/Probas/Applications/Percolation/Percolation-04-Sharpness-Python.ipynb`** : carnet structuré (markdown + code), mesure `Q(n)`, fit `α(L, p)`, visualisation, synthèse
- **`docs/research/percolation-04-sharpness-results.md`** : mémo structuré en sections (cible, architecture, mesures, verdicts, comparaison théorie, limitations, perspectives, conclusion)
- **README update** : une entrée ajoutée au tableau des composants
- **Figures** : 3 PNG (`q_vs_n.png`, `alpha_vs_p.png`, `alpha_ratio.png`)

**Wall-clock total estimé** : ~6-7 min sweep + 5 min post-processing = **~12-15 min pour le carnet complet**. C'est plus long que les paliers 03b/03c (extensions) mais plus court que le carnet 03 initial (qui a aussi demandé du post-processing substantiel).

## 10. Plan 4 phases (estimation)

| Phase | Tâche | Wall-clock | Livrable |
|-------|-------|------------|----------|
| **P1** | Construction du notebook (squelette + helper) | ~3 min | `Percolation-04-Sharpness-Python.ipynb` (non exécuté) |
| **P2** | Exécution papermill sur la grille 4×8×32 | ~7 min | Notebook exécuté, outputs présents |
| **P3** | Fit `α(L, p)` et génération des 3 figures | ~2 min | 3 PNG + résultats agrégés |
| **P4** | Mémo résultats + PR | ~5 min | `percolation-04-sharpness-results.md` + PR |

**Total** : **~17-20 min** wall-clock, ~15 min actifs (P1+P3+P4) + ~7 min passifs (P2 papermill en BG).

**Pré-conditions pour démarrer l'exécution** :
- Claim c.1103 sur #19494 toujours actif (CLEAR, paths scopés) — **vérifié**
- C.1104/03b/03c mergés sur main (pour que le PR palier 4 ait un base solide) — **en attente**, 3 PRs OPEN en stack

**Note** : le palier 4 n'est **pas bloqué** par l'absence de merge des paliers 03/03b/03c — le PR sera stacké sur c.1106 comme les précédents, et rebasera au merge de c.1106. Cf. lesson c.1105-N1.

---

**Cycle c.1107, lane `myia-po-2023:CoursIA-2`** : scoping palier 4 livré. Mémo à publier en PR. **Prochaine étape** : exécution effective du carnet (cycles c.1108+) si la priorité le permet.
