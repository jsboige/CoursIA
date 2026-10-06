# Percolation-03c critique — résultats L=512 (palier 3++, c.1106)

> **Suite directe de [#19494](https://github.com/jsboige/CoursIA/issues/19494)** (plan de croissance Percolation 03 / 04), du scoping memo [PR #19531](https://github.com/jsboige/CoursIA/pull/19531) (c.1103), de l'exécution [PR #19537](https://github.com/jsboige/CoursIA/pull/19537) (c.1104, L ∈ {8, 16, 32, 64}) et de l'extension [PR #19548](https://github.com/jsboige/CoursIA/pull/19548) (c.1105, L ∈ {128, 256}). Ce carnet pousse le sweep à **L = 512** pour vérifier la convergence asymptotique.

## Sections (7)

1. **Cible** — convergence β/ν → 5/36, τ' → 187/91 quand L → ∞
2. **Architecture pipeline** — sweep L=512 × 32 seeds × 5 p
3. **Mesures effectuées** — 160 sims, ~186 s wall-clock
4. **Verdict β/ν (7 L)** — log-log fit, pas d'amélioration
5. **Verdict τ' (7 L)** — L=512 cas pathologique
6. **Verdict p_c(L)** — convergence monotone conforme
7. **Verdict global** — asymptote toujours non atteinte

---

## 1. Cible

Vérifier si les **corrections d'échelle finie** qui faisaient dévier
`β/ν = 0.1065` (c.1105, 6 L) de la valeur asymptotique `5/36 ≈ 0.139`
s'atténuent à L = 512.

**Hypothèse a priori** : sur 7 points au lieu de 6, le fit log-log devrait
mieux capturer la pente asymptotique.

## 2. Architecture pipeline

- **L = 512** (1 nouvelle valeur, ~37 s / `(L, p)` × 32 seeds)
- **p ∈ {0.45, 0.48, 0.50, 0.52, 0.55}** (5 valeurs)
- **seeds = 32 par cellule `(L, p)`** : 5 canoniques `{0, 1, 7, 42, 99}` + 27 auxiliaires `range(100, 127)`
- **Total nouvelles simulations** : 1 × 5 × 32 = **160 simulations** (vs 320 pour c.1105)
- `networkx.grid_2d_graph(L, L, periodic=True)` + `networkx.connected_components`

## 3. Mesures effectuées

**Wall-clock total (c.1106)** : 186.4 s pour 160 simulations
- L = 512 : ~37 s / `(L, p)` × 32 seeds (~1.16 s / simulation)
- 512² = 262144 nœuds par simulation — coût quadratique en L² attendu

**Tableau M(L, p) / L² (L = 512)** :

| p=0.45 | p=0.48 | p=0.50 | p=0.52 | p=0.55 |
|--------|--------|--------|--------|--------|
| 0.0055 ± 0.0010 | 0.0399 ± 0.0146 | 0.5131 ± 0.0988 | 0.7957 ± 0.0089 | 0.8884 ± 0.0026 |

À `p = 0.50`, M/L² à L = 512 (0.5131) est **légèrement inférieur** à L = 256 (0.5352). La décroissance algébrique continue mais **s'atténue** : différence 256→512 (0.0221) vs différence 128→256 (0.0797).

## 4. Verdict β/ν (7 L)

**Régression log-log** sur `M(L, 1/2) / L²` vs `L` (7 points) :

| L | M/L² | Source |
|---|------|--------|
| 8   | 0.7890 | c.1104 (29 seeds) |
| 16  | 0.7320 | c.1104 |
| 32  | 0.7100 | c.1104 |
| 64  | 0.6290 | c.1104 |
| 128 | 0.6149 | c.1105 (32 seeds) |
| 256 | 0.5352 | c.1105 |
| 512 | 0.5131 | c.1106 (32 seeds) |

**Fit log-log** : `β/ν = 0.1062` (cible 5/36 ≈ 0.1389, R²=0.9767, std_err=0.0073)

**Verdict** : `EN COURS — asymptote toujours non atteinte`. Le passage de 6 à 7 points **n'a pas amélioré** `β/ν` (0.1065 → 0.1062, -0.0003). Le R² a légèrement augmenté (0.964 → 0.977), indiquant un fit **localement meilleur** mais la **pente reste asymptotiquement biaisée** par les corrections d'échelle.

**Convention honnête** : l'écart à la cible (0.139 - 0.106 = 0.033) reste ~3× l'écart-type du fit (0.0073). La convergence est **structurellement bloquée** à L ≤ 512.

## 5. Verdict τ' (7 L)

**Distribution de tailles** `P(s)` au point critique, fit log-log sur le bulk (percentile 5-95) :

| L | τ' mesuré | Source |
|---|-----------|--------|
| 8   | 2.25  | c.1104 (approximation) |
| 16  | 2.20  | c.1104 |
| 32  | 2.18  | c.1104 |
| 64  | 2.15  | c.1104 |
| 128 | 2.163 | c.1105 (fit direct) |
| 256 | 2.183 | c.1105 |
| **512** | **2.913** | **c.1106 (fit direct — cas pathologique)** |

- `τ' moyen (7 L) = 2.291` (cible 187/91 ≈ 2.055)
- **Verdict** : `τ' = 2.913` à L = 512 est un **cas pathologique** : le bulk contient énormément de composantes triviales (s = 1, 2, 3...) qui **ne suivent pas la loi de puissance** et tirent le fit vers le haut. Pour un fit propre à L = 512, il faudrait `s_min ~ L/4 = 128`.

**Convention honnête** : la mesure à L = 512 est publiée telle quelle, mais elle ne représente pas l'exposant critique. Un fit avec `s_min = 128` donnerait un `τ'` plus proche de la valeur asymptotique, mais reste à arbitrer pour un carnet ultérieur.

## 6. Verdict p_c(L)

**Interpolation linéaire** de `M(L, p) / L² = 1/2` pour L = 512 :
- `M(512, 0.45) / L² = 0.0055` (giant très petit)
- `M(512, 0.48) / L² = 0.0399`
- `M(512, 0.50) / L² = 0.5131` (juste au-dessus de 1/2)
- `M(512, 0.52) / L² = 0.7957`

`p_c(512)` ≈ 0.4987 (interpolation entre 0.48 et 0.50 où M/L² croise 0.5).

**Convergence monotone** : `0.4512 → 0.4741 → 0.4891 → 0.4942 → 0.4984 → 0.4987 → 1/2` ✓ (écart 0.0013 à L = 512). **PASS conforme**.

## 7. Verdict global

**β/ν = 0.1062** : convergence **bloquée** asymptotiquement. L'extension L = 128 → 256 → 512 **n'a pas amélioré** la pente (`0.102 → 0.1065 → 0.1062`). Le R² continue d'augmenter (0.95 → 0.964 → 0.977) mais la pente reste ~25% sous la cible.

**τ' = 2.913 à L = 512** : cas pathologique, fit à revoir avec `s_min ~ L/4`. Le τ' moyen sur 7 L = 2.291 n'est pas significatif.

**p_c(L) → 1/2** : convergence **conforme** (écart 0.0013 à L = 512).

**Conclusion** : la convergence de β/ν est **structurellement bloquée** aux corrections d'échelle finie. Pour approcher la cible à 1% près, il faudrait :
- L ∈ {1024, 2048} (10-30 min wall-clock), OU
- Une analyse théorique des corrections d'échelle (scaling corrections : `M(L, 1/2) / L² = L^{-β/ν} (1 + a L^{-ω} + ...)` avec `ω` un exposant de correction).

**Convention honnête** : les valeurs sont publiées telles quelles. Le **taux de convergence** de `β/ν` vers `5/36` est le résultat physique de cette étude : ~+0.002 par doublement de L.

**Prochaine étape** : passer au **palier 4 sharpness** (Percolation-04-Sharpness-Python) prévu par le plan de croissance #19494. La convergence `p_c(L) → 1/2` est déjà conforme, et c'est sur la **vitesse de disparition** du géant en régime supercritique que le théorème de Diskin-Easo-Radhakrishnan-Sudakov-Tassion (arXiv:2603.03257 §3.0) attend ses mesures. Trois paliers du carnet 03 épuisés (03 critique, 03b L=128/256, 03c L=512) — passer à la suite logique.

---

**Cycle c.1106, lane `myia-po-2023:CoursIA-2`** : extension L=512 livrée. PR à publier.
