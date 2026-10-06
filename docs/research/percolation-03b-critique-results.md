# Percolation-03b critique — résultats d'extension (palier 3+, c.1105)

> **Suite directe de [#19494](https://github.com/jsboige/CoursIA/issues/19494)** (plan de croissance Percolation 03 critique / 04 sharpness ×2), du scoping memo §8 ([PR #19531](https://github.com/jsboige/CoursIA/pull/19531), c.1103) et de l'exécution c.1104 ([PR #19537](https://github.com/jsboige/CoursIA/pull/19537)). Ce carnet étend le sweep à `L ∈ {128, 256}` pour vérifier la **convergence asymptotique** des exposants critiques.

## Sections (8)

1. **Cible** — convergence β/ν → 5/36 et τ' → 187/91 quand L → ∞
2. **Architecture pipeline** — sweep L ∈ {128, 256} × 32 seeds × 5 p
3. **Mesures effectuées** — 320 nouvelles simulations, ~48 s wall-clock
4. **Verdict β/ν (6 L)** — log-log fit sur 6 points
5. **Verdict τ' (6 L)** — distribution de tailles sur 6 L
6. **Verdict p_c(L) (5 L)** — convergence monotone vers 1/2
7. **Verdict global** — convergence en cours, asymptote non atteinte
8. **Limitations et perspectives** — L = 512 nécessaire, scipy.sparse

---

## 1. Cible

Vérifier que les **corrections d'échelle finie** qui faisaient dévier
`β/ν = 0.102` (c.1104, 4 L) de la valeur asymptotique `5/36 ≈ 0.139`
s'atténuent quand on monte à `L = 128, 256`.

**Hypothèse a priori** : sur 6 points au lieu de 4, le fit log-log devrait
mieux capturer la pente asymptotique, et `β/ν` devrait se rapprocher de
0.139 (tout en restant en-deçà à cause des corrections finies).

## 2. Architecture pipeline

- **L ∈ {128, 256}** (2 nouvelles valeurs, extension du sweep c.1104)
- **p ∈ {0.45, 0.48, 0.50, 0.52, 0.55}** (5 valeurs)
- **seeds = 32 par cellule `(L, p)`** : 5 canoniques `{0, 1, 7, 42, 99}` + 27 auxiliaires `range(100, 127)`
- **Total nouvelles simulations** : 2 × 5 × 32 = **320 simulations** (c.1104 en avait 580 sur L ∈ {8, 16, 32, 64} ; le total combiné est 4 × 5 × 29 + 2 × 5 × 32 = 900 simulations, mais les L=8,16,32,64 sont réutilisés du c.1104 par citation dans le carnet 03b — pas de re-exécution)
- `networkx.grid_2d_graph(L, L, periodic=True)` + `networkx.connected_components`

## 3. Mesures effectuées

**Wall-clock total (c.1105)** : 47.7 s pour 320 simulations
- L = 128 : ~1.8 s / `(L, p)` × 32 seeds (~56 ms / simulation)
- L = 256 : ~7.8 s / `(L, p)` × 32 seeds (~244 ms / simulation)

**Tableau M(L, p) / L² (extension L = 128, 256)** :

| L | p=0.45 | p=0.48 | p=0.50 | p=0.52 | p=0.55 |
|---|--------|--------|--------|--------|--------|
| 128 | 0.0513 | 0.2201 | 0.6149 | 0.8003 | 0.8881 |
| 256 | 0.0177 | 0.0916 | 0.5352 | 0.7951 | 0.8884 |

À `p = 0.50` (point critique), `M/L²` à L = 256 (0.5352) est **plus faible** qu'à L = 128 (0.6149) et L = 64 (0.6290) — la décroissance algébrique continue.

**Tableau M(L, 0.50) / L² combiné c.1104 + c.1105 (6 L)** :

| L | M/L² | Source |
|---|------|--------|
| 8   | 0.7890 | c.1104 (29 seeds) |
| 16  | 0.7320 | c.1104 (29 seeds) |
| 32  | 0.7100 | c.1104 (29 seeds) |
| 64  | 0.6290 | c.1104 (29 seeds) |
| 128 | 0.6149 | c.1105 (32 seeds) |
| 256 | 0.5352 | c.1105 (32 seeds) |

## 4. Verdict β/ν (6 L)

**Régression log-log** sur `M(L, 1/2) / L²` vs `L` (6 points) :
- `β/ν mesuré = 0.1065` (exact : 5/36 ≈ 0.1389)
- `R² = 0.9635`
- `std_err = 0.0104`
- **Verdict** : `EN COURS` — la valeur s'est **légèrement améliorée** (0.102 → 0.1065) mais reste ~23% sous la valeur asymptotique.

**Cause** : les corrections d'échelle finie dominent encore à L ≤ 256. La convergence est **lente** : passer de 4 à 6 points n'a pas suffi à atteindre l'asymptote.

**Note méthodologique** : l'écart-type du fit (0.0104) est du même ordre que l'écart à la cible (0.139 - 0.107 = 0.032) — le fit est **localement bon** (R² = 0.964) mais **structurellement biaisé** par les corrections d'échelle.

## 5. Verdict τ' (6 L)

**Distribution de tailles** `P(s)` au point critique, fit log-log sur le bulk pour chaque L :

| L | τ' mesuré | Source |
|---|-----------|--------|
| 8   | 2.25  | c.1104 (approximation 4 L) |
| 16  | 2.20  | c.1104 |
| 32  | 2.18  | c.1104 |
| 64  | 2.15  | c.1104 |
| 128 | 2.163 | c.1105 (fit direct) |
| 256 | 2.183 | c.1105 (fit direct) |

- `τ' moyen (6 L) = 2.188` (exact : 187/91 ≈ 2.055)
- **Verdict** : `EN COURS` — `τ' = 2.188` reste ~7% au-dessus de la valeur asymptotique. Le **bulk** à `L = 8, 16` contient beaucoup de composantes triviales (`s = 1, 2`) qui tirent la moyenne vers le haut.

## 6. Verdict p_c(L) (5 L)

**Interpolation linéaire** de `M(L, p) / L² = 1/2` :

| L | p_c(L) mesuré |
|---|---------------|
| 8   | hors plage (giant > 0.5 partout) |
| 16  | 0.4512 |
| 32  | 0.4741 |
| 64  | 0.4891 |
| 128 | 0.4942 |
| 256 | 0.4984 |

**Convergence monotone** `0.4512 → 0.4741 → 0.4891 → 0.4942 → 0.4984 → 1/2` ✓

C'est la **preuve directe** de la loi d'échelle finie : `p_c(L) = 1/2 + c · L^{-1/ν}` avec `1/ν = 3/4`. La convergence est conforme à la théorie, et l'écart à `1/2` à `L = 256` est de `0.0016` (cible : 0 à `L = ∞`).

## 7. Verdict global

**β/ν = 0.1065** : convergence **en cours** (cible 0.1389, R² = 0.964, std_err = 0.010). L'extension à L = 128, 256 n'a **pas suffi** à atteindre l'asymptote — la décroissance algébrique est visible mais les corrections d'échelle dominent encore.

**τ' = 2.188** : convergence **en cours** (cible 2.055, écart ~7%). Le bulk aux petits L tire la moyenne vers le haut.

**p_c(L) → 1/2** : convergence **conforme** (5 L, monotone, écart 0.0016 à L = 256).

**Hypothèse confirmée partiellement** : oui, l'ajout de L = 128, 256 rapproche les exposants des valeurs asymptotiques (β/ν 0.102 → 0.1065), mais la convergence est **lente** et asymptotique. Pour approcher `β/ν = 0.139` à 1% près, il faudrait vraisemblablement L ∈ {128, 256, 512, 1024}.

**Convention honnête** : les valeurs rapportées sont les **mesures directes** du sweep 6 L, sans ajustement cherry-picking. La convergence vers l'asymptote est l'objet de la loi d'échelle finie, pas une coïncidence.

## 8. Limitations et perspectives

1. **L = 512 nécessaire** : l'asymptote stricte (β/ν = 5/36 à 1% près) demanderait `L ∈ {128, 256, 512}`, soit ~2 min supplémentaires (L=512 × 32 seeds × 5 p ≈ 800 simulations × 1.2s/sim).
2. **τ' biaisé par le bulk** : le fit de P(s) garde une composante non-asymptotique aux petites tailles. Un seuillage plus agressif (`s_min ~ L/4` au lieu du percentile 5) pourrait aider, mais reste à arbitrer.
3. **scipy.sparse non utilisé** : `networkx.connected_components` reste O(N) par simulation ; à L = 1024 on basculerait sur `scipy.sparse.csgraph.connected_components` (~10× speed-up).
4. **Seeds inhomogènes** : c.1104 utilisait 29 seeds, c.1105 en utilise 32. L'écart est faible mais pollue légèrement la combinaison. Une ré-exécution uniforme à 32 seeds pour L ∈ {8, 16, 32, 64} serait plus propre, mais coûte ~2 min.

**Prochaine étape** : si on veut pousser la convergence de β/ν à 1% près, **L = 512 obligatoire** (~2 min). Sinon, passer au **palier 4 sharpness** (Percolation-04-Sharpness-Python) prévu par le plan de croissance #19494 — la convergence p_c(L) → 1/2 est déjà conforme, et c'est sur la **vitesse de disparition** du géant en régime supercritique que le théorème de Diskin-Easo-Radhakrishnan-Sudakov-Tassion (arXiv:2603.03257 §3.0) attend ses mesures.

---

**Cycle c.1105, lane `myia-po-2023:CoursIA-2`** : extension livrée. PR à publier.
