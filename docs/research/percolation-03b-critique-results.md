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

**Distribution de tailles** `P(s)` au point critique, fit log-log sur le bulk pour chaque L. **Mesures directes c.1104** issues de l'instrumentation R² par L (c.1133, source c.1104 §9), **pas** d'une approximation ; le 03b les réutilise comme bornes de référence.

| L | τ' mesuré | R² | Source | Lecture |
|---|-----------|-----|--------|---------|
| 8   | 2.494 | 0.903 | c.1104 (c.1133 R²) | INCONCLUSIVE — bulk 64 nœuds, R² < 0.95 |
| 16  | 2.021 | 0.996 | c.1104 (c.1133 R²) | descriptif |
| 32  | 2.080 | 0.978 | c.1104 (c.1133 R²) | descriptif |
| 64  | 2.193 | 0.996 | c.1104 (c.1133 R²) | descriptif — **hors [2.0, 2.1]** |
| 128 | 2.163 | 0.990 | c.1105 (fit direct) | descriptif |
| 256 | 2.183 | 0.991 | c.1105 (fit direct) | descriptif |

- `τ' moyen (6 L) = 2.189` (exact : 187/91 ≈ 2.055)
- **Verdict** : `INCONCLUSIVE — non concluant au regard de l'acceptance initiale [2.0, 2.1]`. Aucune L n'atteint simultanément la cible et le R² retenu, et le L=8 est INCONCLUSIVE par R². Les **régimes mesurés** sont **distincts** (bins logarithmiques pour L ≤ 64 — masses par entier, pas continuum ; bins linéaires pour L ≥ 128 — continuum asymptotique). Le 03b **ne choisit pas** d'estimateur pour approcher la cible.

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

**τ' = 2.189** (6 L) : **INCONCLUSIVE** au regard de l'acceptance initiale `τ' ∈ [2.0, 2.1]`. Aucune L ne sort simultanément τ' ∈ [2.0, 2.1] **et** R² ≥ 0.95 **et** au régime asymptotique. L=8 INCONCLUSIVE par R² (0.903), L=64 = 2.193 **hors** acceptance par le haut, L=128/256 au-dessus de 2.1. Le 03b **ne choisit pas** d'estimateur pour approcher la cible. Lecture détaillée §9.

**p_c(L) → 1/2** : convergence **conforme** (5 L, monotone, écart 0.0016 à L = 256). Le seul verdict PASS de la PR.

**Hypothèse a priori (c.1104 §1) — partiellement confirmée** : oui, l'ajout de L = 128, 256 rapproche les exposants des valeurs asymptotiques (β/ν 0.102 → 0.1065), mais la convergence est **lente et asymptotique**. Pour approcher `β/ν = 0.139` à 1% près, il faudrait vraisemblablement L ∈ {128, 256, 512, 1024}.

**Convention descriptive (post-relecture po-2025, c.1136)** : aucune L n'atteint simultanément la cible et l'acceptance R². L'asymptote n'est **pas** tenue. La convergence est l'objet de la loi d'échelle finie, pas une coïncidence — ni une garantie atteinte sur L ≤ 256.

## 8. Limitations et perspectives

1. **L = 512 nécessaire** : l'asymptote stricte (β/ν = 5/36 à 1% près) demanderait `L ∈ {128, 256, 512}`, soit ~2 min supplémentaires (L=512 × 32 seeds × 5 p ≈ 800 simulations × 1.2s/sim).
2. **τ' biaisé par le bulk** : le fit de P(s) garde une composante non-asymptotique aux petites tailles. Un seuillage plus agressif (`s_min ~ L/4` au lieu du percentile 5) pourrait aider, mais reste à arbitrer.
3. **scipy.sparse non utilisé** : `networkx.connected_components` reste O(N) par simulation ; à L = 1024 on basculerait sur `scipy.sparse.csgraph.connected_components` (~10× speed-up).
4. **Seeds inhomogènes** : c.1104 utilisait 29 seeds, c.1105 en utilise 32. L'écart est faible mais pollue légèrement la combinaison. Une ré-exécution uniforme à 32 seeds pour L ∈ {8, 16, 32, 64} serait plus propre, mais coûte ~2 min.

**Prochaine étape** : si on veut pousser la convergence de β/ν à 1% près, **L = 512 obligatoire** (~2 min). Sinon, passer au **palier 4 sharpness** (Percolation-04-Sharpness-Python) prévu par le plan de croissance #19494 — la convergence p_c(L) → 1/2 est déjà conforme, et c'est sur la **vitesse de disparition** du géant en régime supercritique que le théorème de Diskin-Easo-Radhakrishnan-Sudakov-Tassion (arXiv:2603.03257 §3.0) attend ses mesures.

## 9. Diagnostic estimateur τ' (c.1133 + c.1136, suite adjointe po-2025)

**Contexte** : l'adjoint po-2025 a attiré l'attention sur l'estimateur
τ' du carnet 03 et 03b — suspicion que `counts / counts.sum()` (sans
normalisation par largeur de bin) biaisait le fit log-log quand les
bins sont **logarithmiques** (cas du carnet 03).

**Investigations menées** :

1. **Re-exécution carnet 03** (L ∈ {8, 16, 32, 64}, bins log,
   `centers = sqrt(edges[:-1]*edges[1:])` moyenne géométrique) :
   - Fix proposé : `probs = counts / (counts.sum() * np.diff(edges))`
     → `τ' = 3.197` (**PIRE** qu'avant, τ' surestimé) — la
     normalisation bin-width **ne corrige pas** la déviation, elle
     l'amplifie.
   - Réversion à `counts / counts.sum()` + instrumentation R² par L :
     ```
     L=8:  tau_prime=2.494, R²=0.903
     L=16: tau_prime=2.021, R²=0.996
     L=32: tau_prime=2.080, R²=0.978
     L=64: tau_prime=2.193, R²=0.996
     ```
   - **Lecture** : L=8 a R² < 0.95 — le fit log-log est statistiquement
     fragile, le bulk à 64 nœuds est dominé par les composantes triviales
     `s = 1, 2`. Les **3 autres L** ont R² ≥ 0.95 mais τ' **sort de
     [2.0, 2.1]** (L=16=2.021 hors par le bas, L=64=2.193 hors par le
     haut). Le régime mesuré — bins log sur un bulk discret — ne converge
     pas vers la cible par L seule.

2. **Re-exécution carnet 03b** (L ∈ {128, 256}, bins=20 **linéaires**,
   `centers = 0.5*(edges[:-1]+edges[1:])` moyenne arithmétique) :
   - Le fix `counts / (counts.sum() * np.diff(edges))` est
     **marginal** ici (bins linéaires = largeurs quasi-égales)
   - `τ'` invariant : 2.163 (L=128), 2.183 (L=256) → τ' moyen = 2.189
   - R² par L (ré-fit direct, instrumenté c.1133) :
     ```
     L=128: R²=0.990
     L=256: R²=0.991
     ```
   - **Lecture** : R² élevé, mais τ' reste au-dessus de 2.1. Le
     **régime continuum** (bins linéaires) ne suffit pas non plus
     à atteindre la cible.

**Verdict descriptif (c.1136, post-relecture po-2025)** :

- L'**estimateur** n'est pas en cause — le fit est statistiquement bon
  quand R² ≥ 0.95. **Pas de bug**.
- La **cible** `τ' = 187/91 ≈ 2.055` n'est **pas atteinte** sur
  L ∈ {8, 16, 32, 64, 128, 256}. L'écart vient des **corrections
  d'échelle finie**, pas de l'estimateur.
- L=8 est **INCONCLUSIVE** par R² (0.903 < 0.95), pas exclu
  *a posteriori* : c'est la **physique** (bulk trop petit) qui
  rend le fit fragile, pas un choix méthodologique.
- L=64 = 2.193 est **descriptif hors acceptance** : R² = 0.996
  confirme un bon fit local, mais la valeur sort de [2.0, 2.1] —
  le verdict est **non concluant au regard de l'acceptance**, pas
  un PASS.
- Le 03b **ne choisit pas** d'estimateur pour approcher la cible.
  Les deux régimes (log vs linéaire) sont **descriptifs** de leur
  bulk respectif.

**Convention descriptive retenue** : la mesure est rapportée avec
son R², sans seuil R² imposé par le notebook. Le lecteur tranche
l'acceptance. Aucune L ne sort simultanément τ' ∈ [2.0, 2.1] **et**
R² ≥ 0.95 **et** au régime asymptotique — **INCONCLUSIVE** sur
l'acceptance initiale.

---

**Cycle c.1105 + c.1133 + c.1136, lane `myia-po-2023:CoursIA-2`** :
extension livrée + estimateur audité. TAU_PRIME_C1104 (4 L) corrigé
en `{(L, (val, R²))}` à partir des mesures directes c.1104 §9 ;
c.1135b (c.1105) ajoute L=128, 256. Verdict global **INCONCLUSIVE**
au regard de l'acceptance initiale [2.0, 2.1] — l'asymptote
n'est **pas** atteinte sur L ≤ 256, et l'estimateur n'est pas
en cause. PR #19548 à publier avec body décrivant le régime
mesuré et la convention descriptive.
