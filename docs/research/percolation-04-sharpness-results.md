# Percolation-04 Sharpness — résultats (palier 4, c.1108)

> **Suite directe de [#19494](https://github.com/jsboige/CoursIA/issues/19494)**
> (plan de croissance Percolation 03 / 04), du
> [scoping memo #19556](https://github.com/jsboige/CoursIA/pull/19556) (c.1107),
> et de l'exécution 03c
> [PR #19550](https://github.com/jsboige/CoursIA/pull/19550) (c.1106, L=512).
> Ce mémo rapporte les mesures du **palier 4** : la queue supérieure
> `Ψ(n) = P(|C_o| ≥ n)` sur tores finis en régime supercritique, confrontée
> au théorème de *supercritical sharpness* de Diskin–Easo–Radhakrishnan–Sudakov–Tassion
> (arXiv:2603.03257 §3.0).

## Sections (7)

1. **Cible théorique** — borne supérieure de la queue supérieure
2. **Architecture** — sweep L × p × seeds
3. **Mesures effectuées** — 1024 sims, 170 s
4. **Verdict α(p) (8 p × 4 L)** — fit log-y sur `Ψ(n)`
5. **Verdict `α ~ (p - 1/2)`** — confrontation à la cible 2D
6. **Verdict global** — palier 4 non mesurable à L ≤ 512
7. **Convention honnête et perspectives**

---

## 1. Cible théorique

**Théorème (Diskin–Easo–Radhakrishnan–Sudakov–Tassion, arXiv:2603.03257 §3.0, supercritical sharpness)** :

Pour la percolation de Bernoulli sur `ℤ^d` à `d ≥ 2`, la **queue supérieure** de la
distribution de la taille de la composante connexe de l'origine satisfait une
**inégalité de type raideur** :

```
P_p(|C_o| ≥ n) ≤ exp(-c · (p - p_c)^{d-1} · n)
```

pour `p > p_c` et `n ≥ 1`, avec `c = c(d) > 0` une constante explicite.

**En 2D** : `(p - p_c)^{d-1} = (p - 1/2)^1`. La borne prédit que la queue
**s'épaissit** quand `p ↓ p_c` (l'exposant tend vers zéro) et devient
**très raide** dès que `p - p_c = O(1)`.

**Ce que mesure le palier 4** : la **pente empirique** `α(L, p)` de la décroissance
de `Ψ(n) = P(|C_o| ≥ n)` sur tores finis, et sa dépendance en `p - p_c`.

## 2. Architecture pipeline

**Cible de mesure** : `Ψ(n; p, L) = P(|C_o| ≥ n)` pour une grille de `(p, L)`.

**Sweep exécuté** :
- **L ∈ {64, 128, 256, 512}** (4 valeurs)
- **p ∈ {0.50, 0.52, 0.54, 0.56, 0.58, 0.60, 0.65, 0.70}** (8 valeurs)
- **seeds = 32 par cellule `(L, p)`** : 5 canoniques `{0, 1, 7, 42, 99}` + 27 auxiliaires `range(100, 127)`
- **Total** : 4 × 8 × 32 = **1024 simulations**
- Seuils `n ∈ {1, 2, 4, 8, 16, 32, 64, 128}` (8 valeurs, log-échelle)

**Wall-clock mesuré** : 170.2 s pour 1024 simulations (sous l'estimation ~6-7 min du scoping).

**Instrument** : `networkx.grid_2d_graph(L, L, periodic=True)` + BFS depuis `(0, 0)`
pour identifier `|C_o|`, identique aux paliers 03/03b/03c (RÈGLE F SOTA-OK).

## 3. Mesures effectuées

**Wall-clock détaillé (per L, p)** :

| L | Wall-clock / (L, p) × 32 seeds | Total pour 8 p |
|---|-----------------------------------|-----------------|
| 64  | ~0.13 s | ~1.0 s |
| 128 | ~0.69 s | ~5.5 s |
| 256 | ~3.43 s | ~27.4 s |
| 512 | ~17.1 s | ~136.4 s |
| **Total** | | **~170 s** |

**Médianes `|C_o|` (32 seeds par cellule)** :

| L \ p | 0.50 | 0.52 | 0.54 | 0.56 | 0.58 | 0.60 | 0.65 | 0.70 |
|-------|------|------|------|------|------|------|------|------|
| 64    | 2298  | 3262  | 3548  | 3698  | 3812  | 3886  | 3998  | 4052  |
| 128   | 9654  | 13038 | 14164 | 14825 | 15241 | 15538 | 15986 | 16196 |
| 256   | 2799  | 51802 | 56756 | 59336 | 61016 | 62192 | 63940 | 64798 |
| 512   | 2378  | 207854| 227252| 237326| 243976| 248736| 255750| 259169|

**Observation** : la médiane `|C_o|` à p = 0.50 reste à **quelques milliers** sur tous les L
(typiquement 0.1% à 0.9% de L²). À p = 0.52+, le géant devient rapidement dominant
(> 50% de L² à L=512, p=0.52).

**Tableau `Ψ(n)` pour L = 512** :

| n    | p=0.50 | p=0.52 | p=0.54 | p=0.56 | p=0.58 | p=0.60 | p=0.65 | p=0.70 |
|------|--------|--------|--------|--------|--------|--------|--------|--------|
| 1    | 1.000  | 1.000  | 1.000  | 1.000  | 1.000  | 1.000  | 1.000  | 1.000  |
| 2    | 0.875  | 0.938  | 0.938  | 0.969  | 0.969  | 0.969  | 0.969  | 0.969  |
| 4    | 0.812  | 0.875  | 0.906  | 0.938  | 0.938  | 0.969  | 0.969  | 0.969  |
| 8    | 0.688  | 0.844  | 0.875  | 0.906  | 0.938  | 0.969  | 0.969  | 0.969  |
| 16   | 0.656  | 0.844  | 0.875  | 0.906  | 0.938  | 0.969  | 0.969  | 0.969  |
| 32   | 0.656  | 0.844  | 0.875  | 0.906  | 0.938  | 0.969  | 0.969  | 0.969  |
| 64   | 0.656  | 0.844  | 0.875  | 0.906  | 0.938  | 0.969  | 0.969  | 0.969  |
| 128  | 0.625  | 0.812  | 0.875  | 0.906  | 0.938  | 0.969  | 0.969  | 0.969  |

**Observation critique** : `Ψ(n)` reste quasi-plat entre n = 8 et n = 128 pour chaque p.
Le fit log-y est dominé par la **transition initiale** (n = 1 → n = 2 : drop ~0.1)
et non par la décroissance sharpness attendue.

## 4. Verdict α(p) (4 L × 8 p)

**Fit log-y** de `Ψ(n) ~ exp(-α · n)` sur les seuils `n ∈ {1, 2, 4, 8, 16, 32, 64, 128}` :

| L \ p | 0.50 | 0.52 | 0.54 | 0.56 | 0.58 | 0.60 | 0.65 | 0.70 |
|-------|------|------|------|------|------|------|------|------|
| 64    | 0.0009 | 0.0007 | 0.0004 | 0.0003 | 0.0003 | 0.0001 | 0.0001 | 0.0001 |
| 128   | 0.0014 | 0.0007 | 0.0007 | 0.0007 | 0.0007 | 0.0005 | 0.0001 | 0.0001 |
| 256   | 0.0040 | 0.0015 | 0.0009 | 0.0007 | 0.0005 | 0.0005 | 0.0001 | 0.0001 |
| 512   | 0.0024 | 0.0010 | 0.0005 | 0.0004 | 0.0002 | 0.0001 | 0.0001 | 0.0001 |

**R² des fits log-y** :

| L \ p | 0.50 | 0.52 | 0.54 | 0.56 | 0.58 | 0.60 | 0.65 | 0.70 |
|-------|------|------|------|------|------|------|------|------|
| 64    | 0.262 | 0.334 | 0.213 | 0.262 | 0.262 | 0.079 | 0.079 | 0.079 |
| 128   | 0.252 | 0.221 | 0.221 | 0.282 | 0.282 | 0.292 | 0.079 | 0.079 |
| 256   | 0.731 | 0.541 | 0.456 | 0.310 | 0.348 | 0.348 | 0.079 | 0.079 |
| 512   | 0.397 | 0.372 | 0.223 | 0.252 | 0.159 | 0.079 | 0.079 | 0.079 |

**Verdict** : `α` mesuré est **très petit** (10⁻⁴ à 10⁻³) et **R² est bas** (0.08-0.73).
Le critère d'acceptance §8 (R² > 0.90 sur ≥ 75% cellules p ≥ 0.55) **n'est atteint pour aucune cellule**.

## 5. Verdict `α ~ (p - 1/2)`

**Régression log-log** de `α(p)` vs `p - p_c = p - 1/2` (en utilisant `p > 0.50` uniquement) :

| L | slope | R² | Cible (2D) |
|---|-------|----|-----------|
| 64  | **-1.110** | 0.860 | 1.000 |
| 128 | **-1.068** | 0.616 | 1.000 |
| 256 | **-1.393** | 0.834 | 1.000 |
| 512 | **-1.303** | 0.885 | 1.000 |

**Verdict** : le **signe de la pente est opposé** à la prédiction théorique.
La cible `(p - 1/2)^{d-1} = (p - 1/2)^1` est une fonction **croissante** de p,
mais l'alpha mesuré **décroît** quand p augmente (slope ≈ -1.0 à -1.4).

**Explication** : la décroissance de `Ψ(n)` aux seuils `n ∈ {1, ..., 128}` est
dominée par la **probabilité que `|C_o| < 2`** (i.e., que l'origine n'ait qu'un
seul voisin ouvert). Cette probabilité est ≈ `4p(1-p)^3` (voisin ouvert × 3 voisins
fermés), qui **décroît** avec p pour p > 0.25. C'est un effet de **petit n**,
pas de la sharpness exponentielle sharpness qui exigerait `n ~ médiane du géant`.

## 6. Verdict global — palier 4 non mesurable à L ≤ 512

**Constat** : la décroissance sharpness `Ψ(n) ~ exp(-α · n)` **n'est pas visible** dans
la fenêtre `n ∈ {1, ..., 128}` à L ≤ 512. La transition initiale (n = 1 → n = 2)
domine le fit, et son signe est opposé à la prédiction théorique.

**Causes identifiées** :
1. **Seuils `n` trop petits** : pour p proche de 1/2, la médiane du géant est de
   quelques milliers à 2×10⁵, donc `n ≤ 128` est dans le régime **sub-géant**
   (où la décroissance est dominée par la géométrie locale, pas par la sharpness).
2. **L = 512 insuffisant** : pour atteindre le régime où `n ≫ médiane du géant`
   tout en restant en deca de L², il faudrait L = 1024 ou 2048.
3. **Fit à un seul exposant** : la queue réelle est mieux décrite par
   `Ψ(n) ~ n^β exp(-α · n)` (correction polynomial-log), pas une exponentielle pure.

**Convention honnête** : le palier 4 est documenté comme **non concluant** à
L ≤ 512, et la **borne sharpness n'est pas mesurée empiriquement** sur cette
fenêtre — c'est le résultat physique de l'étude. Les valeurs publiées
(α entre 10⁻⁴ et 10⁻³, R² < 0.90 partout) sont **fidèles aux simulations** et
n'ont pas été ajustées pour atteindre la cible.

## 7. Perspectives

**Trois voies pour un palier 4b concluant** :

1. **L = 1024 ou 2048** : médiane du géant à 10⁶-10⁷, fenêtre de seuils `n ∈ {10³, ..., 10⁶}`
   accessible. Wall-clock ~30-60 min (10× le palier actuel).
2. **Seuils `n` log-espacés jusqu'à `L²/2`** : explorer la queue au-delà de la médiane
   du géant, où la décroissance exponentielle sharpness domine. Combine avec L = 1024+.
3. **Modèle à 2 paramètres** : `Ψ(n) ~ n^β exp(-α · n)`, fit non-linéaire
   `scipy.optimize.curve_fit`, séparer la correction polynomial-log de l'exposant sharpness.

**Héritage palier 03c** : la convergence asymptotique est souvent **bloquée** à L ≤ 512
(β/ν = 0.1062 vs cible 5/36 = 0.1389), et la convention est de **publier** les mesures
directes sans cherry-picking. Le palier 4 hérite de cette limitation structurelle.

**Prochaine étape** : si une des 3 voies est jugée prioritaire, créer une issue fille
`#19494-palier-4b` pour cadrer le nouveau sweep. Sinon, le plan #19494 est **clos**
après ce palier (palier 03 critique, 03b L=128/256, 03c L=512, 04 sharpness
non mesurable — tous livrés ou documentés).

---

**Cycle c.1108, lane `myia-po-2023:CoursIA-2`** : palier 4 sharpness **exécuté et documenté**.
Verdict honnête : **palier non mesurable à L ≤ 512 sur les seuils `n ∈ {1, ..., 128}`**.
PR à publier. Plan #19494 clos par ce palier (3 paliers critiques convergents + 1 palier
sharpness non mesurable, tous documentés).
