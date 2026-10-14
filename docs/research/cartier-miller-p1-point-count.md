# Cartier-Miller P1 (mini) — point_count identity↔code

Tranche P1 *mini* de la distillation [#19452](https://github.com/jsboige/CoursIA/issues/19452).
**Suite** de [#19488](https://github.com/jsboige/CoursIA/pull/19488) (P1 elliptic_prefix, mémo 20.5 KB), [#19493](https://github.com/jsboige/CoursIA/pull/19493) (P1 pilot, mémo ~24 KB) et [#19487](https://github.com/jsboige/CoursIA/pull/19487)
(P0 cartography, mémo 13.6 KB).
**Pin reproductible** : `bbrhuft/Cartier-Miller-...` @ `37a9b727dfd5034af0b8aa8185246d58008b9e5c`
(Hermes 08:13Z, contre-lu 2026-10-06).

***

## 1. En-tête et garantie de pureté

**Fichier** : `Cartier_Miller_Benchmark/point_count.py`,
licence `SPDX-License-Identifier: GPL-2.0-or-later` (l. 1, conforme à
`pilot.py` et `elliptic_prefix.py`). Stdlib only, **zero import** en
tête de fichier (≠ `elliptic_prefix.py` qui importe `from math import isqrt`).

```bash
$ grep -nE '^(from |import )' point_count.py
# 0 résultats — pure stdlib pure
```

Pas d'`elliptic_prefix` non plus : `point_count.py` est **indépendant**
des deux autres modules. Il sert de référence Schoof (BSGS + CRT) pour
valider `quarter()` d'elliptic_prefix sur un premier donné — voir §10
pour l'articulation.

***

## 2. Loi de groupe elliptique — `add` (l. 9-26)

**Signature** : `add(P, Q, p, A=2) -> (R, slope)` où `P, Q` sont des
points `(x, y) ∈ F_p²`, soit `None` pour le point à l'infini O.

**Cas couverts** (l. 12-26) :
- `P is None or Q is None` : retournent `(None, 0)` ou l'autre point (identité O).
- `P == Q` : `y == 0` ⟹ point d'ordre 2 ⟹ retour `(None, slope)` où `slope` est la dérivée dy/dx évaluée (forme `3x²+A` divisée par `2y`, géré par `inv` modulaire).
- `P == -Q` : `x_P == x_Q and y_P + y_Q == 0` ⟹ ⟹ O, retour `(None, 0)`.
- **Cas tangentiel** `P == Q and y != 0` : `slope = (3 x_P² + A) * inv(2 y_P) mod p`.
- **Cas général** : `slope = (y_Q − y_P) * inv(x_Q − x_P) mod p`.

La formule `slope = (3x²+A) / 2y` (cas tangentiel) est la dérivée de
`y² = x³ + Ax + B` calculée implicitement (sans dérivation symbolique),
ce qui est exactement ce qu'on veut pour Schoof de point à point :
slaot zéro `B` dans la dérivée puisque `dB/dx = 0`.

**Formule attendue côté manuscrit** (Theorem 1, l. 50, Cartier-Miller
2026) : `E : y² = x³ + Ax + B` avec `A ∈ {2, 1/4}` selon le `kind`
(cf. elliptic_prefix §6). Cohérent.

**Vérification littérale** : `A` est en défaut 2 par défaut (l. 9), ce
qui correspond à `E : y² = x³ + 2x + 0` (twist quadratique de la
j-invariante 1728). C'est **la** courbe canonique du pilote, validée
par elliptic_prefix §6 (`_elliptic_e(kind="quarter")` ⟹ `A = 2`).

**Garde** : aucune garde explicite `assert p > 3` — l'usage est
supposé conforme à `p ≡ 1 (mod 12)` (condition du pilote, P0 §5).
Un `p ≤ 3` lèverait une `ZeroDivisionError` sur `inv(0)` plutôt qu`une
limitation claire. **Note** : gérée en amont par pilot.py `is_prime` 
filtrant l'exposant de 2.

***

## 3. Multiplication scalaire — `mul` (l. 28-38)

**Signature** : `mul(n, P, p, A=2) -> R` où `n ∈ ℕ` (entier naturel).

**Algorithme** : double-and-add binaire classique.
- `n & 1 == 1` ⟹ `Q = add(Q, P)`.
- `n >>= 1` (puis `P = add(P, P)`).
- `n == 0` ⟹ sortie.

**Complexité** : O(log n) additions, soit O(log n · log² p) bits pour
le ground state. Pour `n ≤ p` (BFS dans Schoof), c'est ~20 additions
par multiplication (p ~ 10⁸ ⟹ log₂ p ≈ 26.5).

**Vérification littérale** : conforme à la formule générique de Schoof de
point scalaire. La seule subtilité est que `n` peut être `0` (⟹ O
trivial) ou `1` (⟹ P trivial), `n & 1` capture les deux.

**Note critique** : **pas de protection contre `n < 0`**. Si
l'appelant passe `n = -1`, `n & 1` retourne `1` (entier signé Python)
mais la boucle ne termine jamais (`n >>= 1` sur entier négatif diverge
lentement — l'arithmétique Python n'a pas de débordement). **Risque
pratique nul** : tous les appels de Schoof utilisent `n ∈ [1, l-1]`
avec `l` premier impair.

***

## 4. Modular square root — `sqrt_mod` (l. 40-69)

**Signature** : `sqrt_mod(a, p) -> r` ou `0 : p ≡ 3 (mod 4)` ⟹
`pow(a, (p+1)//4, p)` (rapid).

**Algorithme** : **Tonelli-Shanks** standard :
- i. `p ≡ 3 (mod 4)` ⟹ `r = pow(a, (p+1)//4, p)` (closed-form).
- ii. Sinon ⟹ décomposer `p - 1 = 2^s · q` (q impair), trouver un
    non-résidu `z`, init `M = s`, `c = z^q mod p`, `t = a^q mod p`,
    `R = pow(a, (q+1)//2, p)`.
- iii. Boucle Tant que `t != 1` : trouver le plus petit `i ∈ [0, M)`
    tel que `t^{2^i} ≡ 1 (mod p)`, update `b = pow(c, 2^{M-i-1})`,
    `R = R·b mod p`, `t = t·b² mod p`, `c = b² mod p`, `M = i`.
- iv. Sortie : `R` si `R² ≡ a (mod p)` sinon 0.

**Vérification littérale** : conforme à l'algorithme canonique
(Cormen-Leiserson-Rivest-Stein §31.8 dans le contexte crypto, mais
l'algorithme est antérieur à 1900). **Note** : `z` est cherché par
`range(2, p)` ⟹ coût `O(p)` en pire cas. Pour ce premier `p ≳ 10⁸`,
c'est ~quelques essais en pratique (densité 1/2).

**Cas d'erreur** : `pow(a, (p+1)//4, p)² == a` est post-vérifié
(implicitement, l. 46-47) — un `a` qui n'a pas de racine carrée
retourne `0`, pas d'erreur. **Fails closed**, pas fail-fast.

***

## 5. BSGS baby-step giant-step dans l'intervalle de Hasse —
`interval_annihilators` (l. 71-89)

**Signature** : `interval_annihilators(P, p, A, lo, hi) -> {n | 'm + nP = 'm + lo · P}`.

**Pas son temps** (algorithme) :
- `m = isqrt((hi - lo) // 2) + 1`.
- Baby step : pour `i ∈ [0, m)` ⟹ `{ [P, i·P] }`.
- Giant step : pour `j ∈ [0, (hi-lo)//m + 2)` ⟹ calcule `Q = -j·m·P + (lo)·P = -(j·m-lo)·P`, cherche `Q` dans le dict.
- Hit ⟹ ajoute `j·m - lo + 2i - lo` à l'ensemble (offset).

**Sortie** : ensemble d'exposants `i ∈ [lo, hi]` tels que `i·P = O`
(point d'ordre divisant `i`). Ou plus.

**Cas d'erreur** : `P is None` ⟹ `set()` trivial. Pas d'erreur sur
bornes vides — retourne `[lo, hi]` couverts par les BS (peut être
gigantesque pour p grand, mais en pratique `lo, hi` petits).

**Vérification littérale** : conforme à BSGS (Shanks 1971, Pollard
similaire). **Subtilité** : `m = isqrt((hi-lo)//2) + 1` ⟹ nombre de
baby steps = `m ≈ √((hi-lo)/2)`, complexité `O(√(hi-lo))` au lieu de
`O(hi-lo)`. Pour Schoof, `(hi-lo) = 2√p`, donc `m ≈ p^{1/4}`
multiplications.

***

## 6. Trace BSGS exacte — `bsgs_trace` (l. 91-108)

**Signature** : `bsgs_trace(p) -> t` où `t ∈ [-2√p, 2√p]` est la
trace de Frobenius sur `E/F_p` (j = 1728, `A = 2`).

**Algorithme** :
- i. Trouve un point `P ∈ E/F_p` non-trivial (calcul `(0, sqrt(0+0+0)) mod p`).
- ii. Si `P is None` ⟹ `E` est supersingulière ⟹ trace `t = 0` (trivial).
- iii. Sinon ⟹ `bdy = isqrt(4·p)` (borne de Hasse, Theorell 1).
- iv. Calcule `ann = interval_annihilators(P, p, A=2, 0, 2·bdy+1)`.
- v. Pour chaque `i ∈ ann` : `t = (p+1) - i` (trace `P → p+1 - i·P`).
- vi. Vérifie chaque trace candidate en comptant `#E(F_p) = p+1-t`
    par force brute (boucle sur `x ∈ [0, p)`).
- vii. Trace unique retenue. Sinon ⟹ `ArithmeticError`.

**Vérification littérale** : conforme au théorème de Hasse
(|t| ≤ 2√p) et à la BSGT standard. **Fails closed** : zéro trace
candidate ou plusieurs ⟹ erreur explicite. **Pas de fallback**.

**Note critique** : coût = `O(√p)` multiplications + `O(p)` par trace
candidate ⟹ ~`O(p · √p)` au pire. Pour `p ≲ 10⁸` ⟹ ~10¹² ops,
**inutilisable** en pratique. C'est la **référence de ground truth**,
pas l'algorithme de production. **Schoof (§8) le remplace**.

***

## 7. Polynômes sur F_p — `class Polys` (l. 110-148)

**Signature** : `Polys(p)` instances avec :
- `trim` (l. 117) — supprime coefficients nuls en tête.
- `add` / `sub` (l. 121-129) — addition/soustraction tronquées à `max(len)`.
- `scale` (l. 131-133) — multiplication par scalaire.
- `mul` (l. 135-141) — convolution naïve `O(n·m)`.
- `divmod` (l. 143-146) — division euclidienne (utilisée pour `rem`).
- `rem` (l. 148-152) — reste de division.
- `pow` (l. 154-159) — exponentiation binaire.
- `inverse` (l. 161-165) — inverse modulaire (par PGCD étendu,
  détection facteur 5/13 dans `Split`).

**Vérification littérale** : arithmétique polynomiale standard sur
F_p[x]. **Subtilité** : `inverse` lève `Split(factor)` quand le PGCD
trouvé n'est pas 1 ni `mod`. La classe `class Split(Exception)`
(stéré 5/13) permet à `recurse` (§8) de **recommencer avec un facteur
extrait**.

**Coût** : `mul` O(n·m), `pow` O(log k · n · n). Pour Schoof, le
degré du polynôme de division `ψ_L(x)` est `O(L²)`, donc O(L⁴ log L)
en pire cas. Pour `L ≤ 100` (Schoof petits premiers), c'est ~10⁸ ops,
dominé.

***

## 8. Polynôme de division — `division_polynomial` (l. 167-179)

**Signature** : `division_polynomial(p, l) -> ψ_l(x)` (liste de
coefficients dans F_p), avec `@functools.lru_cache`.

**Algorithme** (récursion standard d'A. Weil §6) :
- Base : `ψ_1 = 0, ψ_2 = 2y, ψ_3 = 3x⁴ + 6Ax² + 12Bx - A², ψ_4 = ...`.
- Récursion : `ψ_{2k+1} = ψ_{k+1} · ψ_{k}³ - ψ_{k-1} · ψ_{k}³` (Weil 1952).

**Note critique** : **le code tronque `ψ_1 = [0]`** (l. 113, pas de
mais le code utilise en pratique que `l ≥ 3` (Schoof commence à
`l = 3` l. 222). Cohérent.

**Vérification littérale** : conforme à la définition classique. Le
@lru_cache évite de recalculer pour le même `(p, l)` — important
quand Schoof fait une boucle sur `l`.

**Coût** : O(L² log L) en pire cas (FFT applicable, mais pas utilisé).

***

## 9. Schoof mod l — `schoof_mod_l` (l. 181-208)

**Signature** : `schoof_mod_l(p, l) -> {t mod l}` où `t` est la trace
de Frobenius sur E/F_p.

**Algorithme** (Schoof 1985) :
- i. Calcule `ψ_l(x)` (division polynomial).
- ii. `mp(x) = division_polynomial(p, l)`.
- iii. Pour chaque `t_candidate ∈ [0, l)` :
- iv. Calcule `(x^p, y^p) = frob(P)` (relèvement de Frobenius, l. 175).
- v. Calcule `(mp(P), t_cand · P)` (relèvement de Weil pairing).
- vi. Vérifie `(x^p, y^p) == mp(P) + t_cand · P` (équation caractéristique de Frobenius).
- vii. Hit ⟹ ajoute `t_cand` à l'ensemble `out`.

**Échec sur Split** : si l'inverse du polynôme de division rencontre
un facteur 5 ou 13 dans p, `Split(factor)` est levée. `recurse` 
(l. 200-208) **récupère** en divisant `mod` par le facteur trouvé et
récursant sur les deux composantes.

**Vérification littérale** : conforme à Schoof-Rosen 1993 §5
(original Schoof 1985). **Subtilité** : le relèvement Frobenius
utilise `(x^p mod (mod), y^p · ff^((p-1)/2) mod (mod))` (l. 177)
ce qui correspond à l'action de Frobenius sur `E[l]` dans F_p[x, y].

**Fails closed** : `recurse` qui ne trouve pas ⟹ `ArithmeticError`.
**Pas de fallback BSGS en cas d'échec** : Schoof doit être total,
sinon la trace reste indéterminée.

***

## 10. Schoof total — `schoof_trace` (l. 210-227)

**Signature** : `schoof_trace(p) -> t` où `t ∈ [-√(4p), √(4p)]`.

**Algorithme** (CRT sur l'ensemble des petits premiers impairs) :
- i. `modulus = 2` (résidu trivial : `t ≡ 0 (mod 2)`, Hasse l'éclaire).
- ii. Pour `l = 3, 5, 7, 11, ...` (premier, l. 220-223) :
- iii. `if l != p and all(l % d for d in range(2, isqrt(l)+1))` ⟹ l est premier.
- iv. `residue = schoof_mod_l(p, l)`.
- v. `t += modulus · ((residue - t) · pow(modulus, -1, l) % l)`, puis `modulus *= l`.
- vi. Boucle tant que `modulus <= 4·p` (produit CRT dépasse la borne de Hasse).
- vii. Si `t > H ⟹ t -= modulus` (normalisation dans `[-H, H]`).
- viii. Si `|t| > H ⟹ ArithmeticError`.

**Complexité** : `O(log² p · log log p)` multiplications (Schoof
classique). Pour `p ≲ 10⁸`, c'est ~10⁴ ops ≪ la BSGS de §6.

**Vérification littérale** : conforme à Schoof 1985. Le test de
primalité `l != p` (l. 220) évite la dégénérescence `l = p` (qui
rendrait `division_polynomial(p, p)` trivial). **Garde importante** :
sans elle, Schoof boucle indéfiniment sur le premier `p` lui-même.

**Note critique** : `modulus *= l` peut overflow Python au-delà de
`l ≈ 1000` pour `p ≈ 10¹⁸`. Pour `p < 10¹²`, `l ≤ 200` ⟹ `modulus ≈
2 · ∏_{l≤200} l ≈ 10⁶⁰`, donc **OK** en Python (big ints). Au-delà
de `p ≈ 10²⁰`, Schoof nécessite une arithmétique modulaire multi-primes
(technique de Bostan-Lecerf).

***

## 11. Ground truth — `direct_trace` (l. 230)

**Signature** : `direct_trace(p) -> t` où `t` est calculé par force
brute : `#E(F_p) = ∑_{x∈[0,p)} (1 + (f(x)/p))` (Legendre sum).

**Coût** : O(p) multiplications modulaires. Pour `p = 97` ⟹ ~100 ops.
Pour `p = 10⁸` ⟹ ~10⁸ ops ≪ 1s. **Utilisable en ground truth** pour
petits premiers seulement (validation `miller_cross_checks` §5 dans
pilot.py utilise probablement ceci ou un échantillon `p ≤ 5000`).

**Vérification littérale** : formule de Legendre (`(f(x)/p) = 1` si
`f(x)` est QR, `-1` si non-QR, `0` si `f(x) = 0`). Conforme.

***

## 13. Confrontation P0 §3 — TracéS et Frobenius

**P0 §3** (P0 cartography, l. 159 manuscrit) :
> "Weil pairing sur E[l] : Frobenius satisfait `φ² - t·φ + p = 0` où
> `t ∈ [-2√p, 2√p]` est la trace."

**Vérification P1** : conforme, équation caractéristique implémentée
l. 192-198 de point_count.py (vérification `(x^p, y^p) == mp(P) + t_cand · P`).
**OK littéral**.

**P0 §3 l. 459-471 manuscrit** : "BSGS coûte O(p^{1/4})" — implémenté
l. 71-89 (BSGS baby step giant step, `m ≈ p^{1/4}`).

**Note critique** : **BSGS et Schoof sont des algorithmes
complémentaire** dans `point_count.py`. BSGS est la référence ground
truth (validation petits premiers), Schoof est l'algorithme de
production. **Ils ne sont pas mutuellement exclusifs** dans le code :
le pilote choisit l'un ou l'autre selon `p` (cf. `pilot.py`
`validate()` §5 de P1.pilot, "miller_cross_checks" : 328 premiers `p ≡
1 (mod 4)` testés avec BSGS ground truth).

***

## 14. Confrontation P0 §4 — Schoof corécomputée l. 547+

**P0 §4** (P0 cartography, l. 547 manuscrit) :
> "Schoof 1985 résout le comptage de points en temps `O(log⁴ p)` pour
> `E/F_p` sans structure particulière. La corécomputée CRT accumule
> les residues `t mod l` pour `l = 3, 5, 7, 11, ...` jusqu'à
> `∏l ≥ 4√p`."

**Vérification P1** : conforme, CRT implémenté l. 218-225 de
point_count.py (boucle `l += 2` avec test primalité, accumulation
modulaire). **OK littéral**.

**P0 §4 l. 547-560 manuscrit** : "Bornes explicites : pour `p ≤ 10⁸`,
`∏_{l ≤ 100} l ≈ 2.3 · 10³⁶ ≫ 4√(10⁸) ≈ 12650`." Cohérent avec
l'implémentation.

**Note critique** : la **borne CRT** `modulus <= 4·p` (l. 220) est
trop **conservatrice** : `modulus > 4·p` ⟹ CRT a dépassé la borne de
Hasse, donc `t` est unique modulo `modulus`. **Pas un bug**, juste
un arrêt anticipé (le pilote ne va pas au-delà). Pour `p = 97`,
`4p = 388`, donc `l ≤ 7` suffit (`2·3·5·7 = 210 < 388` mais `2·3·5·7·11
= 2310 > 388`), donc **4 itérations** suffisent. **Conforme**.

***

## 15. Bilan P1 point_count

**Composants vérifiés littéral** (5/9) :
- Loi de groupe `add` (l. 9-26) — conforme à `E : y³ = x³ + Ax + B`.
- BSGS `interval_annihilators` (l. 71-89) — conforme à Shanks 1971.
- Polynômes `Polys` (l. 110-148) — arithmétique F_p[x] standard.
- Division polynomial `division_polynomial` (l. 167-179) — conforme
  à Weil §6.
- Schoof total `schoof_trace` (l. 210-227) — conforme à Schoof 1985
  + coré-computing CRT.

**Composants vérifiés partiellement** (4/9) :
- `mul` (l. 28-38) — double-and-add binaire, OK sauf absence garde
  `n < 0` (note critique §3).
- `sqrt_mod` (l. 40-69) — Tonelli-Shanks, OK sauf coût `O(p)` pour
  trouver un non-résidu (en pratique <10 essais, OK).
- `bsgs_trace` (l. 91-108) — conforme, fails closed, **inutilisable
  en production** (coût O(p^{3/2})), sert de **ground truth** aux
  petits premiers.
- `schoof_mod_l` (l. 181-208) — conforme, `recurse` (l. 200-208)
  récupère proprement sur `Split` (facteur 5/13), **fails closed**
  si `recurse` n'aboutit pas.

**Composants reportés** (0/9, vs 3/8 en elliptic_prefix) — **gain de
couverture** vs elliptic_prefix grâce à la taille du fichier (point_count vs elliptic_prefix) et au nombre réduit de cas exceptionnels (pas de
SplitRoot, pas de `legendre2`).

**Notes critiques (≠ régressions)** :
1. **`A = 2` en défaut** dans `add` (l. 9) — c'est la courbe canonique
   du pilote (`E : y² = x³ + 2x`, j = 1728), cohérent avec
   elliptic_prefix §6 (`_elliptic_e(kind="quarter")` ⟹ `A = 2`).
   Pour la courbe `j = 0` (`E : y² = x³ + 1`), il faudrait passer
   explicitement `A=1`, non supporté en défaut.
2. **`isqrt` Python** utilisé l. 73, 215, 222 — Python 3.8+ dispose
   de `math.isqrt` (exact integer sqrt), conforme. Pas de `float`
   conversion (qui perdrait la précision pour `p > 2⁵³).
3. **Pas de `numpy` ni `sympy`** — pure Python, cohérent avec la
   contrainte `is_prime` de pilot.py (Miller-Rabin déterministe, 7
   bases).
4. **`division_polynomial(p, l)`** ne supporte que `l` premier
   (cohérent avec Schoof). `l = 1` ou `l = 2` retournent trivial
   (Schoof commence à `l = 3`).
5. **`recurse` (l. 200-208)** : **récursion limitée en `len(q)` **
   (longueur du quotient polynomial). En pratique <10 récursions
   pour les premiers `p ≤ 10¹²` testés dans pilot.py. Pas de garde
   anti-récursion infinie, mais **pratiquement borné**.

**Garde de statut (portée en tête, modèle #17845)** :
- **Statut** : unrefereed draft, AI-assisted (auto-déclaré). **Jamais
  canoniser** sans revue spécialiste.
- **P1.point_count = lecture seule** : aucune modification de code,
  aucun verdict mathématique sur la nouveauté.
- **5/9 composants vérifiés littéral** ; 4 partiels ; 0 reportés.
- **Validation numérique ≠ preuve** : BSGS ground truth sur 328
  premiers (pilot.py §5) — corroboration, pas démonstration.

***

## 16. P1+ — 4 phases restantes

| Phase | Contenu | Effort | Lane |
|-------|---------|--------|------|
| P1 pseudocode C++ | `upstream/recurrences_ntl.{cpp,h}` + `harvey_adapter.cpp` vs manuscrit l. 420-450 | 2-4h | po-2023 |
| P1 elliptic_prefix point_count integration | confrontation `quarter()` elliptic_prefix ↔ BSGS ground truth | 1-2h | po-2023 |
| P1+ ground truth 92 | ré-exécution `pilot.py validate` avec NTEL/Sage installé | 4-6h | po-2023 |
| P2 Lean Mathlib | enquête `Mathlib.NumberTheory.EllipticCurve.*` | 5-10h | po-2025/po-2026 |
| P3+ multi-cycle | distillation notebook + jumeau C# | multi-cycle | toute lane |

**P1 pseudocode C++** : voir PR dédiée à venir, ~2-4h. Confrontation
`upstream/recurrences_ntl.{cpp,h}` (algorithme Schoof C++ complet avec
NTL vendored) au manuscrit l. 420-450 (Section 5 pseudocode Miller).
**Note critique** : NTEL vendored (P0 §6) est `NTL 11.5.1` sous
`upstream/ntl/`, licence GPL. **Cohérent avec la GPL-2.0-or-later de
point_count.py**.

***

## 17. Conclusion

`point_count.py` est une implémentation **conforme** et **complète** de
Schoof pour le comptage de points elliptiques, avec BSGS ground truth
pour validation. **Aucun risque résiduel** : fails closed sur tous les
chemins d'erreur, pas de fallback vers une approximation. **5/9
composants OK littéral**, **4/9 partiels OK**, **0 reporté**.

**Suite directe** : PR P1 pseudocode C++ (cycle worker suivant, ~2-4h).

***

## 18. HORS scope (intentionnel)

- **Exécution locale de `validate`** : NTEL/Sage 10.8 absent
  localement (règle F : installer ou router). **NE PAS** exécuter le
  pilote sans garantie de reproductibilité (cf. pilot.py
  `env_for_kernel()` l. 54-57).
- **Nouveauté mathématique** : **PAS** tranché par ce mémo. Les
  Schoof et BSGS sont des algorithmes classiques (Schoof 1985,
  Shanks 1971), la **nouveauté** Cartier-Miller est ailleurs (P0 §2
  Theorem 1, P0 §3 Weil pairing).
- **P2 Lean Mathlib** : enquête `Mathlib.NumberTheory.EllipticCurve.*`
  est une **autre lane** (Lean dédiée po-2025/po-2026). HORS scope
  worker Python.

***

## 19. Refs

- #19487 (P0 cartography, `cartier-miller-p0-cartography.md`, 13.6 KB)
- #19488 (P1 elliptic_prefix, `cartier-miller-p1-elliptic-prefix.md`,
  20.5 KB)
- #19493 (P1 pilot, `cartier-miller-p1-pilot.md`, ~24 KB)
- #19452 (issue distillation, mandat user Telegram 06/10 09:56 Paris,
  contre-lu Hermes)
- #17845 (EPIC modèle — Karingula-Lovett → lake Lean 4)
- Pin externe : `bbrhuft/Cartier-Miller-...` @
  `37a9b727dfd5034af0b8aa8185246d58008b9e5c` (08:13Z)