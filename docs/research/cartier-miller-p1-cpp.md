# P1 pseudocode C++ identity↔code — Cartier-Miller evaluation of genus-one coefficient sums

**Pin :** bbrhuft/Cartier-Miller-evaluation-of-genus-one-coefficient-sums @ `37a9b72` (clone local `.scratch`)
**Scope :** Fichiers C++ = `harvey_adapter.cpp` (87 l.) + `upstream/recurrences_ntl.{h,cpp}` (43/1301 l.) + `upstream/hypellfrob.{h,cpp}` (83/717 l.). Lecture intégrale sans EOF.
**Méthode :** lecture ligne-par-ligne, confrontations à `point_count.py` (231 l.), `hypellfrob.pyx` (253 l.), `pilot.py`, `benchmark_engine.py`, `SOURCE_PROVENANCE.json`, `build.sh`, `README.md`, `VALIDATION.md`, manuscrit `.paper.txt` l. 330-490.
**Précédents :** P0 cartography (#19487), P1 elliptic_prefix (#19488), P1 pilot (#19493), P1 point_count (#19499). Ce mémo est le 5e volet.
**Statut dépôt :** distillation didactique d'un manuscrit non-référé (MIT externe pour le PDF), dépôt GPL-2.0-or-later. Aucun verdict de nouveauté mathématique n'est porté ici. Lecture seule — aucun fichier C++ modifié.

---

## 1. En-têtes, licences, dépendances (#include), pureté

### 1.1 Licences et provenance

| Fichier | Licence | Preuve | Origine |
|---|---|---|---|
| `recurrences_ntl.h` | GPL-2.0+ (header hypellfrob 2.1.1) | l. 5-21 | David Harvey 2007/2008 |
| `recurrences_ntl.cpp` | GPL-2.0+ | l. 5-22 | idem |
| `hypellfrob.h` | GPL-2.0+ | l. 5-22 | idem |
| `hypellfrob.cpp` | GPL-2.0+ | l. 5-22 | idem |
| `harvey_adapter.cpp` | **GPL-2.0-or-later SPDX** | l. 1 « Quarter-prefix adapter, GPL-2.0-or-later; uses unchanged Sage/Harvey sources » | projet |

Provenance mesurée (`upstream/SOURCE_PROVENANCE.json` l. 2-3) : `sage_tag: 10.8`, commit Sage `981d7d71a2738778c9e3fb4fdf67a0fd3ce0c19c`, 6 entrées (les 4 sources + `hypellfrob.pyx` + `COPYING.txt`) chacune avec URL raw.githubusercontent + SHA256 (l. 4-35). `upstream/COPYING.txt` est le texte GPL de Sage. Le README l. 131-135 confirme : sources Harvey « unchanged from the retained pilot », notices préservées, adaptateur et code neuf du dépôt en GPL-2.0-or-later, `elliptic_prefix.py` retient le notice MIT de l'archive d'origine (pas de licence tierce inventée).

### 1.2 Dépendances #include

- `recurrences_ntl.h` : `<NTL/ZZ.h>`, `<vector>` (l. 26-27).
- `recurrences_ntl.cpp` : `<NTL/ZZ_pX.h>`, `<NTL/mat_ZZ_p.h>`, `<NTL/lzz_pX.h>`, `<NTL/mat_lzz_p.h>`, `<cassert>`, `"recurrences_ntl.h"` (l. 26-31) + `NTL_CLIENT` (l. 34).
- `hypellfrob.h` : `<NTL/ZZ.h>`, `<NTL/ZX.h>`, `<NTL/mat_ZZ.h>`, `<vector>` (l. 26-29).
- `hypellfrob.cpp` : `"hypellfrob.h"`, `"recurrences_ntl.h"`, `<cassert>` (l. 27-30) + `NTL_CLIENT` (l. 32).
- `harvey_adapter.cpp` : `<NTL/ZZ_pX.h>`, `<NTL/lzz_pX.h>`, `<NTL/mat_ZZ_p.h>`, `<NTL/version.h>`, `<NTL/BasicThreadPool.h>`, `"upstream/hypellfrob.h"`, `"upstream/recurrences_ntl.h"`, `<chrono>`, `<iostream>`, `<sstream>`, `<stdexcept>`, `<string>`, `<vector>` (l. 2-14), `using namespace NTL` (l. 15).

Build (`build.sh` l. 6-8) : `g++ -O3 -std=c++17 -pthread harvey_adapter.cpp upstream/recurrences_ntl.cpp upstream/hypellfrob.cpp -lntl -lgmp -o bin/harvey_adapter`. C++17, NTL+GMP système. Le script émet `bin/build_metadata.json` (version compilateur + commande exacte + horodatage UTC, l. 9-16) — garde de reproductibilité du build.

### 1.3 Garantie pureté

Les fichiers upstream ne contiennent **aucune I/O** (aucun `iostream`/`cstdio`), **aucun aléatoire**, **aucun thread**. Le seul état mutable est le modulus global NTL (`ZZ_p::init` / `zz_p::init`), toujours manipulé via `ZZ_pContext`/`zz_pContext` save/restore (hypellfrob.cpp l. 104-106/124, l. 176-177/192, l. 236-237/253, l. 288-299/708). `harvey_adapter.cpp` est le **seul** fichier avec I/O : `cin`/`cout`/`cerr` (l. 61-85) — la bibliothèque reste pure, l'adaptateur porte le protocole.

---

## 2. APIs publiques et signatures

Tout est dans `namespace hypellfrob` — **aucun `extern "C"`**. Trois points d'entrée publics :

```cpp
// recurrences_ntl.h l. 33-37 (template, 2 explicit instantiations recurrences_ntl.cpp l. 1285-1294)
template <typename SCALAR, typename POLY, typename POLYMODULUS,
          typename VECTOR, typename MATRIX, typename FFTREP>
void ntl_interval_products(std::vector<MATRIX>& output,
                           const MATRIX& M0, const MATRIX& M1,
                           const std::vector<NTL::ZZ>& target);

// hypellfrob.h l. 57-59
void hypellfrob_interval_products_wrapper(NTL::mat_ZZ_p& output,
                               const NTL::mat_ZZ_p& M0, const NTL::mat_ZZ_p& M1,
                               const std::vector<NTL::ZZ>& target);

// hypellfrob.h l. 77
int matrix(NTL::mat_ZZ& output, const NTL::ZZ& p, int N, const NTL::ZZX& Q);
```

**Note explicite demandée par le cahier des charges :** il n'existe **pas** de fonction `recurrences::recurrences` ni de « division polynomials » dans le C++. Le prompt supposait ces noms ; la réalité du code est `ntl_interval_products` (le moteur), `hypellfrob_interval_products_wrapper` (le routeur de précision) et `matrix` (le calcul de zeta, non utilisé par le benchmark). Les « division polynomials » vivent dans `point_count.py` l. 139-156, en Python.

Membres internes non exportés (visibles dans les .cpp mais hors headers) : `interval_products_wrapper` version vector (hypellfrob.cpp l. 86-126), `padic_xgcd` (l. 173-216), `padic_invert_matrix` (l. 234-267), helpers `conv(mat_ZZ,...)`/`to_mat_ZZ` (l. 41-61). Le wrapper Cython Sage (`hypellfrob.pyx` l. 64-70) déclare `cdef extern from "hypellfrob.h"` avec renommage `hypellfrob::matrix` → `hypellfrob_matrix` : c'est l'API consommée par Sage, distincte du pont du dépôt (section 5).

L'adaptateur expose sa propre API process-level : `main()` CLI avec `--version` (l. 54-57) et `--force-big` (l. 58), protocole stdin « une ligne = une requête » (l. 60-86).

**Graphe d'appels mesuré** (qui appelle quoi, depuis l'adaptateur) :

```
harvey_adapter calculate() l.21-51
 ├─ IsZero(L) → ident(P,2)                                l.31
 ├─ force_big → hypellfrob::ntl_interval_products<ZZ_p,...> l.33-36  (force ZZ_p)
 └─ sinon → hypellfrob::hypellfrob_interval_products_wrapper l.37
              └─ interval_products_wrapper (hypellfrob.cpp l.86)
                   ├─ !SinglePrecision → ntl_interval_products<ZZ_p,...> l.95-97
                   └─ SinglePrecision → zz_p::init + ntl_interval_products<zz_p,...> l.99-125
                        └─ ntl_short_interval_products (l.762) + dyadic_evaluation (l.351)
```

**Fonctions jamais appelées par le benchmark :** `matrix()` (hypellfrob.cpp l. 274-711 — tout le pipeline zeta de Monsky-Washnitzer), et ses deux sous-fonctions privées `padic_xgcd` (l. 173-216) et `padic_invert_matrix` (l. 234-267), appelées **uniquement** depuis `matrix()`. En revanche `matrix()` **est** consommée en amont par `hypellfrob.pyx::hypellfrob` (l. 158-252) dans Sage — le code n'est pas mort, il est hors périmètre du benchmark quarter-point. Le corps de `matrix()` reste néanmoins requises à la compilation (liées dans le binaire via `hypellfrob.cpp`).

---

## 3. Algorithmes principaux documentés

### 3.1 `recurrences_ntl.cpp` — produits d'intervalles de matrices ( moteur)

Le fichier cite explicitement ses fondations : Theorem 8 de [BGS] pour l'évaluation dyadique (l. 135-136), Corollary 10 de [BGS] pour l'évaluation multipoint (l. 449), Theorem 15 de [BGS] pour les produits d'intervalles (l. 723, 981). [BGS] = Bostan-Gaudry-Schost 2007 (README l. 135).

**a) Adaptateurs de templates ZZ_p↔zz_p** (l. 40-127). Deux colonnes de types (`SCALAR`/`POLY`/`VECTOR`/`MATRIX`/`POLYMODULUS`/`FFTREP`, tableau l. 44-52) + trois ponts explicites : `to_scalar` (l. 64-91), `forward_fft` (`ToFFTRep`/`TofftRep`, l. 94-109), `inverse_fft` (`FromFFTRep`/`FromfftRep`, l. 112-127). C'est ce qui permet au même code de tourner en précision simple (`zz_p`) et multi-précision (`ZZ_p`).

**b) `middle_product`** (l. 155-184). Produit médian : coefficients x^d..x^{2d} de f·g sans calculer le bas. FFT cyclique longueur 2d (l. 166-168), correction du wrap-around du terme x^{2d} de g (l. 172), terme x^{2d} calculé en boucle directe (l. 176-183). Crédité Hanrot-Quercia-Zimmermann (l. 150-152).

**c) `DyadicShifter`** (l. 203-329). Décale des valeurs d'évaluation : F(0),F(b),...,F(db) → F(a),F(a+b),...,F(a+db) (l. 190-195). Précalculs : `input_twist[i] = prod_{j≠i}(i-j)^{-1}` via factorielles cumulées (l. 232-258), `kernel[i] = (a+(i-d)b)^{-1}` via produits cumulés `accum`/`accum_inv` (l. 260-292 — technique des produits partiels et leurs inverses, une seule inversion), `output_twist[i] = b^{-d}·prod fenêtre` (l. 294-304). `shift()` (l. 310-328) : twist d'entrée → middle product contre kernel → twist de sortie. Precondition : 1..d+1 et a+ib inversibles (l. 197-200).

**d) `dyadic_evaluation`** (l. 349-441). Calcule P(a), P(a+2^t), ..., P(a+2^s·2^t) où P(x)=M(x+1)···M(x+2^s) (l. 333-337). Cas de base s≤1 évalué naïvement (l. 357-379). Cas général : récursion s-1 (l. 385-389), **deux** shifters (décalage de 2^{s-1} et de (2^{s-1}+1)·2^t, l. 391-396), double multiplication matricielle par blocs (l. 400-440). Format de sortie optimisé « colonnes-major » : n² vecteurs de longueur 2^s+1 (l. 339-342).

**e) `ProductTree`** (l. 467-525). Arbre de produits (x-a[0])···(x-a[n-1]) (l. 455-464), construction récursive mi-partie (l. 497-515), `new`/`delete` bruts (l. 511-512, 521-523 — pas de RAII, voir §8). Chaque nœud porte deux polynômes de scratch réutilisés entre appels pour éviter les réallocation (l. 477-482).

**f) `Evaluator`** (l. 534-605). Évaluation multipoint par descente de restes : un `POLYMODULUS` par nœud interne précalculé en ordre de parcours (l. 544-566), puis `recursive_evaluate` descend par `rem` successifs (l. 587-604), feuille = `eval` au point (l. 591-594).

**g) `Interpolator`** (l. 616-714). Interpolation aux points 0..L : `input_twist` factoriel symétrisé (l. 640-661), puis remontée d'arbre `combine` : f1·p2 + f2·p1 (l. 673-698). C'est le Corollary 10 de [BGS].

**h) `ntl_short_interval_products`** (l. 762-974). Produits sur intervalles courts, en 5 étapes numérotées dans le code : (1) interpolation de M(X, X+L) en polynôme via accumulateurs gauche/droite (l. 803-853) ; (2) décomposition des cibles en blocs de longueur L + reliquats (l. 855-890) ; (3) récursion sur les reliquats (l. 892-898) ; (4) évaluation multipoint par blocs de ≤L+1 points (l. 900-936) ; (5) fusion (l. 938-973). Le choix de L est heuristique : `L = 1+floor(sqrt(num_intervals·max_length))` si intervalles longs, `1+max_length/2` sinon (l. 785-801).

**i) `ntl_interval_products`** (l. 995-1279). Le moteur principal, en 4 étapes : **Step 0** (l. 1009-1136) — découpe dyadique : plus grand t avec 2^t(2^t+1) ≤ distance restante (l. 1036-1040), appel `dyadic_evaluation` (l. 1046-1047), puis fusion des sous-intervalles ne contenant **aucun** endpoint cible en une matrice « active » (l. 1049-1129) ; **Step 1** (l. 1138-1194) — identification des sous-intervalles de raffinement (segments de tête/queue des cibles non couverts par le dyadique), avec sentinelles `target.back()+10/+20` simplifiant les boucles (l. 1146-1148) ; **Step 1b** (l. 1200-1203) — récursion `ntl_short_interval_products` sur ces raffinements ; **Step 2** (l. 1207-1249) — fusion triée dyadique↔raffinement ; **Step 3** (l. 1251-1278) — reconstruction des produits cibles par multiplication en série. Asserts d'invariants aux jointures (l. 1136, 1205, 1249, 1267).

Les deux explicit instantiations finales (l. 1285-1294) matérialisent le template pour les colonnes `ZZ_p` et `zz_p`.

### 3.2 `hypellfrob.cpp` — routeur de précision + pipeline zeta

**a) `interval_products_wrapper`** (l. 86-126). Route selon `modulus.SinglePrecision()` (l. 92) : grand modulus → version `ZZ_p` directe (l. 95-97) ; petit modulus → bascule `zz_p::init` avec `zz_pContext` save/restore (l. 104-106), conversion aller des entrées par `to_mat_zz_p(to_mat_ZZ(...))` (l. 109-110), exécution `zz_p` (l. 114-116), conversion retour (l. 119-121), restauration du contexte (l. 124).

**b) `hypellfrob_interval_products_wrapper`** (l. 128-143). Enveloppe la version vector en matrice concaténée horizontalement (r×(r·n)) — c'est LE point d'entrée consommé par l'adaptateur (l. 37).

**c) `padic_xgcd`** (l. 173-216). Bézout a·f+b·g=1 mod p^N : XGCD mod p (l. 183-189), relèvement, puis **Newton quadratique** `prec *= 2` avec correction `a_adj = -(h·a) % g` (l. 206-213). Le commentaire l. 167-170 documente pourquoi NTL ne suffit pas : son xgcd n'est garanti que sur un corps — garde-fou contre la bibliothèque elle-même.

**d) `padic_invert_matrix`** (l. 234-267). Inversion mod p puis itération `B = (2I - BA)·B` (l. 263-266) — même méfiance documentée envers l'inversion NTL sur non-corps (l. 228-231).

**e) `matrix()`** (l. 274-711) — **non appelée par le benchmark** (cf. §2). Pipeline complet du Frobenius Monsky-Washnitzer : validations d'entrée (l. 276-286) ; matrices de réduction verticale M_V via `padic_xgcd` sur (Q, Q') donnant R_i, S_i avec x^i = R_i·Q + S_i·Q' (l. 310-331), entrées `(2t-1)R_i + 2S_i'` (l. 333-344), dénominateur D_V(t)=2t-1 (l. 346-352) ; matrices horizontales M_H^t(s) avec D_H^t(s)=(2g+1)(2t-1)-2s, t=(p(2j+1)-1)/2 (l. 354-389) ; Vandermonde inversée par `padic_invert_matrix` (l. 391-401) ; coefficients B_{j,r} via somme `(-1)^j Σ 4^{-k} C(2k,k)C(k,j)` et C_{j,r} = coeff de Q^j (l. 403-442) ; réductions horizontales — la plupart « by hand » sur vecteurs de longueur 2g+1 avec les formules explicites (l. 444-629), dont la réduction au dénominateur divisible par p (l. 568-590, asserts l. 575/586) et l'application des grandes matrices MH (l. 592-601) ; réductions verticales avec division par p explicite (l. 641-682, asserts l. 666/677) ; assemblage final mod p^N (l. 684-705).

### 3.3 `harvey_adapter.cpp` — le traducteur quarter-prefix

`calculate(p, L, force_big)` (l. 21-51) :
1. `ZZ_p::init(p)` (l. 23) — l'unique initialisation de contexte.
2. Construction de la matrice de récurrence 2×2 : `M0[0][0]=-1 ; M1[0][0]=2 ; M1[0][1]=4 ; M1[1][1]=4` (l. 26-27), c.-à-d. **M(x) = [[2x-1, 4x],[0, 4x]]** (M0 = partie constante, M1 = partie linéaire).
3. `target = {0, L}` (l. 28) → le produit P = M(1)·M(2)···M(L) (sémantique de l'intervalle [a,b] = produit M(a+1)···M(b), hypellfrob.h l. 38).
4. L=0 → identité (l. 31) ; sinon appel kernel ou wrapper (l. 32-37).
5. Garde triangulaire (l. 39-40) : `P[1][0]` doit être nul et `P[1][1]` non nul, sinon throw.
6. Extraction : `a = P[0][0]/P[1][1]`, `B = P[0][1]/P[1][1]` (l. 41-42).
7. **Formule U générique : `U = 4B - 2L(2L+5)·a`** (l. 43-44) — voir §6 pour la spécialisation quarter-point.
8. Timing 3 phases via `std::chrono::steady_clock` : setup / kernel / finish (l. 16, 22-50), retournées avec A=P[0][0], C=P[0][1], D=P[1][1] (l. 49-50).

`main()` (l. 52-87) : `SetNumThreads(1)` (l. 53) ; `--version` émet `{ntl, compiler, ntl_threads}` (l. 54-57) ; boucle stdin ligne-par-ligne « p L reps » avec validation complète (l. 60-67) ; exécution de `reps` répétitions (l. 68-69) ; émission JSON avec labels de backend `zz_p_auto`/`ZZ_p_auto` selon `p.SinglePrecision()` ou `ZZ_p_forced` (l. 71-76) ; **contrôle de cohérence inter-répétitions** : tout écart sur a/B/U → throw « repeat mismatch » (l. 80) ; exceptions → stderr + exit 1 (l. 85).

**Sémantique vérifiée littéralement** (lecture de la matrice, démonstration courte) : P étant produit de matrices triangulaires supérieures, P[0][0] = ∏_{k=1}^{L}(2k-1), P[1][1] = ∏ 4k, P[1][0] = 0, et P[0][1]/P[1][1] = Σ_{i=0}^{L-1} ∏_{k=1}^{i}(2k-1)/(4k). Donc **a = a_L = C(2L,L)·8^{-L}** (car C(2i,i) = ∏ 2(2k-1)) et **B = Σ_{i<L} a_i** — exactement les définitions du README l. 14-16. L'adaptateur ne fait RIEN d'autre que ce produit.

---

## 4. Confrontation à `point_count.py`

**Disjonction fonctionnelle d'abord :** `point_count.py` (231 l., SPDX GPL-2.0-or-later l. 1, stdlib pure l. 9-10) calcule la **trace** τ = p+1-#E(𝔽_p) de E: y²=x³+2x par deux voies indépendantes — Schoof déterministe (`schoof_trace` l. 212-226, résidus par équation caractéristique de Frobenius dans des quotients polynomialux `schoof_mod_l` l. 159-209, CRT jusqu'à dépasser la largeur de Hasse l. 218-222) et BSGS certifié (`bsgs_trace` l. 66-86, intersection de tous les annihilateurs d'intervalle de Hasse sur la courbe et sa twist l. 77-85, fail-closed l. 86). Le C++ Harvey calcule le **préfixe produit de matrices** (B, a, U) sans jamais toucher à la trace. **Aucune recouvrement fonctionnel direct** — les deux mondes ne se rencontrent que dans la validation croisée du pilot (§5).

**Équivalents structurels communs** (même idée, deux incarnations) :

| Concept | Python `point_count.py` | C++ |
|---|---|---|
| Arithmétique polynomiale modulaire | `Polys.divmod/rem/pow/inverse` l. 93-136 | `rem`/`%`/`mul` NTL (`ZZ_pXModulus` précalculés, Evaluator l. 544) |
| XGCD / inversibilité | `Polys.inverse` l. 130-136, lève `Split(factor)` si pgcd non trivial l. 134 | `padic_xgcd` l. 173-216 (Newton quadratique) |
| Irréversibilité non-factorielle | exception `Split` l. 89-90 → scission D5 `recurse` l. 199-206 | **rien** : precondition « 2..1+floor(sqrt(d)) inversibles » (hypellfrob.h l. 52-54), garantie en amont par les gardes d'entrée de l'adaptateur (p≥7, L≤(p-1)/2 ⇒ 1+sqrt(L)<p) |
| Somme de caractères (témoin) | `direct_trace` l. 229-230 | doctest Sage `sum(legendre_symbol(f(i), p))` hypellfrob.pyx l. 191-192 |
| Déterminisme | fail-closed par exceptions partout l. 84/86/198/208 | fail-closed par throw/assert/exit≠0 (§8) |

**Ce que le C++ ajoute que le Python n'a pas :** middle product FFT (l. 155-184), shift d'évaluation dyadique (l. 203-329), arbre de produits + évaluation/interpolation multipoint (l. 467-714), stratégies d'intervalles courts/longs (l. 762-1279) — toute la machinerie BGS en Õ(√p). `point_count.py` est **volontairement élémentaire** (l. 6-7 : « Polynomial arithmetic is deliberately elementary, not an optimized Schoof ») : c'est un compteur de référence indépendant, pas un compétiteur de vitesse. La comparaison de performance Harvey C++ vs Miller **Python** (pas vs point_count) est la seule mesurée (pilot, README l. 29-31).

**Articulation réelle des trois voies** (README l. 22-31) : `point_count.py` (Schoof ou BSGS) fournit la trace τ à l'évaluateur Miller Python (`elliptic_prefix.quarter`, P1 #19488) ; Harvey C++ calcule B, a, U directement ; le pilot vérifie l'accord des deux (328 cross-checks quarter, VALIDATION l. 9).

---

## 5. Bridges Python↔C++ (subprocess, JSON lines, CSV)

**Bridge principal — `pilot.py::HarveyWorker`** (processus persistant) :
- `subprocess.Popen([exe], stdin=PIPE, stdout=PIPE, stderr=PIPE, text=True, bufsize=1, env=env_for_kernel())` — l. 78-79. Ligne-buffered, environnement déterministe (OMP/OpenBLAS=1, documenté P1 pilot).
- Protocole requête : une ligne `"{p} {L} {reps}\n"` sur stdin + flush (l. 81).
- Protocole réponse : une ligne JSON sur stdout (`readline` l. 82) ; toute ligne vide → le stderr est lu et remonté en `RuntimeError('Harvey child failed: ...')` (l. 83-84).
- Fin de vie : `stdin.close()` puis `poll`/`kill` (l. 87 et suite).
- L'adaptateur tient sa moitié du contrat : boucle `getline` (l. 61), réponse en **une** ligne JSON avec `std::endl` = flush (l. 84), erreurs sur stderr + exit 1 (l. 85).

**Bridge synchrone — `pilot.py::call_kernel`** (l. 69-71) : `subprocess.run(input=text, capture_output=True)` puis `stdout.splitlines()` → `json.loads` par ligne. Utilisé pour les requêtes one-shot.

**Schéma de message** (adapter l. 72-84) :
```json
{"p":…,"L":…,"B":…,"a":…,"U":…,"A":…,"C":…,"D":…,
 "backend":"zz_p_auto|ZZ_p_auto|ZZ_p_forced",
 "samples":[{"setup_ms":…,"kernel_ms":…,"finish_ms":…,"total_ms":…}, …]}
```
Entiers ZZ sérialisés en décimal ASCII (`std::cout << r.B`, l. 72-74) — précision complète, avertissement Excel 15 digits côté README l. 95. Timings en double précision 12 digits (l. 71).

**Versionnage du pont** : `--version` → `{"ntl":NTL_VERSION,"compiler":__VERSION__,"ntl_threads":1}` (l. 54-57) ; consommé par pilot.py l. 204 (`subprocess.check_output`) et benchmark_engine.py l. 209 (avec `timeout=10`), enregistré dans `benchmark.json` — le pendant C++ des gardes `adapter_sha256`/`miller_source_sha256` Python (P1 pilot §4).

**CSV** : pilot.py écrit `paper_table`/`summary`/`samples` avec colonnes `harvey_setup_median_ms`, `harvey_kernel_median_ms`, `harvey_finish_median_ms`, `harvey_over_miller_time_ratio` (l. 230-246) ; `benchmark_engine.py` l. 201 inclut `harvey_adapter.cpp` dans les `source_sha256`. Formats documentés README l. 80-95 (UTF-8 + BOM pour Excel).

**Le pont Sage (hors benchmark)** : `hypellfrob.pyx` l. 158-252 — la fonction `hypellfrob(p, N, Q)` convertit des matrices Sage→NTL via `set_ntl_matrix_modn_dense` (l. 132-133) et appelle `hypellfrob::matrix`. Ce pont-là n'est PAS utilisé par le dépôt (l'adaptateur appelle le wrapper d'intervalles, pas `matrix`) — il documente l'usage amont Sage des sources vendored.

---

## 6. Confrontation au manuscrit l. 420-450 (Section 5, pseudocode Miller)

**Constat central :** le pseudocode de la chaîne de Miller différenciée (manuscrit l. 420-437) — « T := R; alpha := 0; j := 0 … op := operations[j] … attempt (Tnew, rho) := ADD(T, Q) … split saved R, T, alpha by s → ±a/b … anew := 2*alpha + rho if doubling, otherwise alpha + rho » — n'a **aucune contrepartie dans le code C++**. Le C++ ne contient ni point elliptique, ni pente (tangente (3x₁²+A)/(2y₁), l. 441), ni accumulateur alpha, ni scission D5 (l. 431-434, « dynamic evaluation, or the D5 principle (Della Dora et al., 1985) » l. 417-418). Cette chaîne vit intégralement dans `elliptic_prefix.py` (Python, déjà confronté en P1 #19488 : `Elliptic`, `SplitRoot`, accumulateur). Le C++ est **l'autre voie** : le comparateur « retained Harvey Bostan–Gaudry–Schost recurrence » (README l. 3, l. 29).

**La confrontation l. 420-450 est donc médiée par la récurrence rationnelle.** Le manuscrit définit (l. 488, éq. 32) la suite c_{i+1} = f(c_i, i) rationnelle dont le quarter-point extrait a_n, B_n. L'adaptateur encode cette récurrence en forme matricielle : M(x) = [[2x-1, 4x],[0, 4x]] (adapter l. 26-27), le produit M(1)···M(L) portant le préfixe (§3.3, sémantique vérifiée : a = C(2L,L)8^{-L}, B = Σ a_i). Les formules citées par le cahier des charges :

- **Éq. (28)** (l. 390) — mise à jour de l'accumulateur « 2α+ρ / α+ρ » selon doublement/addition : implémentée en Python Miller ; le C++ n'a pas d'accumulateur, il a un produit de matrices.
- **Éq. (29)** (l. 398) — reconstruction U à partir des constantes des deux chaînes : la contrepartie C++ est la formule générique **U = 4B − 2L(2L+5)·a** (adapter l. 44). **Vérification littérale de la spécialisation :** au quarter-point L = (p−1)/4, on a 2L = (p−1)/2 ≡ −1/2 (mod p) et 2L+5 ≡ 9/2, donc −2L(2L+5) ≡ −(−1/2)(9/2) = **9/4**, et U = 4B + (9/4)a — exactement la formule U_p(n) du README l. 19. La formule C++ est la version générique en L, la formule du manuscrit/README sa spécialisation quarter-point.
- **Éq. (30)** (l. 405) — reconstruction avant/après split dans l'algèbre étale : purement Python (`Quadratic`, P1 #19488), rien en C++.
- **Corollary 4** (l. 457-475) — évaluation déterministe polynomial-time via Schoof : le manuscrit renvoie à Schoof 1985 ; son incarnation du dépôt est `point_count.py` (Python, §4), pas le C++. La remarque l. 479-481 (« The appendix uses specialized Cornacchia/Gauss preparation ») situe l'appendice du manuscrit sur la préparation Cornacchia/Gauss — Harvey C++ est le comparateur indépendant, non décrit par le manuscrit (il relève de [Harv2007]/[BGS2007], littérature externe).

**Équivalence numérique des deux voies** (ce que le dépôt mesure au lieu d'une preuve) : 10 809 stopping-point queries sur 92 premiers + 328 cross-checks quarter Harvey↔Python + 26 forced-arbitrary-precision (VALIDATION l. 9). Aucun désaccord enregistré. Le pont formel entre les deux voies (preuve d'équivalence) n'existe nulle part — c'est un candidat P2.c (§10).

---

## 7. Dépendance NTL (versions, ZZ_p, ZZ_pX, classes)

**Classes/fonctions NTL consommées** (inventaire exhaustif) :
- Types : `ZZ`, `ZZ_p`, `ZZ_pX`, `ZZ_pXModulus`, `FFTRep`, `vec_ZZ_p`, `mat_ZZ_p`, `mat_ZZ`, `ZZX`, et la colonne simple précision `zz_p`, `zz_pX`, `zz_pXModulus`, `fftRep`, `vec_zz_p`, `mat_zz_p` ; contextes `ZZ_pContext`, `zz_pContext`.
- Opérations : `ToFFTRep`/`TofftRep`, `FromFFTRep`/`FromfftRep` (l. 100-127), `XGCD` (hypellfrob.cpp l. 189), `InvMod` (l. 669), `ProbPrime(p,30)` (adapter l. 67), `power`, `SqrRoot` (l. 296, 792), `NumBits` (l. 1018), `ident` (adapter l. 31), `IsZero`/`IsOne`, `LeadCoeff`, `coeff`/`SetCoeff`, `deg`, `diff`, `LeftShift`, `rep`, `conv`/`to_*`, `SinglePrecision` (l. 75 adapter, l. 92 hypellfrob.cpp), `SetNumThreads` (l. 53), `NTL_VERSION` (l. 55).

**Gestion des contextes** (le point délicat NTL) : le modulus `ZZ_p` est un **état global** (par thread en NTL threadée). L'adaptateur initialise une fois (l. 23) ; `interval_products_wrapper` sauvegarde/restaure le contexte `zz_p` autour de la bascule simple précision (l. 104-106, 124) ; `matrix()` (inutilisée ici) fait de même avec trois contextes p^N/p^{N+1}/caller (l. 288-299, 708). Hygiène conforme aux attentes NTL.

**Version** : non épinglée — `-lntl` système (build.sh l. 8). La version est **enregistrée** (NTL_VERSION via `--version`, pilot l. 204, build_metadata.json) mais pas **fixée**. L'inclusion de `NTL/BasicThreadPool.h` + `SetNumThreads` (adapter l. 5-6, 53) requiert NTL ≥ 11.x. Installation documentée : MSYS2 `mingw-w64-ucrt-x86_64-ntl` (README l. 38) ou Ubuntu `libntl-dev` (l. 59). GMP liée en dépendance (`-lgmp`).

**Routage de précision** : `SinglePrecision()` décide zz_p (label `zz_p_auto`) vs ZZ_p (`ZZ_p_auto`) ; `--force-big` court-circuite le wrapper et force la colonne ZZ_p (adapter l. 32-37) — c'est le témoin du routage auto (26 cross-checks forced, VALIDATION l. 9).

**Méfiances documentées envers NTL** (à retenir pour P2) : `padic_xgcd` existe parce que « NTL's xgcd routine is only guaranteed to work if the coefficient ring is a field » (hypellfrob.cpp l. 167-170) ; `padic_invert_matrix` parce que « It's not clear to me whether NTL's matrix inversion is guaranteed to work over a non-field » (l. 228-231). Deux réimplémentations manuelles de primitives NTL pour les anneaux Z/p^N.

**Sources de non-reproductibilité identifiées** :
1. **Version NTL/GMP variable** (enregistrée, non épinglée) : les **résultats arithmétiques sont exacts mod p** (aucun flottant dans le kernel) donc déterministes ; seuls les **timings** et l'empreinte binaire varient.
2. **Threading** : `SetNumThreads(1)` explicite (adapter l. 53) + `ntl_threads:1` émis dans `--version` ; build `-pthread` mais aucun thread explicite dans le code — si la NTL liée est compilée `NTL_THREADS`, le comportement reste single-thread par le SetNumThreads. Le pilot double la garde côté Python (OMP_NUM_THREADS=1, P1 pilot).
3. **Timings machine-dépendants** : steady_clock, médianes par batch — README l. 115 documente language/library/warm state/shared-host variability ; aucun speedup claim population-level (P1 pilot).
4. **`ProbPrime(p, 30)`** probabiliste en théorie — mais le caractère premier est re-validé côté Python avant l'appel (le harness ne soumet que des premiers vérifiés), le verdict n'est jamais la seule ligne de défense.
5. **Allocations brutes du ProductTree** (`new`/`delete` l. 511-523, pas de RAII) : fuite possible sur exception en cours de construction — sans effet sur les résultats, à noter pour une éventuelle relecture qualité du vendored (interdit à modifier ici).
6. **Vendored vs système** : les 4 sources upstream sont SHA256-pinnées (SOURCE_PROVENANCE.json) ; NTL/GMP restent système — un build Docker/MSYS2 reproduit les sources mais lie une NTL locale différente.

---

## 8. Garde-fous identifiés (fails closed, asserts, exceptions)

**Adaptateur (l'entrée du système) :**
- `SetNumThreads(1)` l. 53 — déterminisme des timings.
- Validation totale des entrées l. 64-67 : parse strict, `p≥7`, `0≤L≤(p−1)/2` (cette borne **garantit** la precondition d'inversibilité de la bibliothèque : 1+⌊√L⌋ < p), `1≤reps≤10000`, `ProbPrime(p,30)`.
- Garde triangulaire l. 39-40 : produit invalide (`P[1][0]≠0`) ou dénominateur nul (`P[1][1]=0`) → `runtime_error`.
- **Détection de non-déterminisme interne** : les `reps` exécutions doivent rendre a/B/U identiques, sinon throw « repeat mismatch » l. 80 — l'auto-vérification de reproductibilité est dans le binaire.
- Usage invalide → exit 2 (l. 59) ; toute exception → stderr + exit 1 (l. 85). Aucun chemin ne retourne de résultat fabriqué.

**Bibliothèque upstream :**
- `matrix()` : refus par `return 0` sur N<1, p<3, deg(Q)<3, degré pair, non-monic, p trop petit (l. 277-286) ; échec xgcd (courbe singulière) → `return 0` avec restauration du contexte caller (l. 317-323).
- Asserts d'invariants mathématiques des réductions : divisibilité par p du numérateur et du dénominateur aux étapes critiques (l. 575, 586, 666, 677).
- Asserts structurels : dimensions carrées (recurrences l. 1004-1007), parité de target (l. 1001), égalité de tailles index/matrices aux 4 jointures du pipeline (l. 1136, 1205, 1249, 1267), longueurs Evaluator (l. 549-553), bornes ProductTree (l. 499-501).
- Sentinelles explicites pour les fusions de listes (l. 1147-1148, 1215-1218, 1258-1259) puis retirées (« remove sentinels for my sanity » l. 1196, 1243).

**Fail-closed global :** toute anomalie → exception (adapter), assert (library, mode debug) ou code de retour non nul. Le pilot ferme la boucle : échec enfant = `RuntimeError` (l. 84), jamais de ligne JSON partielle acceptée (`json.loads` lèverait).

---

## 9. Bilan P1 pseudocode C++

**Composants vérifiés littéralement (lecture ligne-par-ligne + sémantique retrouvée) — 16 :**
1. En-têtes/licences/includes (§1).
2. Provenance Sage 10.8 / SHA256 / GPL (§1.1).
3. Pureté des fichiers upstream, I/O cantonnée à l'adaptateur (§1.3).
4. APIs publiques + graphe d'appels complet depuis `calculate()` (§2).
5. Adaptateurs de templates ZZ_p↔zz_p (§3.1a).
6. `middle_product` + crédit HQZ (§3.1b).
7. `DyadicShifter` (twists/kernel/accum, §3.1c).
8. `dyadic_evaluation` (Theorem 8 BGS, cas de base + récursion double-shift, §3.1d).
9. `ProductTree`/`Evaluator`/`Interpolator` (Corollary 10 BGS, §3.1e-g).
10. `ntl_short_interval_products` (5 étapes + heuristique L, §3.1h).
11. `ntl_interval_products` (Steps 0-3 + sentinelles, §3.1i).
12. Routeur de précision `interval_products_wrapper` + zz_pContext save/restore (§3.2a).
13. `padic_xgcd`/`padic_invert_matrix` (Newton quadratique, méfiance NTL documentée, §3.2c-d).
14. `calculate()` : matrice M(x), garde triangulaire, extraction a/B, formule U — **sémantique C(2L,L)8^{-L} / Σ a_i démontrée** (§3.3).
15. `main()` : CLI, validation, JSON, contrôle inter-répétitions (§3.3).
16. Spécialisation quarter-point −2L(2L+5) ≡ 9/4 (mod p) vérifiée (§6).

**Partiels — 3 :**
17. `matrix()` (437 l.) : lu intégralement et documenté phase par phase (§3.2e), mais **jamais exécuté** par le benchmark — la conformité de ses 7 phases au papier Harvey 2007 n'est pas confrontée à une exécution (non-appelé, cf. §2).
18. `hypellfrob.pyx` : lu pour le bridge API ; ses doctests Sage ne sont pas rejoués ici.
19. Détail des timings des 3 phases C++ : sémantique des bornes setup/kernel/finish vérifiée dans le code, mais les mesures de `example_results/` n'ont pas été rejouées (données historiques).

**Reportés à P2+ — 3 :**
20. Preuve formelle de la sémantique de l'adaptateur (matrice produit ↔ coefficients binomiaux centraux) — candidate P2.a.
21. Preuve formelle du middle product / DyadicShifter (correctness du shift Lagrange-twisted) — candidate P2.b.
22. Pont formel chaîne Miller (manuscrit l. 420-447) ↔ produits d'intervalles BGS au quarter-point — l'équivalence n'est attestée qu'empiriquement (10 809+328 requêtes) ; candidate P2.c.

**Risques résiduels :** aucun sur la sémantique du périmètre benchmark (adapter + wrappers + recurrences). Deux notes sans impact résultat : allocations brutes ProductTree (§7.5), `matrix()` compilée mais inerte dans ce binaire (§2).

---

## 10. P2+ — 5 phases

**P2.a — Formalisation Lean Mathlib de la sémantique adaptateur (court, ~2-4 h).** Théorème auto-contenu : pour M(x) = [[2x−1, 4x],[0, 4x]] et P = ∏_{k=1}^{L} M(k) sur 𝔽_p (p≥7, 2L≤p−1), alors P est triangulaire supérieure, a = P₀₀/P₁₁ = ∏(2k−1)/(4k) = C(2L,L)·8^{−L}, B = P₀₁/P₁₁ = Σ_{i<L} a_i, et pour 2L ≡ −1/2 la formule U = 4B − 2L(2L+5)a coïncide avec 4B + (9/4)a. S'appuie sur `Mathlib.Combinatorics.Choose.Central` ou la définition directe. Premier contact Lean avec le dépôt.

**P2.b — Middle product / DyadicShifter en Lean (moyen, multi-cycle).** Correctness du shift d'évaluation (interpolation décalée par twists factoriels) — dépend de l'API polynômes évaluation/interpolation de Mathlib (`Polynomial.eval`, produits). À découper en : identité du twist d'entrée, kernel = inverse des produits fenêtrés, recomposition.

**P2.c — Pont Miller ↔ BGS (le théorème du manuscrit, long).** Formaliser que la chaîne de Miller différenciée du manuscrit l. 420-447 et le produit d'intervalles rendent le même (a, B, U) au quarter-point. C'est la contrepartie formelle des 10 809 vérifications empiriques. Prérequis P2.a ; l'objet mathématique est la récurrence (32) l. 488.

**P3 — Intégration dépôt CoursIA.** Ce mémo → `docs/research/cartier-miller-p1-cpp.md` (PR dédiée, tag `Grain: DEEP/research-code`), aux côtés des P0/P1 déjà livrés (#19487, #19488, #19493).

**P4 — Reproduction exécution.** Build NTL épinglé (MSYS2 UCRT64), re-run `test_validation` + pilot 7 premiers, comparaison byte des JSON contre `example_results/paper_seven`. Valider que le routage auto zz_p s'active sur les 7 premiers (tous < 2^50) et mesurer le delta `--force-big`.

**P5 — (optionnel, hors mandat manuscrit) Notebook pédagogique** didactique sur les deux voies (Miller vs BGS) — uniquement si un intérêt d'enseignement se dégage ; aucune obligation.
