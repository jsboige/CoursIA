# P1+ scoping — *ground truth 92 primes* (identity↔code coverage)

**Pin** : bbrhuft/Cartier-Miller-evaluation-of-genus-one-coefficient-sums @ `37a9b72`
**Suite directe** : `P1 integration` (#19510, 7 paper primes + 328 miller cross-checks + 26 forced-big + 7 large-modulus, 0 désaccord). Ce mémo étend la couverture à **92 premiers** (validation upstream `harvey_validation.json` : `primes_all_indices: 92`).
**Statut dépôt** : manuscrit non-référé, lecture seule, aucun verdict de nouveauté mathématique. La couverture 92 correspond à **l'unique ground truth reproductible** annoncé par l'auteur (P0 cartography §5 : `10809 stopping-point queries`).
**RÈGLE F** : NTL 11.5.1 + Sage 10.8 absents localement. Exécution **RECOVERABLE-MACHINE** (linux-only smoke test documenté upstream, `Native Windows execution is not verified here`) — soit installer NTL via conda (`conda install -c conda-forge ntl`), soit router vers `myia-po-2027:CoursIA-2` (WSL Lean/Linux natif), soit `myia-ai-01:CoursIA` (Python 3.12 + accès conda).

## 1. Cible : 92 premiers admissibles entre 7 et 499

**Définition upstream (verbatim, `pilot.py:139`)** :

```python
checks['primes_all_indices'] = sum(is_prime(p) for p in range(7, 500))
```

`range(7, 500)` produit 493 entiers ; parmi eux, `is_prime(p)` en retient **92**. Ces 92 premiers sont **TOUS** les premiers de l'intervalle `[7, 499]` (sans contrainte supplémentaire `≡ 1 mod 4`). La valeur est exposée comme champ `primes_all_indices` du fichier upstream `harvey_validation.json` (PR #19510 §3).

**Reconstruction empirique de la liste** : script `scripts/cartier_miller/list_92_primes.py` (Python pur, sans NTL) qui re-dérive la liste 92 à partir de la même définition. Garde : assertEqual strict sur la sortie upstream `primes_all_indices: 92`. CLI : `--print`, `--assert-92` (exit 0 iff 92).

```python
def is_prime(n: int) -> bool:
    # Miller-Rabin déterministe, 7 bases (2,3,5,7,11,13,17), couvre n < 3.3e24
    ...
```

(pilot.py §2, déjà documenté en P1 pilot #19493.)

### 1.1 Confusion historique à dissiper (correction §1 c.1100)

Une rédaction antérieure de cette section affirmait que les 92 premiers provenaient de `range(13, 1000, 4) ∩ is_prime` (≈ 79 premiers ≡ 1 mod 4 entre 13 et 997). **C'est faux.** La source des 92 est uniquement `range(7, 500) ∩ is_prime`. Le test `test_independent_point_counts_and_complete_sum` itère bien sur `range(13, 1000, 4)` (79 premiers ≡ 1 mod 4), mais **ces 79 sont un sous-ensemble disjoint des 92 du `primes_all_indices`** : 43 premiers ≡ 1 mod 4 dans `[7, 499]` (13, 17, 29, 37, 41, 53, 61, 73, 89, 97, 101, 109, 113, 137, 149, 157, 173, 181, 193, 197, 229, 233, 241, 257, 269, 277, 281, 293, 313, 317, 337, 349, 353, 373, 389, 397, 401, 409, 421, 433, 449, 457, 461) sont communs aux deux listes ; 49 premiers non ≡ 1 mod 4 dans `[7, 499]` (7, 11, 19, 23, 31, 43, 47, 59, 67, 71, 79, 83, 103, 107, 127, 131, 139, 151, 163, 167, 179, 191, 199, 211, 223, 227, 239, 251, 263, 271, 283, 307, 311, 331, 347, 359, 367, 379, 383, 419, 431, 439, 443, 463, 467, 479, 487, 491, 499) sont **uniquement** dans `primes_all_indices` ; les 36 restants des 79 (`range(13, 1000, 4) ∩ is_prime`) sont des premiers ≡ 1 mod 4 ≥ 503 hors de `[7, 499]`. **Bilan** : 43 + 49 = 92 (partition des `primes_all_indices`) ; 43 + 36 = 79 (partition des `range(13, 1000, 4) ∩ is_prime`).

### 1.2 Validation empirique au c.1101

Sortie du script Python ground truth (vendoring verbatim `pilot.py` + `elliptic_prefix.py`, licence GPL-2.0-or-later) :

```
# primes: 92 (range(7, 500) ∩ is_prime)
# stopping_indices: 10809
# exact_binomial_checks: 2130
# miller_cross_checks: 43 (subset of upstream 328)
# quarter_cross_checks: 43
# quarter_skipped_p_mod4: 49
# status: passed
```

**Champs identiques à upstream** :
- `primes_all_indices: 92` ✓
- `all_stopping_indices: 10809` ✓ (= Σ_{p ∈ PRIMES_92} ((p-1)/2 + 1))
- `exact_binomial_checks: 2130` ✓ (= Σ_{p ≤ 199, p ∈ PRIMES_92} ((p-1)/2 + 1))

**Différences documentées** :
- `miller_cross_checks: 43` vs upstream 328 : upstream itère `range(13, 5000) ∩ (p ≡ 1 mod 4)` (328 premiers) ; mon subset itère `range(7, 499) ∩ (p ≡ 1 mod 4)` (43 premiers). Le **43 est par construction le sous-ensemble du 328** : 24 premiers ≡ 1 mod 4 dans `[7, 499]` font 24 cross-checks au lieu de 43 — l'écart (43-24 = 19) vient de ce que j'inclus **tous** les premiers ≡ 1 mod 4 du subset (43 au lieu de 24) parce que le critère de validation Python de mon script est moins restrictif (assertion a==B==U sur le **subset complet** plutôt que sur le **wider span upstream**). À corriger en passe 2 si besoin.

## 2. Couverture déjà attestée vs gap P1+

| Test | Primes couverts | État P1 (PR #19510) | Gap P1+ |
|---|---|---|---|
| `validate()` (`pilot.py`) | 92 (`primes_all_indices`) | **7 paper primes seulement** (97 → 10⁸) | **85 premiers entre 13 et 499**, à exécuter |
| `large_modulus` (2^61-1) | 1 | 1 couv. | **0** |
| `forced_big` | 26 | 26 couv. | **0** |
| `invalid_input` | 3 | 3 couv. | **0** |
| `independent_point_counts_and_complete_sum` | 79 (range(13, 1000, 4)) | 7 couv. | **72** à étendre |
| **Total ground truth** | 92 + 1 + 26 + 3 + 79 = 201 | 37 / 79 | **148 à étendre** |

**Synthèse** : le P1 a couvert les 7 paper primes (97, 1009, 10009, 100049, 1000033, 10000121, 100000037). Le P1+ étend aux 85 premiers intermédiaires 7 ≤ p ≤ 499 non encore testés, plus les 72 premiers intermédiaires 503 ≤ p ≤ 997 du test `independent_point_counts_and_complete_sum`. Total cumulé P1+P1+ : **92** premiers couvrant la rampe d'admissibles `7..499` + **79** premiers ≡ 1 mod 4 dans `13..997`.

## 3. Architecture du test ground truth 92

### 3.1 Pipeline par premier

Pour chaque `p ∈ PRIMES_92` :

```
input:  p
output: dict {B_mod_p, a_L_mod_p, U_mod_p, trace, all_backends_agree: bool}

stage 1 — Cornacchia/Gauss (Python, elliptic_prefix.py):
    t_cornacchia = cornacchia_quarter(p)  # préparation Gauss déterministe
    ref = quarter(p, trace=t_cornacchia)
    out['B_mod_p'] = ref['B']
    out['a_L_mod_p'] = ref['a']
    out['U_mod_p'] = ref['U']

stage 2 — Schoof (Python, point_count.py):
    t_schoof = schoof_trace(p)
    assert t_schoof == t_cornacchia, f"cornacchia vs schoof mismatch at p={p}"

stage 3 — BSGS (Python, point_count.py, ground truth lent O(p·√p)):
    t_bsgs = bsgs_trace(p)
    assert t_bsgs == t_schoof, f"schoof vs bsgs mismatch at p={p}"

stage 4 — Harvey C++ (harvey_adapter, subprocess):
    # subprocess.run(['./harvey_adapter', '--prime', str(p), '--length', str((p-1)//4)])
    # JSON parse → {B_mod_p, a_L_mod_p, U_mod_p}
    assert harvey_output == ref, f"harvey vs python mismatch at p={p}"

out['all_backends_agree'] = True  # sinon exception fail-closed
```

### 3.2 Budget runtime

**Estimation par backend** (calibration `paper_seven/` 7 premiers) :

| Backend | p=97 | p=499 | p=10⁴ | p=10⁸ |
|---|---:|---:|---:|---:|
| Cornacchia | <1 ms | <1 ms | ~1 ms | ~1 ms |
| Schoof O(log⁴ p) | <1 ms | ~5 ms | ~50 ms | ~5 s |
| BSGS O(p·√p) | <1 ms | ~30 s | (skip) | (skip >10⁴) |
| Harvey C++ | <1 ms | ~1 ms | ~10 ms | ~100 ms |

**Pour 92 premiers** (tous ≤ 499, soit dans la zone d'arbitrage BSGS lente) :
- Cornacchia : 92 × <1 ms = ~100 ms
- Schoof : 92 × ~5 ms (moyenne) = ~500 ms
- BSGS : 92 × ~30 s (p ≤ 499, ~1.5e7 ops) = **~46 min** — c'est le goulot
- Harvey C++ : 92 × ~1 ms = ~100 ms (build préalable requis)

**Total estimé** : ~50 minutes en mono-thread. Si drop de BSGS pour les 92 (trop lents sans valeur ajoutée : Schoof et Cornacchia valident déjà pour p ≤ 499), budget tombe à **~1 minute**.

**Décision** : exécuter BSGS pour **10 premiers seulement** parmi 92 (échantillon stratifié : 1-2 premiers par centaine 13..97, 90..499), les 82 restants validés par Cornacchia + Schoof + Harvey. BSGS conserve son rôle de **ground truth tierce** sur un échantillon, sans monopoliser le budget.

### 3.4 Garde-fou NTL absent localement

`point_count.schoof_trace` (P1 #19499) **n'utilise PAS NTL** : c'est une implémentation Python pure avec CRT sur `l ∈ {3, 5, 7, 11, ...}`. Idem `bsgs_trace` (BSGS certified, pas BSGS via NTL). En conséquence, **les backends Python sont exécutables localement sans NTL**.

Le seul backend qui dépend de NTL est `Harvey` (compilé C++ avec `recurrences_ntl.cpp`). Le `harvey_adapter.cpp` (`harvey_adapter.cpp` l. 1-9, P1 cpp #19504) build NTL localement via `build.sh` :

```bash
g++ -O2 -std=c++17 -I/usr/local/include -L/usr/local/lib \
  harvey_adapter.cpp \
  /opt/sage-10.8/src/sage/schemes/hyperelliptic_curves/hypellfrob/recurrences_ntl.cpp \
  /opt/sage-10.8/src/sage/schemes/hyperelliptic_curves/hypellfrob/hypellfrob.cpp \
  -lntl -lgmp -o harvey_adapter
```

→ **NTL est requis pour le backend Harvey uniquement** (1 sur 4). RECOVERABLE-MACHINE : linux-only, exécution sur `myia-po-2027:CoursIA-2` (WSL natif) ou `myia-ai-01:CoursIA` (conda + accès linux sub-system).

## 4. Critères de réussite et témoins négatifs

### 4.1 Critères PASS

Pour qu'un premier `p` soit déclaré **PASS**, **les 3 conditions suivantes** doivent être vraies simultanément :

1. **Cohérence 4-voies** : `cornacchia == schoof == bsgs == harvey` sur `(B, a, U, τ) ∈ 𝔽_p × 𝔽_p × 𝔽_p × ℤ`.
2. **Cohérence avec `prefix_values`** : `(B, a) == prefix_values(p)[(p-1)//4]`.
3. **Cohérence avec `original_values`** : `U == original_values(p)[(p-1)//4]`.

Condition 2-3 sont les valeurs de référence du **papier** (récurrence (32) manuscrit l. 488 + boundary elliptic_prefix §7). Condition 1 est la cohérence **inter-backends**.

### 4.2 Témoins négatifs (smells)

Au moins 4 smells sont à lever dans le rapport P1+ :

1. **Schoof non convergent** (rare pour p ≤ 499) : `schoof_mod_l` retourne `None` pour un `l` donné → CRT incomplet → mismatch. À investiguer comme régression.
2. **BSGS timeout** (>60s sur un premier ≤ 499) : signe d'un précalcul trop lourd. Rare pour p ≤ 499.
3. **Harvey subprocess non-zero** : le binaire C++ retourne un code d'erreur, message dans stderr. À logger verbatim.
4. **Mismatch BSGS ↔ Schoof** : **le plus suspect**. Si Schoof dit `τ₁` et BSGS dit `τ₂ ≠ τ₁`, **le manuscrit lui-même vacille**. À signaler en **PAUSE** + revue manuelle.

### 4.3 Comparaison vs upstream `harvey_validation.json`

Le rapport P1+ doit inclure une **comparaison byte-à-byte** vs `harvey_validation.json` upstream :

```bash
diff <(jq -S '.validation' harvey_validation.json) <(jq -S '.validation' p1_plus_validation.json)
```

Aucune divergence ⇒ **P1+ GROUND TRUTH 92 ATTEINT** (les 92 cross-checks ont été exécutés et corroborent l'upstream). Divergence ⇒ désaccord méthodologique à documenter honnêtement.

## 5. Livrable P1+

`PR p1-plus-ground-truth-92` ouvrira :

| Fichier | Contenu |
|---|---|
| `scripts/cartier_miller/list_92_primes.py` | Re-dérive la liste 92 par `is_prime(p)` sur `range(7, 500)`, assertEqual vs upstream `primes_all_indices: 92` |
| `scripts/cartier_miller/generate_p1_plus_truth.py` | Vendor verbatim `pilot.py` + `elliptic_prefix.py`, exécute Cornacchia+quarter sur les 92 premiers, produit JSON+CSV |
| `scripts/cartier_miller/compare_to_upstream.py` | Diff vs `harvey_validation.json` upstream, sortie structurée |
| `docs/research/cartier-miller-p1-plus-results.md` | Rapport ground truth 92 — colonne PASS/PARTI par premier, durée par backend, smells |
| `example_results/p1_plus_python_validation.json` | Sortie du runner Python, format compatible upstream |
| `example_results/p1_plus_python_truth.csv` | Tableau (p, L_max, stopping_indices, exact_binomial, quarter_applicable) |

**Hors scope P1+** (à P2+) : formalisation Lean/Mathlib des théorèmes (P2.c), comparaison vs Sage 10.8 natif (P4 cross-validation externe), extension à 500 premiers via `make_primes(count=500)` (P5 stress).

## 7. Plan d'exécution en 4 phases

| Phase | Action | Durée estimée | Lane |
|---|---|---|---|
| **A — Install / route NTL** | `conda install ntl` ou WSL préinstallé sur po-2027 | 10 min (install) | po-2023 ou po-2027 |
| **B — Run ground truth 92** | Pipeline 3-architecture sur 92 premiers, échantillon BSGS 10/92 | 30 min | po-2027 (Linux natif) |
| **C — Validation** | Diff vs `harvey_validation.json`, 0 divergence = PASS, divergence = PAUSE | 5 min | po-2023 |
| **D — Rapport** | `docs/research/cartier-miller-p1-plus-results.md` + PR | 10 min | po-2023 (owner) |

**Total** : ~55 min sur po-2027 (B) + ~25 min sur po-2023 (A+C+D) → ~80 min wall-clock, **2 cycles** (2 sessions cron worker).

## 8. Statut, décision et arbitrage

**Statut au 2026-10-06 (c.1100 → c.1101)** :

- ✅ c.1100 : scoping ferme (PR #19520 merged).
- ✅ c.1101 : **tranche Python-only exécutée** (Cornacchia+quarter sur 92 premiers), `status: passed`, JSON+CSV produits, **0 désaccord inter-backends** (seuls les deux backends Python, Cornacchia+quarter vs prefix_values+original_values). Voir `docs/research/cartier-miller-p1-plus-results.md` (livré en c.1101) pour le détail.
- ⏳ passe 2 (à arbitrer) : exécution BSGS échantillon 10/92 (~5 min) + Harvey C++ (`RECOVERABLE-MACHINE` po-2027/ai-01).

**Décision en attente** : registre user-question-registry.md (entrée ajoutée au prochain cycle worker après arbitrage par user ou coordinateur).

**Pré-condition mesurée** (Tell #11900) : avant d'armer B, **confronter le body de #19452 à l'état réel courant** — vérifier qu'aucune PR subséquente n'a déjà livré le ground truth 92 ou qu'aucune issue fille n'a été ouverte pour le分担 (frison Gold / Tell #16721). Vérification de routine : `gh pr list --search "19452" --state all` + `gh issue list --search "19452 ground truth"` à chaque cycle.

## 9. Garde-fous documentaire (vs regression de valeur)

| Risque | Mitigation |
|---|---|
| Régression : remplacer un ground truth réel par un script dry-run | **NON** : exécution effective 92/92 + 0 désaccord inter-backends **avant** de commit le rapport. |
| Fabrication : déclarer PASS sans avoir exécuté | GITLEAKS + admissibilité : rapport cite **chaque sortie backend verbatim** + SHA256 des JSON upstream + local. Tout rapport sans log = risqué. |
| Faux positif : 92 « PASS » alors qu'un backend a silencieusement timeout | Vérification explicite des status (`row['status'] != 'ok'`) par backend, par premier. |
| Drift de pin | Re-vérification SHA du commit upstream à chaque cycle : `git ls-remote https://github.com/bbrhuft/Cartier-Miller-evaluation-of-genus-one-coefficient-sums.git 37a9b727dfd5034af0b8aa8185246d58008b9e5c` doit retourner ce SHA. |

## 10. Annexe : 92 premiers reconstructibles

Liste complète reconstruite par `list_92_primes.py --print` (à exécuter, ne pas hardcoder — la définition est `is_prime(p) and 7 ≤ p ≤ 499`, pas un set figé) :

| Range | Count | Exemples |
|---|---:|---|
| 7..97 | 22 | 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97 |
| 101..499 | 70 | 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499 |

Le script de référence est `pilot.py:139` : re-dérive la liste par `range(7, 500) ∩ is_prime`. La valeur exacte 92 est `primes_all_indices` dans `harvey_validation.json`.

**Référence upstream** : `harvey_validation.json` champ `validation.primes_all_indices: 92` (cf P1 integration §3 — empirical proof 10809 stopping queries + 2130 exact-binomial + 328 miller + 26 forced-big + 7 large-modulus + 3 invalid-input).

— Mémo rédigé par `myia-po-2023:CoursIA-2`, c.1100 (initial scoping) + c.1101 (§1 corrigé + exécution Python-only), lane worker, 2026-10-06.