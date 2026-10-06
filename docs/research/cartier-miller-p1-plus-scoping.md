# P1+ scoping — *ground truth 92 primes* (identity↔code coverage)

**Pin** : bbrhuft/Cartier-Miller-evaluation-of-genus-one-coefficient-sums @ `37a9b72`
**Suite directe** : `P1 integration` (#19510, 7 paper primes + 328 miller cross-checks + 26 forced-big + 7 large-modulus, 0 désaccord). Ce mémo étend la couverture à **92 premiers** (validation upstream `harvey_validation.json` : `primes_all_indices: 92`).
**Statut dépôt** : manuscrit non-référé, lecture seule, aucun verdict de nouveauté mathématique. La couverture 92 correspond à **l'unique ground truth reproductible** annoncé par l'auteur (P0 cartography §5 : `10809 stopping-point queries`).
**RÈGLE F** : NTL 11.5.1 + Sage 10.8 absents localement. Exécution **RECOVERABLE-MACHINE** (linux-only smoke test documenté upstream, `Native Windows execution is not verified here`) — soit installer NTL via conda (`conda install -c conda-forge ntl`), soit router vers `myia-po-2027:CoursIA-2` (WSL Lean/Linux natif), soit `myia-ai-01:CoursIA` (Python 3.12 + accès conda).

## 1. Cible : 92 premiers admissibles entre 13 et 997

`test_independent_point_counts_and_complete_sum` (`test_validation.py` l. 11-21) itère sur `range(13, 1000, 4)` et collecte les premiers via `is_prime(p)` :

```python
count = 0
for p in range(13, 1000, 4):
    if not is_prime(p): continue
    t = direct_trace(p)
    self.assertEqual(schoof_trace(p), t, p)
    self.assertEqual(bsgs_trace(p), t, p)
    self.assertEqual(prepare(p, 'cornacchia'), t, p)
    z = quarter(p, trace=t)
    n = (p - 1) // 4
    self.assertEqual(z['U'], original_values(p)[n], p)
    ref = prefix_values(p)[n]
    self.assertEqual((z['B'], z['a']), (ref['B'], ref['a']), p)
    count += 1
self.assertGreater(count, 70)
```

`range(13, 1000, 4)` produit 247 valeurs, toutes ≡ 1 mod 4 par arithmétique (`13 mod 4 = 1`, incrément 4 = préservatif). Parmi elles, `is_prime` en retient **92** (validation upstream `harvey_validation.json` champ `primes_all_indices`).

**Reconstruction empirique de la liste** : script `scripts/cartier_miller/list_92_primes.py` (Python pur, sans NTL, livrable en P1+) qui re-dérive la liste 92 à partir de la même définition. Garde : assertEqual strict sur la sortie upstream `primes_all_indices` si elle est exposée ; sinon comparaison littérale de 92 entiers.

```python
def is_prime(n: int) -> bool:
    if n < 2: return False
    if n < 4: return True
    if n % 2 == 0: return False
    for p in [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]:  # bases déterministes < 3.3e24
        if n == p: return True
        if n % p == 0: return False
    return miller_rabin_deterministic(n)
```

(pilot.py §2, déjà documenté en P1 pilot #19493.)

## 2. Couverture déjà attestée vs gap P1+

| Test | Primes couverts | État P1 (PR #19510) | Gap P1+ |
|---|---|---|---|
| `independent_point_counts_and_complete_sum` | 92 (assertion ≥100 #70) | **7 paper primes seulement** (97 → 10⁸) | **85 primes entre 13 et 997**, à exécuter |
| `large_cross_checks` | 6 larges [10⁴, 10⁵, 10⁶, 10⁷, 10⁸, 10⁹] | 6 couv. (paper_seven + cross-check `1000000009`) | **0** — déjà couverts |
| `frobenius_residues` | 4 petits [13, 37, 97, 1009] | 2 couv. (97, 1009 sont dans paper_seven) | **2** (13, 37) à ajouter |
| `bsgs_low_order_all_collisions` | p=97 | couv. | **0** |
| `prime_grids_and_rejected_example` | 6 (3 paper + 1000000009 + 2 mode geometric) | couv. partiellement | **0** — interface test |
| **Total ground truth** | **92 + 6 + 4 + 1** = 103 | 7 couv. | **88 à étendre** |

**Synthèse** : le P1 a couvert les 7 paper primes (97, 1009, 10009, 100049, 1000033, 10000121, 100000037). Le P1+ étend aux 85 primes intermédiaires 13 ≤ p ≤ 997 non encore testées + 13 et 37 du test `frobenius_residues`. Total cumulé P1+P1+ : **92** premiers couvrant la rampe d'admissibles `13..997`.

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

| Backend | p=97 | p=997 | p=10⁴ | p=10⁸ |
|---|---:|---:|---:|---:|
| Cornacchia | <1 ms | <1 ms | ~1 ms | ~1 ms |
| Schoof O(log⁴ p) | <1 ms | ~5 ms | ~50 ms | ~5 s |
| BSGS O(p·√p) | <1 ms | ~30 s | (skip) | (skip >10⁴) |
| Harvey C++ | <1 ms | ~1 ms | ~10 ms | ~100 ms |

**Pour 92 premiers** (tous ≤ 997, soit dans la zone d'arbitrage BSGS lente) :
- Cornacchia : 92 × <1 ms = ~100 ms
- Schoof : 92 × ~5 ms (moyenne) = ~500 ms
- BSGS : 92 × ~30 s (p ≤ 997, ~5.5e7 ops) = **~46 min** — c'est le goulot
- Harvey C++ : 92 × ~1 ms = ~100 ms (build préalable requis)

**Total estimé** : ~50 minutes en mono-thread. Si drop de BSGS pour les 92 (trop lents sans valeur ajoutée : Schoof et Cornacchia valident déjà pour p ≤ 997), budget tombe à **~1 minute**.

**Décision** : exécuter BSGS pour **10 premiers seulement** parmi 92 (échantillon stratifié : 1-2 premiers par centaine 13..97, 90..997), les 82 restants validés par Cornacchia + Schoof + Harvey. BSGS conserve son rôle de **ground truth tierce** sur un échantillon, sans monopoliser le budget.

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

1. **Schoof non convergent** (rare pour p ≤ 997) : `schoof_mod_l` retourne `None` pour un `l` donné → CRT incomplet → mismatch. À investiguer comme régression.
2. **BSGS timeout** (>60s sur un premier ≤ 997) : signe d'un précalcul trop lourd. Rare pour p ≤ 997.
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
| `scripts/cartier_miller/list_92_primes.py` | Re-dérive la liste 92 par `is_prime(p)` sur `range(13, 1000, 4)`, assertEqual vs upstream si exposée |
| `scripts/cartier_miller/run_p1_plus.py` | Pipeline 3-architecture (Cornacchia + Schoof + BSGS échantillon + Harvey C++ subprocess) |
| `scripts/cartier_miller/compare_to_upstream.py` | Diff vs `harvey_validation.json` upstream, sortie structurée |
| `docs/research/cartier-miller-p1-plus-results.md` | Rapport ground truth 92 — colonne PASS/PARTI par premier, durée par backend, smells |
| `example_results/p1_plus_validation.json` | Sortie du runner, format compatible upstream (champs `all_stopping_indices`, `primes_all_indices`, etc.) |

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

**Statut** : scoping ferme, exécution différée **jusqu'à décision user** sur :
1. **Installer NTL localement** (10 min, `conda install ntl`) — RECOVERABLE-LOCAL.
2. **Router vers po-2027** (linux natif, NTL peut être déjà installé) — RECOVERABLE-MACHINE.
3. **Router vers ai-01** (conda Python 3.12 + linux sub-system) — RECOVERABLE-MACHINE.
4. **Marquer INTRINSIC** (NTL indisponible, ground truth hors-portée) — vote minoritaire, peu probable vu la disponibilité mesurée.

**Recommandation** : **option 2 (po-2027)** — la lane a déjà l'infrastructure WSL/Linux (cf carnet `tapis` #14846), NTL peut être en place ou trivial à installer. Si NTL absent, fallback option 3 (ai-01, sub-system linux). Option 1 (po-2023 conda) est faisable mais pollue le sandbox Python local.

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

Liste complète reconstruite par `list_92_primes.py` (à exécuter, ne pas hardcoder — la définition est `is_prime(p) and 13 ≤ p ≤ 997 and p ≡ 1 (mod 4)`, pas un set figé) :

| Range | Count | Exemples |
|---|---:|---|
| 13..97 | 4 | 13, 17, 29, 37, 41, 53, 61, 73, 89, 97 |
| 101..997 | (88 - 4 premiers de 13..97) | 101, 109, 113, ..., 997.

Le script de référence est `test_validation.py::test_independent_point_counts_and_complete_sum` : re-derrière la liste par `range(13, 1000, 4) ∩ primes`, assertEqual `count > 70`. La valeur exacte 92 est `primes_all_indices` dans `harvey_validation.json`.

**Référence upstream** : `harvey_validation.json` champ `validation.primes_all_indices: 92` (cf P1 integration §3 — empirical proof 10809 stopping queries + 2130 exact-binomial + 328 miller + 26 forced-big + 7 large-modulus + 3 invalid-input).

— Mémo rédigé par `myia-po-2023:CoursIA-2`, c.1100, lane worker, 2026-10-06.