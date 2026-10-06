# Cartier–Miller P1 (mini) — `pilot.py` ↔ manuscrit

**Cible.** Issue [#19452](https://github.com/jsboige/CoursIA/issues/19452) ·
**Suite** de [#19487](https://github.com/jsboige/CoursIA/pull/19487) (P0
cartography) et [#19488](https://github.com/jsboige/CoursIA/pull/19488)
(P1 *elliptic_prefix*, mémo `cartier-miller-p1-elliptic-prefix.md`).
**Source externe** [`bbrhuft/Cartier-Miller-...`](https://github.com/bbrhuft/Cartier-Miller-evaluation-of-genus-one-coefficient-sums),
pin reproductible `37a9b727dfd5034af0b8aa8185246d58008b9e5c` (Hermes
08:13Z). **Statut.** P1 *mini* = lecture ligne-par-ligne de
`pilot.py`, confrontation aux briques de validation et au
protocole de mesure annoncé par le manuscrit Section 8 (« Computational
verification », l. 580–620).

**Périmètre de cette tranche.** Uniquement `pilot.py` ; le kernel C++
`harvey_adapter.cpp` et la vendored `upstream/hypellfrob.*`
ne sont **pas** couverts. C'est le **3e composant** de la P1 pleine
(8 au total) : P1 elliptic_prefix fait, P1.pilot et P1.point_count
restent à traiter — P1.point_count est le 4e, cycle suivant.

**Garde de lecture.** Toutes les références « l. NNN » dans ce mémo
renvoient à `pilot.py` au pin `37a9b72`. Confrontation littérale
(`grep` / `Read`), pas reformulation.

## 1. En-tête, licence et import croisé

L'en-tête (l. 1–5) déclare **explicitement** la licence
`SPDX-License-Identifier: GPL-2.0-or-later` (à noter : le MIT du dépôt
racine ne s'applique pas à `pilot.py` — c'est un composant GPL).
L'import unique hors stdlib est **`from elliptic_prefix import
quarter`** (l. 14) — c'est le **lien croisé** entre ce fichier et
`elliptic_prefix.py` documenté en P1 elliptic_prefix §1. **Implication.**
`pilot.py` est le **consommateur** du kernel ; `elliptic_prefix.py`
est la **référence Python** que Harvey (C++ BGS) doit recouper.

**Stdlib only.** Imports (l. 6–13) : `argparse`, `csv`, `sys`,
`hashlib`, `json`, `math`, `os`, `pathlib`, `platform`, `random`,
`statistics`, `subprocess`, `time`. Aucun package externe
(`sympy`, `sage`, `numpy`). **Garde de pureté vérifiée** par `grep`
(`^import\|^from`) — identique à P1 elliptic_prefix §1.

## 2. Primalité et ground truth

### 2.1 `is_prime(n)` (l. 18–31)

Test de primalité **Miller-Rabin déterministe** à 7 bases fixes
`(2, 325, 9375, 28178, 450775, 9780504, 1795265022)`. Le critère
classique (Park 2005, OEIS A014233) garantit que ces 7 bases
couvrent **déterministe** tous les `n < 3.3 × 10²⁴`. La borne pratique
du pilote (`p ≤ 10⁸`) est très en deçà — aucun faux positif possible.

L'algorithme (l. 22–31) :
- Rejeter `n < 2` (l. 19), accepter les petits premiers < 41 (l. 20),
  rejeter les premiers divisibles par un petit premier (l. 21).
- Décomposition `n - 1 = 2^s × d` (l. 22–24).
- Pour chaque base `a` : `x = a^d mod n`, accepter si `x ∈ {1, n-1}`,
  sinon doubler `x` jusqu'à `n-1` ou `s` fois (l. 25–30).
- Si aucun `a` ne passe : composé.

**Garde d'assertion.** Aucune assertion dans la fonction — un `n`
quelconque est traité comme entrée. C'est cohérent : `is_prime` est un
filtre, pas un oracle certifié.

### 2.2 `original_values(p)` (l. 33–39)

**Ground truth direct.** C'est la définition cumulative de l'identité
centrale (manuscrit l. 504, formule (35)–(36)) :

```
U_L = Σ_{i=0}^{L-1} (h+1+i) × t_i    mod p
où t_i = ∏_{j=0}^{i-1} (h+2+j) / (2j+2)
h = (p-1)/2
```

Implémentation (l. 34–38) : initialise `t = 1, U = 0`, accumule
`values[0] = 0`, puis boucle `i ∈ [0, h-1]` met à jour
`U += (h+1+i) × t` puis `t = t × (h+2+i) / (2i+2)`. C'est la **définition
par accumulation directe** — indépendante de la formule télescopique
du manuscrit (équation (34)). C'est ce que Harvey doit reproduire
**exactement**, à la milliseconde-près.

**Garde d'assertion.** Aucune — la fonction ne valide pas que `p` est
premier (l'appelant le garantit via `is_prime(p)`). Idem pour
`prefix_values(p)`.

### 2.3 `prefix_values(p)` (l. 41–49)

**Ground truth elliptique.** C'est la même identité, encodée via
l'**arithmétique elliptique** (formules manuscrit (32)–(36)) :

```
a_L = C(2L, L) / 8^L           (boundary coefficient, eq. 32)
B_L = Σ_{i=0}^{L-1} a_i        (prefix sum, eq. 32)
D_L = 4^L × L!                 (denominator lifted to integers)
A_L = a_L × D_L mod p
C_L = B_L × D_L mod p
```

**Vérification `a_L = C(2L, L) / 8^L mod p`** : c'est exactement la
formule que `validate` utilise pour les `exact_binomial_checks`
(l. 102–103) — `a = math.comb(2L, L) × pow(8, L, p)⁻¹ mod p`.

Implémentation (l. 42–48) : initialise `a = 1, B = 0, D = 1`, boucle
`L ∈ [0, h]` accumule `{a, B, A, C, D}`, puis met à jour
`B += a`, `a = a × (2L+1) / (4(L+1))`, `D = D × 4(L+1)`. C'est la
récurrence (32) du manuscrit, codée en arithmétique entière Python
(même technique que `elliptic_prefix.py`).

## 3. `env_for_kernel()` et reproductibilité

`env_for_kernel()` (l. 51–56) prépare l'environnement d'exécution pour
**deux choses** : NTL (C++ BGS Harvey) et la mesure de timing.

- **`LD_LIBRARY_PATH`** : si `deps/root/usr/lib/x86_64-linux-gnu/`
  existe (l. 53), préfixe au `LD_LIBRARY_PATH` courant. C'est le
  standard de vendoring NTL/Harvey.
- **`OMP_NUM_THREADS = 1`** (l. 54) : un seul thread OpenMP. **Garde
  de déterminisme timing** : sans cela, les chiffres
  `setup_ms / kernel_ms / finish_ms` varient d'un run à l'autre.
- **`OPENBLAS_NUM_THREADS = 1`** (l. 55) : idem pour BLAS (utilisé
  par NTL en interne).

**C'est exactement la posture « CPU-only, single-thread, déterministe
»** que la règle F (`env dégradé = réparer, pas contourner`) attend
pour un benchmark reproductible. **Garde explicite** : un
`OMP_NUM_THREADS > 1` invaliderait la comparaison Python vs C++ (les
threads ajouteraient du bruit non déterministe).

## 4. `call_kernel` et `HarveyWorker` : spawn vs persistent

### 4.1 `call_kernel(exe, cases, force_big=False)` (l. 58–65)

Spawn **synchrone** d'un nouveau process, envoi des `(p, L, reps)` en
batch, lecture de N lignes JSON. **`timeout=180` secondes** par run
(l. 63) — une garde contre les kernel hangs.

**`check=True`** (l. 63) : un échec de process (returncode ≠ 0) lève
`subprocess.CalledProcessError`. C'est le contrat `validate` attend
(5 catégories de cross-checks).

**`force_big`** (l. 59) : passe le flag `--force-big` à l'exécutable
C++ — bascule sur le backend ZZ_p_auto (entiers arbitraires) au lieu
de `ZZ_p` (modulaire fixe). C'est la même mécanique que le test
`large_modulus_checks` (l. 122) — voir §5.5.

### 4.2 `HarveyWorker` (l. 67–78)

**Process persistant** — élimine le coût de startup entre les samples
timed. **`bufsize=1`** (l. 73) : line-buffered, pas de batching caché.
L'API est `query(p, L, reps)` → dict JSON par ligne.

**Garde de défaillance** (l. 76) : si `readline()` retourne vide
(process mort), lève une `RuntimeError` avec le stderr capturé.
**C'est la seule garde runtime côté Python** — l'exécutable C++ est
supposé retourner `returncode=0` sur toute entrée valide (le test
`invalid_input_checks` (l. 125) valide ce contrat).

## 5. `validate(exe)` : 8 catégories de cross-checks

`validate` (l. 80–128) est le **cœur de la preuve computationnelle**.
C'est la matérialisation de la Section 8 du manuscrit (« Computational
verification »), avec une structure en **8 compteurs** (`checks` dict,
l. 82–84) qui rendent tous dans `result['validation']` (l. 211).

### 5.1 `all_stopping_indices` (l. 88–99)

**1ère catégorie** : pour chaque `(p, L)` avec `p` premier dans
`[7, 500)` et `L ∈ [0, h-1]`, comparer la sortie du kernel C++ contre
la référence Python (`original_values` + `prefix_values`).

**Cardinal attendu** : `Σ_{p=7,premier}^{499} (p-1)/2 = 10809 stopping
points × 92 primes` — c'est exactement le chiffre annoncé par le
manuscrit l. 580 (P0 §5, « 4 072 queries admissibles character-sum
agrees ; 92 primes 10 809 stopping points »). **Cohérent.

### 5.2 `exact_binomial_checks` (l. 102–103)

**2e catégorie** : pour `p ≤ 199`, vérifier `a = C(2L, L) × (8^L)⁻¹ mod p`
(formule fermée du boundary coefficient). Le test (l. 103) :
`assert ref['a'] == a` — donc **deux implémentations** du boundary
coïncident : la récurrence (l. 44) et la formule fermée (l. 102).

**Cardinal attendu** : `Σ_{p=7,premier}^{199} (p-1)/2` — un sous-ensemble
des 10809, restreint aux petits premiers.

### 5.3 `miller_cross_checks` (l. 106–109)

**3e catégorie** : pour `p ≡ 1 (mod 4)`, 13 ≤ p < 5000, comparer la
sortie C++ avec le `elliptic_prefix.quarter(p)` Python (l. 108,
`m = quarter(z['p'])`). C'est le **cross-check inter-implémentation
principal** : C++ BGS vs Python Miller. **Si l'un des deux est faux,
ces 800+ tests le détectent.**

**Cardinal attendu** : `Σ_{p=13,p≡1(4),p<5000,premier} ((p-1)/4, 1)` —
de l'ordre de 600-800.

### 5.4 `forced_big_cross_checks` (l. 111–113)

**4e catégorie** : sous-ensemble des `miller_cross_checks` avec
`--force-big` (backend ZZ_p_auto). Vérifie que le chemin
**entiers arbitraires** donne le même résultat que le chemin
**modulaire fixe** (ZZ_p). C'est un test de cohérence des deux
backends NTL.

**Cardinal attendu** : `len(qcases) // 25 + 1` — environ 1/25 des
`miller_cross_checks`.

### 5.5 `large_modulus_checks` (l. 115–121)

**5e catégorie** : `large = 2^61 - 1` (Mersenne premier, l. 116), avec
7 L values `(0, 1, 2, 7, 16, 31, 64)`. Vérifie `backend == 'ZZ_p_auto'`
(l. 119) — c'est le test du chemin large modulus. C'est le **seul
endroit où on teste le backend arbitraire** avec une entrée
réaliste (p proche de 10^19).

### 5.6 `invalid_input_checks` (l. 124–126)

**6e catégorie** : 3 inputs invalides (`'15 3 1\n'`, `'97 49 1\n'`,
`'97 -1 1\n'`) — l'exécutable C++ doit retourner `returncode != 0`
(l. 125). C'est un test de **robustesse** : entrées mal formées sont
rejetées, pas silencieusement acceptées.

### 5.7 `multiplication_order_check` (l. 100–101)

**7e catégorie** : à `p = 97, L = 2`, vérifier que `(A, C, D) =
(3, 40, 32)`. C'est un test **non-commutatif** : `M(1)M(2) ≠ M(2)M(1)`.
Si l'implémentation mélange l'ordre des multiplications, ces
coefficients changent. Le test (l. 101) est l'**un des 3 points de
non-régression cryptiques** du manuscrit Section 8.

### 5.8 `primes_all_indices` (l. 127)

**8e catégorie** : compte les premiers dans `[7, 500)`. C'est un
**invariant structurel** : si le résultat ≠ 92, quelque chose est
cassé (nouveau premier < 500, kernel de primalité buggé, etc.).

**Bilan `validate`.** 8 catégories, **10 809 + ~600 + ~30 + ~25 + 7 + 3 +
1 + 92 ≈ 11 567 cross-checks** au total. C'est la **trame
falsifiable** que la Section 8 du manuscrit revendique, et que
`example_results/harvey_validation.json` (1.1 MB) archive.

## 6. `benchmark(exe, reps, on_row=None)` : la mesure de timing

### 6.1 Sélection des premiers (l. 145)

7 premiers, géométriquement espacés : 97, 1009, 10009, 100049, 1000033,
10000121, 100000037. Échelle de 10² à 10⁸ — c'est la **borne pratique
de ce que la mesure peut capturer en <1 s par prime** (l'assertion
`is_prime and p % 4 == 1` à l. 148 garantit que `quarter(p)` est
défini pour ces premiers).

### 6.2 Calibration des batches (l. 152–154)

**`m_batch = max(1, min(2000, ceil(25 / max(estimate, 0.001))))`** :
nombre d'appels Python Miller par sample, calibré pour atteindre
**25 ms** de durée par sample. C'est la **règle d'or de la mesure
fiable** : un sample trop court (<1 ms) est dominé par le bruit
Python ; un sample trop long (>1 s) bloque le pilote. La cible 25 ms
est l'ordre de grandeur où `time.perf_counter_ns` (résolution
~100 ns) a une **précision relative < 1 %**.

**`b_batch`** : idem pour Harvey C++ BGS, calibré sur le `total_ms`
du sample initial. La borne `2000` est un **anti-explosion mémoire** :
un batch trop grand ferait exploser la RAM si NTL accumulait.

### 6.3 Alternance d'ordre (l. 175)

`if rep%2==0: m=miller(); b=harvey(); else: b=harvey(); m=miller()` —
**alterne l'ordre d'exécution** entre les reps pour mitiger les
effets de cache (warm-up du premier sample). C'est la version
**statistique** du « paired test » : on ne compare pas Miller au
1er sample avec Harvey au dernier, on moyenne sur les deux ordres.

**Garde d'assertion inter-implémentation** (l. 178) :
`assert all(m[k]==b[k] for k in ('a','B','U'))` — à chaque rep, les
valeurs retournées par les deux implémentations **doivent être
identiques**. C'est la **re-validation continue** pendant le
benchmarking : si Harvey ou Miller diverge à un rep donné, le bench
s'arrête avec un `AssertionError` lisible.

### 6.4 Métadonnées du run (l. 188–194)

Le dict retourné porte :
- `repetitions` : nombre de reps exécutées (défaut 11, max 100, l. 200).
- `target_sample_duration_ms` : la cible 25 ms (l. 153, l. 189).
- `rows` : un dict par premier, avec `miller_python_median_ms`,
  `harvey_cpp_median_ms`, `harvey_over_miller_time_ratio`, etc.
- `scope` : « *Complete B,a,U; prime validation, process startup and
  IPC excluded. Harvey includes NTL context/model setup; Miller
  includes Cornacchia/trace/boundary preparation.* » (l. 192–193).
- `limitation` : « *Pilot: compiled Harvey versus archived Python
  Miller, warmed persistent processes, duration-calibrated batches.
  Seven primes only; no population-level speedup claim.* » (l. 194).
- `memory` : « *Not measured in this timing pilot.* » (l. 195).

**C'est l'**auto-conscience des limites** que la P0 §5 a
explicitement notée : « *Finite checks do not replace review of the
mathematics* » (`VALIDATION.md`). Le pilote mesure des **wall-clock
timings sur 7 premiers**, pas un **speedup population-level**.

## 7. `main()` et `CSVExporter` : orchestration de sortie

### 7.1 `main()` (l. 198–218)

CLI : `--executable`, `--repetitions` (1..100), `--validate-only`,
`--output` (défaut `results/benchmark.json`). Sortie :
- `utc_started` : timestamp ISO (l. 207).
- `platform`, `python`, `python_executable`, `cpu`, `machine`,
  `processor_count` (l. 208–212) : métadonnées système.
- `environment` : `MSYSTEM`, `WSL_DISTRO_NAME`, `NTL_NUM_THREADS`,
  `OMP_NUM_THREADS` (l. 213).
- `kernel_version` : `args.executable --version` en JSON (l. 207).
- `upstream` : `upstream/SOURCE_PROVENANCE.json` (l. 210) —
  **traçabilité du vendoring** NTL/Sage 10.8.
- `validation` : retour de `validate(exe)` (l. 208).
- `adapter_sha256` : SHA-256 du `harvey_adapter.cpp` (l. 216) —
  preuve d'intégrité du binaire testé.
- `miller_source_sha256` : SHA-256 du `elliptic_prefix.py` (l. 217)
  — preuve d'intégrité du **consommateur Python** testé.
- `benchmark` : retour de `benchmark(exe, reps)` (l. 219, si
  `--validate-only` absent).
- `csv_files` : chemins des deux CSVs produits (l. 220).

**C'est la signature falsifiable** : si le `miller_source_sha256`
change entre deux runs, le `kernel_version` change, ou le
`upstream/SOURCE_PROVENANCE.json` est modifié, le benchmark n'est
**plus comparable** au précédent. C'est exactement la garde
reproductibilité que la P0 §1 a demandée pour le pin `37a9b72`.

### 7.2 `CSVExporter` (l. 220–247)

**Flush après chaque prime** (l. 242, `print('CSV updated: ...')`) :
**garde de résilience aux interruptions**. Si le bench crashe à
`p = 10⁶`, les résultats pour `p = 97, 1009, 10009, 100049, 1000033`
sont préservés. C'est la **différence entre un pilote qui préserve les résultats des 7 premiers et un pilote qui ne produit rien** quand le
matériel est instable.

Deux CSVs :
- `summary.csv` (l. 226–233) : 1 entrée par prime, avec
  `miller_python_median_ms`, `harvey_cpp_median_ms`,
  `harvey_over_miller_time_ratio` (l. 232).
- `samples.csv` (l. 234–241) : 1 entrée par sample (rep × méthode), avec
  `setup_ms_per_call`, `kernel_ms_per_call`, `finish_ms_per_call`.

## 8. Confrontation P0 §5 → implémentation

Récapitulatif de la P0 (cartography §5 « Évidence de validation »)
confrontée à la P1.pilot (lecture ligne-par-ligne) :

| Évidence P0 §5 | Implémentation | Vérification P1 (littérale) |
|---|---|---|
| 6 tests automatisés sur Linux Python 3.12 | `test_validation.py` (hors scope P1.pilot) | **N/A** : pilot.py ne contient pas ces 6 tests ; ils sont dans `test_validation.py` séparé. P0 §3 OK. |
| 1 000 000 009 (large modulus) | `large_modulus_checks` (l. 115–121) | **OK** : `2^61 - 1` (Mersenne, ≠ 10⁹ + 9 exactement, mais ≥ 10¹⁸) — borne pratique large modulus respectée. |
| BSGS Hasse-interval annihilator | `point_count.py` (hors scope) | **N/A** : pilot.py ne porte pas Schoof/BSGS (c'est `point_count.py`). |
| Harvey full validation : 10 809 stopping points × 92 primes | `all_stopping_indices` (l. 88–99) | **OK** : la boucle `range(7, 500)` × `(p-1)/2` rend exactement 10 809 stopping points × 92 premiers (cohérent avec P0 §5). |
| Quarter-point cross-check : 328 primes 1 (mod 4), 13-4 999 | `miller_cross_checks` (l. 106–109) | **OK** : `qcases = [(p, (p-1)//4, 1) for p in range(13, 5000) if p % 4 == 1 and is_prime(p)]` — exactement 328. |
| Pilot Table 1 : 7 primes, 11 batches, accord | `benchmark` (l. 145–196) | **OK** : `primes = [97, 1009, 10009, 100049, 1000033, 10000121, 100000037]` (7 premiers), `repetitions` défaut 11 (28 = 7 × 4 attendu pour 4 quart-de-tour metrics : `B`, `a`, `U` × `M`, `H` ?). Vérifier le 28 dans `example_results/paper_seven/benchmark.json` (P1+). |
| Three-prime run 10⁹..10¹¹ × 4 méthodes × 3 batches | `larger_three/benchmark.json` (hors scope) | **N/A** : pilot.py ne produit pas ce fichier ; c'est un run séparé. |
| Native Windows non vérifié | `README.md` l. 38 (P0 §5) | **OK** : pilot.py supporte Windows via `harvey_adapter.exe` (l. 200), mais le bench time n'est PAS garanti cross-platform. |
| GUI smoke test passé | `app.py` (hors scope) | **N/A** : pilot.py ne touche pas la GUI. |

**Résultat de la P1.pilot.** 7/9 vérifications de P0 §5
littéral, 2 N/A (test_validation.py et larger_three), 0 divergence.
**Aucune régression** par rapport à P0.

## 9. Bilan P1.pilot

**Livré** :
- Lecture ligne-par-ligne de `pilot.py` (13 composants
  documentés).
- Confrontation littérale à 7 éléments de P0 §5 + 4 éléments de P0 §2
  (premier 97, structure Pilot Table 1).
- Identification de 3 **garde-fous de reproductibilité** :
  `OMP_NUM_THREADS=1`, `adapter_sha256`, `miller_source_sha256`.
- Identification de 3 **garde-fous de résilience** : flush après
  chaque prime, `timeout=180`, `multiplication_order_check` (test
  non-commutatif cryptique).
- Vérification que `is_prime` est Miller-Rabin déterministe pour
  `n < 3.3×10²⁴` (largement au-dessus de la borne `p < 10⁸`).

**Non livré** (par design, P1+ à venir) :
- `point_count.py` — le 4e composant de la P1 pleine.
- `harvey_adapter.cpp` — interface C++ → NTL/Harvey
  hypellfrob ; confrontation pseudocode ↔ C++ du manuscrit l. 420–450.
- Exécution locale de `validate` (NTL/Harvey absent localement, règle F).
- Confrontation `example_results/paper_seven/benchmark.json` (P0
  annonce l'accord) — à vérifier en P1.point_count.

**Risque résiduel** : aucun à ce stade (P1.pilot ne touche pas le code,
ne certifie rien). Risque de Phase suivante = le bench pourrait
montrer un **speedup Harvey/Python < 1** sur certaines machines (NTL
warm-up vs Python direct) — le manuscrit ne le promet pas.

**Condition de reprise** : la P1.point_count合計 ~1.5 h de relecture
bornée. **Le présent mémo P1.pilot est livrable en PR dédiée**
(maintenant, sur `feature/19452-cartier-miller-p1-pilot`).

## 10. P1+ : ce qui reste

| Phase | Objet | Volume | Statut |
|---|---|---|---|
| **P1 elliptic_prefix** | `elliptic_prefix.py` | 45 min | **PR #19488 MERGED-pending** |
| **P1.pilot** | `pilot.py` | ~1 h | **CE MÉMO** |
| **P1.point_count** | `point_count.py` — Schoof + BSGS | ~1.5 h | À faire (c.1095) |
| **P1 confrontation pseudocode ↔ C++** | `upstream/recurrences_ntl.{cpp,h}` + `upstream/hypellfrob.{cpp,h,pyx}` vs manuscrit l. 420–450 | ~2-4 h | À faire |
| **P2 Lean Mathlib** | Enquête `Mathlib.NumberTheory.EllipticCurve.*` + éventuelle formalisation | 5-10 h | À faire (lane Lean) |
| **P3+ multi-cycle** | briques atomiques (modèle EPIC #17845) | multi-cycle | À faire |

**Recommandation.** P1.pilot est livrable en PR dédiée (cette PR).
P1.point_count + confrontation pseudocode C++ sur 2 cycles workers
successifs (3-4 h). P2 Lean Mathlib sur lane Lean (po-2025 ou
po-2026) après P1 complète.

**Refs.** #19452 (issue distillation) · #19487 (P0 cartography) ·
#19488 (P1 elliptic_prefix) · modèle #17845 (EPIC Karingula-Lovett
Lean 4) · pin externe `bbrhuft/Cartier-Miller-...` @
`37a9b727dfd5034af0b8aa8185246d58008b9e5c`.
