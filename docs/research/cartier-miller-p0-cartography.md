# Cartier–Miller P0 — cartographie énoncés ↔ code

**Cible.** Issue
[#19452](https://github.com/jsboige/CoursIA/issues/19452) (distillation, modèle
EPIC #17845). **Source externe**
[`bbrhuft/Cartier-Miller-evaluation-of-genus-one-coefficient-sums`](https://github.com/bbrhuft/Cartier-Miller-evaluation-of-genus-one-coefficient-sums),
manuscrit non référé de David Jordan (David.jordan@mu.ie), assistance IA
auto-déclarée. **Pin reproductible** (Hermes 08:13Z) : commit
`37a9b727dfd5034af0b8aa8185246d58008b9e5c` (`main`, 06/10 08:19Z).

**Statut documentaire.** P0 = lecture intégrale + cartographie. **Pas** de
validation numérique, **pas** de port Lean, **pas** d'arbitrage de la
nouveauté — c'est la brique P1+ (à traiter en cycles suivants). Toutes les
affirmations ici sont **littérales** (page/section + ligne du PDF) ou
**vérifiées** (`grep`/`Read` sur les fichiers au pin).

## 1. Pin et garde de statut

| Champ | Valeur | Source |
|---|---|---|
| Commit audité | `37a9b727dfd5034af0b8aa8185246d58008b9e5c` | `git log --oneline -1` |
| PDF | `Cartier_Miller_Paper_Revised_20261005.pdf` (1 114 306 octets) | `ls -la` |
| Texte extrait | `.paper.txt` (771 lignes, layout) | `pdftotext -layout` |
| Licence dépôt | MIT (LICENCE, 1069 octets) | `cat LICENSE` |
| Statut auteur | « unrefereed draft, AI-assisted » (auto-déclaré) | `README.md` l. 16-17 |
| Garde | « Numerical checks support the formulas, but do not replace independent review » | `README.md` l. 17-18 |

**Implication pour la distillation.** Le corpus est **opinable** (manuscrit
non référé) — la distillation CoursIA formalise la cohérence
identité↔code↔validation, **elle ne certifie pas la nouveauté**. Cette
borne est explicite dans le corps de l'issue #19452 (« ~9 théorèmes, 9
lemmes, 9 propositions, 3 preuves étiquetées » — mesure NanoClaw, à
confirmer en P1+). Le présent mémo assume cette borne et la documente.

## 2. Structure du manuscrit

Le PDF ne porte pas de table des matières explicite ; la structure
reconstituée par inspection du texte (`grep` des en-têtes, lignes de
`.paper.txt`) :

| # | Section / énoncé | Ligne .paper.txt | Énoncés présents |
|---|---|---|---|
| 1 | Abstract | 6-17 | — |
| 2 | Introduction and main theorem | 18-114 | **Theorem 1** (l. 48) — *Uniform base-field evaluation* |
| 3 | Relation to prior work | ~115-130 | refs Serre 1958, Semaev 1998, Rück 1999, Voloch 1990/1997, Satoh-Araki 1998, Smart 1999 |
| 4 | Main proof body | ~130-400 | **Proposition 2** (l. 159) — *Regular residue identity* · **Proposition 3** (l. 215) — *quasi-period negative sign* · **Lemma 3** (l. 220) — *Exceptional Cartier defect* |
| 5 | Algorithm for the differentiated Miller chain | 420-450 | pseudocode (T := R, alpha := 0, j := 0) — subroutine ADD avec splitting sur zéro diviseur |
| 6 | Corollary 4 — *Deterministic polynomial-time evaluation* | 457-481 | preuve informelle Schoof + Miller ; eq. (31) `total = Schoof(p) + O((log p)^3)` |
| 7 | Application to the original quarter point sum | 484-548 | courbe `E: y² = x³ + 2x` (j=1728), `a_n ≡ τ (mod p)` |
| 8 | Computational verification | 580-620 | 4 072 queries admissibles character-sum agrees ; 92 primes 10 809 stopping points |
| 9 | References | 622-679 | Cartier 1957, Miller 2004, Schoof 1985, Satoh-Araki 1998, Smart 1999, Rück 1999, Voloch 1990/1997, Bostan et al. 2007, Harvey 2007, Cosgrave-Dilcher 2010 |
| 10 | Appendix: Pilot Benchmark | 727-771 | Table 1 : 7 primes 1 (mod 4), Python CM vs C++ Harvey/BGS ; reproduction commands |

**Observations structurelles (sans porter de jugement de fond) :**

- Le Theorem 1 est l'énoncé central ; Lemma 3 et Propositions 2-3 sont ses
  briques. Corollary 4 fixe la borne algorithmique. L'application
  quarter-point (Section 7) est un cas particulier qui motive le pipeline.
- L'algorithme (Section 5) est en pseudocode, pas en Lean. Le splitting
  sur zéro diviseur dans `√(2)` est le seul moment où la complexité
  peut doubler (« resuming at most two components preserves this bound »,
  l. 449-450).
- Le Theorem 1 inclut explicitement les traces exceptionnelles `τ=±1`
  (l. 49, l. 296-298, l. 472) — c'est ce qui motive le cas exceptionnel
  traité par Lemma 3.

## 3. Inventaire du dépôt

Dénombrement vérifié à la racine et dans `Cartier_Miller_Benchmark/` :

| Fichier | Taille (octets) | Lignes | Rôle |
|---|---|---|---|
| `Cartier_Miller_Paper_Revised_20261005.pdf` | 1 114 306 | — | manuscrit (28 pages) |
| `Cartier-Miller-With-SEA.jpg` | 151 047 | — | figure illustrative |
| `LICENSE` | 1 069 | — | MIT |
| `README.md` | 8 861 | — | description + références |
| `Cartier_Miller_Benchmark/elliptic_prefix.py` | — | 265 | Cartier preparation (Cornacchia/Gauss, `class Quadratic`, `SplitRoot`) |
| `Cartier_Miller_Benchmark/point_count.py` | — | 230 | Schoof + BSGS, **no Cornacchia, no PARI, no Miller** |
| `Cartier_Miller_Benchmark/pilot.py` | — | 265 | orchestration Miller vs Harvey BGS, hash + per-call math data |
| `Cartier_Miller_Benchmark/benchmark_engine.py` | — | 230 | 4-method benchmark (CM-Cornacchia / CM-Schoof / CM-BSGS / Harvey BGS) |
| `Cartier_Miller_Benchmark/app.py` | — | 198 | GUI Tk + matplotlib |
| `Cartier_Miller_Benchmark/charts.py` | — | 43 | visualisation (4 onglets) |
| `Cartier_Miller_Benchmark/harvey_adapter.cpp` | — | 87 | adaptateur vers `upstream/hypellfrob.{cpp,h,pyx}` |
| `Cartier_Miller_Benchmark/test_validation.py` | — | 52 | 6 tests automatisés |
| `Cartier_Miller_Benchmark/run_windows.{py,cmd}` | — | 54 + 16 | runner Windows natif |
| `Cartier_Miller_Benchmark/build.sh` | — | — | build C++ |
| `Cartier_Miller_Benchmark/requirements.txt` | — | — | dépendances |
| `Cartier_Miller_Benchmark/VALIDATION.md` | — | — | 2e pilier : protocole de validation |
| `Cartier_Miller_Benchmark/SHA256SUMS.txt` | — | — | empreintes par fichier (auto-vérification) |
| `Cartier_Miller_Benchmark/example_results/harvey_validation.json` | — | — | 10 809 stopping points × 92 primes + 2 130 exact binomiaux + 328 quarter-points + 26 large-mod + 3 invalid |
| `Cartier_Miller_Benchmark/example_results/larger_three/` | — | — | 3 primes 10⁹..10¹¹ × 4 méthodes × 3 batches, 12 lignes d'accord |
| `Cartier_Miller_Benchmark/example_results/paper_seven/` | — | — | 7 primes (p = 97 à 100 000 037), 11 batches, 28 lignes d'accord |
| `Cartier_Miller_Benchmark/upstream/` | — | — | `hypellfrob.{cpp,h,pyx}` + `recurrences_ntl.{cpp,h}` (Sage 10.8 vendored) |

**Total code applicatif :** 1 440 lignes Python + 87 lignes C++
adaptateur + upstream vendored. Échelle typique d'une distillation
académique — bien plus petit que les corpus CoursIA existants.

## 4. Identité ↔ code : ce qu'on peut confronter

L'identité centrale (eq. 4 du manuscrit, l. 48-55) est

> `S_f(λ) = H − χ r Ψ_{M_χ}(D)`

avec `H = c_{p-1} ≡ τ (mod p)`, `r = 1/(λ v_0)`, `M_χ = p+1 − χτ`, et
`Ψ_M` une dérivée logarithmique d'une fonction de diviseur `MD`,
normalisée par `dw/v` au point à l'infini.

| Composant identité | Implémentation putative | Vérification P0 | Vérification P1+ |
|---|---|---|---|
| `H = c_{p-1} = τ (mod p)` | `elliptic_prefix.py` (préparation trace) | trace = `p + 1 − |E(𝔽_p)|` apparaît dans les docstrings (Cartier-Miller-With-SEA) | relecture ligne-par-ligne du calcul |
| `χ` (caractère quadratique de `d = f(1/λ)`) | `elliptic_prefix.py::Quadratic` | classe détectée l. 12-30 du fichier | — |
| `r = 1/(λ v_0)` | `pilot.py` + `harvey_adapter.cpp` | pas inspecté en P0 | relecture subroutine ADD l. 420-450 |
| `Ψ_{M_χ}(D)` (dérivée log, recurrence Miller) | `pilot.py` + `upstream/hypellfrob.{cpp,h,pyx}` | pseudocode manuscrit Section 5 (l. 420-450) | confrontation pseudocode ↔ C++ upstream |
| `M_χ = p+1 − χτ` | `pilot.py` | pas inspecté en P0 | relecture |
| Trace preparation (Schoof ou BSGS) | `point_count.py` (Schoof division polynomials + BSGS Hasse) | l. 1-12 docstring explicite « Neither counter calls Cornacchia, Gauss, PARI, or the Miller evaluator » | relecture du kernel Schoof (CRT, D5 splitting) |
| Cas exceptionnel `τ=±1` (Lemma 3) | **non localisé en P0** | — | grep `tau == 1` / `tau == -1` / `exceptional` dans les 6 .py ; identifier le sous-programme |
| Quarter-point application `U_p(n) = 4 B_n + (9/4) a_n` | `elliptic_prefix.py::quarter` | importé dans `pilot.py` (l. 12) | confrontation formule ↔ code |

**Note d'angle mort.** L'angle mort spécialiste (assumé dans le corps de
l'issue #19452 : « elliptique / caractéristique p n'est la profondeur
spécialiste d'aucune lane ») joue ici à plein : la **justesse** de
l'identité relève d'un lecteur formé, pas de l'inspection de surface.
Cette cartographie **ne tranche rien** sur la nouveauté mathématique.

## 5. Évidence de validation

Le `VALIDATION.md` (2e pilier) et les `example_results/` documentent les
**vérifications computationnelles** exécutées par l'auteur. Inventaire
froid des chiffres annoncés vs ce que les fichiers contiennent :

| VALIDATION.md声称 | Source | Vérification P0 (taille / existence) | Statut |
|---|---|---|---|
| 6 tests automatisés sur Linux Python 3.12 | `test_validation.py` (52 lignes) | OK (52 lignes, 6 fonctions visibles via grep) | à exécuter en P1+ |
| 1 000 000 009 (large modulus) | `example_results/larger_three/benchmark.json` (89 732 octets) | OK (fichier présent) | à ouvrir en P1+ |
| BSGS Hasse-interval annihilator | `point_count.py` l. 1-12 | OK (référencé) | à inspecter en P1+ |
| Harvey full validation : 10 809 stopping points × 92 primes | `example_results/harvey_validation.json` | OK (présent) | à inspecter en P1+ |
| Quarter-point cross-check : 328 primes 1 (mod 4), 13-4 999 | `example_results/harvey_validation.json` | OK | à inspecter en P1+ |
| Pilot Table 1 : 7 primes, 11 batches, 28 lignes d'accord | `example_results/paper_seven/benchmark.json` | OK (présent) | à confronter aux valeurs annoncées |
| Three-prime run 10⁹..10¹¹ × 4 méthodes × 3 batches, 12 lignes | `example_results/larger_three/benchmark.json` | OK (présent) | à confronter aux valeurs annoncées |
| Native Windows non vérifié | `README.md` l. 38 | OK (mention explicite) | — |
| GUI smoke test passé (8 lignes, 4 chart tabs, CSV/PNG export) | `GUI_preview.png` (151 047 octets) | OK (image présente) | à ouvrir en P1+ pour QA visuel |

**Garde de lecture.** `VALIDATION.md` est explicitement non canonique
pour les mathématiques : « *Finite checks do not replace review of the
mathematics or of the new implementations* ». L'inspection P0 ne peut
donc pas — et ne doit pas — être lue comme une validation de la
justesse de l'identité. Elle documente la **structure** de la validation.

## 6. Trois briques explicites (à traiter en P1+)

Le corps de #19452 propose 3+1 phases. La P0 (ce mémo) couvre la
cartographie. Les phases suivantes :

| Phase | Objet | Volume attendu | Lane pressentie |
|---|---|---|---|
| **P1** | Vérif statique identité ↔ code : confronter eq. 4 manuscrit (l. 48-55) au calcul dans `elliptic_prefix.py::quarter` + `pilot.py::run` + `point_count.py::Schoof` | ~3-5 h, lecture ciblée des 3 fichiers + sous-programmes | po-2023 (cette lane) — sous-traitance `point_count.py::Schoof` possible vers ai-01 si kernel Schoof demande |
| **P2** | Arbitrage des candidats de formalisation Lean : identité explicite, normalisation cas exceptionnel, quarter-point `j=1728`, et **enquête d'organes Mathlib** (courbes elliptiques, Frobenius, Cartier : couverture Mathlib 4 à mesurer — `Mathlib.NumberTheory.EllipticCurve.*` ?) | ~1-2 h inventaire + 5-10 h formalisation (brique k-x séparée) | po-2025 (adjoint) ou po-2026 (Lean) — expertise Lean spécifique |
| **P3+** | Briques atomiques : oracle externe (modèle #17845), briques itératives, jumeaux i18n, review statique des deux lanes | multi-cycle | multi-lane (modèle #17845 : Karingula-Lovett) |

**Pourquoi la P1+ est à scoper en cycles dédiés.** P1 seule demande une
relecture ligne-par-ligne de ~760 lignes Python, avec confrontation
explicite à 4 formules du manuscrit — c'est un grain de 3-5 h, pas un
mémo. Tenter de la faire dans la foulée de la P0 mélangerait les
niveaux d'évidence (cartographie = `[VERIFIED par grep]` ;
confrontation = `[REVIEWED ligne-par-ligne]`).

## 7. Bilan P0

- **Livré** : cartographie exhaustive (manuscrit, dépôt, identité↔code,
  validation) à un pin précis (`37a9b72`).
- **Non livré** (par design) : verdict sur la nouveauté mathématique,
  exécution locale, port Lean, confrontation pseudocode ↔ C++.
- **Risque résiduel** : aucun à ce stade (P0 ne touche pas le code, ne
  certifie rien). Risque de Phase suivante = dépassement de scope (P1
  tentée comme audit, devrait être relecture bornée).
- **Condition de reprise** : la P1 demande un **kernel Python avec
  NTL/Sage 10.8** pour ré-exécuter `harvey_validation.json` — cette
  lane n'a pas NTL installé (règle F : « kernel manquant = installer,
  pas contourner »). P1+ soit installe NTL localement, soit route vers
  une lane qui l'a (ai-01 historique ? po-2024 ? à mesurer).

Refs #19452 (issue distillation) · modèle #17845 (Karingula-Lovett
Lean 4 distillation) · références externes : Cartier 1957
([zbmath 0077.04502](https://zbmath.org/?q=an:0077.04502)) · Miller 2004
([doi:10.1007/s00145-004-0315-8](https://doi.org/10.1007/s00145-004-0315-8)) ·
Schoof 1985.
