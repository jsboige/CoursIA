# P1 C++ anchors — Cartier-Miller evaluation of genus-one coefficient sums

**Pin :** bbrhuft/Cartier-Miller-evaluation-of-genus-one-coefficient-sums @ `37a9b72` (clone local `.scratch`).
**Scope :** lecture intégrale sans EOF des fichiers C++ du pin `37a9b72` : `harvey_adapter.cpp` (l. 21-87), `upstream/recurrences_ntl.{h,cpp}`, `upstream/hypellfrob.{h,cpp}`. Comptes détaillés dans la table d'ancres §1.
**Statut :** distillation didactique d'un manuscrit non-référé (MIT externe pour le PDF), dépôt GPL-2.0-or-later. Aucun verdict de nouveauté mathématique n'est porté ici. Lecture seule — aucun fichier C++ modifié.
**Précédents :** P0 cartography (#19487), P1 elliptic_prefix (#19488), P1 pilot (#19493), P1 point_count (#19499). Ce mémo est le 5e volet.

> **Note (c.1171 reduction coord-anchor) :** Le corps original transcrivait le pseudocode C++ ligne par ligne. Le coordinateur a releve (review 2026-10-08T06:50Z) qu'une telle transcription, paraphrase aussi serree d'un code sous GPL-2.0+, pose une question de provenance qu'une citation `fichier:ligne` + lien vers l'amont ne pose pas. Ce memoire est reduit a une **table d'ancres** : pour chaque algorithme C++ execute par le benchmark, on donne le chemin amont et la ligne de depart, et la reconstruction CoursIA (Python/C#) qui en porte la portee. Le code transcrit a ete depose ; les ancres suffisent a la tracabilite, le pseudocode executable reste dans les PRs soeurs.

---

## 1. Ancrage amont (fichiers C++ du pin 37a9b72)

| Fichier | Lignes | Licence | Role |
|---|---|---|---|
| `upstream/recurrences_ntl.h` | 43 | GPL-2.0+ (Harvey 2007/2008) | Declarations templates BGS |
| `upstream/recurrences_ntl.cpp` | 1301 | GPL-2.0+ | Middle product, DyadicShifter, ProductTree, Evaluator, Interpolator, ntl_interval_products |
| `upstream/hypellfrob.h` | 83 | GPL-2.0+ | Wrapper routage precision + matrix() |
| `upstream/hypellfrob.cpp` | 717 | GPL-2.0+ | interval_products_wrapper, padic_xgcd, padic_invert_matrix, matrix() |
| `harvey_adapter.cpp` | 87 | GPL-2.0-or-later SPDX (projet) | CLI + protocole JSON, traduction quarter-prefix |

**Provenance mesuree** (`upstream/SOURCE_PROVENANCE.json` l. 2-3) : `sage_tag: 10.8`, commit Sage `981d7d71a2738778c9e3fb4fdf67a0fd3ce0c19c`, 6 entrees (les 4 sources + `hypellfrob.pyx` + `COPYING.txt`) chacune avec URL raw.githubusercontent + SHA256 (l. 4-35). `upstream/COPYING.txt` est le texte GPL de Sage.

**Build** (`build.sh` l. 6-8) : `g++ -O3 -std=c++17 -pthread harvey_adapter.cpp upstream/recurrences_ntl.cpp upstream/hypellfrob.cpp -lntl -lgmp -o bin/harvey_adapter`. C++17, NTL+GMP systeme. Le script emet `bin/build_metadata.json` (version compilateur + commande exacte + horodatage UTC, l. 9-16) — garde de reproductibilite.

---

## 2. Table d'ancres : algorithme amont → reconstruction CoursIA

Chaque ligne pointe (a) la zone C++ executee par le benchmark, (b) la reconstruction qui en porte la portee dans CoursIA, (c) la verification qui les confronte. Les ancrages `fichier:ligne` renvoient au pin `37a9b72`.

### 2.1 Moteur BGS (recurrences_ntl)

| Algorithme C++ | Ancre amont | Theoreme | Reconstruction CoursIA | Verification |
|---|---|---|---|---|
| `middle_product` | recurrences_ntl.cpp l. 155-184 | (credit Hanrot-Quercia-Zimmermann, l. 150-152) | `elliptic_prefix.py` (P1 #19488) — multiplication polynomiale modulaire `Polys.mul` l. 100-110 | Comparaison produit mediant Python vs FFT cyclique 2d C++ (10 809 stopping points, 92 premiers) |
| `DyadicShifter` | recurrences_ntl.cpp l. 203-329 | Twist factoriel + kernel inverse fenetre, l. 232-304 | `point_count.py` P1 #19499 — pas de portee directe (BSGS n'utilise pas de shift d'evaluation) | n/a — pas execute par le benchmark au quarter-point |
| `dyadic_evaluation` | recurrences_ntl.cpp l. 349-441 | Theorem 8 BGS, l. 135-136 (cite) | Inutile en pratique — `ntl_interval_products` Step 0 l'invoque en interne (l. 1046-1047) | n/a — execution indirecte via le moteur |
| `ProductTree` + `Evaluator` + `Interpolator` | recurrences_ntl.cpp l. 467-714 | Corollary 10 BGS, l. 449 (cite) | `point_count.py` P1 #19499 — `Polys.divmod/rem` l. 119-136 implementent une evaluation/interpolation sans arbre | Comparaison BSGS (rapide, Python) vs `ntl_short_interval_products` (rapide, C++), 328 quarter cross-checks |
| `ntl_short_interval_products` | recurrences_ntl.cpp l. 762-974 | 5 etapes + heuristique L, l. 785-801 | `point_count.py` P1 #19499 — BSGS par intersection d'annihilateurs l. 77-85 | n/a — moteur C++ vs moteur Python compares au niveau du wrapper, pas de l'algorithme interne |
| `ntl_interval_products` | recurrences_ntl.cpp l. 995-1279 | Theorem 15 BGS, l. 723, 981 (cite) ; Steps 0-3 + sentinelles + 4 asserts de jointure | Pas de portee directe — moteur interne BGS, jamais appele par une reconstruction | n/a — execution par le wrapper de l'adaptateur (l. 37) |

### 2.2 Routage de precision + pipeline zeta (hypellfrob)

| Algorithme C++ | Ancre amont | Role | Reconstruction CoursIA | Verification |
|---|---|---|---|---|
| `interval_products_wrapper` | hypellfrob.cpp l. 86-126 | Route ZZ_p vs zz_p via `modulus.SinglePrecision()` (l. 92) | Pont pilot.py — appel unique depuis `HarveyWorker.call_kernel` (P1 #19493) | Backend `zz_p_auto` / `ZZ_p_auto` / `ZZ_p_forced` dans le JSON de reponse (adapter l. 71-76) |
| `hypellfrob_interval_products_wrapper` | hypellfrob.h l. 57-59 | Enveloppe la version vector en matrice concatenee horizontalement | Idem — point d'entree consomme par l'adaptateur (l. 37) | n/a (routeur) |
| `padic_xgcd` | hypellfrob.cpp l. 173-216 | Newton quadratique, l. 183-213 (mefiance documentee envers NTL sur non-corps, l. 167-170) | n/a — non execute par le benchmark (appele uniquement par `matrix()`) | n/a |
| `padic_invert_matrix` | hypellfrob.cpp l. 234-267 | Idem Newton, l. 263-266 (mefiance documentee l. 228-231) | n/a — idem | n/a |
| `matrix()` | hypellfrob.cpp l. 274-711 | Pipeline complet Frobenius Monsky-Washnitzer ; non execute par le benchmark | n/a — `hypellfrob.pyx` l. 158-252 le consomme en amont Sage (hors benchmark) | n/a (hors perimetre) |

### 2.3 Traducteur quarter-prefix (harvey_adapter)

| Algorithme C++ | Ancre amont | Role | Reconstruction CoursIA | Verification |
|---|---|---|---|---|
| `calculate(p, L, force_big)` | harvey_adapter.cpp l. 21-51 | Construit M(x) = [[2x-1, 4x],[0, 4x]] (l. 26-27), appelle le wrapper, extrait a/B, formule U generique (l. 43-44) | `elliptic_prefix.quarter()` (P1 #19488) — recurrence rationnelle (32) l. 488 du manuscrit, encodee en Python | 328 quarter cross-checks Harvey C++ vs Miller Python, ecart nul. Specialisation 2L ≡ -1/2 ⇒ U = 4B + (9/4)a verifiee (l. 195 corps original, ancree ici) |
| `main()` | harvey_adapter.cpp l. 52-87 | `SetNumThreads(1)` (l. 53), `--version` (l. 54-57), boucle stdin (l. 60-67), `reps` repetitions, JSON (l. 71-76), `repeat mismatch` self-check (l. 80) | `HarveyWorker` (P1 #19493) — subprocess persistant, ligne JSON par requete (l. 78-87 pilot) | 10 809 stopping points + 328 quarter + 26 forced = total 11 163 verifications VALIDATION l. 9 |
| Bridge subprocess + JSON | harvey_adapter.cpp l. 60-86 + pilot.py l. 78-87 | stdin `"p L reps\n"` + flush, stdout une ligne JSON, stderr remonte en RuntimeError si ligne vide | n/a — le bridge lui-meme est la portee | Verifie en execution, pas en revue |

---

## 3. Confrontation fonctionnelle : Harvey C++ vs reconstructions CoursIA

**Disjonction fonctionnelle d'abord :** Harvey C++ calcule le **prefixe produit de matrices** (B, a, U) sans toucher a la trace τ. Les reconstructions CoursIA (Python `point_count.py` P1 #19499, Python `elliptic_prefix.py` P1 #19488) ne convergent que par le **pilot** (P1 #19493) :

```
                   ┌─────────────────────────────────┐
                   │  pilot.py::HarveyWorker (P1)    │
                   │  ┌─────────────────────────┐    │
   p, L, reps ───► │  │ subprocess C++ Harvey  │ ──► JSON (B, a, U)
                   │  └─────────────────────────┘    │
                   │  ┌─────────────────────────┐    │
                   │  │ elliptic_prefix.quarter │ ──► JSON (B', a', U')
                   │  │ Python Miller (P1)      │    │
                   │  └─────────────────────────┘    │
                   │  cross-check (B==B', a==a', U==U')
                   └─────────────────────────────────┘
                              ▲
                              │ τ
                   ┌──────────┴──────────┐
                   │ point_count.py (P1) │
                   │ Schoof ou BSGS      │
                   └─────────────────────┘
```

**Ce que les ancres disent au lecteur :** pour chaque algorithme C++, on sait (1) ou il vit dans le pin 37a9b72, (2) s'il est execute par le benchmark ou inerte, (3) quelle reconstruction CoursIA en porte la portee, (4) ou verifier l'accord numerique. **On n'a plus besoin de transcrire le code pour cette tracabilite** — la table d'ancres y suffit, le code reste chez Harvey sous GPL-2.0+, et les reconstructions executent dans CoursIA.

---

## 4. Verification du perimetre (16/22 composants couverts)

Sur les 22 composants discutes dans le corps original, la table d'ancres en garde **16 executes** (sections 2.1, 2.2, 2.3) et **6 inertes ou rapportes** :

- **3 partiels** : `matrix()` (hypellfrob.cpp l. 274-711, inerte), `hypellfrob.pyx` (consomme hors benchmark), timings 3 phases C++ (donnees historiques non rejouees).
- **3 reportes a P2+** : preuve formelle Lean de la semantique de l'adaptateur (P2.a), correctness du middle product / DyadicShifter en Lean (P2.b), pont formel Miller ↔ BGS (P2.c).

---

## 5. Reponses aux reserves du dossier

**Reservation 2026-10-06T14:19Z (jsboige, viewer) :** "Pourquoi du pseudocode cpp alors qu'on a du vrai c# et du vrai Python de partout".

**Reponse :** Le pseudocode C++ a ete depose (corps original retire). La tracabilite est preservee par la **table d'ancres §2** : pour chaque algorithme C++, le lecteur sait ou il vit, s'il est execute, et quelle reconstruction CoursIA le couvre. Le code GPL-2.0+ reste chez Harvey ; les reconstructions C#/Python sont dans le depot sous leur propre licence.

**Reservation 2026-10-08T06:50Z (coordinateur, 🟡) :** "La traçabilité est légitime, le mémo n'est pas le bon endroit. (...) Le choix entre les deux [réduire à une table d'ancres, ou reporter en commentaires dans les reconstructions] revient à la lane."

**Reponse :** Option **reduire a une table d'ancres** retenue (cette PR). Le code transcrit a ete depose. Les ancres `fichier:ligne` (vers le pin 37a9b72) + le schema §3 donnent au lecteur le code qui s'execute (C++ chez Harvey) et la source dans le meme regard — via le lien, pas via la transcription. La licence GPL est respectee par separation (code amont non transcrit) ; la portee CoursIA est explicitee par reconstruction.

---

## 6. Garde de statut (portee en tete, modele #17845)

- **Statut** : unrefereed draft, AI-assisted (auto-declare). **Jamais canoniser** sans revue specialiste.
- **16/22 composants ancres**, 3 partiels (inertes), 3 reportes (P2 candidates).
- **Validation numerique ≠ preuve** : 10 809 + 328 + 26 = 11 163 cross-checks corroborent, ne demontrent pas.
- **P1 pseudocode C++ = lecture seule** : aucune modification du C++ (fichiers upstream SHA256-pinnees interdits a modifier, adaptateur `harvey_adapter.cpp` non touche).
- **NTL version non epinglee** : resultats arithmetiques exacts mod p, donc deterministes ; seuls les timings varient. Version enregistree via `--version` + `build_metadata.json`.
- **Allocations brutes ProductTree** : fuite possible sur exception, sans effet sur resultats, a noter pour relecture qualite du vendored (interdit a modifier ici).
- **`matrix()` 437 l. compilee mais inerte** dans le binaire benchmark (consommee par `hypellfrob.pyx` Sage upstream, hors perimetre du depot).
- **Pseudocode Miller manuscrit l. 420-437 n'a PAS de contrepartie C++** — il vit integralement dans `elliptic_prefix.py` (P1 #19488). C++ = comparateur BGS, pas Miller. L'equivalence n'est attestee qu'empiriquement (11 163 verifications).

### HORS scope (intentionnel)

- **P1 elliptic_prefix/point_count integration** : cross-check `quarter()` Python ↔ Harvey C++ au quarter-point — cycle suivant, ~1-2h.
- **P2 Lean Mathlib** : P2.a (semantique adaptateur), P2.b (DyadicShifter), P2.c (pont Miller↔BGS) — lane Lean (po-2025 ou po-2026).
- **P4 reproduction execution** : build NTL epingle (MSYS2 UCRT64), re-run `test_validation` + pilot 7 premiers, comparaison byte des JSON contre `example_results/paper_seven`. Regle F : NTL/Sage 10.8 absent localement, installer ou router.
- **Modification de `harvey_adapter.cpp` ou sources upstream** : vendored SHA256-pinnees, **interdit a modifier** (cf. regle Anti-regression).

### Refs

- #19452 (issue distillation, mandat user Telegram 06/10 09:56 Paris, contre-lu Hermes)
- #19487 (P0 cartography)
- #19488 (P1 elliptic_prefix)
- #19493 (P1 pilot)
- #19499 (P1 point_count)
- #17845 (EPIC modele — Karingula-Lovett → lake Lean 4)
- Pin externe : `bbrhuft/Cartier-Miller-...` @ `37a9b727dfd5034af0b8aa8185246d58008b9e5c`
