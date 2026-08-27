# Inventaire des projets Lean 4 — `SymbolicAI/Lean`

Inventaire transverse de tous les projets de formalisation Lean 4 sous `SymbolicAI/Lean/`,
sur le modèle de [`GameTheory/LEAN_INVENTORY.md`](../../GameTheory/LEAN_INVENTORY.md).
Source de vérité : corps de l'Epic
[#4038](https://github.com/jsboige/CoursIA/issues/4038) + vérification `firsthand` (issue
[#4041](https://github.com/jsboige/CoursIA/issues/4041)). Colonne *sorry (production)* =
métrique CI `standalone-tactic` via `python scripts/lean/count_code_sorry.py --json`
(champ `distinct_code_sorry` après strip des docstrings `-- commentaires` et
`/-! -/`, cf `lean-ci-sorry-filter` et `anti-regression.md` §Lean).

Mesure prise sur `origin/main` au cycle **c.577 (2026-08-27)** — post-convergence
v4.32.1 (#13121, passe 1 audit CoursIA).

## Résumé

| Lake | Toolchain | sorry (production) | Modules | Notebook câblé | Classe | Suivi |
|------|-----------|--------------------:|--------:|---------------:|--------|-------|
| `grothendieck_lean` | v4.32.1 | 0 | 59 (59 FR + 59 EN pairs, voir lake détail) | 4 | REF | #2159, #1646 |
| `conway_lean` | v4.32.1 | 1 | 36 (32 pairs + 4 EN-only) | 24 | PEDA | #1453, #1651, #2162 |
| `knot_lean` | v4.32.1 | 12 | 8 (7 pairs + 1 EN-only) | 2 | PEDA/REF | #2874, #3003 |
| `finiteness_lean` | v4.32.1 | 0 | 2 (1 pair substance + 1 umbrella FR) | 2 | REF | #3111 |
| `sensitivity_lean` | v4.32.1 | 0 | 5 (4 pairs + 1 umbrella) | 2 | PEDA/REF | famille calibration |
| `calibration_lean` | v4.32.1 | 0 | 4 (3 pairs + 1 Nash sibling) | 0 | HARNESS | #1764 |
| `galois_lean` | v4.32.1 | 0 | 1 (FR seul, M₂₃ vendored) | 1 | REF | PR #12875 (c.575) |
| `mimo_lean` | v4.32.1 | 0 | 6 (6 pairs FR+EN, voir lakefile globs) | 1 | REF | #10984, #11148 |
| `mathlib_examples` | v4.32.1 | 0 | 2 (1 pair + 1 umbrella) | 0 | REF | référence |
| **Total** | — | **13** | **124 paires/EN-only** | — | — | — |

**Notes sur le décompte** :

- *Modules* = nombre de fichiers `.lean` effectivement compilés (hors
  `lakefile.lean`/`lake-manifest.json` aglistiques), miroir du `find … *.lean` de
  [`I18N_INVENTORY.md`](I18N_INVENTORY.md) § « Inventaire brut ». Les `_en`
  siblings sont comptés comme paires, pas doublés (convention #4980 sibling pair).
- *sorry (production)* = `distinct_code_sorry` (déjà dédoublonné
  FR↔EN par l'instrument canonique). C'est la valeur **vraie** ; `naive_sorry`
  (sur-compte prose) et `code_sorry` (avec doublons FR/EN) sont **non-canoniques**
  pour ce tableau. Justification détaillée : `anti-regression.md` §Lean
  (« Compter les `sorry` — un seul instrument »).
- L'ancien compte `conway_lean = 4` (verbatim de la note ¹) datait du **monolithe
  pré-split** (7082 lignes, 4 cibles prover `p4_*`/`p5_*`). Post-split
  (`Conway/Life/HashlifeCorrectness.lean` séparé du monolithe, PR #2793-2797), le
  compte canonique est **1** distinct (`hashlife_correct_margin`) : les
  `p4_*`/`p5_*` cibles sont **soit prouvées** (post #9883/#9884) soit **repliées**
  dans le sous-fichier (voir `conway_lean/README.md` § « État honnête du verrou
  HashlifeCorrectness »).
- L'ancien compte `knot_lean = 3` datait d'une mesure pre-#11227 ; le corridor
  Reidemeister #8696 (c.8162-c.8169) a fermé des cibles additionnelles — le
  canonique actuel est **12** distincts. Voir `knot_lean/README.md` § « État des
  sorries » pour la ventilation par fichier.

---

## Par lake

### 1. grothendieck_lean — REFERENCE (recherche)

**Objectif** : formalisation étendue de résultats à la Grothendieck (topos, sites,
faisceaux, topologie dense, foncteur constant, lemme d'Yoneda, conservativité).

- **Toolchain** : v4.32.1 · **Dépendance** : Mathlib4
- **Modules** : `Grothendieck/` (58 fichiers FR + 58 fichiers EN siblings =
  116 `.lean`, plus umbrella `Grothendieck.lean` + lakefile aglistique → **59 paires
  + 1 umbrella**) — instrumentation canonique : 118 fichiers `.lean` total
  (`find … *.lean`, voir `I18N_INVENTORY.md`).
- **sorry (production)** : **0** — entièrement prouvé à la création (« All `sorry`s
  eliminated at creation »). Build SUCCESS.
- **i18n** : 57/58 pairs byte-identical · 1 consumer-pattern (cf.
  `I18N_INVENTORY.md` § grothendieck_lean) · 0 drift, 0 orphan.
- **Notebook câblé** : 4 notebooks (série SymbolicAI/Lean).
- **Suivi** : Epic #1646, #2159 (Phase 6-8).

### 2. conway_lean — PEDAGOGIQUE (hommage Conway)

**Objectif** : hommage à John H. Conway — Doomsday, FRACTRAN, Look-and-Say, Nim, Angel,
Game of Life / Hashlife.

- **Toolchain** : v4.32.1 · **Dépendance** : Mathlib4
- **Modules** : `Conway/` + `Conway/Life/` + umbrella + `patterns/` + `scripts/` —
  72 fichiers `.lean` total instrument canonique (32 pairs FR+EN + 4 fichiers
  EN-only ou FR-only recherche). Détail voir `conway_lean/README.md` § « Modules ».
- **sorry (production)** : **1** distinct (`hashlife_correct_margin` —
  `Conway/Life/HashlifeMarginFragment.lean` L136) — cible P5 du prouveur (Epic
  #1453, #2162). **Note historique** : ce compte remplace l'ancien « 4 »
  (monolithe pré-split) qui datait des cibles P4/P5 avant le split Hashlife en
  sous-fichiers (PR #2793-2797). Les `p4_succ_membership`/`p4_half_steps_compose`/
  `p5_inductive_step`/`p5_large_n_jump` sont soit prouvés (post #9883/#9884), soit
  re-cités dans le fichier de marge (cf. « État honnête du verrou
  HashlifeCorrectness »).
- **i18n** : 32/32 pairs byte-identical · 0 drift, 0 orphan, 0 unbuilt (cf.
  `I18N_INVENTORY.md` § conway_lean).
- **Notebook câblé** : 24 notebooks (série Conway la plus câblée).
- **Suivi** : Epic #1453, #1651 ; Conway P5 (#2162) = research-HOLD.

### 3. knot_lean — PEDAGOGIQUE / REFERENCE (research-HOLD)

**Objectif** : théorie des nœuds — tricolorabilité, polynôme d'Alexander, mutants, slicing,
théorème de Conway.

- **Toolchain** : v4.32.1 · **Dépendance** : Mathlib4
- **Modules** : `Knots/` + umbrella + `MathlibPrerequisites.lean` —
  15 fichiers `.lean` total (7 pairs FR+EN + 1 EN-only). Voir
  `knot_lean/README.md` § « Modules ».
- **sorry (production)** : **12** distincts (`Conway.lean` 8 + `Invariant.lean` 2 +
  `Lidman.lean` 2) — corridor Reidemeister #8696 (c.8162-c.8169) ; pas un gap
  pédagogique, cibles de recherche PL hors Mathlib actuel. Le compte inclut les
  Fox/col du backward transfer, déchargés par #11227 (`absurd` sur kink
  all-distinct).
- **i18n** : 7/7 pairs byte-identical · 0 drift, 0 orphan.
- **Notebook câblé** : 2 notebooks.
- **Suivi** : #2874 (mandate-C trio MERGED #3997/#3999/#4003), #3003 (Path B GF(3) SHIPPED).

### 4. finiteness_lean — REFERENCE

**Objectif** : formalisation compacte du théorème de finitude de Brzozowski (1964).

- **Toolchain** : v4.32.1 · **Dépendance** : **aucune** (Lean core seul — autonome)
- **Modules** : `Finiteness/Basic.lean` + `Finiteness/Basic_en.lean` + umbrella
  `Finiteness.lean` = 1 pair substance + 1 umbrella bilingue-inline. 4 fichiers
  `.lean` total.
- **sorry (production)** : **0**. Build SUCCESS.
- **i18n** : 1/1 pair byte-identical · 0 drift.
- **Notebook câblé** : 2 notebooks (`Lean-14-Finiteness-Derivatives.ipynb`,
  `Lean-14b-Finiteness-Lean-Companion.ipynb`).
- **Suivi** : #3111 (MERGED), #2978 Epic finitude-derivatives.

### 5. sensitivity_lean — PEDAGOGIQUE / REFERENCE

**Objectif** : analyse de sensibilité / calibration (proche de la famille calibration).

- **Toolchain** : v4.32.1 · **Dépendance** : Mathlib4
- **Modules** : `Sensitivity/` (4 fichiers FR + 4 fichiers EN siblings + umbrella +
  `NOTICE.md`) — 5 fichiers `.lean` pairs + 1 umbrella.
- **sorry (production)** : **0**. Build SUCCESS.
- **i18n** : 5/5 pairs byte-identical · 0 drift.
- **Notebook câblé** : 2 notebooks.
- **Suivi** : famille calibration.

### 6. calibration_lean — HARNESS (prover calibration)

**Objectif** : composant du harnais de calibration du prouveur (cibles de test pour le
prover, déplacé depuis GameTheory).

- **Toolchain** : v4.32.1 · **Dépendance** : Mathlib4
- **Modules** : `Calibration/` (4 fichiers FR + 4 fichiers EN siblings + umbrella) —
  9 fichiers `.lean` total (3 pairs + 1 Nash pair + 1 umbrella).
- **sorry (production)** : **0** (les `· sorry` inline de `Calibration/Nash.lean` sont un
  fixture de test intentionnel — pas du code de production, donc
  *sorry (production) = 0*). Le harnais doit gérer un *sorry-increase* 1→2 sans
  régression.
- **i18n** : 4/4 pairs byte-identical · 0 drift.
- **Notebook câblé** : 0 (composant harnais, pas pédagogique).
- **Suivi** : #1764.

### 7. galois_lean — REFERENCE (M₂₃ groupe de Galois)

**Objectif** : couche de preuve pour le notebook **Lean-23** — vérification que M₂₃
est un groupe de Galois sur ℚ (Poonen et al., préprint
[arXiv:2608.08538](https://arxiv.org/abs/2608.08538)).

- **Toolchain** : v4.32.1 · **Dépendance** : Mathlib4 (rev v4.32.1 résolu)
- **Modules** : `Galois/M23Lean4Web.lean` (8115 lignes, single-file vendored) +
  `Galois.lean` agrégateur racine — 3 fichiers `.lean` total. **Pas de sibling `_en`** :
  le lake est single-source vendored depuis l'amont (`KitaKen1/finite-simple-groups-lean`,
  Apache-2.0), convention i18n = **pas de sibling pour les fichiers aglistiques**
  d'origine (cf. `I18N_INVENTORY.md` § hors scope).
- **sorry (production)** : **0** (mode `real`, comptage Lean-aware) — 0 `sorry` tactique,
  0 `native_decide`, 0 `axiom` déclaré.
- **Axiomes** : `#print axioms Sporadic.card_M23` / `simple_M23` →
  `{propext, Classical.choice, Quot.sound}` = whitelist §B.
- **Build** : `lake build Galois` SUCCESS via agrégateur racine (pattern conway_lean
  bare + `import Galois.M23Lean4Web`, contourne le quirk v4.32.1 sur `globs`).
- **Notebook câblé** : `Lean-23-Galois-Probleme-Inverse-M23.ipynb` (vérification
  indépendante sympy du polynôme de degré 23 ; realisation galoisienne non
  formalisée car Belyi absent de Mathlib — voir `sota-not-workaround.md`).
- **Suivi** : PR #12875 (livré c.575).

### 8. mimo_lean — REFERENCE (détection MIMO par flips)

**Objectif** : port formel de l'algorithme de détection MIMO par flips de coordonnées
(Papailiopoulos, 2026 — issue #10984). Module compagnon **Lean-22b-MIMO-Converse-Native.ipynb**.

- **Toolchain** : v4.32.1 · **Dépendances** : Mathlib4 (v4.32.1 résolu) + SLT
  (YuanheZ/lean-stat-learning-theory, pin `d0f506f0a695018265dccb33bcb05e2f5ca1c876`)
- **Modules** : `Descent`, `Objective`, `Lmmse`, `Converse`, `Bridge`, `NormTails` —
  6 pairs FR+EN (12 fichiers `.lean`) + 1 lakefile aglistique. 13 fichiers `.lean`
  total.
- **sorry (production)** : **0**. Build SUCCESS.
- **i18n** : 6/6 pairs byte-identical · 0 drift.
- **Notebook câblé** : `Lean-22b-MIMO-Converse-Native.ipynb` (visite 35
  déclarations, `#check` + `#print axioms`).
- **Suivi** : #10984 (livré c.576, PR #13241 — voir `mimo_lean/README.md` pour la
  table exhaustive libs+siblings+statut), #11148 (grains 4-5).

### 9. mathlib_examples — REFERENCE

**Objectif** : exemples de référence illustrant l'usage de Mathlib.

- **Toolchain** : v4.32.1 · **Dépendance** : Mathlib4
- **Modules** : `MathLibExamples/Basic.lean` + `MathLibExamples/Basic_en.lean` +
  umbrella `MathLibExamples.lean` — 1 pair substance + 1 umbrella.
- **sorry (production)** : **0**. Build SUCCESS.
- **i18n** : 1/1 pair byte-identical · 0 drift.
- **Notebook câblé** : 0 (référence).
- **Suivi** : référence (pas d'issue dédiée).

---

## Classes (taxonomie Epic #4038)

| Classe | Définition | Lakes |
|--------|-----------|-------|
| **PEDA** | Pédagogique (enseigne un concept, destiné aux étudiants, notebooks compagnons) | conway_lean, knot_lean, sensitivity_lean |
| **REF** | Formalisation de référence / recherche (pas directement pédagogique) | grothendieck_lean, finiteness_lean, mathlib_examples, galois_lean, mimo_lean |
| **HARNESS** | Composant de harnais (prover calibration / test fixture) | calibration_lean |
| **SCAFFOLD** | Échafaudage partiel / en cours | _(aucun — tous sont buildables)_ |

## Notes transverses

- **Cohorte v4.32.1 unifiée** : tous les lakes SymbolicAI/Lean ont migré à
  `leanprover/lean4:v4.32.1` (cf. `lean-toolchain` file + lakefile pin
  `mathlib4 @ v4.32.1`). La cohorte antérieure `v4.31.0-rc1` (mentionnée dans
  les versions précédentes de cet inventaire) est **entièrement remplacée** par
  la convergence 4.32.1 de #13121 (passe 1 audit CoursIA). Le tableau ci-dessus
  reflète l'état **post-convergence** — toute référence à `v4.31.0-rc1` dans
  les READMEs de lake (conway_lean, galois_lean) ou dans le `LEAN_INVENTORY.md`
  historique constitue un **drift documentaire** à corriger. Cible PR pilote
  #13211.
- **WDAC workaround** (Windows Defender Application Control bloque `clang.exe` +
  `lake exe cache get`) : tous les lakes se construisent en réutilisant le
  `.lake` d'un lake frère binairement compatible (wholesale `cp -r sibling/.lake`
  + `lake-manifest.json`), à condition d'une révision Mathlib identique. Cohorte
  v4.32.1 (calibration, conway, finiteness, galois, grothendieck, knot,
  mathlib_examples, mimo, sensitivity, kelly, planning, perceptron, astar, erc20,
  argumentation, minimax, sudoku, cooperative) ; cohorte v4.30.0-rc2
  (decision_theory — pin Mathlib cf. lakefile.lean).
- **`SymbolicAI/Lean/examples/llm_assisted_proof.lean`** (2 `sorry`) est un *exemple
  pédagogique* (non production) — non compté dans le tableau ci-dessus.
- **`finiteness_lean`** est également référencé depuis l'Epic finitude-derivatives
  (#2978, coordination vérifiée avec `decision_theory_lean` Gittins — pas de
  chevauchement).
- **`galois_lean`** : la **réalisation galoisienne** (M₂₃ = groupe de Galois sur
  ℚ) est **citée, non formalisée** — Belyi absent de Mathlib, Magma propriétaire
  requis pour l'identification `23T5 = M23`. La vérification indépendante du
  polynôme de degré 23 (degré, irréductibilité, discriminant) est exécutable
  dans le notebook compagnon via sympy.