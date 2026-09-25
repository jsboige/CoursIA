# Inventaire des projets Lean 4 — `Probas`

Inventaire transverse des projets de formalisation Lean 4 sous `Probas/`, sur le modèle de
[`GameTheory/LEAN_INVENTORY.md`](../GameTheory/LEAN_INVENTORY.md) et
[`SymbolicAI/Lean/LEAN_INVENTORY.md`](../SymbolicAI/Lean/LEAN_INVENTORY.md). Source de
vérité : corps de l'Epic
[#4038](https://github.com/jsboige/CoursIA/issues/4038) + vérification `firsthand` (issue
[#4041](https://github.com/jsboige/CoursIA/issues/4041)). Colonne *sorry (production)* =
métrique CI `real` (commentaires strippés, `\bsorry\b`, fichiers FR hors `_en` ; bascule
#11688 — historiquement `standalone-tactic` ; les mentions prose « 0 sorry »/« sans sorry »
n'entrent pas dans ce compte).

## Résumé

| Lake | Toolchain | sorry (production) | Modules | Notebook câblé | Classe | Suivi |
|------|-----------|--------------------:|--------:|---------------:|--------|-------|
| `decision_theory_lean` | v4.32.1 | 2¹ | 13 (3 libs) | 2² | PEDA/REF | #4049, #4050, #4039 |
| `percolation_lean`³ | v4.33.0 | **0** | 6 (1 lib) | 1⁴ | PEDA/REF | #14871, #14927 |
| **Total** | — | **2** | **19** | **3** | — | — |

¹ Les 2 `sorry` (real-mode) de `decision_theory_lean` sont **tous** dans
`Gittins/GittinsTheorem.lean` (théorème d'optimalité de l'index de Gittins — l'opérateur
de valeur `V := sorry` et la preuve d'inégalité, tous deux INTRINSIC). Le fichier documente
**explicitement** en-tête : la preuve complète est INTRACTABLE dans l'état actuel de
Mathlib (pas de machinerie MDP/bandit/Bellman) → classification **INTRINSIC**, pas un gap
pédagogique. Historique : 5 sorry à la création, déchargés à **2** (baseline CI suivie,
`lean-decision-theory.yml` real-mode baseline 2). Les libs `Utility` et `Coherence` sont
**0 sorry**.

² Deux notebooks câblés sous `Probas/DecisionTheory/DecInfer/` : **DecInfer-02**
(Lean Expected Utility) et **DecInfer-09** (Lean Gittins — preuves en cellules Lean).
La série Infer « Decision » (.NET Interactive) reste le companion conceptuel
utilité/décision.

³ `percolation_lean` vit sous `Applications/Percolation/percolation_lean/` (créé
directement là, #14927 — absent de cet inventaire jusqu'ici). Les fichiers `.lean`, au
comptage de l'instrument canonique, (`count_code_sorry.py --lake …` : `files: 13`,
`distinct_code_sorry: 0`, `naive_sorry: 0`, aucun vacuous) — soit les modules FR (5 imbriqués
+ l'agrégateur racine `Percolation.lean`), 6 miroirs `_en` (5 imbriqués + `Percolation_en`),
et le `lakefile.lean`. La CI dédiée `lean-percolation.yml` porte
`sorry-baseline: "0"` / `sorry-filter-mode: real` (dernier run `success`
2026-09-24T23:31:21Z).

⁴ Un notebook câblé : **`Applications/Percolation/Percolation-Lean.ipynb`** (compagnon
exécutable du lake — cf. [`Applications/Percolation/README.md`](Applications/Percolation/README.md)).

*(Historique : `Infer/gittins_lean`, stub non-buildable documenté ici autrefois, a été
**supprimé du dépôt** — la formalisation réelle de Gittins vit dans
`decision_theory_lean/Gittins/`.)*

---

## Par lake

### 1. decision_theory_lean — PEDAGOGIQUE / REFERENCE (3 libs)

**Objectif** : formalisation des fondements de la théorie de la décision — utilité espérée
(vNM), cohérence probabiliste (de Finetti Dutch Book), index de Gittins (bandits manchots à
escompte géométrique).

- **Toolchain** : v4.32.1 · **Dépendance** : Mathlib4
- **libs** (`lean_lib`) : `Gittins`, `Utility`, `Coherence` (modules FR et miroirs
  `_en`)
- **sorry (production)** : **2** (tous INTRINSIC dans Gittins, voir note ¹). CI verte sur
  main (`lean-decision-theory.yml`, dernier run 2026-08-26).

#### `Utility/` (3 fichiers) — 0 sorry · PEDA/REF · #4049

Théorie de l'utilité espérée (von Neumann–Morgenstern). Axiomes de rationalité
(`IsComplete`, `IsTransitive`, `IsIndependent`, `IsContinuous`) dans `Axioms.lean` ;
loteries, espérance, mixage dans `Basic.lean` (lemmes `expectation_mix`,
`expectation_add`, `expectation_smul`, `expectation_const`, `expectation_affine` — tous
prouvés) ; théorèmes de représentation dans `Representation.lean`.

- **Prouvé** : `expected_utility_rep_is_rational` (direction **sound** : une représentation
  EU implique la rationalité VNM), `affine_rep_is_rep` (**stabilité affine** : une
  transformation affine positive d'une utilité EU reste une représentation), +
  `rep_complete`/`rep_transitive`/`rep_independent`/`rep_continuous`.
- **OPEN (non sorry-backed)** : direction **existence** (Herstein–Milnor 1953 :
  rationalité ⟹ représentation EU) — documentée honnêtement comme jalon ouvert dans
  l'en-tête du fichier, **pas** un `sorry`. La lib livre la direction sound entièrement
  sorry-free.

#### `Coherence/` (4 fichiers) — 0 sorry · PEDA/REF · #4050

Cohérence probabiliste au sens de de Finetti (Dutch Book). Indicateur nu
`ind A ω := if ω ∈ A then 1 else 0` dans `Basic.lean` ; Dutch Book dans `DutchBook.lean` ;
lecture **actuariale** dans `Premium.lean` ; caractérisation **probabilité** dans
`Probability.lean`.

- **Prouvé (DutchBook)** : `ind_inclusion_exclusion` (keystone : l'indicateur satisfait
  inclusion-exclusion `ind (A∪B) = ind A + ind B − ind (A∩B)`), `non_additive_implies_dutch_book`
  (direction **constructive** de de Finetti : une fonction de prix non-additive admet un
  Dutch Book, witness de mises `(1,1,−1,−1)`), `coherent_on_implies_additive` (**contraposée**
  : la cohérence entraîne l'additivité).
- **Prouvé (Premium)** : `coherent_on_iff_no_sure_profit` (changement de côté du comptoir :
  un barème de primes est cohérent ssi aucun profit sûr côté assureur),
  `incoherent_premium_sure_insurer_loss` (barème incohérent ⟹ perte sûre de l'assureur),
  `coherent_premium_disjoint_additive` (règle de segmentation : additivité sur risques
  disjoints), `pure_premium_tariff_unarbitrageable` (tarification prime pure non
  arbitrageable).
- **Prouvé (Probability)** : `single_coherent_iff_prob_bounds` — le jalon
  `coherent_iff_probability` **livré en cadre fini mono-livret** : une fonction de prix
  est exploitable par un Dutch Book à un ticket ssi elle viole une borne de probabilité
  (non-négativité, majoration par 1, `q ∅ = 0`, `q univ = 1`) ; les quatre directions
  constructives (`single_dutch_book_of_neg/_high/_pos_empty/_univ_lt`) +
  `priceFromWeights_coherent_on`.
- **OPEN (non sorry-backed)** : la caractérisation **complète à quatre tickets**
  (dualité programmation linéaire sur livrets multi-tickets) — le cadre mono-livret fini
  est livré ci-dessus, pas un `sorry`.

#### `Gittins/` (3 fichiers) — 2 sorry (INTRINSIC) · REF · #4039

Index de Gittins pour les bandits manchots à escompte géométrique.

- **Prouvé (0 sorry)** : `Basic.lean` (types purs : `BanditArm`, `BanditInstance`,
  `Policy`, sans dépendance Mathlib) + `Discount.lean` (identités d'escompte géométrique via
  `tsum_geometric_of_lt_one`, `geometricPartialSum`).
- **INTRINSIC (2 sorry)** : `GittinsTheorem.lean` — théorème d'optimalité de l'index de
  Gittins. **Plafond atteignable honnête** : la preuve complète nécessite la machinerie
  MDP / programmation dynamique / équation de Bellman, **absente** de Mathlib à ce jour. Le
  théorème est **énoncé** avec placeholders `sorry` documentés en-tête (pas maquillés en
  résultat prouvé). Quand Mathlib gagnera un formalisme MDP, ces `sorry` deviennent la
  prochaine cible. *(Historique : 5 sorry à la création, décharge partielle à 2 — l'en-tête
  du fichier documente « ses deux sites `sorry`.)*

---

### 2. percolation_lean — PEDAGOGIQUE / REFERENCE (1 lib)

**Objectif** : formalisation du noyau fini de la percolation de liens sur tore fini
(Diskin–Easo–Radhakrishnan–Sudakov–Tassion, arXiv:2603.03257) — support Lean de
l'application Percolation.

- **Toolchain** : v4.33.0 · **Dépendance** : Mathlib4 (pin `db584cd6`)
- **lib** (`lean_lib`) : `Percolation` (globs `Percolation.*` + `Percolation_en`, convention
  i18n #4980 — même template que `decision_theory_lean`)
- **sorry (production)** : **0** — lake entièrement prouvé (instrument canonique :
  `distinct_code_sorry: 0` ; CI `lean-percolation.yml` baseline 0 real-mode, run vert).
- **Modules FR** (5 imbriqués + agrégateur racine, docstrings citées) :
  - `Basic.lean` — module d'amorce du noyau fini (définitions de base) ;
  - `Connectivity.lean` — connexité (tranche 2) ;
  - `Components.lean` — composantes et frontière (tranche 3) ;
  - `Examples.lean` — un exemple calculable (tranche 3, acceptation 3) ;
  - `Boundary.lean` — frontière isopérimétrique (tranche 4, le plus riche : 17
    théorèmes/lemmes au grep) ;
  - `Percolation.lean` — agrégateur racine.
- **Notebook câblé** : `Applications/Percolation/Percolation-Lean.ipynb` (compagnon
  exécutable, cf. #14871 / #14927).

---

## Classes (taxonomie Epic #4038)

| Classe | Définition | Lakes |
|--------|-----------|-------|
| **PEDA/REF** | Pédagogique / formalisation de référence | decision_theory_lean, percolation_lean |

*(La classe SCAFFOLD n'a plus de représentant : `Infer/gittins_lean` — stub non-buildable
documenté historiquement — a été supprimé du dépôt.)*

## Notes transverses

- **Couverture** : cet inventaire couvre les **deux** lakes de `Probas/` —
  `decision_theory_lean` (racine série) et `percolation_lean`
  (`Applications/Percolation/`, intégré ici par P3 de #14873 ; le Total historique
  ne comptait pas `percolation_lean` (créé après lui, #14927)).
- **Honnêteté des jalons ouverts (G.3/G.9)** : `decision_theory_lean` documente ses jalons
  non atteints (existence Herstein–Milnor, caractérisation multi-tickets complète,
  théorème de Gittins) **explicitement comme OPEN / INTRINSIC** — jamais masqués en
  résultats prouvés, jamais sorry-stubbés pour faire passer une métrique. La direction
  *sound* de chaque résultat est livrée 0 sorry (et le jalon
  `coherent_iff_probability` est livré en cadre mono-livret fini, `Probability.lean`).
- **WDAC workaround** (historique, cohorte d'alors v4.30.0-rc2) : `decision_theory_lean`
  se construisait en réutilisant le `.lake` d'un lake frère binairement compatible
  (wholesale `cp -r sibling/.lake` + `lake-manifest.json`, révision Mathlib identique). Cf.
  `lean-wdac-olean-wholesale-copy`.
- **CI** : `.github/workflows/lean-decision-theory.yml` (`sorry-filter-mode: real`,
  baseline `"2"` — historiquement `standalone-tactic` baseline 4, corrigé par #11688).
- **Coordination finitude-derivatives (#2978)** : `decision_theory_lean` Gittins est
  coordonné avec `finiteness_lean` (#3111) — pas de chevauchement (Gittins = décision
  séquentielle, finiteness = résultat de finitude standalone).
