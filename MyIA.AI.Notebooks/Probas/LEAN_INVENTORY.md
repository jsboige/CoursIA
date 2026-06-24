# Inventaire des projets Lean 4 — `Probas`

Inventaire transverse des projets de formalisation Lean 4 sous `Probas/`, sur le modèle de
[`GameTheory/LEAN_INVENTORY.md`](../GameTheory/LEAN_INVENTORY.md) et
[`SymbolicAI/Lean/LEAN_INVENTORY.md`](../SymbolicAI/Lean/LEAN_INVENTORY.md). Source de
vérité : corps de l'Epic
[#4038](https://github.com/jsboige/CoursIA/issues/4038) + vérification `firsthand` (issue
[#4041](https://github.com/jsboige/CoursIA/issues/4041)). Colonne *sorry (production)* =
métrique CI `standalone-tactic` (les mentions prose « 0 sorry »/« sans sorry » n'entrent pas
dans ce compte ; cf.
[`lean-ci-sorry-filter`](../../.claude/projects/c--dev-CoursIA-2/memory/lean-ci-sorry-filter.md)).

## Résumé

| Lake | Toolchain | sorry (production) | Modules | Notebook câblé | Classe | Suivi |
|------|-----------|--------------------:|--------:|---------------:|--------|-------|
| `decision_theory_lean` | v4.30.0-rc2 | 5¹ | 8 (3 libs) | 0² | PEDA/REF | #4049, #4050, #4039 |
| `Infer/gittins_lean` | — | — | 0³ | 0 | SCAFFOLD | #4039 (broken stub) |
| **Total** | — | **5** | **8** | — | — | — |

¹ Les 5 `sorry` standalone-tactic de `decision_theory_lean` sont **tous** dans
`Gittins/GittinsTheorem.lean` (théorème d'optimalité de l'index de Gittins). Le fichier
documente **explicitement** en-tête : « The full proof is INTRACTABLE in the current Mathlib
(no MDP/bandit/Bellman). We state the theorem and provide sorry placeholders. » →
classification **INTRINSIC**, pas un gap pédagogique : la machinerie MDP/Bellman n'existe
pas encore dans Mathlib. Les libs `Utility` et `Coherence` sont **0 sorry**.

² Aucun notebook n'importe directement le lake `decision_theory_lean`. La série Infer
« Decision » (Infer-14 Utility-Foundations → Infer-20 Sequential) est le **companion
conceptuel** (.NET Interactive, décision/utilité) ; le câblage formel du lake comme
compagnon Lean n'est pas encore effectué.

³ `Infer/gittins_lean` n'est **pas** un lake buildable : il ne contient que
`lake-manifest.json` + `.lake/` (packages vendés), **sans** `lakefile.lean`,
`lean-toolchain`, ni aucune source `.lean`. Échafaudage abandonné. La formalisation réelle
de Gittins vit dans `decision_theory_lean/Gittins/`.

---

## Par lake

### 1. decision_theory_lean — PEDAGOGIQUE / REFERENCE (3 libs)

**Objectif** : formalisation des fondements de la théorie de la décision — utilité espérée
(vNM), cohérence probabiliste (de Finetti Dutch Book), index de Gittins (bandits manchots à
escompte géométrique).

- **Toolchain** : v4.30.0-rc2 · **Dépendance** : Mathlib4
- **libs** (`lean_lib`) : `Gittins`, `Utility`, `Coherence`
- **sorry (production)** : **5** (tous INTRINSIC dans Gittins, voir note ¹)

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

#### `Coherence/` (2 fichiers) — 0 sorry · PEDA/REF · #4050

Cohérence probabiliste au sens de de Finetti (Dutch Book). Indicateur nu
`ind A ω := if ω ∈ A then 1 else 0` dans `Basic.lean` ; Dutch Book dans `DutchBook.lean`.

- **Prouvé** : `ind_inclusion_exclusion` (keystone : l'indicateur satisfait
  inclusion-exclusion `ind (A∪B) = ind A + ind B − ind (A∩B)`), `non_additive_implies_dutch_book`
  (direction **constructive** de de Finetti : une fonction de prix non-additive admet un
  Dutch Book, witness de mises `(1,1,−1,−1)`), `coherent_on_implies_additive` (**contraposée**
  : la cohérence entraîne l'additivité).
- **OPEN (non sorry-backed)** : réciproque `coherent_iff_probability` (dualité
  programmation linéaire : cohérence ⟺ fonction de probabilité) — documentée comme jalon
  ouvert, pas un `sorry`.

#### `Gittins/` (3 fichiers) — 5 sorry (INTRINSIC) · REF · #4039

Index de Gittins pour les bandits manchots à escompte géométrique.

- **Prouvé (0 sorry)** : `Basic.lean` (types purs : `BanditArm`, `BanditInstance`,
  `Policy`, sans dépendance Mathlib) + `Discount.lean` (identités d'escompte géométrique via
  `tsum_geometric_of_lt_one`, `geometricPartialSum`).
- **INTRINSIC (5 sorry)** : `GittinsTheorem.lean` — théorème d'optimalité de l'index de
  Gittins. **Plafond atteignable honnête** : la preuve complète nécessite la machinerie
  MDP / programmation dynamique / équation de Bellman, **absente** de Mathlib à ce jour. Le
  théorème est **énoncé** avec placeholders `sorry` documentés en-tête (pas maquillés en
  résultat prouvé). Quand Mathlib gagnera un formalisme MDP, ces `sorry` deviennent la
  prochaine cible.

### 2. Infer/gittins_lean — SCAFFOLD (broken stub)

**Objectif (abandonné)** : formalisation de l'index de Gittins, prématurément ébauchée sous
`Infer/`.

- **État** : **PAS un lake buildable**. Contenu = `lake-manifest.json` (3158 o) +
  `.lake/packages/` (Mathlib vendé). **Manquent** : `lakefile.lean`, `lean-toolchain`,
  et **toute source `.lean`**.
- **Classification** : SCAFFOLD abandonné. La formalisation réelle de Gittins vit dans
  `decision_theory_lean/Gittins/` (voir ci-dessus). `gittins_lean` est un reliquat à nettoyer
  ou à supprimer (issue #4039).
- **Suivi** : #4039 (G.1 : le corps de l'issue mentionnait « 1 lake gittins » — vérification
  firsthand révèle qu'il s'agit de ce stub non-buildable ; le vrai lake est
  `decision_theory_lean`).

---

## Classes (taxonomie Epic #4038)

| Classe | Définition | Lakes |
|--------|-----------|-------|
| **PEDA/REF** | Pédagogique / formalisation de référence | decision_theory_lean |
| **SCAFFOLD** | Échafaudage partiel / non-buildable | Infer/gittins_lean (broken) |

## Notes transverses

- **Honnêteté des jalons ouverts (G.3/G.9)** : `decision_theory_lean` documente ses jalons
  non atteints (existence Herstein–Milnor, réciproque `coherent_iff_probability`, théorème
  de Gittins) **explicitement comme OPEN / INTRINSIC** — jamais masqués en résultats prouvés,
  jamais sorry-stubbés pour faire passer une métrique. La direction *sound* de chaque
  résultat est livrée 0 sorry.
- **WDAC workaround** : `decision_theory_lean` (cohorte v4.30.0-rc2) se construit en
  réutilisant le `.lake` d'un lake frère binairement compatible (wholesale
  `cp -r sibling/.lake` + `lake-manifest.json`, révision Mathlib identique). Cf.
  [`lean-wdac-olean-wholesale-copy`](../../.claude/projects/c--dev-CoursIA-2/memory/lean-wdac-olean-wholesale-copy.md).
- **Coordination finitude-derivatives (#2978)** : `decision_theory_lean` Gittins est
  coordonné avec `finiteness_lean` (#3111) — pas de chevauchement (Gittins = décision
  séquentielle, finiteness = résultat de finitude standalone).
