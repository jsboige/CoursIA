# iit_lean — intégration par coupes, proxy relationnel (Phase 1)

Premier lake Lean de la série IIT. Sous-grain de l'Epic Aaronson
[#16781](https://github.com/jsboige/CoursIA/issues/16781) (veine 5, moitié
formelle), livré par [#18599](https://github.com/jsboige/CoursIA/issues/18599).

## Ce que le lake formalise

Un **proxy relationnel de décomposition par coupe** — pas une version de Φ :

- un système déterministe à `n` éléments est une fonction d'états
  (`System n := State n → State n`, `State n := Fin n → Bool`) ;
- une **coupe** non triviale (`Cut n`) partage les éléments en deux côtés non vides ;
- une coupe est **indépendante** si tout couple de motifs réalisables séparément
  est réalisable ensemble (`cutIndep`) ;
- un système est **décomposable** s'il existe une coupe indépendante, **intégré** sinon.

La critique d'Aaronson (« construire un objet à intégration énorme et à
comportement trivial ») devient un **couple de théorèmes** :

| Théorème | Énoncé |
|---|---|
| `cutIndep_of_sides_independent` (+ alias `product_decomposable`) | un système dont les deux moitiés évoluent indépendamment est décomposable — témoin constructif (mélange des entrées) |
| `broadcast_integrated` | le système *broadcast-parité* est intégré pour **toute** coupe |
| `broadcast_two_cycle` (+ alias `broadcast_trivial_dynamics`) | toute orbite du broadcast atteint un point fixe en deux pas — comportement trivial |

**Grade honnête** : le proxy mesure la décomposition déterministe de l'image.
Il ne capture ni l'information effective sous perturbation, ni la partition
minimale au sens MIP, ni une valeur numérique de Φ (Phase 2 renvoyée). La
source de la critique est un billet de blog (2014), pas une publication : ce
lake **crée** l'objet formel, il n'en est pas une transcription.

## Build

**Sans dépendance Mathlib** (patron `tegmark_muh_lean`) : core `Fin`, `Bool`,
`xor` et des témoins constructifs suffisent — le lake se construit en
secondes, sans `lake exe cache get`.

```bash
lake build   # WSL : leanprover/lean4:v4.33.0 (lean-toolchain)
```

## Convention i18n (#4980)

`IIT/Integration.lean` (docstrings FR) et `IIT/Integration_en.lean`
(namespace `IIT_en`, docstrings EN) forment une paire *sibling* pattern A :
byte-identiques hors docstrings, vérifiées par
`scripts/lean/check_i18n_siblings.py`.

## CI

Lake enregistré dans `scripts/lean/ci_lakes.json` (`sorry-baseline: "0"`,
`sorry-filter-mode: "real"`), déclenché par les filtres de chemins de
`.github/workflows/lean-ci-matrix.yml` — voir
[`LEAN_INVENTORY.md`](../LEAN_INVENTORY.md) pour l'inventaire des lakes.
