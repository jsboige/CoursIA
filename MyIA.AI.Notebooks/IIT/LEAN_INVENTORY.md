# Inventaire des projets Lean 4 — `IIT`

Inventaire transverse des projets de formalisation Lean 4 sous `IIT/`, sur le modèle de
[`GameTheory/LEAN_INVENTORY.md`](../GameTheory/LEAN_INVENTORY.md) et
[`Sudoku/LEAN_INVENTORY.md`](../Sudoku/LEAN_INVENTORY.md). Source de vérité : gel de la
Phase 1 [#18599](https://github.com/jsboige/CoursIA/issues/18599) (Epic Aaronson
[#16781](https://github.com/jsboige/CoursIA/issues/16781), veine 5, moitié formelle),
escalier [#20414](https://github.com/jsboige/CoursIA/issues/20414) + vérification
`firsthand`. Colonne *sorry (production)* = métrique CI `real` mesurée avec l'instrument
canonique `scripts/lean/count_code_sorry.py --json` (champ `distinct_code_sorry`, jamais
`grep -c sorry`).

## Résumé

| Lake | Toolchain | sorry (production) | Modules | Notebooks câblés | Classe | Suivi |
|------|-----------|--------------------:|--------:|-----------------:|--------|-------|
| `iit_lean` | v4.33.0 | 0 | 3 | 4 | PEDA/FORMAL | #18599, #20414 |
| **Total** | — | **0** | **3** | **4** | — | — |

Notebooks câblés (kernel `lean4-wsl`, exécution directe du lake) :
**IIT-07** (marche 1, coupes et décomposabilité), **IIT-08** et **IIT-08b** (marche 2,
parité de bout en bout et théorèmes B/C), **IIT-09** (marche 3, capstone du couple B/C).
Renvoi croisé sans exécution : **IIT-06-L** (notebook Python, cite le lake en conclusion).

---

## Par lake

### iit_lean — PEDAGOGIQUE / FORMALISATION

**Objectif** : le **proxy relationnel de décomposition par coupe** figé dans #18599 —
pas une version de Φ. Un système déterministe sur `n` bits (`State n := Fin n → Bool`),
une coupe non triviale, l'indépendance d'une coupe (`cutIndep`), et le couple qui fait de
la critique d'Aaronson un objet formel : les systèmes à dynamiques latérales
indépendantes sont décomposables (`cutIndep_of_sides_independent`), le broadcast-parité
est intégré pour toute coupe (`broadcast_integrated`) avec dynamique triviale
(`broadcast_two_cycle`, point fixe en deux pas).

**Toolchain** : v4.33.0 | **Dépendances** : aucune — sans Mathlib (patron
`tegmark_muh_lean`) : core `Fin`, `Bool`, `xor` et témoins constructifs ; le lake se
construit en secondes, sans `lake exe cache get`.

| Module | sorry | Contenu |
|--------|------:|---------|
| `IIT/Integration.lean` (FR) | 0 | defs `projT`/`projF`/`cutIndep`/`decomposable`/`integrated`/`parity`/`broadcast` ; théorèmes `cutIndep_of_sides_independent` (+ alias `product_decomposable`), `broadcast_integrated`, `broadcast_two_cycle` (+ alias `broadcast_trivial_dynamics`), lemmes `parity_*` (tout-faux, tout-vrai, bit unique, constante) |
| `IIT/Integration_en.lean` (EN) | 0 | jumeau i18n pattern A (#4980) : namespace `IIT_en`, docstrings seules diffèrent |
| `IIT.lean` (racine) | 0 | agrégateur |

**Grade honnête** (porté par le [README du lake](iit_lean/README.md)) : le proxy mesure la
décomposition déterministe de l'image — ni l'information effective sous perturbation, ni
la partition minimale au sens MIP, ni une valeur numérique de Φ (Phase 2 renvoyée). La
source de la critique est un billet de blog (2014), pas une publication : le lake **crée**
l'objet formel, il n'en est pas une transcription.

**i18n** : paire sibling pattern A vérifiée byte-identique par
`scripts/lean/check_i18n_siblings.py` (1/1 OK, mesuré le 2026-10-25).

**CI** : lake enregistré dans `scripts/lean/ci_lakes.json` (`sorry-baseline: "0"`,
`sorry-filter-mode: "real"`), déclenché par les filtres de chemins de
`.github/workflows/lean-ci-matrix.yml`.

**Réconciliation** : mesuré le 2026-10-25 contre `main` (`distinct_code_sorry = 0` sur
l'ensemble du lake, aucune preuve vacuous) ; relocalisé dans sa série consommatrice par #22008,
carnets présentés dans le README de la série par #22002.
