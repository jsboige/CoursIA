# combinators_lean — confluence du système S/K/I

Pli 4 de l'Epic Origami [#19742](https://github.com/jsboige/CoursIA/issues/19742)
(grain B, [#25061](https://github.com/jsboige/CoursIA/issues/25061)) : preuve
formelle de la confluence (Church-Rosser) de la réduction des combinateurs
S, K, I, **par invocation de l'organe Mathlib** — la règle organ-first du dépôt
impose de nommer l'organe existant avant toute réimplémentation.

## L'organe invoqué

`Relation.church_rosser` — [`Mathlib/Logic/Relation.lean` l.896 au pin
`v4.33.0`](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/Logic/Relation.lean#L896)
(rev `db584cd6d46c92f209a44c0f1c829460d327499d`, épinglé dans
`lake-manifest.json`). Forme de Hindley–Rosen : si une relation intermédiaire
`r` satisfait le losange local (deux pas depuis `a` se rejoignent), alors sa
clôture réflexive-transitive est confluente.

## Architecture de la preuve

Réduction de style Tait–Martin-Löf, sans lieurs — ce que S/K/I rend nettement
plus simple que le lambda-calcul :

| Module | Contenu |
|---|---|
| `Combinators/Term.lean` | Syntaxe (`Term`, application infixe `⊙`), taille, réduction à un pas `step` (fermeture contextuelle de S/K/I) |
| `Combinators/Parallel.lean` | Réduction parallèle `par`, lemmes de forme (`par_atom`, `par_Shead`, `par_Khead`, `par_S2`), **lemme du losange** par induction forte sur la taille |
| `Combinators/Confluence.lean` | Ponts `step ⊆ par ⊆ step*`, théorème **`confluence`** (organe `church_rosser`), corollaire **`unique_normal_form`** |

Le losange est prouvé par induction **forte sur la taille du terme** (pas
structurelle) : les cas d'affrontement congruence-contre-redex exigent le
losange sur des sous-termes stricts plus profonds que les fils immédiats.

## Construction

Toolchain `leanprover/lean4:v4.33.0`, Mathlib épinglé `v4.33.0` (voir
`lakefile.lean`). Depuis WSL (build borné mémoire, cf. règles du dépôt) :

```bash
lake exe cache get   # oleans Mathlib pré-compilés
lake build
```

## Témoin empirique

Le carnet pédagogique
[`IIT/ICT-Series/ICT-51-CombinateursSKI-TagDePost-Python.ipynb`](../../../IIT/ICT-Series/ICT-51-CombinateursSKI-TagDePost-Python.ipynb)
(section 6) mesure la confluence empiriquement (30 ordres de réduction
aléatoires d'un même terme convergent vers la même forme normale) — le témoin
que cette preuve formalise.

## Références

- Hindley & Seldin, *Lambda-Calculus and Combinators, an Introduction* (2008), ch. 2
- Takahashi, « Parallel Reductions in λ-Calculus » (1995)
- Nipkow, « More Church-Rosser Proofs (in Isabelle/HOL) » (1996), section combinatory logic
- Wolfram, *Combinators: A Centennial View* (2020), ch. 3 et 11
