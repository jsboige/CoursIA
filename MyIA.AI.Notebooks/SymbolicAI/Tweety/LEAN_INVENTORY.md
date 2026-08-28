# Inventaire des projets Lean 4 — `SymbolicAI/Tweety`

Inventaire transverse des projets de formalisation Lean 4 sous `SymbolicAI/Tweety/`, sur le
modèle de [`GameTheory/LEAN_INVENTORY.md`](../../GameTheory/LEAN_INVENTORY.md) et
[`SymbolicAI/Lean/LEAN_INVENTORY.md`](../Lean/LEAN_INVENTORY.md). Source de vérité : corps
de l'Epic [#4038](https://github.com/jsboige/CoursIA/issues/4038) + vérification
`firsthand`. Colonne *Sorry (production)* = métrique CI `real` (commentaires strippés [ligne
`--` et bloc `/- -/`] puis `\bsorry\b` — les mentions prose « 0 sorry » n'entrent pas dans
ce compte ; cf. `lean-ci-sorry-filter`).

## Résumé

| Lake | Toolchain | sorry (production) | Modules | Notebook câblé | Classe | Suivi |
|------|-----------|--------------------:|--------:|---------------:|--------|-------|
| `argumentation_lean` | v4.32.1 | 0 | 6 | 1 | PEDA/REF | #4046, #4038 |
| **Total** | — | **0** | **6** | — | — | — |

¹ Notebook Lean câblé = `SymbolicAI/Tweety/Tweety-5b-Lean-Argumentation.ipynb` (kernel
`lean4-wsl`, importe `Argumentation.*`). Companion conceptuel = le notebook **Tweety-5**.
Formalisation compagnon du notebook Tweety-5 (Dung, 1995) — premier lake Lean de la série
Tweety (roadmap Lean #4038, #4046).

---

## Par lake

### argumentation_lean — PEDAGOGIQUE / REFERENCE

**Objectif** : **argumentation abstraite de Dung (1995)** — extension grounded
(Knaster–Tarski), Dung Fundamental Lemma, hiérarchie des 5 sémantiques
(stable → preferred → complete → admissible, et grounded). Formalisation compagnon du
notebook Tweety-5 (roadmap Lean #4038, #4046).

- **Toolchain** : v4.32.1 · **Dépendance** : Mathlib4
- **lib** : `Argumentation`
  (`globs := #[.one \`Argumentation, .submodules \`Argumentation]`), package
  `argumentation_lean`
- **Modules** : `Argumentation.lean` (umbrella) + `Argumentation/Basic.lean`,
  `Argumentation/Characteristic.lean`, `Argumentation/Extensions.lean`,
  `Argumentation/Fundamental.lean`, `Argumentation/Grounded.lean` (FR ; jumeaux `_en`
  exclus, i18n #4980)
- **sorry (production)** : **0** (métrique CI `real`, baseline `"0"`).

#### Théorèmes prouvés (0 sorry)

- **`fundamental_lemma`** (Dung Fundamental Lemma) : l'ensemble des arguments défendus par
  une extension admissible est lui-même admissible et défend `F(S)`.
- **`fundamental_lemma_defends`** / **`fundamental_lemma_defends_self`** : lemmas de support
  du Fondamental Lemma.
- **`grounded_fixed`** (Knaster–Tarski) : `F(grounded) = grounded` — l'extension grounded est
  un point fixe.
- **`grounded_least_complete`** : l'extension grounded est la plus petite extension complète.
- **`complete_admissible`** / **`preferred_complete`** / **`stable_complete`** : hiérarchie
  des sémantiques (stable ⊆ preferred ⊆ complete ⊆ admissible).
- **`characteristic_eq_defendedBy`** / `mem_characteristic_iff` : la fonction caractéristique
  `F` se lit comme « arguments défendus ».
- **`defends_mono`**, `conflictFree_empty`, `F_preserves_admissible`,
  `F_preserves_conflictFree`, `no_internal_attack_on_defended`.

#### Honnêteté du périmètre (G.3/G.9)

La hiérarchie des 5 sémantiques et l'extension grounded sont prouvées 0 sorry. Ce qui reste
**OPEN (non sorry-backed)**, documenté honnêtement :

- **« Grounded est elle-même complète »** (Dung Proposition 11, stabilisation finie) —
  documenté **OPEN**, pas supporté par sorry.
- **Équivalence/complétude réciproque complète** des sémantiques (réciproques et cas
  d'égalité entre préférées et stables, etc.) — non établie.

## Notes transverses

- **CI** : `.github/workflows/lean-argumentation.yml` (`project-path: …/argumentation_lean`,
  `sorry-filter-mode: real`, baseline `"0"`), caller de `lean-build.yml@main`. `real` = awk
  canonique (lean-build.yml:111-134) + grep word-bounded — rattrape `exact sorry`,
  `:= by sorry`, `sorry -- c` même entouré d'un case-bullet `·` (U+00B7) ; les mentions prose
  « sorry-free » en commentaires `--` sont strippées et jamais comptées.
- **i18n (#4980)** : jumeaux `Argumentation/Basic_en.lean` etc. (l'umbrella `Argumentation.lean`
  n'a pas de jumeau `_en`) — les comptes sorries et le décompte de modules portent sur les
  fichiers FR.
