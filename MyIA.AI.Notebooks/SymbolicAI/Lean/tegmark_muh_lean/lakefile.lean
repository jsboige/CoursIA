import Lake
open Lake DSL

/-! # Mini-projet Lean pédagogique : structures mathématiques finies (Annexe A, Tegmark R16)

Formalisation **constructive** Lean 4 de la définition d'une *structure
mathématique finie* telle que donnée en Annexe A de Tegmark (2007), *The
Mathematical Universe* ([arXiv:0704.0646](https://arxiv.org/abs/0704.0646)) —
PDF : `G:\Mon Drive\MyIA\IA\Bibliographie IA\Consciousness\2007 - Tegmark - The Mathematical Universe.pdf`
(sha8 `85712871`).

Le projet illustre l'idée que **l'équivalence de deux structures finies est
décidable par algorithme haltant** (énumération des tableaux de valeurs) — c'est
la base de la CUH (Computable Universe Hypothesis) au §VII.E du même papier.

**Pas de dépendance Mathlib** : `Decidable`, `List`, `Fin`, `Bool`, `Array`
suffisent pour la signature d'une structure finie, ses générateurs, et la
décidabilité de l'équivalence dans le cas où l'arité est bornée et le nombre
d'éléments des ensembles est borné (l'algorithme haltant énumère alors un
espace fini de tableaux). -/

package «muh» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib «MUH» where
  -- `MUH.Structure` : signature d'une structure finie (sets + relations
  -- génératrices + arités/types), `MUH.Encoding` : encodage selon Tegmark §c,
  -- `MUH.Boolean` : algèbre de Boole à 1 générateur (Sheffer/NAND), avec preuve
  -- que la définition à 8 générateurs (NOR/NOT/etc.) est équivalente.
  -- `MUH.Cyclic` : groupes cycliques C₂ et C₃, structure + automorphismes.
  -- `MUH.Decidable` : décidabilité décida par algorithme énumératif haltant
  -- pour arité ≤ 2, cardinalité d'ensemble ≤ 3.
  -- `globs` (not default roots) so `lake build` auto-discovers `*_en` siblings (#4980).
  globs := #[.submodules `MUH]