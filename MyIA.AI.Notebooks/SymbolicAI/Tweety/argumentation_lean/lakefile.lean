import Lake
open Lake DSL

/-!
# Mini-projet Lean pédagogique : sémantique de l'argumentation abstraite de Dung

Projet Lean 4 (avec Mathlib) formalisant la **théorie de l'argumentation abstraite
de Dung (1995)** : cadres d'argumentation, extensions (admissible, complète,
grounded, preferred, stable) et le **théorème de point fixe** (extension grounded
= plus petit point fixe de la fonction caractéristique, Knaster–Tarski). Voir
l'issue #4046 (roadmap #4038).

C'est le cœur formel de la série Tweety et un **pont direct vers l'Epic Argumentum
#2137**. La théorie de Dung est *exactement* de la théorie du point fixe sur treillis
fini — Mathlib fournit `CompleteLattice (Set α)`, `OrderHom.lfp`/`gfp` et
Knaster–Tarski clé en main, sur lesquels la sémantique se mappe presque
littéralement.

Modèle : un cadre d'argumentation `AF α` munit un type d'arguments `α` d'une
relation d'attaque `attacks : α → α → Prop` (l'univers des arguments est le type
entier `α`, encodage standard). La **fonction caractéristique**
`F(S) = { a | S défend a }` est un `OrderHom` monotone sur `Set α` ; l'extension
**grounded** est son plus petit point fixe `F.lfp`.

Notebook compagnon (`Tweety-5-Abstract-Argumentation.ipynb`, série Tweety) :
présentation pédagogique des cadres de Dung côte à côte Python (tweety) / Lean.
Le câblage du notebook revient au propriétaire de la série Tweety.
-/

package «argumentation_lean» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.31.0-rc1"

@[default_target]
lean_lib «Argumentation» where
  globs := #[.submodules `Argumentation]
