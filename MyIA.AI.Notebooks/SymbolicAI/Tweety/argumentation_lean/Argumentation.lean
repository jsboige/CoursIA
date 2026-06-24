import Mathlib

/-!
# Argumentation — sémantique de Dung (1995) en Lean 4

Bibliothèque formalisant la **théorie de l'argumentation abstraite de Dung** :
cadres d'argumentation, extensions (admissible, complète, grounded, preferred,
stable) et le théorème de point fixe (grounded = lfp de la fonction
caractéristique, Knaster–Tarski).

## Statut

- **Toolchain** : `leanprover/lean4:v4.31.0-rc1` + Mathlib4 (`v4.31.0-rc1`).
- **Sorry** : **0** sur tout le module — Fundamental Lemma de Dung, identités de
  point fixe du grounded, plus-petite-complétude, hiérarchie des sémantiques
  (stable ⇒ preferred ⇒ complete ⇒ admissible), et le lemme-clé
  `F_preserves_admissible`.
- **Jalon OPEN documenté** : « le grounded est lui-même une extension complète »
  (stabilisation finie de la suite itérée) — **non** sorry-backed, voir
  `Grounded.lean`.

## Modules

- `Argumentation.Basic` — `AF α` (relation d'attaque), `conflictFree`, `defends`,
  monotonie de la défense.
- `Argumentation.Characteristic` — fonction caractéristique `F : Set α →o Set α`
  (monotone, Knaster–Tarski applicable).
- `Argumentation.Extensions` — `Admissible`, `Complete`, `grounded = F.lfp`,
  `Preferred`, `Stable`, + hiérarchie (`stable_complete`, `preferred_complete`,
  `complete_admissible`).
- `Argumentation.Fundamental` — **Fundamental Lemma de Dung** (sans sorry).
- `Argumentation.Grounded` — `grounded_fixed`, `grounded_defends_iff_mem`,
  `grounded_least_complete`, `F_preserves_admissible`.

## Références croisées

- Notebook compagnon `Tweety-5-Abstract-Argumentation.ipynb` (série Tweety) :
  présentation Python (tweety) des cadres de Dung, dont ceci est le pendant prouvé.
- Issue #4046 (roadmap Lean #4038), Epic Argumentum #2137.
-/

namespace Argumentation

variable {α : Type*} (af : AF α)

/-- Le treillis complet `(Set α, ⊆)` sur lequel opère la fonction
caractéristique. -/
abbrev ArgLattice (α : Type*) := Set α

end Argumentation
