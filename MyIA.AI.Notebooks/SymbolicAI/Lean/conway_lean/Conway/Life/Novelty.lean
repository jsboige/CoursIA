/-
Copyright (c) 2026 CoursIA. Tous droits reserves.
Distribue sous licence Apache 2.0 comme decrit dans le fichier LICENSE.

## Jeu de la Vie de Conway — Borne de nouveaute pour la classe des oscillateurs

Axe EFFICACITE de hashlife (#11162) : la quantite qui fait tenir Golly n'est
pas le confinement (`jumpCaptured`, #11007 — la licence) mais la NOVEAUTE,
c'est-a-dire la stabilite de l'ensemble des etats visites le long de la
trajectoire. Ce module formalise l'invariant de stabilite pour la classe
la plus simple : les oscillateurs.

**Resultat.** Si `evolve p g = g` avec `p > 0` (g est un point fixe de la
p-ieme iteratee — la periode au sens de `isOscillator`), alors la trajectoire
complete `t |-> evolve t g` ne visite que des etats deja apparus dans les `p`
premiers instants (`novelty_bound_of_period`), donc il existe un `Finset` de
cardinal au plus `p` contenant toute la trajectoire
(`trajectory_states_le_of_period`). La nouveaute au niveau grille est bornee
par `p`, independamment de l'horizon : c'est le pendant quantitatif du
constat empirique « Golly est rapide sur les oscillateurs ».

**Portee et limite, documentees.** La borne est au niveau GRILLE (etats
distincts). La nouveaute operationnelle de hashlife se mesure au niveau des
NOEUDS de macrocells (taux de hit du cache de memoisation, avec partage de
sous-arbres) : pour un oscillateur borde, chaque etat periodique engendre un
arbre dont les sous-arbres se repetent, mais le passage grille -> arbre de
macrocells a une taille qui croit avec la fenetre, et la borne au niveau
noeud demande une induction sur la structure de `MacroCell` qui reste
hors de portee de ce module (diagnostic ecrit, cf #11162 acceptation :
l'alternative « borne deriverie ou diagnostic » est ici le diagnostic de la
borne noeud, la borne grille etant livree).

La caracterisation « quels motifs ont une nouveaute persistante » est
indecidable a la limite (Life est Turing-complet : une machine de Turing
programmee encode la production infinie de motifs neufs) — les patterns
pathologiques (MT, #6724) sont les temoins de ce plafond.

Ce module est entierement prouve (aucun `sorry`, aucun axiome natif).
-/

/-
  Convention i18n (EPIC #4980, decision user 2026-07-04) : ce fichier est **FR canonique**,
  avec son miroir anglais dans le fichier sibling `Novelty_en.lean` (modele sibling
  pair ratifie 2026-07-04, cf `code-style.md` §Lean i18n). Les enonces de theoremes,
  les tactiques Lean, les noms de lemmes et les references Mathlib restent en anglais
  (compat Mathlib 4) ; seules les docstrings de theoreme et ce bloc d'en-tete different
  entre les deux fichiers.
-/

import Conway.Life
import Conway.Life.HashlifeCorrectness.Foundation

namespace Conway
namespace Life

/-! ## Multiples de la periode

Le lemme d'iteration `evolve_add` (Foundation, P4.4) dit que `evolve` est un
morphisme de l'addition : composer `q` blocs de periode `p` ramene a l'etat
initial. C'est la seule arithmetique dont la borne a besoin. -/

/-- La periode se re-applique en tout point de la trajectoire : si
`evolve p g = g`, alors `evolve p (evolve m g) = evolve m g` pour tout `m`.
C'est la commutativite de l'addition des iteratees qui le donne :
`p + m = m + p`, et le bloc `p` cote droit se reduit par `hp`. -/
theorem evolve_period_shift (g : Grid) (p : Nat) (hp : evolve p g = g) (m : Nat) :
    evolve p (evolve m g) = evolve m g := by
  rw [← evolve_add, Nat.add_comm, evolve_add, hp]

/-- Tout multiple de la periode laisse tout point de la trajectoire invariant :
si `evolve p g = g`, alors `evolve (p * q) (evolve m g) = evolve m g` pour
tous `q`, `m` — le bloc `p * q` se decompose en `q` blocs `p`, chacun se
reduisant par `evolve_period_shift`. -/
theorem evolve_mul_shift (g : Grid) (p : Nat) (hp : evolve p g = g) (q m : Nat) :
    evolve (p * q) (evolve m g) = evolve m g := by
  induction q with
  | zero => simp
  | succ q ih => rw [Nat.mul_succ, evolve_add, evolve_period_shift g p hp m, ih]

/-- Tout multiple de la periode ramene a l'etat initial : si `evolve p g = g`,
alors `evolve (p * q) g = g` pour tout `q` (cas `m = 0` du shift). -/
theorem evolve_mul_of_period (g : Grid) (p : Nat) (hp : evolve p g = g) (q : Nat) :
    evolve (p * q) g = g := by
  simpa using evolve_mul_shift g p hp q 0

/-! ## Borne de nouveaute (niveau grille)

L'invariant de stabilite : apres `p` instants, la trajectoire ne produit plus
d'etat neuf. Tout ce qui est visite a l'instant `t` est deja apparu a un
instant `r < p`. -/

/-- **Borne de nouveaute pour un oscillateur** : si `evolve p g = g` avec
`p > 0`, alors tout etat visite a un instant quelconque `t` est deja apparu
dans les `p` premiers instants — la trajectoire ne produit jamais d'etat
neuf apres la periode. Le temoin est le reste `t % p`. -/
theorem novelty_bound_of_period (g : Grid) (p : Nat) (hp0 : 0 < p)
    (hp : evolve p g = g) (t : Nat) :
    ∃ r, r < p ∧ evolve t g = evolve r g := by
  obtain ⟨r, hr, hdecomp⟩ : ∃ r, r < p ∧ t = p * (t / p) + r :=
    ⟨t % p, Nat.mod_lt t hp0, (Nat.div_add_mod t p).symm⟩
  refine ⟨r, hr, ?_⟩
  rw [hdecomp, evolve_add, evolve_mul_shift g p hp (t / p) r]

/-- **Cardinal de la trajectoire** : la trajectoire complete d'un oscillateur
de periode `p` tient dans un `Finset` de cardinal au plus `p`. C'est la
formulation ensembliste de « au plus `p` etats distincts », le pendant
formel du constat empirique « Golly est rapide sur les oscillateurs » :
le taux de hit de la memoisation ne peut pas se degrader avec l'horizon. -/
theorem trajectory_states_le_of_period (g : Grid) (p : Nat) (hp0 : 0 < p)
    (hp : evolve p g = g) :
    ∃ s : Finset Grid, s.card ≤ p ∧ ∀ t : Nat, evolve t g ∈ s := by
  refine ⟨(Finset.range p).image (fun r => evolve r g),
    Finset.card_image_le.trans_eq (Finset.card_range p), fun t => ?_⟩
  obtain ⟨r, hr, heq⟩ := novelty_bound_of_period g p hp0 hp t
  exact Finset.mem_image.2 ⟨r, Finset.mem_range.2 hr, heq.symm⟩

/-! ## Application : le blinker

Le blinker (periode 2, `blinker_period_two` dans `Conway.Life`) visite au
plus 2 etats — l'horizontal et le vertical — quel que soit l'horizon. -/

/-- La trajectoire du blinker horizontal (periode 2) tient dans un `Finset`
de cardinal au plus 2 : deux etats distincts, jamais plus, quel que soit
l'horizon de simulation. -/
theorem blinker_h_trajectory_states_le :
    ∃ s : Finset Grid, s.card ≤ 2 ∧ ∀ t : Nat, evolve t blinker_h ∈ s :=
  trajectory_states_le_of_period _ 2 (by norm_num) (by decide)

end Life
end Conway
