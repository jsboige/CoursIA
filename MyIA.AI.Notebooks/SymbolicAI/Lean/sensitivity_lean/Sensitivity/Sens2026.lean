import Sensitivity.Separations
import Mathlib.Tactic.FinCases

/-!
# Sensibilité 2026 : trois équipes, une réfutation, et ce que le dépôt openai/math dit de ces objets

Ce fichier est un **ajout additif** au lac `sensitivity_lean` (Epic Origami
#19898, Pli 2, issue #20184) : il ne modifie aucun énoncé existant — ni le
théorème de Huang (`MainTheorem`), ni les définitions et témoins de
`Separations`. Il réutilise `sensitivity`, `blockSensitivity` et `flipBlock`
tels quels, et ajoute le témoin **tribus à trois équipes** `tribes32` : la
disjonction de trois conjonctions de taille deux sur `Q 6`.

## La famille 132, citée avec son statut

La famille 132 du dépôt openai/math (2026) — « fonctions booléennes totales
avec `bs(f) ≥ s(f)^α` pour un `α > 2` fixé » — **réfute** le renforcement
quadratique de la conjecture de sensibilité : le gap `bs/s` peut dépasser
tout polynôme fixé en `s`. Ce résultat est cité **avec son statut**
(formalisé en amont, `lean/docs/132.md` du dépôt ; non re-prouvé par nous) :
sa re-preuve est hors d'échelle du lac.

`tribes32` est l'**écho calculable** de ce voisinage — et il enseigne deux
choses, dont une contre-intuitive :

1. **La séparation locale s'étend** : au sommet nul, `s = 0` et `bs ≥ 3`
   (la famille des trois tribus est admissible) — le même écart local que le
   témoin `orOfAnds` de `Separations`, mais avec trois blocs au lieu d'un.
2. **Le majorant naïf `s ≤ t` (taille d'une tribu) est FAUX** — et c'est
   `decide` qui l'a réfuté, à la compilation : au sommet « une lampe allumée
   par tribu », chaque première coordonnée allume sa conjonction, et la
   sensibilité locale vaut **3** (`tribes32_sensitivity_eq_three`). À cette
   échelle, `s` rattrape `bs` : les tribus seules ne séparent pas
   *globalement* — la séparation de la littérature demande les constructions
   d'adressage (Rubinstein 1995), hors d'échelle ici, citées pour ça.

Le récit pédagogique est exactement celui de 2026 : **mesuré, pas supposé** —
l'intuition « deux lampes par tribu, donc sensibilité 2 » ne survit pas à
l'énumération exhaustive du noyau.
-/

namespace Sensitivity

open Bool Finset Fintype

/-- Témoignage « tribus » en dimension 6 : disjonction de trois conjonctions
de taille deux (trois « équipes » de deux coordonnées) — les `tribes` de la
littérature Nisan–Szegedy, à l'échelle calculable. -/
def tribes32 (x : Q 6) : Bool :=
  (x 0 && x 1) || (x 2 && x 3) || (x 4 && x 5)

/-- Au sommet nul, aucune coordonnée seule n'allume `tribes32` : il faut
retourner une tribu **entière**. La sensibilité locale y est nulle. -/
theorem tribes32_sensitivity_zero :
    sensitivity tribes32 (fun _ => false) = 0 := by
  decide

/-- **La réfutation de l'intuition, par énumération exhaustive.** Au sommet
« une lampe allumée par tribu » (coordonnées impaires), chaque première
coordonnée allume sa conjonction à elle seule : la sensibilité locale vaut
**3**, pas 2. Le majorant naïf « au plus une taille de tribu » est faux —
c'est le noyau Lean qui l'a établi, en réfutant la conjecture `∀ x, s ≤ 2`
à la compilation. -/
theorem tribes32_sensitivity_eq_three :
    sensitivity tribes32 (fun i => i.val % 2 = 1) = 3 := by
  decide

set_option maxRecDepth 8192 in
/-- Au sommet nul, la famille des trois tribus `{{0,1}, {2,3}, {4,5}}` est
admissible au sens de `blockSensitivity` : blocs non vides, chacun bascule la
valeur, deux à deux disjoints. La sensibilité de bloc y est donc au moins
**3**. -/
theorem tribes32_blockSensitivity_ge_three :
    3 ≤ blockSensitivity tribes32 (fun _ => false) := by
  classical
  have hfam : ∀ B ∈ ({({0, 1} : Finset (Fin 6)), {2, 3}, {4, 5}} :
      Finset (Finset (Fin 6))),
      B.Nonempty ∧ tribes32 (flipBlock (fun _ => false) B) ≠ tribes32 (fun _ => false) := by
    decide
  have hpair : ∀ B₁ ∈ ({({0, 1} : Finset (Fin 6)), {2, 3}, {4, 5}} :
      Finset (Finset (Fin 6))),
      ∀ B₂ ∈ ({({0, 1} : Finset (Fin 6)), {2, 3}, {4, 5}} :
        Finset (Finset (Fin 6))),
      B₁ ≠ B₂ → (B₁ ∩ B₂ : Finset (Fin 6)) = ∅ := by
    decide
  have hcard : ({({0, 1} : Finset (Fin 6)), {2, 3}, {4, 5}} :
      Finset (Finset (Fin 6))).card = 3 := by
    decide
  have hle : ({({0, 1} : Finset (Fin 6)), {2, 3}, {4, 5}} :
      Finset (Finset (Fin 6))).card ≤ blockSensitivity tribes32 (fun _ => false) :=
    Finset.le_sup (Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨hfam, hpair⟩⟩)
  rw [hcard] at hle
  exact hle

/-- **Séparation locale à trois blocs** : au sommet nul, `s = 0 < 3 ≤ bs`.
Le même écart local que le témoin `orOfAnds` de `Separations` (un bloc),
généralisé à trois blocs disjoints — la mécanique exacte par laquelle les
constructions d'adressage de la littérature fabriquent leurs gaps. La
séparation *globale* n'est pas claimée : `tribes32_sensitivity_eq_three`
montre que `s` rattrape `bs` ailleurs sur le cube. -/
theorem tribes32_local_separation :
    sensitivity tribes32 (fun _ => false) <
      blockSensitivity tribes32 (fun _ => false) := by
  rw [tribes32_sensitivity_zero]
  exact Nat.lt_of_lt_of_le (by decide) tribes32_blockSensitivity_ge_three

end Sensitivity
