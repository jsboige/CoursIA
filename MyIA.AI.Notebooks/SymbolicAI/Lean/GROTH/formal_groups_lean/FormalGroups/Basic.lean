import Mathlib.RingTheory.MvPowerSeries.Substitution

/-!
# Groupes formels multivariés : la structure de base

Ce module définit la notion de **groupe formel multivarié** de dimension `g`
sur un anneau commutatif `R` : une loi de composition donnée par `g` séries
formelles en `2g` variables (les deux copies de l'espace ambiant), dont
l'origine est le neutre et dont la partie linéaire est l'identité.

Le fichier amont est `Definitions/Def_MvFormalGroup_BasicV2.lean` du dépôt
[`anthropics/fermats-last-theorem`](https://github.com/anthropics/fermats-last-theorem)
(commit `aa2d8b34`, Apache-2.0 — voir `NOTICE`), découpé ici en modules
progressifs (issue #14785). Witt, Cartier et Artin–Hasse sont hors scope.
-/

set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace FormalGroups

/-- Un groupe formel multivarié de dimension `g` sur `R` : la loi est un
`g`-uplet de séries formelles en `2g` variables vérifiant les axiomes de
neutre (terme constant nul), de partie linéaire identité et
d'associativité (par substitution). -/
@[ext]
structure MvFormalGroup (g : ℕ) (R : Type*) [CommRing R] where

  toPowerSeries : Fin g → MvPowerSeries (Fin g ⊕ Fin g) R

  /-- Le terme constant est nul : l'origine est le neutre de la loi. -/
  constantCoeff_eq_zero : ∀ i, (toPowerSeries i).constantCoeff = 0

  /-- Partie linéaire, première copie : chaque composante `i` dépend
  linéairement de la variable `inl i` uniquement. -/
  coeff_single_inl : ∀ i j,
    (toPowerSeries i).coeff (Finsupp.single (Sum.inl j) 1) = if i = j then 1 else 0

  /-- Partie linéaire, seconde copie : symétrique de `coeff_single_inl`
  pour la variable `inr j`. -/
  coeff_single_inr : ∀ i j,
    (toPowerSeries i).coeff (Finsupp.single (Sum.inr j) 1) = if i = j then 1 else 0

  /-- Associativité de la loi : substituer la loi dans la loi, à gauche ou
  à droite, donne la même série en `3g` variables. -/
  assoc : ∀ i,
    subst
      (Sum.elim
        (fun j => subst
          (Sum.elim
            (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
            fun l => X (Sum.inr (Sum.inl l)))
          (toPowerSeries j))
        fun j => X (Sum.inr (Sum.inr j)))
      (toPowerSeries i)
      =
    subst
      (Sum.elim
        (fun j => (X (Sum.inl j) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
        fun j => subst
          (Sum.elim
            (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
            fun l => X (Sum.inr (Sum.inr l)))
          (toPowerSeries j))
      (toPowerSeries i)

namespace MvFormalGroup

variable {g : ℕ} {R : Type*} [CommRing R]

/-- Commutativité d'un groupe formel multivarié : la loi est invariante par
échange des deux blocs de variables. Classe `Prop`, posée comme instance
pour la loi additive dans `FormalGroups.Additive`. -/
class IsComm (F : MvFormalGroup g R) : Prop where
  comm : ∀ i,
    subst
      (Sum.elim
        (fun j => (X (Sum.inr j) : MvPowerSeries (Fin g ⊕ Fin g) R))
        fun j => X (Sum.inl j))
      (F.toPowerSeries i)
      = F.toPowerSeries i

/-- La loi d'un groupe formel est substituable : ses composantes sont à
termes constants nuls. -/
theorem hasSubst_toPowerSeries (F : MvFormalGroup g R) : HasSubst F.toPowerSeries :=
  hasSubst_of_constantCoeff_zero F.constantCoeff_eq_zero

/-- La substitution est additive sur les sommes d'indéterminées :
`subst a (X s + X t) = a s + a t` lorsque la famille `a` est à termes
constants nuls. Lemme-clé des preuves d'associativité de la loi additive. -/
theorem subst_X_add_X {σ τ : Type*} [Finite σ] {a : σ → MvPowerSeries τ R}
    (ha : ∀ s, (a s).constantCoeff = 0) (s t : σ) :
    subst a (X s + X t : MvPowerSeries σ R) = a s + a t := by
  have h := hasSubst_of_constantCoeff_zero ha
  rw [subst_add h, subst_X h, subst_X h]

end MvFormalGroup

end FormalGroups

end
