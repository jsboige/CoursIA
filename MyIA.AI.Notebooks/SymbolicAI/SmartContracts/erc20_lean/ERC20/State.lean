import Mathlib

/-!
# ERC20.State — état d'un jeton ERC-20 (balances + offre totale)

Modélisation en machine à états finie du standard de jeton fongible ERC-20
(issue #4047). Les adresses sont `Fin n` (un nombre fini de détenteurs
potentiels, muni d'un `Fintype`), les soldes `Address → ℕ`, l'offre totale un
`ℕ`. L'invariant fondateur `Σ balances = totalSupply` est défini ici.
-/

namespace ERC20

variable {n : ℕ}

/-- Une adresse = le `i`-ème compte parmi `n` détenteurs potentiels. Le type
    `Fin n` est fini (`Fintype`), ce qui rend la somme des soldes bien définie. -/
abbrev Address (n : ℕ) := Fin n

/-- L'état global d'un jeton ERC-20 : table des soldes de chaque adresse + offre
    totale (frappée initialement, conservée par `transfer`, symétriquement
    modifiée par `mint`/`burn`). -/
structure State (n : ℕ) where
  /-- Solde courant de chaque adresse. -/
  balances : Address n → ℕ
  /-- Offre totale du jeton : somme conservée des soldes sous l'invariant. -/
  totalSupply : ℕ

/-- **Invariant de conservation ERC-20** : la somme des soldes de toutes les
    adresses égale l'offre totale. C'est la propriété foncière d'un jeton
    fongible — aucun token ne peut être créé ou détruit par `transfer` (seuls
    `mint`/`burn` le font, symétriquement sur l'offre). -/
def supplyInvariant (s : State n) : Prop :=
  ∑ a : Address n, s.balances a = s.totalSupply

end ERC20
