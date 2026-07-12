import Mathlib

/-!
# ERC20.State — state of an ERC-20 token (balances + total supply)

Finite state-machine modelling of the ERC-20 fungible-token standard
(issue #4047). Addresses are `Fin n` (a finite number of potential holders,
equipped with a `Fintype`), balances are `Address → ℕ`, the total supply an
`ℕ`. The founding invariant `Σ balances = totalSupply` is defined here.
-/

namespace ERC20_en

variable {n : ℕ}

/-- An address = the `i`-th account among `n` potential holders. The type
    `Fin n` is finite (`Fintype`), which makes the sum of balances well-defined. -/
abbrev Address (n : ℕ) := Fin n

/-- The global state of an ERC-20 token: the balance table of each address plus
    the total supply (initially minted, preserved by `transfer`, symmetrically
    modified by `mint`/`burn`). -/
structure State (n : ℕ) where
  /-- Current balance of each address. -/
  balances : Address n → ℕ
  /-- Total supply of the token: the conserved sum of balances under the invariant. -/
  totalSupply : ℕ

/-- **ERC-20 conservation invariant**: the sum of the balances of all addresses
    equals the total supply. This is the defining property of a fungible token —
    no token can be created or destroyed by `transfer` (only `mint`/`burn` do so,
    symmetrically on the supply). -/
def supplyInvariant (s : State n) : Prop :=
  ∑ a : Address n, s.balances a = s.totalSupply

end ERC20_en
