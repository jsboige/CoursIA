import Mathlib
import ERC20.State_en

/-!
# ERC20.Ops — guarded transitions (transfer, mint, burn)

The three standard operations of an ERC-20 token, viewed as guarded state
transitions. The guards (`sufficient balance`) ensure the absence of underflow:
a `transfer`/`burn` cannot withdraw more than the present balance.

Note: the names `src`/`dst` (source/destination) substitute the usual ERC-20
parameters `from`/`to`, which are reserved keywords in Lean 4.
-/

namespace ERC20_en

variable {n : ℕ}

/-- `mint dst amount`: mints `amount` tokens credited to the `dst` account, and
    increases the total supply by the same amount. (Privileged operation of the
    contract owner.) -/
def mint (s : State n) (dst : Address n) (amount : ℕ) : State n :=
  { balances := fun a => if a = dst then s.balances a + amount else s.balances a
    totalSupply := s.totalSupply + amount }

/-- `burn src amount`: burns `amount` tokens from the `src` account (implicit
    guard: sufficient balance), and decreases the total supply by the same amount. -/
def burn (s : State n) (src : Address n) (amount : ℕ) : State n :=
  { balances := fun a => if a = src then s.balances a - amount else s.balances a
    totalSupply := s.totalSupply - amount }

/-- `transfer src dst amount`: transfers `amount` tokens from `src` to `dst`.
    The total supply is unchanged (internal move of tokens). The source account
    balance must cover `amount` (guard, checked in `transfer_no_underflow`). -/
def transfer (s : State n) (src dst : Address n) (amount : ℕ) : State n :=
  { balances := fun a =>
      if a = src then s.balances a - amount
      else if a = dst then s.balances a + amount
      else s.balances a
    totalSupply := s.totalSupply }

end ERC20_en
