# `erc20_lean` — English documentation companion

> **Convention — issue #4980, user decision 2026-07-02 (option B).**
> The `.lean` source files (`lakefile.lean`, `ERC20.lean`, `ERC20/State.lean`,
> `ERC20/Ops.lean`, `ERC20/Invariant.lean`) are the **canonical French**
> documentation — the single source of truth, unchanged. This file is the
> **English companion**: a non-compiled Markdown mirror of the same docstrings,
> translated. It follows the `README.md` → `README.en.md` pattern of Epic #1650
> (pilot: sudoku_lean #4998; rollout: finiteness #5000, kelly #5003).
>
> - **Zero build cost** (Markdown is not compiled by `lake`), **zero risk** to
>   compilation — the `.lean` files are untouched.
> - **Source of truth = the `.lean`**. If the two ever disagree, the French in
>   the `.lean` wins; this companion mirrors the source and is regenerated
>   against it. Section order below matches declaration order in each file so
>   drift is easy to spot.
> - Tactical `--` comments (inline, developer-facing, proof-tactic-bound) are
>   French-only in the source by convention and are **not** mirrored here — they
>   are tied to the Lean tactic language and add noise if duplicated.

---

## `lakefile.lean` — module

# Lean pedagogical mini-project: conservation invariant of an ERC-20 token

A Lean 4 project (with Mathlib) formalizing the **foundational conservation
invariant of a fungible ERC-20 token**: the sum of the balances of all
addresses equals the total supply, and this invariant is preserved by each
standard operation (`transfer`, `mint`, `burn`). See issue #4047 (roadmap
#4038).

This is a textbook case of the link between formal methods and blockchain,
ultra-topical and **concrete**: it demonstrates the value of formal proof on
"real" code that students recognize (Solidity's ERC-20 standard). The
SmartContract series had no Lean lake until this one.

Model: a finite-state machine. Addresses are `Fin n` (a finite number of
potential holders), balances `Address → ℕ`, total supply a `ℕ`.
`supplyInvariant s := ∑ a, s.balances a = s.totalSupply`. Operations are guarded
transitions (sufficient balance for `transfer`/`burn`, no underflow).

Companion notebook (`SC-7-Token-Standards.ipynb`, SmartContract series):
pedagogical presentation of the token + formal verification side by side with
the Solidity implementation. Wiring the notebook is the responsibility of the
SmartContract series owner.

(`ERC20.lean` is three import lines — nothing to mirror.)

---

## `ERC20/State.lean`

### Module

# ERC20.State — the state of an ERC-20 token (balances + total supply)

Finite-state-machine modeling of the ERC-20 fungible-token standard (issue
#4047). Addresses are `Fin n` (a finite number of potential holders, equipped
with a `Fintype`), balances `Address → ℕ`, the total supply a `ℕ`. The
foundational invariant `Σ balances = totalSupply` is defined here.

### `Address`

An address = the `i`-th account among `n` potential holders. The type `Fin n`
is finite (`Fintype`), which makes the sum of balances well-defined.

### `State`

The global state of an ERC-20 token: the table of balances for each address +
total supply (minted initially, preserved by `transfer`, symmetrically modified
by `mint`/`burn`).

### `State.balances`

Current balance of each address.

### `State.totalSupply`

Total supply of the token: the conserved sum of balances under the invariant.

### `supplyInvariant`

**ERC-20 conservation invariant**: the sum of the balances of all addresses
equals the total supply. This is the foundational property of a fungible token —
no token can be created or destroyed by `transfer` (only `mint`/`burn` do so,
symmetrically on the supply).

---

## `ERC20/Ops.lean`

### Module

# ERC20.Ops — guarded transitions (transfer, mint, burn)

The three standard ERC-20 operations, viewed as guarded transitions of the
state. The guards (`sufficient balance`) ensure the absence of underflow: a
`transfer`/`burn` cannot withdraw more than the balance present.

Note: the names `src`/`dst` (source/destination) substitute the usual ERC-20
parameters `from`/`to`, which are reserved keywords in Lean 4.

### `mint`

`mint dst amount`: mints `amount` tokens credited to the account `dst`, and
increases the total supply by the same amount. (Privileged operation of the
contract owner.)

### `burn`

`burn src amount`: burns `amount` tokens from the account `src` (implicit guard:
sufficient balance), and decreases the total supply by the same amount.

### `transfer`

`transfer src dst amount`: transfers `amount` tokens from `src` to `dst`. The
total supply is unchanged (internal movement of tokens). The source balance must
cover `amount` (guard, verified in `transfer_no_underflow`).

---

## `ERC20/Invariant.lean`

### Module

# ERC20.Invariant — preservation of the conservation invariant

We prove that the invariant `Σ balances = totalSupply` is preserved by each of
the three standard operations (`mint`, `burn`, `transfer`), then by an arbitrary
sequence of reachable operations (induction on the trace). These are the target
theorems of issue #4047.

The key technical ingredient is the **additive extraction** of a point from a
finite sum: on `Fin n` (a finite type), `∑ a ∈ s, f a = f a₀ + ∑ a ∈ s.erase a₀,
f a` as soon as `a₀ ∈ s`. We carefully avoid distributing truncated `ℕ`
subtraction over the sum (`∑ (f - g) = ∑ f - ∑ g` is false in general on `ℕ`),
reasoning instead by extraction (via `insert_erase`/`sum_insert`, additive form)
then `ℕ` arithmetic (`Nat.add_sub_assoc`, `omega`).

### `sum_split_mem`

Additive extraction of a point from a finite sum: if `a ∈ s`, the sum over `s`
equals the value at `a` plus the sum over `s.erase a`. Additive form (no
subtraction), hence valid on `ℕ`.

### `sum_univ_split`

The special case `s = univ` (the sum over all addresses).

### `balance_le_totalSupply`

The balance of an account is bounded by the total supply (under the invariant):
each term of an `ℕ` sum is bounded by the total sum.

### `mint_preserves_supply`

**`mint` preserves the supply.** Minting `amount` to `dst` credits `amount` to
the balances AND to the total supply: the invariant is conserved.

### `burn_preserves_supply`

**`burn` preserves the supply.** Burning `amount` from `src` (sufficient
balance) removes `amount` from the balances AND from the total supply: the
invariant is conserved.

### `transfer_preserves_supply`

**`transfer` preserves the supply.** Transferring `amount` from `src` to `dst`
(distinct addresses, sufficient balance) moves the tokens without creating or
destroying: the sum of balances is unchanged, as is the total supply.

### `transfer_no_underflow`

**`transfer` debits the source by exactly `amount`, without underflow.** The
source balance after `transfer` is `bal src - amount`, and the guard makes this
subtraction reversible (no semantic underflow).

### `Op`

**Reachable operation.** A step `s → s'` is one of the three operations
`mint`/`burn`/`transfer` executed from a state carrying the invariant.

### `op_preserves_invariant`

A reachable operation preserves the invariant (case by case).

### `Reachable`

**Reflexive-transitive reachability.** `Reachable n s s'`: `s'` is reachable
from `s` by zero, one, or several operations.

### `reachable_preserves_invariant`

**Induction on the trace:** any sequence of reachable operations preserves the
invariant end to end. The final state still carries the invariant.
