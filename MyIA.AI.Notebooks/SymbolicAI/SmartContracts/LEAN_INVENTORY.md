# Inventaire des projets Lean 4 — `SymbolicAI/SmartContracts`

Inventaire transverse des projets de formalisation Lean 4 sous `SymbolicAI/SmartContracts/`,
sur le modèle de [`GameTheory/LEAN_INVENTORY.md`](../../GameTheory/LEAN_INVENTORY.md) et
[`SymbolicAI/Lean/LEAN_INVENTORY.md`](../Lean/LEAN_INVENTORY.md). Source de vérité : corps
de l'Epic [#4038](https://github.com/jsboige/CoursIA/issues/4038) + vérification
`firsthand`. Colonne *Sorry (production)* = métrique CI `real` (commentaires strippés,
`\bsorry\b`, fichiers FR hors `_en` ; bascule #11688 — historiquement
`standalone-tactic` ; les mentions prose « 0 sorry » n'entrent pas dans ce compte).

## Résumé

| Lake | Toolchain | sorry (production) | Modules | Notebook câblé | Classe | Suivi |
|------|-----------|--------------------:|--------:|---------------:|--------|-------|
| `erc20_lean` | v4.32.1 | 0 | 4 | 2¹ | PEDA/REF (blockchain) | #4047, #4038 |
| **Total** | — | **0** | **4** | **2** | — | — |

¹ Deux notebooks câblés sous `SymbolicAI/Lean/` : **Lean-24** (ERC20 Invariant
Companion) et **Lean-24b** (ERC20 Native Companion, kernel `lean4-wsl` — modules du lake
visitables in-kernel). Companion conceptuel = le notebook **SC-7** (ERC-20 en
Solidity — convention sibling-lake). Premier lake Lean de la série SmartContracts.

---

## Par lake

### erc20_lean — PEDAGOGIQUE / REFERENCE

**Objectif** : **invariant de conservation** d'un jeton ERC-20 — la somme des soldes de
tous les comptes est toujours égale au `totalSupply`. Formalisation des méthodes formelles
appliquées à la blockchain (roadmap #4038 Tier 1, #4047).

- **Toolchain** : v4.32.1 · **Dépendance** : Mathlib4
- **lib** : `ERC20` (`globs := #[.submodules \`ERC20]`)
- **Modules** : `ERC20/State.lean`, `ERC20/Ops.lean`, `ERC20/Invariant.lean` + umbrella
  `ERC20.lean`
- **sorry (production)** : **0** (real-mode). CI verte sur main
  (`lean-erc20.yml`, dernier run main 2026-08-18).

#### Théorèmes prouvés (0 sorry)

- **`reachable_preserves_invariant`** (flagship) : tout état atteignable depuis l'état
  initial satisfait `∑ balances = totalSupply`.
- **`mint_preserves_supply`** / **`burn_preserves_supply`** / **`transfer_preserves_supply`**
  : chacune des trois opérations préserve l'invariant.
- **`transfer_no_underflow`** : un transfert ne produit pas de solde négatif (pas de
  débordement arithmétique).
- `balance_le_totalSupply`, `op_preserves_invariant` (lemmes de support).

#### Honnêteté du périmètre (G.3/G.9)

L'**invariant de conservation ERC-20** est prouvé 0 sorry (via extraction additive par
`conv_lhs` + `Finset.insert_erase`). Ce qui reste **OPEN (non sorry-backed)**, documenté
honnêtement :

- **Sémantique d'approbation / allowance** (`approve`/`transferFrom`) et l'invariant
  composé balances+allowances.
- **Safety vis-à-vis du reentrancy** (modèle opérationnel multi-appels).

Axiomes `[propext, Classical.choice, Quot.sound]` (Mathlib standard, **pas de `sorryAx`**).

## Notes transverses

- **Mathlib v4.31.0-rc1 Finset sum binder** (documenté durably) : le binder de somme est
  unicode **`∑ x ∈ s`**, PAS le mot `in` (`∑ x in s` ne parse pas) ; extraction additive via
  `conv_lhs` + `Finset.insert_erase` ; mots-clés `to`/`from` → `src`/`dst`. Cf.
  `lean-finset-sum-binder-elem`.
- **WDAC workaround** (RECOVERABLE-LOCAL) : `lake exe cache get` bloqué → copie wholesale
  des oleans d'un lake frère compatible. Cf.
  `lean-wdac-olean-wholesale-copy`.
- CI : `.github/workflows/lean-erc20.yml` (`sorry-filter-mode: real`, baseline `"0"` ;
  bascule mode #11688).
