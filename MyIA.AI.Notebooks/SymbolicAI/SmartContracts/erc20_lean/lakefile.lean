import Lake
open Lake DSL

/-!
# Mini-projet Lean pédagogique : invariant de conservation d'un jeton ERC-20

Projet Lean 4 (avec Mathlib) formalisant l'**invariant de conservation fondateur
d'un jeton ERC-20 fongible** : la somme des soldes de toutes les adresses égale
l'offre totale, et cet invariant est préservé par chaque opération standard
(`transfer`, `mint`, `burn`). Voir l'issue #4047 (roadmap #4038).

C'est un cas d'école du lien entre méthodes formelles et blockchain, ultra-topical
et **concret** : on démontre la valeur de la preuve formelle sur du code « réel »
que les étudiants reconnaissent (le standard ERC-20 de Solidity). La série
SmartContract n'avait aucun lake Lean jusque-là.

Modèle : machine à états finie. Les adresses sont `Fin n` (un nombre fini de
détenteurs potentiels), les soldes `Address → ℕ`, l'offre totale un `ℕ`.
`supplyInvariant s := ∑ a, s.balances a = s.totalSupply`. Les opérations sont des
transitions gardées (solde suffisant pour `transfer`/`burn`, pas d'underflow).

Notebook compagnon (`SC-7-Token-Standards.ipynb`, série SmartContract) :
présentation pédagogique du jeton + vérification formelle côte à côte avec
l'implémentation Solidity. Le câblage du notebook revient au propriétaire de la
série SmartContract.
-/

package «erc20_lean» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.31.0-rc1"

@[default_target]
lean_lib «ERC20» where
  globs := #[.submodules `ERC20]
