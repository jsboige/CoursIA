import Mathlib
import ERC20.State

/-!
# ERC20.Ops — transitions gardées (transfer, mint, burn)

Les trois opérations standard d'un jeton ERC-20, vues comme des transitions
gardées de l'état. Les gardes (`solde suffisant`) garantissent l'absence
d'underflow : un `transfer`/`burn` ne peut retirer plus que le solde présent.

Note : les noms `src`/`dst` (source/destination) substituent les paramètres
ERC-20 usuels `from`/`to`, qui sont des mots-clés réservés en Lean 4.
-/

namespace ERC20

variable {n : ℕ}

open ERC20

/-- `mint dst amount` : frappe `amount` tokens crédités au compte `dst`, et
    augmente l'offre totale du même montant. (Opération privilégiée du
    propriétaire du contrat.) -/
def mint (s : State n) (dst : Address n) (amount : ℕ) : State n :=
  { balances := fun a => if a = dst then s.balances a + amount else s.balances a
    totalSupply := s.totalSupply + amount }

/-- `burn src amount` : brûle `amount` tokens au compte `src` (garde implicite :
    solde suffisant), et diminue l'offre totale du même montant. -/
def burn (s : State n) (src : Address n) (amount : ℕ) : State n :=
  { balances := fun a => if a = src then s.balances a - amount else s.balances a
    totalSupply := s.totalSupply - amount }

/-- `transfer src dst amount` : transfère `amount` tokens de `src` vers `dst`.
    L'offre totale est inchangée (déplacement interne de tokens). Le solde du
    compte source doit couvrir `amount` (garde, vérifiée dans
    `transfer_no_underflow`). -/
def transfer (s : State n) (src dst : Address n) (amount : ℕ) : State n :=
  { balances := fun a =>
      if a = src then s.balances a - amount
      else if a = dst then s.balances a + amount
      else s.balances a
    totalSupply := s.totalSupply }

end ERC20
