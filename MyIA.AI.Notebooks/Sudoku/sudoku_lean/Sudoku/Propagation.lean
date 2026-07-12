import Mathlib
import Sudoku.Basic

/-!
# Sudoku.Propagation — soundness des règles de propagation

Issue #4055. Les solveurs Sudoku (backtracking, OR-Tools, .NET de la série `Sudoku`)
accélèrent la résolution en **propageant** les contraintes : dès qu'une valeur est
placée, on élimine les candidats devenus impossibles. Deux règles canoniques :

- **Naked single** : une cellule dont le seul candidat restant est `v` doit contenir `v`.
- **Hidden single** : une valeur qui ne peut aller que dans une seule cellule d'une
  portée doit y aller.

Ce module prouve la **soundness** de ces règles : elles **ne retirent aucune solution
valide** — éliminer un candidat via la propagation, c'est éliminer une affectation
qu'**aucune solution n'utilise**. La clé de voûte est `peer_excludes_value` : une cellule
affectée exclut sa valeur de toutes ses paires.

**Cadrage honnête (G.3/G.9).** La soundness des deux règles de propagation est prouvée
intégralement (0 `sorry`). La **réduction Sudoku ⇔ couverture exacte** (Knuth, 4
familles de contraintes), ainsi que la complétude (les règles suffisent-elles à résoudre
tout Sudoku ? non en général — d'où le backtracking), sont des jalons naturels laissés
**ouverts**, délibérément **non `sorry`-backed** : la bibliothèque reste entièrement
`sorry`-free. Le résultat de calcul massif « 17 indices minimum » est hors scope
(non formalisable).
-/

namespace Sudoku

/-! ## Clé de voûte : exclusion par les paires -/

/-- **Clé de voûte.** Dans une solution, une cellule `c` portant la valeur `v` exclut
    `v` de toute cellule **paire** `c'` (même portée) : `σ c' ≠ v`. C'est le fait
    fondamental dont dérivent toutes les règles de propagation.

    **Preuve** (0 `sorry`) : `c` et `c'` partagent une portée `s` ; `σ` est
    toutes-distinctes sur `s`, donc `σ c = σ c'` impliquerait `c = c'`, contredisant
    `c ≠ c'` (définition de paire). -/
theorem peer_excludes_value {ι V : Type*} [Fintype ι] [DecidableEq ι] [Fintype V]
    [DecidableEq V] (scopes : Scopes ι) (σ : Solution ι V)
    (hσ : IsSolution scopes σ) (c c' : ι) (v : V)
    (hpeer : IsPeer scopes c c') (hcv : σ c = v) :
    σ c' ≠ v := by
  obtain ⟨hcc', s, hs, hcs, hc's⟩ := hpeer
  intro hc'v
  have hcc : c = c' := hσ s hs hcs hc's (hcv.trans hc'v.symm)
  exact hcc' hcc

/-! ## Naked single -/

/-- **Naked single (soundness).** Si, dans une solution `σ`, toutes les valeurs sauf `v`
    sont déjà portées par des **paires** de `c` (i.e. chaque `w ≠ v` apparaît sur une
    cellule paire de `c`), alors `σ c = v`.

    C'est la formalisation du « naked single » : la cellule `c` n'a plus que `v` comme
    candidat possible (toutes les autres valeurs sont exclues par ses paires), donc
    toute solution y place `v`. La règle ne retire aucune solution car elle identifie
    une valeur **forcée**.

    **Preuve** (0 `sorry`) : par l'absurde, `σ c = w ≠ v`. Par l'hypothèse de couverture,
    `w` apparaît sur une paire `c'` de `c` ; mais `peer_excludes_value` interdit à `c'`
    de porter `σ c`. Contradiction. -/
theorem naked_single_sound {ι V : Type*} [Fintype ι] [DecidableEq ι] [Fintype V]
    [DecidableEq V] (scopes : Scopes ι) (σ : Solution ι V)
    (hσ : IsSolution scopes σ) (c : ι) (v : V)
    (hcover : ∀ w : V, w ≠ v → ∃ c' : ι, IsPeer scopes c c' ∧ σ c' = w) :
    σ c = v := by
  by_contra hne
  obtain ⟨c', hpeer, hc'w⟩ := hcover (σ c) hne
  exact peer_excludes_value scopes σ hσ c c' (σ c) hpeer rfl hc'w

/-! ## Hidden single -/

/-- **Hidden single (soundness).** Si, dans une solution `σ` de la structure `scopes`,
    la valeur `v` est présente dans la portée `s` (`PresentIn σ s v`), que `c ∈ s`, et
    que `v` est **exclue** de toute autre cellule `c' ∈ s` (chaque `c' ≠ c` a une paire
    portant `v`), alors `σ c = v`.

    C'est la formalisation du « hidden single » : dans une portée, `v` ne peut aller que
    dans `c`, donc toute solution l'y place. Pour une portée « pleine maison »
    (`|s| = |V|`), l'hypothèse `PresentIn σ s v` est automatique (toute valeur apparaît).

    **Preuve** (0 `sorry`) : `v` apparaît en `c0 ∈ s`. Si `c0 ≠ c`, l'hypothèse
    d'exclusion donne une paire `c''` de `c0` portant `v` ; mais `peer_excludes_value`
    interdit à `c''` de porter `σ c0 = v`. Contradiction. Donc `c0 = c`, `σ c = v`. -/
theorem hidden_single_sound {ι V : Type*} [Fintype ι] [DecidableEq ι] [Fintype V]
    [DecidableEq V] (scopes : Scopes ι) (σ : Solution ι V)
    (hσ : IsSolution scopes σ) (s : Finset ι) (_hs : s ∈ scopes)
    (c : ι) (v : V) (_hcs : c ∈ s)
    (hvin : PresentIn σ s v)
    (hexcl : ∀ c' ∈ s, c' ≠ c → ∃ c'' : ι, IsPeer scopes c' c'' ∧ σ c'' = v) :
    σ c = v := by
  obtain ⟨c0, hc0s, hc0v⟩ := hvin
  by_contra hne
  have hc0c : c0 ≠ c := fun heq => hne (heq ▸ hc0v)
  obtain ⟨c'', hpeer, hc''v⟩ := hexcl c0 hc0s hc0c
  exact peer_excludes_value scopes σ hσ c0 c'' v hpeer hc0v hc''v

end Sudoku
