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

---

**English — Soundness of the propagation rules.**

Issue #4055. Sudoku solvers (backtracking, OR-Tools, the .NET solvers of the `Sudoku`
series) speed up resolution by **propagating** constraints: as soon as a value is placed,
the candidates that have become impossible are eliminated. Two canonical rules:

- **Naked single**: a cell whose only remaining candidate is `v` must contain `v`.
- **Hidden single**: a value that can go in only one cell of a scope must go there.

This module proves the **soundness** of these rules: they **remove no valid solution** —
eliminating a candidate via propagation means eliminating an assignment that **no
solution uses**. The keystone is `peer_excludes_value`: an assigned cell excludes its
value from all its peers.

**Honest scoping (G.3/G.9).** The soundness of both propagation rules is proved in full
(0 `sorry`). The **Sudoku ⇔ exact-cover reduction** (Knuth, 4 constraint families), as
well as completeness (do the rules suffice to solve every Sudoku? no in general — hence
backtracking), are natural milestones left **open**, deliberately **not `sorry`-backed**:
the library remains entirely `sorry`-free. The massive-computation "17-clue minimum"
result is out of scope (not formalisable).
-/

namespace Sudoku

/-! ## Clé de voûte : exclusion par les paires -/

/-- **Clé de voûte.** Dans une solution, une cellule `c` portant la valeur `v` exclut
    `v` de toute cellule **paire** `c'` (même portée) : `σ c' ≠ v`. C'est le fait
    fondamental dont dérivent toutes les règles de propagation.

    **Preuve** (0 `sorry`) : `c` et `c'` partagent une portée `s` ; `σ` est
    toutes-distinctes sur `s`, donc `σ c = σ c'` impliquerait `c = c'`, contredisant
    `c ≠ c'` (définition de paire).

    **Keystone.** In a solution, a cell `c` carrying the value `v` excludes `v` from
    every **peer** cell `c'` (same scope): `σ c' ≠ v`. This is the fundamental fact from
    which all propagation rules derive.

    **Proof** (0 `sorry`): `c` and `c'` share a scope `s`; `σ` is all-distinct on `s`, so
    `σ c = σ c'` would imply `c = c'`, contradicting `c ≠ c'` (the definition of peer). -/
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
    de porter `σ c`. Contradiction.

    **Naked single (soundness).** If, in a solution `σ`, every value but `v` is already
    carried by a **peer** of `c` (i.e. each `w ≠ v` occurs on a peer cell of `c`), then
    `σ c = v`.

    This is the formalisation of the "naked single": cell `c` has only `v` left as a
    possible candidate (every other value is excluded by its peers), so every solution
    places `v` there. The rule removes no solution because it identifies a **forced**
    value.

    **Proof** (0 `sorry`): by contradiction, `σ c = w ≠ v`. By the coverage hypothesis,
    `w` occurs on a peer `c'` of `c`; but `peer_excludes_value` forbids `c'` from
    carrying `σ c`. Contradiction. -/
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
    interdit à `c''` de porter `σ c0 = v`. Contradiction. Donc `c0 = c`, `σ c = v`.

    **Hidden single (soundness).** If, in a solution `σ` of the structure `scopes`, the
    value `v` is present in the scope `s` (`PresentIn σ s v`), `c ∈ s`, and `v` is
    **excluded** from every other cell `c' ∈ s` (each `c' ≠ c` has a peer carrying `v`),
    then `σ c = v`.

    This is the formalisation of the "hidden single": within a scope, `v` can only go in
    `c`, so every solution places it there. For a "full house" scope (`|s| = |V|`), the
    hypothesis `PresentIn σ s v` is automatic (every value occurs).

    **Proof** (0 `sorry`): `v` occurs at `c0 ∈ s`. If `c0 ≠ c`, the exclusion hypothesis
    gives a peer `c''` of `c0` carrying `v`; but `peer_excludes_value` forbids `c''` from
    carrying `σ c0 = v`. Contradiction. Hence `c0 = c`, so `σ c = v`. -/
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
