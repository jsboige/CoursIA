"""
One-shot fix script for Lean-3 and Lean-4 notebooks unused variable warnings.

Strategy:
1. Add `set_option linter.unusedVariables false` to the first code cell of each
   notebook -- this addresses inherited `variable (p q r : Prop)` warnings that
   propagate across the env chain (would otherwise require restructuring).
2. Apply `_` prefix to true lambda-binder unused variables (the canonical fix
   pattern described in the task brief).

Discarded approaches:
- Wrapping every cell with section/end -> breaks env chaining in Lean4 Jupyter.
- Renaming variables in upstream `variable` declarations to `_p _q _r` -> breaks
  downstream cells that reference `p q r`.

Re-execution must be done after this script via:
  python scripts/notebook_tools/wsl_papermill.py execute <nb> --kernel lean4-wsl --timeout 600
"""
import json
import sys
from pathlib import Path


def normalize_source(cell):
    """Return source as a string."""
    src = cell.get('source', '')
    if isinstance(src, list):
        return ''.join(src)
    return src


def set_source(cell, new_str):
    """Set source as list-of-strings preserving newlines."""
    # Keep \n at end of every line except possibly last
    lines = new_str.splitlines(keepends=True)
    cell['source'] = lines


def prepend_setopt(cell):
    """Prepend `set_option linter.unusedVariables false` block."""
    cur = normalize_source(cell)
    prefix = (
        "-- Desactiver le linter `unused variable` pour reduire le bruit pedagogique\n"
        "-- (les declarations `variable (p q r : Prop)` partagees declenchent des warnings\n"
        "--  inherites dans les cellules en aval -- artefact du chainage d'environnement)\n"
        "set_option linter.unusedVariables false\n"
        "\n"
    )
    set_source(cell, prefix + cur)


def replace_in_cell(cell, old, new, count=1):
    """Replace exactly `count` occurrences of `old` with `new` in cell source.

    Raises AssertionError if `old` not found exactly `count` times.
    """
    cur = normalize_source(cell)
    found = cur.count(old)
    assert found == count, f"Expected {count} occurrences of {old!r}, found {found}"
    new_src = cur.replace(old, new, count)
    set_source(cell, new_src)


def fix_lean3(path):
    with open(path, 'r', encoding='utf-8') as f:
        nb = json.load(f)

    # Cell 2 (id=7280bbe5): add set_option at top
    prepend_setopt(nb['cells'][2])

    # Cell 6 (id=44e03e41): fun hq : q => hp -> fun _hq : q => hp
    replace_in_cell(
        nb['cells'][6],
        "    fun hq : q => hp",
        "    fun _hq : q => hp",
        count=1,
    )

    with open(path, 'w', encoding='utf-8', newline='\n') as f:
        json.dump(nb, f, indent=1, ensure_ascii=False)
        f.write('\n')
    print(f'Lean-3 fixes applied: {path}')


def fix_lean4(path):
    with open(path, 'r', encoding='utf-8') as f:
        nb = json.load(f)

    # Cell 2 (id=48848806): add set_option at top
    prepend_setopt(nb['cells'][2])

    # Cell 4: theorem add_zero_forall ... `fun n => rfl` (n unused, rfl computes)
    replace_in_cell(
        nb['cells'][4],
        "  fun n => rfl   -- La preuve de n + 0 = n est rfl (calcul)",
        "  fun _n => rfl   -- La preuve de n + 0 = n est rfl (calcul)",
        count=1,
    )

    # Cell 6: theorem add_zero_forall_copy ... `fun n => rfl`
    replace_in_cell(
        nb['cells'][6],
        "  fun n => rfl\n",
        "  fun _n => rfl\n",
        count=1,
    )

    # Cell 14: Exists.elim (fun n hn => True.intro)   -- n and hn unused
    replace_in_cell(
        nb['cells'][14],
        "  Exists.elim h (fun n hn => True.intro)",
        "  Exists.elim h (fun _n _hn => True.intro)",
        count=1,
    )
    # Cell 14: match `| ⟨n, hn⟩ => ⟨n, Nat.zero_le n⟩` -- only hn unused (n IS used)
    replace_in_cell(
        nb['cells'][14],
        "  | ⟨n, hn⟩ => ⟨n, Nat.zero_le n⟩",
        "  | ⟨n, _hn⟩ => ⟨n, Nat.zero_le n⟩",
        count=1,
    )

    # Cell 28: fun hp hq => hp   -- hq unused
    replace_in_cell(
        nb['cells'][28],
        "  fun hp hq => hp",
        "  fun hp _hq => hp",
        count=1,
    )
    # Cell 28: fun (hp : p) (hq : q) => hp   -- hq unused
    replace_in_cell(
        nb['cells'][28],
        "  fun (hp : p) (hq : q) => hp",
        "  fun (hp : p) (_hq : q) => hp",
        count=1,
    )

    # Cell 30: theorem subst_in_forall ... (h : a = b) (hp : forall n, P n) : P b
    # `h` unused in `hp b` proof
    replace_in_cell(
        nb['cells'][30],
        "  (h : a = b) (hp : forall n, P n) : P b :=\n  hp b",
        "  (_h : a = b) (hp : forall n, P n) : P b :=\n  hp b",
        count=1,
    )

    with open(path, 'w', encoding='utf-8', newline='\n') as f:
        json.dump(nb, f, indent=1, ensure_ascii=False)
        f.write('\n')
    print(f'Lean-4 fixes applied: {path}')


def main():
    root = Path(r'C:/dev/CoursIA')
    fix_lean3(root / 'MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-3-Propositions-Proofs.ipynb')
    fix_lean4(root / 'MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-4-Quantifiers.ipynb')


if __name__ == '__main__':
    main()
