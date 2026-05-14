# Lake Cache Nuke Procedure

When `lake build` fails with stale cache artifacts (e.g., after toolchain bumps,
Mathlib updates, or cross-branch switches), a simple `lake clean` is insufficient.
Lake uses content-addressable caching and `.olean.hash`/`.ilean.hash`/`.trace` files
that survive `lake clean`.

## When to use

- `lake build` errors referencing `.olean` mismatches or stale imports
- After switching Lean toolchain versions (e.g., v4.28.0-rc1 -> v4.30.0-rc2)
- After `git checkout` between branches with different Mathlib pins
- After `lake exe cache get` downloads corrupt artifacts
- `unknown definition` or `declaration has '?'` errors that don't match source

## Procedure

```bash
# 1. Clean standard build artifacts
lake clean

# 2. Nuke ALL Lake cache directories (content-addressable)
rm -rf .lake/build/lib/lean/CooperativeGames/
rm -rf .lake/build/ir/CooperativeGames/
rm -rf .lake/build/lib/lean/Mathlib/
rm -rf .lake/build/ir/Mathlib/
rm -rf .lake/build/lib/lean/Lean/
rm -rf .lake/build/ir/Lean/

# 3. Remove hash files (these bypass content checks)
find .lake/build -name "*.olean.hash" -delete
find .lake/build -name "*.ilean.hash" -delete
find .lake/build -name "*.trace" -delete

# 4. Rebuild from scratch
lake build
```

## WSL variant (from Windows)

```powershell
wsl -e bash -c "cd /mnt/c/dev/CoursIA/MyIA.AI.Notebooks/GameTheory/cooperative_games_lean && lake clean && rm -rf .lake/build/lib/lean/CooperativeGames .lake/build/ir/CooperativeGames && find .lake/build -name '*.olean.hash' -delete && find .lake/build -name '*.ilean.hash' -delete && find .lake/build -name '*.trace' -delete && lake build"
```

## Nuclear option (last resort)

If the above doesn't resolve, delete the entire `.lake/` directory:

```bash
rm -rf .lake/
lake build
```

Warning: this triggers a full Mathlib rebuild (~10-30 min depending on hardware).

## Root cause

Lake's cache is content-addressable: each `.olean` file is paired with a
`.olean.hash` file containing its content hash. When the toolchain changes,
the hash scheme may differ, but Lake trusts the hash file if it exists.
Similarly, `.trace` files record build dependencies and can become stale.

`lake clean` only removes `.olean`/`.ilean` files, NOT the hash/trace files.
So after `lake clean`, Lake sees "no .olean" but "hash file exists" and may
produce inconsistent rebuilds.

## History

- 2026-05-13: Encountered during toolchain bump v4.28.0-rc1 -> v4.30.0-rc2
- po-2026: `lake clean` alone insufficient, full nuke of hash/trace required
