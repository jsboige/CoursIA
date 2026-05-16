import Lake
open Lake DSL

package «stable-marriage-lean» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.25.0"

lean_lib StableMarriageLean

lean_exe «stable-marriage-lean» where
  root := `Main
