import Mathlib.Data.Nat.Basic

namespace SmokeTest

theorem zero_add_smoke (n : Nat) : 0 + n = n := by
  exact Nat.zero_add n

end SmokeTest
