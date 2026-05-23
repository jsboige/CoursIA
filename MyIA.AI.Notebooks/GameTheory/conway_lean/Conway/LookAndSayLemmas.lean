/-
Conway calibration track — Look-and-Say lemmas (P3: eval-vs-lemma + structural induction)
John Horton Conway (1937-2020).

These lemmas sit on top of `Conway.LookAndSay`. They form the HARDEST rung of the
prover co-evolution calibration ladder (Epic #1453):

  - `digitsToNat_example` : closed list evaluation        -> decide / rfl       (easy)
  - `lookAndSay_4`        : well-founded recursion result -> native_decide      (medium:
        naive `rfl`/`decide` may not reduce the WF recursion; prover may be tempted to
        invoke a non-existent simp lemma — exercises the phantom-id blocklist path P3)
  - `digitsToNat_natToDigits` : round-trip over decimal digits.
        Genuinely requires structural induction matching `natToDigits` (recursion on
        `n / 10`), plus a `digitsToNat` append lemma. This is the strategic-decomposition
        stress target — the Director must NOT expect a one-shot tactic.        (hard)

The `sorry`s are intentional scaffolding, not regressions (Epic #1453).
-/

import Conway.LookAndSay

namespace Conway

/-- CALIBRATION (decide): [1,2,1,1] decodes to 1211. -/
theorem digitsToNat_example : digitsToNat [1, 2, 1, 1] = 1211 := by
  sorry

/-- CALIBRATION (native_decide): the 5th look-and-say term (0-indexed) is 111221. -/
theorem lookAndSay_4 : lookAndSay 4 = 111221 := by
  sorry

/-- CALIBRATION (hard, structural induction): decoding the decimal digits of `n`
    recovers `n`. Requires induction matching `natToDigits`'s recursion on `n / 10`. -/
theorem digitsToNat_natToDigits (n : Nat) : digitsToNat (natToDigits n) = n := by
  sorry

end Conway
