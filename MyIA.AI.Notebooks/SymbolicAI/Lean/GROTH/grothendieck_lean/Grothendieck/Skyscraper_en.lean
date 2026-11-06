/-
Grothendieck tribute — Part 77: the skyscraper sheaf, support and stalks.

Alexandre Grothendieck (1928-2014).

Phase 2 extension (#2159, Epic #1646).

A skyscraper sheaf is a presheaf "concentrated" at a point: its value on an
open set `U` is `A` if `p₀ ∈ U`, and a terminal object otherwise. Mathlib
computes its stalks, but separately:

  - `skyscraperPresheafStalkOfSpecializes`: if `p₀ ⤳ y`, then
    `(skyscraperPresheaf p₀ A).stalk y ≅ A`;
  - `skyscraperPresheafStalkOfNotSpecializes`: if `¬ p₀ ⤳ y`, then
    `(skyscraperPresheaf p₀ A).stalk y ≅ terminal C`;
  - `skyscraperPresheafStalkOfNotSpecializesIsTerminal`: the same content as
    the previous one, stated directly as `IsTerminal` of the stalk.

What Mathlib states **nowhere** is the notion of the *support* of a presheaf,
nor the computation of the skyscraper's support: `grep -rn "def support"` over
`Mathlib/Topology/Sheaves/` returns nothing, and the five occurrences of the
word in `Mathlib/Topology/Sheaves/Skyscraper.lean` (lines 16, 17, 55, 246, 431)
are docstring prose, never a statement. That is what this part adds: we define
the **support** of a presheaf as the set of points where its stalk is **not**
terminal, and we show

  `support_skyscraper : support (skyscraper p₀ A) = closure {p₀}`

that is, the skyscraper is supported **exactly** on the closure of `{p₀}` —
provided the value `A` is not itself terminal (without that hypothesis, a
skyscraper with terminal value is terminal at every point and its support is
empty, whatever `p₀` may be). The name of the sheaf is then justified: if `p₀`
is a closed point, the support is the singleton `{p₀}`
(`support_skyscraper_of_closed`).

The proof is a transport of `IsTerminal` along an isomorphism, in both
directions, and that is where the content lies: the `⊆` direction transports
`IsTerminal A` to the stalk through the specialization iso, so a terminal stalk
forces `A` terminal, contradicting the hypothesis; the `⊇` direction transports
the non-specialization iso to the terminal object. Neither isomorphism is
superfluous, and the hypothesis `IsEmpty (IsTerminal A)` is necessary — it is
named, not implicit.

CoursIA vocabulary ↔ exact Mathlib hypotheses: the specialization order `⤳` and
the closure are related by `specializes_iff_mem_closure`, so that Mathlib's
hypotheses (`p₀ ⤳ y`, `¬ p₀ ⤳ y`) are stated here in terms of closure, which is
the expected geometric reading.

References:
  - SGA 4, IV 6.3 (stalks and points of a site).
  - S. Mac Lane, I. Moerdijk, *Sheaves in Geometry and Logic* [MM92],
    Chap. II §4 (skyscraper sheaves, support).
  - Mathlib, `Mathlib.Topology.Sheaves.Skyscraper`.
  - Part 72 (`Grothendieck.Stalks`): concrete germs and stalks.
  - Part 73 (`Grothendieck.StalkPoints`): the stalk is the fibre functor.
  - Part 76 (`Grothendieck.StalkCharacterization`): the characterization of a
    sheaf by its stalks, of which this part is the application to a presheaf
    whose stalks are computable.

i18n convention (EPIC #4980 ratified 2026-07-04): this module is paired with
`Skyscraper.lean`. Statements, proofs and Lean names remain identical; only
docstrings and comments differ.

Epic #1646, Phase 2 (#2159). No `sorry` introduced.
-/

import Grothendieck.Spaces
import Mathlib.Topology.Inseparable
import Mathlib.Topology.Sheaves.Skyscraper

namespace Grothendieck.Skyscraper_en

open CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace

universe u v

namespace Contenu

variable {X : TopCat.{u}} (p₀ : X) [∀ U : Opens X, Decidable (p₀ ∈ U)]
-- Mathlib restricts the universe level of the morphisms of `C` to that of the points of `X`
-- in order to compute the stalks of the skyscraper (cf. `Skyscraper.lean`, section "We need to
-- restrict universe level"). The constraint is inherited, not chosen here.
variable {C : Type v} [Category.{u} C] [HasTerminal C] [HasColimits C]

/-- The skyscraper presheaf with value `A` at the point `p₀`: `A` on the open
sets containing `p₀`, a terminal object otherwise. CoursIA vocabulary for
`skyscraperPresheaf`, of which it duplicates no structure. -/
noncomputable abbrev skyscraper (A : C) : Presheaf C X := skyscraperPresheaf p₀ A

/-- **Support** of a presheaf: the set of points where its stalk is not a
terminal object. This is the notion that Mathlib's two isomorphisms allow one to
compute for the skyscraper. -/
def support (F : Presheaf C X) : Set X := {y | IsEmpty (IsTerminal (F.stalk y))}

/-- Inside the closure of `{p₀}`: if `y ∈ closure {p₀}`, the stalk of the
skyscraper at `y` is `A`. Direct application of
`skyscraperPresheafStalkOfSpecializes` under its exact hypothesis, translated
into closure.

This statement does **not** assume `IsEmpty (IsTerminal A)`: it bears on the
closure, not on the support. The two notions coincide only under that
hypothesis (cf. `support_skyscraper`), which is why the docstring does not say
"on the support". -/
noncomputable def stalkIsoOfMemClosure (A : C) {y : X}
    (h : y ∈ closure ({p₀} : Set X)) : (skyscraper p₀ A).stalk y ≅ A :=
  skyscraperPresheafStalkOfSpecializes p₀ A (specializes_iff_mem_closure.mpr h)

/-- Outside the closure of `{p₀}`: if `y ∉ closure {p₀}`, the stalk of the
skyscraper at `y` is a terminal object. Direct application of
`skyscraperPresheafStalkOfNotSpecializes`.

Like its counterpart, this statement does not assume
`IsEmpty (IsTerminal A)`: without it, "outside the closure" is **not** "off the
support". -/
noncomputable def stalkIsoOfNotMemClosure (A : C) {y : X}
    (h : y ∉ closure ({p₀} : Set X)) : (skyscraper p₀ A).stalk y ≅ terminal C :=
  skyscraperPresheafStalkOfNotSpecializes p₀ A
    (fun hs => h (specializes_iff_mem_closure.mp hs))

/-- **The support of the skyscraper is exactly the closure of `{p₀}`.** This is
the result this part assembles: Mathlib states the two stalk isomorphisms
separately, this one says what their union means.

The hypothesis `IsEmpty (IsTerminal A)` is necessary and not decorative:
without it, a skyscraper with terminal value has all its stalks terminal, hence
an empty support, whereas `closure {p₀}` is nonempty. The two directions of the
proof transport `IsTerminal` along an isomorphism (`IsTerminal.ofIso`), each
through one of Mathlib's two isomorphisms.

Note on universes and on the value of `IsTerminal` in this Mathlib:
`IsTerminal` is not a `Prop` but a **type** ("transport a *term* of type
`IsTerminal`" in `IsTerminal.lean`), hence `IsEmpty (IsTerminal _)` and not
`¬ IsTerminal _` to say "is not terminal". -/
theorem support_skyscraper (A : C) (hA : IsEmpty (IsTerminal A)) :
    support (skyscraper p₀ A) = closure ({p₀} : Set X) := by
  ext y
  change IsEmpty (IsTerminal ((skyscraper p₀ A).stalk y)) ↔ y ∈ closure ({p₀} : Set X)
  constructor
  · intro hy
    by_contra hc
    exact hy.false
      (IsTerminal.ofIso terminalIsTerminal (stalkIsoOfNotMemClosure p₀ A hc).symm)
  · intro hmem
    exact ⟨fun hterm => hA.false (IsTerminal.ofIso hterm (stalkIsoOfMemClosure p₀ A hmem))⟩

/-- **The name of the sheaf is justified.** If `p₀` is a closed point, the
support of the skyscraper is the singleton `{p₀}`: the presheaf is concentrated
at a single point, exactly as its name announces. Immediate corollary of
`support_skyscraper` via `closure {p₀} = {p₀}`. -/
theorem support_skyscraper_of_closed (A : C) (hA : IsEmpty (IsTerminal A))
    (hcl : IsClosed ({p₀} : Set X)) :
    support (skyscraper p₀ A) = {p₀} := by
  rw [support_skyscraper p₀ A hA, hcl.closure_eq]

/-- **Dichotomy of stalks.** Under `IsEmpty (IsTerminal A)` — the hypothesis
that identifies the support with the closure of `{p₀}` (cf.
`support_skyscraper`) — the stalk of the skyscraper at every point `y` is either
`A` or terminal, and the point is located in the **support** or outside it
accordingly. This is the "at every point" form of what `support_skyscraper`
states over the set of points: the support is not merely described there, it is
decided point by point.

The hypothesis `hA` is indispensable to this statement, and not only to its
proof: without it, `y ∈ closure {p₀}` says nothing about the support, as the
counterexample of `support_skyscraper` shows (terminal value: all stalks
terminal, empty support, non-empty closure). -/
theorem stalk_dichotomy (A : C) (hA : IsEmpty (IsTerminal A)) (y : X) :
    (y ∈ support (skyscraper p₀ A) ∧ Nonempty ((skyscraper p₀ A).stalk y ≅ A)) ∨
      (y ∉ support (skyscraper p₀ A) ∧
        Nonempty ((skyscraper p₀ A).stalk y ≅ terminal C)) := by
  rw [support_skyscraper p₀ A hA]
  by_cases h : y ∈ closure ({p₀} : Set X)
  · exact Or.inl ⟨h, ⟨stalkIsoOfMemClosure p₀ A h⟩⟩
  · exact Or.inr ⟨h, ⟨stalkIsoOfNotMemClosure p₀ A h⟩⟩

end Contenu

end Grothendieck.Skyscraper_en
