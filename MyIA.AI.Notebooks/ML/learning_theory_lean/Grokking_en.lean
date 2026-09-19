/-
# Grokking — effective theory of representation learning

Root of the `Grokking_en` library (issue #16752, slice R02 of the Tegmark corpus
#16741). Formalizes the short statements of "Towards Understanding Grokking — An
Effective Theory of Representation Learning" (Liu, Michaud, Tegmark,
arXiv:2205.10343):

* `Grokking_en.Effective` — representation parallelograms: Definition 1 and
  Propositions 1-2 (zero loss ⟹ permissible parallelograms; injective decoder ⟹
  formation of parallelograms), plus the set `P₀` of permissible quadruples.
* `Grokking_en.Conservation` — Appendix F: the two symmetries of the loss ℓ₀
  (translation, scaling), conservation of `Z₀` along the flow of `ℓ_eff = ℓ₀/Z₀`,
  conservation of `C` along the flow of `ℓ₀`, and the residual term
  `dC/dt = (2ℓ₀/Z₀²) • C` omitted by the paper's proof — hence the invariance of
  the centered hyperplane `C = 0`.

English mirror of `Grokking.lean` (FR-first canonical), EPIC #4980.
-/
import Grokking.Effective_en
import Grokking.Conservation_en
