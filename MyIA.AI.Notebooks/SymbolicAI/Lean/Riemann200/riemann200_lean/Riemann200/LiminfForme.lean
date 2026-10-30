/-
# La forme epsilon du théorème A, face à Mathlib

Module du grain R-12 de l'EPIC #20403 (issue #23141) : le langage exact
dans lequel le théorème A d'Alpöge–Furman (arXiv:2608.13637) est énoncé —
« plus des deux tiers des zéros de zêta sont simples et sur la droite
critique », au sens d'un `liminf` — et ce que ce langage implique
mécaniquement.

L'énoncé du papier est une affirmation asymptotique :
`N₀ˢ(T,2T) ≥ (2/3 − o(1)) N(T,2T)`. La « fonction o(1) » n'est pas une
fonction qu'on peut évaluer : l'énoncé rigoureux est une inégalité de
`liminf`, et sa lecture opérationnelle est la **forme epsilon** — pour
tout ε > 0, il existe un T₀ tel qu'au-delà, la proportion dépasse c − ε.
Ce module prouve cette mise en forme, sa monotonie en la constante c, et
le passage de la proportion au comptage `(c − ε)·N(T) ≤ X(T)` utilisé
dans le carnet R-12.

## Grounding mesuré (convention de la série)

- Mathlib **ne porte pas** la fonction ζ ni ses zéros (v4.33.0, greppé au
  grain 1) : le théorème A lui-même est hors de portée formelle ici, et
  ce module ne le prétend pas.
- Mathlib **porte** : `Filter.liminf` et ses caractérisations
  (`Mathlib.Order.LiminfLimsup` — `le_liminf_iff`, `eventually_lt_of_lt_liminf`,
  dont les hypothèses de bornitude sont celles que ce module expose telles
  quelles), la caractérisation « ∃ T₀, ∀ T ≥ T₀ » de `atTop`
  (`Mathlib.Order.Filter.AtTopBot.Basic`, `eventually_atTop`).
- Le carnet R-12 rend les comptages **calculables** (`mpmath.zetazero`) ;
  ce module rend leur **forme** formelle. Les deux ne se rencontrent pas :
  aucune donnée du carnet n'est vendue ici.
-/

import Mathlib.Order.LiminfLimsup
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic

namespace Riemann200

open Filter

/-- **Forme epsilon du liminf.** `liminf f ≥ c` si et seulement si pour
tout ε > 0 il existe un seuil T₀ au-delà duquel `f` dépasse `c − ε`.
C'est la seule lecture **opérationnelle** d'un énoncé en `liminf` : une
fenêtre finie ne peut jamais le confirmer ni le réfuter (elle ne voit
que des T particuliers), mais elle peut mesurer la proportion courante —
c'est exactement ce que fait le carnet R-12 à T fini. Le sens réciproque
est la moitié utile : une famille de fenêtres gagnantes pour tout ε
certifie le `liminf`.

Les deux hypothèses de bornitude sont celles que Mathlib exige pour que
le `liminf` d'une fonction réelle soit bien défini côté `sSup` (ℝ
n'est pas complet) ; une proportion à valeurs dans [0, 1] les satisfait
les deux (bornée par 0, cobornée par 1). -/
theorem liminf_ge_iff_eps (f : ℝ → ℝ) (c : ℝ)
    (hco : Filter.IsCoboundedUnder (· ≥ ·) Filter.atTop f)
    (hbdd : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop f) :
    c ≤ Filter.liminf f Filter.atTop ↔
      ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, c - ε < f T := by
  constructor
  · intro h ε hε
    have h1 : c - ε < c := by linarith
    have hlt : c - ε < Filter.liminf f Filter.atTop :=
      lt_of_lt_of_le h1 h
    have hev := Filter.eventually_lt_of_lt_liminf hlt hbdd
    rw [Filter.eventually_atTop] at hev
    obtain ⟨T₀, hT₀⟩ := hev
    exact ⟨T₀, fun T hT => hT₀ T hT⟩
  · intro h
    by_contra hnc
    push Not at hnc
    obtain ⟨T₀, hT₀⟩ := h ((c - Filter.liminf f Filter.atTop) / 2)
      (div_pos (sub_pos.mpr hnc) two_pos)
    have hEq : c - (c - Filter.liminf f Filter.atTop) / 2
        = (c + Filter.liminf f Filter.atTop) / 2 := by ring
    have hev : ∀ᶠ T in Filter.atTop,
        (c + Filter.liminf f Filter.atTop) / 2 ≤ f T := by
      rw [Filter.eventually_atTop]
      refine ⟨T₀, fun T hT => le_of_lt ?_⟩
      rw [← hEq]
      exact hT₀ T hT
    have hle := Filter.le_liminf_of_le hco hev
    linarith

/-- **Monotonie en la constante.** Ce que le théorème A garantit à
`c = 2/3` est garanti pour toute constante plus petite — en particulier
pour les records antérieurs (`5/12 ≈ 0,4167`, puis `0,6603`) : chaque
nouveau record **hérite** de tous les énoncés plus faibles. Inversement,
la difficulté mathématique vit tout entière dans l'écart `2/3 − 0,6603` :
ce module ne dit rien de lui. -/
theorem liminf_ge_mono (f : ℝ → ℝ) {c c' : ℝ}
    (h : c ≤ Filter.liminf f Filter.atTop) (hle : c' ≤ c) :
    c' ≤ Filter.liminf f Filter.atTop :=
  le_trans hle h

/-- **De la proportion au comptage.** Si pour tout ε > 0 la proportion
`X/N` finit par dépasser `c − ε` (la forme epsilon du `liminf ≥ c`, cf
`liminf_ge_iff_eps`) et si le dénominateur `N` reste strictement positif
au-delà d'un seuil (vérifié pour un comptage de zéros, qui tend vers
l'infini), alors pour tout ε > 0 la fenêtre `(c − ε)·N(T) ≤ X(T)`
s'ouvre et reste ouverte. C'est la forme exacte sous laquelle le carnet
R-12 compare les records à ses mesures : la conclusion porte sur les
**comptages**, pas seulement sur leur rapport. -/
theorem proportion_depuis_eps (N X : ℝ → ℝ) (c : ℝ)
    (h : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, c - ε < X T / N T)
    (hN : ∀ᶠ T in Filter.atTop, 0 < N T) :
    ∀ ε > 0, ∃ T₁ : ℝ, ∀ T ≥ T₁, (c - ε) * N T ≤ X T := by
  intro ε hε
  obtain ⟨T₀, h₀⟩ := h ε hε
  rw [Filter.eventually_atTop] at hN
  obtain ⟨T₂, h₂⟩ := hN
  refine ⟨max T₀ T₂, fun T hT => ?_⟩
  have hNpos : 0 < N T := h₂ T (le_trans (le_max_right T₀ T₂) hT)
  have hlt : (c - ε) * N T < (X T / N T) * N T :=
    mul_lt_mul_of_pos_right (h₀ T (le_trans (le_max_left T₀ T₂) hT)) hNpos
  rw [div_mul_cancel₀ _ (ne_of_gt hNpos)] at hlt
  exact le_of_lt hlt

end Riemann200
