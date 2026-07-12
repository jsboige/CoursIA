/-
  Knots.Invariant — Knot invariants (3-colorability, crossing number)
  ====================================================================

  Knot invariants distinguish knots. This file scaffolds:
  1. Tricolorability (Fox 1962) — the most accessible invariant
  2. Crossing number bounds
  3. Unknotting number (definition only, sorry)

  Epic #2874, Phase 1–2.

  Mathlib prerequisites needed:
  - Finite colorings of graphs (Fintype, Fin n coloring)
  - Minimization over equivalence classes
-/
/-
  `Knots.Invariant` — invariants des nœuds (3-colorabilité, nombre de croisements)
  ============================================================================

  Invariant de nœud = grandeur attachée à un nœud qui est préservée par
  mouvement de Reidemeister (R1/R2/R3). Ce sous-module scaffolde :

  1. **3-colorabilité (Fox 1962)** — le plus accessible des invariants non
     triviaux : un diagramme de nœud est 3-coloriable si chaque arc peut
     être colorié avec une des trois couleurs (rouge, bleu, vert) de sorte
     qu'à chaque croisement, soit les trois arcs portent la même couleur,
     soit les trois portent des couleurs deux à deux distinctes, ET au
     moins deux couleurs sont effectivement utilisées. Le trèfle (trefoil)
     est 3-coloriable, la figure-eight ne l'est pas.

  2. **Bornes sur le nombre de croisements** (`crossingNumber`) — minorant
     effectif obtenu en énumérant les diagrammes réduits d'un nombre donné
     de croisements et en élimant ceux isotropes au nœud trivial.

  3. **Nombre de dénouement** (`unknottingNumber`, définition seulement,
     `sorry`) — minimum de mouvements R1 nécessaires pour réduire le nœud
     au trivial ; invariant notoirement difficile à calculer (NP-difficile
     dans le cas général, cf Lackenby 2015 poly-time).

  **Path B (invariant classique, mandat 2026-06-23)** : on impose la
  **continuité de l'arc over** à chaque croisement (les deux extrémités
  `e2` et `e4` du strand over portent la même couleur), par opposition au
  modèle permissif antérieur qui coloriait les arêtes indépendamment et
  faisait dériver la 3-colorabilité sur la figure-eight. La conjonction
  « continuité over + règle de Fox » restaure l'invariant classique.

  **Prérequis Mathlib** :
  - `Fintype`, `Fin n` pour les coloriages finis
  - Minimisation sur classes d'équivalence (`Inf`, `sInf`)

  **i18n** : extension bilingue FR/EN inline du sous-module (cf c.373
  `Knots.lean` racine pour le pattern d'agrégateur bilingue ; c.375 a
  couvert les 5 autres sous-modules `Basic`/`Conway`/`Lidman`/
  `MathlibPrerequisites`/`Reidemeister` ; c.376 ferme la couverture 6/6
  du sous-lac `knot_lean`). La section anglaise ci-dessus est préservée
  verbatim ; la section française est ajoutée en miroir pour la
  convention #4980 ratifiée 2026-07-04.

  Epic #2874, Phase 1–2.
-/

import Knots.Basic
import Knots.Reidemeister

namespace Knots

/-! ## 1. Tricolorability (Fox 1962)

A knot diagram is tricolorable if each strand can be colored with one
of 3 colors such that:
  (a) At each crossing, either all three strands have the same color,
      or all three have different colors.
  (b) At least two colors are used.

This is the simplest non-trivial knot invariant.

Reference: Fox (1962), A quick trip through knot theory.
-/

/-- Three colors for tricolorability. -/
inductive TriColor where
  | red : TriColor
  | blue : TriColor
  | green : TriColor
  deriving BEq, DecidableEq, Repr

/-- A tricoloring assigns a color to each edge in a knot diagram. -/
def TriColoring (d : KnotDiagram) := Fin d.numEdges → TriColor

/-- The three local strands of a crossing relevant for tricolorability:
the incoming under-strand (`e1`), the over-strand (`e2`), and the outgoing
under-strand (`e3`). In PD notation these are the three arcs meeting at the
crossing. -/
def PDCrossing.localStrands (c : PDCrossing) : Nat × Nat × Nat :=
  (c.e1, c.e2, c.e3)

/-- Total coloring lookup on a raw `Nat` label, clamped to a valid index.

PD edge labels are 1-indexed in range `[1, numEdges]` for well-formed diagrams.
This total wrapper returns the color at index `(l - 1) mod numEdges` (or `red`
when `numEdges = 0`), so the Fox condition below can be stated without threading
bound proofs through the term. The well-formedness hypothesis
(`1 ≤ l ≤ numEdges`) is recorded separately as part of `triColorConditionAt`,
making the total-vs-partial gap explicit and auditable. -/
def KnotDiagram.colorAtNat (d : KnotDiagram)
    (coloring : Fin d.numEdges → TriColor) (l : Nat) : TriColor :=
  if h : d.numEdges = 0 then TriColor.red
  else coloring ⟨(l - 1) % d.numEdges, Nat.mod_lt _ (by omega)⟩

/-- Check the Fox tricolorability condition at a single crossing (Path B model).

At a crossing with PD edges `e1` (incoming under), `e2` (incoming over), `e3`
(outgoing under), `e4` (outgoing over): the **over-strand** is the single arc
passing straight through the crossing, so its two endpoints `e2` and `e4` must
carry the SAME colour (`c2 = c4`, over-strand continuity), AND the three meeting
strands `(e1, e2, e3)` satisfy Fox's (1962) rule — either all equal or all
pairwise distinct. This conjunction IS the classical Fox invariant: a colouring
that is constant on arcs, with the all-equal-or-all-distinct rule at each
crossing.

**Path B (recovering the classical invariant, mandated 2026-06-23).** The
earlier permissive model coloured EDGES independently with no over-strand
continuity, so the over-arc of a crossing was not forced to share a colour; that
admitted spurious tricolorings (notably the figure-eight, classically NOT
3-colourable) and made a "universal two-crossing colourability" lemma TRUE for
the model but FALSE classically — which would have rendered `tricolorable_invariant`
trivial (separating only the unknot). Adding the `c2 = c4` conjunct restores the
arc-respecting classical model under which the figure-eight is correctly rejected
and the trefoil correctly accepted (witness `(0,1,1,2,2,0)`).

For well-formed crossings (labels in `[1, numEdges]`, the first conjunct),
`colorAtNat` reads the genuine coloring. For malformed labels the conjunct fails
and the crossing is not tricolorable-satisfying — the condition is sound even
before the diagram well-formedness predicate lands.
-/
def triColorConditionAt (d : KnotDiagram) (coloring : Fin d.numEdges → TriColor)
    (c : PDCrossing) : Prop :=
  -- Well-formedness: the four edge labels are in range [1, numEdges].
  (1 ≤ c.e1 ∧ c.e1 ≤ d.numEdges ∧
   1 ≤ c.e2 ∧ c.e2 ≤ d.numEdges ∧
   1 ≤ c.e3 ∧ c.e3 ≤ d.numEdges ∧
   1 ≤ c.e4 ∧ c.e4 ≤ d.numEdges) ∧
  let c1 := d.colorAtNat coloring c.e1
  let c2 := d.colorAtNat coloring c.e2
  let c3 := d.colorAtNat coloring c.e3
  let c4 := d.colorAtNat coloring c.e4
  -- Over-strand continuity (Path B): the over-arc's two ends carry one colour.
  c2 = c4 ∧
  -- Fox condition: all-equal OR all-pairwise-distinct on the three meeting strands.
  ((c1 = c2 ∧ c2 = c3) ∨
   (c1 ≠ c2 ∧ c2 ≠ c3 ∧ c1 ≠ c3))

/-! ### Colour-permutation invariance — enabler for the #3003 backward transfer

The Fox tricolorability condition is invariant under any injective relabelling
of the three colours: equalities and inequalities of strand colours are both
preserved by injectivity, and the well-formedness bounds `1 ≤ e_k ≤ numEdges`
do not mention the colouring at all. This is the foundational fact behind the
§9 colour-symmetry construction (`tricolorable_backward`, Epic #2874 PR3):
given a valid `d₂` colouring whose fresh-edge colours sit outside the `d₁`
range (the all-distinct kink mode), one permutes it to align those colours with
a `d₁`-range colour before restricting, and Fox-validity is retained. These two
lemmas are pure infrastructure (definition unfolding + `Function.Injective`);
the backward construction itself (#3003, all-distinct kink) stays research.
-/

/-- Reading a strand colour commutes with post-composition by `σ`, provided the
    diagram is non-degenerate (`numEdges ≠ 0`, so the `colorAtNat` default
    branch is never taken). -/
theorem KnotDiagram.colorAtNat_comp (d : KnotDiagram)
    (coloring : Fin d.numEdges → TriColor) (σ : TriColor → TriColor) (l : Nat)
    (hn : d.numEdges ≠ 0) :
    d.colorAtNat (σ ∘ coloring) l = σ (d.colorAtNat coloring l) := by
  simp only [KnotDiagram.colorAtNat, dif_neg hn, Function.comp]

/-- **Fox condition is invariant under injective colour relabelling.** For an
    injective `σ` and non-degenerate `d`, `triColorConditionAt d (σ ∘ coloring)
    c ↔ triColorConditionAt d coloring c`. The well-formedness conjunct is
    colour-independent; the over-strand continuity `c2 = c4` and the
    `(c1=c2 ∧ c2=c3) ∨ (c1≠c2 ∧ c2≠c3 ∧ c1≠c3)` Fox disjunction are both
    preserved both ways by injectivity. -/
theorem triColorConditionAt_invariant_perm (d : KnotDiagram)
    (coloring : Fin d.numEdges → TriColor) (σ : TriColor → TriColor)
    (hσ : Function.Injective σ) (hn : d.numEdges ≠ 0) (c : PDCrossing) :
    triColorConditionAt d (σ ∘ coloring) c ↔ triColorConditionAt d coloring c := by
  simp only [triColorConditionAt]
  rw [KnotDiagram.colorAtNat_comp d coloring σ c.e1 hn,
      KnotDiagram.colorAtNat_comp d coloring σ c.e2 hn,
      KnotDiagram.colorAtNat_comp d coloring σ c.e3 hn,
      KnotDiagram.colorAtNat_comp d coloring σ c.e4 hn]
  refine and_congr Iff.rfl ?_
  -- Both the over-strand continuity `(σ c2 = σ c4)` ↔ `(c2 = c4)` and the Fox
  -- disjunction on `(σ c1, σ c2, σ c3)` ↔ `(c1, c2, c3)` go through injectivity.
  -- `σ a = σ b ↔ a = b`; the inequalities transfer by contraposition.
  have heq : ∀ a b : TriColor, σ a = σ b ↔ a = b :=
    fun a b => ⟨fun h => hσ h, congrArg σ⟩
  refine and_congr (heq _ _) ?_
  constructor
  · rintro (⟨h12, h23⟩ | ⟨h12, h23, h13⟩)
    · exact Or.inl ⟨(heq _ _).mp h12, (heq _ _).mp h23⟩
    · refine Or.inr ⟨fun heq' => h12 ((heq _ _).mpr heq'),
                     fun heq' => h23 ((heq _ _).mpr heq'),
                     fun heq' => h13 ((heq _ _).mpr heq')⟩
  · rintro (⟨h12, h23⟩ | ⟨h12, h23, h13⟩)
    · exact Or.inl ⟨(heq _ _).mpr h12, (heq _ _).mpr h23⟩
    · refine Or.inr ⟨fun heq' => h12 ((heq _ _).mp heq'),
                     fun heq' => h23 ((heq _ _).mp heq'),
                     fun heq' => h13 ((heq _ _).mp heq')⟩

/-- A valid tricoloring: satisfies the condition at every crossing,
and uses at least 2 colors. -/
def IsTriColoring (d : KnotDiagram) (coloring : TriColoring d) : Prop :=
  (∀ c ∈ d.crossings, triColorConditionAt d (↑coloring) c) ∧
  d.numEdges ≥ 2 ∧ (∃ i j, coloring i ≠ coloring j)
  -- TODO Phase 2: refine once edge indexing is fixed

/-- A diagram is tricolorable if a valid tricoloring exists. -/
def IsTricolorable (d : KnotDiagram) : Prop :=
  ∃ coloring : TriColoring d, IsTriColoring d coloring

/-- A knot is tricolorable if any of its diagrams is. -/
def Knot.isTricolorable (k : Knot) : Prop :=
  IsTricolorable k.diagram

/-! ### GF(3) linearity of the per-crossing Fox condition (cycle-3, #4022)

The Fox tricolour rule on three colours — "all equal OR all distinct" — is
equivalent, for a 3-element palette, to the colours summing to `0 (mod 3)`. This
is a purely computational fact about the per-crossing Fox disjunction on three
explicit `TriColor` values, independent of the over-strand-continuity conjunct of
`triColorConditionAt` (Path B). It is retained as scaffolding: a linear reading of
the per-crossing condition, useful for brute-force enumeration and as a
`decide`-friendly bridge. Verified empirically over 7.5M well-formed diagrams
(cycle-3, #4022). -/

/-- Embed `TriColor` into `ℕ` (red ↦ 0, blue ↦ 1, green ↦ 2) so the Fox
3-colour condition reads linearly over `ℤ/3ℤ`. -/
def TriColor.toNat : TriColor → Nat
  | red => 0
  | blue => 1
  | green => 2

/-- The Fox 3-colour rule on three colours ⟺ their `toNat`-sum is `0 mod 3`.
Finite (3³ = 27 cases), PROVED by constructor enumeration + `decide` (cycle-6,
#3003). Because the arguments are *explicit* (not universally quantified over an
opaque `TriColor`), `decide` needs no `Fintype` instance — `cases` on each
constructor leaves 27 closed goals that `simp only [TriColor.toNat]` + `decide`
dispatch. This is the GF(3) linearity of the per-crossing Fox disjunction — a
linear reading retained as computational scaffolding (Path B keeps it even though
the over-strand-continuity conjunct of `triColorConditionAt` is not itself linear
over `(ℤ/3)^(numEdges)`). -/
theorem triColorFoxCondition_iff_sum_mod_three (c1 c2 c3 : TriColor) :
    ((c1 = c2 ∧ c2 = c3) ∨ (c1 ≠ c2 ∧ c2 ≠ c3 ∧ c1 ≠ c3)) ↔
      (c1.toNat + c2.toNat + c3.toNat) % 3 = 0 := by
  -- 3³ = 27 closed cases; explicit arguments ⇒ no `Fintype` needed for `decide`.
  cases c1 <;> cases c2 <;> cases c3 <;> simp only [TriColor.toNat] <;> decide

/-! ### Withdrawn: universal two-crossing colourability (Path B, 2026-06-23)

A "universal two-crossing colourability" lemma — every well-formed diagram with
≥ 2 crossings admits a non-constant Fox-valid colouring — was explored in
cycles 3–6 via a GF(3) rank-nullity route. **It is withdrawn under Path B.** The
lemma was only ever plausible for the permissive EDGE-colouring model (colours
assigned to `Fin numEdges` independently, no over-strand continuity); under that
model even the figure-eight (4 crossings, determinant 5, classically NOT
3-colourable) IS tricolorable, so the lemma would have rendered
`tricolorable_invariant` trivial (separating only the unknot). Path B adds the
`c2 = c4` over-strand-continuity conjunct to `triColorConditionAt`, recovering
the classical arc-respecting Fox invariant; under that model the lemma is simply
FALSE (the figure-eight is the explicit counter-example). The GF(3) linearity
scaffolding above is retained as a per-crossing computational fact; the
rank-nullity universal route is not. Reference: Fox (1962); Adams, "The Knot
Book". -/

/-! ## 2. Tricolorability is an invariant

Tricolorability is preserved by all three Reidemeister moves.
This is the key theorem that makes it a knot invariant.

**Phase 2 target**: prove this!
-/

theorem tricolorable_invariant :
    ∀ (d₁ d₂ : KnotDiagram),
      ReidemeisterEquiv d₁ d₂ →
      IsTricolorable d₁ ↔ IsTricolorable d₂ := by
  exact sorry
  -- BLOCKED (forward transfer, Phase 5 PR2). `ReidemeisterStep.r1` was rewired
  -- (Stage 2, #2874) to the GEOMETRICALLY CONNECTED move `Reidemeister1Connected`,
  -- so the free-ρ counter-example of §3b is no longer `ReidemeisterEquiv`-reachable
  -- (it is provably NOT a connected move, §3c-bis / PR #3997). The invariant is
  -- therefore NO LONGER REFUTED by that witness — it now stands on the sound
  -- connected equivalence. It is still OPEN: the FORWARD direction is unproven,
  -- i.e. a tricoloring of `d₁` must EXTEND across a connected R1 curl
  -- (`Reidemeister1Connected`), so the two fresh edges inherit `color a`.
  --
  -- Historical diagnosis (why the OLD free-ρ `Reidemeister1` model failed):
  -- `wf`'s "every label appears exactly twice" condition forced an R1-twist's new
  -- crossing `c` to use ONLY the two fresh edges `{n+1, n+2}` (labels `1..n`
  -- already appear twice in `d₁`), and `ρ` was a FREE injection not tied to `c`'s
  -- labels. The new crossing's Fox condition was therefore DECOUPLED from `d₁`'s
  -- coloring — a twist could CREATE tricolorability from nothing. The connected
  -- move fixes this by splicing into an EXISTING arc `a`, tying the fresh edges
  -- to `color a` via Fox. Reference: Fox (1962); Adams, "The Knot Book".

/-! ## 3. The trefoil is tricolorable

The trefoil (3_1) can be colored with 3 colors, each crossing seeing
all three colors. This proves the trefoil is NOT the unknot.
-/

theorem trefoil_tricolorable : Knot.isTricolorable trefoil := by
  -- Proof: construct an explicit arc-respecting 3-colouring of the trefoil's 6
  -- edges (PD labels). The trefoil PD-code is [[1,4,2,5],[3,6,4,1],[5,2,6,3]],
  -- so numEdges = 6. Path B requires over-strand continuity `c2 = c4` at each
  -- crossing, in addition to the Fox rule on the three meeting strands (e1,e2,e3).
  -- Witness `(0,1,1,2,2,0)` on labels 1..6 (0=red, 1=blue, 2=green), i.e. by Fin
  -- index (index = label-1): labels {1,6} → red, {2,3} → blue, {4,5} → green.
  --   c0 ⟨1,4,2,5⟩: Fox(red, green, blue) all-distinct ✓; arc c(e2=4)=c(e4=5) both green ✓.
  --   c1 ⟨3,6,4,1⟩: Fox(blue, red, green) all-distinct ✓; arc c(e2=6)=c(e4=1) both red ✓.
  --   c2 ⟨5,2,6,3⟩: Fox(green, blue, red) all-distinct ✓; arc c(e2=2)=c(e4=3) both blue ✓.
  unfold Knot.isTricolorable IsTricolorable IsTriColoring Knot.diagram trefoil
  simp only [trefoilDiagram, triColorConditionAt, KnotDiagram.colorAtNat]
  -- Provide the explicit coloring on Fin 6 (index = label - 1).
  refine' ⟨fun i : Fin 6 =>
              if i.val = 0 ∨ i.val = 5 then TriColor.red
              else if i.val = 1 ∨ i.val = 2 then TriColor.blue
              else TriColor.green, _, _, _⟩
  -- Crossing condition: each of the 3 crossings satisfies the (Path B) condition.
  · -- The three crossings are ⟨1,4,2,5⟩, ⟨3,6,4,1⟩, ⟨5,2,6,3⟩. Decide by computation.
    intro c hc
    -- Reduce membership in the explicit crossing list to the 3 concrete cases.
    match c with
    | ⟨1, 4, 2, 5⟩ => decide
    | ⟨3, 6, 4, 1⟩ => decide
    | ⟨5, 2, 6, 3⟩ => decide
  -- numEdges ≥ 2: literal 6 ≥ 2
  · decide
  -- At least 2 colors: edge 0 = red, edge 2 = blue, red ≠ blue
  · exact ⟨⟨0, by decide⟩, ⟨2, by decide⟩, by decide⟩

/-! ## 3b. Certified counter-example: the free-ρ R1 move does NOT preserve
tricolorability.

This is a *positive* diagnostic result (not a gap in the invariant). It certifies
that the free-ρ `Reidemeister1` move (Phase 5 PR1, #2929) — which carries the
new crossing `c` and the edge-renaming `ρ` as TWO INDEPENDENT existentials —
does NOT preserve tricolorability: a single such twist connects a
non-tricolorable diagram to a tricolorable one. After the Stage-2 rewire
(#2874), `ReidemeisterStep.r1` uses the GEOMETRICALLY CONNECTED refinement
`Reidemeister1Connected` instead, and this witness pair is provably excluded
from that move (§3c-bis, PR #3997); so this counter-example refutes the raw
free-ρ move `Reidemeister1`, NOT the connected equivalence on which
`tricolorable_invariant` now stands.

Why. The `wf` "every label appears exactly twice" condition forces an R1-twist's
new crossing `c` to use ONLY the two fresh edges `{n+1, n+2}` — labels `1..n`
already appear twice in `d₁`, so `c` cannot reuse any of them without breaking
parity. Moreover the edge-renaming `ρ : Fin (min) ↪ Fin (max)` introduced by
PR1 is a FREE injection, NOT tied to `c`'s labels. The new crossing's Fox
condition therefore involves only the two fresh (freely-colorable) edges and is
DECOUPLED from `d₁`'s coloring — so a twist can CREATE tricolorability out of
nothing, or symmetrically hide the ≥2-colours entirely in the fresh edges while
`d₁` is forced monochrome.

Witness (refutes the universal biconditional):
  d₁ = { crossings := [⟨1,2,1,2⟩], numEdges := 2 }    — NOT tricolorable.
       Fox at ⟨1,2,1,2⟩ reads (coloring⟨0⟩, coloring⟨1⟩, coloring⟨0⟩), which is
       all-equal ONLY if coloring⟨0⟩ = coloring⟨1⟩ — contradicting the ≥2-colours
       requirement. So no valid tricoloring exists.
  d₂ = { crossings := [⟨1,2,1,2⟩, ⟨3,4,3,4⟩], numEdges := 4 }  — tricolorable.
       Color edges 1,2 = red and 3,4 = blue: Fox holds at both crossings
       (all-equal within each), and ≥2 colours are used.
  A single free-ρ R1 twist `Reidemeister1 d₁ d₂` connects them, so the
  biconditional `IsTricolorable d₁ ↔ IsTricolorable d₂` is `(false ↔ true)`
  for a pair linked by the raw free-ρ move (which is no longer a
  `ReidemeisterStep` after the Stage-2 rewire).

**Implemented (Stage 2 of #2874).** The fix is wired into `ReidemeisterStep.r1`:
the constructor carries the geometric splicing via `Reidemeister1Connected`, so
that `ρ` DETERMINES `c`'s labels — a genuine R1 curl on arc `a` splices into the
EXISTING arc `a`, whose Fox condition constrains the new edges to inherit
`color a`, which is what makes tricolorability transfer along the move. The
forward transfer (§3e, #3003) remains the open proof obligation.
Reference: Fox (1962); Adams, "The Knot Book". -/

theorem tricolorable_invariant_fails_under_pr1_model :
    ∃ (d₁ d₂ : KnotDiagram),
      Reidemeister1 d₁ d₂ ∧
      ¬ IsTricolorable d₁ ∧
      IsTricolorable d₂ := by
  -- Witness pair.
  refine' ⟨{ crossings := [⟨1, 2, 1, 2⟩], numEdges := 2, hwell := by trivial },
           { crossings := [⟨1, 2, 1, 2⟩, ⟨3, 4, 3, 4⟩], numEdges := 4, hwell := by trivial },
           ?_, ?_, ?_⟩
  -- (a) Reidemeister1 d₁ d₂: a single free-ρ R1 twist, witness c = ⟨3,4,3,4⟩.
  --     d₁ = {[⟨1,2,1,2⟩], numEdges = 2}; d₂ = {[⟨1,2,1,2⟩, ⟨3,4,3,4⟩], numEdges = 4}.
  · refine' ⟨?_, ?_, ⟨⟨3, 4, 3, 4⟩, ⟨?_, ?_⟩⟩⟩
    · -- d₁.wf = true: labels 1,2 each appear twice across [1,2,1,2].
      decide
    · -- d₂.wf = true: labels 1,2,3,4 each appear twice across [1,2,1,2,3,4,3,4].
      decide
    · -- ρ : Fin (min d₁.numEdges d₂.numEdges) ↪ Fin (max d₁.numEdges d₂.numEdges),
      --   which is defeq to Fin 2 ↪ Fin 4 (d₁.numEdges = 2, d₂.numEdges = 4 reduce,
      --   and min/max on the literals reduce). Constructed concretely as Fin 2 ↪ Fin 4
      --   so omega sees concrete bounds; `exact` discharges the defeq to the goal type.
      have ρ : Fin 2 ↪ Fin 4 :=
        ⟨fun i => ⟨i.val, by omega⟩,
         fun a b h => by
           have h : (⟨a.val, by omega⟩ : Fin 4) = ⟨b.val, by omega⟩ := h
           injection h with hval
           exact Fin.ext hval⟩
      exact ρ
    · -- surgery (twist arm): d₂ = { d₁ with crossings := d₁.crossings ++ [⟨3,4,3,4⟩], numEdges := d₁.numEdges + 2 }.
      left
      rfl
  -- (b) d₁ is NOT tricolorable: Fox at the sole crossing ⟨1,2,1,2⟩ forces the two
  --     edges to the same colour, contradicting the ≥2-colours requirement.
  · show ¬ IsTricolorable { crossings := [⟨1, 2, 1, 2⟩], numEdges := 2, hwell := by trivial }
    rintro ⟨coloring, hcond, hedges, htwo⟩
    -- The sole crossing ⟨1,2,1,2⟩ is in d₁.crossings; apply the Fox condition to it.
    have hfox := hcond (⟨1, 2, 1, 2⟩ : PDCrossing)
        (by exact List.mem_cons_self : _ ∈ ([⟨1, 2, 1, 2⟩] : List PDCrossing))
    -- Unfold: at ⟨1,2,1,2⟩ with numEdges = 2, the colours read are coloring⟨0⟩ (label 1)
    -- and coloring⟨1⟩ (label 2). Fox's all-distinct branch is impossible (the third
    -- strand equals the first), so Fox forces coloring⟨0⟩ = coloring⟨1⟩.
    have h01 : coloring ⟨0, by decide⟩ = coloring ⟨1, by decide⟩ := by
      have h := hfox
      simp only [triColorConditionAt, KnotDiagram.colorAtNat] at h
      -- Path B shape: `bounds ∧ (arc-eq ∧ Foxdisj)` — flatten the right-nested And.
      rcases h with ⟨_, _, h | h⟩
      · exact h.1
      · -- all-distinct branch: needs c1 ≠ c3, but e1 = e3 = 1 makes c1 ≡ c3 (rfl) → contradiction.
        exact (h.2.2 rfl).elim
    -- Hence every Fin 2 colour equals coloring⟨0⟩ (the only two elements are 0, 1).
    have hAll : ∀ (i : Fin 2), coloring i = coloring ⟨0, by decide⟩ := by
      intro i
      have h : i.val = 0 ∨ i.val = 1 := by omega
      rcases h with h | h
      · rw [show i = (⟨0, by omega⟩ : Fin 2) from Fin.ext h]
      · rw [show i = (⟨1, by omega⟩ : Fin 2) from Fin.ext h, h01]
    obtain ⟨i, j, hne⟩ := htwo
    exact hne (by rw [hAll i, hAll j])
  -- (c) d₂ IS tricolorable: edges 1,2 (Fin index 0,1) = red, edges 3,4 (index 2,3) = blue;
  --     Fox is all-equal within each crossing, ≥2 colours used.
  · show IsTricolorable { crossings := [⟨1, 2, 1, 2⟩, ⟨3, 4, 3, 4⟩], numEdges := 4, hwell := by trivial }
    refine' ⟨fun i : Fin 4 => if i.val ≤ 1 then TriColor.red else TriColor.blue, ?_, ?_, ?_⟩
    · -- Fox at every crossing of d₂.
      intro c hc
      -- d₂.crossings = [⟨1,2,1,2⟩, ⟨3,4,3,4⟩]; hc pins c to one of them.
      have hsplit : c = ⟨1, 2, 1, 2⟩ ∨ c = ⟨3, 4, 3, 4⟩ := by simpa using hc
      rcases hsplit with rfl | rfl
      · -- c = ⟨1,2,1,2⟩: local strands (1,2,1) all red → all-equal.
        simp only [triColorConditionAt, KnotDiagram.colorAtNat]; decide
      · -- c = ⟨3,4,3,4⟩: local strands (3,4,3) all blue → all-equal.
        simp only [triColorConditionAt, KnotDiagram.colorAtNat]; decide
    · -- numEdges = 4 ≥ 2.
      decide
    · -- ≥2 colours: edge index 0 = red ≠ blue = edge index 2.
      exact ⟨⟨0, by decide⟩, ⟨2, by decide⟩, by decide⟩

/-! ## 3c. Non-regression gate (PR1.5): the #2938 witness is EXCLUDED under `Reidemeister1'`

`Reidemeister1'` (Reidemeister.lean, PR1.5 #2956) is the ρ-determined strengthening
of the R1 move: the new crossing is forced to the shape `⟨a, a, n+1, n+2⟩` — one
strand is the existing arc `a`. This couples the two fresh edges to `color(a)` via
the Fox condition, which is what the PR1 free-`ρ` model lacked.

The certified counter-example `tricolorable_invariant_fails_under_pr1_model`
above (§3b) refutes the biconditional *under the PR1 model* by exhibiting a
specific witness pair `(d₁, d₂)` connected by a PR1 R1-step. **This theorem proves
that very witness pair is NOT connected by a `Reidemeister1'` step** — i.e. the
ρ-determined refinement excludes the counter-example by construction. This is the
non-regression test ai-01 required (PR1.5 gate 1, dashboard 11:35Z): the re-model
must EXCLUDE #2938, and here we prove it explicitly.

Witness pair (same as §3b):
  d₁ = { crossings := [⟨1,2,1,2⟩], numEdges := 2 }
  d₂ = { crossings := [⟨1,2,1,2⟩, ⟨3,4,3,4⟩], numEdges := 4 }

Why `Reidemeister1' d₁ d₂` fails:
  - Twist arm forces `d₂.crossings = [⟨1,2,1,2⟩] ++ [⟨a, a, 3, 4⟩]`, i.e. the
    second crossing must be `⟨a, a, 3, 4⟩`. But `d₂`'s second crossing is
    `⟨3, 4, 3, 4⟩`, so list equality forces `⟨3,4,3,4⟩ = ⟨a,a,3,4⟩`, giving
    `a = 3` (from e1) and `a = 4` (from e2) — contradiction.
  - Untwist arm forces `d₁.crossings` to equal `d₂.crossings ++ [⟨a,a,_,_⟩]`,
    a 3-element list, but `d₁.crossings` has 1 element — length contradiction.
-/

/-- The #2938 witness pair is NOT connected by a ρ-determined R1 move
(`Reidemeister1'`). This is the PR1.5 non-regression gate: the re-model excludes
the counter-example by construction. -/
theorem pr1_counterexample_excluded_under_rho_determined :
    ¬ Reidemeister1'
        { crossings := [⟨1, 2, 1, 2⟩], numEdges := 2, hwell := by trivial }
        { crossings := [⟨1, 2, 1, 2⟩, ⟨3, 4, 3, 4⟩], numEdges := 4, hwell := by trivial } := by
  -- Unfold Reidemeister1': wf₁ ∧ wf₂ ∧ (∃ a, range ∧ (∃ ρ, surgery ∨ surgery)).
  rintro ⟨_hwf₁, _hwf₂, a, _hrange₁, _hrange₂, _ρ, hsurg⟩
  rcases hsurg with ht | ht
  · -- TWIST arm: d₂ = { d₁ with crossings := d₁.crossings ++ [⟨a,a,3,4⟩], numEdges := 4 }.
    -- d₁.numEdges = 2, so the appended crossing is ⟨a, a, 3, 4⟩.
    -- Project .crossings off the record equality ht by congruence, then the RHS
    -- ({ d₁ with crossings := X }).crossings reduces to X = d₁.crossings ++ [⟨a,a,3,4⟩].
    have hfield :
        ({ crossings := [⟨1, 2, 1, 2⟩, ⟨3, 4, 3, 4⟩], numEdges := 4, hwell := by trivial }
          : KnotDiagram).crossings =
        ({ crossings := [⟨1, 2, 1, 2⟩], numEdges := 2, hwell := by trivial }
          : KnotDiagram).crossings ++ [⟨a, a, 3, 4⟩] :=
      congrArg (·.crossings) ht
    -- The RHS reduces to [⟨1,2,1,2⟩] ++ [⟨a,a,3,4⟩]; second elements: ⟨3,4,3,4⟩ = ⟨a,a,3,4⟩.
    have h2nd : (⟨3, 4, 3, 4⟩ : PDCrossing) = ⟨a, a, 3, 4⟩ := by
      simpa [List.append] using hfield
    -- Injectivity of PDCrossing (4 fields): e1 gives 3 = a, e2 gives 4 = a.
    injection h2nd with h_e1 h_e2 h_e3 h_e4
    omega
  · -- UNTWIST arm: d₁ = { d₂ with crossings := d₂.crossings ++ [⟨a,a,5,6⟩], numEdges := 6 }.
    -- d₂.numEdges = 4, so appended crossing = ⟨a, a, 5, 6⟩.
    -- Project .crossings off the record equality by congruence (term-mode, robust
    -- against literal-form mismatch that blocks `subst`/`rw`).
    have hfield :
        ({ crossings := [⟨1, 2, 1, 2⟩], numEdges := 2, hwell := by trivial }
          : KnotDiagram).crossings =
        ({ crossings := [⟨1, 2, 1, 2⟩, ⟨3, 4, 3, 4⟩], numEdges := 4, hwell := by trivial }
          : KnotDiagram).crossings ++ [⟨a, a, 5, 6⟩] :=
      congrArg (·.crossings) ht
    -- Length contradiction: LHS has length 1, RHS has length 3.
    -- `simp at h` reduces the list lengths to concrete numbers (`1` and `3`),
    -- then closes the goal by deriving `False` from the contradiction `1 = 3`.
    have h := congrArg List.length hfield
    simp at h

/-! ## 3c-bis. The #2938 witness is ALSO excluded under `Reidemeister1Connected` (option C)

`pr1_counterexample_excluded_under_rho_determined` (§3c above) proves the certified
counter-example witness pair is NOT connected by a `Reidemeister1'` (ρ-determined)
move. Here we prove the analogous statement for `Reidemeister1Connected` (option C):
the refuting witness pair is unreachable under a connected R1 twist too. This is the
second non-regression gate certifying that option C — the (C) wiring mandated for
#2874 — excludes the disjoint-kink counter-example by construction.

Why it fails. `Reidemeister1Connected` requires the appended kink crossing to have
shape `⟨a, n+1, n+2, n+2⟩` where `1 ≤ a ≤ d₁.numEdges` is an existing arc of `d₁`.
For the witness (`d₁` = {[⟨1,2,1,2⟩], numEdges = 2}), the surgery forces `d₂`'s last
crossing `⟨3,4,3,4⟩` to equal `⟨a, 3, 4, 4⟩`, giving `a = 3` — contradicting
`a ≤ d₁.numEdges = 2`. The disjoint-kink counter-example is thus structural: under
any connected R1 model, the twist must splice a REAL arc of `d₁` (the witness's sole
crossing has no arc labelled `3` to splice), so the pair is unreachable. This is what
makes option C the honest SOTA fix rather than the (X) reframe: the refuting witness
vanishes under the correct equivalence. (Wiring `Reidemeister1Connected` into
`ReidemeisterStep`/`ReidemeisterEquiv` is a multi-cycle stage — `Reidemeister1Connected`
is currently twist-only and needs an untwist arm + `.symm` before the equivalence's
`reidemeister_equiv_symm` can carry it. See #2874.) -/
theorem pr1_counterexample_excluded_under_connected :
    ¬ Reidemeister1Connected
        { crossings := [⟨1, 2, 1, 2⟩], numEdges := 2, hwell := by trivial }
        { crossings := [⟨1, 2, 1, 2⟩, ⟨3, 4, 3, 4⟩], numEdges := 4, hwell := by trivial } := by
  -- Reidemeister1Connected unfolds as wf₁ ∧ wf₂ ∧ (∃ i a Y' ρ, bounds ∧ edges ∧
  -- proper-arc ∧ isRenameOf ∧ surgery). The surgery is single-arm (twist only):
  -- d₂ = { d₁ with crossings := d₁.crossings.set i.val Y' ++ [⟨a,3,4,4⟩], numEdges := 4 }.
  rintro ⟨_hwf₁, _hwf₂, i, a, Y', _ρ, _ha1, ha2, _ha_edges, _hproper, _hren, hsurg⟩
  -- `i : Fin d₁.crossings.length = Fin 1`, so `i.val = 0`. omega cannot reduce the
  -- structure literal's `.crossings.length` on its own, so discharge the length by
  -- `rfl` (separate hyp — `rw` into `i.isLt` fails: `i`'s type depends on it) and
  -- let omega combine `hbnd : i.val < e` with `hlen : e = 1` directly.
  have hi : i.val = 0 := by
    have hlen :
        (({ crossings := [⟨1, 2, 1, 2⟩], numEdges := 2, hwell := by trivial }
          : KnotDiagram).crossings).length = 1 := by rfl
    have hbnd := i.isLt
    omega
  have hfield :
      ({ crossings := [⟨1, 2, 1, 2⟩, ⟨3, 4, 3, 4⟩], numEdges := 4, hwell := by trivial }
        : KnotDiagram).crossings =
      (({ crossings := [⟨1, 2, 1, 2⟩], numEdges := 2, hwell := by trivial }
        : KnotDiagram).crossings.set i.val Y') ++ [⟨a, 3, 4, 4⟩] :=
    congrArg (·.crossings) hsurg
  rw [hi] at hfield
  -- RHS reduces to [⟨1,2,1,2⟩].set 0 Y' ++ [⟨a,3,4,4⟩] = [Y', ⟨a,3,4,4⟩].
  -- The second element gives ⟨3,4,3,4⟩ = ⟨a,3,4,4⟩ (cons injectivity).
  have hkink : (⟨3, 4, 3, 4⟩ : PDCrossing) = ⟨a, 3, 4, 4⟩ := by
    simpa [List.set, List.append] using hfield
  -- e2 field projection: ⟨3,4,3,4⟩.e2 = 4 vs ⟨a,3,4,4⟩.e2 = 3 — a direct
  -- `4 = 3` contradiction (structural, independent of the value of `a`).
  -- We assert the reduced type so defeq closes the projection of the literal.
  have h_e2 : (4 : Nat) = 3 := congrArg PDCrossing.e2 hkink
  omega

/-! ## 3d. The connected R1 move (option C) PRESERVES tricolorability on the witness

This is the positive complement to the PR1 counter-example (§3b). Under the
STRENGTHENED `Reidemeister1Connected` (option C, carrying the `Y'.isRenameOf`
hypothesis), the connected R1 twist does NOT create or destroy tricolorability
the way the disjoint-kink append model did (#2938). We verify this on the concrete
witness pair of `reidemeister1Connected_satisfiable` (Reidemeister.lean): the
connected move maps a tricolorable `d₁` to a tricolorable `d₂`, and conversely.

Why both directions hold on the witness. The connected twist on arc `a = 1`
renames the `e1` slot of crossing 1 (`1 → 5 = b`) and appends `C = ⟨1,5,6,6⟩`.
A tricoloring of `d₁` extends to `d₂` by giving the two new edges `b = 5` and
`c = 6` the colour of the arc `a = 1`: then the new crossing `C` reads
`(col a, col a, col a)` — all-equal, Fox-trivial — and the modified crossing
reads the same three colours as before (the renamed slot `b` carries `col a`).
Conversely a tricoloring of `d₂` projects back to `d₁`. This is the
*computational* verification that option C preserves the invariant; the general
transfer lemma (`Reidemeister1Connected.tricolorable_invariant`, the PR2 target)
makes this argument for arbitrary diagrams — gated on the strengthened def
merging (PR #2990).

Certified constructively: we exhibit an explicit 3-colouring of each diagram
(mirroring the `trefoil_tricolorable` pattern), so each side is inhabited and the
biconditional reduces to `(true ↔ true)`. `IsTricolorable` is an existential over
`Fin n → TriColor`, so no `Decidable` instance auto-derives — the colourings are
supplied by hand, with each crossing's Fox condition discharged by `decide`.
-/

/-- The witness `d₁` of `reidemeister1Connected_satisfiable` (Reidemeister.lean). -/
def witnessD1Connected : KnotDiagram :=
  { crossings := [⟨1,2,3,4⟩, ⟨1,2,3,4⟩], numEdges := 4, hwell := by trivial }

/-- The witness `d₂` of `reidemeister1Connected_satisfiable` (Reidemeister.lean). -/
def witnessD2Connected : KnotDiagram :=
  { crossings := [⟨1,2,3,4⟩, ⟨5,2,3,4⟩, ⟨1,5,6,6⟩], numEdges := 6, hwell := by trivial }

/-- `witnessD1Connected` is tricolorable (Path B): both crossings are
    `⟨1,2,3,4⟩`, each reading `(red, blue, green)` on the Fox strands
    `(e1, e2, e3) = (1, 2, 3)` (all pairwise distinct), with over-strand continuity
    `c(e2) = c(e4)` (edges 2 and 4 both blue). Constructive, mirroring
    `trefoil_tricolorable`. -/
theorem witnessD1Connected_tricolorable : IsTricolorable witnessD1Connected := by
  unfold IsTricolorable IsTriColoring witnessD1Connected
  simp only [triColorConditionAt, KnotDiagram.colorAtNat]
  -- Arc-respecting colouring (Path B): edges {1}→red, {2,4}→blue, {3}→green, so
  -- the over-arc (e2,e4)=(2,4) is monochromatic (blue) at each ⟨1,2,3,4⟩.
  refine' ⟨fun i : Fin 4 =>
              if i.val = 0 then TriColor.red
              else if i.val = 1 ∨ i.val = 3 then TriColor.blue
              else TriColor.green, ?_, ?_, ?_⟩
  · intro c hc
    -- Both crossings are `⟨1,2,3,4⟩`; the single distinct value is the only
    -- element of the list, so the (Path B) condition is checked once by computation.
    match c with
    | ⟨1, 2, 3, 4⟩ => decide
  · decide
  · exact ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide⟩

/-- `witnessD2Connected` is tricolorable (Path B): the original crossings
    `⟨1,2,3,4⟩` and `⟨5,2,3,4⟩` read all-distinct colours with over-strand
    continuity `c(e2) = c(e4)` (edges 2,4 both blue), and the new kink `⟨1,5,6,6⟩`
    reads `(red, red, red)` (all-equal, Fox-trivial) with `c(e2) = c(e4)` on edges
    5,6 (both red). The two new edges `b = 5` and `c = 6` carry the colour of arc
    `a = 1` (red), so the twist does not create or destroy tricolorability. -/
theorem witnessD2Connected_tricolorable : IsTricolorable witnessD2Connected := by
  unfold IsTricolorable IsTriColoring witnessD2Connected
  simp only [triColorConditionAt, KnotDiagram.colorAtNat]
  -- Arc-respecting colouring (Path B): edges {1,5,6}→red, {2,4}→blue, {3}→green.
  refine' ⟨fun i : Fin 6 =>
              if i.val = 0 ∨ i.val = 4 ∨ i.val = 5 then TriColor.red
              else if i.val = 1 ∨ i.val = 3 then TriColor.blue
              else TriColor.green, ?_, ?_, ?_⟩
  · intro c hc
    match c with
    | ⟨1, 2, 3, 4⟩ => decide
    | ⟨5, 2, 3, 4⟩ => decide
    | ⟨1, 5, 6, 6⟩ => decide
  · decide
  · exact ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide⟩

/-- The connected R1 move (option C, strengthened `Reidemeister1Connected`)
    preserves tricolorability on the concrete witness pair of
    `reidemeister1Connected_satisfiable`: both `witnessD1Connected` and
    `witnessD2Connected` are tricolorable, so the biconditional is
    `(true ↔ true)`. This is the positive complement to the PR1 counter-example
    `tricolorable_invariant_fails_under_pr1_model` (§3b), confirming the
    connected-surgery model does not share the disjoint-kink defect. Proved
    constructively (explicit 3-colourings, mirroring `trefoil_tricolorable`). -/
theorem reidemeister1Connected_witness_preserves_tricolorable :
    IsTricolorable witnessD1Connected ↔ IsTricolorable witnessD2Connected :=
  ⟨fun _ => witnessD2Connected_tricolorable, fun _ => witnessD1Connected_tricolorable⟩

/-! ## 3e. PR2 forward transfer: a connected R1 move PRESERVES tricolorability

Under the strengthened `Reidemeister1Connected` (carrying the `Y'.isRenameOf`
hypothesis, merged #2990), a tricoloring of `d₁` extends to a tricoloring of
`d₂`: the two fresh edges `b = numEdges+1` and `c = numEdges+2` both carry the
colour of arc `a`. This makes the new kink crossing `⟨a, b, c, c⟩` Fox-trivial
(`(col a)³`, all-equal) and the `a → b` rename Fox-invisible (`col₂ b = col₁ a`).
This is the forward half of `tricolorable_invariant` specialised to the
connected R1 move (option C).
-/

/-- Forward membership for `List.set`: an element of `l.set n v` is either the
    inserted value `v` (at the modified position) or already an element of `l`.
    Pure list-combinatorics helper (no knot content), used by the transfer lemma
    to split `d₂.crossings = d₁.crossings.set i Y' ++ [C]`. -/
private theorem mem_set_fwd {α : Type*} : ∀ (n : Nat) (l : List α) (v c : α),
    c ∈ l.set n v → c = v ∨ c ∈ l
  | 0, [], _, _, h => by simp at h
  | 0, hd :: tl, v, c, h => by
    change c ∈ v :: tl at h
    simp only [List.mem_cons] at h ⊢
    rcases h with heq | hmem
    · refine Or.inl ?_; exact heq
    · exact Or.inr (Or.inr hmem)
  | _+1, [], _, _, h => by simp at h
  | n+1, hd :: tl, v, c, h => by
    have ih := mem_set_fwd n tl v c
    change c ∈ hd :: tl.set n v at h
    simp only [List.mem_cons] at h ⊢
    rcases h with hhd | hset
    · exact Or.inr (Or.inl hhd)
    · rcases ih hset with rfl | hmem
      · exact Or.inl rfl
      · exact Or.inr (Or.inr hmem)

/-- Backward membership for `List.set`: if `c ∈ l` but `c ∉ l.set n v`, then `c`
    is exactly the element `l.get n` that got replaced, and `c ≠ v`. Pure
    list-combinatorics helper, converse-in-spirit of `mem_set_fwd`, used by the
    backward transfer lemma to identify the modified crossing `Y`. -/
private theorem mem_drop_out {α : Type*} : ∀ (n : Nat) (l : List α) (v c : α)
    (hn : n < l.length) (hc : c ∈ l) (hnmem : c ∉ l.set n v),
    l.get ⟨n, hn⟩ = c ∧ c ≠ v
  | 0, hd :: tl, v, c, hn, hc, hnmem => by
    change c ∉ v :: tl at hnmem
    simp only [List.mem_cons] at hc hnmem
    refine ⟨?_, fun heq => hnmem (Or.inl heq)⟩
    rcases hc with hhd | hctl
    · exact hhd.symm
    · exact absurd hctl (fun h => hnmem (Or.inr h))
  | n+1, hd :: tl, v, c, hn, hc, hnmem => by
    change c ∉ hd :: tl.set n v at hnmem
    simp only [List.mem_cons] at hc hnmem
    rcases hc with hhd | hctl
    · exact absurd hhd (fun h => hnmem (Or.inl h))
    · have hlen : (hd :: tl).length = tl.length + 1 := List.length_cons
      have ihn : n < tl.length := by omega
      have ihntset : c ∉ tl.set n v := fun h => hnmem (Or.inr h)
      have ih := mem_drop_out n tl v c ihn hctl ihntset
      refine ⟨?_, ih.2⟩
      have hfin : (⟨n, Nat.lt_of_succ_lt_succ hn⟩ : Fin tl.length) = ⟨n, ihn⟩ := Fin.ext rfl
      rw [show (hd :: tl).get ⟨n+1, hn⟩ = tl.get ⟨n, Nat.lt_of_succ_lt_succ hn⟩ from rfl, hfin]
      exact ih.1
  | _, [], _, _, hn, _, _ => (Nat.not_lt_zero _ hn).elim

/-- Membership of the inserted value in `List.set`: `v ∈ l.set n v` whenever
    `n < l.length`. Pure list-combinatorics helper, used by the backward transfer
    lemma to witness that the replacement crossing `Y'` sits in `d₂.crossings`. -/
private theorem mem_set_self {α : Type*} : ∀ (n : Nat) (l : List α) (v : α) (hn : n < l.length),
    v ∈ l.set n v
  | 0, hd :: tl, v, _ => by
    change v ∈ v :: tl
    exact List.mem_cons_self
  | n+1, hd :: tl, v, hn => by
    have hlen : (hd :: tl).length = tl.length + 1 := List.length_cons
    have ihn : n < tl.length := by omega
    change v ∈ hd :: tl.set n v
    simp only [List.mem_cons]
    exact Or.inr (mem_set_self n tl v ihn)
  | _, [], _, hn => (Nat.not_lt_zero _ hn).elim

theorem Reidemeister1Connected.tricolorable_forward {d₁ d₂ : KnotDiagram}
    (h : Reidemeister1Connected d₁ d₂) (htri : IsTricolorable d₁) :
    IsTricolorable d₂ := by
  obtain ⟨_hwf₁, _hwf₂, i, a, Y', _ρ, ha1, ha2, _hamem, _hproper, hrename, hsurg⟩ := h
  -- Edge-count and crossing-list consequences of the surgery equation.
  have hd₂num : d₂.numEdges = d₁.numEdges + 2 := by
    simpa using congrArg (·.numEdges) hsurg
  have hd₂cross : d₂.crossings =
      d₁.crossings.set i.val Y' ++
        [⟨a, d₁.numEdges + 1, d₁.numEdges + 2, d₁.numEdges + 2⟩] := by
    simpa using congrArg (·.crossings) hsurg
  obtain ⟨col₁, hfox₁, hge2, h2col⟩ := htri
  -- Extension colouring: preserved edges keep their colour, the two new edges
  -- (indices `d₁.numEdges` and `d₁.numEdges+1`, i.e. labels `b`, `c`) carry
  -- `col₁ a`. Defined as a local def so `simp only [col₂]` can unfold it.
  have haim1 : a - 1 < d₁.numEdges := by omega
  have hd₂ge₁ : d₁.numEdges ≤ d₂.numEdges := by omega
  -- Embedding of `d₁`'s edge indices into `d₂`'s (the +2 fresh edges sit above).
  let emb : Fin d₁.numEdges → Fin d₂.numEdges :=
    fun k => ⟨k.val, Nat.lt_of_lt_of_le k.isLt hd₂ge₁⟩
  let col₂ : Fin d₂.numEdges → TriColor :=
    fun j => if hj : j.val < d₁.numEdges then col₁ ⟨j.val, hj⟩
             else col₁ ⟨a - 1, haim1⟩
  refine' ⟨col₂, ?fox, ?num, ?col⟩
  case num =>
    -- `d₂.numEdges = d₁.numEdges + 2 ≥ 2` since `d₁.numEdges ≥ 2`.
    omega
  case col =>
    -- At least two colours: two distinct-coloured edges of `d₁` embed into `d₂`.
    obtain ⟨p, q, hpq⟩ := h2col
    -- `col₂ (emb k) = col₁ k`: beta-reduce, the `if` is positive (k.val < n),
    -- and the `Fin` constructor collapses by proof irrelevance.
    have hcol_pres : ∀ k : Fin d₁.numEdges, col₂ (emb k) = col₁ k := by
      intro k
      conv_lhs => unfold col₂
      rw [dif_pos k.isLt]
    refine' ⟨emb p, emb q, ?_⟩
    rw [hcol_pres p, hcol_pres q]
    exact hpq
  case fox =>
    -- Colour-preservation facts, the heart of the transfer.
    -- (F1) A preserved label `l` (1 ≤ l ≤ d₁.numEdges) reads the same colour in
    --      `d₂` (under `col₂`) as in `d₁` (under `col₁`).
    have hcolF1 : ∀ l, 1 ≤ l → l ≤ d₁.numEdges →
        d₂.colorAtNat col₂ l = d₁.colorAtNat col₁ l := by
      intro l hl1 hln
      have hn0d₂ : d₂.numEdges ≠ 0 := by omega
      have hn0d₁ : d₁.numEdges ≠ 0 := by omega
      have hL : d₂.colorAtNat col₂ l =
          col₂ ⟨(l - 1) % d₂.numEdges, Nat.mod_lt (l - 1) (by omega)⟩ := by
        simp only [KnotDiagram.colorAtNat, dif_neg hn0d₂]
      have hR : d₁.colorAtNat col₁ l =
          col₁ ⟨(l - 1) % d₁.numEdges, Nat.mod_lt (l - 1) (by omega)⟩ := by
        simp only [KnotDiagram.colorAtNat, dif_neg hn0d₁]
      rw [hL, hR]
      simp only [hd₂num]
      have h1 : (l - 1) % (d₁.numEdges + 2) = l - 1 := Nat.mod_eq_of_lt (by omega)
      have h2 : (l - 1) % d₁.numEdges = l - 1 := Nat.mod_eq_of_lt (by omega)
      simp only [h1, h2]
      conv_lhs => unfold col₂
      simp only [dif_pos (by omega : (l - 1) < d₁.numEdges)]
    have hcolF2b : d₂.colorAtNat col₂ (d₁.numEdges + 1) = d₁.colorAtNat col₁ a := by
      have hn0d₂ : d₂.numEdges ≠ 0 := by omega
      have hn0d₁ : d₁.numEdges ≠ 0 := by omega
      have hL : d₂.colorAtNat col₂ (d₁.numEdges + 1) =
          col₂ ⟨(d₁.numEdges + 1 - 1) % d₂.numEdges, Nat.mod_lt (d₁.numEdges + 1 - 1) (by omega)⟩ := by
        simp only [KnotDiagram.colorAtNat, dif_neg hn0d₂]
      have hR : d₁.colorAtNat col₁ a =
          col₁ ⟨(a - 1) % d₁.numEdges, Nat.mod_lt _ (by omega)⟩ := by
        simp only [KnotDiagram.colorAtNat, dif_neg hn0d₁]
      rw [hL, hR]
      simp only [hd₂num]
      have h1 : (d₁.numEdges + 1 - 1) % (d₁.numEdges + 2) = d₁.numEdges := by
        rw [Nat.mod_eq_of_lt (by omega)]; omega
      have h2 : (a - 1) % d₁.numEdges = a - 1 := Nat.mod_eq_of_lt (by omega)
      simp only [h1, h2]
      conv_lhs => unfold col₂
      simp only [dif_neg (by omega : ¬(d₁.numEdges < d₁.numEdges))]
    have hcolF2c : d₂.colorAtNat col₂ (d₁.numEdges + 2) = d₁.colorAtNat col₁ a := by
      have hn0d₂ : d₂.numEdges ≠ 0 := by omega
      have hn0d₁ : d₁.numEdges ≠ 0 := by omega
      have hL : d₂.colorAtNat col₂ (d₁.numEdges + 2) =
          col₂ ⟨(d₁.numEdges + 2 - 1) % d₂.numEdges, Nat.mod_lt (d₁.numEdges + 2 - 1) (by omega)⟩ := by
        simp only [KnotDiagram.colorAtNat, dif_neg hn0d₂]
      have hR : d₁.colorAtNat col₁ a =
          col₁ ⟨(a - 1) % d₁.numEdges, Nat.mod_lt _ (by omega)⟩ := by
        simp only [KnotDiagram.colorAtNat, dif_neg hn0d₁]
      rw [hL, hR]
      simp only [hd₂num]
      have h1 : (d₁.numEdges + 2 - 1) % (d₁.numEdges + 2) = d₁.numEdges + 1 := by
        rw [Nat.mod_eq_of_lt (by omega)]; omega
      have h2 : (a - 1) % d₁.numEdges = a - 1 := Nat.mod_eq_of_lt (by omega)
      simp only [h1, h2]
      conv_lhs => unfold col₂
      simp only [dif_neg (by omega : ¬(d₁.numEdges + 1 < d₁.numEdges))]
    -- ===== Forward Fox transfer: ∀ c ∈ d₂.crossings, triColorConditionAt d₂ col₂ c.
    -- We only unfold `triColorConditionAt` (NOT `colorAtNat`), so the Fox part keeps
    -- `colorAtNat` folded and the colour lemmas hcolF1/hcolF2b/hcolF2c fire by `rw`.
    -- (C) New kink ⟨a, n+1, n+2, n+2⟩: strands (a, n+1, n+2) all read `col₁ a`.
    have hC : triColorConditionAt d₂ col₂
        ⟨a, d₁.numEdges + 1, d₁.numEdges + 2, d₁.numEdges + 2⟩ := by
      simp only [triColorConditionAt]
      refine ⟨⟨by omega, by omega, by omega, by omega, by omega, by omega,
                by omega, by omega⟩, ?_⟩
      -- Path B: over-strand continuity c(e2)=c(e4), then Fox on (a, n+1, n+2).
      refine ⟨?_, ?_⟩
      · -- c(e2) = c(n+1) = col₁ a, c(e4) = c(n+2) = col₁ a (hcolF2b / hcolF2c).
        rw [hcolF2b, hcolF2c]
      · left
        refine ⟨?_, ?_⟩
        · rw [hcolF1 a ha1 ha2, hcolF2b]
        · rw [hcolF2b, hcolF2c]
    -- (iii) An unchanged crossing inherits d₁'s Fox: each preserved strand reads the
    --       same colour under `col₂` (via hcolF1), so the Fox condition is identical.
    have h_inherit : ∀ c, c ∈ d₁.crossings → triColorConditionAt d₂ col₂ c := by
      intro c hcmem
      have hfc : triColorConditionAt d₁ col₁ c := hfox₁ c hcmem
      simp only [triColorConditionAt] at hfc ⊢
      obtain ⟨⟨he11, he12, he21, he22, he31, he32, he41, he42⟩, ⟨harc, hfox⟩⟩ := hfc
      have h1 : d₂.colorAtNat col₂ c.e1 = d₁.colorAtNat col₁ c.e1 := hcolF1 c.e1 he11 he12
      have h2 : d₂.colorAtNat col₂ c.e2 = d₁.colorAtNat col₁ c.e2 := hcolF1 c.e2 he21 he22
      have h3 : d₂.colorAtNat col₂ c.e3 = d₁.colorAtNat col₁ c.e3 := hcolF1 c.e3 he31 he32
      have h4 : d₂.colorAtNat col₂ c.e4 = d₁.colorAtNat col₁ c.e4 := hcolF1 c.e4 he41 he42
      refine ⟨⟨he11, by omega, he21, by omega, he31, by omega, he41, by omega⟩, ⟨?_, ?_⟩⟩
      · -- Over-strand continuity col₂(e2)=col₂(e4) via colour-preservation + d₁'s arc-eq.
        rw [h2, h4]; exact harc
      · rcases hfox with ⟨h12, h23⟩ | ⟨h12, h23, h13⟩
        · left; refine ⟨?_, ?_⟩
          · rw [h1, h2]; exact h12
          · rw [h2, h3]; exact h23
        · right; refine ⟨?_, ?_, ?_⟩
          · rw [h1, h2]; exact h12
          · rw [h2, h3]; exact h23
          · rw [h1, h3]; exact h13
    -- (ii) The modified endpoint Y' preserves Fox: `isRenameOf` makes each strand of
    --       Y' read the same colour as the corresponding strand of the original crossing
    --       under `col₁` (unchanged strand via hcolF1; renamed `a→b` strand via hcolF2b).
    have hY' : triColorConditionAt d₂ col₂ Y' := by
      have hYorig : triColorConditionAt d₁ col₁ (d₁.crossings.get i) :=
        hfox₁ _ (List.get_mem d₁.crossings i)
      simp only [triColorConditionAt] at hYorig ⊢
      obtain ⟨⟨oe11, oe12, oe21, oe22, oe31, oe32, oe41, oe42⟩, ⟨harc_orig, hfoxo⟩⟩ := hYorig
      -- isRenameOf field-by-field: derive a colour-equation for each strand.
      obtain ⟨hre1, hre2, hre3, hre4⟩ := hrename
      -- Lemma: a renamed-or-unchanged strand `Y'.f` reads `col₁ (orig.f)`.
      have help : ∀ (hf : Nat) (ho : Nat) (hr : hf = ho ∨ (hf = d₁.numEdges + 1 ∧ ho = a))
                     (ho1 : 1 ≤ ho) (hon : ho ≤ d₁.numEdges),
          d₂.colorAtNat col₂ hf = d₁.colorAtNat col₁ ho := by
        intro hf ho hr ho1 hon
        rcases hr with heq | ⟨heqf, heqa⟩
        · rw [heq]; exact hcolF1 ho ho1 hon
        · -- hf = b = d₁.numEdges+1 (heqf), ho = a (heqa): col₂ reads col₁ a on edge b.
          rw [heqf, heqa, hcolF2b]
      have he1' : 1 ≤ Y'.e1 ∧ Y'.e1 ≤ d₂.numEdges := by
        rcases hre1 with heq | ⟨heqf, heqa⟩
        · rw [heq]; exact ⟨oe11, by omega⟩
        · rw [heqf]; exact ⟨by omega, by omega⟩
      have he2' : 1 ≤ Y'.e2 ∧ Y'.e2 ≤ d₂.numEdges := by
        rcases hre2 with heq | ⟨heqf, heqa⟩
        · rw [heq]; exact ⟨oe21, by omega⟩
        · rw [heqf]; exact ⟨by omega, by omega⟩
      have he3' : 1 ≤ Y'.e3 ∧ Y'.e3 ≤ d₂.numEdges := by
        rcases hre3 with heq | ⟨heqf, heqa⟩
        · rw [heq]; exact ⟨oe31, by omega⟩
        · rw [heqf]; exact ⟨by omega, by omega⟩
      have he4' : 1 ≤ Y'.e4 ∧ Y'.e4 ≤ d₂.numEdges := by
        rcases hre4 with heq | ⟨heqf, heqa⟩
        · rw [heq]; exact ⟨oe41, by omega⟩
        · rw [heqf]; exact ⟨by omega, by omega⟩
      have h1 : d₂.colorAtNat col₂ Y'.e1 = d₁.colorAtNat col₁ (d₁.crossings.get i).e1 :=
        help Y'.e1 (d₁.crossings.get i).e1 hre1 oe11 oe12
      have h2 : d₂.colorAtNat col₂ Y'.e2 = d₁.colorAtNat col₁ (d₁.crossings.get i).e2 :=
        help Y'.e2 (d₁.crossings.get i).e2 hre2 oe21 oe22
      have h3 : d₂.colorAtNat col₂ Y'.e3 = d₁.colorAtNat col₁ (d₁.crossings.get i).e3 :=
        help Y'.e3 (d₁.crossings.get i).e3 hre3 oe31 oe32
      have h4 : d₂.colorAtNat col₂ Y'.e4 = d₁.colorAtNat col₁ (d₁.crossings.get i).e4 :=
        help Y'.e4 (d₁.crossings.get i).e4 hre4 oe41 oe42
      refine ⟨⟨he1'.1, he1'.2, he2'.1, he2'.2, he3'.1, he3'.2, he4'.1, he4'.2⟩, ⟨?_, ?_⟩⟩
      · -- Over-strand continuity col₂(Y'.e2)=col₂(Y'.e4) via rename transfer + d₁'s arc-eq.
        rw [h2, h4]; exact harc_orig
      · rcases hfoxo with ⟨h12, h23⟩ | ⟨h12, h23, h13⟩
        · left; refine ⟨?_, ?_⟩
          · rw [h1, h2]; exact h12
          · rw [h2, h3]; exact h23
        · right; refine ⟨?_, ?_, ?_⟩
          · rw [h1, h2]; exact h12
          · rw [h2, h3]; exact h23
          · rw [h1, h3]; exact h13
    -- Membership split: c ∈ d₂.crossings = (set i Y') ++ [C]  →  C / Y' / unchanged.
    have hset_fwd : ∀ c, c ∈ d₁.crossings.set i.val Y' → c = Y' ∨ c ∈ d₁.crossings :=
      fun c hcm => mem_set_fwd i.val d₁.crossings Y' c hcm
    intro c hcmem
    rw [hd₂cross] at hcmem
    simp only [List.mem_append, List.mem_singleton] at hcmem
    rcases hcmem with hset | rfl
    · rcases hset_fwd c hset with rfl | hcorig
      · exact hY'
      · exact h_inherit c hcorig
    · exact hC

/-! ## 4. The unknot is NOT tricolorable

The unknot has a diagram with no crossings. Any coloring uses only
one strand, so the "at least 2 colors" condition fails.
-/

theorem unknot_not_tricolorable : ¬ Knot.isTricolorable unknot := by
  -- Proof: unknot has exactly 1 edge (numEdges = 1).
  -- Fin 1 has a single element ⟨0, _⟩, so every coloring is constant.
  -- Hence ∃ i j, coloring i ≠ coloring j is impossible.
  unfold Knot.isTricolorable IsTricolorable IsTriColoring
  rintro ⟨coloring, hcond, hedges, htwocolors⟩
  -- htwocolors : ∃ i j, coloring i ≠ coloring j
  -- But Fin 1 has only one element, contradiction
  have : ∀ (i j : Fin 1), coloring i = coloring j := by
    intro i j
    -- Fin 1 has only ⟨0, _⟩
    have hi : i = ⟨0, by omega⟩ := by exact Fin.ext_iff.mpr (Fin.val_eq_zero i)
    have hj : j = ⟨0, by omega⟩ := by exact Fin.ext_iff.mpr (Fin.val_eq_zero j)
    rw [hi, hj]
  obtain ⟨i, j, hne⟩ := htwocolors
  exact hne (this i j)

/-! ## 5. Corollary: the trefoil is not the unknot

Since tricolorability is an invariant, and the trefoil has it
but the unknot doesn't, they are different knots.
-/

theorem trefoil_not_unknot : ¬ KnotEquiv trefoil unknot := by
  intro h
  -- If trefoil ≈ unknot, then trefoil tricolorable ↔ unknot tricolorable
  -- But trefoil IS tricolorable and unknot IS NOT → contradiction
  -- Sketch: have := (tricolorable_invariant trefoilDiagram unknotDiagram h).mp
  --            trefoil_tricolorable
  --         exact unknot_not_tricolorable this
  exact sorry
  -- BLOCKED (Phase 4 update): the natural route (tricolorable_invariant +
  -- trefoil_tricolorable + unknot_not_tricolorable) is gated by
  -- tricolorable_invariant (this file), whose remaining blocker is the transfer
  -- lemma across Reidemeister moves (see the diagnostic there). The two pieces
  -- it composes — `trefoil_tricolorable` and `unknot_not_tricolorable` — are
  -- now both proven under the real Fox condition, so once the invariant lands
  -- this corollary follows by the sketch above.
  -- Alternative route attempted: prove ¬KnotEquiv directly by showing the diagrams
  -- cannot be Reidemeister-equivalent. Reidemeister1/2/3 are concrete, but
  -- ReidemeisterEquiv is the RTC of those steps; to show two diagrams are NOT
  -- connected one must classify all diagrams reachable from trefoilDiagram —
  -- out of reach without a normalisation invariant (e.g. crossing-number
  -- monotonicity under the moves, itself needing the true minimal crossing number).
  -- Dependency: tricolorable_invariant (→ transfer lemma across moves).

/-! ## 6. Crossing number bounds

The crossing number of a diagram gives an upper bound on the
minimal crossing number of the knot.
-/

/-- The trefoil has crossing number exactly 3.

This requires showing both:
  (a) there exists a diagram with 3 crossings (obvious)
  (b) no diagram with fewer crossings represents the trefoil

Part (b) requires the classification of knots by crossing number.
-/
theorem trefoil_crossing_number :
    Knot.crossingNumber trefoil = 3 := by
  -- Proof: under the Phase 3 provisional definition, crossingNumber equals
  -- crossingNumberOfDiagram, which counts the trefoil diagram's crossings.
  -- The standard trefoil PD-code has exactly 3 crossings.
  show trefoil.crossingNumberOfDiagram = 3
  unfold Knot.crossingNumberOfDiagram Knot.diagram trefoil trefoilDiagram
  decide

/-! ## 7. Unknotting number (definition only)

The unknotting number u(K) is the minimum number of crossing changes
needed to turn K into the unknot. This is a much harder invariant.

Reference: unknotting number is NP-hard to compute in general.
-/

/-- Change a crossing from positive to negative or vice versa. -/
def changeCrossing (c : PDCrossing) : PDCrossing where
  e1 := c.e1
  e2 := c.e4  -- swap over and under at this crossing
  e3 := c.e3
  e4 := c.e2

/-- Unknotting number: minimum crossing changes to reach the unknot. -/
def Knot.unknottingNumber (k : Knot) : Nat := by
  exact sorry
  -- BLOCKED: requires substantial infrastructure not yet in the project:
  --   1. Crossing change operation on KnotDiagram (changeCrossing exists but no
  --      well-formedness proof that the result is a valid diagram)
  --   2. Minimization over equivalence classes (Knot.crossingNumber has same issue)
  --   3. Reachability in a graph of diagrams
  -- Phase 4+ target — out of scope for Phase 2

/-! ## 8. Backward transfer (research scaffolding — Epic #2874, Phase 5 PR3)

This section is **research scaffolding only**: it records the proof obligation
for the backward direction of `Reidemeister1Connected.tricolorable_*` (the
mate of the forward lemma in PR #3000, awaiting merge at the time of writing),
together with empirical evidence pinning down the proof shape and a small
non-empty structural lemma about `Reidemeister1Connected` that is reusable in
both directions.

**No new sorries are introduced.** The backward theorem is intentionally not
stated here as a tactic-stub placeholder because the Knots-CI prose-header
sorries baseline is locked at 25 (see `lean-knot.yml`) and a research stub
would push it to 26. The proof obligation is therefore documented as a
comment-only contract and the next BG-prover / dedicated cycle will state the
theorem at the same time it proves it (the lemma + body land in one commit,
keeping the sorries baseline at 25 throughout).

### 8.1. Proof obligation (informal contract)

Under the fix-(a) (proper-arc) strengthening of `Reidemeister1Connected`
landed in PR #3003 (`133f7031`), the backward direction
```
∀ {d₁ d₂ : KnotDiagram},
  Reidemeister1Connected d₁ d₂ →
  IsTricolorable d₂ →
  IsTricolorable d₁
```
is conjectured TRUE. Together with `Reidemeister1Connected.tricolorable_forward`
(PR #3000), this gives the R1 bi-implication needed to unblock
`tricolorable_invariant` (§2, the long-standing tactic placeholder on
line 116) — modulo analogous statements for R2 and R3 (separate PRs).

### 8.2. Empirical evidence (brute-force, exhaustive on small diagrams)

A brute-force `3^n` colour search on all well-formed diagrams with
`numCrossings ∈ {1, 2}` and `numEdges ∈ {2, 4}` (2526 distinct wf diagrams,
generating 20184 valid connected R1 twists under proper-arc) reports
**0 backward failures**: for every `(d₁, d₂)` with
`Reidemeister1Connected d₁ d₂` and proper-arc, every tricoloring of `d₂`
admits a tricoloring of `d₁`. This is the same brute-force methodology that
de-risked fix (a) itself before PR #3003 was opened (see the body of #3003
for the analogous "24 monogon-loop failures → 0" empirical table).

A *finer* version of the search reports a non-trivial fact: in **48% of those
cases (139968 / 292032 (pair, col₂) probes)**, the *naïve* candidate
`col₁ := col₂|_{Fin d₁.numEdges}` (restrict to the first `d₁.numEdges`
indices) is NOT a valid tricoloring of `d₁` — the witness exists but it is
NOT this naïve restriction. The construction of `col₁` from `col₂` must
therefore be more nuanced.

### 8.3. Why the naïve restriction can fail

Recall (`Reidemeister.lean`) that `Reidemeister1Connected d₁ d₂` carries an
endpoint index `i`, an arc label `a` shared by two crossings of `d₁`, and a
renamed crossing `Y'` with `PDCrossing.isRenameOf Y' (d₁.crossings[i]) a b`
where `b = d₁.numEdges + 1`. The surgery is:
```
d₂.crossings = (d₁.crossings.set i Y') ++ [⟨a, b, c, c⟩]   (c = d₁.numEdges + 2)
d₂.numEdges   = d₁.numEdges + 2.
```
Fix any tricoloring `col₂` of `d₂`. The Fox condition at `Y'` reads on the
slots of `Y'`, where one occurrence of `a` was renamed to `b`. Setting
`col₁ := col₂|_{Fin d₁.numEdges}` evaluates the slot in `d₁`'s `Y` at
`col₂(a-1)`, while `col₂` evaluated the same slot of `Y'` at `col₂(b-1)`.
When the Fox condition forces `col₂(a-1) ≠ col₂(b-1)` (the all-distinct
branch at `Y'`), the naïve restriction violates Fox at `Y` in `d₁`.

The proper-arc hypothesis (`a` shared by another crossing `j ≠ i` of `d₁`)
is what prevents this failure mode from refuting the lemma globally: it forces
`a` to play a role in a *different* crossing, constraining the Fox structure
of `d₁` enough that a valid `col₁` always exists — but the construction is
NOT simply restriction. It must reconcile the colour of `a` between the
renamed slot of `Y'` (which `col₂` set freely as `col₂(b-1)`) and the other
occurrence of `a` at crossing `j` (which `col₁` inherits from `col₂(a-1)`).

### 8.4. Suggested proof strategies (for BG-prover / dedicated cycle)

1. **Direct case-analysis on the Fox mode of `Y` in `d₁`**: each PD slot
   matches one of four `isRenameOf` clauses (preserved or renamed). In each
   case, derive a colour-equality/inequality constraint on `col₂` at
   `{a-1, b-1}` and exhibit a `col₁` (built from `col₂` with a controlled
   override at `a-1` or at the other occurrence of `a`).
2. **Use the proper-arc witness directly**: from `∃ j ≠ i, a ∈ d₁.crossings[j]`,
   recover the secondary crossing of `a` in `d₁` and use its Fox condition
   under `col₂` to fix the colour of `a` in `col₁`.
3. **Reduce to forward**: build a *bijective* candidate `col₁` and check
   Fox at every crossing of `d₁`, exploiting the surgery equation and the
   fact that all crossings of `d₁` except `Y` are present *verbatim* (same
   labels, same indices) in `d₂.crossings`.

Empirically, strategy (1) suffices in 100% of the brute-forced cases. The
case analysis is mechanical but ~4-way; a small custom tactic could discharge
it uniformly.

### 8.5. Structural lemma: `Reidemeister1Connected.numEdges_eq`

A small, immediate consequence of the surgery equation: under
`Reidemeister1Connected d₁ d₂`, `d₂.numEdges = d₁.numEdges + 2`. The forward
proof (PR #3000) discharges this inline as a `have hd₂num` from
`congrArg (·.numEdges) hsurg`. Extracting it as a named lemma keeps it
available for both directions and any follow-up R1 lemma without duplication.
-/

/-- `Reidemeister1Connected` strictly grows the edge count by 2: the surgery
appends one new crossing with two fresh PD labels `b = d₁.numEdges + 1` and
`c = d₁.numEdges + 2`. Used by both `tricolorable_forward` (#3000) and the
forthcoming `tricolorable_backward` to bound colour-index arithmetic. -/
theorem Reidemeister1Connected.numEdges_eq {d₁ d₂ : KnotDiagram}
    (h : Reidemeister1Connected d₁ d₂) :
    d₂.numEdges = d₁.numEdges + 2 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hsurg⟩ := h
  simpa using congrArg (·.numEdges) hsurg

/-! ## 9. Backward transfer — decomposition analysis (Epic #2874, Phase 5)

Backward direction of `Reidemeister1Connected.tricolorable_*`: a tricoloring
of `d₂` restricts to one of `d₁`. Together with the forward lemma (PR #3000),
this gives the R1 bi-implication needed to unblock the §2 placeholder
`tricolorable_invariant`.

This section is a **documentation-only** analysis: it records the decomposition
the future proof will follow, identifies which sub-cases are easy vs.
research-level, and pins the empirical evidence. **No new Lean declaration
is added in this section** — the formal theorem will land in a dedicated PR
once the all-distinct sub-case is constructed. CI baseline remains unchanged.

### 9.1. Sub-case decomposition

Decompose by Fox mode at the new kink crossing
`C = ⟨a, b, c, c⟩` with `b = d₁.numEdges + 1`, `c = d₁.numEdges + 2`.

Fox at `C` under `col₂` reads on slots `(a, b, c)`. The two modes:
* **all-equal mode:** `col₂(a-1) = col₂(b-1) = col₂(c-1)`. The naïve
  restriction `col₁ := col₂|_{Fin d₁.numEdges}` then works directly: at the
  modified endpoint `Y` in `d₁`, the (renamed) `b` slot in `Y'` is replaced
  by an `a` slot in `Y` whose colour under `col₁` equals `col₂(a-1) = col₂(b-1)`
  by the all-equal condition. Fox is therefore preserved at `Y` in `d₁`.
* **all-distinct mode:** `col₂(a-1) ≠ col₂(b-1)`. Naïve restriction casts
  the wrong colour at the renamed slot of `Y` in `d₁` (reads `col₂(a-1)` where
  `Y'` read `col₂(b-1)`). Fox at `Y` in `d₁` may then break — this is the
  source of the empirical 48% naïve-fail rate documented in §8.2.

Furthermore, the "obvious" repair `col₁(a-1) := col₂(b-1)` does NOT work
either: under it, Fox at the proper-arc partner crossing `j ≠ i` (which
still contains `a` in `d₁`) reads the wrong colour at slot `a` (reads
`col₂(b-1)` instead of `col₂(a-1)`), so Fox at `j` breaks symmetrically.
The all-distinct case requires a globally-consistent multi-position
adjustment — likely via the colour-symmetry argument (permute TriColor
across the arc-path connecting `Y` to the proper-arc partner via `a`)
suggested by ai-01's deep-queue brief.

### 9.2. Empirical status

The brute-force search of §8.2 (292032 `(pair, col₂)` probes on 20184 valid
proper-arc twists with `numCrossings ≤ 2`) reports **0 backward failures**.
The conjecture is therefore strongly supported empirically; the obstruction
is purely the formal proof of the all-distinct mode.

### 9.3. Roadmap to the formal theorem

When the all-distinct construction is in hand, the theorem statement is:

```
theorem Reidemeister1Connected.tricolorable_backward {d₁ d₂}
    (h : Reidemeister1Connected d₁ d₂) (htri₂ : IsTricolorable d₂) :
    IsTricolorable d₁
```

The proof body will (i) extract the surgery shape via `numEdges_eq` (§8.5)
and `hsurg`, (ii) case-split on the Fox mode at `C`, (iii) close all-equal
by naïve restriction, (iv) close all-distinct by the colour-symmetry
construction. Reserved for a dedicated cycle; no strategic-placeholder
declaration is committed here to keep the CI baseline honest.

### 9.4. Empirical structural bounds (probe v2)

A finer enumeration on the same scope (`numCrossings = 2`, `numEdges = 4`,
292032 `(pair, col₂)` probes) characterises **the shape of the working `col₁`**
when the naïve restriction fails. Source: `scripts/tmp_backward_probe_v2.py`.

Naïve-fail rate, refined:
* Fox condition only on `col₁_naive`: **139968 / 292032 = 47.93%** (the figure
  reported in §8.2).
* Full Lean `IsTriColoring` (Fox **and** `≥ 2` colours used): **157248 / 292032
  = 53.85%**. The 17280 extra cases have a Fox-valid but monochrome
  `col₁_naive` — the surviving 4-edge restriction collapses to a single colour,
  which `IsTriColoring` rejects but Fox alone does not.

Structure of the working `col₁` (minimum-Hamming-distance extension from
`col₁_naive` to a valid Lean tricoloring of `d₁`):
* **Always exists** (0 / 157248 missing), matching the §8.2 "0 backward
  failures" claim under the stricter Lean criterion.
* **Bounded by 2 slot changes**: 110592 cases (70.3% of naïve-fails) are
  closed by a *single*-slot override; 46656 cases (29.7%) require *two*-slot
  override; no case needs three or more.
* **Single-slot override is not concentrated at slot `a-1`**: the four edge
  positions of `d₁` each receive 27648 single-slot overrides (uniformly
  distributed). Only 26352 of the 110592 single-slot overrides (≈ 24%) act
  at slot `a-1`; the remaining 76% act at a different edge of `d₁`. This
  refutes a tempting "override-at-`a` only" formulation.
* **The "obvious" closed form `col₁(a-1) := col₂(b-1)`** (the §9.1 candidate
  ruled out informally) covers **24192 / 157248 = 15.4%** of naïve-fails
  overall. Restricted to the subset where the override does act at slot `a-1`,
  it succeeds in **24192 / 26352 = 91.8%** of cases — confirming the
  qualitative §9.1 argument that even within its target slice it is incomplete
  (2160 single-slot-at-`a-1` cases need a different colour). The
  `(col₂(a-1), col₂(b-1))` distribution on naïve-fails is perfectly uniform
  across the 6 ordered colour pairs (26208 each), so the construction cannot
  be biased by a particular colour configuration.

Implications for the formal construction:
* The Hamming-bound (≤ 2 slot changes per `col₁`) is a **finite case bound**:
  any constructive proof can enumerate "single-slot at edge `k`" for
  `k ∈ Fin d₁.numEdges` and "two-slot at `(k, ℓ)`" for ordered pairs, then
  discharge each by a local Fox argument.
* The single-slot-at-non-`a` overrides (76% of single-slot, ≈ 53% of all
  naïve-fails) involve a slot whose Fox role is determined by the *proper-arc
  partner crossing* `j` and the rest of `d₁` — not by the kink. This is the
  geometric content the colour-symmetry argument captures.
* The 17280 monochrome-`col₁_naive` cases are a trivially-fixable sub-family:
  any other colour at any slot recovers `≥ 2` colours, and Fox is already
  preserved (it held on `col₁_naive` before the colour-count check). They
  collapse into the single-slot bucket above.

These bounds reduce the construction problem from "globally consistent
multi-position adjustment" (the §9.1 qualitative claim) to "a finite,
structured family of local overrides" — the formal proof can proceed
case-by-case once the local Fox-rebalancing lemma is stated. Reserved for
a dedicated cycle; CI baseline remains unchanged.

### 9.5. Fox-decoupling at the proper-arc partner crossing

Probe v3 (`scripts/tmp_backward_probe_v3.py`, same 292032-case scope)
characterises, for the 84240 single-slot-at-non-`a-1` overrides (≈ 53.6% of
all naïve-fails), the **geometric relation** between the override edge label
`ℓ := k + 1` and the proper-arc partner crossing `j`.

Findings:
* **66.15% (55728 / 84240) of overrides have `ℓ ∉ d₁.crossings[j]`** — the
  override edge does not appear in the partner crossing at all. Under the
  `wf` constraint at `numCrossings = 2, numEdges = 4`, that means `ℓ` appears
  twice in the *kink crossing* `i`, and the override propagates entirely
  through Fox at `i`.
* **33.85% (28512 / 84240) of overrides have `ℓ ∈ d₁.crossings[j]`** — and
  in **100%** of those cases, `ℓ` sits at **slot 3 of `j`** (the slot that
  `triColorConditionAt` ignores; see §3 / Lean Invariant.lean L82-87 where
  Fox reads only `(e1, e2, e3)`). Crucially, this means **0% of overrides
  touch a Fox-sensitive slot of `j`**.
* The `(a-slot in j, override-slot in j)` joint distribution is balanced:
  `a` at slots 0/1/2 of `j` each appears with `ℓ` at slot 3 of `j` in 9504
  cases (uniform across the 3 Fox positions of `a`). No bias toward a
  particular `a` slot.

Mechanism. The kink surgery at `Y` modifies a Fox slot of `i`. The naïve
restriction breaks Fox at `Y`. To repair, change the colour at some edge `ℓ`.
The probe shows that the chosen `ℓ` is *always* Fox-irrelevant at `j`:
either because `ℓ` does not appear in `j` (66% case), or because `ℓ` appears
only at the Fox-blind slot 3 of `j` (34% case). In both sub-cases, **the
override is invisible to Fox at `j`**, and the Fox-repair flows entirely
through Fox at `i` (where `ℓ` sits at a Fox slot by the same accounting).

This is the colour-symmetry argument of §9.1 made concrete: the override
"swaps" a colour at an edge whose only Fox role is at the kink crossing
itself, so changing it cannot break the partner's Fox condition. The
formal proof can therefore localise the rebalancing entirely at `i` once
the override edge is identified by its Fox-blindness at `j`.

The 29.7% two-slot bucket (§9.4) is the residue where this single-slot
Fox-blind move is unavailable; v3 does not characterise it yet (deferred
to §9.6 below). CI baseline remains unchanged.

### 9.6. Two-slot bucket Fox-coupling at the proper-arc partner crossing

Probe v4 (`scripts/tmp_backward_probe_v4.py`, same 292032-case scope)
characterises the 46656 two-slot overrides (29.7% of all naïve-fails) and
contrasts them with §9.5's single-slot Fox-decoupling.

Findings:
* **Q1 partner-presence.** **94.21% (43956 / 46656) of two-slot overrides
  have both override edges in `d₁.crossings[j]`**; the remaining 5.79%
  (2700) have exactly one in `j`; **none** have neither. So in the two-slot
  bucket, at least one override edge is always present at the partner
  crossing — a stark contrast with the 66.15% none-in-`j` rate of §9.5.
* **Q2 slot distribution in `j`.** Among the override edges that do appear
  in `j`, the slots split as **slot 0: 33.25%, slot 1: 32.34%, slot 2:
  31.43%, slot 3: 2.98%**. The Fox-sensitive slots (0, 1, 2) carry the
  overwhelming mass, opposite to §9.5's 100% concentration at slot 3.
* **Q3 edge pair distribution.** The six unordered pairs `(1,2), (1,3),
  (1,4), (2,3), (2,4), (3,4)` of override edge labels occur near-uniformly
  (7596–7956 each), with no pair forbidden — every pair of distinct
  `d₁`-edges can serve as a two-slot override under some `(d₁, surg, col₂)`.
* **Q4 Fox-visibility.** **94.21% (43956 / 46656) of two-slot overrides
  have at least one override edge sitting in a Fox slot (0, 1, 2) of `j`**;
  only 5.79% are entirely Fox-blind. The two-slot bucket is *Fox-coupled*
  at `j`, not Fox-decoupled.

Mechanism. The two-slot rebalancing changes colours at two edges, and the
probe shows that — almost always — at least one of those two edges is
Fox-relevant at the partner crossing `j`. A naïve local move at `i` would
therefore disturb the Fox condition at `j`; the rebalancing must propagate
across the proper arc, choosing colours at both override slots that
simultaneously restore Fox at `i` (via the surgery edge `a`) and preserve
Fox at `j` (via the cross-position constraint at the shared edge).

This is the missing half of the §9.1 colour-symmetry argument: §9.5 shows
the 70.3% single-slot bucket is *locally* repairable at `i` because the
override is Fox-decoupled at `j`; §9.6 shows the 29.7% two-slot bucket is
*not* locally repairable because the override is Fox-coupled at `j` —
exactly the regime that requires the §9.3 multi-position colour-symmetry
construction. The characterisation series §9.4 → §9.6 thus closes
empirically: every naïve failure falls into one of two buckets with
explicit, contrasting Fox-structure at the partner crossing.

The formal `tricolorable_backward` lemma therefore admits two clean
sub-cases — the locally repairable single-slot family (with the override
edge identified by Fox-blindness at `j`) and the cross-position two-slot
family (with both override slots constrained by Fox at `j` and at `i`).
Both still require formal proof at a future cycle; the present probe
quantifies *why* the two-slot bucket cannot be reduced to the single-slot
construction. CI baseline remains unchanged.
-/

/-! ## 10. Backward transfer — formal declaration (partial, Epic #2874 PR3)

The mate of `Reidemeister1Connected.tricolorable_forward` (PR #3000): a
tricoloring of `d₂` restricts to one of `d₁` under the strengthened connected-R1
model. The §9 decomposition analysis splits the proof by the Fox mode at the
appended kink `C = ⟨a, b, c, c⟩` (with `b = d₁.numEdges + 1`, `c = d₁.numEdges + 2`):

* **all-equal mode** (`col₂(a-1) = col₂(b-1) = col₂(c-1)`): the naïve
  restriction `col₁ := col₂|_{Fin d₁.numEdges}` is Fox-preserving — the
  `a → b` rename at the modified endpoint crossing is colour-invisible. The
  sub-lemma `tricolorable_backward` below proves the **colour-preservation**
  half constructively (a preserved label reads the same colour under `col₁` in
  `d₁` as under `col₂` in `d₂`; mirrors `tricolorable_forward`'s `hcolF1`).
* **all-distinct mode** (`col₂(a-1) ≠ col₂(b-1)`): needs the colour-symmetry /
  multi-position rebalancing characterised empirically in §9.4–§9.6 (the 47.9%
  naïve-fail regime). Research-level.

The remaining assembly — Fox-transfer at every `d₁` crossing (the unchanged
ones inherit via the colour-preservation fact, mirroring `h_inherit`; the
modified crossing `Y` and the all-distinct kink mode need the §9.1
construction), the `d₁.numEdges ≥ 2` lift (derivable from `d₁.wf` + the
proper-arc hypothesis, but a separate wf-parity argument), and the `≥ 2`-colour
lift — is left as three residual tactic `sorries` for ai-01 to advise on. This
raises the Knots-CI prose-header baseline from 25 to 28 (three residual tactic
`sorries`, one per sub-goal). User-authorised partial delivery (2026-06-15):
ship with residual sub-proof obligations that ai-01 will advise on. Together
with `tricolorable_forward` (#3000) this yields the R1 bi-implication needed
to unblock the §2 placeholder `tricolorable_invariant`. See #2874.
-/

/-- BACKWARD tricolorability transfer (PARTIAL): under the strengthened
    connected-R1 model `Reidemeister1Connected d₁ d₂`, a tricoloring of `d₂`
    restricts to a tricoloring of `d₁`. The colour-preservation sub-lemma is
    discharged constructively (mirrors `tricolorable_forward`'s `hcolF1`); the
    Fox-transfer assembly and the all-distinct kink mode remain as residual
    tactic `sorries` (see §9.1, §9.4–§9.6). -/
theorem Reidemeister1Connected.tricolorable_backward {d₁ d₂ : KnotDiagram}
    (h : Reidemeister1Connected d₁ d₂) (htri₂ : IsTricolorable d₂) :
    IsTricolorable d₁ := by
  obtain ⟨_hwf₁, _hwf₂, i, a, Y', _ρ, ha1, ha2, _hamem, _hproper, hrename, hsurg⟩ := h
  -- Surgery shape (mirrors `tricolorable_forward`).
  have hd₂num : d₂.numEdges = d₁.numEdges + 2 := by
    simpa using congrArg (·.numEdges) hsurg
  have hd₂cross : d₂.crossings =
      d₁.crossings.set i.val Y' ++
        [⟨a, d₁.numEdges + 1, d₁.numEdges + 2, d₁.numEdges + 2⟩] := by
    simpa using congrArg (·.crossings) hsurg
  obtain ⟨col₂, hfox₂, hge2₂, h2col₂⟩ := htri₂
  -- Naïve restriction: `col₁` embeds `d₁`'s edge indices into `d₂` (the +2
  -- fresh edges sit above `Fin d₁.numEdges`). Mirrors `tricolorable_forward`'s
  -- `emb`/`col₂` (PR #3000), reversed.
  have hd₂ge₁ : d₁.numEdges ≤ d₂.numEdges := by omega
  let col₁ : Fin d₁.numEdges → TriColor :=
    fun k => col₂ ⟨k.val, Nat.lt_of_lt_of_le k.isLt hd₂ge₁⟩
  -- (F1) Colour preservation: a preserved label `l ∈ [1, d₁.numEdges]` reads
  -- the SAME colour under `col₁` (in `d₁`) as under `col₂` (in `d₂`). Pure
  -- arithmetic on the `(l-1) % numEdges` index; the reverse of forward `hcolF1`.
  -- This is the constructive core that the unchanged-crossing Fox-inheritance
  -- (`h_inherit` in the forward proof) rides on.
  have hcolPres : ∀ l, 1 ≤ l → l ≤ d₁.numEdges →
      d₁.colorAtNat col₁ l = d₂.colorAtNat col₂ l := by
    intro l hl1 hln
    have hn0d₁ : d₁.numEdges ≠ 0 := by omega
    have hn0d₂ : d₂.numEdges ≠ 0 := by omega
    simp only [KnotDiagram.colorAtNat, dif_neg hn0d₁, dif_neg hn0d₂]
    have h1 : (l - 1) % d₁.numEdges = l - 1 := Nat.mod_eq_of_lt (by omega)
    have h2 : (l - 1) % d₂.numEdges = l - 1 := Nat.mod_eq_of_lt (by omega)
    simp only [h1, h2]
    rfl
  -- Residual assembly (§9): Fox-transfer at every `d₁` crossing under `col₁`
  -- (unchanged crossings inherit via `hcolPres` — mirrors forward `h_inherit`;
  -- the modified crossing `Y` and the all-distinct kink mode need the §9.1
  -- colour-symmetry construction), the `d₁.numEdges ≥ 2` lift (wf + proper-arc),
  -- and the `≥ 2`-colour lift. Left for ai-01 to advise on.
  refine' ⟨col₁, ?fox, ?num, ?col⟩
  case fox =>
    -- ∀ c ∈ d₁.crossings, triColorConditionAt d₁ col₁ c.
    -- Split on whether c survives into d₂. The only d₁ crossing that can drop
    -- out of d₂ is the modified one Y = d₁.crossings.get i (replaced by Y' at
    -- index i in d₂.crossings.set i Y' ++ [kink]). Everything else inherits Fox
    -- via hcolPres — the reverse of forward `h_inherit` (Invariant.lean L587-603).
    intro c hc
    by_cases hc2 : c ∈ d₂.crossings
    · -- pos: unchanged crossing. Fox holds under col₂ (hfox₂), transferred.
      have hfc2 : triColorConditionAt d₂ col₂ c := hfox₂ c hc2
      simp only [triColorConditionAt] at hfc2 ⊢
      obtain ⟨⟨he11, he12, he21, he22, he31, he32, he41, he42⟩, ⟨harc, hfox⟩⟩ := hfc2
      -- WF upper bound: hfc2 only gives c.e_k ≤ d₂.numEdges (= d₁.numEdges + 2).
      -- The stronger bound c.e_k ≤ d₁.numEdges comes from d₁.wf clause (a)
      -- (every d₁ edge label ∈ [1, numEdges]): c ∈ d₁.crossings ⟹ c.e_k ∈ d₁.edges.
      have hcross_ne : d₁.crossings ≠ [] := by
        intro h; rw [h] at hc; exact (List.mem_nil_iff _).mp hc
      have hwf := _hwf₁
      simp only [KnotDiagram.wf, if_neg hcross_ne, Bool.and_eq_true, List.all_eq_true,
        decide_eq_true_iff] at hwf
      obtain ⟨ha, _hb⟩ := hwf
      have hmem_e1 : c.e1 ∈ d₁.edges := by
        simp only [KnotDiagram.edges, List.mem_flatMap]; exact ⟨c, hc, by simp⟩
      have hmem_e2 : c.e2 ∈ d₁.edges := by
        simp only [KnotDiagram.edges, List.mem_flatMap]; exact ⟨c, hc, by simp⟩
      have hmem_e3 : c.e3 ∈ d₁.edges := by
        simp only [KnotDiagram.edges, List.mem_flatMap]; exact ⟨c, hc, by simp⟩
      have hmem_e4 : c.e4 ∈ d₁.edges := by
        simp only [KnotDiagram.edges, List.mem_flatMap]; exact ⟨c, hc, by simp⟩
      have he1 := ha c.e1 hmem_e1
      have he2 := ha c.e2 hmem_e2
      have he3 := ha c.e3 hmem_e3
      have he4 := ha c.e4 hmem_e4
      -- Colour preservation (reverse of forward hcolF1): d₁ colour = d₂ colour.
      have h1 : d₁.colorAtNat col₁ c.e1 = d₂.colorAtNat col₂ c.e1 :=
        hcolPres c.e1 he11 he1.2
      have h2 : d₁.colorAtNat col₁ c.e2 = d₂.colorAtNat col₂ c.e2 :=
        hcolPres c.e2 he21 he2.2
      have h3 : d₁.colorAtNat col₁ c.e3 = d₂.colorAtNat col₂ c.e3 :=
        hcolPres c.e3 he31 he3.2
      have h4 : d₁.colorAtNat col₁ c.e4 = d₂.colorAtNat col₂ c.e4 :=
        hcolPres c.e4 he41 he4.2
      refine ⟨⟨he11, he1.2, he21, he2.2, he31, he3.2, he41, he4.2⟩, ⟨?_, ?_⟩⟩
      · -- Over-strand continuity col₁(e2)=col₁(e4) via colour-preservation + d₂'s arc-eq.
        rw [h2, h4]; exact harc
      · rcases hfox with ⟨h12, h23⟩ | ⟨h12, h23, h13⟩
        · left; refine ⟨?_, ?_⟩
          · rw [h1, h2]; exact h12
          · rw [h2, h3]; exact h23
        · right; refine ⟨?_, ?_, ?_⟩
          · rw [h1, h2]; exact h12
          · rw [h2, h3]; exact h23
          · rw [h1, h3]; exact h13
    · -- neg: c = Y (the modified crossing, dropped from d₂ by `set i Y'`). Fox
      -- at Y under col₁ transfers from Fox at Y' under col₂ (hfox₂): unchanged
      -- strands via hcolPres, the renamed a→b strand via the kink all-equality
      -- (col₂(a)=col₂(n+1) supplies the backward analogue of forward hcolF2b).
      -- all-distinct kink mode: residual §9.1 (col₂(n+1)≠col₂(a) breaks the
      -- rename transfer). BG-prover ai-01 territory; user-authorised residual.
      -- (1) c = d₁.crossings.get i (= Y) and c ≠ Y'.
      have hnotmemSet : c ∉ d₁.crossings.set i Y' := by
        intro hmem; apply hc2; rw [hd₂cross]; exact List.mem_append_left _ hmem
      have hdrop := mem_drop_out i.val d₁.crossings Y' c i.isLt hc hnotmemSet
      rw [show c = d₁.crossings.get i from hdrop.1.symm]
      -- (2) Fox at Y' under col₂ (Y' sits at index i in d₂.crossings).
      have hY'mem : Y' ∈ d₂.crossings := by
        rw [hd₂cross]
        exact List.mem_append.mpr (.inl (mem_set_self i.val d₁.crossings Y' i.isLt))
      have hY'fox : triColorConditionAt d₂ col₂ Y' := hfox₂ _ hY'mem
      -- (3) Fox at the kink under col₂; split on its mode.
      have hCmem : (⟨a, d₁.numEdges + 1, d₁.numEdges + 2, d₁.numEdges + 2⟩ : PDCrossing)
          ∈ d₂.crossings := by
        rw [hd₂cross]; exact List.mem_append_right _ (List.mem_singleton_self _)
      have hCfox : triColorConditionAt d₂ col₂
          ⟨a, d₁.numEdges + 1, d₁.numEdges + 2, d₁.numEdges + 2⟩ := hfox₂ _ hCmem
      obtain ⟨_, hCmode⟩ := hCfox
      have hCmode' :
          (d₂.colorAtNat col₂ (d₁.numEdges + 1) = d₂.colorAtNat col₂ (d₁.numEdges + 2)) ∧
          ((d₂.colorAtNat col₂ a = d₂.colorAtNat col₂ (d₁.numEdges + 1) ∧
            d₂.colorAtNat col₂ (d₁.numEdges + 1) = d₂.colorAtNat col₂ (d₁.numEdges + 2)) ∨
           (d₂.colorAtNat col₂ a ≠ d₂.colorAtNat col₂ (d₁.numEdges + 1) ∧
            d₂.colorAtNat col₂ (d₁.numEdges + 1) ≠ d₂.colorAtNat col₂ (d₁.numEdges + 2) ∧
            d₂.colorAtNat col₂ a ≠ d₂.colorAtNat col₂ (d₁.numEdges + 2))) := hCmode
      rcases hCmode' with ⟨_hCarc, ⟨hCa_n1, _⟩ | _hdist⟩
      · -- all-equal kink mode: col₂(a)=col₂(n+1). Transfer Fox Y'→Y.
        simp only [triColorConditionAt] at hY'fox ⊢
        obtain ⟨⟨he'11, he'12, he'21, he'22, he'31, he'32, he'41, he'42⟩, ⟨harc_Y', hY'foxmode⟩⟩ := hY'fox
        obtain ⟨hre1, hre2, hre3, hre4⟩ := hrename
        -- WF bounds for Y's strands (d₁.wf clause a: every edge label ∈ [1,n]).
        have hcross_ne : d₁.crossings ≠ [] := by
          intro h; rw [h] at hc; exact (List.mem_nil_iff _).mp hc
        have hwf := _hwf₁
        simp only [KnotDiagram.wf, if_neg hcross_ne, Bool.and_eq_true, List.all_eq_true,
          decide_eq_true_iff] at hwf
        obtain ⟨ha_all, _⟩ := hwf
        have hYmem : (d₁.crossings.get i) ∈ d₁.crossings := List.get_mem _ _
        have hmem_eY1 : (d₁.crossings.get i).e1 ∈ d₁.edges := by
          simp only [KnotDiagram.edges, List.mem_flatMap]; exact ⟨_, hYmem, by simp⟩
        have hmem_eY2 : (d₁.crossings.get i).e2 ∈ d₁.edges := by
          simp only [KnotDiagram.edges, List.mem_flatMap]; exact ⟨_, hYmem, by simp⟩
        have hmem_eY3 : (d₁.crossings.get i).e3 ∈ d₁.edges := by
          simp only [KnotDiagram.edges, List.mem_flatMap]; exact ⟨_, hYmem, by simp⟩
        have hmem_eY4 : (d₁.crossings.get i).e4 ∈ d₁.edges := by
          simp only [KnotDiagram.edges, List.mem_flatMap]; exact ⟨_, hYmem, by simp⟩
        have heY1 := ha_all _ hmem_eY1
        have heY2 := ha_all _ hmem_eY2
        have heY3 := ha_all _ hmem_eY3
        have heY4 := ha_all _ hmem_eY4
        -- Per-strand colour transfer (unchanged via hcolPres; renamed via kink).
        have help : ∀ (hf ho : Nat)
            (hmode : hf = ho ∨ (hf = d₁.numEdges + 1 ∧ ho = a))
            (ho1 : 1 ≤ ho) (hon : ho ≤ d₁.numEdges),
            d₂.colorAtNat col₂ hf = d₁.colorAtNat col₁ ho := by
          intro hf ho hmode ho1 hon
          rcases hmode with heq | ⟨heqf, heqa⟩
          · rw [heq]; exact (hcolPres ho ho1 hon).symm
          · rw [heqf, heqa, ← hCa_n1]; exact (hcolPres a ha1 ha2).symm
        have h1 : d₂.colorAtNat col₂ Y'.e1 =
            d₁.colorAtNat col₁ (d₁.crossings.get i).e1 :=
          help Y'.e1 (d₁.crossings.get i).e1 hre1 heY1.1 heY1.2
        have h2 : d₂.colorAtNat col₂ Y'.e2 =
            d₁.colorAtNat col₁ (d₁.crossings.get i).e2 :=
          help Y'.e2 (d₁.crossings.get i).e2 hre2 heY2.1 heY2.2
        have h3 : d₂.colorAtNat col₂ Y'.e3 =
            d₁.colorAtNat col₁ (d₁.crossings.get i).e3 :=
          help Y'.e3 (d₁.crossings.get i).e3 hre3 heY3.1 heY3.2
        have h4 : d₂.colorAtNat col₂ Y'.e4 =
            d₁.colorAtNat col₁ (d₁.crossings.get i).e4 :=
          help Y'.e4 (d₁.crossings.get i).e4 hre4 heY4.1 heY4.2
        refine ⟨⟨heY1.1, heY1.2, heY2.1, heY2.2, heY3.1, heY3.2, heY4.1, heY4.2⟩, ⟨?_, ?_⟩⟩
        · -- Over-strand continuity col₁(Y.e2)=col₁(Y.e4) via rename transfer + Y's arc-eq under col₂.
          rw [← h2, ← h4]; exact harc_Y'
        rcases hY'foxmode with ⟨h12, h23⟩ | ⟨h12, h23, h13⟩
        · left; refine ⟨?_, ?_⟩
          · rw [← h1, ← h2]; exact h12
          · rw [← h2, ← h3]; exact h23
        · right; refine ⟨?_, ?_, ?_⟩
          · rw [← h1, ← h2]; exact h12
          · rw [← h2, ← h3]; exact h23
          · rw [← h1, ← h3]; exact h13
      · -- all-distinct kink mode: residual §9.1.
        --
        -- BREAKTHROUGH PROOF STRATEGY (cycle-3): Fox tricolorability is
        -- LINEAR over GF(3) — `triColorConditionAt` ⟺ c₁+c₂+c₃ ≡ 0 mod 3
        -- (verified: 0 disagreements over 7.5M wf diagrams, m∈{2,3}). The
        -- coloring space V(d) is a linear subspace of (Z/3)^n with
        -- dim V(d) ≥ n − m = m (m crossings ⇒ m homogeneous equations;
        -- n = 2m edges by wf parity). The 3 constant colorings form a
        -- 1-dim subspace, so dim V(d) ≥ m ≥ 2 ⟹ a non-constant
        -- Fox-coloring exists ⟹ IsTricolorable d. UNIVERSAL LEMMA:
        -- `wf d → d.crossings.length ≥ 2 → IsTricolorable d` (GF(3)
        -- rank-nullity; bridge `triColorConditionAt ↔ sum ≡ 0` by decide
        -- on Fin 3). d₁ qualifies (wf + proper-arc ⟹ ≥2 crossings, see
        -- `num` case), so d₁ is tricolorable INDEPENDENTLY of col₂ —
        -- WITHDRAWN under Path B (2026-06-23). The universal lemma above is
        -- FALSE classically: the figure-eight knot is well-formed with 4
        -- crossings yet is NOT Fox-tricolorable (only its 3 constant colourings
        -- exist). The per-crossing GF(3) bridge (`triColorFoxCondition_iff_sum_mod_three`,
        -- cycle-6) still holds, but it does not lift to universal colourability.
        -- This branch is therefore OPEN, awaiting a direct col2->col1 lift
        -- (see the Record below); it is NOT discharged by the withdrawn lemma.
        --
        -- Record — why the direct col₂→col₁ lift below is blocked: d₂.wf
        -- parity on fresh edge b=n₁+1 forces Y to hold `a` in exactly one
        -- slot, and d₁.wf forces `a` at exactly one proper-arc c_j; `a`
        -- is torn (Y wants col₁(a)=col₂(b), c_j wants col₁(a)=col₂(a),
        -- all-distinct denies equality). Projective / single-swap /
        -- σ∘col₂ all fail (Fox σ-invariant, #4003). The GF(3) lemma above
        -- bypasses this entirely — the col₂ construction is unnecessary.
        sorry
  case num =>
    -- d₁.numEdges ≥ 2. Diagnostic for the BG-prover (ai-01): d₁ is forced
    -- NON-DEGENERATE (`crossings ≠ []`) because `_hproper` supplies a distinct
    -- crossing index `j ≠ i`, both inhabiting `Fin d₁.crossings.length`. Hence
    -- `d₁.wf` (Basic.lean:261) takes its ELSE branch — the parity condition:
    -- every label in `[1, numEdges]` appears exactly twice
    -- (`(List.range numEdges).all (fun i => edges.count (i+1) = 2)`), and every
    -- occurring label lies in `[1, numEdges]` (clause (a)).
    --   * numEdges = 0: `edges ≠ []` (crossings ≠ []), so (a) demands labels in
    --     [1, 0] = ∅ — impossible.
    --   * numEdges = 1: a single crossing contributes 4 slots, each forced to
    --     label 1, so `edges.count 1 = 4 ≠ 2` — parity (b) fails.
    -- PROVEN: `_hproper` ⟹ two distinct `Fin crossings.length` indices `i ≠ j`
    -- ⟹ `crossings.length ≥ 2`, so `d₁` is non-degenerate and `wf` takes its
    -- parity branch. `edges.length = 4·crossings.length` (4 slots/crossing);
    -- parity (a)+(b) force `2·numEdges = edges.length`, hence `numEdges ≥ 4`.
    obtain ⟨j, hjne, _⟩ := _hproper
    have hlen2 : 2 ≤ d₁.crossings.length := by
      by_contra h
      have hi : i.val = 0 := by omega
      have hj : j.val = 0 := by omega
      exact hjne (Fin.ext (hj.trans hi.symm))
    have hne : d₁.crossings ≠ [] := by
      intro he; rw [he] at hlen2; simp at hlen2
    have hwf := _hwf₁
    simp only [KnotDiagram.wf, if_neg hne, Bool.and_eq_true] at hwf
    obtain ⟨ha_all, hb_all⟩ := hwf
    have hedges_len : d₁.edges.length = 4 * d₁.crossings.length := by
      have H : ∀ (cs : List PDCrossing),
          (cs.flatMap fun c => [c.e1, c.e2, c.e3, c.e4] : List Nat).length =
            4 * cs.length := by
        intro cs; induction cs with
        | nil => rfl
        | cons c cs' ih =>
          simp only [List.flatMap_cons, List.length_append, List.length_cons,
            List.length_nil, ih]; omega
      simp only [KnotDiagram.edges]; exact H d₁.crossings
    by_contra hne2
    -- `d₁.edges ≠ []`: length = 4·crossings.length ≥ 8 > 0.
    have hedges_ne : d₁.edges ≠ [] := by
      intro h0; rw [h0, List.length_nil] at hedges_len; omega
    obtain ⟨l0, hl0⟩ := List.exists_mem_of_ne_nil d₁.edges hedges_ne
    rw [List.all_eq_true] at ha_all hb_all
    -- Clause (a) at `l0 ∈ edges` forces `1 ≤ l0 ≤ numEdges`, so `numEdges ≥ 1`;
    -- with `hne2` (`numEdges ≤ 1`), `numEdges = 1`.
    have ha_l0 : 1 ≤ l0 ∧ l0 ≤ d₁.numEdges := by
      simpa using ha_all l0 hl0
    have hne1 : d₁.numEdges = 1 := by omega
    -- Clause (b) at `i = 0`: `edges.count 1 = 2`.
    have hb1 : d₁.edges.count 1 = 2 := by
      have h0mem : (0 : ℕ) ∈ List.range d₁.numEdges := by
        rw [List.mem_range]; omega
      have h := hb_all 0 h0mem; simpa using h
    -- Clause (a) (numEdges = 1) forces every edge = 1, so `count 1 = length`.
    have hall1 : ∀ e ∈ d₁.edges, e = 1 := by
      intro e he
      have h : 1 ≤ e ∧ e ≤ d₁.numEdges := by simpa using ha_all e he
      omega
    have hcount1 : d₁.edges.count 1 = d₁.edges.length := by
      have H : ∀ (l : List Nat), (∀ e ∈ l, e = 1) → l.count 1 = l.length := by
        intro l hl
        induction l with
        | nil => rfl
        | cons hd tl ih =>
          obtain rfl : hd = 1 := hl hd List.mem_cons_self
          rw [List.count_cons, List.length_cons, if_pos (by decide)]
          have := ih (fun e he => hl e (List.mem_cons_of_mem _ he))
          omega
      exact H d₁.edges hall1
    -- `4·crossings.length = count 1 = 2` contradicts `crossings.length ≥ 2`.
    rw [hcount1, hedges_len] at hb1; omega
  case col =>
    -- ≥ 2 colours under col₁. Split on the kink's Fox mode. The kink is
    -- C = ⟨a, n+1, n+2, n+2⟩ (the appended surgery crossing, hd₂cross).
    have hCmem : (⟨a, d₁.numEdges + 1, d₁.numEdges + 2, d₁.numEdges + 2⟩ : PDCrossing)
        ∈ d₂.crossings := by
      rw [hd₂cross]
      exact List.mem_append_right _ (by simp)
    have hCfox : triColorConditionAt d₂ col₂
        ⟨a, d₁.numEdges + 1, d₁.numEdges + 2, d₁.numEdges + 2⟩ := hfox₂ _ hCmem
    obtain ⟨_, hCmode⟩ := hCfox
    -- Coerce the `let`-bound Fox disjunction to its inlined form (defeq on C's
    -- fields: e1 = a, e2 = n+1, e3 = n+2) so `rcases` can split the disjunction.
    have hCmode' :
        (d₂.colorAtNat col₂ (d₁.numEdges + 1) = d₂.colorAtNat col₂ (d₁.numEdges + 2)) ∧
        ((d₂.colorAtNat col₂ a = d₂.colorAtNat col₂ (d₁.numEdges + 1) ∧
          d₂.colorAtNat col₂ (d₁.numEdges + 1) = d₂.colorAtNat col₂ (d₁.numEdges + 2)) ∨
         (d₂.colorAtNat col₂ a ≠ d₂.colorAtNat col₂ (d₁.numEdges + 1) ∧
          d₂.colorAtNat col₂ (d₁.numEdges + 1) ≠ d₂.colorAtNat col₂ (d₁.numEdges + 2) ∧
          d₂.colorAtNat col₂ a ≠ d₂.colorAtNat col₂ (d₁.numEdges + 2))) := hCmode
    rcases hCmode' with ⟨_hCarc, ⟨h_a_n1, h_n1_n2⟩ | _hdist⟩
    · -- all-equal kink mode. By contradiction: if col₁ is constant, col₂ is
      -- constant on the whole [0, d₂.numEdges) range (d₁-range via the col₁
      -- embedding; the two fresh indices via the kink's all-equal, tying them to
      -- col₂(a-1)) — contradicting h2col₂ (col₂ has ≥2 colours).
      have hn0d₂ : d₂.numEdges ≠ 0 := by omega
      -- Fixed Fin proofs (avoid `by omega` re-elaborating fresh each use).
      have ha_le : a - 1 < d₂.numEdges := by omega
      have hn_le : d₁.numEdges < d₂.numEdges := by omega
      have hn1_le : d₁.numEdges + 1 < d₂.numEdges := by omega
      have ha1_le : a - 1 < d₁.numEdges := by omega
      -- Reduce the kink's colorAtNat applications to bare col₂ applications,
      -- with the FIXED Fin proofs above.
      have ha_col : d₂.colorAtNat col₂ a = col₂ ⟨a - 1, ha_le⟩ := by
        simp only [KnotDiagram.colorAtNat, dif_neg hn0d₂]
        exact congrArg col₂ (Fin.ext (Nat.mod_eq_of_lt ha_le))
      have hn1_col : d₂.colorAtNat col₂ (d₁.numEdges + 1) =
          col₂ ⟨d₁.numEdges, hn_le⟩ := by
        simp only [KnotDiagram.colorAtNat, dif_neg hn0d₂]
        have hmod : (d₁.numEdges + 1 - 1) % d₂.numEdges = d₁.numEdges := by
          rw [Nat.mod_eq_of_lt (by omega)]; omega
        exact congrArg col₂ (Fin.ext hmod)
      have hn2_col : d₂.colorAtNat col₂ (d₁.numEdges + 2) =
          col₂ ⟨d₁.numEdges + 1, hn1_le⟩ := by
        simp only [KnotDiagram.colorAtNat, dif_neg hn0d₂]
        have hmod : (d₁.numEdges + 2 - 1) % d₂.numEdges = d₁.numEdges + 1 := by
          rw [Nat.mod_eq_of_lt (by omega)]; omega
        exact congrArg col₂ (Fin.ext hmod)
      rw [ha_col, hn1_col] at h_a_n1
      rw [hn1_col, hn2_col] at h_n1_n2
      -- h_a_n1  : col₂ ⟨a-1, ha_le⟩ = col₂ ⟨d₁.numEdges, hn_le⟩
      -- h_n1_n2 : col₂ ⟨d₁.numEdges, hn_le⟩ = col₂ ⟨d₁.numEdges+1, hn1_le⟩
      by_contra hncol
      push_neg at hncol
      obtain ⟨i₀, j₀, hij⟩ := h2col₂
      have hanch : ∀ k : Fin d₂.numEdges, col₂ k = col₂ ⟨a - 1, ha_le⟩ := by
        intro k
        rcases Nat.lt_trichotomy k.val d₁.numEdges with hklt | hkeq | hkgt
        · -- k.val < d₁.numEdges: col₂ k = col₁ ⟨k.val, hklt⟩ (embedding) = anchor.
          have hkemb : col₂ k = col₁ ⟨k.val, hklt⟩ := by simp only [col₁]
          have hncol_k : col₁ ⟨k.val, hklt⟩ = col₁ ⟨a - 1, ha1_le⟩ := hncol _ _
          rw [hkemb, hncol_k]
        · -- k.val = d₁.numEdges: kink all-equal ties it to col₂⟨a-1, ha_le⟩.
          rw [show k = (⟨d₁.numEdges, hn_le⟩ : Fin d₂.numEdges) from Fin.ext hkeq]
          exact h_a_n1.symm
        · -- k.val = d₁.numEdges + 1 (the only index > n in Fin (n+2)).
          have hk1 : k.val = d₁.numEdges + 1 := by omega
          rw [show k = (⟨d₁.numEdges + 1, hn1_le⟩ : Fin d₂.numEdges) from Fin.ext hk1]
          exact h_n1_n2.symm.trans h_a_n1.symm
      exact hij (by rw [hanch i₀, hanch j₀])
    · -- all-distinct kink mode: §9.1 residual. The fresh edges carry a NEW
      -- colour absent from the d₁ range, so the naïve col₁ restriction can be
      -- monochromatic and the ≥2-colour lift via col₂ fails (see the `fox`
      -- case above). [WITHDRAWN under Path B] The hoped-for discharge via the
      -- cycle-3 GF(3) universal lemma (`wf d, >=2 crossings => IsTricolorable d`,
      -- Fox linear over GF(3)) is FALSE classically: the figure-eight knot has
      -- 4 crossings yet is NOT Fox-tricolorable. The universal shortcut is gone,
      -- so this `col` residual is OPEN (as is the `fox` case above); both await a
      -- direct arc-respecting col2->col1 lift rather than the withdrawn lemma.
      sorry

end Knots
