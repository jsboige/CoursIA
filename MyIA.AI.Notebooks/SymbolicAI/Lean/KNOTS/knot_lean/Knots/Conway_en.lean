/-
  Knots.Conway — aggregator of the Conway and Kinoshita-Terasaka knots
  ==========================================================================

  Historically a monolith (mutation, PD codes, Alexander polynomial,
  Dehn proofs, slice, Piccirillo), this module is reduced to the
  Option A plan aggregator stub (#18397, slices 2-4): the content now
  lives in the sub-modules, all available transitively via
  `import Knots.Conway_en` (historical entry point preserved):

  - `Knots.Mutation_en` — Conway mutation (slice 2);
  - `Knots.ConwayPD_en` — PD codes of both knots 11n34/11n42 (slice 2);
  - `Knots.ArcPartition_en` — arc partition of the PD code (slice 3);
  - `Knots.AlexanderTrivial_en` — Alexander polynomial and Dehn proofs
    (conway_trivial_alexander, KT_trivial_alexander) (slice 4).

  The slice/Piccirillo part lives in `Knots.Slice_en` (sister module,
  imported separately — Slice imports Conway, the reverse would cycle).
-/

import Knots.Basic_en
import Knots.Invariant_en
import Knots.Mutation_en
import Knots.ConwayPD_en
import Knots.ArcPartition_en
import Knots.AlexanderTrivial_en
