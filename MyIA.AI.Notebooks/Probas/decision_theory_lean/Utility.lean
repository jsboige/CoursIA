import Utility.Basic
import Utility.Axioms
import Utility.Representation

/-!
  Théorie de la décision — Utilité espérée de von Neumann–Morgenstern

  Formalisation des fondements décisionnels de l'utilité espérée :
  loteries, les quatre axiomes de rationalité vNM, et le théorème de
  représentation de l'utilité espérée.

  ## Contenu
  - `Utility.Basic` : loteries (distributions à support fini), espérance,
    mélanges convexes, identités affines (prouvées, sans sorry).
  - `Utility.Axioms` : complétude, transitivité, indépendance, continuité ;
    `IsRational` regroupe les quatre axiomes vNM.
  - `Utility.Representation` : `IsExpectedUtilityRep`, la direction de
    validité (représentation ⟹ rationalité, prouvée sans sorry), stabilité
    affine (unicité à transformation affine positive près), et l'algèbre
    ordre-théorétique de `≻` / `~` (ordre strict, relation d'équivalence,
    trichotomie). La direction d'existence est documentée comme un jalon
    ouvert.

  ## Statut
  - Prouvé sans sorry : algèbre de l'espérance, les quatre axiomes sous une
    représentation, stabilité affine, et l'algèbre ordre-théorétique de la
    préférence stricte et de l'indifférence (ordre strict + équivalence +
    trichotomie).
  - Ouvert (prochain jalon) : la direction d'existence `IsRational P → ∃ u,
    IsExpectedUtilityRep u P` (le théorème substantiel de Herstein–Milnor).

  ## Références croisées
  - Infer-14 (Infer.NET) : utilité espérée bayésienne sous incertitude
    a posteriori.
  - PyMC-1 (PyMC) : estimation de l'utilité espérée par échantillonnage
    a posteriori.

  ---

  # Decision Theory — von Neumann–Morgenstern Expected Utility

  Formalisation of the decision-theoretic foundations of expected utility:
  lotteries, the four vNM rationality axioms, and the expected-utility
  representation theorem.

  ## Contents
  - `Utility.Basic`: lotteries (finite-support distributions), expectation,
    convex mixtures, affine identities (proved, sorry-free).
  - `Utility.Axioms`: completeness, transitivity, independence, continuity;
    `IsRational` bundles the four vNM axioms.
  - `Utility.Representation`: `IsExpectedUtilityRep`, the sound direction
    (representation ⟹ rationality, proved sorry-free), affine stability
    (uniqueness up to positive affine transformation), and the order-theoretic
    algebra of `≻` / `~` (strict order, equivalence relation, trichotomy). The
    existence direction is documented as an open milestone.

  ## Status
  - Proved sorry-free: expectation algebra, all four axioms under a
    representation, affine stability, and the order-theoretic algebra of strict
    preference and indifference (strict order + equivalence + trichotomy).
  - Open (next milestone): the existence direction `IsRational P → ∃ u,
    IsExpectedUtilityRep u P` (the substantive Herstein–Milnor theorem).

  ## Cross-references
  - Infer-14 (Infer.NET): Bayesian expected utility under posterior uncertainty.
  - PyMC-1 (PyMC): expected-utility estimation by posterior sampling.

  Convention i18n (EPIC #4980, décision user 2026-07-04) : ce fichier root
  aggregator est bilingue inline (FR canonique d'abord, EN en miroir),
  conformément au pattern canonique `Gittins.lean` du même lake. Les modules
  substantiels (`Utility.Basic`, `Utility.Axioms`, `Utility.Representation`)
  vivent dans des fichiers siblings `_en.lean` séparés, auto-découverts par
  le `globs := #[`Utility.*]` du lakefile.
-/
