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

  Convention i18n (EPIC #4980, décision user 2026-07-04) : ce fichier root
  aggregator est **FR canonique**, avec son miroir anglais dans le fichier
  sibling `Utility_en.lean` (modèle sibling pair ratifié 2026-07-04, cf
  `code-style.md` §Lean i18n). Les modules substantiels (`Utility.Basic`,
  `Utility.Axioms`, `Utility.Representation`) vivent dans des fichiers
  siblings `_en.lean` séparés (auto-découverts par le
  `globs := #[`Utility.*]` du lakefile).
-/
