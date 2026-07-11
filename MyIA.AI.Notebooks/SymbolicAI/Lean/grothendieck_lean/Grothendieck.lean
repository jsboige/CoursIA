/-
Hommage Grothendieck — visite de Mathlib du langage mathématique de Grothendieck
Alexandre Grothendieck (1928-2014), l'un des plus grands mathématiciens du XXᵉ siècle.

Grothendieck a été lauréat de la médaille Fields en 1966 pour ses travaux
révolutionnaires en géométrie algébrique. Né à Berlin en 1928, élevé en France,
réfugié durant la guerre, il a révolutionné notre conception des espaces
mathématiques en remplaçant l'étude ponctuelle par l'étude des morphismes et des
structures catégoriques. Il a refusé la médaille Fields au Congrès international
des mathématiciens de Moscou en 1966 pour des raisons éthiques, politique et
personnelle — fait unique dans l'histoire de la médaille. Il est décédé en 2014
à Saint-Lizier (Ariège), laissant une œuvre monumentale (plus de 10 000 pages
publiées, plusieurs milliers en chantier via EGA, SGA, et autres séminaires).

Ce workspace est un **hommage pédagogique** montrant combien de son langage
mathématique vit déjà dans Mathlib 4 :

  - Catégories, foncteurs, transformations naturelles
  - Cribles (sieves) et topologies de Grothendieck (triviale, discrète, dense)
  - Faisceaux sur un site
  - Schémas (espaces localement annelés localement isomorphes à Spec R)
  - Topologie de Zariski comme topologie de Grothendieck
  - Propriétés locales de morphismes (étale, lisse, séparé)
  - Topos de préfaisceaux, lemme de Yoneda, cohomologie des faisceaux

Ce n'est **PAS** une tentative de formaliser EGA/SGA. C'est une visite
pédagogique pour les apprenants qui découvrent ces concepts via Lean.

Substance réelle :
- `Grothendieck.CategoryAndSites` : objets/morphismes, foncteurs, transformations
  naturelles, catégories d'ensembles préfaiscés.
- `Grothendieck.SchemesTour` : visite structurée des schémas comme espaces
  localement annelés localement isomorphes à Spec R (Spec R localement
  annelé, recollement de schémas affines).
- `Grothendieck.ZariskiSite` : topologie de Zariski comme topologie de
  Grothendieck — couverture standard des ouverts D(f) = Spec R_f, foncteur
  structural, propriétés locales.
- `Grothendieck.MathlibMap` : table de correspondance entre les concepts
  formalisés ici et les modules Mathlib 4 sous-jacents.
- `Grothendieck.Calibration` : calibration track (Epic #1453) - quelques
  lemmes volontairement `sorry` pour gradient de difficulté du prouveur
  multi-agent.
- `Grothendieck.SieveLattice` : treillis des cribles sur un objet — clôtures,
  unions, intersections, relation d'inclusion.
- `Grothendieck.SieveOps` : opérations sur les cribles — image inverse,
  image directe, composition, compatibilités.
- `Grothendieck.CoverageGen` : familles couvrantes génératrices pour
  topologies de Grothendieck.
- `Grothendieck.CanonicalProps` : propriétés canoniques (mono, epi, iso)
  préservées par limites/colimites.
- `Grothendieck.SieveGenerate` : le crible engendré par une famille — clôture
  supérieure dans le treillis des cribles.
- `Grothendieck.DenseTopology` : topologies denses — tout ouvert non vide
  contient un ouvert dense couvrant ; lien avec la topologie de Zariski.
- `Grothendieck.Sheafification` : adjoint à gauche du foncteur d'oubli
  Préfaisceaux → Ensembles ; faisceautification universelle.
- `Grothendieck.LeftExact` : exactitude à gauche du foncteur de
  faisceautification (Grothendieck 1958, Tohoku).
- `Grothendieck.Subcanonical` : topologie sous-canonique — le faisceau
  représentable est un faisceau pour la topologie considérée (cf. Yoneda).
- `Grothendieck.SitePoints` : points d'un site — généralisation des points
  géométriques d'un schéma, faisceaux de points.
- `Grothendieck.SheafHom` : hom interne de faisceaux — structure de catégorie
  fermée (cartésien closed).
- `Grothendieck.ConstantSheaf` : faisceau constant associé à un ensemble,
  faisceau localement constant.
- `Grothendieck.Conservative` : carac conservative (fidèle) du foncteur
  d'oubli Préfaisceaux → Ensembles sur les faisceaux.
- `Grothendieck.SheafCohomology.Basic` : cohomologie Čech des faisceaux —
  foncteur δ dérivé, suite exacte longue.
- `Grothendieck.MayerVietorisSquare` : carrés de Mayer-Vietoris — recollement
  d'un objet par deux ouverts avec intersection.
- `Grothendieck.SheafCohomology.MayerVietoris` : suite de Mayer-Vietoris en
  cohomologie des faisceaux (analogue à la topologie algébrique).
- `Grothendieck.SheafCohomology.Cech` : cohomologie Čech comme cas
  particulier du complexe de Godement (Grothendieck 1957).
- `Grothendieck.YonedaLemma` : lemme de Yoneda — plongement pleinement
  fidèle d'une catégorie C dans la catégorie de foncteurs [C^op, Ens],
  c_{x} ↦ Hom_C(-, x) (Grothendieck 1960, CatAlg).

Tous les `sorry` ne sont pas comblés — la plupart sont des échafaudages
intentionnels pour le prouveur multi-agent (cf. Epic #1453).

---

English: Grothendieck tribute — Mathlib tour of Grothendieck's mathematical
language. Alexandre Grothendieck (1928-2014), one of the greatest
mathematicians of the 20th century.

Grothendieck was awarded the Fields medal in 1966 for his revolutionary work
in algebraic geometry. Born in Berlin in 1928, raised in France, refugee
during the war, he revolutionised our conception of mathematical spaces by
replacing punctual study with the study of morphisms and categorial
structures. He refused the Fields medal at the International Congress of
Mathematicians in Moscow in 1966 for ethical, political and personal reasons
— a unique fact in the medal's history. He passed away in 2014 in
Saint-Lizier (Ariège), leaving a monumental body of work (more than 10 000
published pages, several thousand in progress via EGA, SGA, and other
seminars).

This workspace is a **pedagogical tribute** showing how much of Grothendieck's
mathematical language already lives in Mathlib 4:

  - Categories, functors, natural transformations
  - Sieves and Grothendieck topologies (trivial, discrete, dense)
  - Sheaves on a site
  - Schemes (locally ringed spaces locally isomorphic to Spec R)
  - Zariski topology as a Grothendieck topology
  - Local properties of morphisms (etale, smooth, separated)
  - Topos of presheaves, Yoneda lemma, sheaf cohomology

This is **NOT** an attempt to formalize EGA/SGA. It is a curated tour for
learners encountering these concepts through Lean for the first time.

Substance (English):
- `Grothendieck.CategoryAndSites`: objects/morphisms, functors, natural
  transformations, categories of presheaves.
- `Grothendieck.SchemesTour`: structured tour of schemes as locally ringed
  spaces locally isomorphic to Spec R.
- `Grothendieck.ZariskiSite`: Zariski topology as a Grothendieck topology —
  standard cover by D(f) = Spec R_f, structure functor, local properties.
- `Grothendieck.MathlibMap`: correspondence table between the formalized
  concepts and the underlying Mathlib 4 modules.
- `Grothendieck.Calibration`: calibration track (Epic #1453) - intentional
  sorry as a difficulty gradient for the multi-agent prover.
- `Grothendieck.SieveLattice`: lattice of sieves on an object — closures,
  unions, intersections, inclusion order.
- `Grothendieck.SieveOps`: sieve operations — inverse image, direct image,
  composition, compatibilities.
- `Grothendieck.CoverageGen`: generating covering families for Grothendieck
  topologies.
- `Grothendieck.CanonicalProps`: canonical properties (mono, epi, iso)
  preserved by limits/colimits.
- `Grothendieck.SieveGenerate`: sieve generated by a family — upper closure
  in the lattice of sieves.
- `Grothendieck.DenseTopology`: dense topologies — every non-empty open
  contains a covering dense open; link with the Zariski topology.
- `Grothendieck.Sheafification`: left adjoint of the forgetful functor
  Presheaves → Sets; universal sheafification.
- `Grothendieck.LeftExact`: left exactness of the sheafification functor
  (Grothendieck 1958, Tohoku).
- `Grothendieck.Subcanonical`: subcanonical topology — the representable
  presheaf is a sheaf for the topology considered (cf. Yoneda).
- `Grothendieck.SitePoints`: points of a site — generalisation of geometric
  points of a scheme, point sheaves.
- `Grothendieck.SheafHom`: internal hom of sheaves — structure of cartesian
  closed category.
- `Grothendieck.ConstantSheaf`: constant sheaf associated to a set,
  locally constant sheaf.
- `Grothendieck.Conservative`: conservativeness (faithfulness) of the
  forgetful functor Presheaves → Sets on sheaves.
- `Grothendieck.SheafCohomology.Basic`: Čech cohomology of sheaves —
  derived δ functor, long exact sequence.
- `Grothendieck.MayerVietorisSquare`: Mayer-Vietoris squares — gluing of
  an object by two opens with intersection.
- `Grothendieck.SheafCohomology.MayerVietoris`: Mayer-Vietoris sequence in
  sheaf cohomology (analogue of algebraic topology).
- `Grothendieck.SheafCohomology.Cech`: Čech cohomology as a particular case
  of the Godement complex (Grothendieck 1957).
- `Grothendieck.YonedaLemma`: Yoneda lemma — fully faithful embedding of a
  category C into the functor category [C^op, Set], c_{x} ↦ Hom_C(-, x)
  (Grothendieck 1960, CatAlg).

Not all `sorry`s are filled — most are intentional scaffolds for the
multi-agent prover (cf. Epic #1453).

Convention i18n (EPIC #4980 ratifiée user 2026-07-04) : ce fichier root
aggregator est bilingue inline (FR canonique d'abord, EN en miroir),
conformément au pattern canonique `CooperativeGames.lean` (PR #5883,
pilote EPIC), `Utility.lean` (PR #6045), `RepeatedGames.lean` (PR #6048),
`Minimax.lean` (PR #6101), `SocialChoice.lean` (PR #6106), `Conway.lean`
(PR #6111). Les modules substantiels vivent dans des fichiers siblings (cf.
structure lake ci-dessous), auto-découverts par le
`lean_lib «Grothendieck»` du lakefile (cf. `globs` glob par défaut).
-/
import Grothendieck.CategoryAndSites
import Grothendieck.SchemesTour
import Grothendieck.ZariskiSite
import Grothendieck.MathlibMap
import Grothendieck.Calibration
import Grothendieck.SieveLattice
import Grothendieck.SheafBasics
import Grothendieck.SieveOps
import Grothendieck.CoverageGen
import Grothendieck.CanonicalProps
import Grothendieck.SieveGenerate
import Grothendieck.DenseTopology
import Grothendieck.Sheafification
import Grothendieck.LeftExact
import Grothendieck.Subcanonical
import Grothendieck.SitePoints
import Grothendieck.SheafHom
import Grothendieck.ConstantSheaf
import Grothendieck.Conservative
import Grothendieck.SheafCohomology.Basic
import Grothendieck.MayerVietorisSquare
import Grothendieck.SheafCohomology.MayerVietoris
import Grothendieck.SheafCohomology.Cech
import Grothendieck.YonedaLemma
