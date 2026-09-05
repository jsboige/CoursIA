/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Hommage Grothendieck — Partie 69 : forme flèche de la topologie étale

Alexandre Grothendieck (1928-2014).

Extension Phase 5 (#2159, EPIC #1646).

Les parties 1-68 ont établi les fondamentaux : catégories, cribles,
topologies, lois de treillis, identités de pullback, bases de faisceaux,
clôture couvrante, calibration, sous-canonicalité, topologies denses,
faisceaux, hom interne, cohomologie de Čech, limite de Mayer-Vietoris,
extensions de Kan, adjonctions, monades, équivalences, catégories monoïdales,
la construction de Grothendieck, l'image directe/exceptionnelle, la forme
flèche de la couverture, les lois de cohérence du pseudo-foncteur pullback,
les lois de treillis indexées, la forme flèche des topologies dense,
extrémales, de l'adjonction pushforward-pullback, du bind, de la topologie
engendrée par une prétopologie, de la topologie induite le long d'un
foncteur, des foncteurs préservant les couvertures, des lois de
composition de ces foncteurs, de la topologie engendrée par une couverture
au sens de `Coverage`, de la topologie engendrée par une pré-couverture,
de la topologie de Zariski sur les schémas, de la topologie atomique, du
classifieur de sous-objets, de la topologie de Lawvere–Tierney et de son
dictionnaire, des foncteurs continus et du lemme de comparaison, de la
construction Plus, de la condition de faisceau produit-égaliseur et de ses
caractérisations, du spectre de topologies d'un préfaisceau, du spectre de
surjectivité locale, et de la topologie d'un espace topologique.

Cette partie applique le fil conducteur « forme flèche » à la **topologie
étale** `Scheme.etaleTopology` — la topologie des sites étales, cœur de la
cohomologie étale de SGA 4-½ et du programme de Weil dont Grothendieck fut
l'architecte. Mathlib définit `etaleTopology := grothendieckTopology @Etale`
(la topologie engendrée par les familles d'applications étales conjointement
surjectives), fournit le pont ponctuel `mem_grothendieckTopology_iff`
(appartenance = existence d'une couverture étale raffinant le crible) et la
comparaison `zariskiTopology_le_etaleTopology`, mais **aucune loi ne connecte
la topologie étale à la forme flèche `J.Covers`**. On comble le trou par
huit théorèmes propres :

  - `etale_topology_eq_pretopology` : pont de définition, `etaleTopology =
    etalePretopology.toGrothendieck` (miroir exact de `zariskiTopology_eq`) ;
  - `covers_iff_etale` (central, moule P54/P56 instancié) : pour des
    schémas `X Y`, une flèche `f : Y ⟶ X` et un crible `S` sur `X`,
    `etaleTopology.Covers S f ↔ ∃ 𝒰 : Scheme.Cover.{u}
    Scheme.etalePrecoverage Y, Presieve.ofArrows 𝒰.X 𝒰.f ≤ S.pullback f`
    — la couverture flèche se teste sur `Y` par l'existence d'une famille
    étale couvrante raffinant le pullback ;
  - `covers_etale_of_cover` : la direction constructive du central ;
  - `zariski_covers_etale` : toute couverture de Zariski est une couverture
    étale (corollaire flèche de `zariskiTopology_le_etaleTopology` — les
    immersions ouvertes sont étales) ;
  - `covers_etale_of_mem` : toute flèche de `S` couvre toute flèche ;
  - `covers_etale_precomp` : stabilité par précomposition ;
  - `covers_etale_id` : retombée ponctuelle à l'identité ;
  - `covers_etale_top` : le crible maximal couvre toute flèche.

Le fil conducteur : tout énoncé ponctuel `S ∈ J X` admet un jumeau en forme
flèche `J.Covers S f` (par `covers_iff`, `S.pullback f ∈ J Y`). Après la
topologie dense (P44), les topologies cohérente, régulière et extensive
(P55a-c), la topologie de Zariski (P56) et la topologie atomique (P57), la
topologie étale poursuit la série des topologies nommées — et c'est celle
qui porte le nom de Grothendieck dans l'histoire des mathématiques.

Convention i18n (EPIC #4980 ratifiée 2026-07-04) : ce module est apparié avec
son jumeau anglais dans le fichier sibling `CoversEtaleArrow_en.lean`
(modèle sibling pair, voir PR #6154 pour le pilote sur `Utility.lean`).
Namespace suffix `_en` appliqué au fichier EN (anti-collision, conforme
code-style.md #4980). Les énoncés de théorèmes, les noms de lemmes, les
tactiques Lean et les références Mathlib restent en anglais ; seules les
docstrings `/-- ... -/` et les commentaires `-- ...` diffèrent entre les
deux fichiers (préservation byte-identity).

Epic #1646, Phase 5 (#2159). Tous les `sorry`s éliminés à la création.
-/

import Mathlib.AlgebraicGeometry.Sites.Etale

namespace Grothendieck.CoversEtaleArrow

open CategoryTheory AlgebraicGeometry

universe u

/-!
## Section 1 : le pont de définition et la forme flèche centrale

La topologie étale de Mathlib est un `abbrev` sur `(precoverage @Etale).toGrothendieck`.
On établit d'abord le pont vers la prétopologie (miroir de `zariskiTopology_eq`),
puis la forme flèche centrale : `S` couvre `f` pour `etaleTopology` si et
seulement si le pullback `S.pullback f` contient une famille d'applications
étales conjointement surjectives (une `Scheme.Cover.{u} Scheme.etalePrecoverage Y`).
-/

/-- Pont de définition : la topologie étale est la topologie engendrée par
    la prétopologie étale — le miroir exact de `zariskiTopology_eq`.
    Preuve : `Precoverage.toGrothendieck_toPretopology_eq_toGrothendieck`
    relie les deux chemins de génération. -/
theorem etale_topology_eq_pretopology :
    Scheme.etaleTopology.{u} = Scheme.etalePretopology.toGrothendieck :=
  Precoverage.toGrothendieck_toPretopology_eq_toGrothendieck.symm

/-- Forme flèche de la topologie étale : `etaleTopology.Covers S f` si et
    seulement s'il existe une couverture étale `𝒰` de `Y` dont la famille
    de flèches raffine le pullback `S.pullback f`.
    Preuve : `covers_iff` réduit le membre gauche à `S.pullback f ∈
    etaleTopology Y`, puis `mem_grothendieckTopology_iff` (l'appartenance à
    la topologie engendrée par `@Etale` est l'existence d'une couverture
    raffinante) conclut. -/
theorem covers_iff_etale {X Y : Scheme.{u}} (S : Sieve X) (f : Y ⟶ X) :
    Scheme.etaleTopology.Covers S f ↔
      ∃ 𝒰 : Scheme.Cover.{u} Scheme.etalePrecoverage Y,
        Presieve.ofArrows 𝒰.X 𝒰.f ≤ S.pullback f := by
  rw [GrothendieckTopology.covers_iff]
  exact Scheme.mem_grothendieckTopology_iff (P := @Etale)

/-- Direction constructive du théorème central : une couverture étale
    explicite de `Y` raffinant `S.pullback f` witness la couverture flèche. -/
theorem covers_etale_of_cover {X Y : Scheme.{u}} (S : Sieve X) (f : Y ⟶ X)
    (𝒰 : Scheme.Cover.{u} Scheme.etalePrecoverage Y)
    (h : Presieve.ofArrows 𝒰.X 𝒰.f ≤ S.pullback f) :
    Scheme.etaleTopology.Covers S f :=
  (covers_iff_etale S f).2 ⟨𝒰, h⟩

/-!
## Section 2 : monotonicité Zariski → étale

`zariskiTopology_le_etaleTopology` dit que la topologie de Zariski est plus
fine... plus *grossière* : toute immersion ouverte est étale (`IsOpenImmersion →
Etale`), donc toute couverture de Zariski est une couverture étale. La forme
flèche de cette comparaison est un transport immédiat par `covers_iff`.
-/

/-- Toute couverture flèche de Zariski est une couverture flèche étale :
    `zariskiTopology.Covers S f → etaleTopology.Covers S f`.
    Preuve : `covers_iff` des deux côtés, puis `zariskiTopology_le_etaleTopology`
    transporte l'appartenance du pullback. -/
theorem zariski_covers_etale {X Y : Scheme.{u}} (S : Sieve X) (f : Y ⟶ X)
    (h : Scheme.zariskiTopology.Covers S f) :
    Scheme.etaleTopology.Covers S f := by
  rw [GrothendieckTopology.covers_iff] at h ⊢
  exact Scheme.zariskiTopology_le_etaleTopology Y h

/-!
## Section 3 : flèches témoins, stabilité, identité

Trois conséquences du calcul des cribles, indépendantes de la spécificité
étale (elles valent pour toute topologie, mais s'énoncent ici pour `etaleTopology`
comme lois de la forme flèche étale) : une flèche *témoin* appartenant à `S`
suffit, la couverture flèche est stable par précomposition, et la forme
au-dessus de l'identité retombe sur l'appartenance ponctuelle.
-/

/-- Toute flèche de `S` couvre toute flèche vers `X` pour la topologie
    étale : `S f → etaleTopology.Covers S f`.
    Preuve : `S f` force `S.pullback f = ⊤` (`Sieve.pullback_eq_top_of_mem`),
    et le crible maximal appartient à toute topologie (`top_mem`). -/
theorem covers_etale_of_mem {X Y : Scheme.{u}} (S : Sieve X) {f : Y ⟶ X}
    (h : S f) :
    Scheme.etaleTopology.Covers S f := by
  rw [GrothendieckTopology.covers_iff, Sieve.pullback_eq_top_of_mem S h]
  exact GrothendieckTopology.top_mem Scheme.etaleTopology Y

/-- La forme flèche étale est stable par précomposition : si `S` couvre
    `f : Y ⟶ X`, alors `S` couvre aussi `g ≫ f` pour toute `g : Z ⟶ Y`.
    Preuve : `covers_iff` des deux côtés, puis `Sieve.pullback_comp`
    identifie `S.pullback (g ≫ f)` à `(S.pullback f).pullback g`, et
    `pullback_stable` de la topologie conclut. -/
theorem covers_etale_precomp {X Y Z : Scheme.{u}} (S : Sieve X)
    (f : Y ⟶ X) (g : Z ⟶ Y) :
    Scheme.etaleTopology.Covers S f →
      Scheme.etaleTopology.Covers S (g ≫ f) := by
  intro h
  rw [GrothendieckTopology.covers_iff] at h ⊢
  rw [Sieve.pullback_comp]
  exact Scheme.etaleTopology.pullback_stable g h

/-- La forme flèche étale au-dessus de l'identité coïncide avec
    l'appartenance ponctuelle :
    `etaleTopology.Covers S (𝟙 X) ↔ S ∈ etaleTopology X`.
    Preuve : `covers_iff` puis `Sieve.pullback_id`. -/
theorem covers_etale_id {X : Scheme.{u}} (S : Sieve X) :
    Scheme.etaleTopology.Covers S (𝟙 X) ↔
      S ∈ Scheme.etaleTopology X := by
  rw [GrothendieckTopology.covers_iff, Sieve.pullback_id]

/-- Le crible maximal couvre toute flèche pour la topologie étale :
    `etaleTopology.Covers ⊤ f`.
    Preuve : `covers_iff` puis `Sieve.pullback_top`, et `top_mem` conclut. -/
theorem covers_etale_top {X Y : Scheme.{u}} (f : Y ⟶ X) :
    Scheme.etaleTopology.Covers ⊤ f := by
  rw [GrothendieckTopology.covers_iff, Sieve.pullback_top]
  exact GrothendieckTopology.top_mem Scheme.etaleTopology Y

end Grothendieck.CoversEtaleArrow
