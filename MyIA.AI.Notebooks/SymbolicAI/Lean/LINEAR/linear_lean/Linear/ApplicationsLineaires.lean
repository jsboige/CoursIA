/-
  Linear.ApplicationsLineaires — marche 2 (chapitre 3 d'Axler, sections 3.A/3.B/3.D)
  ============================================

  Source : Sheldon Axler, *Linear Algebra Done Right*, 4e éd., Springer 2024,
  licence CC BY-NC 4.0, version du 30 octobre 2026. Copie archivée au gisement
  partagé : `G:\Mon Drive\MyIA\IA\Bibliographie IA\Pedagogie-Proves\2024 -
  Axler - Linear Algebra Done Right (Springer, 4e edition, CC BY-NC 4.0,
  version 30 oct 2026).pdf`. Chaque énoncé cite son numéro dans le livre ;
  la numérotation suit la 4e édition (elle diffère de la 3e).

  Périmètre de cette marche : 3.A (applications linéaires, opérations sur
  ℒ(V, W), composition), 3.B (noyau, image, injectivité, surjectivité,
  théorème fondamental 3.21) et 3.D (inversibilité, isomorphismes). Restent
  pour des tranches suivantes : 3.C (matrices, matrice d'une application,
  rang), 3.E (produits et quotients), 3.F (dualité), ainsi que le théorème
  d'extension 3.5 (une application linéaire est déterminée par les images
  d'une base — organe Mathlib `Basis.constr`), qui suppose le vocabulaire
  matriciel de 3.C.

  Ce fichier distille l'ORDRE d'Axler, pas son texte : les définitions
  d'Axler sont portées par les organes natifs de Mathlib, que la marche
  déclare et cite, jamais redéfinies. Aucune ligne n'est recopiée des
  compagnons sans licence (rkirov/linear-algebra-done-right-lean,
  blanketism/Axler-Solutions), consultés seulement pour comparer les
  progressions. L'ouvrage de Riehl, *Category Theory in Context*, est
  archivé au même gisement (`2016 - Riehl - Category Theory in Context
  (Dover ; 2e edition en ligne, adaptee de la 1re).pdf`) : les marches qui
  partiront de sa progression le citeront à leur tour.

  Correspondance Axler → Mathlib :
  - application linéaire (Axler 3.1) → `V →ₗ[K] W` (`LinearMap K V W`) ;
  - ℒ(V, W) (Axler 3.2) → le type `V →ₗ[K] W` lui-même ;
  - produit d'applications ST (Axler 3.7) → `LinearMap.comp S T` ;
  - noyau null T (Axler 3.11) → `LinearMap.ker T`, un `Submodule K V` ;
  - image range T (Axler 3.16) → `LinearMap.range T`, un `Submodule K W` ;
  - inversible (Axler 3.59), isomorphisme (Axler 3.69) →
    `LinearEquiv K V W` ; « V et W sont isomorphes » → `Nonempty (V ≃ₗ[K] W)`.

  La dimension finie (3.21 et ses corollaires) suppose `[Module.Finite K V]`
  — la traduction de « finite-dimensional » retenue par la marche 1.

  Cette tranche est FR seule ; les jumeaux `_en` (convention #4980) sont une
  tranche suivante, comme pour la marche 1.
-/
import Mathlib

namespace Linear

-- Mêmes ouvertures que la marche 1 : les organes cités vivent sous `LinearMap`
-- (ker, range, comp), `Submodule` (⊥, ⊤, finrank) et `Module` (finrank).
open LinearMap Submodule Module

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

/-! ### 3.A — L'espace vectoriel des applications linéaires (Axler 3.1-3.10)

Axler définit une application linéaire par ses deux additivités (3.1) et
nomme ℒ(V, W) l'ensemble de ces applications (3.2). Les deux opérations de
3.5 sont point par point, et 3.6 constate que ℒ(V, W) est un espace
vectoriel. Dans Mathlib, tout cela est porté par la structure `LinearMap` et
l'instance `Module K (V →ₗ[K] W)` : la marche énonce les opérations sous
leur numéro d'Axler et délègue. -/

section Operations

variable {U : Type*} [AddCommGroup U] [Module K U]

/-- **Axler 3.5** (« addition and scalar multiplication on ℒ(V, W) ») :
l'addition de deux applications linéaires est point par point,
`(S + T)(v) = S(v) + T(v)`. Organe Mathlib : `LinearMap.add_apply`. -/
theorem somme_point_par_point (S T : V →ₗ[K] W) (v : V) :
    (S + T) v = S v + T v :=
  LinearMap.add_apply S T v

/-- **Axler 3.5** (volet scalaire) : la multiplication par un scalaire est
point par point, `(a • S)(v) = a • S(v)`. L'énoncé 3.6 (« ℒ(V, W) is a
vector space ») est l'instance `Module K (V →ₗ[K] W)`, qui rend ces deux
opérations légitimes. Organe Mathlib : `LinearMap.smul_apply`. -/
theorem scalaire_point_par_point (a : K) (S : V →ₗ[K] W) (v : V) :
    (a • S) v = a • S v :=
  LinearMap.smul_apply a S v

/-- **Axler 3.8** (« algebraic properties of products of linear maps »,
associativité) : `(ST)U = S(TU)`. Organe Mathlib :
`LinearMap.comp_assoc`. -/
theorem associativite_composition (S : W →ₗ[K] U) (T : V →ₗ[K] W)
    (R : U →ₗ[K] V) : (S.comp T).comp R = S.comp (T.comp R) :=
  LinearMap.comp_assoc R T S

/-- **Axler 3.8** (identité) : `TI = T`, l'identité de ℒ(V) composée à
gauche. Organe Mathlib : `LinearMap.id_comp`. -/
theorem composition_identite_gauche (T : V →ₗ[K] W) :
    T.comp LinearMap.id = T :=
  LinearMap.id_comp T

/-- **Axler 3.8** (identité) : `IT = T`, l'identité composée à droite.
Organe Mathlib : `LinearMap.comp_id`. -/
theorem composition_identite_droite (S : V →ₗ[K] W) :
    LinearMap.id.comp S = S :=
  LinearMap.comp_id S

/-- **Axler 3.8** (linéarité du produit) : `a(ST) = (aS)T` — un scalaire
sort de la composition. Organe Mathlib : `LinearMap.smul_comp`. -/
theorem scalaire_composition (a : K) (S : V →ₗ[K] W) (T : U →ₗ[K] V) :
    a • (S.comp T) = (a • S).comp T :=
  LinearMap.smul_comp a S T

end Operations

/-- **Axler 3.10** (« linear maps take 0 to 0 ») : `T(0) = 0`. Organe
Mathlib : `LinearMap.map_zero`. -/
theorem zero_vers_zero (T : V →ₗ[K] W) : T 0 = 0 :=
  LinearMap.map_zero T

/-! ### 3.B — Noyaux et images (Axler 3.11-3.24)

Le noyau (3.11) et l'image (3.16) sont des sous-espaces (3.13, 3.18) : dans
Mathlib ce sont directement des `Submodule`, si bien que « le noyau est un
sous-espace » est porté par le TYPE et non par un théorème. L'appartenance
s'énonce par `mem_ker` et `mem_range` ; l'injectivité se lit sur le noyau
(3.15), la surjectivité sur l'image (3.19). Le théorème fondamental (3.21)
— `dim V = dim null T + dim range T` — fonde les deux corollaires de
dimension (3.22 : vers un espace plus petit, jamais injective ; 3.24 : vers
un espace plus grand, jamais surjective). -/

/-- **Axler 3.11/3.13** (« null space », puis « the null space is a
subspace ») : `v ∈ null T ↔ T(v) = 0`. Le caractère sous-espace est porté
par le type `Submodule K V` de `LinearMap.ker`. Organe Mathlib :
`LinearMap.mem_ker`. -/
theorem membre_noyau (T : V →ₗ[K] W) (v : V) :
    v ∈ LinearMap.ker T ↔ T v = 0 :=
  LinearMap.mem_ker

/-- **Axler 3.15** (« injectivity ⟺ null space equals {0} ») : `T` est
injective si et seulement si son noyau est réduit au vecteur nul (⊥ dans le
treillis des sous-modules). Organe Mathlib : `LinearMap.ker_eq_bot`. -/
theorem injectif_ssi_noyau_nul (T : V →ₗ[K] W) :
    LinearMap.ker T = ⊥ ↔ Function.Injective T :=
  LinearMap.ker_eq_bot

/-- **Axler 3.16/3.18** (« range », puis « the range is a subspace ») :
`w ∈ range T ↔ ∃ v, T(v) = w`. Le caractère sous-espace est porté par le
type `Submodule K W` de `LinearMap.range`. Organe Mathlib :
`LinearMap.mem_range`. -/
theorem membre_image (T : V →ₗ[K] W) (w : W) :
    w ∈ LinearMap.range T ↔ ∃ v, T v = w :=
  LinearMap.mem_range

/-- **Axler 3.19** (« surjective ») : `T` est surjective si et seulement si
son image est l'espace tout entier. Organe Mathlib :
`LinearMap.range_eq_top`. -/
theorem surjectif_ssi_image_pleine (T : V →ₗ[K] W) :
    LinearMap.range T = ⊤ ↔ Function.Surjective T :=
  LinearMap.range_eq_top

/-- **Axler 3.21** (« fundamental theorem of linear maps ») :
`dim V = dim null T + dim range T` pour `V` de dimension finie. Organe
Mathlib : `LinearMap.finrank_range_add_finrank_ker` (qui somme dans
l'autre ordre ; `omega` réaligne sur l'énoncé d'Axler). -/
theorem theoreme_fondamental [Module.Finite K V] (T : V →ₗ[K] W) :
    finrank K V = finrank K ↥(LinearMap.ker T) + finrank K ↥(LinearMap.range T) := by
  have h := LinearMap.finrank_range_add_finrank_ker T
  omega

/-- **Axler 3.22** (« linear map to a lower-dimensional space is not
injective ») : si `dim W < dim V`, aucune application linéaire `V → W`
n'est injective. Preuve d'Axler : l'injectivité annule le noyau (3.15),
donc `dim range T = dim V > dim W`, impossible pour un sous-espace de `W`
(3.21 contredit la majoration). -/
theorem vers_dimension_inferieure_non_injectif [Module.Finite K V]
    [Module.Finite K W] (T : V →ₗ[K] W) (h : finrank K W < finrank K V) :
    ¬Function.Injective T := by
  intro hinj
  have hb : LinearMap.ker T = ⊥ := (LinearMap.ker_eq_bot).mpr hinj
  have h0 : finrank K ↥(LinearMap.ker T) = 0 := by
    rw [hb]
    exact finrank_bot K V
  have hf := theoreme_fondamental T
  have hle : finrank K ↥(LinearMap.range T) ≤ finrank K W :=
    Submodule.finrank_le (LinearMap.range T)
  omega

/-- **Axler 3.24** (« linear map to a higher-dimensional space is not
surjective ») : si `dim V < dim W`, aucune application linéaire `V → W`
n'est surjective. Preuve d'Axler : la surjectivité remplit l'image,
`dim range T = dim W > dim V`, alors que 3.21 borne `dim range T` par
`dim V`. -/
theorem vers_dimension_superieure_non_surjectif [Module.Finite K V]
    [Module.Finite K W] (T : V →ₗ[K] W) (h : finrank K V < finrank K W) :
    ¬Function.Surjective T := by
  intro hsurj
  have htop : LinearMap.range T = ⊤ := (LinearMap.range_eq_top).mpr hsurj
  have hfr : finrank K ↥(LinearMap.range T) = finrank K W := by
    rw [htop]
    exact finrank_top K W
  have hf := theoreme_fondamental T
  omega

/-! ### 3.D — Inversibilité et isomorphismes (Axler 3.59-3.70)

Un inverse de `T` est une application linéaire `S` telle que `ST = I` et
`TS = I` (3.59) ; il est unique et noté `T⁻¹` (3.60) — dans Mathlib,
l'organe est `LinearEquiv`, où l'inverse est `LinearEquiv.symm` et les deux
identités sont `symm_apply_apply` et `apply_symm_apply`. La marche énonce
les deux critères de 3.D : inversible ⟺ bijective (3.63), et sur un espace
de dimension finie, injective ⟺ surjective (3.65) ; puis le critère
d'inversibilité par les compositions (3.68) et la classification par la
dimension (3.70). -/

/-- **Axler 3.63** (« invertibility ⟺ injectivity and surjectivity ») :
`T` admet un inverse bilatère linéaire si et seulement si `T` est
bijective. L'inverse est construit par `LinearEquiv.ofBijective`, dont
`symm` porte les deux identités. -/
theorem bilaterne_ssi_bijectif (T : V →ₗ[K] W) :
    (∃ S : W →ₗ[K] V, S.comp T = LinearMap.id ∧ T.comp S = LinearMap.id) ↔
      Function.Bijective T := by
  constructor
  · rintro ⟨S, hST, hTS⟩
    refine ⟨fun v w hvw => ?_, fun w => ⟨S w, ?_⟩⟩
    · have h : S (T v) = S (T w) := by rw [hvw]
      rwa [show S (T v) = v from congrFun (congrArg DFunLike.coe hST) v,
        show S (T w) = w from congrFun (congrArg DFunLike.coe hST) w] at h
    · show T (S w) = w
      exact congrFun (congrArg DFunLike.coe hTS) w
  · rintro ⟨hinj, hsurj⟩
    let e : V ≃ₗ[K] W := LinearEquiv.ofBijective T ⟨hinj, hsurj⟩
    refine ⟨e.symm.toLinearMap, ?_, ?_⟩
    · ext v
      exact e.symm_apply_apply v
    · ext w
      exact e.apply_symm_apply w

/-- **Axler 3.65** (« injectivity is equivalent to surjectivity » sur des
espaces de même dimension finie) : si `dim V = dim W < ∞`, une application
linéaire `V → W` est injective si et seulement si elle est surjective.
Preuve par 3.21 : l'injectivité donne `dim range T = dim V = dim W`, donc
l'image est pleine ; la surjectivité donne `dim ker T = 0`, donc le noyau
est nul. -/
theorem injectif_ssi_surjectif_meme_dimension [Module.Finite K V]
    [Module.Finite K W] (T : V →ₗ[K] W) (hdim : finrank K V = finrank K W) :
    Function.Injective T ↔ Function.Surjective T := by
  constructor
  · intro hinj
    have hb : LinearMap.ker T = ⊥ := (LinearMap.ker_eq_bot).mpr hinj
    have h0 : finrank K ↥(LinearMap.ker T) = 0 := by
      rw [hb]
      exact finrank_bot K V
    have hf := theoreme_fondamental T
    have hfin : finrank K ↥(LinearMap.range T) = finrank K W := by omega
    have htop : LinearMap.range T = ⊤ :=
      Submodule.eq_top_of_finrank_eq hfin
    exact (LinearMap.range_eq_top).mp htop
  · intro hsurj
    by_contra hinj
    have hne : LinearMap.ker T ≠ ⊥ := fun hb => hinj ((LinearMap.ker_eq_bot).mp hb)
    have hpos : 0 < finrank K ↥(LinearMap.ker T) := by
      by_contra hle
      have h0 : finrank K ↥(LinearMap.ker T) = 0 := Nat.le_zero.mp (not_lt.mp hle)
      exact hne ((Submodule.finrank_eq_zero).mp h0)
    have htop : LinearMap.range T = ⊤ := (LinearMap.range_eq_top).mpr hsurj
    have hfr : finrank K ↥(LinearMap.range T) = finrank K W := by
      rw [htop]
      exact finrank_top K W
    have hf := theoreme_fondamental T
    omega

/-- **Axler 3.68** (« ST = I ⟺ TS = I » sur un espace de dimension finie) :
pour deux endomorphismes de `V`, avoir `S` inverse à gauche de `T` équivaut
à l'avoir à droite. Preuve par 3.65 : `ST = I` rend `T` injective, donc
surjective, et l'antécédent fourni par la surjectivité recompose `TS = I`. -/
theorem bilaterne_a_droite_ssi_a_gauche [Module.Finite K V] (S T : V →ₗ[K] V) :
    S.comp T = LinearMap.id ↔ T.comp S = LinearMap.id := by
  constructor
  · intro h
    have hinj : Function.Injective T := by
      intro v w hvw
      have h' : S (T v) = S (T w) := by rw [hvw]
      rwa [show S (T v) = v from congrFun (congrArg DFunLike.coe h) v,
        show S (T w) = w from congrFun (congrArg DFunLike.coe h) w] at h'
    have hsurj : Function.Surjective T :=
      (injectif_ssi_surjectif_meme_dimension T rfl).mp hinj
    ext v
    obtain ⟨u, hu⟩ := hsurj v
    have hSu : S v = u := by
      rw [show v = T u from hu.symm]
      exact congrFun (congrArg DFunLike.coe h) u
    show T (S v) = v
    rw [hSu]
    exact hu
  · intro h
    have hinj : Function.Injective S := by
      intro v w hvw
      have h' : T (S v) = T (S w) := by rw [hvw]
      rwa [show T (S v) = v from congrFun (congrArg DFunLike.coe h) v,
        show T (S w) = w from congrFun (congrArg DFunLike.coe h) w] at h'
    have hsurj : Function.Surjective S :=
      (injectif_ssi_surjectif_meme_dimension S rfl).mp hinj
    ext v
    obtain ⟨u, hu⟩ := hsurj v
    have hTu : T v = u := by
      rw [show v = S u from hu.symm]
      exact congrFun (congrArg DFunLike.coe h) u
    show S (T v) = v
    rw [hTu]
    exact hu

/-- **Axler 3.69/3.70** (« isomorphism », puis « dimension shows whether
vector spaces are isomorphic ») : sur des espaces de dimension finie, `V`
et `W` sont isomorphes si et seulement s'ils ont même dimension. Le sens
direct est `LinearEquiv.finrank_eq`, la réciproque
`Module.equivOfFinrankEq`. -/
theorem isomorphe_ssi_meme_dimension [Module.Finite K V] [Module.Finite K W] :
    Nonempty (V ≃ₗ[K] W) ↔ finrank K V = finrank K W := by
  constructor
  · rintro ⟨e⟩
    exact LinearEquiv.finrank_eq e
  · intro h
    exact ⟨LinearEquiv.ofFinrankEq V W h⟩