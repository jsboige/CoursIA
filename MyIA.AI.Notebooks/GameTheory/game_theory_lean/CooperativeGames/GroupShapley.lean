/-
  CooperativeGames.GroupShapley — valeur de Shapley de groupes (palier 1)
  =======================================================================

  Formalisation de la valeur de Shapley de groupes de Flores, Molina &
  Tejada (2018), « Evaluating groups with the generalized Shapley value »,
  4OR 17(4), DOI 10.1007/s10288-018-0380-8 (Definition 2), construite sur
  le jeu fusionne de Lehrer (1988).

  Source archivee (lecture depuis la copie archivee, convention
  bibliographie) :
  `G:\Mon Drive\MyIA\IA\Bibliographie IA\GameTheory\Cooperative Games and the Shapley Value\2018 - Flores Molina Tejada - Evaluating groups with the generalized Shapley value.pdf`

  Palier 1 (issue #25966, fille de #14468) :
  - le type des joueurs fusionnes `MergedPlayers C` et le proxy `proxy C` ;
  - le jeu fusionne de Lehrer `mergedGame G C` : le proxy porte la valeur
    du groupe entier — v^C(S) = v(S) si c ∉ S, v(S ∪ C) si c ∈ S
    (Definition 1 de l'article, sous la forme developpee) ;
  - la valeur de groupe `shapleyGroupValue G C` (Definition 2) ;
  - le theoreme-coeur de reduction au singleton : la valeur d'un groupe
    singleton coïncide avec la valeur individuelle du joueur.

  Palier 2 (non couvert ici) : linearite en C, additivite, monotonicite,
  exemple numerique du papier.

  Convention i18n (EPIC #4980) : docstrings FR, code/tactiques EN. Sibling
  `_en` optionnel — non requis au palier 1 (le checker i18n ne cree pas
  d'obligation tant que le module n'a pas de jumeau declare).
-/

import CooperativeGames.Shapley

/-! ## Jeu fusionne de Lehrer et valeur de Shapley de groupes

  Le joueur `proxy C` represente le groupe `C` fusionne en un seul agent ;
  les autres joueurs du jeu fusionne sont les elements de `N \ C`. -/

namespace GroupShapley

universe u

variable {N : Type u} [Fintype N] [DecidableEq N]

/-- Les joueurs hors du groupe `C` (partie gauche du jeu fusionne). -/
abbrev Outside (C : Finset N) : Type u := {x : N // x ∉ C}

/-- Les joueurs du jeu fusionne de Lehrer : les joueurs hors de `C`,
    plus le proxy `c` qui remplace le groupe tout entier. -/
abbrev MergedPlayers (C : Finset N) : Type u := Outside C ⊕ Unit

/-- Le proxy du groupe `C` — l'agent `c` du jeu fusionne. -/
def proxy (C : Finset N) : MergedPlayers C := Sum.inr ()

/-- Reexpansion d'une coalition du jeu fusionne : chaque joueur hors du
    groupe contribue son singleton, et le proxy reexpande en le groupe
    entier `C`. C'est l'operation qui fait defiler `v^C` vers `v` :
    `v^C(S) = v(expandFinset C S)`. -/
def expandFinset (C : Finset N) (S : Finset (MergedPlayers C)) : Finset N :=
  S.biUnion (Sum.elim (fun x => ({x.val} : Finset N)) (fun _ => C))

/-- Le jeu fusionne de Lehrer (1988) sur les joueurs `MergedPlayers C` :
    la valeur d'une coalition S est celle de sa reexpansion — v(S) si
    `c ∉ S`, v(S ∪ C) si `c ∈ S` (Definition 1 de Flores-Molina-Tejada
    2018, forme developpee). -/
noncomputable def mergedGame (G : TUGame N) (C : Finset N) :
    TUGame (MergedPlayers C) where
  v := fun S => G.v (expandFinset C S)
  empty_zero := by simp [expandFinset, G.empty_zero]

/-- La valeur d'une coalition du jeu fusionne est la valeur du jeu initial
    sur sa reexpansion. -/
@[simp] lemma mergedGame_v (G : TUGame N) (C : Finset N)
    (S : Finset (MergedPlayers C)) :
    (mergedGame G C).v S = G.v (expandFinset C S) := rfl

/-- Valeur de Shapley d'un groupe (Definition 2 de Flores-Molina-Tejada
    2018) : la valeur de Shapley du proxy `c` dans le jeu fusionne
    `(N_C, v^C)`. Pour `C = ∅` le proxy est un joueur nul (l'expansion
    de `C` est vide) — la definition reste alors valable et vaut 0. -/
noncomputable def shapleyGroupValue (G : TUGame N) (C : Finset N) : ℝ :=
  shapleyValue (mergedGame G C) (proxy C)

/-! ## Lemmes de transport coalitions fusionnees <-> coalitions originales -/

section Transport

variable {C : Finset N}

/-- Reexpansion d'une coalition augmentee du proxy : le proxy reexpande
    en le groupe entier. (Toujours vrai, meme si `proxy C ∈ S` : dans ce
    cas les deux cotes sont egaux par absorption de l'union.) -/
lemma expandFinset_insert_proxy (S : Finset (MergedPlayers C)) :
    expandFinset C (S ∪ {proxy C}) = expandFinset C S ∪ C := by
  unfold expandFinset
  rw [Finset.union_biUnion, Finset.singleton_biUnion]
  rfl

/-- Une coalition sans proxy n'expande que des singletons : son expansion
    est une image, de meme cardinal. La branche `inr` de la fonction
    n'est jamais atteinte (le proxy est exclue de `S`), la valeur
    `Classical.arbitrary` est un placeholder inoffensif. -/
lemma expandFinset_eq_image_of_not_mem_proxy [Nonempty N]
    {S : Finset (MergedPlayers C)} (h : proxy C ∉ S) :
    expandFinset C S =
      S.image (Sum.elim Subtype.val (fun _ => Classical.arbitrary N)) := by
  have hcongr : ∀ x ∈ S,
      Sum.elim (fun x => ({x.val} : Finset N)) (fun _ => C) x
        = {Sum.elim Subtype.val (fun _ => Classical.arbitrary N) x} := by
    intro x hx
    cases x with
    | inl y => simp only [Sum.elim_inl]
    | inr u => cases u; exact absurd hx h
  simp only [expandFinset]
  rw [Finset.biUnion_congr rfl hcongr, Finset.biUnion_singleton]

/-- Le cardinal d'une coalition sans proxy est preserve par expansion. -/
lemma card_expandFinset_of_not_mem_proxy [Nonempty N]
    {S : Finset (MergedPlayers C)} (h : proxy C ∉ S) :
    (expandFinset C S).card = S.card := by
  rw [expandFinset_eq_image_of_not_mem_proxy h]
  refine Finset.card_image_of_injOn ?_
  intro a ha b hb hab
  cases a with
  | inl x =>
      cases b with
      | inl y => exact congrArg Sum.inl (Subtype.ext hab)
      | inr u => cases u; exact absurd hb h
  | inr u => cases u; exact absurd ha h

end Transport

/-! ## Theoreme-coeur du palier 1 : reduction au singleton -/

section Singleton

variable (N)

/-- Pour un groupe singleton, le jeu fusionne compte exactement autant de
    joueurs que le jeu initial (le joueur `i` est remplace par le proxy). -/
lemma card_mergedPlayers_singleton (i : N) :
    Fintype.card (MergedPlayers ({i} : Finset N)) = Fintype.card N := by
  classical
  have h1 : Fintype.card (MergedPlayers ({i} : Finset N))
      = Fintype.card {x : N // x ∉ ({i} : Finset N)} + Fintype.card Unit :=
    Fintype.card_sum
  have h2 : Fintype.card {x : N // x ∉ ({i} : Finset N)}
      = Fintype.card N - Fintype.card {x : N // x ∈ ({i} : Finset N)} :=
    Fintype.card_subtype_compl (fun x => x ∈ ({i} : Finset N))
  have h3 : Fintype.card {x : N // x ∈ ({i} : Finset N)} = 1 :=
    (Fintype.card_coe ({i} : Finset N)).trans (Finset.card_singleton i)
  have h4 : (0 : ℕ) < Fintype.card N := Fintype.card_pos_iff.mpr ⟨i⟩
  rw [h1, h2, h3, Fintype.card_unit]
  omega

variable {N}

/-- Relevement d'un joueur original en joueur fusionne pour le groupe
    singleton `{i}` : le joueur `i` devient le proxy, tout autre joueur
    devient sa partie gauche. Sur une coalition ne contenant pas `i`,
    ce relevement est l'inverse exact de l'expansion. -/
private def liftSingleton (i : N) (j : N) : MergedPlayers ({i} : Finset N) :=
  if h : j ∈ ({i} : Finset N) then Sum.inr () else Sum.inl ⟨j, h⟩

/-- **Theoreme-coeur du palier 1 (reduction au singleton).**
    La valeur de Shapley d'un groupe singleton `{i}` au sens de
    Flores-Molina-Tejada 2018 (Definition 2) coïncide avec la valeur de
    Shapley individuelle du joueur `i` dans le jeu original.

    Preuve : bijection `Finset.sum_bij'` entre les coalitions sans proxy
    (jeu fusionne) et les coalitions sans `i` (jeu original) — l'expansion
    `expandFinset` dans un sens, le relevement `liftSingleton` dans
    l'autre ; cardinal du jeu fusionne egal a celui du jeu original, et
    contribution marginale du proxy egale a celle de `i` via
    `expandFinset_insert_proxy`. -/
theorem shapleyGroupValue_singleton (G : TUGame N) (i : N) :
    shapleyGroupValue G ({i} : Finset N) = shapleyValue G i := by
  classical
  haveI : Nonempty N := ⟨i⟩
  have hcard : Fintype.card (MergedPlayers ({i} : Finset N)) = Fintype.card N :=
    card_mergedPlayers_singleton N i
  unfold shapleyGroupValue shapleyValue TUGame.marginalContribution
  simp only [mergedGame_v]
  rw [hcard]
  refine Finset.sum_bij'
    (fun S _ => expandFinset ({i} : Finset N) S)
    (fun T _ => Finset.image (liftSingleton i) T)
    ?fwd_mem ?inv_mem ?left_inv ?right_inv ?hfg
  case fwd_mem =>
    -- L'expansion d'une coalition sans proxy ne contient pas i
    intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
    intro hmem
    rw [expandFinset] at hmem
    obtain ⟨x, hxS, hxi⟩ := Finset.mem_biUnion.mp hmem
    cases x with
    | inl y =>
        have hyi : i = y.val := by simpa using hxi
        exact y.2 (by simp [hyi])
    | inr u => cases u; exact absurd hxS hS
  case inv_mem =>
    -- Le releve d'une coalition sans i ne contient pas le proxy
    intro T hT
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT ⊢
    intro hmem
    obtain ⟨j, hjT, hj⟩ := Finset.mem_image.mp hmem
    have hji : j ∉ ({i} : Finset N) := fun hm => hT (Finset.mem_singleton.mp hm ▸ hjT)
    unfold liftSingleton at hj
    rw [dif_neg hji] at hj
    simp only [proxy] at hj
    exact Sum.inl_ne_inr hj
  case left_inv =>
    -- liftSingleton ∘ expandFinset = id sur les coalitions sans proxy
    intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
    rw [expandFinset_eq_image_of_not_mem_proxy hS, Finset.image_image]
    have hcomp : ∀ x ∈ S,
        liftSingleton i (Sum.elim Subtype.val (fun _ => Classical.arbitrary N) x)
          = x := by
      intro x hx
      cases x with
      | inl y =>
          have hyi : y.val ∉ ({i} : Finset N) := fun hm => y.2 hm
          simp only [Sum.elim_inl]
          unfold liftSingleton
          -- `rw` ferme le but : l'irrelevance de preuve rend `⟨y.val, hyi⟩ = y`
          -- definitionnellement egal, donc la reecriture conclut par `rfl`.
          rw [dif_neg hyi]
      | inr u =>
          cases u
          exact absurd hx (by simpa [proxy] using hS)
    simp only [Function.comp_def]
    rw [Finset.image_congr hcomp]
    exact Finset.image_id
  case right_inv =>
    -- expandFinset ∘ liftSingleton = id sur les coalitions sans i
    intro T hT
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT
    have hmap : ∀ j ∈ T,
        Sum.elim (fun x => ({x.val} : Finset N)) (fun _ => ({i} : Finset N))
            (liftSingleton i j) = {j} := by
      intro j hj
      have hji : j ∉ ({i} : Finset N) := fun hm => hT (Finset.mem_singleton.mp hm ▸ hj)
      unfold liftSingleton
      rw [dif_neg hji]
      simp [Sum.elim_inl]
    calc expandFinset ({i} : Finset N) (Finset.image (liftSingleton i) T)
        = (Finset.image (liftSingleton i) T).biUnion
            (Sum.elim (fun x => ({x.val} : Finset N)) (fun _ => ({i} : Finset N))) := rfl
      _ = T.biUnion (fun j =>
            Sum.elim (fun x => ({x.val} : Finset N)) (fun _ => ({i} : Finset N))
              (liftSingleton i j)) := by
        ext x
        simp only [Finset.mem_biUnion, Finset.mem_image]
        constructor
        · rintro ⟨a, ⟨j, hjT, happ⟩, hx⟩
          refine ⟨j, hjT, ?_⟩
          rw [← happ, hmap j hjT] at hx
          rw [hmap j hjT]
          exact hx
        · rintro ⟨j, hjT, hxj⟩
          refine ⟨liftSingleton i j, ⟨j, hjT, rfl⟩, ?_⟩
          rw [hmap j hjT] at hxj
          rw [hmap j hjT]
          exact hxj
      _ = T.biUnion (fun j => ({j} : Finset N)) := Finset.biUnion_congr rfl hmap
      _ = T := by simp
  case hfg =>
    -- Egalite des sommes partielles : coefficient (meme cardinal) et
    -- contribution marginale (expansion de S ∪ {proxy} = expansion ∪ {i})
    intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
    have hcardS : (expandFinset ({i} : Finset N) S).card = S.card :=
      card_expandFinset_of_not_mem_proxy hS
    have hexp : expandFinset ({i} : Finset N) (S ∪ {proxy ({i} : Finset N)})
        = expandFinset ({i} : Finset N) S ∪ ({i} : Finset N) :=
      expandFinset_insert_proxy S
    rw [hexp, hcardS]

end Singleton

end GroupShapley
