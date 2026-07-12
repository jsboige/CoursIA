/-
  Paradoxe libéral de Sen
  ========================

  Port de asouther4/lean-social-choice vers Lean 4

  Le théorème d'impossibilité de Sen montre qu'aucune procédure de décision sociale
  ne peut simultanément satisfaire :
  1. Le critère de Pareto faible
  2. Le libéralisme minimal (certains individus sont décisifs sur certaines paires)
  3. Un domaine non restreint

  C'est un résultat fondamental montrant la tension entre efficacité et liberté.
-/

import SocialChoice.Framework
import Mathlib.Tactic

variable {ι : Type*} {σ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq σ]

/-! ## Libéralisme minimal -/

/-- L'individu i est décisif sur la paire (x, y) :
    la société suit la préférence stricte de i dans les deux directions.
    Conforme à Sen 1970 et Holliday/Norman/Pacuit 2021 (bidirectionnel). -/
def is_decisive_over (f : SWF ι σ) (i : ι) (x y : σ) : Prop :=
  (∀ prof : Profile ι σ, P (prof i).rel x y → P (f prof).rel x y) ∧
  (∀ prof : Profile ι σ, P (prof i).rel y x → P (f prof).rel y x)

/-- Libéralisme minimal : au moins deux individus ont chacun au moins une
    paire sur laquelle ils sont décisifs -/
def minimal_liberal (f : SWF ι σ) (X : Finset σ) : Prop :=
  ∃ i j : ι, i ≠ j ∧
    (∃ x y : σ, x ∈ X ∧ y ∈ X ∧ x ≠ y ∧ is_decisive_over f i x y) ∧
    (∃ x y : σ, x ∈ X ∧ y ∈ X ∧ x ≠ y ∧ is_decisive_over f j x y)

-- Domaine non restreint : la SWF accepte tout profil
-- (Ceci est implicite dans notre définition de SWF)

/-! ## Construction du paradoxe de Sen -/

-- Un profil de préférence qui démontre le paradoxe :
-- Prude préfère (pas-lire, pas-lire) > (lu-par-autre, pas-lire) > (lire, lu-par-autre)
-- Lewd préfère (lu-par-autre, lire) > (lire, pas-lire) > (pas-lire, pas-lire)

/-! ## Théorème d'impossibilité de Sen -/

/--
Paradoxe libéral de Sen :
il n'existe aucune fonction de bien-être social qui satisfait à la fois
Pareto faible et Libéralisme minimal pour tous les profils de préférence.
ESQUISSE DE PREUVE :
de minimal_liberal, on tire deux individus i, j avec des paires décisives :
  i est décisif sur (x, y), j est décisif sur (z, w).
Ces paires peuvent se chevaucher. La construction standard utilise :
  i décisif sur (a, b), j décisif sur (b, c) (ou paires disjointes).
Cas 1 (chevauchement) : i décisif sur (a,b), j décisif sur (b,c).
  Construire un profil où i préfère a > b (exerce son droit → société : a > b)
  et j préfère b > c (exerce son droit → société : b > c)
  et tout le monde préfère c > a (Pareto → société : c > a).
  Cycle : a > b > c > a. Aucun élément meilleur n'existe.
Cas 2 (disjoint) : i décisif sur (a,b), j décisif sur (c,d).
  Construction de cycle similaire en utilisant les quatre alternatives.
  Requiert |X| >= 4 dans ce cas (garanti par hX : 3 ≤ |X| seulement
  donne 3, donc la preuve utilise le cas chevauchant). -/
theorem sen_impossibility (f : SWF ι σ) (X : Finset σ)
    (hne : (2 : ℕ) ≤ Fintype.card ι)
    (hX : 3 ≤ X.card)
    (hwp : weak_pareto f X)
    (hml : minimal_liberal f X) :
    ∃ prof : Profile ι σ, ¬∃ best : σ, is_best_element best X (f prof).rel := by
  obtain ⟨i, j, hij, ⟨a, b, ha, hb, hab, hi_dec⟩, ⟨c, d, hc, hd, hcd, hj_dec⟩⟩ := hml
  by_cases hbc : b = c
  · -- Chevauchement : i décisif sur (a,b), j décisif sur (b,d) puisque b=c
    subst hbc
    -- Sous-cas : a = d signifie les deux décisifs sur des paires partageant b, avec a=d
    by_cases had : a = d
    · -- a=d : i sur (a,b), j sur (b,a). Construire le profil : i préfère a>b, j préfère b>a
      -- La société obtient P a b et P b a → contradiction
      subst had
      let base : PrefOrder σ := ⟨fun _ _ => True, fun _ => trivial,
        fun _ _ => Or.inl trivial, fun _ _ _ _ _ => trivial⟩
      let prof : Profile ι σ := fun k =>
        if k = i then maketop_pref base a
        else if k = j then maketop_pref base b
        else maketop_pref base a
      use prof
      intro ⟨best, hbest⟩
      have hPa_b : P (f prof).rel a b := hi_dec.1 prof (by
        unfold prof; simp only [hij]
        show maketop_rel (fun _ _ ↦ True) a a b ∧ ¬maketop_rel (fun _ _ ↦ True) a b a
        simp [maketop_rel, hab, hab.symm])
      have hPb_a : P (f prof).rel b a := hj_dec.1 prof (by
        unfold prof; simp only [hij.symm]
        show maketop_rel (fun _ _ ↦ True) b b a ∧ ¬maketop_rel (fun _ _ ↦ True) b a b
        simp [maketop_rel, hab])
      exact hPa_b.2 hPb_a.1
    · -- a≠d, b≠d : chevauchement avec i sur (a,b), j sur (b,d)
      -- Cycle : P a b (i décisif), P b d (j décisif), P d a (Pareto)
      have hbd : b ≠ d := hcd
      let base : PrefOrder σ := ⟨fun _ _ => True, fun _ => trivial,
        fun _ _ => Or.inl trivial, fun _ _ _ _ _ => trivial⟩
      let prof : Profile ι σ := fun k =>
        if k = i then maketop_pref (makebot_pref base b) d
        else if k = j then maketop_pref (makebot_pref base a) b
        else maketop_pref (makebot_pref base a) d
      use prof
      intro ⟨best, hbest⟩
      have hPa_b : P (f prof).rel a b := hi_dec.1 prof (by
        unfold prof; simp only [hij]
        simp [P, maketop_pref, maketop_rel, makebot_pref, makebot_rel, hab, had, hbd])
      have hPb_d : P (f prof).rel b d := hj_dec.1 prof (by
        unfold prof
        simp [P, maketop_pref, maketop_rel, makebot_pref, makebot_rel, hab, hbd.symm, hij.symm])
      have hAll_d_a : ∀ k, P (prof k).rel d a := by
        intro k; unfold prof; split_ifs with hki hkj
        · simp [P, maketop_pref, maketop_rel, makebot_pref, makebot_rel, hab, had, hbd]
        · show P (maketop_rel (makebot_rel (fun _ _ ↦ True) a) b) d a
          simp [P, maketop_rel, makebot_rel, hab, hbd.symm]
          exact fun h => had h.symm
        · simp [P, maketop_pref, maketop_rel, makebot_pref, makebot_rel, hab, had, hbd]
      have hPd_a : P (f prof).rel d a := hwp prof d a hd ha hAll_d_a
      have hPad := P_trans (f prof).trans hPa_b hPb_d
      exact hPad.2 hPd_a.1
  · -- b≠c : i sur (a,b), j sur (c,d) avec b≠c
    have hcb : c ≠ b := fun h => hbc h.symm
    by_cases had : a = d
    · -- a=d : i sur (a,b), j sur (c,a) — chevauchement compatible en chaîne (a partagé dans
      -- des positions différentes : 1er dans la paire de i, 2nd dans celle de j). Cycle : a>b (i), b>c (Pareto), c>a (j)
      subst had
      have hca : c ≠ a := hcd
      let base : PrefOrder σ := ⟨fun _ _ => True, fun _ => trivial,
        fun _ _ => Or.inl trivial, fun _ _ _ _ _ => trivial⟩
      let prof : Profile ι σ := fun k =>
        if k = i then maketop_pref (makebot_pref base c) a
        else maketop_pref (makebot_pref base a) b
      use prof
      intro ⟨best, hbest⟩
      have hPa_b : P (f prof).rel a b := hi_dec.1 prof (by
        unfold prof; simp only [hij]
        simp [P, maketop_pref, maketop_rel, makebot_pref, makebot_rel, hab, hab.symm, hca, hca.symm])
      have hPc_a : P (f prof).rel c a := hj_dec.1 prof (by
        unfold prof; simp only [hij.symm]
        simp [P, maketop_pref, maketop_rel, makebot_pref, makebot_rel, hca, hca.symm, hab, hab.symm, hcb])
      have hcb_local : ¬c = b := fun h => hbc h.symm
      have hAll_b_c : ∀ k, P (prof k).rel b c := by
        intro k; unfold prof; split_ifs with hki
        · simp [P, maketop_pref, maketop_rel, makebot_pref, makebot_rel,
            hab, hab.symm, hca, hca.symm, hbc]
        · simp [P, maketop_pref, maketop_rel, makebot_pref, makebot_rel,
            hab, hab.symm, hca, hca.symm, hcb_local]
      have hPb_c : P (f prof).rel b c := hwp prof b c hb hc hAll_b_c
      exact (P_trans (f prof).trans hPa_b hPb_c).2 hPc_a.1
    · -- a≠d, b≠c : la décisivité bidirectionnelle nous permet de gérer les cas de bifurcation
      by_cases hac : a = c
      · -- a=c (bifurcation) : i sur (a,b), j sur (a,d) avec j bidirectionnel sur (d,a).
        subst hac
        by_cases hbd_check : b = d
        · -- b=d signifie les deux décisifs sur (a,b) : contradiction sur la même paire
          subst hbd_check
          let base : PrefOrder σ := ⟨fun _ _ => True, fun _ => trivial,
            fun _ _ => Or.inl trivial, fun _ _ _ _ _ => trivial⟩
          let prof : Profile ι σ := fun k =>
            if k = i then maketop_pref base a
            else maketop_pref base b
          use prof
          intro ⟨best, hbest⟩
          have hPa_b : P (f prof).rel a b := hi_dec.1 prof (by
            unfold prof; simp only [hij]
            show maketop_rel (fun _ _ ↦ True) a a b ∧ ¬maketop_rel (fun _ _ ↦ True) a b a
            simp [maketop_rel, hab, hab.symm])
          have hPb_a : P (f prof).rel b a := hj_dec.2 prof (by
            unfold prof; simp only [hij.symm]
            show maketop_rel (fun _ _ ↦ True) b b a ∧ ¬maketop_rel (fun _ _ ↦ True) b a b
            simp [maketop_rel, hab, hab.symm])
          exact hPa_b.2 hPb_a.1
        · -- b≠d : cycle a>b (i.1), b>d (Pareto), d>a (j.2)
          have hbd_ne : b ≠ d := fun h => hbd_check h
          let base : PrefOrder σ := ⟨fun _ _ => True, fun _ => trivial,
            fun _ _ => Or.inl trivial, fun _ _ _ _ _ => trivial⟩
          let prof : Profile ι σ := fun k =>
            if k = i then maketop_pref (makebot_pref base d) a
            else maketop_pref (makebot_pref base a) b
          use prof
          intro ⟨best, hbest⟩
          have hPa_b : P (f prof).rel a b := hi_dec.1 prof (by
            unfold prof; simp only [hij]
            show maketop_rel (makebot_rel (fun _ _ ↦ True) d) a a b ∧
              ¬maketop_rel (makebot_rel (fun _ _ ↦ True) d) a b a
            simp [maketop_rel, makebot_rel, hab, hab.symm, hbd_ne, hcd, hcd.symm])
          have hPd_a : P (f prof).rel d a := hj_dec.2 prof (by
            unfold prof; simp only [hij.symm]
            show maketop_rel (makebot_rel (fun _ _ ↦ True) a) b d a ∧
              ¬maketop_rel (makebot_rel (fun _ _ ↦ True) a) b a d
            simp [maketop_rel, makebot_rel, hab, hab.symm, hbd_ne, hcd, hcd.symm])
          have hAll_b_d : ∀ k, P (prof k).rel b d := by
            intro k; unfold prof; split_ifs with hki
            · simp [P, maketop_pref, maketop_rel, makebot_pref, makebot_rel,
                hab, hab.symm, hbd_ne, hcd, hcd.symm]
            · simp [P, maketop_pref, maketop_rel, makebot_pref, makebot_rel,
                hab, hab.symm, hbd_ne, hcd, hcd.symm]; exact fun h => hbd_ne h.symm
          have hPb_d : P (f prof).rel b d := hwp prof b d hb hd hAll_b_d
          exact (P_trans (f prof).trans hPa_b hPb_d).2 hPd_a.1
      · -- a≠c, b≠c, a≠d : examiner la bifurcation b=d
        by_cases hbd2 : b = d
        · -- b=d (bifurcation) : après subst, d→b. i sur (a,b), j sur (c,b) bidirectionnel.
          -- Cycle : c>b (j.1), b>a (i.2), a>c (Pareto)
          subst hbd2
          have hac' : ¬a = c := hac
          let base : PrefOrder σ := ⟨fun _ _ => True, fun _ => trivial,
            fun _ _ => Or.inl trivial, fun _ _ _ _ _ => trivial⟩
          let prof : Profile ι σ := fun k =>
            if k = i then maketop_pref (maketop_pref (makebot_pref base c) a) b
            else if k = j then maketop_pref (maketop_pref (makebot_pref base b) c) a
            else maketop_pref (makebot_pref base c) a
          use prof
          intro ⟨best, hbest⟩
          have hPc_b : P (f prof).rel c b := hj_dec.1 prof (by
            unfold prof; simp only [hij.symm]
            simp [P, maketop_pref, maketop_rel, makebot_pref, makebot_rel,
                hac', hab, hab.symm, hcd, hcd.symm])
          have hPb_a : P (f prof).rel b a := hi_dec.2 prof (by
            unfold prof; simp only [hij]
            simp [P, maketop_pref, maketop_rel, makebot_pref, makebot_rel,
                hac', hab, hab.symm, hcd, hcd.symm])
          have hca : c ≠ a := fun h => hac' h.symm
          have hAll_a_c : ∀ k, P (prof k).rel a c := by
            intro k; unfold prof; split_ifs with hki hkj
            · simp [P, maketop_pref, maketop_rel, makebot_pref, makebot_rel,
                hac', hca, hab, hab.symm, hcd, hcd.symm]
            · simp [P, maketop_pref, maketop_rel, makebot_pref, makebot_rel,
                hac', hca, hab, hab.symm, hcd, hcd.symm]
            · simp [P, maketop_pref, maketop_rel, makebot_pref, makebot_rel,
                hac', hca, hab, hcd]
          have hPa_c : P (f prof).rel a c := hwp prof a c ha hc hAll_a_c
          exact (P_trans (f prof).trans hPc_b hPb_a).2 hPa_c.1
        · -- Tous distincts : cycle à 4 éléments a>b>c>d>a en utilisant 4 alternatives
          -- i sur (a,b) bidirectionnel, j sur (c,d) bidirectionnel
          -- Cycle : a>b (i.1), b>c (Pareto), c>d (j.1), d>a (Pareto)
          let base : PrefOrder σ := ⟨fun _ _ => True, fun _ => trivial,
            fun _ _ => Or.inl trivial, fun _ _ _ _ _ => trivial⟩
          let prof : Profile ι σ := fun k =>
            if k = i then maketop_pref (maketop_pref (maketop_pref (makebot_pref base c) b) a) d
            else if k = j then maketop_pref (maketop_pref (maketop_pref (makebot_pref base a) d) c) b
            else maketop_pref (maketop_pref (makebot_pref base c) b) d
          use prof
          intro ⟨best, hbest⟩
          have hdb : ¬d = b := fun h => hbd2 h.symm
          have hda : ¬d = a := fun h => had h.symm
          have hca : ¬c = a := fun h => hac h.symm
          have hPa_b : P (f prof).rel a b := hi_dec.1 prof (by
            unfold prof; simp only [hij]
            simp [P, maketop_pref, maketop_rel, makebot_pref, makebot_rel,
                hab, hab.symm, hac, hca, had, hda, hbc, hcb, hbd2, hdb, hcd])
          have hPc_d : P (f prof).rel c d := hj_dec.1 prof (by
            unfold prof; simp only [hij.symm]
            simp [P, maketop_pref, maketop_rel, makebot_pref, makebot_rel,
                hab, hab.symm, hac, hca, had, hda, hbc, hcb, hbd2, hdb, hcd, hcd.symm])
          have hAll_b_c : ∀ k, P (prof k).rel b c := by
            intro k; unfold prof; split_ifs with hki hkj
            · simp [P, maketop_pref, maketop_rel, makebot_pref, makebot_rel,
                hab, hab.symm, hac, hca, had, hda, hbc, hcb, hbd2, hdb, hcd, hcd.symm]
            · simp [P, maketop_pref, maketop_rel, makebot_pref, makebot_rel,
                hab, hab.symm, hac, hca, had, hda, hbc, hcb, hbd2, hdb, hcd, hcd.symm]
            · simp [P, maketop_pref, maketop_rel, makebot_pref, makebot_rel,
                hab, hab.symm, hac, hca, had, hda, hbc, hcb, hbd2, hdb, hcd, hcd.symm]
          have hAll_d_a : ∀ k, P (prof k).rel d a := by
            intro k; unfold prof; split_ifs with hki hkj
            · simp [P, maketop_pref, maketop_rel, makebot_pref, makebot_rel,
                hab, hab.symm, hac, hca, had, hda, hbc, hcb, hbd2, hdb, hcd, hcd.symm]
            · simp [P, maketop_pref, maketop_rel, makebot_pref, makebot_rel,
                hab, hab.symm, hac, hca, had, hda, hbc, hcb, hbd2, hdb, hcd, hcd.symm]
            · simp [P, maketop_pref, maketop_rel, makebot_pref, makebot_rel,
                hab, hab.symm, hac, hca, had, hda, hbc, hcb, hbd2, hdb, hcd, hcd.symm]
          have hPb_c : P (f prof).rel b c := hwp prof b c hb hc hAll_b_c
          have hPd_a : P (f prof).rel d a := hwp prof d a hd ha hAll_d_a
          exact (P_trans (f prof).trans hPa_b hPb_c).2
            (P_trans (f prof).trans hPc_d hPd_a).1

/-! ## Exemple : le paradoxe de la lecture du livre -/

/-- Exemple classique avec Prude (p) et Lewd (l) choisissant qui lit un livre
    Alternatives : np (personne ne lit), pr (prude lit), lr (lewd lit) -/

-- Le paradoxe surgit parce que :
-- 1. Prude est décisif sur (pr, lr) : préfère ne pas lire si Lewd lit
-- 2. Lewd est décisif sur (np, lr) : préfère lire plutôt que personne
-- 3. Tous deux sont d'accord (Pareto) : (np, pr) — mieux si Prude lit que personne
--
-- Ceci crée un cycle : np > pr (Pareto), pr > lr (Prude), lr > np (Lewd)
-- Aucune fonction de choix social ne peut briser ce cycle

theorem book_paradox_demonstrates_sen
    (prude lewd : ι) (hne : prude ≠ lewd)
    (np pr lr : σ) (hdist : np ≠ pr ∧ pr ≠ lr ∧ np ≠ lr)
    (f : SWF ι σ) (X : Finset σ)
    (hX : X = {np, pr, lr})
    (hwp : weak_pareto f X)
    (hprude : is_decisive_over f prude pr lr)
    (hlewd : is_decisive_over f lewd lr np) :
    ∃ prof : Profile ι σ,
      P (f prof).rel np pr ∧ P (f prof).rel pr lr ∧ P (f prof).rel lr np := by
  -- Construct a base PrefOrder (using Classical.choice)
  have ⟨hnppr, hprlr, hnp_lr⟩ := hdist
  let base : PrefOrder σ := ⟨fun _ _ => True, fun _ => trivial,
    fun _ _ => Or.inl trivial, fun _ _ _ _ _ => trivial⟩
  -- Construction du profil :
  --   Prude : np en haut, lr en bas → P np pr, P pr lr
  --   Lewd : lr en haut, pr en bas → P lr np, P np pr
  --   Autres : np en haut → P np pr
  let prof : Profile ι σ := fun i =>
    if i = prude then
      maketop_pref (makebot_pref base lr) np
    else if i = lewd then
      maketop_pref (makebot_pref base pr) lr
    else
      maketop_pref base np
  use prof
  -- Étape 1 : tout le monde préfère np > pr (Pareto faible)
  have hpr_np : pr ≠ np := fun h => hnppr h.symm
  have hlr_np : lr ≠ np := fun h => hnp_lr h.symm
  have hpr_lr : pr ≠ lr := hprlr
  have hAllNpPr : ∀ i : ι, P (prof i).rel np pr := by
    intro i
    unfold prof
    split_ifs with hi_p hi_l
    · -- Prude: maketop(makebot(base, lr), np) → np is top → P np pr
      simp [P, maketop_pref, maketop_rel, hpr_np, hlr_np]
    · -- Lewd: maketop(makebot(base, pr), lr) → np, pr ≠ lr
      simp [P, maketop_pref, maketop_rel, makebot_pref, makebot_rel, hnppr, hnp_lr, hpr_lr]
    · -- Others: maketop(base, np) → np is top → P np pr
      simp [P, maketop_pref, maketop_rel, hpr_np]
  have hPnpPr : P (f prof).rel np pr := hwp prof np pr
    (by rw [hX]; simp) (by rw [hX]; simp) hAllNpPr
  -- Étape 2 : Prude préfère pr > lr (décisif)
  have hPrudePrLr : P (prof prude).rel pr lr := by
    unfold prof; simp only [hne]
    simp [P, maketop_pref, maketop_rel, makebot_pref, makebot_rel, hpr_np, hlr_np, hpr_lr]
  have hPprLr : P (f prof).rel pr lr :=
    hprude.1 prof hPrudePrLr
  -- Étape 3 : Lewd préfère lr > np (décisif)
  have hLewdLrNp : P (prof lewd).rel lr np := by
    unfold prof; simp only [hne.symm]
    simp [P, maketop_pref, maketop_rel, makebot_pref, makebot_rel, hnp_lr]
  have hPlrNp : P (f prof).rel lr np :=
    hlewd.1 prof hLewdLrNp
  exact ⟨hPnpPr, hPprLr, hPlrNp⟩

/-! ## Approches de résolution -/

-- Le paradoxe de Sen a conduit à diverses approches de résolution :
-- 1. Restreindre le domaine (tous les profils ne sont pas autorisés)
-- 2. Affaiblir Pareto (Pareto conditionnel)
-- 3. Affaiblir le libéralisme (libéralisme conditionnel)
-- 4. Approches procédurales (les droits comme formes de jeu)

-- Le paradoxe reste philosophiquement important car il montre
-- une tension fondamentale entre efficacité et droits individuels.
