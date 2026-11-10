/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
Adapté à `discrepancy_lean` (issue #17845, Karingula–Lovett distillation
arXiv:2609.20979) : toolchain v4.33.0, Mathlib `db584cd6`, convention i18n #4980.

Le source Dahia original vit dans le dépôt `gdahia/Komlos` (module
`Komlos/Distribution.lean`, toolchain v4.34.0, cadre `Finsupp` sur `E →₀ ℝ`).
L'adaptation reprend le module **nom pour nom**.

**Portée de ce commit** (brique k2.5, `lake build SUCCESS` requis, 0 `sorry`) :

Le module oracle porte toute une infrastructure `Finsupp` — `mass`, `mean`,
`IsDist`, additivités (`mass_add`, `mass_smul`, `mean_smul`), monotonies
(`mass_nonneg`, `mass_mono`), comptes de support sup/inf et les identités
`mass_sup_add_mass_inf` / `mean_sup_add_mean_inf` — dont **seule la
conclusion** a un consommateur mesuré dans notre chaîne :

`mean_mem_convexHull` (l.105) est le **cas de base `n = 0`** de l'assemblage
k1.7 (`SignedSums.lean` l.42 : `simpa using mean_mem_convexHull hP le_rfl`).
Cette brique livre ce pendant seul : le barycentre d'une distribution
positive de masse 1 sur son support `S` appartient à l'enveloppe convexe du
support **transporté** (k2.3 : `S.map ⟨toReal, toReal_injective⟩`).

**Chez l'oracle, la preuve est un one-liner** : les poids que
`Finset.mem_convexHull'` demande sont le `Finsupp` lui-même, nul hors
support **par construction** (`Finsupp` = fonction nulle hors d'un support
fini). C'est précisément le travail que le cadre `Finset` explicite du lake
redemande — et c'est l'organe `push` de k2.3 qui le fournit : `push toReal P`
est la distribution poussée sur la grille réelle, relisant `P` sur l'image
(`push_apply`) et nulle hors image (`push_eq_zero`). La preuve redevient le
one-liner oracle, ses trois composantes se lisant sur les organes k2.3 :
`push_apply` (positivité des poids transportés), `push_mass` (masse, le
`mass_push` de l'oracle), `coordMoment_toReal` (le point produit, le
`mean_push` de l'oracle — le barycentre affirmé dans l'enveloppe est
exactement celui que les moments coordonnés k2.0 calculent).

**Écarts de cadre arbitrés** (même famille qu'en k2.4) :

1. **le `mean` se lit coordonnée par coordonnée** — la base `Fin d → ℤ`
   n'est pas un `ℝ`-module (bloqueur mesuré en k2.2) ; le point est
   `fun i => coordMoment P S i` (k2.0), qui vit dans `Fin d → ℝ` où
   `convexHull ℝ` s'exprime (k2.2/k2.3) ;
2. **`IsDist` devient deux hypothèses** (`hP` : positivité ponctuelle,
   `hmass` : masse 1 sur `S`) — la structure `Finsupp` portait ces faits par
   construction ; le lake les prend en hypothèse, comme `hSQ`/`hPsupp` en
   k2.4 ;
3. **le support de l'énoncé est `S` lui-même** — l'oracle conclut sur un
   `s ⊇ support` arbitraire ; ici le lake conclut sur le support transporté
   exact `S.map ⟨toReal, _⟩`, la même forme que la conclusion de `pullback`
   (k2.4).

**Reportés avec consommateur mesuré** :

- l'infrastructure sup/inf du module oracle (`mass_sup_add_mass_inf`,
  `mean_sup_add_mean_inf`, `support_inf_subset`, `support_sup_subset`) n'a
  pas de consommateur dans notre cadre — la préservation de la masse à la
  scission est déjà `split_mass` (k1.2), que l'assemblage consommera en
  hypothèse chaînée ;
- `sum_smul_inl` (reporté en k2.4 « sans consommateur mesuré ») **acquiert
  un consommateur mesuré** par la lecture k1.7 du pas (`SignedSums.lean`
  l.53 : `rw [mean_split, sum_smul_inl, Prod.mk_add_mk, add_zero] at hmem`)
  — il sera livré avec l'assemblage k2.6, où sa forme exacte se fixe.
-/

import Discrepancy.Basic
import Discrepancy.Komlos.MeanSplit
import Discrepancy.Komlos.Transport

namespace Discrepancy.Komlos

/-- **`mean_mem_convexHull`** (forme lake de l.105 de l'oracle) : le
barycentre — lu coordonnée par coordonnée, `fun i => coordMoment P S i`
(k2.0) — d'une distribution positive de masse 1 sur son support `S`
appartient à l'enveloppe convexe du support **transporté** sur la grille
réelle. C'est le cas de base `n = 0` de l'assemblage du Lemme 1.4 (k1.7,
`SignedSums.lean` l.42).

La preuve est celle de l'oracle — `Finset.mem_convexHull'` avec la
distribution elle-même comme poids — **dès lors** que le poids demandé sur
la grille réelle existe : c'est `push toReal P` (k2.3, l'organe
`Finsupp.embDomain` du lake), nul hors image par construction. Les trois
composantes se lisent sur les organes k2.3 : `push_apply` (positivité),
`push_mass` (masse), `coordMoment_toReal` (le point). -/
theorem mean_mem_convexHull {d : ℕ} {P : (Fin d → ℤ) → ℝ}
    {S : Finset (Fin d → ℤ)}
    (hP : ∀ x, 0 ≤ P x) (hmass : ∑ x ∈ S, P x = 1) :
    (fun i => coordMoment P S i) ∈ convexHull ℝ
      ↑(S.map (⟨⇑toReal, toReal_injective⟩ : (Fin d → ℤ) ↪ (Fin d → ℝ))) := by
  refine Finset.mem_convexHull'.2 ⟨push toReal P, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨x, -, hxy⟩ := Finset.mem_map.1 hy
    have hval : push toReal P y = P x := by
      rw [← hxy]
      exact push_apply toReal toReal_injective P x
    rw [hval]
    exact hP x
  · rw [push_mass toReal toReal_injective P S]
    exact hmass
  · funext i
    rw [← coordMoment_toReal P S i]
    simp only [Finset.sum_apply, coordMomentReal, Pi.smul_apply, smul_eq_mul]

end Discrepancy.Komlos
