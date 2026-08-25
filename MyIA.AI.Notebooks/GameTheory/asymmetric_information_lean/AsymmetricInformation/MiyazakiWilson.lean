/-
  Miyazaki-Wilson-Spence 1977-1978 — équilibre anticipatory, formalisation bornée
  ===============================================================================

  Formalisation **bornée** du modèle d'équilibre anticipatory de Wilson 1977
  *JET* 16:167-207, Miyazaki 1977 *Bell J.* 8(2):394-418 et Spence 1978.

  Bornes strictes (audit canonique c.475 catégorie #4) :
  - **PAS** de `wilson_anticipatory_always_exists : ∃!` dans cette livraison ;
  - **PAS** d'unicité MWS générale sans hypothèses substantielles ;
  - **PAS** de « Wilson 1989 fictif » — date correcte : 1977-1978 ;
  - Définitions finies + **exemples décidables** où zéro, un ou plusieurs
    menus satisfont le prédicat.

  Trois théorèmes modestes valent mieux qu'un `∃!` dont les hypothèses
  encodent déjà la conclusion.
-/

import AsymmetricInformation.Screening

namespace AsymmetricInformation.MiyazakiWilson

/-- Prédicat **anticipatory** : aucun contrat du menu ne peut être unilatéralement
    retiré pour proposer un contrat hors-menu profitable. C'est la version
    **statique** (pas de réaction post-sélection) de Wilson 1977. -/
def anticipatoryMenu
    (menu : AsymmetricInformation.Screening.Menu)
    (r : AsymmetricInformation.Screening.RiskProfile) : Prop :=
  ∀ c ∈ menu, ∀ c' : AsymmetricInformation.Screening.Contract, c' ∉ menu →
    AsymmetricInformation.Screening.globalExpectedProfit c' r ≤
      AsymmetricInformation.Screening.globalExpectedProfit c r

/-- **Cross-subsidy tenable** : il existe un contrat `c` dans le menu qui
    subventionne un type par l'autre (profit positif sur un type, négatif
    sur l'autre). C'est la **définition locale** du cross-subsidy, qui
    n'appartient PAS à RS. -/
def crossSubsidyTenable
    (menu : AsymmetricInformation.Screening.Menu)
    (r : AsymmetricInformation.Screening.RiskProfile) : Prop :=
  ∃ c ∈ menu, ∃ q : AsymmetricInformation.Screening.RiskType,
    AsymmetricInformation.Screening.expectedProfit c r q > 0 ∧
    ∃ c' ∈ menu, ∃ q' : AsymmetricInformation.Screening.RiskType, q' ≠ q ∧
      AsymmetricInformation.Screening.expectedProfit c' r q' < 0

/-- Menu trivialement anticipatory : le menu vide l'est (vacuité du `∀ c ∈ ∅`). -/
theorem anticipatory_empty :
    ∀ (r : AsymmetricInformation.Screening.RiskProfile),
      anticipatoryMenu [] r := by
  intro r c hc
  -- `hc : c ∈ []` est `False` par construction de `List.Mem`. On extrait
  -- la contradiction par `cases` puis on applique `False.elim`.
  cases hc

/-- Un singleton `(α, β)` n'est PAS anticipatory s'il existe un contrat
    hors-menu **strictement plus profitable** que le contrat du singleton.
    C'est l'**exemple d'instabilité cream-skim** dans le cas limite : la
    direction cream-skim ⟹ ¬ anticipatory, sur singleton, se réduit à
    une comparaison directe d'inégalités strictes — preuve par
    instanciation de `hAnt` sur le contrat singleton + la déviation
    hors-menu de `hPos`. Pas de `Decidable` requis, pas de Mathlib :
    arithmétique `Int` close. -/
theorem singleton_not_anticipatory_with_profitable_deviation
    (r : AsymmetricInformation.Screening.RiskProfile)
    (c : AsymmetricInformation.Screening.Contract)
    (hPos : ∃ c' : AsymmetricInformation.Screening.Contract,
              c' ≠ c ∧
              AsymmetricInformation.Screening.globalExpectedProfit c' r >
                AsymmetricInformation.Screening.globalExpectedProfit c r) :
    ¬ anticipatoryMenu [c] r := by
  intro hAnt
  obtain ⟨c', hne, hprof⟩ := hPos
  -- `hAnt` sur le singleton [c] : pour tout membre c'' ∈ [c] (= c) et tout
  -- d ∉ [c], `globalExpectedProfit d ≤ globalExpectedProfit c''`.
  -- Instanciation sur c'' = c et d = c' (qui satisfait c' ∉ [c] car c' ≠ c) :
  have hdOut : c' ∉ [c] := by
    intro hIn
    rcases hIn with heq | hrest
    · exact hne heq
    · cases hrest
  have hle := hAnt c (by left; rfl) c' hdOut
  omega

/-- **Exemple décidé — menu à 2 contrats sans cross-subsidy** : profil
    `(p_H, p_L) = (25, 75)`, menu `[(α=100, β=20), (α=40, β=10)]`. Calcul :
    - Contrat 1 sur H : `20*100 - 25*100 = -500` (négatif)
    - Contrat 2 sur L : `10*100 - 75*40 = 1000 - 3000 = -2000` (négatif)
    - Contrat 1 sur L : `20*100 - 75*100 = 2000 - 7500 = -5500` (négatif)
    - Contrat 2 sur H : `10*100 - 25*40 = 1000 - 1000 = 0` (neutre)
    Donc cross-subsidy n'est PAS tenable sur ce menu : aucun contrat n'a
    profit **strictement positif** (tous ≤ 0), donc la conjonction
    `(expectedProfit c r q > 0) ∧ (expectedProfit c' r q' < 0)` ne peut
    jamais être satisfaite sur ce menu. L'exemple démontre que
    `crossSubsidyTenable` peut être `False` (le prédicat n'est pas
    trivialement satisfait). **Preuve par décisions sur les 4 paires
    `(c, q)` puis `cases` exhaustif** : aucune conjonction positive de
    deux profits stricts ne se réalise arithmétiquement. -/
example : ¬ crossSubsidyTenable
    ([⟨100, 20⟩, ⟨40, 10⟩] : AsymmetricInformation.Screening.Menu)
    ⟨25, 75, by omega⟩ := by
  intro ⟨c, hc, q, hp, c', hc', q', hneq, hn⟩
  -- Éliminer le `c ∈ [⟨100,20⟩, ⟨40,10⟩]` par `cases` via `List.Mem`.
  -- Chaque membre `c` peut être `⟨100, 20⟩` (head) ou `⟨40, 10⟩` (tail) ;
  -- idem `c'`. On traite les 4 paires possibles.
  rcases hc with hch | hct
  · -- c = ⟨100, 20⟩ (head) : `expectedProfit ⟨100, 20⟩ r q > 0`
    subst hch
    rcases q with q | q
    · -- q = .high : expectedProfit = 20*100 - 25*100 = -500 (négatif)
      simp [AsymmetricInformation.Screening.expectedProfit,
            AsymmetricInformation.Screening.RiskProfile.mk.injEq] at hp
    · -- q = .low : expectedProfit = 20*100 - 75*100 = -5500 (négatif)
      simp [AsymmetricInformation.Screening.expectedProfit,
            AsymmetricInformation.Screening.RiskProfile.mk.injEq] at hp
  · -- c = ⟨40, 10⟩ (tail)
    rcases hct with hct' | hrest
    · -- c = ⟨40, 10⟩
      subst hct'
      rcases q with q | q
      · -- q = .high : expectedProfit = 10*100 - 25*40 = 0 (not > 0!)
        simp [AsymmetricInformation.Screening.expectedProfit,
              AsymmetricInformation.Screening.RiskProfile.mk.injEq] at hp
      · -- q = .low : expectedProfit = 10*100 - 75*40 = -2000
        simp [AsymmetricInformation.Screening.expectedProfit,
              AsymmetricInformation.Screening.RiskProfile.mk.injEq] at hp
    · -- c ∈ [] : impossible par construction de `List.Mem`.
      cases hrest

/-- **PAS de claim d'unicité ni d'existence générale** dans cette livraison.
    Trois théorèmes modestes :
    (1) anticipatory_empty (trivial) ;
    (2) singleton_not_anticipatory_with_profitable_deviation (directional,
        preuve close — voir commentaire interne) ;
    (3) example cross-subsidy decided.
    Wilson/MWS « anticipatory always exists » et MWS « unique » sont des
    théorèmes qui demandent des hypothèses supplémentaires substantielles
    (single-crossing, anticipatory menu-level, break-even), et sont **hors
    scope** de cette première livraison (cf body v4 D). -/
theorem no_general_existence_claim :
    -- stub volontairement restrictif : on ne claim PAS l'existence générale.
    True := trivial

end AsymmetricInformation.MiyazakiWilson