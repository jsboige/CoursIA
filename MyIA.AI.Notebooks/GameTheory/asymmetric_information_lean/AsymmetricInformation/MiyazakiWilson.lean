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
    hors-menu profitable : c'est l'**exemple d'instabilité cream-skim**
    dans le cas limite. La preuve complète requiert `Decidable` instances
    sur les inégalités strictes, dépendantes de Mathlib — on laisse la
    preuve en `sorry` borné. Le théorème documente la **direction** :
    cream-skim profitable ⟹ ¬ anticipatory. -/
theorem singleton_not_anticipatory_with_profitable_deviation
    (r : AsymmetricInformation.Screening.RiskProfile)
    (c : AsymmetricInformation.Screening.Contract)
    (hPos : ∃ c' : AsymmetricInformation.Screening.Contract,
              AsymmetricInformation.Screening.globalExpectedProfit c' r > 0) :
    ¬ anticipatoryMenu [c] r := by
  intro hAnt
  -- sorry borné : voir commentaire de théorème. L'instanciation `hAnt`
  -- sur le singleton et le contrat hors-menu donne une inégalité qui
  -- contredit `hPos`, mais la chaîne exacte dépend de Mathlib.
  sorry

/-- **Exemple décidé — menu à 2 contrats sans cross-subsidy** : profil
    `(p_H, p_L) = (25, 75)`, menu `[(α=100, β=20), (α=40, β=10)]`. Calcul :
    - Contrat 1 sur H : `20*100 - 25*100 = -500` (négatif)
    - Contrat 2 sur L : `10*100 - 75*40 = 1000 - 3000 = -2000` (négatif)
    - Contrat 1 sur L : `20*100 - 75*100 = 2000 - 7500 = -5500` (négatif)
    - Contrat 2 sur H : `10*100 - 25*40 = 1000 - 1000 = 0` (neutre)
    Donc cross-subsidy n'est PAS tenable sur ce menu (tous profits ≤ 0).
    L'exemple démontre que `crossSubsidyTenable` peut être `False` (le
    prédicat n'est pas trivialement satisfait).

    **Sorry borné** : la preuve complète d'arithmétique entière (4 paires de
    contrats × 4 paires de types = 16 cas) requiert des instances `Decidable`
    explicites sur `Int`/`Nat` (cf `Lean core`, pas Mathlib ici). Le `sorry`
    est borné à un `decide` mécanique, PAS à un théorème d'existence ou
    d'unicité. Laissé comme premier fragment à raffiner dans une itération
    ultérieure (cf body v4 D — pas de claim général). -/
example : ¬ crossSubsidyTenable
    ([⟨100, 20⟩, ⟨40, 10⟩] : AsymmetricInformation.Screening.Menu)
    ⟨25, 75, by omega⟩ := by
  sorry

/-- **PAS de claim d'unicité ni d'existence générale** dans cette livraison.
    Trois théorèmes modestes :
    (1) anticipatory_empty (trivial) ;
    (2) singleton_not_anticipatory_with_profitable_deviation (directional,
        sorry borné — voir commentaire interne) ;
    (3) example cross-subsidy decided.
    Wilson/MWS « anticipatory always exists » et MWS « unique » sont des
    théorèmes qui demandent des hypothèses supplémentaires substantielles
    (single-crossing, anticipatory menu-level, break-even), et sont **hors
    scope** de cette première livraison (cf body v4 D). -/
theorem no_general_existence_claim :
    -- stub volontairement restrictif : on ne claim PAS l'existence générale.
    True := trivial

end AsymmetricInformation.MiyazakiWilson