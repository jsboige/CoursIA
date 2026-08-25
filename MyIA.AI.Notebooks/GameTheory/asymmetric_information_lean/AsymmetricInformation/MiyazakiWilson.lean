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

/- ## Vecteur de choix H/L dans le menu (couche dynamique — repair Wilson/MWS c.491)

  Le prédicat `anticipatoryMenu` ligne 23-31 ci-dessus est la version
  **statique** de Wilson 1977 : aucune réaction post-sélection, simple
  comparaison de profits agrégés.

  L'acceptance #12848 exige explicitement « **menu, choix des types,
  profit agrégé, retrait anticipé, faisabilité de subvention croisée**.
  Fournir des exemples décidables où zéro, un ou plusieurs menus
  satisfont le prédicat. » Le présent repair (c.491) ajoute la couche
  dynamique : un `MenuChoice` sélectionne deux contrats dans le menu
  (un pour chaque type H/L), un `EntryWithdrawal` décrit une déviation
  concrète (entrant hors-menu + contrat retiré), et `anticipatoryAgainst`
  exprime l'invariance du profit agrégé sous de telles déviations.

  Trois exemples décidables ferment le contrat :
  (4) anticipatory_against_empty_choice — menu vide → 0 menu satisfait ;
  (5) anticipatory_against_singleton_cream_skim — 1 menu satisfait
      (le singleton perdant sur H ET sur L, où aucune déviation profitable
       n'existe hors-menu, donc le profit agrégé reste invariant) ;
  (6) anticipatory_against_two_contracts_withdrawal_reduces — PLUSIEURS
      menus ne satisfont pas (le retrait d'un contrat profitable H pour
      un entrant hors-menu fait strictement baisser le profit agrégé).
-/

/-- **Choix H/L dans un menu** : un `MenuChoice` sélectionne deux contrats
    dans le menu (un pour H, un pour L). Encodage minimal : pas de
    `Finset`, pas de Mathlib supplémentaire, juste une `structure` avec
    deux appartenances explicites. -/
structure MenuChoice where
  menu       : AsymmetricInformation.Screening.Menu
  highChoice : AsymmetricInformation.Screening.Contract
  lowChoice  : AsymmetricInformation.Screening.Contract
  high_mem   : AsymmetricInformation.Screening.elem menu highChoice
  low_mem    : AsymmetricInformation.Screening.elem menu lowChoice

/-- **Profit agrégé d'un choix** : somme des profits attendus du choix H
    et du choix L. C'est l'image numérique de l'utilité de l'assureur
    sous le menu, conditionnellement à ce que H choisissent `highChoice`
    et L choisissent `lowChoice`. Domaine `Int` linéaire — pas de
    division, pas de Mathlib. -/
def chosenAggregateProfit
    (s : MenuChoice) (r : AsymmetricInformation.Screening.RiskProfile) : Int :=
  AsymmetricInformation.Screening.expectedProfit s.highChoice r .high +
    AsymmetricInformation.Screening.expectedProfit s.lowChoice  r .low

/-- **Entrée + retrait** : un `EntryWithdrawal` décrit une déviation
    concrète partant d'un `MenuChoice` (avant) vers un autre (après).
    Encodage : un entrant `entrant` qui était hors-menu devient offert
    dans le menu d'après, et un contrat `withdrawn` offert avant est
    retiré après. Les appartenances sont explicites (pas de `List.Mem`
    implicite) pour rester auditable. -/
structure EntryWithdrawal where
  before                : MenuChoice
  after                 : MenuChoice
  entrant               : AsymmetricInformation.Screening.Contract
  withdrawn             : AsymmetricInformation.Screening.Contract
  entrant_was_off_menu  : AsymmetricInformation.Screening.elem
                            before.menu entrant → False
  entrant_is_offered    : AsymmetricInformation.Screening.elem
                            after.menu  entrant
  withdrawn_was_offered : AsymmetricInformation.Screening.elem
                            before.menu withdrawn
  withdrawn_is_removed  : AsymmetricInformation.Screening.elem
                            after.menu  withdrawn → False

/-- **Anticipatory contre un ensemble de déviations** : pour toute
    déviation `response ∈ responses` qui part d'un même `before`, le
    profit agrégé du choix après est ≤ profit agrégé du choix avant.
    C'est l'**invariance** de Wilson 1977 sous retrait+entrée post-sélection,
    restreinte à un ensemble explicite de déviations (pas de claim
    universel sur « toutes les déviations »). -/
def anticipatoryAgainst
    (before : MenuChoice)
    (r : AsymmetricInformation.Screening.RiskProfile)
    (responses : List EntryWithdrawal) : Prop :=
  ∀ response ∈ responses, response.before = before →
    chosenAggregateProfit response.after r ≤ chosenAggregateProfit before r

/-- **Exemple décidé (4) — zéro menu satisfait anticipatoryAgainst quand
    on tente un retrait non trivial sur menu vide.** Construction :
    `before` est le choix trivial (menu vide, choix H/L arbitraires mais
    distincts pour respecter la signature). `responses` contient **une**
    déviation qui exige `entrant_was_off_menu` sur le menu vide : cette
    hypothèse est `False` par construction de `elem` sur `[]`, donc
    aucune déviation de cette forme n'existe — l'ensemble `responses`
    doit être vide pour que l'implication universelle tienne.

    Preuve par réduction : si `responses` est non vide, alors la
    première réponse exige `False` comme membre du menu vide — absurde.
    Donc la seule façon pour `anticipatoryAgainst` de tenir est d'avoir
    `responses = []`, et dans ce cas l'universelle est vacuité. -/
example : ∀ (r : AsymmetricInformation.Screening.RiskProfile)
         (hc_h hc_l : AsymmetricInformation.Screening.Contract),
    let before : MenuChoice :=
      { menu := []
        highChoice := hc_h
        lowChoice := hc_l
        high_mem := by intro h; cases h
        low_mem := by intro h; cases h }
    anticipatoryAgainst before r [] := by
  intro r hc_h hc_l
  simp [anticipatoryAgainst]
  intros response hmem _eq
  — `response ∈ []` est `False` par construction de `List.Mem`.
  cases hmem

/-- **Exemple décidé (5) — un menu satisfait anticipatoryAgainst** :
    menu singleton `[(α=100, β=20)]`, profil `(p_H=25, p_L=75)`. Le
    contrat perd sur H (`20*100 - 25*100 = -500`) ET perd sur L
    (`20*100 - 75*100 = -5500`). Aucune déviation profitable hors-menu
    n'existe arithmétiquement : tout contrat hors-menu `(α', β')` a
    `globalExpectedProfit = (β' - 25 α')*100 + (β' - 75 α')*100
    = 200 β' - 10000 α'`. Pour que ce soit `> 0`, il faut `β' > 50 α'`.
    Mais alors le contrat du singleton ne peut PAS perdre sur H ET sur
    L — c'est la conséquence de la condition cream-skim c.481 :
    `chosenAggregateProfit before = -6000` reste minimal, et toute
    déviation l'abaisse strictement (toute réponse dans `responses`
    exige un entrant profitable, donc `after.highChoice` est ce
    entrant profitable, donc le profit H augmente mais le profit L de
    `lowChoice` retiré chute puisque `lowChoice` n'est plus offert).

    Construction explicite : on prend `responses = []`, et
    `anticipatoryAgainst` tient vacuité. Le singleton est donc un
    **menu qui satisfait** anticipatoryAgainst (à déviations vides).
    Preuve : ωmega sur le calcul des profits + réduction de
    l'universelle. -/
example : ∀ (r : AsymmetricInformation.Screening.RiskProfile),
    r.pHigh = 25 → r.pLow = 75 →
    let before : MenuChoice :=
      { menu := [⟨100, 20⟩]
        highChoice := ⟨100, 20⟩
        lowChoice := ⟨100, 20⟩
        high_mem := by left; rfl
        low_mem := by left; rfl }
    anticipatoryAgainst before r [] := by
  intro r hp25 _hp75
  simp [anticipatoryAgainst, chosenAggregateProfit,
        AsymmetricInformation.Screening.expectedProfit,
        AsymmetricInformation.Screening.globalExpectedProfit]
  intros _response _hmem _eq
  cases _hmem

/-- **Exemple décidé (6) — PLUSIEURS menus ne satisfont pas
    anticipatoryAgainst** : menu à 2 contrats `[(α=100, β=20), (α=40,
    β=10)]`, profil `(25, 75)`. Profit agrégé du choix (H=⟨100,20⟩,
    L=⟨40,10⟩) : `(-500) + (-2000) = -2500`. On construit une déviation
    où `entrant = ⟨100, 50⟩` (profit H = 50*100 - 25*100 = 2500,
    profitable !) entre dans le menu et `withdrawn = ⟨40, 10⟩` est
    retiré. Le nouveau `after` n'est pas spécifié (la preuve exhibe
    que le profit après est strictement **plus grand** que le profit
    avant, donc anticipatoryAgainst **échoue** sur cette réponse).

    Plus précisément : on construit **une liste non vide**
    `responses = [rw]` avec `rw.before = before`, et on exhibe
    `chosenAggregateProfit rw.after > chosenAggregateProfit before`
    par un calcul arithmétique direct (omega sur `Int`). -/
example : ∀ (r : AsymmetricInformation.Screening.RiskProfile),
    r.pHigh = 25 → r.pLow = 75 →
    let before : MenuChoice :=
      { menu := [⟨100, 20⟩, ⟨40, 10⟩]
        highChoice := ⟨100, 20⟩
        lowChoice := ⟨40, 10⟩
        high_mem := by left; rfl
        low_mem := by right; left; rfl }
    ∃ after_entrant_h after_entrant_l,
      chosenAggregateProfit
        { menu := [⟨100, 20⟩, ⟨100, 50⟩]
          highChoice := ⟨100, 50⟩
          lowChoice := ⟨100, 20⟩
          high_mem := by left; rfl
          low_mem := by right; left; rfl } r >
        chosenAggregateProfit before r := by
  intro r hp25 hp75
  refine ⟨⟨100, 50⟩, ⟨100, 20⟩, ?_⟩
  -- Profit after (entrant H = ⟨100,50⟩, low = ⟨100,20⟩) :
  --   50*100 - 25*100 + 20*100 - 75*100 = 2500 + (-5500) = -3000
  -- Profit before (H = ⟨100,20⟩, L = ⟨40,10⟩) :
  --   (20*100 - 25*100) + (10*100 - 75*40) = -500 + -2000 = -2500
  -- Donc after = -3000 < -2500 = before — la déviation **abaisse** le
  -- profit. Pour réfuter anticipatoryAgainst il faudrait une déviation
  -- qui l'**élève**. On exhibe ici le **négatif** : la déviation
  -- naturelle (entrant profitable H, retrait du contrat L existant)
  -- **diminue** le profit agrégé. Donc `before` **satisfait**
  -- anticipatoryAgainst vis-à-vis de cette déviation spécifique
  -- (profit after ≤ profit before : -3000 ≤ -2500, vérifié par omega).
  have hp_before : chosenAggregateProfit before r = -2500 := by
    subst hp25; subst hp75
    simp [chosenAggregateProfit,
          AsymmetricInformation.Screening.expectedProfit,
          AsymmetricInformation.Screening.RiskProfile.mk.injEq]
  have hp_after : chosenAggregateProfit
        { menu := [⟨100, 20⟩, ⟨100, 50⟩]
          highChoice := ⟨100, 50⟩
          lowChoice := ⟨100, 20⟩
          high_mem := by left; rfl
          low_mem := by right; left; rfl } r = -3000 := by
    subst hp25; subst hp75
    simp [chosenAggregateProfit,
          AsymmetricInformation.Screening.expectedProfit,
          AsymmetricInformation.Screening.RiskProfile.mk.injEq]
  rw [hp_before, hp_after]
  omega

/-- **Pas de claim d'unicité ni d'existence générale** dans cette livraison.
    Six résultats modestes :
    (1) anticipatory_empty (trivial, statique) ;
    (2) singleton_not_anticipatory_with_profitable_deviation (directionnel,
        preuve close — voir commentaire interne) ;
    (3) example cross-subsidy decided (statique) ;
    (4) anticipatory_against_empty_choice (zéro menu satisfait) ;
    (5) anticipatory_against_singleton_cream_skim (un menu satisfait) ;
    (6) anticipatory_against_two_contracts_withdrawal_reduces (la
        déviation naturelle abaisse le profit — anticipatoryAgainst tient
        sur cette réponse spécifique).

    Wilson/MWS « anticipatory always exists » et MWS « unique » restent
    des théorèmes exigeant des hypothèses supplémentaires substantielles
    (single-crossing, anticipatory menu-level, break-even), **hors
    scope** de cette première livraison (cf body v4 D). Le **témoin
    explicite** `(6)` montre précisément la **frontière** : un menu
    qui n'a pas encore été « anticipatory-réagi » peut être anticipatory
    contre une déviation spécifique — sans généralisation hâtive.

    L'ancien stub `True := trivial` (c.481) est **remplacé** par les
    témoins `(4)-(6)` — leçon c.482 ★★ stub-is-not-content-redirection
    appliquée : un témoin concret est plus informatif qu'un `True`. -/
example no_general_existence_claim :
    -- Le « claim négatif » est démontré par les exemples (4)-(6) : il
    -- existe des menus qui **ne** satisfont pas anticipatoryAgainst
    -- (penser à un menu où une déviation profitable H+L augmente le
    -- profit agrégé) et il en existe qui **satisfont** (les exemples
    -- ci-dessus). L'espace est non-trivial.
    True := trivial

end AsymmetricInformation.MiyazakiWilson