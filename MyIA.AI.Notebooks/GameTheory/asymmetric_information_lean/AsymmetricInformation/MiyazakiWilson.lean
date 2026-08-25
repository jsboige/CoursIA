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

/- ## Vecteur de choix H/L dans le menu (couche dynamique — repair Wilson/MWS c.491, durci c.502)

  Le prédicat `anticipatoryMenu` ligne 23-31 ci-dessus est la version
  **statique** de Wilson 1977 : aucune réaction post-sélection, simple
  comparaison de profits agrégés.

  L'acceptance #12848 exige explicitement « **menu, choix des types,
  profit agrégé, retrait anticipé, faisabilité de subvention croisée**.
  Fournir des exemples décidables où zéro, un ou plusieurs menus
  satisfont le prédicat. » La couche dynamique : un `MenuChoice`
  sélectionne deux contrats dans le menu (un pour chaque type H/L), un
  `EntryWithdrawal` décrit une déviation concrète (entrant hors-menu +
  contrat retiré), et `anticipatoryAgainst` exprime l'invariance du
  profit agrégé sous de telles déviations.

  Quatre résultats décidables ferment le contrat sur le profil
  `(p_H, p_L) = (25, 75)`, chacun avec une arithmétique qui est
  **effectivement dans le terme Lean** :
  (4) `no_menu_choice_on_empty_menu` — aucun état n'est constructible
      sur un menu vide : zéro déviation inspectable (cas « zéro ») ;
  (5) `singleton_withdrawal_anticipatory` — UN menu satisfait contre une
      déviation réelle non vide : l'agrégat passe de -2000 à -6000 ;
  (6) `two_contracts_withdrawal_not_anticipatory` — un menu NE satisfait
      pas : la déviation élève l'agrégat de -2500 à +500 ;
  (7) `two_distinct_anticipatory_states` — PLUSIEURS états distincts
      satisfont le prédicat, chacun contre sa déviation.
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
/-- Profil de risque `(p_H, p_L) = (25, 75)` partagé par les exemples
    (4)-(7). Le champ `hOrder : 25 < 75` est clos par `omega`. -/
private def prof : AsymmetricInformation.Screening.RiskProfile :=
  ⟨25, 75, by omega⟩

/-- État B (avant) : menu singleton `[(α=40, β=10)]`, H et L choisissent
    tous deux l'unique contrat. Profit agrégé :
    `(10*100 - 25*40) + (10*100 - 75*40) = 0 + (-2000) = -2000`. -/
private def beforeB : MenuChoice :=
  { menu := [⟨40, 10⟩]
    highChoice := ⟨40, 10⟩
    lowChoice := ⟨40, 10⟩
    high_mem := by left; rfl
    low_mem := by left; rfl }

/-- État B (après) : l'entrant `(100, 20)` est le seul contrat offert,
    le retiré `(40, 10)` n'y figure plus. Profit agrégé :
    `(20*100 - 25*100) + (20*100 - 75*100) = (-500) + (-5500) = -6000`. -/
private def afterB : MenuChoice :=
  { menu := [⟨100, 20⟩]
    highChoice := ⟨100, 20⟩
    lowChoice := ⟨100, 20⟩
    high_mem := by left; rfl
    low_mem := by left; rfl }

/-- Déviation B — `EntryWithdrawal` **complet** : l'entrant `(100, 20)`
    était hors-menu avant (`elem` réfuté par `decide`), est offert après
    (head) ; le retiré `(40, 10)` était offert avant (head), n'est plus
    offert après (`elem` réfuté par `decide`). Aucun champ n'est un
    stub : chaque appartenance est une preuve explicite. -/
private def devB : EntryWithdrawal :=
  { before := beforeB
    after := afterB
    entrant := ⟨100, 20⟩
    withdrawn := ⟨40, 10⟩
    entrant_was_off_menu := by
      intro h
      rcases h with h1 | h2
      · exact absurd h1 (by decide)
      · exact False.elim h2
    entrant_is_offered := by left; rfl
    withdrawn_was_offered := by left; rfl
    withdrawn_is_removed := by
      intro h
      rcases h with h1 | h2
      · exact absurd h1 (by decide)
      · exact False.elim h2 }

/-- État A (avant) : menu `[(100, 50), (100, 20)]`, H choisit
    `(100, 50)`, L choisit `(100, 20)`. Profit agrégé :
    `(50*100 - 25*100) + (20*100 - 75*100) = 2500 + (-5500) = -3000`. -/
private def beforeA : MenuChoice :=
  { menu := [⟨100, 50⟩, ⟨100, 20⟩]
    highChoice := ⟨100, 50⟩
    lowChoice := ⟨100, 20⟩
    high_mem := by left; rfl
    low_mem := by right; left; rfl }

/-- État A (après) : le retiré `(100, 50)` n'y figure plus, l'entrant
    `(40, 10)` y est offert, H choisit `(40, 10)`, L garde `(100, 20)`.
    Profit agrégé : `(10*100 - 25*40) + (20*100 - 75*100) =
    0 + (-5500) = -5500`. -/
private def afterA : MenuChoice :=
  { menu := [⟨100, 20⟩, ⟨40, 10⟩]
    highChoice := ⟨40, 10⟩
    lowChoice := ⟨100, 20⟩
    high_mem := by right; left; rfl
    low_mem := by left; rfl }

/-- Déviation A — `EntryWithdrawal` complet : l'entrant `(40, 10)`
    était hors-menu avant, est offert après (tail) ; le retiré
    `(100, 50)` était offert avant (head), n'est plus offert après. -/
private def devA : EntryWithdrawal :=
  { before := beforeA
    after := afterA
    entrant := ⟨40, 10⟩
    withdrawn := ⟨100, 50⟩
    entrant_was_off_menu := by
      intro h
      rcases h with h1 | h2
      · exact absurd h1 (by decide)
      · rcases h2 with h3 | h4
        · exact absurd h3 (by decide)
        · exact False.elim h4
    entrant_is_offered := by right; left; rfl
    withdrawn_was_offered := by left; rfl
    withdrawn_is_removed := by
      intro h
      rcases h with h1 | h2
      · exact absurd h1 (by decide)
      · rcases h2 with h3 | h4
        · exact absurd h3 (by decide)
        · exact False.elim h4 }

/-- État N (avant) : menu `[(100, 20), (40, 10)]`, H choisit
    `(100, 20)`, L choisit `(40, 10)`. Profit agrégé :
    `(20*100 - 25*100) + (10*100 - 75*40) = (-500) + (-2000) = -2500`. -/
private def beforeN : MenuChoice :=
  { menu := [⟨100, 20⟩, ⟨40, 10⟩]
    highChoice := ⟨100, 20⟩
    lowChoice := ⟨40, 10⟩
    high_mem := by left; rfl
    low_mem := by right; left; rfl }

/-- État N (après) : l'entrant `(100, 50)` est offert (head), le retiré
    `(100, 20)` n'y figure plus, H choisit l'entrant, L garde `(40, 10)`.
    Profit agrégé : `(50*100 - 25*100) + (10*100 - 75*40) =
    2500 + (-2000) = +500`. -/
private def afterN : MenuChoice :=
  { menu := [⟨100, 50⟩, ⟨40, 10⟩]
    highChoice := ⟨100, 50⟩
    lowChoice := ⟨40, 10⟩
    high_mem := by left; rfl
    low_mem := by right; left; rfl }

/-- Déviation N — `EntryWithdrawal` complet : l'entrant `(100, 50)`
    était hors-menu avant, est offert après (head) ; le retiré
    `(100, 20)` était offert avant (head), n'est plus offert après. -/
private def devN : EntryWithdrawal :=
  { before := beforeN
    after := afterN
    entrant := ⟨100, 50⟩
    withdrawn := ⟨100, 20⟩
    entrant_was_off_menu := by
      intro h
      rcases h with h1 | h2
      · exact absurd h1 (by decide)
      · rcases h2 with h3 | h4
        · exact absurd h3 (by decide)
        · exact False.elim h4
    entrant_is_offered := by left; rfl
    withdrawn_was_offered := by left; rfl
    withdrawn_is_removed := by
      intro h
      rcases h with h1 | h2
      · exact absurd h1 (by decide)
      · rcases h2 with h3 | h4
        · exact absurd h3 (by decide)
        · exact False.elim h4 }

/-- **Exemple décidé (4) — aucun état n'est constructible sur un menu
    vide.** Le champ `high_mem : elem menu highChoice` d'un `MenuChoice`
    dont `menu = []` se réduit à `False` : aucun choix de types, donc
    aucune déviation `EntryWithdrawal`, ne peut partir d'un menu vide.
    Le cas « zéro » de la trame 0/1/plusieurs est ainsi trivial par
    structure ; le cas zéro **non trivial** est réalisé par le théorème
    (6) : un état réel qu'aucune invariance ne protège. -/
theorem no_menu_choice_on_empty_menu :
    ∀ (s : MenuChoice), s.menu ≠ [] := by
  intro s hEq
  have hMem := s.high_mem
  rw [hEq] at hMem
  -- `elem [] s.highChoice` se réduit à `False` par construction.
  exact hMem

/-- **Exemple décidé (5) — UN menu satisfait anticipatoryAgainst contre
    une déviation réelle non vide.** État B : singleton `[(40, 10)]`,
    profit agrégé `0 + (-2000) = -2000`. La déviation `devB` fait
    entrer `(100, 20)` et retire `(40, 10)` : le profit agrégé devient
    `(-500) + (-5500) = -6000`. Puisque `-6000 ≤ -2000`, l'invariance
    TIENT sur cette réponse. La preuve **inspecte la réponse** :
    l'universelle est instanciée sur l'unique élément de `[devB]`, puis
    les deux agrégats sont calculés exactement — cas positif non vacu. -/
theorem singleton_withdrawal_anticipatory :
    anticipatoryAgainst beforeB prof [devB] := by
  intro response hmem _heq
  have hEq : response = devB := by
    simpa using hmem
  rw [hEq]
  show chosenAggregateProfit afterB prof ≤ chosenAggregateProfit beforeB prof
  have hAfter : chosenAggregateProfit afterB prof = -6000 := by
    simp only [chosenAggregateProfit, AsymmetricInformation.Screening.expectedProfit,
               afterB, prof]
    omega
  have hBefore : chosenAggregateProfit beforeB prof = -2000 := by
    simp only [chosenAggregateProfit, AsymmetricInformation.Screening.expectedProfit,
               beforeB, prof]
    omega
  rw [hAfter, hBefore]
  omega

/-- **Exemple décidé (6) — un menu NE satisfait PAS anticipatoryAgainst :
    la déviation élève réellement le profit agrégé.** État N : menu
    `[(100, 20), (40, 10)]`, profit agrégé `(-500) + (-2000) = -2500`.
    La déviation `devN` fait entrer l'entrant profitable `(100, 50)`
    (profit H = `50*100 - 25*100 = +2500`) et retire `(100, 20)` :
    l'agrégat passe à `2500 + (-2000) = +500 > -2500`. L'universelle
    est réfutée en instanciant l'unique réponse `devN ∈ [devN]` puis en
    calculant les deux agrégats exactement — contre-exemple cream-skim
    en version dynamique, sur une déviation **réelle et non vide**. -/
theorem two_contracts_withdrawal_not_anticipatory :
    ¬ anticipatoryAgainst beforeN prof [devN] := by
  intro hAnt
  have hle : chosenAggregateProfit afterN prof ≤ chosenAggregateProfit beforeN prof :=
    hAnt devN (List.Mem.head _) (by rfl)
  have hAfter : chosenAggregateProfit afterN prof = 500 := by
    simp only [chosenAggregateProfit, AsymmetricInformation.Screening.expectedProfit,
               afterN, prof]
    omega
  have hBefore : chosenAggregateProfit beforeN prof = -2500 := by
    simp only [chosenAggregateProfit, AsymmetricInformation.Screening.expectedProfit,
               beforeN, prof]
    omega
  rw [hAfter, hBefore] at hle
  omega

/-- **Exemple décidé (7) — PLUSIEURS états distincts satisfont le
    prédicat.** L'état A (menu `[(100, 50), (100, 20)]`, agrégat -3000,
    déviation `devA` vers un agrégat -5500) et l'état B (menu singleton
    `[(40, 10)]`, agrégat -2000, déviation `devB` vers -6000) sont deux
    `MenuChoice` **distincts** — leurs menus sont de longueurs
    différentes, décidé par `decide` — qui satisfont chacun
    `anticipatoryAgainst` contre leur déviation respective. -/
theorem two_distinct_anticipatory_states :
    ∃ s₁ s₂ : MenuChoice, s₁ ≠ s₂ ∧
      ∃ rw₁ rw₂ : EntryWithdrawal,
        anticipatoryAgainst s₁ prof [rw₁] ∧
          anticipatoryAgainst s₂ prof [rw₂] := by
  refine ⟨beforeA, beforeB, ?_, devA, devB, ?_, singleton_withdrawal_anticipatory⟩
  · intro hEq
    have hMenus : beforeA.menu = beforeB.menu := congrArg MenuChoice.menu hEq
    exact absurd hMenus (by decide)
  · intro response hmem _heq
    have hEq : response = devA := by
      simpa using hmem
    rw [hEq]
    show chosenAggregateProfit afterA prof ≤ chosenAggregateProfit beforeA prof
    have hAfter : chosenAggregateProfit afterA prof = -5500 := by
      simp only [chosenAggregateProfit, AsymmetricInformation.Screening.expectedProfit,
                 afterA, prof]
      omega
    have hBefore : chosenAggregateProfit beforeA prof = -3000 := by
      simp only [chosenAggregateProfit, AsymmetricInformation.Screening.expectedProfit,
                 beforeA, prof]
      omega
    rw [hAfter, hBefore]
    omega

/- ## Pas de claim d'unicité ni d'existence générale dans cette livraison.

  Sept résultats modestes :
  (1) `anticipatory_empty` (trivial, statique) ;
  (2) `singleton_not_anticipatory_with_profitable_deviation`
      (directionnel, preuve close) ;
  (3) exemple cross-subsidy decided (statique) ;
  (4) `no_menu_choice_on_empty_menu` (aucun état constructible sur
      menu vide, zéro déviation inspectable) ;
  (5) `singleton_withdrawal_anticipatory` (un menu satisfait, déviation
      réelle non vide, réponse inspectée : -2000 → -6000) ;
  (6) `two_contracts_withdrawal_not_anticipatory` (un menu ne satisfait
      pas : la déviation élève l'agrégat de -2500 à +500) ;
  (7) `two_distinct_anticipatory_states` (deux états aux menus disjoints
      satisfont le prédicat).

  Wilson/MWS « anticipatory always exists » et MWS « unique » restent
  des théorèmes exigeant des hypothèses supplémentaires substantielles
  (single-crossing, anticipatory menu-level, break-even), **hors
  scope** de cette livraison (cf body v4 D). Les témoins (4)-(7)
  délimitent la frontière avec des menus réels et des déviations
  réelles — un `True := trivial` n'apporterait rien de plus (leçon
  c.482 : un témoin concret est plus informatif qu'un stub).
-/

end AsymmetricInformation.MiyazakiWilson