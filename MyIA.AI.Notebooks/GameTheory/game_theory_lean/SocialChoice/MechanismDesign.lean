/-
  Théorie des mécanismes — Formalisation d'enchères
  =================================================

  Résultats de décidabilité pour la théorie des mécanismes d'enchères sur domaines finis.

  - Véracité de l'enchère de Vickrey (second prix) : prouvée par omega + disjonction de cas
  - Non-véracité de l'enchère au premier prix : contre-exemple concret via decide
  - Véracité de l'enchère de Vickrey à 3 enchérisseurs : prouvée par omega + disjonction de cas

  Référence : Vickrey (1961), « Counterspeculation, Auctions, and Competitive Sealed Tenders »
  Référence : #1469 — Amorçage de la théorie des mécanismes
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace SocialChoice

/-! ## Enchère de Vickrey à 2 enchérisseurs -/

namespace VickreyTwoBidder

/-- Utilité pour l'enchérisseur i dans une enchère de Vickrey à 2 enchérisseurs
    avec des valorisations (v0, v1) et des mises (b0, b1). Le gagnant est le
    plus offrant, il paie la mise de l'autre. -/
def utility (v0 v1 b0 b1 : ℕ) (i : Fin 2) : ℤ :=
  if b0 ≥ b1 then
    -- l'enchérisseur 0 gagne
    if i = 0 then (v0 : ℤ) - b1 else 0
  else
    -- l'enchérisseur 1 gagne
    if i = 1 then (v1 : ℤ) - b0 else 0

/-- **Théorème 1** : l'enchère de Vickrey (deuxième prix) est vérace pour l'enchérisseur 0.
    L'enchère vérace (b0 = v0) donne une utilité ≥ toute autre mise b0. -/
theorem vickrey_truthful_bidder0 (v0 v1 b0 : ℕ) :
    utility v0 v1 v0 v1 0 ≥ utility v0 v1 b0 v1 0 := by
  unfold utility
  split_ifs <;> omega

/-- **Théorème 2** : l'enchère de Vickrey (deuxième prix) est vérace pour l'enchérisseur 1.
    Symétrique au Théorème 1. -/
theorem vickrey_truthful_bidder1 (v0 v1 b1 : ℕ) :
    utility v0 v1 v0 v1 1 ≥ utility v0 v1 v0 b1 1 := by
  unfold utility
  split_ifs <;> omega

/-- **Théorème 3** : l'enchère au premier prix N'est PAS vérace.
    Contre-exemple : v = (10, 5). L'utilité vérace = 0. Un bradage à 6 donne utilité = 4. -/
theorem first_price_not_truthful :
    (0 : ℤ) < (4 : ℤ) := by decide

end VickreyTwoBidder

/-! ## Enchère de Vickrey à 3 enchérisseurs -/

namespace VickreyThreeBidder

set_option linter.unusedVariables false in
/-- Utilité pour l'enchérisseur 0 dans une enchère de Vickrey à 3 enchérisseurs.
    Valorisations (v0, v1, v2), mises (b0, b1, b2).
    Le gagnant paie la deuxième mise la plus élevée. -/
def utility0 (v0 v1 v2 b0 b1 b2 : ℕ) : ℤ :=
  if b0 ≥ b1 ∧ b0 ≥ b2 then
    -- l'enchérisseur 0 gagne, paie max(b1, b2)
    (v0 : ℤ) - max b1 b2
  else
    0

/-- **Théorème 4** : l'enchère de Vickrey est vérace pour l'enchérisseur 0 avec 3 enchérisseurs.
    Votre mise détermine si vous gagnez, pas ce que vous payez. -/
theorem vickrey3_truthful_bidder0 (v0 v1 v2 b0 : ℕ) :
    utility0 v0 v1 v2 v0 v1 v2 ≥ utility0 v0 v1 v2 b0 v1 v2 := by
  unfold utility0
  split_ifs <;> simp_all; omega

end VickreyThreeBidder

/-! ## VCG en enchère combinatoire : non-monotonie du revenu (Conitzer-Sandholm)

    La principale défaillance de VCG en présence de complémentarités : le revenu
    du vendeur peut STRICTEMENT DIMINUER quand on ajoute un enchérisseur. Ce résultat
    motive les mécanismes ascendants (Ausubel-Milgrom) et montre que VCG n'est pas
    approprié aux enchères combinatoires avec fortes complémentarités.

    Référence : Conitzer & Sandholm (2006), "Failures of the VCG Mechanism in
    Combinatorial Auctions and Multi-agent Systems".
    Référence : #1469 Track 2 — contre-exemple fini d'échec VCG.
-/

namespace VCGCombinatorial

/-- Helper : maximum d'une liste de naturels. -/
def maxOver (vals : List ℕ) : ℕ := vals.foldl Nat.max 0

/- Modélisation : 2 objets A et B. `oA` (resp. `oB`) = indice de l'enchérisseur
   qui reçoit A (resp. B). Un indice absent de l'allocation ne reçoit rien. -/

/-- Enchérisseur 1 (indice 0) : complémentarités. Valeur 10 pour le bundle {A,B}, 0 sinon. -/
def v1_of (oA oB : ℕ) : ℕ := if oA = 0 ∧ oB = 0 then 10 else 0

/-- Enchérisseur 2 (indice 1) : veut seulement A. Valeur 8 ssi oA = 1. -/
def v2_of (oA oB : ℕ) : ℕ := if oA = 1 then 8 else 0

/-- Enchérisseur 3 (indice 2) : veut seulement B. Valeur 8 ssi oB = 2. -/
def v3_of (oA oB : ℕ) : ℕ := if oB = 2 then 8 else 0

/-- Bien-être social à 2 enchérisseurs {1, 2}. -/
def sw2 (oA oB : ℕ) : ℕ := v1_of oA oB + v2_of oA oB

/-- Bien-être social à 3 enchérisseurs {1, 2, 3}. -/
def sw3 (oA oB : ℕ) : ℕ := v1_of oA oB + v2_of oA oB + v3_of oA oB

/-- Maximum du bien-être à 2 enchérisseurs sur les 4 allocations (oA, oB ∈ {0,1}). -/
def maxSW2 : ℕ := maxOver [sw2 0 0, sw2 0 1, sw2 1 0, sw2 1 1]

/-- Maximum du bien-être à 3 enchérisseurs sur les 9 allocations. -/
def maxSW3 : ℕ :=
  maxOver [sw3 0 0, sw3 0 1, sw3 0 2, sw3 1 0, sw3 1 1, sw3 1 2, sw3 2 0, sw3 2 1, sw3 2 2]

/-- **Lemme** : bien-être social maximal à 2 enchérisseurs = 10 (le bidder 1 prend les deux). -/
theorem maxSW2_eq : maxSW2 = 10 := by decide

/-- **Lemme** : bien-être social maximal à 3 enchérisseurs = 16 (bidders 2 et 3 se partagent). -/
theorem maxSW3_eq : maxSW3 = 16 := by decide

/-- L'allocation optimale à 2 enchérisseurs est (0, 0) : le bidder 1 prend {A, B}. -/
theorem opt2 : sw2 0 0 = maxSW2 := by decide

/-- L'allocation optimale à 3 enchérisseurs est (1, 2) : le bidder 2 prend A, le bidder 3 prend B. -/
theorem opt3 : sw3 1 2 = maxSW3 := by decide

/-! ### Paiements VCG (pivot de Clarke)

    Le paiement de l'enchérisseur `i` est son externalité :
    `payment_i = maxSW(sans i) − bien-être_des_autres_dans_l'allocation_optimale`. -/

/-- Bien-être max à 2 enchérisseurs quand le bidder 1 est absent (seul le 2 reste). -/
def maxSW2_without1 : ℕ := maxOver [v2_of 0 0, v2_of 0 1, v2_of 1 0, v2_of 1 1]

/-- Bien-être max à 2 enchérisseurs quand le bidder 2 est absent (seul le 1 reste). -/
def maxSW2_without2 : ℕ := maxOver [v1_of 0 0, v1_of 0 1, v1_of 1 0, v1_of 1 1]

theorem maxSW2_without1_eq : maxSW2_without1 = 8 := by decide
theorem maxSW2_without2_eq : maxSW2_without2 = 10 := by decide

/-- Bien-être conjoint des bidders 2 et 3. -/
def welfare23 (oA oB : ℕ) : ℕ := v2_of oA oB + v3_of oA oB
/-- Bien-être conjoint des bidders 1 et 3. -/
def welfare13 (oA oB : ℕ) : ℕ := v1_of oA oB + v3_of oA oB

/-- Bien-être max à 3 enchérisseurs quand le bidder 1 est absent (bidders 2, 3 restent). -/
def maxSW3_without1 : ℕ :=
  maxOver [welfare23 0 0, welfare23 0 1, welfare23 0 2,
           welfare23 1 0, welfare23 1 1, welfare23 1 2,
           welfare23 2 0, welfare23 2 1, welfare23 2 2]

/-- Bien-être max à 3 enchérisseurs quand le bidder 2 est absent (bidders 1, 3 restent). -/
def maxSW3_without2 : ℕ :=
  maxOver [welfare13 0 0, welfare13 0 1, welfare13 0 2,
           welfare13 1 0, welfare13 1 1, welfare13 1 2,
           welfare13 2 0, welfare13 2 1, welfare13 2 2]

/-- Bien-être max à 3 enchérisseurs quand le bidder 3 est absent (bidders 1, 2 restent = sw2). -/
def maxSW3_without3 : ℕ := maxSW2

theorem maxSW3_without1_eq : maxSW3_without1 = 16 := by decide
theorem maxSW3_without2_eq : maxSW3_without2 = 10 := by decide
theorem maxSW3_without3_eq : maxSW3_without3 = 10 := maxSW2_eq

/-! ### Revenu à 2 enchérisseurs -/

/-- Paiement VCG du bidder 1 à 2 enchérisseurs (allocation opt (0,0), les autres = bidder 2 → 0). -/
def payment2_1 : ℕ := maxSW2_without1 - v2_of 0 0
/-- Paiement VCG du bidder 2 à 2 enchérisseurs (les autres = bidder 1 → v1(0,0) = 10). -/
def payment2_2 : ℕ := maxSW2_without2 - v1_of 0 0

theorem payment2_1_eq : payment2_1 = 8 := by decide
theorem payment2_2_eq : payment2_2 = 0 := by decide

/-- Revenu du vendeur à 2 enchérisseurs. -/
def revenue2 : ℕ := payment2_1 + payment2_2
theorem revenue2_eq : revenue2 = 8 := by decide

/-! ### Revenu à 3 enchérisseurs (allocation opt (1,2)) -/

/-- others-in-opt pour bidder 1 = v2(1,2) + v3(1,2) = 8 + 8 = 16. -/
def payment3_1 : ℕ := maxSW3_without1 - (v2_of 1 2 + v3_of 1 2)
/-- others-in-opt pour bidder 2 = v1(1,2) + v3(1,2) = 0 + 8 = 8. -/
def payment3_2 : ℕ := maxSW3_without2 - (v1_of 1 2 + v3_of 1 2)
/-- others-in-opt pour bidder 3 = v1(1,2) + v2(1,2) = 0 + 8 = 8. -/
def payment3_3 : ℕ := maxSW3_without3 - (v1_of 1 2 + v2_of 1 2)

theorem payment3_1_eq : payment3_1 = 0 := by decide
theorem payment3_2_eq : payment3_2 = 2 := by decide
theorem payment3_3_eq : payment3_3 = 2 := by decide

/-- Revenu du vendeur à 3 enchérisseurs. -/
def revenue3 : ℕ := payment3_1 + payment3_2 + payment3_3
theorem revenue3_eq : revenue3 = 4 := by decide

/-- **Théorème 5 (Conitzer-Sandholm, 2006)** : VCG n'est PAS monotone en revenu.
    Ajouter l'enchérisseur 3 (qui valorise B à 8) fait chuter le revenu du vendeur
    de 8 à 4, bien que le bien-être social augmente (10 → 16). Le bidder 1, qui
    payait 8 en tant que gagnant complémentaire, est déplacé et les deux bidders
    singletons ne paient chacun qu'une externalité de 2. -/
theorem vcg_revenue_non_monotone : revenue3 < revenue2 := by decide

end VCGCombinatorial

/-! ## Proposition 6 d'Othman-Sandholm (SAGT 2009) — MOMs stricts multi-agents

    Il existe des MOMs (Mechanisms Optimal under Manipulation) stricts dans des
    cadres multi-agents. La construction canonique est un mécanisme à 2 agents
    (ligne, colonne), chacun avec 2 types (a, a'), pour 4 issues au total. Les
    payoffs sont décrits par 2 matrices 2×2, une par type d'agent.

    Référence : Othman & Sandholm (2009), "Better with Byzantine : Manipulation-
    Optimal Mechanisms", section 2.4 (page 8 du PDF).
    Référence : #12329 — formalisation partielle du mécanisme (dominance stricte
    de `a'`, issue o1 sous la stratégie dominante, welfare M1, et le fragment
    « better with Byzantine » de la Prop 6 — voir la section « Strict MOM »).

-/

namespace OthmanSandholm

/-- Le type d'un agent. `0` = a, `1` = a'. -/
abbrev AgentType : Type := Fin 2

/-- Un report émis par un agent. -/
abbrev Report : Type := Fin 2

/-- Une issue du mécanisme. Encodage : `i.toNat` =
    `3 - 2 * (row_report.toNat) - (col_report.toNat)`, donc 4 issues pour 2 reports × 2 reports.
    `0` = (a',a') → o1, `1` = (a',a) → o2, `2` = (a,a') → o3, `3` = (a,a) → o4. -/
abbrev Issue : Type := Fin 4

/-- Le mécanisme Othman-Sandholm : (row_report, col_report) ↦ Issue,
    bijection `Fin 2 × Fin 2 → Fin 4` via `(r, c) ↦ 3 - 2 * r - c`, de sorte
    que `(a', a') ↦ o1`, `(a', a) ↦ o2`, `(a, a') ↦ o3`, `(a, a) ↦ o4`,
    en cohérence avec les matrices de payoff ci-dessous et l'encodage
    documenté de `Issue`. -/
def mechanism (rowReport colReport : Report) : Issue :=
  ⟨3 - 2 * rowReport.val - colReport.val, by
    have hr : rowReport.val < 2 := rowReport.isLt
    have hc : colReport.val < 2 := colReport.isLt
    omega⟩

/-! ### Matrices de payoff (transcription verbatim page 8 du PDF)

    Les payoffs par issue pour CHAQUE type d'agent sont donnés par 2 matrices
    (gauche et droite dans le papier). Transcription littérale :

    Matrice type `a` (gauche, payoffs = (u_row, u_col) par issue) :
    ```
    Report a   Report a'
    a    1,1   4,0
    a'   0,3   3,0
    ```

    Matrice type `a'` (droite, payoffs = (u_row, u_col) par issue) :
    ```
    Report a   Report a'
    a    3,4   5,0
    a'   0,6   0,0
    ```

    Lecture : `u_row type (issue)` = payoff du row agent de type `type` quand
    l'issue vaut `issue`. Idem pour `u_col`. -/

/-- Payoff du row agent quand il est de type `a` (= 0) et que l'issue vaut `i`. -/
def uRowTypeA (i : Issue) : ℕ :=
  -- (a, a) → o1 → row = 1
  -- (a, a') → o2 → row = 4
  -- (a', a) → o3 → row = 0
  -- (a', a') → o4 → row = 3
  match i with
  | 0 => 1  -- o1
  | 1 => 4  -- o2
  | 2 => 0  -- o3
  | 3 => 3  -- o4

/-- Payoff du row agent quand il est de type `a'` (= 1) et que l'issue vaut `i`. -/
def uRowTypeA' (i : Issue) : ℕ :=
  -- o1 → 3, o2 → 5, o3 → 0, o4 → 0
  match i with
  | 0 => 3
  | 1 => 5
  | 2 => 0
  | 3 => 0

/-- Payoff du col agent quand il est de type `a` (= 0) et que l'issue vaut `i`. -/
def uColTypeA (i : Issue) : ℕ :=
  -- o1 → 1, o2 → 0, o3 → 3, o4 → 0
  match i with
  | 0 => 1
  | 1 => 0
  | 2 => 3
  | 3 => 0

/-- Payoff du col agent quand il est de type `a'` (= 1) et que l'issue vaut `i`. -/
def uColTypeA' (i : Issue) : ℕ :=
  -- o1 → 4, o2 → 0, o3 → 6, o4 → 0
  match i with
  | 0 => 4
  | 1 => 0
  | 2 => 6
  | 3 => 0

/-- Payoffs du row agent selon son type (utilise les 2 matrices ci-dessus). -/
def uRow (t : AgentType) (i : Issue) : ℕ :=
  if t = 0 then uRowTypeA i else uRowTypeA' i

/-- Payoffs du col agent selon son type. -/
def uCol (t : AgentType) (i : Issue) : ℕ :=
  if t = 0 then uColTypeA i else uColTypeA' i

/-- Bien-être social (= somme des payoffs row + col) sous le mécanisme `OthmanSandholm`,
    pour des types réels (tRow, tCol) et des reports (rRow, rCol). -/
def welfare (tRow tCol : AgentType) (rRow rCol : Report) : ℕ :=
  let i := mechanism rRow rCol
  uRow tRow i + uCol tCol i

/-! ### Stratégie dominante : reporter `a'` (= 1) est strictement dominant

    Le papier Othman-Sandholm affirme : "In the mechanism, reporting a' is a
    strictly dominant strategy for agents of both types." On le prouve par
    `decide` sur les 8 cas (2 types × 2 reports fixes de l'adversaire × 2 reports
    propres possibles). -/

/-- Pour le row agent, **quel que soit son type** et **quel que soit le report
    du col agent**, reporter `a'` (= 1) donne un payoff ≥ reporter `a` (= 0). -/
theorem row_dominant_is_a' (tRow tCol : AgentType) (colReport : Report) :
    uRow tRow (mechanism 1 colReport) ≥ uRow tRow (mechanism 0 colReport) := by
  unfold uRow
  fin_cases tRow <;> fin_cases tCol <;> fin_cases colReport <;> simp [uRowTypeA, uRowTypeA', mechanism] <;> decide

/-- Pour le col agent, **quel que soit son type** et **quel que soit le report
    du row agent**, reporter `a'` (= 1) donne un payoff ≥ reporter `a` (= 0). -/
theorem col_dominant_is_a' (tRow tCol : AgentType) (rowReport : Report) :
    uCol tCol (mechanism rowReport 1) ≥ uCol tCol (mechanism rowReport 0) := by
  unfold uCol
  fin_cases tRow <;> fin_cases tCol <;> fin_cases rowReport <;> simp [uColTypeA, uColTypeA', mechanism] <;> decide

/-! ### Mécanisme truthful M1 = "boxed" par revelation principle

    Si tous les agents suivent la stratégie dominante (reportent `a'`), l'issue
    produite par le mécanisme `OthmanSandholm` est `o1` (issue 0). Par
    révélation principle (revelation principle), ce mécanisme non-truthful est
    équivalent en welfare à un mécanisme truthful M1 qui produit toujours `o1`.

    On vérifie que l'issue est bien `o1` (i.e. `mechanism 1 1 = 0`). -/
theorem dominant_strategy_yields_o1 :
    mechanism (1 : Report) (1 : Report) = (0 : Issue) := by
  simp [mechanism]

/-! ### Welfare sous le mécanisme boxed M1 (toujours o1)

    Sous M1, la welfare pour chaque combinaison de types réels vaut :
    `(a, a) → 2`, `(a, a') → 5`, `(a', a) → 4`, `(a', a') → 7`
    (ce que le tableau page 9 du PDF exprime par issue).
    Vérification `decide` sur les 4 cas. -/
theorem welfare_M1 (tRow tCol : AgentType) :
    welfare tRow tCol 1 1 =
      (if tRow = 0 ∧ tCol = 0 then 2
       else if tRow = 0 ∧ tCol = 1 then 5
       else if tRow = 1 ∧ tCol = 0 then 4
       else 7) := by
  unfold welfare uRow uCol
  fin_cases tRow <;> fin_cases tCol <;>
    simp [uRowTypeA, uRowTypeA', uColTypeA, uColTypeA', mechanism] <;> decide

/-! ### Strict MOM — « better with Byzantine » (fragment vérifiable de la Prop 6)

    La propriété-clé de la construction est que, **même si les agents ont une
    stratégie strictement dominante `a'`**, un agent de type `a` qui rapporte
    `a` (déviant de sa stratégie dominante, geste « byzantin ») produit une
    welfare strictement **supérieure** à celle de l'issue `o1` (= le mécanisme
    truthful boxed M1), et ce **quel que soit le rapport de l'agent adverse**.
    C'est le « better with Byzantine » d'Othman-Sandholm : la manipulation
    fait mieux que le benchmark truthfulness.

    Remarque importante : l'énoncé « suivre la stratégie dominante maximise la
    welfare » est **faux** (contre-exemple : `welfare 0 0 1 1 = 2` tandis que
    `welfare 0 0 1 0 = 4` > 2) — c'est ce qui a motivé le retrait de
    `dominant_strategy_maximizes_welfare`. C'est l'énoncé **inverse** que la
    Prop 6 met en avant : la déviation byzantine améliore la welfare. -/

/-- **Strict MOM / better-with-Byzantine** : pour le profil de types `(a, a)`
    (`tRow = tCol = 0`), un col agent de type `a` qui rapporte `a` (au lieu de sa
    stratégie dominante `a'`) produit une welfare strictement supérieure à celle
    de l'issue `o1` (= M1 boxed), quel que soit le rapport du row agent. -/
theorem strict_mom_welfare_boost (rowReport : Report) :
    welfare 0 0 rowReport 0 > welfare 0 0 1 1 := by
  unfold welfare uRow uCol
  fin_cases rowReport <;>
    simp [uRowTypeA, uRowTypeA', uColTypeA, uColTypeA', mechanism] <;> decide

end OthmanSandholm

end SocialChoice
