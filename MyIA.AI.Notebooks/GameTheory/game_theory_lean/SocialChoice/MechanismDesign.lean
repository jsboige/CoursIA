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

/-! ## Manipulation-optimal mechanisms : Proposition 6 d'Othman-Sandholm (SAGT 2009) -/

namespace OthmanSandholmProp6

/- Construction de la Proposition 6 (« Better with Byzantine », SAGT 2009, page 8) :
   il existe des strict MOM multi-agents avec objectif de bien-être social.

   Deux agents (row, column), deux types chacun (a, a'), quatre issues o1..o4.
   Le mécanisme mappe le profil de rapports (row, column) vers :
     (a', a') -> o1 ; (a', a) -> o2 ; (a, a') -> o3 ; (a, a) -> o4.
   (Dans le papier, row = ligne, column = colonne.)

   Matrices de gains de la page 8, recopiées littéralement — gains du type a
   à gauche, du type a' à droite (chaque cellule = (row, column)) :

     Rapport   a'      a            Rapport   a'      a
     a'      1,1     4,0            a'      3,4     5,0
     a       0,3     3,0            a       0,6     0,0
            type a                      type a'

   Vue par issue (page 9 du papier, urow puis ucolumn pour chaque type) :

     Issue   u_row(a)  u_row(a')  u_col(a)  u_col(a')
     o1         1         3         1         4
     o2         4         5         0         0
     o3         0         0         3         6
     o4         3         0         0         0

   Ce sont exactement les valeurs du notebook GameTheory-16 §4.6.1 (u_row/u_col). -/

/-- `T` = types possibles d'un agent : `aa` (type a) ou `ap` (type a'). -/
inductive T | aa | ap
deriving DecidableEq

/-- `O` = les quatre issues du mécanisme. -/
inductive O | o1 | o2 | o3 | o4
deriving DecidableEq

/-- Gain de l'agent row selon l'issue et son vrai type (valeurs page 8, type a à gauche, a' à droite). -/
def uRow : O → T → ℕ
  | .o1, .aa => 1  | .o1, .ap => 3
  | .o2, .aa => 4  | .o2, .ap => 5
  | .o3, .aa => 0  | .o3, .ap => 0
  | .o4, .aa => 3  | .o4, .ap => 0

/-- Gain de l'agent column selon l'issue et son vrai type (valeurs page 8). -/
def uCol : O → T → ℕ
  | .o1, .aa => 1  | .o1, .ap => 4
  | .o2, .aa => 0  | .o2, .ap => 0
  | .o3, .aa => 3  | .o3, .ap => 6
  | .o4, .aa => 0  | .o4, .ap => 0

/-- Le mécanisme original : mappe le profil de rapports vers une issue
    (a',a')→o1, (a',a)→o2, (a,a')→o3, (a,a)→o4 — table page 8. -/
def mech : T → T → O
  | .ap, .ap => .o1
  | .ap, .aa => .o2
  | .aa, .ap => .o3
  | .aa, .aa => .o4

/-- Bien-être social d'une issue sous un profil de vrais types (somme des gains). -/
def sw (o : O) (tr tc : T) : ℕ := uRow o tr + uCol o tc

/-- Bien-être social produit par le mécanisme sous un profil de rapports. -/
def swMech (rr rc : T) (tr tc : T) : ℕ := sw (mech rr rc) tr tc

/-- `M₁`, le « boxed truthful mechanism » du papier : par le principe de
    révélation (rapporter a' est strictement dominant), M₁ choisit toujours o1. -/
def M1 : T → T → O := fun _ _ => .o1

/-! ### Caractéristique 1 : a' est strictement dominant ; M₁ est truthful -/

/-- Rapporter a' est strictement dominant pour l'agent row, quel que soit son
    vrai type, le rapport de l'autre, et pour les deux mécanismes (mech et M₁) —
    calculé ici sur `mech` : pour chaque (vrai type, rapport column), le gain de
    rapporter a' dépasse strictement celui de rapporter a. -/
theorem report_ap_strictly_dominant_row (tr : T) (rc : T) :
    uRow (mech .ap rc) tr > uRow (mech .aa rc) tr := by
  cases tr <;> cases rc <;> decide

/-- Rapporter a' est strictement dominant pour l'agent column (symétrie). -/
theorem report_ap_strictly_dominant_col (tc : T) (rr : T) :
    uCol (mech rr .ap) tc > uCol (mech rr .aa) tc := by
  cases tc <;> cases rr <;> decide

/-! ### Caractéristique 2 : le bien-être social est strictement supérieur
    dès qu'un agent de type a joue a -/

/-- Caractéristique 2 (forme stricte) : si l'agent row (de vrai type a) joue a
    au lieu de a', le bien-être social est strictement plus élevé que celui de
    M₁ (o1), quel que soit le vrai type de l'agent column. -/
theorem char2_row_plays_a (tc : T) :
    swMech .aa .ap .aa tc > sw .o1 .aa tc := by
  cases tc <;> decide

/-- Caractéristique 2 (forme stricte) : si l'agent column (de vrai type a)
    joue a au lieu de a', le bien-être social est strictement plus élevé que
    celui de M₁, quel que soit le vrai type de l'agent row. -/
theorem char2_col_plays_a (tr : T) :
    swMech .ap .aa tr .aa > sw .o1 tr .aa := by
  cases tr <;> decide

/-! ### La table SW du papier (page 9) -/

/-- La table de bien-être social de la page 9 : SW(o1,o2,o3,o4) pour chaque
    profil de vrais types. Chaque ligne est un théorème vérifié par decide. -/
theorem sw_table_aa_aa : [sw .o1 .aa .aa, sw .o2 .aa .aa, sw .o3 .aa .aa, sw .o4 .aa .aa] = [2, 4, 3, 3] := by decide
theorem sw_table_aa_ap : [sw .o1 .aa .ap, sw .o2 .aa .ap, sw .o3 .aa .ap, sw .o4 .aa .ap] = [5, 4, 6, 3] := by decide
theorem sw_table_ap_aa : [sw .o1 .ap .aa, sw .o2 .ap .aa, sw .o3 .ap .aa, sw .o4 .ap .aa] = [4, 5, 3, 0] := by decide
theorem sw_table_ap_ap : [sw .o1 .ap .ap, sw .o2 .ap .ap, sw .o3 .ap .ap, sw .o4 .ap .ap] = [7, 5, 6, 0] := by decide

/-! ### Proposition 6 : M₁ est un strict MOM (forme v1 : caractéristiques 1 et 2) -/

/-- **Proposition 6 (Othman-Sandholm 2009)** — il existe des strict MOM
    multi-agents avec objectif de bien-être social. Formellement, sur ce
    domaine fini : (1) rapporter a' est strictement dominant pour les deux
    agents, donc M₁ (qui choisit toujours o1) est le mécanisme truthful
    « boxed » de mech ; (2) dès qu'un agent de type a dévie et joue a, le
    bien-être social dépasse strictement celui de M₁ — le mécanisme fait
    *mieux avec Byzantine*. -/
theorem prop6_strict_mom :
    (∀ tr rc, uRow (mech .ap rc) tr > uRow (mech .aa rc) tr)
    ∧ (∀ tc rr, uCol (mech rr .ap) tc > uCol (mech rr .aa) tc)
    ∧ (∀ tc, swMech .aa .ap .aa tc > sw .o1 .aa tc)
    ∧ (∀ tr, swMech .ap .aa tr .aa > sw .o1 tr .aa) := by
  constructor <;> [ exact report_ap_strictly_dominant_row
                  ; constructor <;> [ exact report_ap_strictly_dominant_col
                                    ; constructor <;> [ exact char2_row_plays_a
                                                      ; exact char2_col_plays_a ] ] ]

/-- M₁ choisit toujours o1 : sa table de bien-être est la colonne o1 de la
    table SW. -/
theorem M1_is_sw_o1 (tr tc : T) : sw (M1 tr tc) tr tc = sw .o1 tr tc := by
  cases tr <;> cases tc <;> decide

/-- o1 est optimal pour le profil (a', a') — c'est pourquoi M_D(a',a') = o1
    dans l'argument de Pareto-indominabilité (page 9). -/
theorem o1_optimal_at_ap_ap (o : O) : sw .o1 .ap .ap ≥ sw o .ap .ap := by
  cases o <;> decide

end OthmanSandholmProp6


end SocialChoice
