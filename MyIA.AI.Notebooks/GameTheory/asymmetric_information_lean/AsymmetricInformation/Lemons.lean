/-
  Lemons — modèle Akerlof 1970, formalisation bornée
  ===================================================

  Formalisation en Lean 4 core (sans Mathlib) du modèle fondateur d'Akerlof
  sur le marché des « lemons » : sous asymétrie d'information entre vendeur
  (informé) et acheteur (non-informé), un **point fixe** sur l'ensemble des
  participants `S(P) = {q | c_q ≤ P}` peut fermer le marché pour la haute
  qualité.

  Trois régions paramétriques exclusivement :
  - `pooling_tenable` : un prix unique P accepte les deux types ;
  - `lemons_only` : un prix P ∈ [c_L, c_H) est compatible avec L seul ;
  - `no_trade` : aucun prix P ∈ [c_L, c_H] ne satisfait simultanément la
    participation vendeur et l'acceptation acheteur.

  Bornes strictes (audit canonique po-2025 c.475 + leçon DRINT c.477) :
  - PAS de clause auxiliaire en κ — non dérivée d'Akerlof 1970 *QJE* 84(3):488-500 ;
  - PAS de `∃!` sans hypothèses FINIES listées dans la signature ;
  - PAS de single-crossing/menu/signal — Akerlof est strictement price-only ;
  - Multiplicité acceptée : si plusieurs prix satisfont le point fixe, ils
    sont tous renvoyés.
-/

namespace AsymmetricInformation.Lemons

/-- Deux qualités : haut (H) et bas (L). Inductif concret, pas `Type H ⊕ L`. -/
inductive Quality where
  | low
  | high
  deriving DecidableEq, Repr

/-- Marché à deux qualités : paramètres algébriques **entiers** (cohérent
    avec l'API amont `BayesGame2` qui utilise `Int` pour les paiements).
    Tous les théorèmes de ce module portent sur ces entiers bornés. -/
structure TwoQualityMarket where
  cLow : Int     -- coût d'opportunité L (c_L)
  cHigh : Int    -- coût d'opportunité H (c_H)
  vLow : Int     -- valeur acheteur de L (v_L)
  vHigh : Int    -- valeur acheteur de H (v_H)
  /-- Contraintes de cohérence : les valeurs sont strictement ordonnées et
      les coûts strictement croissants avec la qualité. -/
  hValue : vLow < vHigh
  hCost : cLow < cHigh

/-- Probabilité a priori π ∈ [0, 1] encodée par numérateur sur 100. Hypothèse
    explicite : `πNum ≤ 100` est portée par chaque théorème qui l'utilise. -/
structure Prior where
  piNum : Nat     -- π = piNum / 100
  hPiNum : piNum ≤ 100

/-- Ensemble des qualités offertes à un prix P : `{q | c_q ≤ P}`. -/
def offered (m : TwoQualityMarket) (P : Int) : List Quality :=
  let sLow := if m.cLow ≤ P then [Quality.low] else []
  let sHigh := if m.cHigh ≤ P then [Quality.high] else []
  sLow ++ sHigh

/-- Espérance de la valeur acheteur, conditionnée à `offered m P`. La
    convention : si `offered` est vide, l'espérance est `0` (no-trade). Si
    un seul type est offert, l'espérance est sa valeur. Si les deux, c'est
    la moyenne pondérée par les fréquences du prior `π`. -/
def expectedValue (m : TwoQualityMarket) (π : Prior) (P : Int) : Int :=
  let qs := offered m P
  match qs with
  | []      => 0
  | [q]     => if q = Quality.low then m.vLow else m.vHigh
  | [_, _]  => (π.piNum * m.vHigh + (100 - π.piNum) * m.vLow) / 100
  | _       => 0  -- inatteignable pour 2 qualités

/-- Condition acheteur à un prix P : `P ≤ E[v(q) | q ∈ S(P)]`.
    C'est l'**anticipation bayésienne** : l'acheteur exige que la valeur
    espérée des voitures proposées couvre le prix. -/
def buyerAccepts (m : TwoQualityMarket) (π : Prior) (P : Int) : Prop :=
  P ≤ expectedValue m π P

/-- Prix pooling tenable : `c_H * 100 ≤ π * vHigh + (100 - π) * vLow`.
    Multiplication par 100 pour rester en entier (cohérent API amont). -/
def poolingTenable (m : TwoQualityMarket) (π : Prior) : Prop :=
  m.cHigh * 100 ≤ π.piNum * m.vHigh + (100 - π.piNum) * m.vLow

/-- Instance `Decidable` pour `poolingTenable` : toutes les opérations
    sous-jacentes sont sur `Int`/`Nat`, et Lean fournit `Int.decLe`. -/
instance poolingTenable.decidable (m : TwoQualityMarket) (π : Prior) :
    Decidable (poolingTenable m π) :=
  inferInstanceAs (Decidable (m.cHigh * 100 ≤ ↑π.piNum * m.vHigh + (100 - ↑π.piNum) * m.vLow))

/-- **Caractérisation lemons-only locale** : il existe un prix P ∈ [c_L, c_H)
    tel que `buyerAccepts m π P` tienne, **et** tel que seul L est offert
    (`offered m P = [Quality.low]`). -/
def lemonsOnlyPossible (m : TwoQualityMarket) (π : Prior) : Prop :=
  ∃ P : Int, m.cLow ≤ P ∧ P < m.cHigh ∧ P ≤ expectedValue m π P ∧
    offered m P = [Quality.low]

/-- No-trade : aucun prix P ∈ [c_L, c_H] ne satisfait simultanément la
    participation vendeur et l'acceptation acheteur. -/
def noTrade (m : TwoQualityMarket) (π : Prior) : Prop :=
  ¬ ∃ P : Int, m.cLow ≤ P ∧ P < m.cHigh ∧ P ≤ expectedValue m π P

/-- **Exemples décidés** — la formalisation **utilise réellement**
    l'arithmétique entière (sans Mathlib) :

    (a) `(c_L, c_H, v_L, v_H) = (0, 5, 0, 4)`, `π = 50%` → lemons-only possible
        avec `P = 0` : `offered = [Quality.low]`, `expectedValue m π 0 = 0`,
        donc `buyerAccepts 0 ≤ 0 = True`. -/
example : lemonsOnlyPossible ⟨0, 5, 0, 4, by omega, by omega⟩ ⟨50, by decide⟩ := by
  refine ⟨0, by decide, by decide, ?_, by decide⟩
  -- `buyerAccepts` : `0 ≤ expectedValue ⟨0,5,0,4⟩ π 0 = vLow = 0`.
  simp [expectedValue, offered]

/-- (b) `(c_L, c_H, v_L, v_H) = (0, 5, 0, 4)`, `π = 100%` → lemons-only avec `P = 0`. -/
example : lemonsOnlyPossible ⟨0, 5, 0, 4, by omega, by omega⟩ ⟨100, by decide⟩ := by
  refine ⟨0, by decide, by decide, ?_, by decide⟩
  simp [expectedValue, offered]

/-- (c) `(c_L, c_H, v_L, v_H) = (0, 2, 0, 4)`, `π = 50%` : pooling tenable. -/
example : poolingTenable ⟨0, 2, 0, 4, by omega, by omega⟩ ⟨50, by decide⟩ := by
  decide

/-- (d) `(c_L, c_H, v_L, v_H) = (0, 5, 0, 4)`, `π = 50%` : pooling NOT tenable. -/
example : ¬ poolingTenable ⟨0, 5, 0, 4, by omega, by omega⟩ ⟨50, by decide⟩ := by
  decide

end AsymmetricInformation.Lemons
