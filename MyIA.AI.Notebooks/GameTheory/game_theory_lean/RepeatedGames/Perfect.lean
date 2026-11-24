import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic
import RepeatedGames.Stage
import RepeatedGames.Discounting
import RepeatedGames.GrimTrigger
import RepeatedGames.Folk

/-!
# Équilibre parfait en sous-jeux et principe de déviation unique

`GrimTrigger.lean` énonce la condition INCITATIVE du grim trigger
(`coopValue R δ ≥ deviateValue T P δ ↔ δ ≥ (T − R)/(T − P)`) et signale
lui-même le trou : sans sémantique des historiques et des profils de
stratégies, cette condition ne dit pas que le profil est un équilibre
parfait en sous-jeux (ESPS). Ce module comble ce trou.

## Ce qui est construit

1. **Histoires et stratégies** : `Hist` est la liste des actions conjointes
   déjà jouées (la plus ancienne en tête) ; une stratégie comportementale
   `Strategy` lit l'histoire et choisit une action. `orbitAux` déroule les
   histoires successives ; `contPayoff` est le paiement actualisé depuis une
   histoire arbitraire — il évalue donc aussi les sous-jeux hors du chemin.

2. **Principe de déviation unique** (`oneShotDeviationPrinciple`) : un profil
   est un équilibre parfait en sous-jeux dès qu'aucune déviation *d'un seul
   coup* (dévier à une histoire, puis revenir au profil) n'est profitable,
   **à toute histoire**.

3. **Grim trigger est un ESPS ssi `δ ≥ (T − R)/(T − P)`** (`grim_isSPE_iff`),
   sous `0 ≤ δ < 1`.

## L'hypothèse de plus, nommée

Le principe de déviation unique n'est pas gratuit. Il demande que le gain
d'une déviation s'éteigne le long de l'orbite de déviation. Deux hypothèses
le portent, et elles figurent **dans la signature du théorème**, pas en
commentaire :

  **(H1) gains de stage uniformément bornés** — `hK : ∀ a b, |u a b| ≤ K`.
  Sur un jeu fini c'est automatique (`stagePayoff_abs_le` : quatre valeurs),
  mais c'est bien une hypothèse sur le jeu de stage, pas une tautologie.
  C'est elle qui donne `|V_h| ≤ K/(1 − δ)` pour *toute* histoire `h`
  (`abs_contPayoff_le`), donc un gain de déviation uniformément borné le
  long de l'orbite de déviation.

  **(H2) `δ < 1`** — c'est elle qui fait tendre `δ^k · B` vers `0`
  (`le_zero_of_forall_geometric_bound`), donc éteindre le gain résiduel.

Sans (H1) ou (H2) l'énoncé est faux : une déviation peut ne devenir
profitable qu'asymptotiquement. C'est précisément l'hypothèse que
`GrimTrigger.lean` ne pouvait pas nommer, faute de sémantique des historiques.

## La récursion du gain, et pourquoi elle n'est pas une identité

Point technique qui porte tout le module. Écrire `G(h) = OS(h) + δ·G(h')`
serait faux comme identité : le profil déviant et le profil de référence
**n'empilent pas la même action conjointe**, donc leurs paiements ne se
décomposent pas au même successeur. Ce qui est vrai — et suffisant — est
l'**inégalité** `G(h) ≤ δ·G(h')`, obtenue en confrontant le gain du premier
coup déviant à la non-profitabilité de la déviation ponctuelle **en `h`**.
La démonstration est `gainRow_le_step` / `gainCol_le_step` ; l'identité
`contPayoff_cons` dont elles partent, elle, est purement algébrique.

## Pourquoi le jeu est paramétré par `u₁` et `u₂`

Le théorème est énoncé pour deux tables de gains abstraites `u₁ u₂` et deux
bornes `K₁ K₂`, puis instancié sur le Dilemme du Prisonnier. Cela rend visible
que le principe ne dépend d'aucune propriété du jeu de stage au-delà de (H1).
-/

open scoped Topology
open Filter

namespace RepeatedGames
open PDAction

/-! ## Histoires, stratégies, orbites -/

/-- Histoire finie : la liste des actions conjointes déjà jouées, la plus
    ancienne en tête. -/
abbrev Hist : Type := List (PDAction × PDAction)

/-- Stratégie comportementale : ce qu'un joueur joue après une histoire finie. -/
abbrev Strategy : Type := Hist → PDAction

/-- L'orbite : la suite des histoires rencontrées depuis `h` quand les deux
    joueurs suivent `σ₁` et `σ₂`. Récursion sur le nombre de pas ; l'histoire
    est un paramètre qui avance. -/
def orbitAux (σ₁ σ₂ : Strategy) : ℕ → Hist → Hist
  | 0, h => h
  | (n + 1), h => orbitAux σ₁ σ₂ n (h ++ [(σ₁ h, σ₂ h)])

/-- L'action conjointe jouée à l'étape `n` depuis l'histoire `h`. -/
def actionAt (σ₁ σ₂ : Strategy) (h : Hist) (n : ℕ) : PDAction × PDAction :=
  (σ₁ (orbitAux σ₁ σ₂ n h), σ₂ (orbitAux σ₁ σ₂ n h))

/-- Paiement actualisé d'un joueur de table de gains `u`, depuis l'histoire
    `h` : le sous-jeu qui commence en `h`. En `h = []` c'est le paiement du
    jeu entier. -/
noncomputable def contPayoff (u : PDAction → PDAction → ℝ) (δ : ℝ)
    (σ₁ σ₂ : Strategy) (h : Hist) : ℝ :=
  ∑' n : ℕ, δ ^ n * u (actionAt σ₁ σ₂ h n).1 (actionAt σ₁ σ₂ h n).2

/-! ## Lemmes de structure de l'orbite -/

lemma actionAt_zero (σ₁ σ₂ : Strategy) (h : Hist) :
    actionAt σ₁ σ₂ h 0 = (σ₁ h, σ₂ h) := rfl

lemma actionAt_succ (σ₁ σ₂ : Strategy) (h : Hist) (n : ℕ) :
    actionAt σ₁ σ₂ h (n + 1) = actionAt σ₁ σ₂ (h ++ [actionAt σ₁ σ₂ h 0]) n := rfl

/-- Toute orbite garde l'histoire de départ comme préfixe. -/
lemma orbitAux_exists_append (σ₁ σ₂ : Strategy) (n : ℕ) (h : Hist) :
    ∃ t : Hist, orbitAux σ₁ σ₂ n h = h ++ t := by
  induction n generalizing h with
  | zero => exact ⟨[], by simp [orbitAux]⟩
  | succ n ih =>
    obtain ⟨t, ht⟩ := ih (h ++ [(σ₁ h, σ₂ h)])
    exact ⟨(σ₁ h, σ₂ h) :: t, by rw [orbitAux, ht, List.append_assoc]; rfl⟩

/-- Corollaire : une orbite n'est jamais plus courte que son histoire de départ. -/
lemma length_le_orbitAux (σ₁ σ₂ : Strategy) (n : ℕ) (h : Hist) :
    h.length ≤ (orbitAux σ₁ σ₂ n h).length := by
  obtain ⟨t, ht⟩ := orbitAux_exists_append σ₁ σ₂ n h
  rw [ht, List.length_append]
  omega

/-- Deux profils qui coïncident sur toute histoire plus longue que `h₀`
    produisent la même orbite depuis toute histoire plus longue que `h₀`.
    C'est ce qui autorise une déviation ponctuelle à redevenir le profil
    d'origine une fois l'histoire allongée. -/
lemma orbitAux_congr {σ₁ σ₁' σ₂ σ₂' : Strategy} {h₀ : Hist}
    (h₁ : ∀ k : Hist, h₀.length < k.length → σ₁ k = σ₁' k)
    (h₂ : ∀ k : Hist, h₀.length < k.length → σ₂ k = σ₂' k)
    (n : ℕ) {h : Hist} (hl : h₀.length < h.length) :
    orbitAux σ₁ σ₂ n h = orbitAux σ₁' σ₂' n h := by
  induction n generalizing h with
  | zero => rfl
  | succ n ih =>
    have hx : (σ₁ h, σ₂ h) = (σ₁' h, σ₂' h) := by rw [h₁ h hl, h₂ h hl]
    have hl' : h₀.length < (h ++ [(σ₁' h, σ₂' h)]).length := by
      rw [List.length_append]; simp; omega
    rw [orbitAux, orbitAux, hx]
    exact ih hl'

lemma actionAt_congr {σ₁ σ₁' σ₂ σ₂' : Strategy} {h₀ : Hist}
    (h₁ : ∀ k : Hist, h₀.length < k.length → σ₁ k = σ₁' k)
    (h₂ : ∀ k : Hist, h₀.length < k.length → σ₂ k = σ₂' k)
    (n : ℕ) {h : Hist} (hl : h₀.length < h.length) :
    actionAt σ₁ σ₂ h n = actionAt σ₁' σ₂' h n := by
  have ho := orbitAux_congr h₁ h₂ n hl
  have hlen : h₀.length < (orbitAux σ₁' σ₂' n h).length := by
    rw [← ho]
    exact lt_of_lt_of_le hl (length_le_orbitAux σ₁ σ₂ n h)
  simp only [actionAt, ho, h₁ _ hlen, h₂ _ hlen]

/-- Congruence du paiement actualisé pour deux profils qui coïncident au-delà
    de l'histoire `h₀`. -/
lemma contPayoff_congr_of_length {u : PDAction → PDAction → ℝ} {δ : ℝ}
    {σ₁ σ₁' σ₂ σ₂' : Strategy} {h₀ : Hist}
    (h₁ : ∀ k : Hist, h₀.length < k.length → σ₁ k = σ₁' k)
    (h₂ : ∀ k : Hist, h₀.length < k.length → σ₂ k = σ₂' k)
    {h : Hist} (hl : h₀.length < h.length) :
    contPayoff u δ σ₁ σ₂ h = contPayoff u δ σ₁' σ₂' h := by
  unfold contPayoff
  congr 1
  funext n
  rw [actionAt_congr h₁ h₂ n hl]

/-! ## Sommabilité et borne uniforme : (H1) en action -/

/-- Le paiement actualisé depuis n'importe quelle histoire est sommable dès que
    `0 ≤ δ < 1` et que les gains de stage sont bornés par `K`. C'est ici que
    (H1) entre : la comparaison géométrique exige une borne uniforme,
    indépendante de l'histoire. -/
lemma summable_contPayoff (u : PDAction → PDAction → ℝ) {K : ℝ}
    (hK : ∀ a b, |u a b| ≤ K) {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ < 1)
    (σ₁ σ₂ : Strategy) (h : Hist) :
    Summable (fun n : ℕ =>
      δ ^ n * u (actionAt σ₁ σ₂ h n).1 (actionAt σ₁ σ₂ h n).2) := by
  have hK0 : 0 ≤ K := le_trans (abs_nonneg _) (hK cooperate cooperate)
  have hgeo : HasSum (fun n : ℕ => δ ^ n) ((1 - δ)⁻¹) :=
    hasSum_geometric_of_lt_one h0 h1
  refine Summable.of_norm_bounded
    ⟨(1 - δ)⁻¹ * K, HasSum.mul_right K hgeo⟩ ?_
  intro n
  have hp : (0 : ℝ) ≤ δ ^ n := pow_nonneg h0 n
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hp]
  exact mul_le_mul_of_nonneg_left (hK _ _) hp

/-- Borne uniforme `K/(1−δ)` sur le paiement actualisé depuis **toute**
    histoire. C'est cette uniformité — et non la seule sommabilité — qui
    rend le gain de déviation borné le long de l'orbite, donc éteignable. -/
lemma abs_contPayoff_le (u : PDAction → PDAction → ℝ) {K : ℝ}
    (hK : ∀ a b, |u a b| ≤ K) {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ < 1)
    (σ₁ σ₂ : Strategy) (h : Hist) :
    |contPayoff u δ σ₁ σ₂ h| ≤ K / (1 - δ) := by
  have hK0 : 0 ≤ K := le_trans (abs_nonneg _) (hK cooperate cooperate)
  have h1pos : 0 < 1 - δ := by linarith
  have hgeo : HasSum (fun n : ℕ => δ ^ n) ((1 - δ)⁻¹) :=
    hasSum_geometric_of_lt_one h0 h1
  have hbound : ∀ n : ℕ, ‖δ ^ n * u (actionAt σ₁ σ₂ h n).1
      (actionAt σ₁ σ₂ h n).2‖ ≤ δ ^ n * K := by
    intro n
    have hp : (0 : ℝ) ≤ δ ^ n := pow_nonneg h0 n
    calc ‖δ ^ n * u (actionAt σ₁ σ₂ h n).1 (actionAt σ₁ σ₂ h n).2‖
        = δ ^ n * |u (actionAt σ₁ σ₂ h n).1 (actionAt σ₁ σ₂ h n).2| := by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hp]
      _ ≤ δ ^ n * K := mul_le_mul_of_nonneg_left (hK _ _) hp
  have hb : Summable (fun n : ℕ => δ ^ n * K) :=
    (HasSum.mul_right K hgeo).summable
  have hfn : Summable (fun n : ℕ => ‖δ ^ n * u (actionAt σ₁ σ₂ h n).1
      (actionAt σ₁ σ₂ h n).2‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hbound hb
  have hmain : ‖∑' n : ℕ, δ ^ n * u (actionAt σ₁ σ₂ h n).1
        (actionAt σ₁ σ₂ h n).2‖ ≤ K / (1 - δ) := by
    calc ‖∑' n : ℕ, δ ^ n * u (actionAt σ₁ σ₂ h n).1 (actionAt σ₁ σ₂ h n).2‖
        ≤ ∑' n : ℕ, ‖δ ^ n * u (actionAt σ₁ σ₂ h n).1
            (actionAt σ₁ σ₂ h n).2‖ := norm_tsum_le_tsum_norm hfn
      _ ≤ ∑' n : ℕ, δ ^ n * K := Summable.tsum_le_tsum hbound hfn hb
      _ = K * (1 - δ)⁻¹ := by
        have hh := (HasSum.mul_right K hgeo).tsum_eq
        rw [hh]; ring
      _ = K / (1 - δ) := by rw [div_eq_mul_inv]
  simpa [contPayoff, Real.norm_eq_abs] using hmain

/-- **Extinction du résidu géométrique** — c'est (H2). Sans `δ < 1`, une
    majoration `x ≤ δ^k B` pour tout `k` n'interdit pas `x > 0`. -/
lemma le_zero_of_forall_geometric_bound {δ B x : ℝ} (h0 : 0 ≤ δ) (h1 : δ < 1)
    (_hB : 0 ≤ B) (h : ∀ k : ℕ, x ≤ δ ^ k * B) : x ≤ 0 := by
  by_contra hx
  rw [not_le] at hx
  have hpow : Tendsto (fun k : ℕ => δ ^ k) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1
  have hlim : Tendsto (fun k : ℕ => δ ^ k * B) atTop (nhds 0) := by
    simpa using hpow.mul_const B
  have hev : ∀ᶠ k : ℕ in atTop, δ ^ k * B < x := (tendsto_order.1 hlim).2 x hx
  obtain ⟨k, hk⟩ := eventually_atTop.1 hev
  have hk' : δ ^ k * B < x := hk k le_rfl
  linarith [h k]

/-! ## Décomposition du paiement : une identité algébrique -/

/-- Identité de scission : le paiement depuis `h` est le gain du coup présent
    plus `δ` fois le paiement depuis l'histoire augmentée. Purement algébrique
    une fois la sommabilité acquise (H1).

    C'est une identité — mais elle ne relie le profil déviant et le profil de
    référence qu'à des successeurs **différents** (chacun empile sa propre
    action conjointe). D'où l'inégalité, et non l'identité, dans
    `gainRow_le_step`. -/
lemma contPayoff_cons (u : PDAction → PDAction → ℝ) {K : ℝ}
    (hK : ∀ a b, |u a b| ≤ K) {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ < 1)
    (σ₁ σ₂ : Strategy) (h : Hist) :
    contPayoff u δ σ₁ σ₂ h
      = u (σ₁ h) (σ₂ h) + δ * contPayoff u δ σ₁ σ₂ (h ++ [(σ₁ h, σ₂ h)]) := by
  have hsum := summable_contPayoff u hK h0 h1 σ₁ σ₂ h
  have hshift : ∀ n : ℕ,
      δ ^ (n + 1) * u (actionAt σ₁ σ₂ h (n + 1)).1 (actionAt σ₁ σ₂ h (n + 1)).2
        = δ * (δ ^ n * u (actionAt σ₁ σ₂ (h ++ [(σ₁ h, σ₂ h)]) n).1
            (actionAt σ₁ σ₂ (h ++ [(σ₁ h, σ₂ h)]) n).2) := by
    intro n
    rw [actionAt_succ]
    calc δ ^ (n + 1) * u (actionAt σ₁ σ₂ (h ++ [actionAt σ₁ σ₂ h 0]) n).1
          (actionAt σ₁ σ₂ (h ++ [actionAt σ₁ σ₂ h 0]) n).2
        = (δ ^ n * δ) * u (actionAt σ₁ σ₂ (h ++ [actionAt σ₁ σ₂ h 0]) n).1
            (actionAt σ₁ σ₂ (h ++ [actionAt σ₁ σ₂ h 0]) n).2 := by rw [pow_succ]
      _ = δ * (δ ^ n * u (actionAt σ₁ σ₂ (h ++ [actionAt σ₁ σ₂ h 0]) n).1
            (actionAt σ₁ σ₂ (h ++ [actionAt σ₁ σ₂ h 0]) n).2) := by ring
  unfold contPayoff
  rw [Summable.tsum_eq_zero_add hsum, tsum_congr hshift, tsum_mul_left]
  simp [actionAt, orbitAux]

/-! ## Déviation ponctuelle -/

/-- Déviation ponctuelle : jouer `a` à l'histoire `h`, puis revenir au profil. -/
def oneShot (σ : Strategy) (h : Hist) (a : PDAction) : Strategy :=
  fun k => if k = h then a else σ k

@[simp] lemma oneShot_apply_self (σ : Strategy) (h : Hist) (a : PDAction) :
    oneShot σ h a h = a := by
  simp [oneShot]

lemma oneShot_agree (σ : Strategy) (h : Hist) (a : PDAction) :
    ∀ k : Hist, h.length < k.length → oneShot σ h a k = σ k := by
  intro k hk
  have hne : k ≠ h := by
    intro hh
    rw [hh] at hk
    exact lt_irrefl _ hk
  simp [oneShot, hne]

/-- Premier joueur : après une déviation ponctuelle en `h`, le paiement du
    sous-jeu qui commence juste après redevient celui du profil d'origine —
    l'histoire a grandi, la déviation n'y est plus active. -/
lemma contPayoff_oneShot_tail_row (u : PDAction → PDAction → ℝ) (δ : ℝ)
    (σ₁ σ₂ : Strategy) (h : Hist) (a : PDAction) :
    contPayoff u δ (oneShot σ₁ h a) σ₂ (h ++ [(a, σ₂ h)])
      = contPayoff u δ σ₁ σ₂ (h ++ [(a, σ₂ h)]) := by
  refine contPayoff_congr_of_length (h₀ := h) ?_ ?_ ?_
  · exact fun k hk => oneShot_agree σ₁ h a k hk
  · intro k _
    rfl
  · rw [List.length_append]
    simp

/-- Second joueur : même énoncé, la déviation porte sur la colonne. -/
lemma contPayoff_oneShot_tail_col (u : PDAction → PDAction → ℝ) (δ : ℝ)
    (σ₁ σ₂ : Strategy) (h : Hist) (b : PDAction) :
    contPayoff u δ σ₁ (oneShot σ₂ h b) (h ++ [(σ₁ h, b)])
      = contPayoff u δ σ₁ σ₂ (h ++ [(σ₁ h, b)]) := by
  refine contPayoff_congr_of_length (h₀ := h) ?_ ?_ ?_
  · intro k _
    rfl
  · exact fun k hk => oneShot_agree σ₂ h b k hk
  · rw [List.length_append]
    simp

/-- Gain net du premier coup pour le joueur de ligne : dévier en `h` vers `a`,
    encaisser, puis revenir au profil. -/
noncomputable def oneShotGainRow (u : PDAction → PDAction → ℝ) (δ : ℝ)
    (σ₁ σ₂ : Strategy) (h : Hist) (a : PDAction) : ℝ :=
  u a (σ₂ h) + δ * contPayoff u δ σ₁ σ₂ (h ++ [(a, σ₂ h)])
    - contPayoff u δ σ₁ σ₂ h

/-- Gain net du premier coup pour le joueur de colonne. -/
noncomputable def oneShotGainCol (u : PDAction → PDAction → ℝ) (δ : ℝ)
    (σ₁ σ₂ : Strategy) (h : Hist) (b : PDAction) : ℝ :=
  u (σ₁ h) b + δ * contPayoff u δ σ₁ σ₂ (h ++ [(σ₁ h, b)])
    - contPayoff u δ σ₁ σ₂ h

/-- Le paiement d'une déviation de ligne en `h` vers `a` vaut le paiement du
    profil plus le gain du premier coup. -/
lemma contPayoff_oneShot_row_eq (u : PDAction → PDAction → ℝ) {K : ℝ}
    (hK : ∀ a b, |u a b| ≤ K) {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ < 1)
    (σ₁ σ₂ : Strategy) (h : Hist) (a : PDAction) :
    contPayoff u δ (oneShot σ₁ h a) σ₂ h
      = contPayoff u δ σ₁ σ₂ h + oneShotGainRow u δ σ₁ σ₂ h a := by
  rw [contPayoff_cons u hK h0 h1 (oneShot σ₁ h a) σ₂ h, oneShot_apply_self,
    contPayoff_oneShot_tail_row]
  unfold oneShotGainRow
  ring

/-- Le paiement d'une déviation de colonne en `h` vers `b`. -/
lemma contPayoff_oneShot_col_eq (u : PDAction → PDAction → ℝ) {K : ℝ}
    (hK : ∀ a b, |u a b| ≤ K) {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ < 1)
    (σ₁ σ₂ : Strategy) (h : Hist) (b : PDAction) :
    contPayoff u δ σ₁ (oneShot σ₂ h b) h
      = contPayoff u δ σ₁ σ₂ h + oneShotGainCol u δ σ₁ σ₂ h b := by
  rw [contPayoff_cons u hK h0 h1 σ₁ (oneShot σ₂ h b) h, oneShot_apply_self,
    contPayoff_oneShot_tail_col]
  unfold oneShotGainCol
  ring

/-! ## Le gain d'une déviation arbitraire -/

/-- Gain de la stratégie de ligne `σ₁'` contre `σ₂`, à l'histoire `h`. -/
noncomputable def gainRow (u : PDAction → PDAction → ℝ) (δ : ℝ)
    (σ₁ σ₁' σ₂ : Strategy) (h : Hist) : ℝ :=
  contPayoff u δ σ₁' σ₂ h - contPayoff u δ σ₁ σ₂ h

/-- Gain de la stratégie de colonne `σ₂'` contre `σ₁`, à l'histoire `h`. -/
noncomputable def gainCol (u : PDAction → PDAction → ℝ) (δ : ℝ)
    (σ₁ σ₂ σ₂' : Strategy) (h : Hist) : ℝ :=
  contPayoff u δ σ₁ σ₂' h - contPayoff u δ σ₁ σ₂ h

/-- **Pas de récursion du gain, joueur de ligne.** Si le premier coup d'une
    déviation arbitraire n'est pas profitable (`hOS`), le gain total est
    majoré par `δ` fois le gain résiduel au successeur **du profil déviant**.

    C'est l'inégalité qui porte le principe. L'identité correspondante est
    fausse : les deux profils empilent des actions conjointes différentes. -/
lemma gainRow_le_step (u : PDAction → PDAction → ℝ) {K : ℝ}
    (hK : ∀ a b, |u a b| ≤ K) {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ < 1)
    (σ₁ σ₁' σ₂ : Strategy) (h : Hist)
    (hOS : oneShotGainRow u δ σ₁ σ₂ h (σ₁' h) ≤ 0) :
    gainRow u δ σ₁ σ₁' σ₂ h
      ≤ δ * gainRow u δ σ₁ σ₁' σ₂ (h ++ [(σ₁' h, σ₂ h)]) := by
  -- la déviation ponctuelle vers `σ₁' h` n'est pas profitable
  have hkey : u (σ₁' h) (σ₂ h) + δ * contPayoff u δ σ₁ σ₂ (h ++ [(σ₁' h, σ₂ h)])
      ≤ contPayoff u δ σ₁ σ₂ h := by
    have hh := contPayoff_oneShot_row_eq u hK h0 h1 σ₁ σ₂ h (σ₁' h)
    unfold oneShotGainRow at hOS
    linarith
  -- et le paiement déviant se scinde au même successeur
  have hdev : contPayoff u δ σ₁' σ₂ h
      = u (σ₁' h) (σ₂ h)
        + δ * contPayoff u δ σ₁' σ₂ (h ++ [(σ₁' h, σ₂ h)]) :=
    contPayoff_cons u hK h0 h1 σ₁' σ₂ h
  have hmul : δ * gainRow u δ σ₁ σ₁' σ₂ (h ++ [(σ₁' h, σ₂ h)])
      = δ * contPayoff u δ σ₁' σ₂ (h ++ [(σ₁' h, σ₂ h)])
        - δ * contPayoff u δ σ₁ σ₂ (h ++ [(σ₁' h, σ₂ h)]) := by
    rw [gainRow]; ring
  rw [gainRow, hdev, hmul]
  linarith

/-- **Pas de récursion du gain, joueur de colonne.** -/
lemma gainCol_le_step (u : PDAction → PDAction → ℝ) {K : ℝ}
    (hK : ∀ a b, |u a b| ≤ K) {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ < 1)
    (σ₁ σ₂ σ₂' : Strategy) (h : Hist)
    (hOS : oneShotGainCol u δ σ₁ σ₂ h (σ₂' h) ≤ 0) :
    gainCol u δ σ₁ σ₂ σ₂' h
      ≤ δ * gainCol u δ σ₁ σ₂ σ₂' (h ++ [(σ₁ h, σ₂' h)]) := by
  have hkey : u (σ₁ h) (σ₂' h) + δ * contPayoff u δ σ₁ σ₂ (h ++ [(σ₁ h, σ₂' h)])
      ≤ contPayoff u δ σ₁ σ₂ h := by
    have hh := contPayoff_oneShot_col_eq u hK h0 h1 σ₁ σ₂ h (σ₂' h)
    unfold oneShotGainCol at hOS
    linarith
  have hdev : contPayoff u δ σ₁ σ₂' h
      = u (σ₁ h) (σ₂' h)
        + δ * contPayoff u δ σ₁ σ₂' (h ++ [(σ₁ h, σ₂' h)]) :=
    contPayoff_cons u hK h0 h1 σ₁ σ₂' h
  have hmul : δ * gainCol u δ σ₁ σ₂ σ₂' (h ++ [(σ₁ h, σ₂' h)])
      = δ * contPayoff u δ σ₁ σ₂' (h ++ [(σ₁ h, σ₂' h)])
        - δ * contPayoff u δ σ₁ σ₂ (h ++ [(σ₁ h, σ₂' h)]) := by
    rw [gainCol]; ring
  rw [gainCol, hdev, hmul]
  linarith

/-- **Itération du gain, joueur de ligne.** Le gain d'une déviation arbitraire
    est majoré par `δⁿ` fois le gain résiduel à l'étape `n` de l'orbite de
    déviation. -/
lemma gainRow_le_iter (u : PDAction → PDAction → ℝ) {K : ℝ}
    (hK : ∀ a b, |u a b| ≤ K) {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ < 1)
    (σ₁ σ₁' σ₂ : Strategy) (h : Hist)
    (hOS : ∀ k : Hist, oneShotGainRow u δ σ₁ σ₂ k (σ₁' k) ≤ 0) (n : ℕ) :
    gainRow u δ σ₁ σ₁' σ₂ h
      ≤ δ ^ n * gainRow u δ σ₁ σ₁' σ₂ (orbitAux σ₁' σ₂ n h) := by
  induction n generalizing h with
  | zero => simp [orbitAux]
  | succ n ih =>
    have hb := gainRow_le_step u hK h0 h1 σ₁ σ₁' σ₂ h (hOS h)
    have hr := ih (h ++ [(σ₁' h, σ₂ h)])
    have hm := mul_le_mul_of_nonneg_left hr h0
    have hp : δ * (δ ^ n * gainRow u δ σ₁ σ₁' σ₂
        (orbitAux σ₁' σ₂ n (h ++ [(σ₁' h, σ₂ h)])))
        = δ ^ (n + 1) * gainRow u δ σ₁ σ₁' σ₂ (orbitAux σ₁' σ₂ (n + 1) h) := by
      rw [orbitAux, pow_succ]
      ring
    linarith [hb, hm, hp.le, hp.ge]

/-- **Itération du gain, joueur de colonne.** -/
lemma gainCol_le_iter (u : PDAction → PDAction → ℝ) {K : ℝ}
    (hK : ∀ a b, |u a b| ≤ K) {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ < 1)
    (σ₁ σ₂ σ₂' : Strategy) (h : Hist)
    (hOS : ∀ k : Hist, oneShotGainCol u δ σ₁ σ₂ k (σ₂' k) ≤ 0) (n : ℕ) :
    gainCol u δ σ₁ σ₂ σ₂' h
      ≤ δ ^ n * gainCol u δ σ₁ σ₂ σ₂' (orbitAux σ₁ σ₂' n h) := by
  induction n generalizing h with
  | zero => simp [orbitAux]
  | succ n ih =>
    have hb := gainCol_le_step u hK h0 h1 σ₁ σ₂ σ₂' h (hOS h)
    have hr := ih (h ++ [(σ₁ h, σ₂' h)])
    have hm := mul_le_mul_of_nonneg_left hr h0
    have hp : δ * (δ ^ n * gainCol u δ σ₁ σ₂ σ₂'
        (orbitAux σ₁ σ₂' n (h ++ [(σ₁ h, σ₂' h)])))
        = δ ^ (n + 1) * gainCol u δ σ₁ σ₂ σ₂' (orbitAux σ₁ σ₂' (n + 1) h) := by
      rw [orbitAux, pow_succ]
      ring
    linarith [hb, hm, hp.le, hp.ge]

/-- Un paiement actualisé est majoré par `K/(1−δ)`, une fois (H1) acquise. -/
lemma contPayoff_le_bound (u : PDAction → PDAction → ℝ) {K : ℝ}
    (hK : ∀ a b, |u a b| ≤ K) {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ < 1)
    (σ₁ σ₂ : Strategy) (h : Hist) :
    contPayoff u δ σ₁ σ₂ h ≤ K / (1 - δ) := by
  have hle : contPayoff u δ σ₁ σ₂ h ≤ |contPayoff u δ σ₁ σ₂ h| := le_abs_self _
  have habs := abs_contPayoff_le u hK h0 h1 σ₁ σ₂ h
  linarith

/-- Le pendant inférieur : `−(K/(1−δ))` minore tout paiement actualisé. Les
    deux côtés sont nécessaires pour borner une **différence** de paiements. -/
lemma neg_contPayoff_le_bound (u : PDAction → PDAction → ℝ) {K : ℝ}
    (hK : ∀ a b, |u a b| ≤ K) {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ < 1)
    (σ₁ σ₂ : Strategy) (h : Hist) :
    -(K / (1 - δ)) ≤ contPayoff u δ σ₁ σ₂ h := by
  have hle : -|contPayoff u δ σ₁ σ₂ h| ≤ contPayoff u δ σ₁ σ₂ h := neg_abs_le _
  have habs := abs_contPayoff_le u hK h0 h1 σ₁ σ₂ h
  linarith

/-! ## Conditions de déviation unique et ESPS -/

/-- Aucune déviation ponctuelle de ligne n'est profitable, **à toute histoire** —
    y compris hors du chemin d'équilibre. -/
def NoProfitableOneShotRow (u : PDAction → PDAction → ℝ) (δ : ℝ)
    (σ₁ σ₂ : Strategy) : Prop :=
  ∀ (h : Hist) (a : PDAction),
    contPayoff u δ (oneShot σ₁ h a) σ₂ h ≤ contPayoff u δ σ₁ σ₂ h

/-- Aucune déviation ponctuelle de colonne n'est profitable. -/
def NoProfitableOneShotCol (u : PDAction → PDAction → ℝ) (δ : ℝ)
    (σ₁ σ₂ : Strategy) : Prop :=
  ∀ (h : Hist) (b : PDAction),
    contPayoff u δ σ₁ (oneShot σ₂ h b) h ≤ contPayoff u δ σ₁ σ₂ h

/-- Condition de déviation unique. -/
def NoProfitableOneShot (u₁ u₂ : PDAction → PDAction → ℝ) (δ : ℝ)
    (σ₁ σ₂ : Strategy) : Prop :=
  NoProfitableOneShotRow u₁ δ σ₁ σ₂ ∧ NoProfitableOneShotCol u₂ δ σ₁ σ₂

/-- Équilibre parfait en sous-jeux : à toute histoire, aucun joueur ne gagne à
    changer de stratégie, l'adversaire restant fixé. -/
def IsSPE (u₁ u₂ : PDAction → PDAction → ℝ) (δ : ℝ) (σ₁ σ₂ : Strategy) : Prop :=
  (∀ (h : Hist) (σ₁' : Strategy),
      contPayoff u₁ δ σ₁' σ₂ h ≤ contPayoff u₁ δ σ₁ σ₂ h) ∧
  (∀ (h : Hist) (σ₂' : Strategy),
      contPayoff u₂ δ σ₁ σ₂' h ≤ contPayoff u₂ δ σ₁ σ₂ h)

/-- Non-profitabilité d'une déviation ponctuelle de ligne ⟺ gain du premier
    coup négatif. -/
lemma oneShotRow_le_iff (u : PDAction → PDAction → ℝ) {K : ℝ}
    (hK : ∀ a b, |u a b| ≤ K) {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ < 1)
    (σ₁ σ₂ : Strategy) (h : Hist) (a : PDAction) :
    contPayoff u δ (oneShot σ₁ h a) σ₂ h ≤ contPayoff u δ σ₁ σ₂ h
      ↔ oneShotGainRow u δ σ₁ σ₂ h a ≤ 0 := by
  rw [contPayoff_oneShot_row_eq u hK h0 h1 σ₁ σ₂ h a]
  constructor <;> intro hh <;> linarith

/-- Non-profitabilité d'une déviation ponctuelle de colonne ⟺ gain négatif. -/
lemma oneShotCol_le_iff (u : PDAction → PDAction → ℝ) {K : ℝ}
    (hK : ∀ a b, |u a b| ≤ K) {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ < 1)
    (σ₁ σ₂ : Strategy) (h : Hist) (b : PDAction) :
    contPayoff u δ σ₁ (oneShot σ₂ h b) h ≤ contPayoff u δ σ₁ σ₂ h
      ↔ oneShotGainCol u δ σ₁ σ₂ h b ≤ 0 := by
  rw [contPayoff_oneShot_col_eq u hK h0 h1 σ₁ σ₂ h b]
  constructor <;> intro hh <;> linarith

/-- **Principe de déviation unique.** Si aucune déviation d'un seul coup n'est
    profitable à aucune histoire, le profil est un équilibre parfait en
    sous-jeux — sous (H1) `∀ a b, |uᵢ a b| ≤ Kᵢ` et (H2) `δ < 1`.

    Argument : `G(h) ≤ δ·G(h')` où `h'` suit le premier coup déviant
    (`gainRow_le_step`), donc `G(h) ≤ δⁿ·G(hₙ)` le long de l'orbite de
    déviation ; or `G(hₙ) ≤ 2K/(1−δ)` par (H1), et `δⁿ → 0` par (H2), donc
    `G(h) ≤ 0`. -/
theorem oneShotDeviationPrinciple (u₁ u₂ : PDAction → PDAction → ℝ) {K₁ K₂ : ℝ}
    (hK₁ : ∀ a b, |u₁ a b| ≤ K₁) (hK₂ : ∀ a b, |u₂ a b| ≤ K₂)
    {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ < 1) (σ₁ σ₂ : Strategy)
    (hNE : NoProfitableOneShot u₁ u₂ δ σ₁ σ₂) : IsSPE u₁ u₂ δ σ₁ σ₂ := by
  obtain ⟨hRow, hCol⟩ := hNE
  have hK₁0 : 0 ≤ K₁ := le_trans (abs_nonneg _) (hK₁ cooperate cooperate)
  have hK₂0 : 0 ≤ K₂ := le_trans (abs_nonneg _) (hK₂ cooperate cooperate)
  have h1pos : 0 < 1 - δ := by linarith
  constructor
  · intro h σ₁'
    have hOS : ∀ k : Hist, oneShotGainRow u₁ δ σ₁ σ₂ k (σ₁' k) ≤ 0 :=
      fun k => (oneShotRow_le_iff u₁ hK₁ h0 h1 σ₁ σ₂ k (σ₁' k)).1
        (hRow k (σ₁' k))
    have hB : 0 ≤ 2 * (K₁ / (1 - δ)) := by
      have hd : 0 ≤ K₁ / (1 - δ) := div_nonneg hK₁0 h1pos.le
      linarith
    have hforall : ∀ k : ℕ,
        gainRow u₁ δ σ₁ σ₁' σ₂ h ≤ δ ^ k * (2 * (K₁ / (1 - δ))) := by
      intro k
      have hi := gainRow_le_iter u₁ hK₁ h0 h1 σ₁ σ₁' σ₂ h hOS k
      have ha := contPayoff_le_bound u₁ hK₁ h0 h1 σ₁' σ₂ (orbitAux σ₁' σ₂ k h)
      have hb := neg_contPayoff_le_bound u₁ hK₁ h0 h1 σ₁ σ₂ (orbitAux σ₁' σ₂ k h)
      have hgr : gainRow u₁ δ σ₁ σ₁' σ₂ (orbitAux σ₁' σ₂ k h)
          ≤ 2 * (K₁ / (1 - δ)) := by
        unfold gainRow
        linarith
      have h3 : δ ^ k * gainRow u₁ δ σ₁ σ₁' σ₂ (orbitAux σ₁' σ₂ k h)
          ≤ δ ^ k * (2 * (K₁ / (1 - δ))) :=
        mul_le_mul_of_nonneg_left hgr (pow_nonneg h0 k)
      linarith
    have hz := le_zero_of_forall_geometric_bound h0 h1 hB hforall
    unfold gainRow at hz
    linarith
  · intro h σ₂'
    have hOS : ∀ k : Hist, oneShotGainCol u₂ δ σ₁ σ₂ k (σ₂' k) ≤ 0 :=
      fun k => (oneShotCol_le_iff u₂ hK₂ h0 h1 σ₁ σ₂ k (σ₂' k)).1
        (hCol k (σ₂' k))
    have hB : 0 ≤ 2 * (K₂ / (1 - δ)) := by
      have hd : 0 ≤ K₂ / (1 - δ) := div_nonneg hK₂0 h1pos.le
      linarith
    have hforall : ∀ k : ℕ,
        gainCol u₂ δ σ₁ σ₂ σ₂' h ≤ δ ^ k * (2 * (K₂ / (1 - δ))) := by
      intro k
      have hi := gainCol_le_iter u₂ hK₂ h0 h1 σ₁ σ₂ σ₂' h hOS k
      have ha := contPayoff_le_bound u₂ hK₂ h0 h1 σ₁ σ₂' (orbitAux σ₁ σ₂' k h)
      have hb := neg_contPayoff_le_bound u₂ hK₂ h0 h1 σ₁ σ₂ (orbitAux σ₁ σ₂' k h)
      have hgr : gainCol u₂ δ σ₁ σ₂ σ₂' (orbitAux σ₁ σ₂' k h)
          ≤ 2 * (K₂ / (1 - δ)) := by
        unfold gainCol
        linarith
      have h3 : δ ^ k * gainCol u₂ δ σ₁ σ₂ σ₂' (orbitAux σ₁ σ₂' k h)
          ≤ δ ^ k * (2 * (K₂ / (1 - δ))) :=
        mul_le_mul_of_nonneg_left hgr (pow_nonneg h0 k)
      linarith
    have hz := le_zero_of_forall_geometric_bound h0 h1 hB hforall
    unfold gainCol at hz
    linarith

/-! ## C. Grim trigger comme équilibre parfait en sous-jeux

Les sections A et B ont établi le principe de déviation unique pour un jeu de
stage abstrait. Cette section l'instancie sur le Dilemme du Prisonnier : le
profil « grim trigger contre grim trigger » est un ESPS **ssi**
`δ ≥ (T − R)/(T − P)`.

L'organe de la preuve est un unique booléen d'histoire, `anyDefect` : une
histoire est « vierge » si aucun des deux joueurs n'y a jamais dévié. Grim
coopère sur une histoire vierge et punit sinon — donc ce booléen est
**invariant** le long de l'orbite grim/grim, et le paiement actualisé du profil
n'a que deux valeurs possibles, `R/(1−δ)` et `P/(1−δ)`. C'est ce qui rend
l'analyse de la déviation ponctuelle calculable. -/

/-- (H1) sur le Dilemme du Prisonnier : les quatre paiements de stage sont
    uniformément bornés par la somme de leurs valeurs absolues. Sur un jeu
    fini c'est automatique — et c'est bien une hypothèse sur le jeu de stage,
    pas une tautologie : le principe de déviation unique l'exige nommément. -/
lemma stagePayoff_abs_le (g : PrisonersDilemma) (a b : PDAction) :
    |stagePayoff g a b| ≤ |g.R| + |g.T| + |g.S| + |g.P| := by
  cases a <;> cases b <;>
    simp only [stagePayoff] <;>
    linarith [abs_nonneg g.R, abs_nonneg g.T, abs_nonneg g.S, abs_nonneg g.P]

/-- Le paiement du joueur de colonne, vu comme une fonction des actions : c'est
    le paiement de ligne, arguments échangés. Le nommer donne une clé de
    réécriture stable — une lambda anonyme ne s'unifie pas d'un but à l'autre. -/
def colPayoff (g : PrisonersDilemma) : PDAction → PDAction → ℝ :=
  fun a b => stagePayoff g b a

/-- (H1) pour `colPayoff`, qui est le paiement du joueur de colonne. -/
lemma colPayoff_abs_le (g : PrisonersDilemma) (a b : PDAction) :
    |colPayoff g a b| ≤ |g.R| + |g.T| + |g.S| + |g.P| :=
  stagePayoff_abs_le g b a

/-! ### L'instrument : le booléen « une défection a-t-elle eu lieu ? » -/

/-- L'histoire contient-elle déjà une défection, d'un côté ou de l'autre ? -/
def anyDefect (h : Hist) : Bool :=
  h.any (fun p => decide (p.1 = defect ∨ p.2 = defect))

/-- Stratégie grim trigger : coopérer tant que l'histoire est vierge, punir
    pour toujours dès qu'une défection y figure. -/
def grimStrategy : Strategy := fun h => if anyDefect h then defect else cooperate

/-- Stratégie « dévier à chaque coup », utilisée pour exhiber une déviation
    profitable quand le seuil n'est pas atteint. -/
def deviateAlways : Strategy := fun _ => defect

@[simp] lemma anyDefect_nil : anyDefect ([] : Hist) = false := by
  simp [anyDefect]

lemma anyDefect_append (h : Hist) (p : PDAction × PDAction) :
    anyDefect (h ++ [p]) =
      (anyDefect h || decide (p.1 = defect ∨ p.2 = defect)) := by
  simp [anyDefect, List.any_append]

lemma anyDefect_append_coop (h : Hist) :
    anyDefect (h ++ [(cooperate, cooperate)]) = anyDefect h := by
  rw [anyDefect_append]
  simp

lemma anyDefect_append_of_fst_defect (h : Hist) (b : PDAction) :
    anyDefect (h ++ [(defect, b)]) = true := by
  rw [anyDefect_append]
  cases hd : anyDefect h <;> cases b <;> simp

lemma anyDefect_append_of_snd_defect (h : Hist) (a : PDAction) :
    anyDefect (h ++ [(a, defect)]) = true := by
  rw [anyDefect_append]
  cases hd : anyDefect h <;> cases a <;> simp

lemma grimStrategy_of_no_defect (h : Hist) (hd : anyDefect h = false) :
    grimStrategy h = cooperate := by
  simp [grimStrategy, hd]

lemma grimStrategy_of_defect (h : Hist) (hd : anyDefect h = true) :
    grimStrategy h = defect := by
  simp [grimStrategy, hd]

/-- Le booléen est **invariant** le long de l'orbite grim-contre-grim : les
    deux joueurs y jouent toujours la même action, donc aucun n'y ajoute une
    défection que l'autre n'ajoute pas. -/
lemma anyDefect_orbit_grim (h : Hist) (n : ℕ) :
    anyDefect (orbitAux grimStrategy grimStrategy n h) = anyDefect h := by
  induction n generalizing h with
  | zero => simp [orbitAux]
  | succ n ih =>
      rw [orbitAux, ih]
      cases hd : anyDefect h with
      | true =>
          rw [grimStrategy_of_defect h hd]
          exact anyDefect_append_of_snd_defect h defect
      | false =>
          rw [grimStrategy_of_no_defect h hd, anyDefect_append_coop]
          exact hd

/-- Sous une histoire déjà souillée, une déviation perpétuelle reste dans la
    zone de punition : le booléen y reste vrai à jamais. -/
lemma anyDefect_orbit_deviate (h : Hist) (hd : anyDefect h = true) (n : ℕ) :
    anyDefect (orbitAux deviateAlways grimStrategy n h) = true := by
  induction n generalizing h with
  | zero => simpa [orbitAux] using hd
  | succ n ih =>
      rw [orbitAux]
      exact ih (h ++ [(deviateAlways h, grimStrategy h)])
        (anyDefect_append_of_fst_defect h (grimStrategy h))

/-! ### Paiements actualisés du profil et de la déviation -/

/-- Le paiement du joueur de colonne coïncide avec celui du joueur de ligne sur
    l'orbite grim/grim : les deux composantes de l'action y sont le **même**
    terme `grimStrategy (orbitAux …)`, donc l'échange des arguments est
    invisible définitionnellement. -/
lemma contPayoff_col_grim (g : PrisonersDilemma) (δ : ℝ) (h : Hist) :
    contPayoff (colPayoff g) δ grimStrategy grimStrategy h
      = contPayoff (stagePayoff g) δ grimStrategy grimStrategy h := by
  unfold contPayoff colPayoff actionAt
  exact tsum_congr (fun n => rfl)

/-- Paiement actualisé d'un profil dont le paiement de stage est constant. -/
lemma contPayoff_of_const_orbit (u : PDAction → PDAction → ℝ) {δ : ℝ}
    (h0 : 0 ≤ δ) (h1 : δ < 1) (σ₁ σ₂ : Strategy) (h : Hist) (c : ℝ)
    (hc : ∀ n : ℕ, u (actionAt σ₁ σ₂ h n).1 (actionAt σ₁ σ₂ h n).2 = c) :
    contPayoff u δ σ₁ σ₂ h = c * (1 - δ)⁻¹ := by
  unfold contPayoff
  calc ∑' n : ℕ, δ ^ n * u (actionAt σ₁ σ₂ h n).1 (actionAt σ₁ σ₂ h n).2
      = ∑' n : ℕ, δ ^ n * c := tsum_congr (fun n => by rw [hc n])
    _ = c * ∑' n : ℕ, δ ^ n := by
          rw [← tsum_mul_left]
          exact tsum_congr (fun n => by ring)
    _ = c * (1 - δ)⁻¹ := by rw [geom_sum h0 h1]

lemma actionAt_grim_of_no_defect (h : Hist) (hd : anyDefect h = false) (n : ℕ) :
    actionAt grimStrategy grimStrategy h n = (cooperate, cooperate) := by
  unfold actionAt
  have h1 : anyDefect (orbitAux grimStrategy grimStrategy n h) = false := by
    rw [anyDefect_orbit_grim, hd]
  rw [grimStrategy_of_no_defect _ h1]

lemma actionAt_grim_of_defect (h : Hist) (hd : anyDefect h = true) (n : ℕ) :
    actionAt grimStrategy grimStrategy h n = (defect, defect) := by
  unfold actionAt
  have h1 : anyDefect (orbitAux grimStrategy grimStrategy n h) = true := by
    rw [anyDefect_orbit_grim, hd]
  rw [grimStrategy_of_defect _ h1]

lemma actionAt_deviate_of_defect (h : Hist) (hd : anyDefect h = true) (n : ℕ) :
    actionAt deviateAlways grimStrategy h n = (defect, defect) := by
  unfold actionAt
  have h1 := anyDefect_orbit_deviate h hd n
  rw [grimStrategy_of_defect _ h1]
  rfl

/-- Sur une histoire vierge, le profil grim/grim vaut la coopération
    perpétuelle : `R/(1−δ)`. -/
lemma contPayoff_grim_of_no_defect (g : PrisonersDilemma) {δ : ℝ}
    (h0 : 0 ≤ δ) (h1 : δ < 1) (h : Hist) (hd : anyDefect h = false) :
    contPayoff (stagePayoff g) δ grimStrategy grimStrategy h = coopValue g.R δ := by
  have hc : ∀ n : ℕ,
      (stagePayoff g) (actionAt grimStrategy grimStrategy h n).1
        (actionAt grimStrategy grimStrategy h n).2 = g.R := by
    intro n
    rw [actionAt_grim_of_no_defect h hd n]
    rfl
  rw [contPayoff_of_const_orbit (stagePayoff g) h0 h1 grimStrategy grimStrategy h g.R hc]
  unfold coopValue
  rw [div_eq_mul_inv]

/-- Sur une histoire souillée, le profil grim/grim vaut la punition
    perpétuelle : `P/(1−δ)`. -/
lemma contPayoff_grim_of_defect (g : PrisonersDilemma) {δ : ℝ}
    (h0 : 0 ≤ δ) (h1 : δ < 1) (h : Hist) (hd : anyDefect h = true) :
    contPayoff (stagePayoff g) δ grimStrategy grimStrategy h = coopValue g.P δ := by
  have hc : ∀ n : ℕ,
      (stagePayoff g) (actionAt grimStrategy grimStrategy h n).1
        (actionAt grimStrategy grimStrategy h n).2 = g.P := by
    intro n
    rw [actionAt_grim_of_defect h hd n]
    rfl
  rw [contPayoff_of_const_orbit (stagePayoff g) h0 h1 grimStrategy grimStrategy h g.P hc]
  unfold coopValue
  rw [div_eq_mul_inv]

/-- Un déviateur perpétuel face à grim encaisse la punition perpétuelle dès que
    l'histoire est souillée. -/
lemma contPayoff_deviate_of_defect (g : PrisonersDilemma) {δ : ℝ}
    (h0 : 0 ≤ δ) (h1 : δ < 1) (h : Hist) (hd : anyDefect h = true) :
    contPayoff (stagePayoff g) δ deviateAlways grimStrategy h = coopValue g.P δ := by
  have hc : ∀ n : ℕ,
      (stagePayoff g) (actionAt deviateAlways grimStrategy h n).1
        (actionAt deviateAlways grimStrategy h n).2 = g.P := by
    intro n
    rw [actionAt_deviate_of_defect h hd n]
    rfl
  rw [contPayoff_of_const_orbit (stagePayoff g) h0 h1 deviateAlways grimStrategy h g.P hc]
  unfold coopValue
  rw [div_eq_mul_inv]

/-- Le paiement d'une déviation perpétuelle depuis l'histoire vide vaut
    exactement `deviateValue T P δ` : `T` au premier coup, puis `P` à jamais. -/
lemma contPayoff_deviate_root (g : PrisonersDilemma) {δ : ℝ}
    (h0 : 0 ≤ δ) (h1 : δ < 1) :
    contPayoff (stagePayoff g) δ deviateAlways grimStrategy ([] : Hist)
      = deviateValue g.T g.P δ := by
  have hstep := contPayoff_cons (stagePayoff g) (stagePayoff_abs_le g) h0 h1
    deviateAlways grimStrategy ([] : Hist)
  have hgr : grimStrategy ([] : Hist) = cooperate := grimStrategy_of_no_defect _ anyDefect_nil
  have htail : contPayoff (stagePayoff g) δ deviateAlways grimStrategy
      (([] : Hist) ++ [(deviateAlways ([] : Hist), grimStrategy ([] : Hist))])
      = coopValue g.P δ := by
    refine contPayoff_deviate_of_defect g h0 h1 _ ?_
    rw [hgr]
    exact anyDefect_append_of_fst_defect [] cooperate
  rw [hstep, htail, hgr]
  simp only [deviateAlways, stagePayoff]
  unfold coopValue deviateValue
  ring

/-! ### L'algèbre du gain d'une déviation ponctuelle

Deux identités réelles suffisent : `δ·x/(1−δ) − x/(1−δ) = −x`, et le seuil
`coopValue R δ ≥ deviateValue T P δ`. -/

private lemma gain_atom (x δ : ℝ) (h1 : δ < 1) :
    δ * (x / (1 - δ)) - x / (1 - δ) = -x := by
  have h : (1 : ℝ) - δ ≠ 0 := by intro hh; linarith
  field_simp
  ring

/-- **La déviation ponctuelle de ligne n'est jamais profitable** dès que le
    seuil est atteint. Quatre cas, un par couple `(histoire, action)` :
    histoire vierge ou souillée, action coopérer ou dévier.

    - vierge + coopérer : gain `0` (on rejoue le profil) ;
    - vierge + dévier   : gain `deviateValue − coopValue ≤ 0`, c'est le seuil ;
    - souillée + coopérer : gain `S − P < 0` ;
    - souillée + dévier : gain `0` (la punition est déjà en place). -/
lemma oneShotGainRow_grim_nonpos (g : PrisonersDilemma) {δ : ℝ}
    (h0 : 0 ≤ δ) (h1 : δ < 1)
    (hthr : coopValue g.R δ ≥ deviateValue g.T g.P δ) (h : Hist) (a : PDAction) :
    oneShotGainRow (stagePayoff g) δ grimStrategy grimStrategy h a ≤ 0 := by
  unfold oneShotGainRow
  have hδp : (0 : ℝ) < 1 - δ := by linarith
  cases hd : anyDefect h with
  | false =>
      have hg : grimStrategy h = cooperate := grimStrategy_of_no_defect h hd
      rw [hg, contPayoff_grim_of_no_defect g h0 h1 h hd]
      cases a with
      | cooperate =>
          have hd2 : anyDefect (h ++ [(cooperate, cooperate)]) = false := by
            rw [anyDefect_append_coop, hd]
          rw [contPayoff_grim_of_no_defect g h0 h1 _ hd2]
          simp only [stagePayoff]
          have hkey := gain_atom g.R δ h1
          unfold coopValue
          linarith
      | defect =>
          have hd2 : anyDefect (h ++ [(defect, cooperate)]) = true :=
            anyDefect_append_of_fst_defect h cooperate
          rw [contPayoff_grim_of_defect g h0 h1 _ hd2]
          simp only [stagePayoff]
          -- Normaliser le seuil sur la même forme que le but : `δ * x / (1-δ)`
          -- et `δ * (x / (1-δ))` sont égaux mais syntaxiquement distincts, et
          -- `linarith` raisonne sur les atomes, pas sur les formes.
          have hthr' : g.T + δ * (g.P / (1 - δ)) ≤ g.R / (1 - δ) := by
            unfold coopValue deviateValue at hthr
            rw [mul_div_assoc] at hthr
            linarith
          unfold coopValue
          linarith
  | true =>
      have hg : grimStrategy h = defect := grimStrategy_of_defect h hd
      rw [hg, contPayoff_grim_of_defect g h0 h1 h hd]
      cases a with
      | cooperate =>
          have hd2 : anyDefect (h ++ [(cooperate, defect)]) = true :=
            anyDefect_append_of_snd_defect h cooperate
          rw [contPayoff_grim_of_defect g h0 h1 _ hd2]
          simp only [stagePayoff]
          have hkey := gain_atom g.P δ h1
          unfold coopValue
          linarith [g.hPS]
      | defect =>
          have hd2 : anyDefect (h ++ [(defect, defect)]) = true :=
            anyDefect_append_of_snd_defect h defect
          rw [contPayoff_grim_of_defect g h0 h1 _ hd2]
          simp only [stagePayoff]
          have hkey := gain_atom g.P δ h1
          unfold coopValue
          linarith

/-- Le paiement du profil grim/grim ne dépend de l'histoire que par son booléen
    de défection : deux histoires de même booléen donnent le même paiement. -/
lemma contPayoff_grim_congr_anyDefect (g : PrisonersDilemma) {δ : ℝ}
    (h0 : 0 ≤ δ) (h1 : δ < 1) {h₁ h₂ : Hist}
    (hd : anyDefect h₁ = anyDefect h₂) :
    contPayoff (stagePayoff g) δ grimStrategy grimStrategy h₁
      = contPayoff (stagePayoff g) δ grimStrategy grimStrategy h₂ := by
  cases ha : anyDefect h₁ with
  | false =>
      rw [contPayoff_grim_of_no_defect g h0 h1 h₁ ha,
        contPayoff_grim_of_no_defect g h0 h1 h₂ (by rw [← hd]; exact ha)]
  | true =>
      rw [contPayoff_grim_of_defect g h0 h1 h₁ ha,
        contPayoff_grim_of_defect g h0 h1 h₂ (by rw [← hd]; exact ha)]

/-- Le gain de la déviation ponctuelle de colonne coïncide avec celui de la
    déviation de ligne : la seule différence est l'ordre du couple ajouté à
    l'histoire, et le paiement ne le voit pas (il ne dépend que de `anyDefect`). -/
lemma oneShotGainCol_grim_eq_row (g : PrisonersDilemma) {δ : ℝ}
    (h0 : 0 ≤ δ) (h1 : δ < 1) (h : Hist) (b : PDAction) :
    oneShotGainCol (colPayoff g) δ grimStrategy grimStrategy h b
      = oneShotGainRow (stagePayoff g) δ grimStrategy grimStrategy h b := by
  unfold oneShotGainCol oneShotGainRow
  rw [contPayoff_col_grim g δ, contPayoff_col_grim g δ]
  simp only [colPayoff]
  have hord : anyDefect (h ++ [(grimStrategy h, b)]) = anyDefect (h ++ [(b, grimStrategy h)]) := by
    rw [anyDefect_append, anyDefect_append]
    by_cases hx : grimStrategy h = defect <;> by_cases hb : b = defect <;> simp [hx, hb]
  rw [contPayoff_grim_congr_anyDefect g h0 h1 hord]

/-- Les deux joueurs du Dilemme du Prisonnier ont la même stratégie grim, donc
    le résultat de ligne vaut aussi pour la colonne. -/
lemma oneShotGainCol_grim_nonpos (g : PrisonersDilemma) {δ : ℝ}
    (h0 : 0 ≤ δ) (h1 : δ < 1)
    (hthr : coopValue g.R δ ≥ deviateValue g.T g.P δ) (h : Hist) (b : PDAction) :
    oneShotGainCol (colPayoff g) δ grimStrategy grimStrategy h b ≤ 0 := by
  rw [oneShotGainCol_grim_eq_row g h0 h1 h b]
  exact oneShotGainRow_grim_nonpos g h0 h1 hthr h b

/-- Aucune déviation ponctuelle n'est profitable pour aucun des deux joueurs. -/
lemma noProfitableOneShot_grim (g : PrisonersDilemma) {δ : ℝ}
    (h0 : 0 ≤ δ) (h1 : δ < 1)
    (hthr : coopValue g.R δ ≥ deviateValue g.T g.P δ) :
    NoProfitableOneShot (stagePayoff g) (colPayoff g) δ
      grimStrategy grimStrategy := by
  constructor
  · intro h a
    rw [contPayoff_oneShot_row_eq (stagePayoff g) (stagePayoff_abs_le g) h0 h1
      grimStrategy grimStrategy h a]
    have hg := oneShotGainRow_grim_nonpos g h0 h1 hthr h a
    linarith
  · intro h b
    rw [contPayoff_oneShot_col_eq (colPayoff g)
      (colPayoff_abs_le g) h0 h1 grimStrategy grimStrategy h b]
    have hg := oneShotGainCol_grim_nonpos g h0 h1 hthr h b
    linarith

/-! ### Les deux sens de l'équivalence -/

/-- **Sens direct.** Au-dessus du seuil, le profil grim trigger est un
    équilibre parfait en sous-jeux — conséquence du principe de déviation
    unique, avec (H1) `stagePayoff_abs_le` et (H2) `δ < 1`. -/
theorem grim_isSPE_of_threshold (g : PrisonersDilemma) {δ : ℝ}
    (h0 : 0 ≤ δ) (h1 : δ < 1)
    (hthr : δ ≥ (g.T - g.R) / (g.T - g.P)) :
    IsSPE (stagePayoff g) (colPayoff g) δ grimStrategy grimStrategy :=
  oneShotDeviationPrinciple (stagePayoff g) (colPayoff g)
    (stagePayoff_abs_le g) (colPayoff_abs_le g) h0 h1 grimStrategy grimStrategy
    (noProfitableOneShot_grim g h0 h1 ((coop_ge_deviate_iff g h0 h1).mpr hthr))

/-- **Sens réciproque.** Sous le seuil, le profil n'est pas un ESPS : la
    stratégie « dévier à chaque coup » bat la coopération perpétuelle au
    sous-jeu initial. -/
theorem threshold_of_grim_isSPE (g : PrisonersDilemma) {δ : ℝ}
    (h0 : 0 ≤ δ) (h1 : δ < 1)
    (hspe : IsSPE (stagePayoff g) (colPayoff g) δ grimStrategy grimStrategy) :
    δ ≥ (g.T - g.R) / (g.T - g.P) := by
  obtain ⟨hrow, _⟩ := hspe
  have hdev := hrow ([] : Hist) deviateAlways
  rw [contPayoff_deviate_root g h0 h1] at hdev
  have hbase : contPayoff (stagePayoff g) δ grimStrategy grimStrategy ([] : Hist)
      = coopValue g.R δ :=
    contPayoff_grim_of_no_defect g h0 h1 [] anyDefect_nil
  rw [hbase] at hdev
  exact (coop_ge_deviate_iff g h0 h1).mp hdev

/-- **Théorème principal.** Le profil grim trigger du Dilemme du Prisonnier
    actualisé est un équilibre parfait en sous-jeux **ssi** le facteur
    d'actualisation atteint le seuil critique `(T − R)/(T − P)`.

    Les deux hypothèses de la section A sont ici nommées explicitement : (H1)
    est `stagePayoff_abs_le`, (H2) est `h1 : δ < 1`. `GrimTrigger.lean`
    énonçait la condition incitative ; ce théorème en fait un énoncé
    d'équilibre, quantifié sur les historiques et les profils. -/
theorem grim_isSPE_iff (g : PrisonersDilemma) {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ < 1) :
    IsSPE (stagePayoff g) (colPayoff g) δ grimStrategy grimStrategy ↔
      δ ≥ (g.T - g.R) / (g.T - g.P) :=
  ⟨threshold_of_grim_isSPE g h0 h1, grim_isSPE_of_threshold g h0 h1⟩

end RepeatedGames