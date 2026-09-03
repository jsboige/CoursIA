/-
  Parité des chemins de swaps — une obstruction non bornée
  ========================================================

  Compagnon de `Swaps/Basic.lean` (grain #12222) et du §6 de l'EPIC
  #12205, volet « témoin d'impossibilité ».

  Ce que les certificats existants réfutent, et ce qu'ils laissent
  ouvert :

  - `aucun_chemin_court` (dans `Basic.lean`) réfute **7 chemins** — le
    chemin vide et les six chemins d'un pas — par énumération
    décidable. Sa portée est exactement la taille de l'énumération.
  - Le notebook `GameTheory-24b` certifie l'impossibilité **relative à
    un budget** : `IMPOSSIBLE` dès que `d_ligne + d_colonne > k_max`.
    Le graphe des chambres étant connexe (576 sommets, degré 6,
    diamètre 12), c'est la seule lecture non vide — le notebook le dit
    lui-même : « au-delà de `k_max = 12`, tout est POSSIBLE par
    définition ».

  Aucun des deux ne dit rien des chemins de longueur **arbitraire**.
  C'est ce que ferme ce module, par un invariant plutôt que par un
  parcours : chaque générateur est une transposition d'un seul côté,
  donc bascule la parité jointe du nombre d'inversions. Par récurrence,
  la parité de la longueur d'un chemin est **déterminée par ses deux
  extrémités**. Dilemme et Chicken portant la même signature, tout
  chemin de longueur impaire entre eux est réfuté — une famille
  infinie (6 + 6³ + 6⁵ + … chemins), là où l'énumération plafonne à 7.

  Les deux obstructions sont complémentaires et aucune ne subsume
  l'autre : la distance réfute *tout* en dessous d'une borne mais exige
  de calculer la borne ; la parité ne réfute qu'une classe de longueurs,
  mais sans aucune borne.

  L'invariant n'est vrai que sur les tables **valides** (les 24 ordres
  stricts). Sur une liste quelconque il est faux : `[1, 1]` a zéro
  inversion, son image par le générateur `k = 1` est `[2, 2]`, qui en a
  zéro aussi — la parité ne bascule pas. Tout est donc relativisé à
  `ordresStricts`, ce qui garde l'ensemble décidable : les deux lemmes
  de base sont clos par `decide` sur 24 × 3 = 72 instances.

  Comme `Basic.lean`, ce module est volontairement SANS Mathlib.
-/

import Swaps.Basic

/-! ## 1. L'invariant : parité du nombre d'inversions -/

/-- Nombre d'inversions d'une liste de rangs : les paires de positions
`i < j` dont la valeur en `i` est strictement plus grande que celle en
`j`. Comptées tête par tête, sans tri. -/
def inversions : List Nat → Nat
  | [] => 0
  | v :: reste => (reste.filter (fun w => decide (w < v))).length + inversions reste

/-- Parité du nombre d'inversions d'une table. -/
def parite (t : Table) : Bool := inversions t % 2 == 1

/-- **Signature** d'un jeu : la parité jointe des deux tables. C'est
l'invariant transporté le long des chemins. -/
def signature (g : Jeu) : Bool := Bool.xor (parite g.1) (parite g.2)

/-! ## 2. L'univers valide : les 24 ordres stricts -/

/-- Les 24 tables valides — les permutations des rangs 1 à 4. -/
def ordresStricts : List Table :=
  [ [1, 2, 3, 4], [1, 2, 4, 3], [1, 3, 2, 4], [1, 3, 4, 2], [1, 4, 2, 3], [1, 4, 3, 2],
    [2, 1, 3, 4], [2, 1, 4, 3], [2, 3, 1, 4], [2, 3, 4, 1], [2, 4, 1, 3], [2, 4, 3, 1],
    [3, 1, 2, 4], [3, 1, 4, 2], [3, 2, 1, 4], [3, 2, 4, 1], [3, 4, 1, 2], [3, 4, 2, 1],
    [4, 1, 2, 3], [4, 1, 3, 2], [4, 2, 1, 3], [4, 2, 3, 1], [4, 3, 1, 2], [4, 3, 2, 1] ]

/-- Une table est-elle un ordre strict ? -/
def estOrdre (t : Table) : Bool := decide (t ∈ ordresStricts)

/-- Un jeu est-il valide — ses deux tables sont-elles des ordres stricts ? -/
def estJeu (g : Jeu) : Bool := estOrdre g.1 && estOrdre g.2

theorem dilemme_valide : estJeu dilemme = true := by decide

theorem chicken_valide : estJeu chicken = true := by decide

theorem cerf_valide : estJeu cerf = true := by decide

/-! ## 3. Le lemme de bascule -/

/-- Sur une table valide, un générateur adjacent **préserve la validité**
et **renverse la parité**. Les deux conclusions ensemble : c'est le seul
énoncé du module qui repose sur un calcul exhaustif (24 tables × 3
générateurs = 72 instances), et il est indépendant de la longueur des
chemins. -/
theorem bascule :
    ∀ t ∈ ordresStricts, ∀ k ∈ [1, 2, 3],
      estOrdre (swapAdj t k) = true ∧ parite (swapAdj t k) = !parite t := by decide

/-- La valeur de base d'une étape est 1, 2 ou 3. -/
theorem etape_k_valide (e : Etape) : e.k ∈ [1, 2, 3] := by cases e <;> decide

/-! ## 4. Transport le long d'un chemin -/

/-- Le passage d'une étape supplémentaire renverse la parité de la
longueur. Seul lemme arithmétique du module. -/
theorem parite_succ (n : Nat) :
    decide ((n + 1) % 2 = 1) = !decide (n % 2 = 1) := by
  have h : n % 2 = 0 ∨ n % 2 = 1 := by omega
  have hs : (n + 1) % 2 = (n % 2 + 1) % 2 := by omega
  rcases h with h | h <;> simp [hs, h]

/-- **Une étape bascule la signature**, et préserve la validité. -/
theorem signature_etape (g : Jeu) (hg : estJeu g = true) (e : Etape) :
    estJeu (appliqueEtape g e) = true ∧ signature (appliqueEtape g e) = !signature g := by
  have hg' : estOrdre g.1 = true ∧ estOrdre g.2 = true := by
    simpa [estJeu, Bool.and_eq_true] using hg
  have h1 : g.1 ∈ ordresStricts := of_decide_eq_true hg'.1
  have h2 : g.2 ∈ ordresStricts := of_decide_eq_true hg'.2
  have hk := etape_k_valide e
  cases he : e.ligne with
  | true =>
      have hb := bascule g.1 h1 e.k hk
      simp [appliqueEtape, he, estJeu, signature, hb.1, hb.2, hg'.2]
  | false =>
      have hb := bascule g.2 h2 e.k hk
      simp [appliqueEtape, he, estJeu, signature, hb.1, hb.2, hg'.1]

/-- **Transport** : le long d'un chemin quelconque, la validité se
conserve et la signature bascule exactement autant de fois que le chemin
a d'étapes. Récurrence sur le chemin — aucune borne sur sa longueur. -/
theorem signature_chemin :
    ∀ (p : List Etape) (g : Jeu), estJeu g = true →
      estJeu (applique g p) = true ∧
        signature (applique g p) = Bool.xor (signature g) (decide (p.length % 2 = 1)) := by
  intro p
  induction p with
  | nil => intro g hg; simpa [applique] using hg
  | cons e q ih =>
      intro g hg
      have hs := signature_etape g hg e
      have hq := ih (appliqueEtape g e) hs.1
      refine ⟨by simpa [applique] using hq.1, ?_⟩
      have : signature (applique g (e :: q))
          = Bool.xor (!signature g) (decide (q.length % 2 = 1)) := by
        simpa [applique, hs.2] using hq.2
      simp [this, List.length_cons, parite_succ]

/-! ## 5. Le théorème de parité et ses conséquences -/

/-- **La parité d'un chemin est déterminée par ses extrémités.** Énoncé
central : pour deux jeux valides quelconques, tout chemin de l'un à
l'autre a une longueur dont la parité est lue sur les signatures. Aucune
énumération, aucune borne. -/
theorem parite_determinee (g h : Jeu) (hg : estJeu g = true) (p : List Etape)
    (hp : applique g p = h) :
    decide (p.length % 2 = 1) = Bool.xor (signature g) (signature h) := by
  have hc := (signature_chemin p g hg).2
  rw [hp] at hc
  rw [hc]
  cases signature g <;> cases hd : decide (p.length % 2 = 1) <;> simp

/-- **Impossibilité non bornée, cas général** : deux jeux valides de
signatures **égales** ne sont reliés par aucun chemin de longueur
impaire — quelle que soit cette longueur. -/
theorem aucun_chemin_impair_si_signatures_egales (g h : Jeu) (hg : estJeu g = true)
    (hsig : signature g = signature h) (p : List Etape) (himpair : p.length % 2 = 1) :
    applique g p ≠ h := by
  intro hp
  have hd := parite_determinee g h hg p hp
  rw [hsig] at hd
  simp [himpair] at hd

/-- **Impossibilité non bornée, cas dual** : deux jeux valides de
signatures **différentes** ne sont reliés par aucun chemin de longueur
paire. -/
theorem aucun_chemin_pair_si_signatures_differentes (g h : Jeu) (hg : estJeu g = true)
    (hsig : signature g ≠ signature h) (p : List Etape) (hpair : p.length % 2 = 0) :
    applique g p ≠ h := by
  intro hp
  have hd := parite_determinee g h hg p hp
  have : ¬ (p.length % 2 = 1) := by omega
  rw [decide_eq_false this] at hd
  exact hsig (by cases hx : signature g <;> cases hy : signature h <;>
    simp [hx, hy] at hd ⊢)

/-! ## 6. Le témoin : Dilemme → Chicken -/

/-- Dilemme et Chicken portent la **même** signature. -/
theorem signatures_egales_dilemme_chicken : signature dilemme = signature chicken := by decide

/-- **Le témoin d'impossibilité non borné.** Aucun chemin de longueur
impaire ne relie le Dilemme à Chicken.

À comparer avec `aucun_chemin_court`, qui réfute **7** chemins (le vide
et les six d'un pas) : cet énoncé en réfute une **famille infinie** —
tous les chemins de longueur 1, 3, 5, … soit 6 + 6³ + 6⁵ + … chemins.
La différence n'est pas de degré mais de nature : l'un est une
énumération, l'autre un invariant. -/
theorem aucun_chemin_impair_dilemme_chicken (p : List Etape) (himpair : p.length % 2 = 1) :
    applique dilemme p ≠ chicken :=
  aucun_chemin_impair_si_signatures_egales dilemme chicken dilemme_valide
    signatures_egales_dilemme_chicken p himpair

/-- Corollaire de lecture directe : **tout** chemin du Dilemme à Chicken
est de longueur paire. -/
theorem chemin_dilemme_chicken_pair (p : List Etape) (hp : applique dilemme p = chicken) :
    p.length % 2 = 0 := by
  rcases (show p.length % 2 = 0 ∨ p.length % 2 = 1 by omega) with h | h
  · exact h
  · exact absurd hp (aucun_chemin_impair_dilemme_chicken p h)

/-- Le chemin certifié de `Basic.lean` est bien de longueur paire — la
parité n'entre pas en conflit avec le certificat d'arrivée, elle le
complète. -/
theorem coherence_certificat : cheminDilemmeChicken.length % 2 = 0 :=
  chemin_dilemme_chicken_pair cheminDilemmeChicken certificat_chemin

/-! ## 7. Un témoin du cas dual -/

/-- Un voisin immédiat du Dilemme : son image par le générateur R₁₂.
C'est un jeu valide, à distance impaire du Dilemme par construction. -/
def voisinR12 : Jeu := appliqueEtape dilemme .R12

theorem voisinR12_valide : estJeu voisinR12 = true := by decide

/-- Le Dilemme et son voisin R₁₂ portent des signatures **différentes**. -/
theorem signatures_differentes_voisin : signature dilemme ≠ signature voisinR12 := by decide

/-- **Témoin dual, non borné** : aucun chemin de longueur paire ne relie
le Dilemme à son voisin R₁₂ — y compris le chemin vide, et y compris
tous les allers-retours de longueur 2, 4, 6, … -/
theorem aucun_chemin_pair_voisin (p : List Etape) (hpair : p.length % 2 = 0) :
    applique dilemme p ≠ voisinR12 :=
  aucun_chemin_pair_si_signatures_differentes dilemme voisinR12 dilemme_valide
    signatures_differentes_voisin p hpair
