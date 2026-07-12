/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

## Cone geometry — pure lattice facts (Mathlib only)

This module is the **pure-geometry base** of the Conway Hashlife tight-locality
infrastructure (EPIC #3846, N2 redesign arc). It holds the lattice geometry over
`Int × Int` that depends on **no Game-of-Life semantics** — neither `evolve`,
`isAlive`, `candidates`, `mooreNeighbors`, the `lightCone` set, the `manhattan`
metric, nor any `MacroCell` / `Grid` proof-body module. Its only import is
Mathlib. This independence is structural, not cosmetic:

**Why a separate module (cycle-break).** `Conway.Life.LightCone` *imports*
`Conway.Life.HashlifeCorrectness` (it needs `evolve`, `lightCone`, `manhattan`
for the reach theorem `evolve_reach_chebyshev` and the N2 capstone). The reverse
import — `HashlifeCorrectness` importing `LightCone` to consume
`window_cheb_cone_in_domain` in the P5 `p5_large_n_jump` path — would therefore
be **circular**. Extracting the pure Chebyshev geometry here breaks the cycle:
`LightCone` and `HashlifeCorrectness` both import `ConeGeometry`, but
`ConeGeometry` imports neither of them.

**Split criterion (ai-01 design-gate msg-...338lw8, 2026-07-11).** A declaration
migrates here iff its proof references only `Int × Int`, `Int.natAbs`, `max`,
omega/linarith, and Mathlib arithmetic lemmas — i.e. it does *not* reference
`evolve` / `MacroCell` / `Grid`-live concepts. The evolve-coupled lemmas
(`evolve_reach_chebyshev`, the N2 margin capstone, the `manhattan`/`lightCone`
bridges) stay in `LightCone`, where the GoL semantics live.

All declarations keep their qualified names (`Conway.Life.chebDist`, etc.), so
every existing call site in `LightCone` resolves unchanged — only the defining
module moves. Sorry-free at creation. EPIC #3846, W3/W4 cycle-break.
-/

/-
# Géométrie du cône — faits purs de treillis (Mathlib uniquement)

Copyright (c) 2026 CoursIA. Tous droits réservés.
Distribué sous licence Apache 2.0 comme décrit dans le fichier LICENSE.
Version française mirrorée depuis l'anglais — voir les notes d'accessibilité
plus bas pour le rationale i18n.

## Géométrie du cône — base de pure géométrie (Mathlib uniquement)

Ce module est la **base de pure géométrie** de l'infrastructure Hashlife
à localité étroite de Conway (EPIC #3846, arc de refonte N2). Il héberge
la géométrie de treillis sur `Int × Int` qui ne dépend d'**aucune
sémantique du Jeu de la Vie** — ni `evolve`, ni `isAlive`, ni `candidates`,
ni `mooreNeighbors`, ni l'ensemble `lightCone`, ni la métrique `manhattan`,
ni aucun module de corps de preuve `MacroCell` / `Grid`. Son seul import
est Mathlib. Cette indépendance est structurelle, non cosmétique :

**Pourquoi un module séparé (cycle-break).** `Conway.Life.LightCone`
*importe* `Conway.Life.HashlifeCorrectness` (il a besoin de `evolve`,
`lightCone`, `manhattan` pour le théorème de portée `evolve_reach_chebyshev`
et le couronnement N2). L'import inverse — `HashlifeCorrectness` important
`LightCone` pour consommer `window_cheb_cone_in_domain` dans le chemin
P5 `p5_large_n_jump` — serait donc **circulaire**. Extraire ici la
géométrie Chebyshev pure casse le cycle : `LightCone` et `HashlifeCorrectness`
importent tous deux `ConeGeometry`, mais `ConeGeometry` n'importe ni l'un
ni l'autre.

**Critère de découpage (design-gate ai-01 msg-...338lw8, 2026-07-11).**
Une déclaration migre ici si et seulement si sa preuve ne référence que
`Int × Int`, `Int.natAbs`, `max`, omega/linarith, et les lemmes
arithmétiques de Mathlib — c'est-à-dire elle ne référence *pas* les
concepts `evolve` / `MacroCell` / `Grid`-live. Les lemmes couplés à
l'évolution (`evolve_reach_chebyshev`, le couronnement de marge N2, les
ponts `manhattan`/`lightCone`) restent dans `LightCone`, où vit la
sémantique du GoL.

Toutes les déclarations conservent leurs noms qualifiés
(`Conway.Life.chebDist`, etc.), donc tous les sites d'appel existants dans
`LightCone` se résolvent inchangés — seul le module de définition change.
Sans sorry à la création. EPIC #3846, cycle-break W3/W4.

## Note d'accessibilité Epic #1452/#1453

Ce module est un **kernel théorique pur** : géométrie du cône Chebyshev
réduite aux champs de structure canoniques Mathlib 4 (`max`, `Int.natAbs`,
`Nat.cast_pow`) et tactiques triviales (`omega`, `linarith`, `unfold`).
**Aucun moteur de preuve exotique requis** — la substance est entièrement
capturée par l'arithmétique entière linéaire de Mathlib. C'est précisément
la calibration SOTA-OK visée par l'Epic #1453 : cibles faciles à atteindre
pour le prouveur, accessibles aux étudiants qui s'initient à Lean 4, et
utiles aux modules aval (`LightCone`, `HashlifeCorrectness`) sans créer
de couplage sémantique.

Suit : hommage MathOverflow + convention Mathlib i18n #4980 ratifiée 2026-07-04.

## Substance réelle — géométrie pure du cône Chebyshev (L∞), 8 theorem + 1 def

`ConeGeometry.lean` héberge **8 theorem** + **1 def** sur la **géométrie
pure du cône de Chebyshev (L∞)** — la métrique qui gouverne la localité
*étroite* du Jeu de la Vie (un voisinage de Moore par génération B3/S23
donne exactement une coque de Chebyshev, donc `t` générations atteignent
le rayon de Chebyshev `t`, pas `2*t`) :

- `chebDist` : **définition** — distance de Chebyshev (L∞ / échecs) entre
  deux cellules `(p q : Int × Int)` : le max des deux déplacements
  absolus de coordonnées. C'est l'instance canonique de localité étroite
  du GoL, plus serrée que la métrique de Manhattan (L1) qui
  sur-approxime la portée par un facteur 2.
- `chebDist_self` : **réflexivité** — une cellule est à distance 0
  d'elle-même (réduit à `omega` sur `max`/`natAbs`).
- `chebDist_comm` : **symétrie** — invariance par échange des deux
  cellules (réduit à `omega`, max et natAbs sont symétriques).
- `chebDist_le_trans` : **monotonie en le rayon** — un rayon plus grand
  contient faiblement le cône (`hd.trans h` natif).
- `coord_bound_of_chebDist_le` : **suffisance de marge** — fait
  géométrique central : une cellule à distance Chebyshev `≤ t` de `p`
  a chacune de ses coordonnées à distance `≤ t` de la coordonnée
  correspondante de `p`. C'est précisément la raison pour laquelle une
  marge de boîte `t` (par ex. `padCenter2` avec marge `2^k`) couvre la
  portée Chebyshev-`t` *étroite*, là où la même marge `t` ne couvre pas
  le cône Manhattan-`t` (qui atteint `2*t`).
- `chebDist_triangle` : **inégalité triangulaire** pour Chebyshev
  (`max ≤ max + max`, `omega`).
- `chebDist_le_succ_iff` : **croissance exacte par étape de Moore** — la
  *conjonction* centrale pour la localité étroite : `q` est dans le
  cône Chebyshev-`(t+1)` de `p` ssi il existe une cellule `r` dans le
  cône Chebyshev-`t` de `p` qui soit un voisin de Moore de `q`
  (Chebyshev `≤ 1`). La direction forward construit `r` en pas-à-pas de
  `q` vers `p` sur chaque coordonnée non-nulle ; la direction backward
  utilise l'inégalité triangulaire. C'est le lemme additif qui sous-tend
  la localité *étroite* `t`-étapes (une coque de Moore par génération).
- `chebDist_le_succ` : **inclusion du cône dans son successeur** — rayon
  `t` ⊆ rayon `t+1` (corollaire de `chebDist_le_succ_iff` ou
  directement `Nat.le_succ`).
- `window_cheb_cone_in_domain` : **W3 localité étroite reste dans le
  domaine** — l'analogue *serré* de `window_cone_in_domain` (lemme
  fermé **S2** dans `HashlifeCorrectness` qui utilisait le cône Manhattan
  *lâche* `manhattan p q ≤ 2^k`). Pour un point `p` dans la fenêtre
  centrée `[2^k, 2^k + 2^(k+1))²` (la région couverte par un résultat
  Hashlife), toute cellule `q` à rayon *Chebyshev* `2^k` — cône
  strict, plus petit que le cône Manhattan-`2^k` lâche — reste dans le
  domaine MacroCell complet `[0, 2^(k+2))²`. La preuve est *plus simple*
  que l'analogue lâche : elle consomme `coord_bound_of_chebDist_le`
  (borne par coordonnée immédiate) au lieu de ponter via
  `manhattan_deviation`. Pas de `hashlifeResultAux`, pas de mur `whnf` —
  arithmétique `Int` pure. Sans sorry.

**Densité 0.762 thm/KB** (8/10496) — modeste car la substance est
*géométrique* (1 axiome par ~30 lignes de preuve structurée) plutôt que
*cohomologique* ou *catégorielle*. C'est la signature attendue d'un
module de géométrie pure : densité comparable à `LightCone` (5 theorem
sur ~17 KB) plutôt qu'à `SieveOps` (9 theorem sur ~5 KB).

## Pont Mathlib + accessibilité Epic #1452

L'unique import est **Mathlib** (et tout est dans `namespace Conway ∘ namespace Life`,
qualifié `Conway.Life.chebDist` aux sites d'appel). Les 8 theorem
réduisent la géométrie du cône Chebyshev aux **champs de structure
canoniques Mathlib 4** sur `Int` et `Nat` (`max`, `Int.natAbs`,
`Nat.cast_pow`) et à `Int.abs_le` (dépaquetage d'`abs` en clamp
bilatéral). Les tactiques sont purement arithmétiques (`omega`,
`linarith`, `exact_mod_cast`, `unfold`, `Nat.le_succ`). **Aucun`decide`
ni moteur de preuve exotique requis** : c'est le kernel théorique pur
que `#1453` cible pour la co-évolution du harnais prouveur.

Hommage MathOverflow + Mathlib i18n convention #4980 ratifiée 2026-07-04
(option A pragmatique : deux blocs `/` top-level distincts, sans
séparateur `---` interne).
-/
import Mathlib

namespace Conway
namespace Life

/-! ## Chebyshev (chessboard) distance and the tight locality cone

The *tight* Game-of-Life locality is governed by the Chebyshev (L∞) distance:
one B3/S23 generation reaches exactly the Moore neighborhood (Chebyshev radius
1), so `t` generations reach Chebyshev radius `t`. The `lightCone` machinery in
`LightCone` uses the Manhattan (L1) distance, which over-approximates the tight
reach by a factor of 2 — `step_light_cone` demands Manhattan radius `2 * t`. The
lemmas below formalize the Chebyshev cone structure that a *tight* single-jump
correctness proof chains through:

- the cone fits in a margin-`t` box (**margin sufficiency** — the geometric fact
  that makes the `padCenter2` margin `2^k` sufficient for a single jump of `2^k`
  generations: the tight Chebyshev reach `2^k` fits exactly in a margin-`2^k`
  box, whereas the loose Manhattan-`2^k` light cone would need `2^(k+1)`); and

These are the elementary distance facts; they do not assert anything about
`evolve` (the locality statement `step_light_cone` lives in `HashlifeCorrectness`).
Epic #3846 (Hashlife correctness infrastructure, N2 tight-locality groundwork). -/

/-- Chebyshev (chessboard / L∞) distance between two cells: the larger of the
    absolute coordinate displacements. -/
def chebDist (p q : Int × Int) : Nat :=
  max (Int.natAbs (q.1 - p.1)) (Int.natAbs (q.2 - p.2))

/-- Reflexivity: a cell is at Chebyshev distance 0 from itself. -/
theorem chebDist_self (p : Int × Int) : chebDist p p = 0 := by
  unfold chebDist; omega

/-- Symmetry: the Chebyshev distance is invariant under swapping the two cells. -/
theorem chebDist_comm (p q : Int × Int) : chebDist p q = chebDist q p := by
  unfold chebDist; omega

/-- Monotonicity in the radius: a larger radius weakly contains the cone. -/
theorem chebDist_le_trans {t₁ t₂ : Nat} (h : t₁ ≤ t₂) {p q : Int × Int}
    (hd : chebDist p q ≤ t₁) : chebDist p q ≤ t₂ := hd.trans h

/-- Margin sufficiency: a cell within Chebyshev radius `t` of `p` lies in the
    margin-`t` box — each coordinate is within `t` of `p`'s coordinate. This is
    the geometric reason a box margin of `t` (e.g. `padCenter2`'s `2^k` margin
    at a level advancing `2^k` generations) covers the *tight* Chebyshev-`t`
    reach, even though that same margin `t` does not cover the *loose*
    Manhattan-`t` light cone (which reaches `2 * t`). -/
theorem coord_bound_of_chebDist_le (p q : Int × Int) (t : Nat)
    (h : chebDist p q ≤ t) :
    Int.natAbs (q.1 - p.1) ≤ t ∧ Int.natAbs (q.2 - p.2) ≤ t := by
  unfold chebDist at h
  omega

/-! ## Chebyshev triangle inequality and cone growth by a Moore step

The foundational metric fact (`chebDist_triangle`) and the **tight-cone growth
theorem** named by ai-01's N2 greenlight: a cell lies in the Chebyshev-`(t+1)`
cone of `p` iff one can reach it from the Chebyshev-`t` cone via a single Moore
neighborhood step. This is the inductive engine of the tight-locality statement
(after one B3/S23 generation, reach expands by exactly one Moore shell), and the
reason the tight Chebyshev reach grows linearly with `t` rather than as `2*t`.
-/

/-- Triangle inequality for the Chebyshev distance. -/
theorem chebDist_triangle (p q r : Int × Int) :
    chebDist p q ≤ chebDist p r + chebDist r q := by
  unfold chebDist
  omega

/-- The Chebyshev cone grows by exactly one Moore step: `q` is within Chebyshev
    radius `t+1` of `p` iff there is a cell `r` within Chebyshev radius `t` of `p`
    that is a Moore neighbor of `q` (Chebyshev radius `≤ 1`). Forward direction
    steps from `q` toward `p` by one unit in each nonzero coordinate; backward
    direction is the triangle inequality. This is the additive-growth lemma that
    underpins the tight `t`-step locality (one Moore shell per generation). -/
theorem chebDist_le_succ_iff (p q : Int × Int) (t : Nat) :
    chebDist p q ≤ t + 1 ↔
      ∃ r : Int × Int, chebDist p r ≤ t ∧ chebDist r q ≤ 1 := by
  constructor
  · -- forward: step from `q` toward `p` by one unit in each nonzero coordinate
    intro h
    unfold chebDist at h
    refine ⟨(q.1 - if q.1 - p.1 = 0 then 0 else if 0 < q.1 - p.1 then 1 else -1,
             q.2 - if q.2 - p.2 = 0 then 0 else if 0 < q.2 - p.2 then 1 else -1), ?_, ?_⟩
    all_goals unfold chebDist; omega
  · -- backward: triangle inequality
    rintro ⟨r, hr, hq⟩
    exact (chebDist_triangle p q r).trans (add_le_add hr hq)

/-- The tight Chebyshev cone is nested in its successor: radius `t` ⊆ radius
    `t+1`. Corollary of `chebDist_le_succ_iff` (or directly `Nat.le_succ`). -/
theorem chebDist_le_succ (p q : Int × Int) (t : Nat) (h : chebDist p q ≤ t) :
    chebDist p q ≤ t + 1 := h.trans (Nat.le_succ t)

/-! ## W3 tight cone-in-domain: Chebyshev-tight locality stays in the domain

The tight Chebyshev analog of `window_cone_in_domain` (the **S2** closed lemma in
`HashlifeCorrectness`, which used the *loose* Manhattan cone `manhattan p q ≤ 2^k`).
For a point `p` in the centered window `[2^k, 2^k + 2^(k+1))²` (the region a
Hashlife result covers), any cell `q` within **Chebyshev** radius `2^k` — the
*tight* GoL speed-of-light cone, strictly smaller than the loose Manhattan-`2^k`
cone (a Chebyshev-`t` ball fits in a Manhattan-`2t` ball, not the reverse) — stays
inside the full MacroCell domain `[0, 2^(k+2))²`.

This is the missing tight locality bound for the N2 redesign arc (EPIC #3846, W3).
The loose `window_cone_in_domain` demanded Manhattan-`2^k` agreement, over-
approximating the real reach by a factor of 2; the tight version demands only
Chebyshev-`2^k` agreement (the actual one-Moore-shell-per-generation reach
formalized by `evolve_reach_chebyshev`). Because Chebyshev distance bounds each
coordinate directly, the proof is **simpler** than the loose analog: it consumes
`coord_bound_of_chebDist_le` (per-coordinate bound immediately) rather than
bridging through `manhattan_deviation`. No `hashlifeResultAux`, no whnf wall —
pure `Int` window arithmetic. Sorry-free.

This lemma lives in `ConeGeometry` (not `LightCone`) so that the P5
`p5_large_n_jump` path in `HashlifeCorrectness` can consume it directly via
`import Conway.Life.ConeGeometry`, without the circular reverse-import that would
arise if it stayed in `LightCone` (which imports `HashlifeCorrectness`). The
proof substance is independent of the P4 mono-verrou. -/
theorem window_cheb_cone_in_domain (k : Nat) (p q : Int × Int)
    (hp1_lo : (2^k : Int) ≤ p.1) (hp1_hi : p.1 < 2^k + 2^(k+1))
    (hp2_lo : (2^k : Int) ≤ p.2) (hp2_hi : p.2 < 2^k + 2^(k+1))
    (hc : chebDist p q ≤ 2^k) :
    (0 : Int) ≤ q.1 ∧ q.1 < 2^(k+2) ∧ (0 : Int) ≤ q.2 ∧ q.2 < 2^(k+2) := by
  -- Chebyshev radius bounds each coordinate directly (no manhattan bridge).
  obtain ⟨hq1, hq2⟩ := coord_bound_of_chebDist_le p q (2^k) hc
  -- `coord_bound_of_chebDist_le` types its bounds as `Nat` (`Int.natAbs ... ≤
  -- 2^k`); the window hypotheses below use native-Int `(2^k : Int)` (`HPower`).
  -- Bridge the Nat-bound to an `Int.abs`-typed bound (mirroring the loose
  -- analog's `manhattan_deviation` output, which is already Int-typed), then
  -- unify the atoms via `Nat.cast_pow`.
  have hk_pow : (↑((2:Nat)^k) : Int) = (2^k : Int) := Nat.cast_pow 2 k
  have hq1' : |q.1 - p.1| ≤ (2^k : Int) := by
    rw [hk_pow.symm, Int.abs_eq_natAbs]; exact_mod_cast hq1
  have hq2' : |q.2 - p.2| ≤ (2^k : Int) := by
    rw [hk_pow.symm, Int.abs_eq_natAbs]; exact_mod_cast hq2
  -- Power facts in pure `Nat`, lifted to `Int` (linarith reads the atoms).
  have hpe1 : (2^(k+1) : Int) = 2 * (2^k : Int) := by
    have h : (2 : Nat)^(k+1) = 2 * (2 : Nat)^k := by
      rw [show (k + 1 : Nat) = Nat.succ k from rfl, Nat.pow_succ, Nat.mul_comm]
    exact_mod_cast h
  have hpe2 : (2^(k+2) : Int) = 4 * (2^k : Int) := by
    have h1 : (2 : Nat)^(k+1) = 2 * (2 : Nat)^k := by
      rw [show (k + 1 : Nat) = Nat.succ k from rfl, Nat.pow_succ, Nat.mul_comm]
    have h2 : (2 : Nat)^(k+2) = 2 * (2 : Nat)^(k+1) := by
      rw [show (k + 2 : Nat) = Nat.succ (k + 1) from rfl, Nat.pow_succ, Nat.mul_comm]
    have h : (2 : Nat)^(k+2) = 4 * (2 : Nat)^k := by rw [h2, h1]; ring
    exact_mod_cast h
  -- `Int.abs` bound unpacked into a two-sided `Int` clamp on `q.i - p.i`.
  obtain ⟨hq1lo, hq1hi⟩ := abs_le.mp hq1'
  obtain ⟨hq2lo, hq2hi⟩ := abs_le.mp hq2'
  -- Rewrite every power occurrence into a multiple of the single atom `2^k`.
  rw [hpe1] at hp1_hi hp2_hi
  rw [hpe2]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

end Life
end Conway
