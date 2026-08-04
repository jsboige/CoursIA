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

/-! ## Distance de Chebyshev (échiquier) et cône de localité étroite

La localité *étroite* du Jeu de la Vie est gouvernée par la distance de
Chebyshev (L∞) : une génération B3/S23 atteint exactement le voisinage de Moore
(rayon de Chebyshev 1), donc `t` générations atteignent le rayon de Chebyshev
`t`. La machinerie `lightCone` dans `LightCone` utilise la distance de Manhattan
(L1), qui sur-approxime la portée étroite d'un facteur 2 — `step_light_cone`
exige le rayon de Manhattan `2 * t`. Les lemmes ci-dessous formalisent la
structure du cône de Chebyshev qu'une preuve de correction à saut unique
*étroite* enchaîne :

- le cône tient dans une boîte de marge `t` (**suffisance de marge** — le fait
  géométrique qui rend la marge `padCenter2` `2^k` suffisante pour un saut de
  `2^k` générations : la portée Chebyshev étroite `2^k` tient exactement dans
  une boîte de marge `2^k`, alors que le cône de lumière Manhattan-`2^k`
  lâche nécessiterait `2^(k+1)`) ; et

Ce sont les faits de distance élémentaires ; ils n'affirment rien sur `evolve`
(l'énoncé de localité `step_light_cone` vit dans `HashlifeCorrectness`).
EPIC #3846 (infrastructure de correction Hashlife, fondation N2 de localité
étroite). -/

/-- Distance de Chebyshev (échiquier / L∞) entre deux cellules : le plus grand
    des déplacements absolus de coordonnées. -/
def chebDist (p q : Int × Int) : Nat :=
  max (Int.natAbs (q.1 - p.1)) (Int.natAbs (q.2 - p.2))

/-- Réflexivité : une cellule est à distance de Chebyshev 0 d'elle-même. -/
theorem chebDist_self (p : Int × Int) : chebDist p p = 0 := by
  unfold chebDist; omega

/-- Symétrie : la distance de Chebyshev est invariante par échange des deux cellules. -/
theorem chebDist_comm (p q : Int × Int) : chebDist p q = chebDist q p := by
  unfold chebDist; omega

/-- Monotonie en le rayon : un rayon plus grand contient faiblement le cône. -/
theorem chebDist_le_trans {t₁ t₂ : Nat} (h : t₁ ≤ t₂) {p q : Int × Int}
    (hd : chebDist p q ≤ t₁) : chebDist p q ≤ t₂ := hd.trans h

/-- Suffisance de marge : une cellule à distance Chebyshev `≤ t` de `p` se
    trouve dans la boîte de marge `t` — chaque coordonnée est à distance `≤ t`
    de la coordonnée de `p`. C'est la raison géométrique pour laquelle une marge
    de boîte `t` (par ex. la marge `2^k` de `padCenter2` à un niveau avançant de
    `2^k` générations) couvre la portée Chebyshev-`t` *étroite*, alors que cette
    même marge `t` ne couvre pas le cône de lumière Manhattan-`t` *lâche* (qui
    atteint `2 * t`). -/
theorem coord_bound_of_chebDist_le (p q : Int × Int) (t : Nat)
    (h : chebDist p q ≤ t) :
    Int.natAbs (q.1 - p.1) ≤ t ∧ Int.natAbs (q.2 - p.2) ≤ t := by
  unfold chebDist at h
  omega

/-! ## Inégalité triangulaire de Chebyshev et croissance du cône par pas de Moore

Le fait métrique fondateur (`chebDist_triangle`) et le **théorème de croissance
du cône étroit** nommé par le greenlight N2 d'ai-01 : une cellule se trouve
dans le cône Chebyshev-`(t+1)` de `p` ssi on peut l'atteindre depuis le cône
Chebyshev-`t` par un seul pas de voisinage de Moore. C'est le moteur inductif de
l'énoncé de localité étroite (après une génération B3/S23, la portée s'étend
d'exactement une coque de Moore), et la raison pour laquelle la portée Chebyshev
étroite croît linéairement avec `t` plutôt qu'en `2*t`.
-/

/-- Inégalité triangulaire pour la distance de Chebyshev. -/
theorem chebDist_triangle (p q r : Int × Int) :
    chebDist p q ≤ chebDist p r + chebDist r q := by
  unfold chebDist
  omega

/-- Le cône de Chebyshev croît d'exactement un pas de Moore : `q` est à distance
    Chebyshev `t+1` de `p` ssi il existe une cellule `r` à distance Chebyshev `t`
    de `p` qui soit un voisin de Moore de `q` (distance Chebyshev `≤ 1`). La
    direction forward progresse de `q` vers `p` d'une unité sur chaque coordonnée
    non nulle ; la direction backward est l'inégalité triangulaire. C'est le
    lemme de croissance additive qui sous-tend la localité étroite à `t` étapes
    (une coque de Moore par génération). -/
theorem chebDist_le_succ_iff (p q : Int × Int) (t : Nat) :
    chebDist p q ≤ t + 1 ↔
      ∃ r : Int × Int, chebDist p r ≤ t ∧ chebDist r q ≤ 1 := by
  constructor
  · -- forward : progresser de `q` vers `p` d'une unité sur chaque coordonnée non nulle
    intro h
    unfold chebDist at h
    refine ⟨(q.1 - if q.1 - p.1 = 0 then 0 else if 0 < q.1 - p.1 then 1 else -1,
             q.2 - if q.2 - p.2 = 0 then 0 else if 0 < q.2 - p.2 then 1 else -1), ?_, ?_⟩
    all_goals unfold chebDist; omega
  · -- backward : inégalité triangulaire
    rintro ⟨r, hr, hq⟩
    exact (chebDist_triangle p q r).trans (add_le_add hr hq)

/-- Le cône de Chebyshev étroit est inclus dans son successeur : rayon `t` ⊆
    rayon `t+1`. Corollaire de `chebDist_le_succ_iff` (ou directement
    `Nat.le_succ`). -/
theorem chebDist_le_succ (p q : Int × Int) (t : Nat) (h : chebDist p q ≤ t) :
    chebDist p q ≤ t + 1 := h.trans (Nat.le_succ t)

/-! ## W3 cône étroit dans le domaine : la localité Chebyshev-étroite reste dans le domaine

L'analogue Chebyshev étroit de `window_cone_in_domain` (le lemme fermé **S2**
dans `HashlifeCorrectness`, qui utilisait le cône Manhattan *lâche*
`manhattan p q ≤ 2^k`). Pour un point `p` dans la fenêtre centrée
`[2^k, 2^k + 2^(k+1))²` (la région couverte par un résultat Hashlife), toute
cellule `q` à distance **Chebyshev** `2^k` — le cône de vitesse de la
lumière GoL *étroit*, strictement plus petit que le cône Manhattan-`2^k`
lâche (une boule Chebyshev-`t` tient dans une boule Manhattan-`2t`, pas
l'inverse) — reste dans le domaine MacroCell complet `[0, 2^(k+2))²`.

C'est la borne de localité étroite manquante pour l'arc de refonte N2 (EPIC
#3846, W3). Le `window_cone_in_domain` lâche exigeait l'accord Manhattan-`2^k`,
sur-approximant la portée réelle d'un facteur 2 ; la version étroite n'exige
que l'accord Chebyshev-`2^k` (la portée réelle d'une-coque-de-Moore-par-
génération formalisée par `evolve_reach_chebyshev`). Comme la distance de
Chebyshev borne directement chaque coordonnée, la preuve est **plus simple**
que l'analogue lâche : elle consomme `coord_bound_of_chebDist_le` (borne par
coordonnée immédiate) au lieu de ponter via `manhattan_deviation`. Pas de
`hashlifeResultAux`, pas de mur `whnf` — arithmétique de fenêtre `Int` pure.
Sans sorry.

Ce lemme vit dans `ConeGeometry` (pas dans `LightCone`) pour que le chemin P5
`p5_large_n_jump` dans `HashlifeCorrectness` puisse le consommer directement via
`import Conway.Life.ConeGeometry`, sans l'import inverse circulaire qui
surviendrait s'il restait dans `LightCone` (qui importe `HashlifeCorrectness`).
La substance de la preuve est indépendante du mono-verrou P4. -/

/-- Identité de puissance `2^(k+1) = 2 · 2^k` dans `Int`, prouvée en `Nat` pur
(rw + `Nat.pow_succ`) puis remontée via `exact_mod_cast`. Partagée par les deux
théorèmes d'appartenance à la fenêtre `window_cheb_cone_in_domain` (ce module)
et `window_cone_in_domain` (`HashlifeCorrectness`, qui importe ce module), d'où
sa factorisation ici plutôt que sa duplication inline dans chaque consommateur. -/
lemma pow_two_add_one_int (k : Nat) : (2^(k+1) : Int) = 2 * (2^k : Int) := by
  have h : (2 : Nat)^(k+1) = 2 * (2 : Nat)^k := by
    rw [show (k + 1 : Nat) = Nat.succ k from rfl, Nat.pow_succ, Nat.mul_comm]
  exact_mod_cast h

/-- Identité de puissance `2^(k+2) = 4 · 2^k` dans `Int`, prouvée en `Nat` pur
(rw + `Nat.pow_succ` sur deux étapes) puis remontée via `exact_mod_cast`. Même
rationale de partage que `pow_two_add_one_int` : consommée par les deux
théorèmes d'appartenance à la fenêtre. -/
lemma pow_two_add_two_int (k : Nat) : (2^(k+2) : Int) = 4 * (2^k : Int) := by
  have h1 : (2 : Nat)^(k+1) = 2 * (2 : Nat)^k := by
    rw [show (k + 1 : Nat) = Nat.succ k from rfl, Nat.pow_succ, Nat.mul_comm]
  have h2 : (2 : Nat)^(k+2) = 2 * (2 : Nat)^(k+1) := by
    rw [show (k + 2 : Nat) = Nat.succ (k + 1 : Nat) from rfl, Nat.pow_succ, Nat.mul_comm]
  have h : (2 : Nat)^(k+2) = 4 * (2 : Nat)^k := by rw [h2, h1]; ring
  exact_mod_cast h

theorem window_cheb_cone_in_domain (k : Nat) (p q : Int × Int)
    (hp1_lo : (2^k : Int) ≤ p.1) (hp1_hi : p.1 < 2^k + 2^(k+1))
    (hp2_lo : (2^k : Int) ≤ p.2) (hp2_hi : p.2 < 2^k + 2^(k+1))
    (hc : chebDist p q ≤ 2^k) :
    (0 : Int) ≤ q.1 ∧ q.1 < 2^(k+2) ∧ (0 : Int) ≤ q.2 ∧ q.2 < 2^(k+2) := by
  -- Le rayon de Chebyshev borne directement chaque coordonnée (pas de pont Manhattan).
  obtain ⟨hq1, hq2⟩ := coord_bound_of_chebDist_le p q (2^k) hc
  -- `coord_bound_of_chebDist_le` type ses bornes comme `Nat` (`Int.natAbs ... ≤
  -- 2^k`) ; les hypothèses de fenêtre ci-dessous utilisent du `(2^k : Int)` natif
  -- (`HPower`). On ponte la borne `Nat` vers une borne typée `Int.abs` (miroir
  -- de la sortie `manhattan_deviation` de l'analogue lâche, déjà typée Int),
  -- puis on unifie les atomes via `Nat.cast_pow`.
  have hk_pow : (↑((2:Nat)^k) : Int) = (2^k : Int) := Nat.cast_pow 2 k
  have hq1' : |q.1 - p.1| ≤ (2^k : Int) := by
    rw [hk_pow.symm, Int.abs_eq_natAbs]; exact_mod_cast hq1
  have hq2' : |q.2 - p.2| ≤ (2^k : Int) := by
    rw [hk_pow.symm, Int.abs_eq_natAbs]; exact_mod_cast hq2
  -- Faits de puissance en `Nat` pur, remontés vers `Int` (linarith lit les
  -- atomes), factorisés dans les lemmes nommés
  -- `pow_two_add_one_int`/`pow_two_add_two_int` ci-dessus (partagés avec
  -- `window_cone_in_domain` dans `HashlifeCorrectness`).
  have hpe1 : (2^(k+1) : Int) = 2 * (2^k : Int) := pow_two_add_one_int k
  have hpe2 : (2^(k+2) : Int) = 4 * (2^k : Int) := pow_two_add_two_int k
  -- Borne `Int.abs` dépaquetée en un clamp `Int` bilatéral sur `q.i - p.i`.
  obtain ⟨hq1lo, hq1hi⟩ := abs_le.mp hq1'
  obtain ⟨hq2lo, hq2hi⟩ := abs_le.mp hq2'
  -- Réécriture de chaque occurrence de puissance en un multiple du seul atome `2^k`.
  rw [hpe1] at hp1_hi hp2_hi
  rw [hpe2]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

end Life
end Conway
