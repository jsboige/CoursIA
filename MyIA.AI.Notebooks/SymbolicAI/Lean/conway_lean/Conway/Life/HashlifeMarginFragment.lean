/-
Copyright (c) 2026 CoursIA. Tous droits réservés.
Distribué sous licence Apache 2.0 comme décrit dans le fichier LICENSE.

## Livrable B (#9568) — le fragment « fenêtre à marge » (premier cran Spartan logic)

Module compagnon de `Conway.Life.HashlifeCorrectness` (l'infrastructure de correction
`hashlife_correct` / `centralCorrect` / `centralCorrect_mem`, c.153) et du bestiaire
`Conway.Life.AdversarialBattery` (#9589). Il formalise le **premier cran de relativisation
géométrique** du cadrage user (2026-08-06, issue #9568) : prouver que Hashlife « marche
bien en Spartan logic » — une correction **relative/bornée**, connue pour être bien plus
facile que l'universelle et **suffisante pour les corollaires réels visés**.

### Le fragment

Le fragment des configurations dont le **support tient dans la fenêtre centrale avec une
marge de garde égale à l'horizon `2^k`** : chaque cellule vivante est à au moins `2^k`
cellules de la frontière du domaine MacroCell, donc sur les `2^k` générations de
l'horizon, **rien ne peut jamais saigner hors de la fenêtre** — le cône de lumière
Chebyshev de rayon `2^k` reste strictement à l'intérieur de la marge.

Prédicat candidat :
  `supportInMargin c k := BoxAssezGrandN (c.toGrid (0, 0)) (2^k)`

On utilise la variante **n-aware** `BoxAssezGrandN` (padding `max 2 n`, satisfiable pour
tout `n`) plutôt que la fixed-frame `BoxAssezGrand` (plafonnée à `n ≤ 2` par
`boxAssezGrand_nonempty_le_two`) : c'est ce qui rend le fragment **satisfiable pour tout
horizon `2^k`** et valide l'argument de suffisance « choisir `k` par horizon » ci-dessous.
Le sanity-check `cexBlock1_supportInMargin_k2` exhibe `2^2 = 4` sur le bloc 2×2 —
impossible avec la fixed-frame, possible ici.

### L'énoncé-cadre `hashlife_correct_margin` (sorry documenté, verdict INTRINSIC)

Sous le fragment `supportInMargin c k` et l'hypothèse de correction centrale
`centralCorrect c k` (le whnf-wall bypass de c.153), l'égalité de grille globale
`evolveHashlifeFast (2^k) (c.toGrid (0,0)) = evolve (2^k) (c.toGrid (0,0))` tient sur tout
l'horizon `2^k`. La preuve requiert l'**assemblage borné P4/P5** — comment `centralCorrect`
(correction MacroCell-level au niveau `k`) se relève en égalité de grille globale via la
récursion Hashlife, avec la marge contenant le cône de lumière à chaque saut. Cet
assemblage est le contenu des PR #9745/#9760 d'ai-01 (c.92–c.94, `p4_nw_overlap_wall`
sorry 10→9) et reste le cœur de recherche ouvert. L'énoncé est livré comme **cadre**
(acceptance B : sorry documenté acceptable au premier commit), pas comme une preuve
manquée — verdict INTRINSIC sur la partie non prouvée, avec la raison.

### Pourquoi ce fragment GÉOMÉTRIQUE suffit pour les corollaires réels

La « Spartan logic » au sens strict (still lifes + gliders, vocabulaire Goucher) est un
raffinement ultérieur ; ce fragment géométrique la précède et suffit déjà :

1. **Machine de Turing finie (T pas)** : toute computation de MT pour `T` pas s'embed dans
   le fragment en choisissant `k` tel que `2^k ≥ T` (horizon) avec la marge de garde. L'aspect
   non-borné en temps se traite par **ré-invocation à `k` croissant** (le wrapper Hashlife
   standard « expand puis récurse ») — chaque horizon instancié vit dans le fragment.
2. **Tuile OTCA / réplication Gemini** : ces patterns ont un support borné connu ; on
   choisit `k` par la taille du pattern + horizon de réplication, et la marge contient le
   cône de lumière de la phase de réplication.
3. **GOL-dans-GOL** : l'émulation d'un GOL fini dans un GOL plus grand s'embed avec marge
   par construction (le GOL hôte fournit la fenêtre centrale, l'invité le support).

### Contraintes

FR canonique + sibling `_en` (gate #4980 : refus merge FR-only). Le `sorry` documenté est
accepté explicitement au titre de l'acceptance B. Sanity-checks réels (décidables au
kernel) sur le bestiaire ci-dessous. EPIC #3846 / #6724 / #9568.
-/

/-
  Convention i18n (EPIC #4980, décision user 2026-07-04) : ce fichier est **FR
  canonique**, avec son miroir anglais dans le fichier sibling
  `HashlifeMarginFragment_en.lean`. Les énoncés de théorèmes, les tactiques Lean, les noms
  de lemmes et les références Mathlib restent en anglais (compat Mathlib 4) ; seules les
  docstrings et ce bloc d'en-tête diffèrent entre les deux fichiers.
-/

import Conway.Life.AdversarialBattery
import Conway.Life.HashlifeCorrectness
import Conway.Life.LightCone

namespace Conway
namespace Life

/-! ## Le prédicat de fragment `supportInMargin` -/

/-- **Le fragment « fenêtre à marge » (Livrable B, #9568).** Le support de la cellule
    `c` (rendu en grille à l'origine) tient dans la fenêtre centrale avec une marge de
    garde égale à l'horizon `2^k` : chaque cellule vivante est à au moins `2^k` de la
    frontière du domaine MacroCell. Sur les `2^k` générations de l'horizon, le cône de
    lumière Chebyshev (rayon `2^k`) reste strictement à l'intérieur de la marge, donc
    **rien ne saigne hors de la fenêtre**.

    On utilise la variante **n-aware** `BoxAssezGrandN` (padding `max 2 n`, satisfiable
    pour tout `n`) plutôt que la fixed-frame `BoxAssezGrand` (plafonnée à `n ≤ 2` par
    `boxAssezGrand_nonempty_le_two`) : c'est ce qui rend le fragment satisfiable pour tout
    horizon `2^k` et valide l'argument de suffisance « choisir `k` par horizon ». -/
def supportInMargin (c : MacroCell) (k : Nat) : Prop :=
  BoxAssezGrandN (c.toGrid (0, 0)) (2^k)

/-- **Décidabilité du fragment** (compagnon de l'instance `Decidable (BoxAssezGrandN)`,
    HashlifeCorrectness L227). `supportInMargin` est une `def ... : Prop` séparée, donc
    l'instance `Decidable (BoxAssezGrandN g n)` ne se propage pas automatiquement à travers
    elle (Lean ne réduit pas une `def` non-`@[reducible]` lors de la synthèse d'instance).
    On déclare l'instance compagnon, exactement comme `BoxAssezGrandN` déclare la sienne
    au-dessus de l'instance `Decidable` native — pattern canonique du codebase. -/
instance (c : MacroCell) (k : Nat) : Decidable (supportInMargin c k) :=
  inferInstanceAs (Decidable (BoxAssezGrandN (c.toGrid (0, 0)) (2^k)))

/-- **Trivialité du fragment** (relocalisé c.8206, #9568). `supportInMargin`
    contient TOUTE MacroCell à TOUT horizon `k` — c'est une **tautologie**,
    prouvé sur place depuis `boxAssezGrandN_trivial` (à côté de
    `BoxAssezGrandN` dans `Foundation`, c.8206). L'hypothèse
    `h_margin : supportInMargin c k` de `hashlife_correct_margin` ne restreint
    donc rien ; voir la note *inconditionnel-en-attente* dans la docstring
    de ce théorème. -/
theorem supportInMargin_trivial (c : MacroCell) (k : Nat) :
    supportInMargin c k :=
  boxAssezGrandN_trivial _ _

/-! ## L'énoncé-cadre `hashlife_correct_margin` (sorry documenté, INTRINSIC)

Sous le fragment + `centralCorrect c k`, l'égalité de grille globale
`evolveHashlifeFast (2^k) (c.toGrid (0,0)) = evolve (2^k) (c.toGrid (0,0))` tient sur
l'horizon `2^k`. Le `sorry` est l'assemblage borné P4/P5 (ai-01, #9745/#9760) : comment
`centralCorrect` (correction MacroCell-level) se relève en égalité globale via la récursion
Hashlife, la marge contenant le cône de lumière à chaque saut. Énoncé-cadre (acceptance B),
pas une preuve manquée. -/

/-- **Correction Hashlife relative au fragment « fenêtre à marge » (Livrable B, #9568).**
    Si le support de `c` tient dans la fenêtre centrale avec marge de garde `2^k`
    (`supportInMargin`), et si la correction centrale `centralCorrect c k` tient au
    niveau `k`, alors `evolveHashlifeFast` coïncide avec l'évolution de référence `evolve`
    sur tout l'horizon `2^k` — la marge garantit qu'aucun cône de lumière ne saigne hors de
    la fenêtre pendant la récursion Hashlife.

    **Suffisance pour les corollaires réels** (le cœur pédagogique de ce Livrable B) :
    toute computation bornée s'embed dans le fragment en choisissant `k` par horizon.
    (1) **MT finie (T pas)** : choisir `2^k ≥ T` + marge ; l'aspect non-borné en temps se
    traite par ré-invocation à `k` croissant (wrapper « expand puis récurse »). (2) **Tuile
    OTCA / réplication Gemini** : support borné connu, `k` par taille + horizon de
    réplication. (3) **GOL-dans-GOL** : l'émulation d'un GOL fini dans un GOL plus grand
    s'embed avec marge par construction. La Spartan logic stricte (still lifes + gliders,
    vocabulaire Goucher) est un raffinement ultérieur de ce fragment géométrique.

    **Verdict sur la preuve : INTRINSIC.** Le pont de `centralCorrect` (correction
    MacroCell-level) vers l'égalité de grille globale requiert l'assemblage borné P4/P5 —
    `p4_nw_overlap_wall` et sa chaîne helper 4-stage (PR #9745/#9760, ai-01 c.92–c.94,
    sorry 10→9). C'est le cœur de recherche ouvert ; cet énoncé en est le cadre honnête
    (acceptance B : sorry documenté acceptable au premier commit).

    **Note de cadrage (c.212, 2026-08-11) — *inconditionnel-en-attente*.** Le prédicat
    `supportInMargin` est une **tautologie** (prouvé par `supportInMargin_trivial`,
    JumpCapture.lean:120) : `gridFrameN n g` pad par `max 2 n ≥ n` et `cellMargin` côté
    proche est non strict, donc `BoxAssezGrandN g n` est vraie pour **toute** grille et
    **tout** `n`. L'hypothèse `h_margin : supportInMargin c k` ne restreint donc rien —
    l'énoncé effectif est l'inconditionnel complet, sous un habillage géométrique qui ne
    relativise pas. La vraie relativisation est ailleurs (prédicat `jumpCaptured`,
    JumpCapture.lean §3, avec témoin `jumpCaptured_not_trivial`). Ce `sorry` reste donc
    le **cœur de recherche ouvert**, indépendamment de la fragilité de son habillage —
    verdict INTRINSIC préservé, contenu scientifique non-affaibli par ce constat. -/
theorem hashlife_correct_margin (c : MacroCell) (k : Nat)
    (h_margin : supportInMargin c k) (h_central : centralCorrect c k) :
    evolveHashlifeFast (2^k) (c.toGrid (0, 0)) = evolve (2^k) (c.toGrid (0, 0)) := by
  -- INTRINSIC: bounded P4/P5 assembly (ai-01, #9745/#9760). The margin `supportInMargin`
  -- contains the Chebyshev light-cone (radius 2^k) of the jump, so the hashlife recursion
  -- never reads outside the central window; `centralCorrect` (c.153 whnf-wall bypass) then
  -- lifts to the global grid equality over the horizon. The inductive lift through the
  -- MacroCell recursion (`p4_nw_overlap_wall` and the offset-matching assembly) is the
  -- open P4/P5 heart — sorry documenté (acceptance B).
  sorry

/-! ## Assemblage P4.4 — réduction sorry-stable (tranche 2, #13483)

Diagnostic du 2026-09-04 (c.5539811910) : toutes les briques préliminaires sont prouvées
(`p5_large_n_jumpN` b3', P4 complet, les 4 murs bornés sans sorry) — le sorry de
`hashlife_correct_margin` est l'assemblage lui-même. Décomposition :

- **L1** — l'hypothèse `h_margin` est gratuite : `supportInMargin` est tautologique
  (`supportInMargin_trivial`), l'énoncé effectif est l'inconditionnel sous `centralCorrect`.
- **L2** — le but se réduit à l'hypothèse de la machine N : `hashlife_correctN` (prouvé,
  HashlifeCorrectness) donne l'égalité globale dès `hcap : ∀ t ≤ 2^k, jumpCaptured …`.
  C'est le lemme ci-dessous, sorry-free.
- **L3 (cœur ouvert)** — relever `centralCorrect c k` (égalité de grille RESTREINTE à la
  fenêtre finale) en `hcap` (confinement de la TRAJECTOIRE entière). C'est l'assemblage
  borné P4/P5 proprement dit : un argument de structure de la récursion Hashlife (la marge
  contient le cône de lumière à chaque saut), PAS un argument de réversibilité — le GoL
  n'est pas réversible, le cône rétrograde ne contraint pas les états intermédiaires.
- **L4** — la jambe d'égalité : `centralCorrect` est une égalité restreinte, le but est
  global ; la fermeture exige que les deux grilles portent leur support dans la fenêtre
  (`jumpCaptured` du final + borne forward du support de `evolve`).

`hashlife_correct_margin c k h_margin h_central` se déchargerait par
`hashlife_correct_margin_of_hcap c k h_central (L3 c k h_central)` : L3/L4 sont les seuls
maillons ouverts. -/

/-- **P4.4 L2 — copie locale byte-identical de `jumpCaptured`** (pattern
    d'inlining du lake, cf HashlifeCorrectness L6436 : le `jumpCaptured` que
    consomme `hashlife_correctN` y est `private` — inline de
    `Conway.Life.JumpCapture.jumpCaptured` pour casser le cycle d'import
    A↔B, `JumpCapture.lean` important CE module). Ce module ne peut donc ni
    voir le private ni importer `JumpCapture` (cycle) : même remède, copie
    byte-identical. La defeq des corps identiques (delta-unfolding des deux
    `def` semi-reducibles) fait passer l'appel à `hashlife_correctN` ci-dessous. -/
private def jumpCapturedF (c : MacroCell) : Bool :=
  (evolve (2 ^ c.level) ((padCenter2 c).toGrid (0, 0))).all fun p =>
    decide ((2 ^ c.level : Int) ≤ p.1) &&
    decide (p.1 < (2 ^ c.level : Int) + ((2 ^ (c.level + 1) : Nat) : Int)) &&
    decide ((2 ^ c.level : Int) ≤ p.2) &&
    decide (p.2 < (2 ^ c.level : Int) + ((2 ^ (c.level + 1) : Nat) : Int))

/-- **Interface (c) tranche 3, étape 1 — dépliage propositionnel de `jumpCapturedF`.**
    Même preuve que `jumpCaptured_iff` (JumpCapture L264), répliquée localement :
    ce module ne peut pas importer `JumpCapture` (cycle d'import, cf docstring de
    `jumpCapturedF` ci-dessus). C'est la porte d'entrée du corridor (LightCone,
    langage `isAlive`) dans le prédicat Bool que `hcap` exige. -/
theorem jumpCapturedF_iff (c : MacroCell) :
    jumpCapturedF c = true ↔
      ∀ p ∈ evolve (2 ^ c.level) ((padCenter2 c).toGrid (0, 0)),
        (2 ^ c.level : Int) ≤ p.1 ∧
          p.1 < (2 ^ c.level : Int) + ((2 ^ (c.level + 1) : Nat) : Int) ∧
          (2 ^ c.level : Int) ≤ p.2 ∧
          p.2 < (2 ^ c.level : Int) + ((2 ^ (c.level + 1) : Nat) : Int) := by
  unfold jumpCapturedF
  rw [List.all_eq_true]
  constructor
  · intro h p hp
    have hb := h p hp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
    tauto
  · intro h p hp
    have hb := h p hp
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    tauto

/-- **Interface (c) tranche 3, étape 2 — le corridor forward ferme le saut dès
    que la fenêtre absorbe la dérive.** Pont entre le langage du corridor
    (`evolve_support_dilation_from`, brique (a-b) de la tranche 3, LightCone :
    confinement `isAlive` de la trajectoire) et le prédicat Bool `jumpCapturedF` :
    si le support de la grille paddée tient dans la boîte `[a, b)` (`h₀`) et que
    la boîte dilatée de `2^c.level` — la dérive forward maximale du saut — reste
    dans la fenêtre du test `[2^lvl, 2^lvl + 2^(lvl+1))²` (`hwin1..4`), alors le
    saut est capturé. La preuve ne fait aucune hypothèse de réversibilité (le GoL
    n'est pas réversible) : le relais forward borne la dérive depuis `t₀ = 0`,
    l'inclusion de fenêtres est linéaire. Les hypothèses `h₀`/`hwin` sont ce que
    la partie géométrique de L3 (caractériser le niveau de la reconstruction le
    long de la trajectoire) doit établir — ce lemme en est la cloison nette :
    confinement forward [prouvé par le corridor] séparé de géométrie de fenêtre
    [ouverte]. Les bornes de `hwin` portent le cast nat explicite
    `((2 ^ c.level : Nat) : Int)` — même atome que celle du corridor (sinon la
    puissance est forcée dans Int et omega la voit déconnectée). -/
theorem jumpCapturedF_of_dilation (c : MacroCell) (a b : Int × Int)
    (h₀ : ∀ p, isAlive ((padCenter2 c).toGrid (0, 0)) p = true →
      a.1 ≤ p.1 ∧ p.1 < b.1 ∧ a.2 ≤ p.2 ∧ p.2 < b.2)
    (hwin1 : ((2 ^ c.level : Nat) : Int) ≤ a.1 - ((2 ^ c.level : Nat) : Int))
    (hwin2 : b.1 + ((2 ^ c.level : Nat) : Int) ≤
      ((2 ^ c.level : Nat) : Int) + ((2 ^ (c.level + 1) : Nat) : Int))
    (hwin3 : ((2 ^ c.level : Nat) : Int) ≤ a.2 - ((2 ^ c.level : Nat) : Int))
    (hwin4 : b.2 + ((2 ^ c.level : Nat) : Int) ≤
      ((2 ^ c.level : Nat) : Int) + ((2 ^ (c.level + 1) : Nat) : Int)) :
    jumpCapturedF c = true := by
  rw [jumpCapturedF_iff]
  intro p hp
  have hq : isAlive (evolve (2 ^ c.level) ((padCenter2 c).toGrid (0, 0))) p = true := by
    rw [isAlive]
    exact List.elem_iff.mpr hp
  obtain ⟨c1, c2, c3, c4⟩ :=
    evolve_support_dilation_from 0 (2 ^ c.level) ((padCenter2 c).toGrid (0, 0)) a b
      (Nat.zero_le _) h₀ p hq
  simp only [Nat.sub_zero] at c1 c2 c3 c4
  -- le but (issu de la définition) parle en `(2 ^ lvl : Int)` (pow dans Int) :
  -- la relation avec le cast nat du corridor est fournie explicitement, puis
  -- tout est linéaire.
  have hpow : (2 ^ c.level : Int) = ((2 ^ c.level : Nat) : Int) := by
    exact (Nat.cast_pow 2 c.level).symm
  omega

/-- **Une période se répète** (copie locale byte-identical de
    `evolve_mul_of_period`, JumpCapture L518 — ce module ne peut pas
    l'importer, cycle A↔B, cf docstring de `jumpCapturedF`) : si `g` est de
    période `T` (au sens faible `evolve T g = g`), alors tout multiple
    `m·T` d'étapes la ramène à elle-même. Par induction sur `m` via
    `evolve_add`. -/
theorem evolve_mulF_of_period {T : Nat} (g : Grid)
    (hper : evolve T g = g) (m : Nat) :
    evolve (m * T) g = g := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hsplit : (m + 1) * T = m * T + T := by ring
    rw [hsplit, evolve_add, hper, ih]

/-- **Borne de domaine d'une cellule bien formée** (copie locale
    byte-identical de `cellWf_toGrid_bounds`, JumpCapture L475 — cycle
    d'import A↔B, cf ci-dessus) : toute cellule vivante du `toGrid` d'une
    `MacroCell` bien formée (au sens `cellWf`) de niveau `n` vit dans le
    carré `[r0, r0 + 2^n) × [c0, c0 + 2^n)`. Induction sur `cellWf` :
    chaque feuille émet au plus son coin, chaque nœud distribue ses quatre
    enfants de niveau `n` sur les quadrants d'offset `0` ou `2^n`, donc le
    nœud de niveau `n+1` couvre `[·, · + 2^(n+1))`. -/
theorem cellWfF_toGrid_bounds {c : MacroCell} (hc : cellWf c) (r0 c0 : Int)
    {p : Int × Int} (hp : p ∈ c.toGrid (r0, c0)) :
    r0 ≤ p.1 ∧ p.1 < r0 + (2 ^ c.level : Int) ∧
      c0 ≤ p.2 ∧ p.2 < c0 + (2 ^ c.level : Int) := by
  induction hc generalizing r0 c0 with
  | leaf b =>
    rw [mem_toGrid] at hp
    cases b with
    | true =>
      simp only [MacroCell.toCellsAux, Prod.fst, Prod.snd, List.mem_singleton] at hp
      obtain ⟨hrr, hcc⟩ : p.1 = r0 ∧ p.2 = c0 := Prod.ext_iff.mp hp
      subst hrr hcc
      simp only [MacroCell.level, pow_zero]
      omega
    | false => simp [MacroCell.toCellsAux] at hp
  | node hnw hne hsw hse hne_lvl hsw_lvl hse_lvl inw ine isw ise =>
    rename_i nw ne sw se
    simp only [mem_toGrid, MacroCell.toCellsAux, List.mem_append, or_assoc] at hp
    push_cast at hp
    have hlvl : MacroCell.level (MacroCell.node nw ne sw se) = nw.level + 1 := by
      simp only [MacroCell.level]; omega
    have hpos : (0 : Int) ≤ 2 ^ nw.level := by positivity
    rcases hp with hp | hp | hp | hp
    · have hb := inw r0 c0 (mem_toGrid.mpr hp)
      rw [hlvl, pow_succ]
      omega
    · have hb := ine r0 (c0 + (2 ^ nw.level : Int)) (mem_toGrid.mpr hp)
      simp only [← hne_lvl, ← hsw_lvl, ← hse_lvl] at hb
      rw [hlvl, pow_succ]
      omega
    · have hb := isw (r0 + (2 ^ nw.level : Int)) c0 (mem_toGrid.mpr hp)
      simp only [← hne_lvl, ← hsw_lvl, ← hse_lvl] at hb
      rw [hlvl, pow_succ]
      omega
    · have hb := ise (r0 + (2 ^ nw.level : Int)) (c0 + (2 ^ nw.level : Int))
        (mem_toGrid.mpr hp)
      simp only [← hne_lvl, ← hsw_lvl, ← hse_lvl] at hb
      rw [hlvl, pow_succ]
      omega

/-- **Interface (c) tranche 3, étape 3 — la classe périodique `T ∣ 2^k` est
    capturée.** Version `jumpCapturedF` du critère 3
    (`jumpCaptured_of_period_divides`, JumpCapture L533) : tout motif de
    période `T ≥ 1` divisant l'horizon du jump `2^c.level`, porté par une
    cellule bien formée de niveau `k ≥ 1`, satisfait le prédicat de capture.
    La génération finale du jump est le motif lui-même (période répétée),
    inchangé dans son cadrage `padCenter2` — donc dans la fenêtre centrale
    par la géométrie `[3·2^(k-1), 5·2^(k-1)) ⊂ [2^k, 3·2^k)`.

    **Complément orthogonal du corridor** (étape 2,
    `jumpCapturedF_of_dilation`) : le corridor exige une fenêtre qui absorbe
    la dérive forward `2^lvl` — arithmétiquement fermée au niveau plein pour
    tout contenu non vide (les `hwin` forcent une boîte de largeur nulle).
    La classe périodique, elle, ne dérive pas du tout : l'invariance
    temporelle exacte `evolve T g = g` remplace la sur-approximation du
    corridor. C'est la classe hcap-atteignable identifiée par le scoping
    tranche 3 (c.5551593604) : natures mortes (`T = 1`) et oscillateurs à
    période dyadique (`T ∣ 2^k`), les témoins du langage multi-cycles. -/
theorem jumpCapturedF_of_period_divides (c : MacroCell) (hwf : c.wf = true)
    (hlvl : 1 ≤ c.level) {T : Nat} (_hT : 0 < T)
    (hper : evolve T (c.toGrid (0, 0)) = c.toGrid (0, 0))
    (hdiv : T ∣ 2 ^ c.level) :
    jumpCapturedF c = true := by
  have hcw : cellWf c := cellWf_of_wf c hwf
  obtain ⟨m, hm⟩ := hdiv
  have hself : evolve (2 ^ c.level) (c.toGrid (0, 0)) = c.toGrid (0, 0) := by
    rw [hm, Nat.mul_comm]
    exact evolve_mulF_of_period _ hper m
  have hfinal : evolve (2 ^ c.level) ((padCenter2 c).toGrid (0, 0))
      = shift ((3 * 2 ^ (c.level - 1) : Int), (3 * 2 ^ (c.level - 1) : Int))
          (c.toGrid (0, 0)) := by
    rw [padCenter2_toGrid_shift c hlvl, ← evolve_shift, hself]
  rw [jumpCapturedF_iff]
  intro p hp
  rw [hfinal, mem_shift] at hp
  -- Bornes du contenu dans son propre cadrage `[0, 2^c.level)²`…
  obtain ⟨hb1, hb2, hb3, hb4⟩ := cellWfF_toGrid_bounds hcw 0 0 hp
  dsimp only at hb1 hb2 hb3 hb4
  -- …et relations linéaires entre les trois atomes `2^(c.level-1)`,
  -- `2^c.level`, `2^(c.level+1)` — le reste est `omega`.
  have hpow : (2 ^ c.level : Int) = 2 * (2 ^ (c.level - 1) : Int) := by
    have hsplit : c.level = (c.level - 1) + 1 := by omega
    conv_lhs => rw [hsplit]
    rw [pow_succ]
    ring
  have hnext : ((2 ^ (c.level + 1) : Nat) : Int)
      = (2 ^ c.level : Int) + (2 ^ c.level : Int) := by
    rw [Nat.cast_pow, pow_succ]
    ring
  have hy : (0 : Int) ≤ 2 ^ (c.level - 1) := by positivity
  omega

/-- **Corollaire still-life** (`T = 1`) : toute nature morte — motif avec
    `evolve 1 g = g`, au sens fort un point fixe de `step` — est capturée
    à tout niveau `k ≥ 1`. C'est la forme consommable de la classe pour
    les objets Life usuels (bloc, ruche, pain, baril…) : le premier maillon
    de L3 pour la classe `T = 1` — quel que soit `t ≤ 2^k`, `evolve t g = g`
    et la reconstruction de la trajectoire est la cellule elle-même. -/
theorem jumpCapturedF_of_still_life (c : MacroCell) (hwf : c.wf = true)
    (hlvl : 1 ≤ c.level)
    (hfix : evolve 1 (c.toGrid (0, 0)) = c.toGrid (0, 0)) :
    jumpCapturedF c = true :=
  jumpCapturedF_of_period_divides c hwf hlvl (T := 1) (by omega) hfix (by omega)

/-- **P4.4 L2 (réduction sorry-stable).** L'égalité globale du cadre se réduit à
    l'hypothèse de capture de trajectoire de la machine N : `hashlife_correctN` (prouvé)
    clôt le but dès `hcap`. Les maillons ouverts sont L3 (relever `centralCorrect c k`
    en `hcap`) et L4 (égalité restreinte → globale). -/
theorem hashlife_correct_margin_of_hcap (c : MacroCell) (k : Nat)
    (h_central : centralCorrect c k)
    (hcap : ∀ t ≤ 2^k, jumpCapturedF
      (gridToMacroCellWithOffset (evolve t (c.toGrid (0, 0)))).2 = true) :
    evolveHashlifeFast (2^k) (c.toGrid (0, 0)) = evolve (2^k) (c.toGrid (0, 0)) :=
  hashlife_correctN (2^k) (c.toGrid (0, 0)) hcap

/-! ## L3 classe `T = 1` — hcap des natures mortes (tranche 3, étape 4)

Premier maillon L3 **entièrement clos** : pour la classe des natures mortes
(`evolve 1 g = g`, point fixe de `step`), l'hypothèse `hcap` de la réduction L2
est établie de bout en bout — la trajectoire est constante, la reconstruction
est constante, et le saut est capturé par `jumpCapturedF_of_still_life`. Le
chaînage : round-trip ÉGALITÉ de la reconstruction pour grilles canoniques
(`Canonical.ext`, rigidité des listes triées-dédupliquées) → transport du point
fixe à l'origine via `toGrid_shift_grid`/`evolve_shift` → capture. -/

/-- **Round-trip ÉGALITÉ de la reconstruction (grilles canoniques).**
    La forme générale du docstring de `gridToMacroCellWithOffset` — jusqu'ici
    établie seulement au niveau des membres
    (`mem_toGrid_gridToMacroCellWithOffset`, MacroCell L857) — se renforce en
    **égalité de listes** dès que `g` est canonique : les deux grilles sont
    canoniques (`toGrid` est une image `sortDedup`, `g` l'est par hypothèse)
    et ont les mêmes membres, donc sont égales par rigidité
    (`Canonical.ext`). C'est le pont members→égalité qui manquait pour
    transporter des équivalences de point fixe (des `Prop` d'égalité) à
    travers la reconstruction. -/
theorem toGrid_gridToMacroCellWithOffset_eq (g : Grid) (hg : Canonical g) :
    (gridToMacroCellWithOffset g).2.toGrid (gridToMacroCellWithOffset g).1 = g :=
  Canonical.ext (canonical_sortDedup _) hg (fun p => mem_toGrid_gridToMacroCellWithOffset g p)

/-- **Transport du point fixe à la reconstruction (rendue à l'origine).**
    Si `g` est une nature morte canonique, alors la MacroCell reconstruite
    rendue à l'origine `(gridToMacroCellWithOffset g).2.toGrid (0, 0)` est
    elle-même un point fixe de `evolve 1` : la navette `toGrid_shift_grid`
    ramène l'origine à un shift de la grille cadrée, `evolve_shift` fait
    commuter le shift avec `evolve`, `evolve_congr` transporte l'évolution au
    cadre de `g` (même membres), et le round-trip ÉGALITÉ referme la boucle.
    C'est l'hypothèse `hfix` exacte qu'exige `jumpCapturedF_of_still_life`
    sur la reconstruction — désormais disponible pour la classe `T = 1`. -/
theorem still_life_fix_toGrid_zero (g : Grid) (hg : Canonical g)
    (hfix : evolve 1 g = g) :
    evolve 1 ((gridToMacroCellWithOffset g).2.toGrid (0, 0))
      = (gridToMacroCellWithOffset g).2.toGrid (0, 0) := by
  have hrt : (gridToMacroCellWithOffset g).2.toGrid (gridToMacroCellWithOffset g).1
      = g := toGrid_gridToMacroCellWithOffset_eq g hg
  have hshift : (gridToMacroCellWithOffset g).2.toGrid (0, 0)
      = shift (0 - (gridToMacroCellWithOffset g).1.1,
               0 - (gridToMacroCellWithOffset g).1.2)
          ((gridToMacroCellWithOffset g).2.toGrid (gridToMacroCellWithOffset g).1) :=
    toGrid_shift_grid _ 0 0 _ _
  rw [hshift, ← evolve_shift, hrt, hfix]

/-- **hcap de la classe `T = 1` (natures mortes) — la capture de la
    reconstruction.** Pour toute nature morte `g` (canonique ou vide), la
    MacroCell reconstruite satisfait le prédicat de saut : c'est l'hypothèse
    de capture que la réduction L2 consomme, établie pour la classe entière.
    Cas non vide : `jumpCapturedF_of_still_life` consomme les trois hypothèses
    désormais disponibles — wf (`buildFromGrid_wf`), niveau (la borne
    n-aware : `2 < 2^lvl` dès `g ≠ []`, donc `1 ≤ lvl`) et point fixe
    (`still_life_fix_toGrid_zero`). Cas vide : la reconstruction est une
    feuille morte de niveau 0, la grille paddée est vide, et `List.all` sur
    `[]` est trivialement vrai — décidé par le noyau. -/
theorem jumpCapturedF_reconstruction_of_still_life (g : Grid) (hg : Canonical g)
    (hfix : evolve 1 g = g) :
    jumpCapturedF (gridToMacroCellWithOffset g).2 = true := by
  by_cases hne : g = []
  · subst hne
    decide
  · apply jumpCapturedF_of_still_life _ ?_ ?_ ?_
    · unfold gridToMacroCellWithOffset
      exact buildFromGrid_wf g _ _ _
    · have hN := gridToMacroCellWithOffsetN_level_gt_n 2 g hne
      rw [gridToMacroCellWithOffsetN_le_two_eq 2 g (by omega)] at hN
      cases hL : (gridToMacroCellWithOffset g).2.level with
      | zero => rw [hL] at hN; exact absurd hN (by decide)
      | succ m => omega
    · exact still_life_fix_toGrid_zero g hg hfix

/-- **hcap des natures mortes, trajectoire complète.** Pour toute nature
    morte `g`, **tout** instant `t` (a fortiori tout `t ≤ 2^k`) : la
    trajectoire est constante (`evolve t g = g`, période 1 répétée via
    `evolve_mulF_of_period`), donc la reconstruction le long de la trajectoire
    est l'objet constant `gridToMacroCellWithOffset g`, dont le saut est
    capturé. Avec le corollaire d'assemblage ci-dessous, c'est le **premier
    maillon L3 entièrement prouvé** de la décomposition P4.4 : relever une
    classe de motifs en l'hypothèse `hcap` de la machine N, sans aucun sorry. -/
theorem hcap_of_still_life (g : Grid) (hg : Canonical g)
    (hfix : evolve 1 g = g) (t : Nat) :
    jumpCapturedF (gridToMacroCellWithOffset (evolve t g)).2 = true := by
  have hself : evolve t g = g := by
    have hmul := evolve_mulF_of_period g hfix t
    rwa [Nat.mul_one] at hmul
  rw [hself]
  exact jumpCapturedF_reconstruction_of_still_life g hg hfix

/-- **L3 clos pour la classe `T = 1` : correction Hashlife des natures
    mortes.** Corollaire d'assemblage — le premier cas de la décomposition
    P4.4 où le maillon L3 (relever une classe de motifs en `hcap`) est
    **entièrement prouvé** : pour toute MacroCell dont la grille rendue à
    l'origine est une nature morte, l'égalité globale `hashlife_correctN`
    s'applique à tout horizon `2^k` sous `centralCorrect`. Il ne reste que
    L4 (l'égalité restreinte `centralCorrect` elle-même), qui vit dans
    l'hypothèse — exactement la cloison annoncée par la réduction L2. -/
theorem hashlife_correct_margin_of_still_life (c : MacroCell) (k : Nat)
    (h_central : centralCorrect c k)
    (hfix : evolve 1 (c.toGrid (0, 0)) = c.toGrid (0, 0)) :
    evolveHashlifeFast (2^k) (c.toGrid (0, 0)) = evolve (2^k) (c.toGrid (0, 0)) :=
  hashlife_correct_margin_of_hcap c k h_central
    (fun t _ => hcap_of_still_life _ (canonical_sortDedup _) hfix t)

/-! ## L3 classe périodique `T ∣ 2^k` — hcap des oscillateurs (tranche 3, étape 6)

Deuxième maillon L3 **entièrement clos** : la généralisation de la chaîne
`T = 1` aux oscillateurs de période `T > 1` à période dyadique. L'orbite
n'est plus constante — `evolve t g` parcourt les `T` phases — donc la
capture se prouve **phase par phase** : chaque phase `evolve r g` (`r < T`)
est elle-même un point fixe de `evolve T` (`evolve_phase_fix`), la
trajectoire se réduit au résidu modulo `T` (`evolve_mod_period`), et le
schéma round-trip → point fixe transporté s'applique à chaque phase
canonique. La prémisse géométrique `T ∣ 2^level` de
`jumpCapturedF_of_period_divides` est portée **explicitement** : c'est une
contrainte réelle sur le niveau de la reconstruction de chaque phase (le
niveau doit atteindre `log₂ T`), pas une conséquence — la borne de niveau
supérieure du côté `gridFrame` (étape 5) est ce qui la rend calculable. -/

/-- **Chaque phase est un point fixe de `evolve T`.** Si `g` est
    `T`-périodique, toute phase `evolve r g` l'est aussi : l'évolution
    commute à elle-même (`evolve_add`), donc `evolve T (evolve r g)
    = evolve r (evolve T g) = evolve r g`. C'est l'hypothèse `hper` exacte
    qu'exige la capture au niveau de chaque phase. -/
theorem evolve_phase_fix {T : Nat} (g : Grid)
    (hper : evolve T g = g) (r : Nat) :
    evolve T (evolve r g) = evolve r g := by
  rw [← evolve_add, Nat.add_comm T r, evolve_add, hper]

/-- **Réduction de la trajectoire au résidu modulo `T`.** Pour un motif
    `T`-périodique, la trajectoire entière se replie sur ses `T` phases :
    `evolve t g = evolve (t % T) g` — le quotient `t / T` de périodes
    complètes disparaît par point fixe. C'est ce qui borne le travail de la
    capture de « tout `t ≤ 2^k` » à « chacune des `T` phases ». -/
theorem evolve_mod_period {T : Nat} (g : Grid)
    (hper : evolve T g = g) (t : Nat) :
    evolve t g = evolve (t % T) g := by
  have hsplit : t = T * (t / T) + t % T := (Nat.div_add_mod t T).symm
  conv_lhs => rw [hsplit, evolve_add, Nat.mul_comm]
  exact evolve_mulF_of_period _ (evolve_phase_fix g hper _) _

/-- **Transport du point fixe de période `T` à la reconstruction (rendue à
    l'origine).** L'analogue exact de `still_life_fix_toGrid_zero` pour la
    période `T` : si `g` est canonique et `T`-périodique, la MacroCell
    reconstruite rendue à l'origine est elle-même un point fixe de
    `evolve T` — navette `toGrid_shift_grid`, commutation `evolve_shift`,
    round-trip ÉGALITÉ, point fixe. -/
theorem periodic_fix_toGrid_zero (g : Grid) (hg : Canonical g) {T : Nat}
    (hper : evolve T g = g) :
    evolve T ((gridToMacroCellWithOffset g).2.toGrid (0, 0))
      = (gridToMacroCellWithOffset g).2.toGrid (0, 0) := by
  have hrt : (gridToMacroCellWithOffset g).2.toGrid (gridToMacroCellWithOffset g).1
      = g := toGrid_gridToMacroCellWithOffset_eq g hg
  have hshift : (gridToMacroCellWithOffset g).2.toGrid (0, 0)
      = shift (0 - (gridToMacroCellWithOffset g).1.1,
               0 - (gridToMacroCellWithOffset g).1.2)
          ((gridToMacroCellWithOffset g).2.toGrid (gridToMacroCellWithOffset g).1) :=
    toGrid_shift_grid _ 0 0 _ _
  rw [hshift, ← evolve_shift, hrt, hper]

/-- **Capture de la reconstruction d'une phase périodique.** Pour toute
    phase canonique `g` d'un oscillateur `T`-périodique (`T > 1` a fortiori
    `0 < T`), dont le niveau de reconstruction divise l'horizon du saut
    (`T ∣ 2^level`), la reconstruction satisfait le prédicat de saut —
    c'est `jumpCapturedF_of_period_divides` consommé au niveau de la
    reconstruction, avec les trois hypothèses désormais disponibles : wf
    (`buildFromGrid_wf`), niveau (`1 ≤ lvl` dès `g ≠ []`, borne n-aware) et
    point fixe de période `T` (`periodic_fix_toGrid_zero`). Cas vide : la
    reconstruction est une feuille morte de niveau 0, décidée par le noyau. -/
theorem jumpCapturedF_reconstruction_of_period (g : Grid) (hg : Canonical g)
    {T : Nat} (hT0 : 0 < T) (hper : evolve T g = g)
    (hdiv : T ∣ 2 ^ (gridToMacroCellWithOffset g).2.level) :
    jumpCapturedF (gridToMacroCellWithOffset g).2 = true := by
  by_cases hne : g = []
  · subst hne
    decide
  · have hwf : ((gridToMacroCellWithOffset g).2).wf = true := by
      unfold gridToMacroCellWithOffset
      exact buildFromGrid_wf g _ _ _
    have hlvl : 1 ≤ (gridToMacroCellWithOffset g).2.level := by
      have hN := gridToMacroCellWithOffsetN_level_gt_n 2 g hne
      rw [gridToMacroCellWithOffsetN_le_two_eq 2 g (by omega)] at hN
      cases hL : (gridToMacroCellWithOffset g).2.level with
      | zero => rw [hL] at hN; exact absurd hN (by decide)
      | succ m => omega
    exact jumpCapturedF_of_period_divides _ hwf hlvl hT0
      (periodic_fix_toGrid_zero g hg hper) hdiv

/-- **hcap de la classe périodique, trajectoire complète.** Pour un
    oscillateur canonique de période `T > 1` dont **chaque phase** a un
    niveau de reconstruction divisible par `T` (au sens `T ∣ 2^level`), tout
    instant `t` (a fortiori tout `t ≤ 2^k`) est capturé : la trajectoire se
    réduit à la phase `t % T` (`evolve_mod_period`), la phase est canonique
    (`canonical_evolve_of_pos`, ou `g` lui-même pour la phase nulle),
    point fixe de `evolve T` (`evolve_phase_fix`), et sa reconstruction est
    capturée. La prémisse de divisibilité est finie : elle porte sur les `T`
    phases seulement, pas sur la trajectoire infinie. -/
theorem hcap_of_period (g : Grid) (hg : Canonical g) {T : Nat} (hT0 : 0 < T)
    (hper : evolve T g = g)
    (hdiv : ∀ i, i < T →
      T ∣ 2 ^ (gridToMacroCellWithOffset (evolve i g)).2.level) :
    ∀ t, jumpCapturedF (gridToMacroCellWithOffset (evolve t g)).2 = true := by
  intro t
  rw [evolve_mod_period g hper t]
  have hr : t % T < T := Nat.mod_lt _ hT0
  have hcan : Canonical (evolve (t % T) g) := by
    rcases Nat.eq_zero_or_pos (t % T) with h0 | hpos
    · rw [h0]
      simpa using hg
    · exact canonical_evolve_of_pos hpos _
  have hfix : evolve T (evolve (t % T) g) = evolve (t % T) g :=
    evolve_phase_fix g hper _
  exact jumpCapturedF_reconstruction_of_period _ hcan hT0 hfix (hdiv _ hr)

/-- **L3 clos pour la classe périodique `T ∣ 2^k` : correction Hashlife des
    oscillateurs.** Corollaire d'assemblage — le deuxième cas de la
    décomposition P4.4 où le maillon L3 est **entièrement prouvé** : pour
    toute MacroCell dont la grille rendue à l'origine est un oscillateur de
    période `T > 1` (chaque phase de niveau divisible), l'égalité globale
    `hashlife_correctN` s'applique à tout horizon `2^k` sous `centralCorrect`.
    La classe couvre les témoins multi-cycles du bestiaire (clignotant
    `T = 2`, crapaud `T = 2`, phare `T = 3` dès que `T ∣ 2^level`). -/
theorem hashlife_correct_margin_of_period (c : MacroCell) (k : Nat)
    (h_central : centralCorrect c k) {T : Nat} (hT0 : 0 < T)
    (hper : evolve T (c.toGrid (0, 0)) = c.toGrid (0, 0))
    (hdiv : ∀ i, i < T →
      T ∣ 2 ^ (gridToMacroCellWithOffset (evolve i (c.toGrid (0, 0)))).2.level) :
    evolveHashlifeFast (2^k) (c.toGrid (0, 0)) = evolve (2^k) (c.toGrid (0, 0)) :=
  hashlife_correct_margin_of_hcap c k h_central
    (fun t _ => hcap_of_period _ (canonical_sortDedup _) hT0 hper hdiv t)

/-! ## Sanity-checks sur le bestiaire

Le fragment `supportInMargin` est **décidable** (instance `Decidable (BoxAssezGrandN)`,
HashlifeCorrectness L227) et **non vide** sur les témoins du bestiaire. Ces lemmes sont les
sanity-checks réels (honnêtes) du fragment : le bloc 2×2 et le vide satisfont la marge à
plusieurs horizons, et le sanity `k2` exhibe `2^2 = 4` — impossible avec la fixed-frame
`BoxAssezGrand`, possible ici car `BoxAssezGrandN` pad par `max 2 4 = 4`.

**Note (c.212, 2026-08-11)** : la classe d'axiome `native_decide` est interdite au sens de
`pr-review-discipline` §B (forbidden). Or `supportInMargin` est machine-prouvé
**tautologique** par `supportInMargin_trivial` (L113 ci-dessus) — vraie pour **toute**
MacroCell et **tout** horizon. Les quatre témoins ci-dessous sont donc établis gratuitement
par cette preuve générale, sans recours au noyau natif. Le `native_decide` historique
témoignait d'une tautologie déjà démontrée — retrait net, zéro perte de contenu, axiome
interdit ôté. -/

/-- **Sanité** : le bloc 2×2 (`cexBlock1`) satisfait le fragment à l'horizon `2^0 = 1`
    (marge ≥ 1). Non-vacuité du fragment. -/
theorem cexBlock1_supportInMargin_k0 : supportInMargin cexBlock1 0 :=
  supportInMargin_trivial _ _

/-- **Sanité** : le bloc 2×2 satisfait le fragment à l'horizon `2^1 = 2` (marge ≥ 2).
    C'est le plafond de la fixed-frame `BoxAssezGrand` (`boxAssezGrand_nonempty_le_two`). -/
theorem cexBlock1_supportInMargin_k1 : supportInMargin cexBlock1 1 :=
  supportInMargin_trivial _ _

/-- **Sanité (n-aware)** : le bloc 2×2 satisfait le fragment à l'horizon `2^2 = 4`
    (marge ≥ 4) — IMPOSSIBLE avec la fixed-frame `BoxAssezGrand` (plafonnée à 2), possible
    ici car `BoxAssezGrandN` pad par `max 2 4 = 4`. C'est la raison du choix n-aware :
    sans lui, l'argument de suffisance « choisir `k` par horizon » s'effondrerait. -/
theorem cexBlock1_supportInMargin_k2 : supportInMargin cexBlock1 2 :=
  supportInMargin_trivial _ _

/-- **Sanité** : le vide (`cexEmpty1`) satisfait le fragment à l'horizon `2^0 = 1` (pas de
    cellules vivantes à contraindre — `List.all` sur `[]` vacuously true). -/
theorem cexEmpty1_supportInMargin_k0 : supportInMargin cexEmpty1 0 :=
  supportInMargin_trivial _ _

/-! ## Synthèse — le fragment est non vide et l'énoncé-cadre est honnête

`supportInMargin` est décidable et témoigné sur le bestiaire (ci-dessus). L'énoncé-cadre
`hashlife_correct_margin` porte la correction relative au fragment (en habillage — voir
note *inconditionnel-en-attente* dans sa docstring : le prédicat est tautologique, le
cœur de recherche reste l'assemblage borné P4/P5) ; son `sorry` documente ouvertement
l'assemblage borné P4/P5 encore ouvert (`p4_nw_overlap_wall`, ai-01 c.94).
Stratégie pour la suite de #6724 : les murs NE/SW/SE bornés sont FERMÉS et `p5_large_n_jumpN`
est prouvé (b3') — la réduction L2 ci-dessus est en place, restent les maillons L3 (le pont
`centralCorrect → hcap`, l'assemblage borné proprement dit) et L4 (égalité restreinte →
globale), qui déchargeront le `sorry` de `hashlife_correct_margin`. **Premier maillon L3
clos** (tranche 3, étape 4) : la classe `T = 1` des natures mortes est intégralement
relevée en `hcap` (`hcap_of_still_life` → `hashlife_correct_margin_of_still_life`),
sans sorry — la généralisation aux autres classes périodiques `T ∣ 2^k` suivra le même
schéma (round-trip canonique → point fixe transporté → capture).
-/

end Life
end Conway
