/-
Copyright (c) 2026 CoursIA. All rights reserved.
Distributed under the Apache 2.0 License as described in the LICENSE file.

## P5 — géométrie de capture du jump Hashlife (#6724, finding 2026-08-07)

Formalisation du finding d'analyse posté sur #6724 (commentaire ai-01
2026-08-07) : l'hypothèse `BoxAssezGrandN` des théorèmes P5 est une
**tautologie**, et la question géométrique réellement ouverte est la
**capture par la fenêtre centrale** (le `restrictGridTo` de P4), pas la
non-interférence au bord externe que mesurent les lemmes de marge existants
(`padCenter2_margin_ge_jumpReach`, `evolve_reach_within_padCenter2_margin`).

### 1. La tautologie

`gridFrameN n g` rembourre par `max 2 n` et `box_assez_grandN` vérifie
`cellMargin n` sur le cadre construit par ce même rembourrage : le côté
proche est non strict (`r0 + n ≤ r`), donc la marge vaut exactement
`max 2 n ≥ n` — toujours vraie ; l'arrondi du côté à `2^lvl` ne fait
qu'agrandir le côté lointain. `box_assez_grandN_trivial` le prouve pour
toute grille et tout `n`. Conséquences : `p5_large_n_jumpN` équivaut à
l'énoncé inconditionnel (`p5_large_n_jumpN_iff_unconditional`), et le
fragment `supportInMargin` de `HashlifeMarginFragment` (#9568) est l'espace
entier (`supportInMargin_trivial`) — l'hypothèse `h_margin` de
`hashlife_correct_margin` ne travaille pas.

### 2. L'arithmétique de capture

Après `padCenter2`, le contenu est décalé de `+3·2^(k-1)`
(`padCenter2_correct`) ; la fenêtre centrale est `[2^k, 3·2^k)`, soit une
marge de fenêtre de `2^(k-1)` par côté, plus la marge de motif 2 du cadre
fixe : slack total `2^(k-1) + 2`. Le cône de vitesse 1 atteint `2^k` en
`2^k` générations : `window_margin_lt_cone_reach` prouve
`2^(k-1) + 2 < 2^k` dès `k ≥ 3` (la machinerie cône-c=1 ne peut pas
conclure), et `window_margin_eq_cone_reach_at_two` l'égalité exacte à
`k = 2` (seul niveau exactement couvert).

### 3. Le prédicat de confinement authentique `jumpCaptured`

Le remplaçant non tautologique : la génération finale du jump reste dans la
fenêtre centrale du domaine paddé. Décidable, témoigné vrai sur bloc et
planeur (`jumpCaptured_block` / `jumpCaptured_glider`) et **faux** sur la
ligne de largeur 7 en niveau 3 (`jumpCaptured_not_trivial`) : le burst
transitoire à vitesse 1 atteint la rangée 7 < 8 (bord haut de la fenêtre) à
la génération 8 exactement — le prédicat porte une information géométrique
réelle, contrairement à `BoxAssezGrandN`.

### 4. La correction du jump sous capture

`hashlifeJump_correct_of_captured` : sous `jumpCaptured c = true`, le jump
Hashlife est exact (pas seulement clippé) — P4
(`hashlifeResult_central_correct`) donne l'égalité clippée, et la capture
rend le clip transparent (`restrictGridTo_eq_self`). C'est la brique
« un jump » que la re-signature de `p5_large_n_jumpN` consommera.
-/
import Conway.Life.HashlifeCorrectness
import Conway.Life.HashlifeMarginFragment

namespace Conway
namespace Life

open MacroCell

/-! ## 1. La tautologie `BoxAssezGrandN` (relocalisée, c.8206, #9568)

Les lemmes `box_assez_grandN_trivial` et `boxAssezGrandN_trivial` vivaient
ici avant c.8206. Ils ont été relocalisés dans
`Conway.Life.HashlifeCorrectness.Foundation` (à côté de `BoxAssezGrandN`,
L161) pour casser un cycle d'import : `JumpCapture` importe
`HashlifeMarginFragment` (pour la re-signature c.95 de
`hashlife_correctN`), et `MarginFragment` aurait eu besoin de `JumpCapture`
pour atteindre `supportInMargin_trivial`. La relocalisation place la
preuve de trivialité à côté de la définition du prédicat, et les
consommateurs existants — `p5_large_n_jumpN_iff_unconditional`, et les 4
sanity-checks du fragment — accèdent au lemme via l'import
`Conway.Life.HashlifeCorrectness` déjà présent. Le pendant
`supportInMargin_trivial` vit dans `HashlifeMarginFragment` (même imported,
L113). -/

/-- **`p5_large_n_jumpN` équivaut à la correction inconditionnelle** : sa
    signature avec l'hypothèse tautologique `BoxAssezGrandN g n` a
    exactement la même force que l'énoncé sans hypothèse. C'est le finding
    #6724 (2026-08-07) rendu machine-vérifié : la borne géométrique promise
    par l'hypothèse n'existe pas, et la preuve devrait établir la
    correction du jump pour toute grille — hors de portée du cône c=1 pour
    `lvl ≥ 3` (`window_margin_lt_cone_reach`). -/
theorem p5_large_n_jumpN_iff_unconditional :
    (∀ (n : Nat) (g : Grid), BoxAssezGrandN g n →
        n ≥ jumpSize (gridToMacroCellWithOffset g).2.level →
        evolveHashlifeFast n g = evolve n g) ↔
    (∀ (n : Nat) (g : Grid),
        n ≥ jumpSize (gridToMacroCellWithOffset g).2.level →
        evolveHashlifeFast n g = evolve n g) := by
  constructor
  · intro H n g hbig
    exact H n g (boxAssezGrandN_trivial g n) hbig
  · intro H n g _ hbig
    exact H n g hbig

/-! ## 2. L'arithmétique de capture (slack de fenêtre vs portée du cône) -/

/-- **Le slack d'échappement est strictement inférieur à la portée du cône
    dès `k ≥ 3`** : la marge de fenêtre `2^(k-1)` (contenu centré par
    `padCenter2` dans la fenêtre `[2^k, 3·2^k)`) plus la marge de motif 2
    du cadre fixe ne couvrent pas la portée `2^k` du cône de vitesse 1 sur
    `2^k` générations. La machinerie cône-c=1 existante ne peut donc pas
    fermer la correction du jump pour `lvl ≥ 3`. -/
theorem window_margin_lt_cone_reach {k : Nat} (hk : 3 ≤ k) :
    2 ^ (k - 1) + 2 < 2 ^ k := by
  have hsplit : 2 ^ k = 2 ^ (k - 1) * 2 := by
    conv_lhs => rw [show k = (k - 1) + 1 by omega]
    rw [pow_succ]
  have h4 : (4 : Nat) ≤ 2 ^ (k - 1) := by
    have h22 : (2 : Nat) ^ 2 ≤ 2 ^ (k - 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    simpa using h22
  omega

/-- **Égalité exacte à `k = 2`** : `2^(2-1) + 2 = 4 = 2^2` — le niveau 2
    est le seul où le slack couvre exactement la portée du cône ; la
    machinerie actuelle est « exactly tight » à ce niveau. -/
theorem window_margin_eq_cone_reach_at_two :
    2 ^ (2 - 1) + 2 = 2 ^ 2 := by norm_num

/-! ## 3. Marges nommées (route P5 étape 0, finding #6724 du 2026-08-10)

Le lake contient deux lemmes de marge, tous deux prouvés sorry-free, dont
les verdicts paraissent opposés parce qu'ils mesurent vers **deux
frontières différentes** :

| lemme | marge jusqu'à | valeur | vs portée `2^k` |
|---|---|---|---|
| `padCenter2_margin_ge_jumpReach` (Foundation:1201) | bord de la **cellule rembourrée** | `3·2^(k-1)` = `1.5·2^k` | surplus 1.5× |
| `window_margin_lt_cone_reach` (JumpCapture:152) | bord de la **fenêtre de résultat** | `2^(k-1)` (+2) = `0.5·2^k` | déficit 0.5× |

`2^(k+p-1) − 2^(k+p-2) = 2^(k+p-2)` = exactement une portée : le bord de
fenêtre est en retrait d'une portée entière par rapport au bord de
cellule, d'où deux ratios qui diffèrent exactement de 1
(`2 − 2^(1-p)` contre `1 − 2^(1-p)`). Corollaire : le surplus de
Foundation est **définitionnel** et ne porte aucune information sur la
capture — « le cône reste dans la cellule rembourrée » est
automatiquement vrai dès que « le cône reste dans la fenêtre » échoue
de moins d'une portée.

L'étape 0 **nomme les deux frontières** et ferme leur arithmétique
pour rendre l'illusion non reproductible (cf `supportInMargin` #9568,
même classe de piège — un énoncé vrai qui paraît dire plus qu'il ne
dit). -/

/-- **Marge du contenu au bord de la cellule rembourrée** (profondeur de
    rembourrage `p ≥ 1`). La cellule paddée fait `2^(k+p)` cellules de
    côté, le contenu (original) fait `2^k` cellules de côté centré. La
    distance du bord du contenu au bord de la cellule est donc
    `(2^(k+p) − 2^k) / 2 = 2^(k+p-1) − 2^(k-1)`. -/
def marginToPaddedCell (k p : Nat) : Nat :=
  2 ^ (k + p - 1) - 2 ^ (k - 1)

/-- **Marge du contenu au bord de la fenêtre de résultat** (profondeur
    `p`). La fenêtre centrale fait `2^(k+p-1)` cellules de côté
    (`hashlifeResult` sur la cellule paddée de niveau `k+p`), centrée
    sur `[2^(k+p-2), 3·2^(k+p-2))`. Le contenu reste centré sur
    `[2^(k-1), 2^k + 2^(k-1))`. La distance du bord du contenu au bord
    gauche de la fenêtre est donc `2^(k+p-2) − 2^(k-1)`. -/
def marginToResultWindow (k p : Nat) : Nat :=
  2 ^ (k + p - 2) - 2 ^ (k - 1)

/-- **Portée du cône de vitesse 1 sur le jump Hashlife** : `hashlifeResult`
    sur une cellule de niveau `k+p` avance `2^(k+p-2)` générations, et la
    vitesse c=1 (cône de lumière du Game of Life) atteint donc cette
    distance au bord. -/
def jumpReach (k p : Nat) : Nat :=
  2 ^ (k + p - 2)

/-- **Lemme de liaison** : la différence entre marge de cellule et
    marge de fenêtre vaut exactement la portée du cône. C'est ce qui
    rend les deux ratios (`2 − 2^(1-p)` et `1 − 2^(1-p)`) séparés
    d'exactement 1 — non une coïncidence, mais la définition de la
    fenêtre comme moitié centrale de la cellule. -/
theorem margin_liaison (k p : Nat) (hk : 1 ≤ k) (hp : 1 ≤ p) :
    marginToPaddedCell k p - marginToResultWindow k p = jumpReach k p := by
  unfold marginToPaddedCell marginToResultWindow jumpReach
  -- Goal après unfold : `(2^(k+p-1) - 2^(k-1)) - (2^(k+p-2) - 2^(k-1)) = 2^(k+p-2)`.
  -- `ring` est IMPOSSIBLE : `Nat.sub` est tronqué, ce n'est pas une opération
  -- d'anneau (Lean dit « ring failed to close »). Il faut la bound `2^(k-1) ≤
  -- 2^(k+p-2)` (= `k-1 ≤ k+p-2` = `hp`) sous la forme que `omega` consomme.
  have hle : (2 : Nat) ^ (k - 1) ≤ (2 : Nat) ^ (k + p - 2) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  -- `omega` traite `2^e` comme un ATOME opaque : sans ce pont, `2^(k+p-1)` et
  -- `2^(k+p-2)` sont deux inconnues sans relation, et la cible est hors de portee.
  have hkey : (2 : Nat) ^ (k + p - 1) = 2 * 2 ^ (k + p - 2) := by
    conv_lhs => rw [show k + p - 1 = (k + p - 2) + 1 by omega]
    ring
  omega

/-- **Étape 0 — le rembourrage ne peut pas refermer l'écart** : pour
    toute profondeur `p ≥ 1`, la marge de fenêtre reste strictement
    inférieure à la portée du cône. Formellement :
    `marginToResultWindow k p < jumpReach k p`, soit
    `2^(k+p-2) − 2^(k-1) < 2^(k+p-2)`. Découle immédiatement de
    `2^(k-1) > 0`.

    **Ce que ça décide** : la profondeur de rembourrage ne peut pas
    suffire à elle seule à fermer la capture. Le levier restant est
    **décorréler la portée du niveau**, via un paramètre `j` de Gosper
    (`hashlifeResultAt j`, à `j = level-3` au lieu de `level-2` :
    portée `2^(k-1)` au lieu de `2^(k+p-2)`, marge `2^(k-1) + 2` alors
    strictement **supérieure**). À `j = level-3` le ratio marge/portée
    devient `2 − 2^(2-p)` : **tendu à `p=2`**, **surplus strict à
    `p ≥ 3`** — `j` et rembourrage travaillent **ensemble**, ce que la
    formulation initiale « la profondeur de rembourrage ne peut pas
    aider » disait trop sèchement. Cette étape 2 fera l'objet d'une
    PR distincte ; elle n'est pas livrée ici. -/
theorem no_padding_depth_suffices (k p : Nat) (hk : 1 ≤ k) (hp : 1 ≤ p) :
    marginToResultWindow k p < jumpReach k p := by
  unfold marginToResultWindow jumpReach
  -- L'inégalité après unfold est `2^(k+p-2) - 2^(k-1) < 2^(k+p-2)`.
  -- En Nat, `A - B < A` exige `0 < A` **autant que** `0 < B`. `omega`
  -- nomme lui-même le manque dans son contre-exemple (quand il énumère
  -- des contraintes absurdes, ce sont les faits qu'on ne lui a pas donnés).
  have hbound : (2 : Nat) ^ (k - 1) ≤ 2 ^ (k + p - 2) := by
    apply Nat.pow_le_pow_right (by norm_num); omega
  have hpos : (2 : Nat) ^ (k - 1) > 0 := Nat.two_pow_pos (k - 1)
  have hjump_pos : (2 : Nat) ^ (k + p - 2) > 0 := Nat.two_pow_pos (k + p - 2)
  omega

/-! ## 4. Le clip transparent sous confinement -/

/-- `restrictGridTo` est l'identité quand toutes les cellules vivantes sont
    déjà dans la fenêtre : c'est le pont qui rend le clip de P4 transparent
    sous l'hypothèse de capture. -/
theorem restrictGridTo_eq_self (g : Grid) (lo : Int) (size : Nat)
    (h : ∀ p ∈ g, lo ≤ p.1 ∧ p.1 < lo + (size : Int) ∧
          lo ≤ p.2 ∧ p.2 < lo + (size : Int)) :
    restrictGridTo g lo size = g := by
  induction g with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨h1, h2, h3, h4⟩ := h p List.mem_cons_self
    have hps : restrictGridTo ps lo size = ps :=
      ih fun q hq => h q (List.mem_cons_of_mem p hq)
    unfold restrictGridTo at hps ⊢
    rw [List.filter_cons, if_pos (by
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      tauto), hps]

/-! ## 4. Le prédicat de confinement authentique `jumpCaptured` -/

/-- **Confinement authentique du jump** : la génération finale (`2^c.level`
    pas, l'horizon du jump) de la grille paddée `padCenter2 c` reste dans
    la fenêtre centrale `[2^c.level, 3·2^c.level)` que P4 clippe.
    Contrairement à `BoxAssezGrandN` (tautologique), ce prédicat est mesuré
    contre le domaine PROPRE de la cellule paddée — il est faux dès qu'un
    burst transitoire atteint le bord (`jumpCaptured_not_trivial`). -/
def jumpCaptured (c : MacroCell) : Bool :=
  (evolve (2 ^ c.level) ((padCenter2 c).toGrid (0, 0))).all fun p =>
    decide ((2 ^ c.level : Int) ≤ p.1) &&
    decide (p.1 < (2 ^ c.level : Int) + ((2 ^ (c.level + 1) : Nat) : Int)) &&
    decide ((2 ^ c.level : Int) ≤ p.2) &&
    decide (p.2 < (2 ^ c.level : Int) + ((2 ^ (c.level + 1) : Nat) : Int))

/-- Dépliage propositionnel de `jumpCaptured`. -/
theorem jumpCaptured_iff (c : MacroCell) :
    jumpCaptured c = true ↔
      ∀ p ∈ evolve (2 ^ c.level) ((padCenter2 c).toGrid (0, 0)),
        (2 ^ c.level : Int) ≤ p.1 ∧
          p.1 < (2 ^ c.level : Int) + ((2 ^ (c.level + 1) : Nat) : Int) ∧
          (2 ^ c.level : Int) ≤ p.2 ∧
          p.2 < (2 ^ c.level : Int) + ((2 ^ (c.level + 1) : Nat) : Int) := by
  unfold jumpCaptured
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

/-- Bloc 2×2 (nature morte) dans une cellule de niveau 2 : capturé. -/
private def blockCell2 : MacroCell :=
  buildFromGrid [(1, 1), (1, 2), (2, 1), (2, 2)] 0 0 2

/-- Planeur dans une cellule de niveau 3 : vitesse c/4 diagonale, 8
    générations = 2 cellules de déplacement — capturé. -/
private def gliderCell3 : MacroCell :=
  buildFromGrid [(1, 2), (2, 3), (3, 1), (3, 2), (3, 3)] 0 0 3

/-- Ligne horizontale de largeur 7 en rangée 0 du domaine `[0,8)²` d'une
    cellule de niveau 3 : le burst transitoire à vitesse 1 (une ligne de
    largeur `w` avance de `(w-1)/2` rangées à vitesse 1) atteint la rangée
    7 < 8 (bord de la fenêtre `[8, 24)`) à la génération 8 exactement. -/
private def lineCell3 : MacroCell :=
  buildFromGrid [(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6)] 0 0 3

/-- Le bloc est capturé (témoin niveau 2). -/
theorem jumpCaptured_block : jumpCaptured blockCell2 = true := by
  native_decide

/-- Le planeur est capturé (témoin niveau 3). -/
theorem jumpCaptured_glider : jumpCaptured gliderCell3 = true := by
  native_decide

/-- **`jumpCaptured` n'est PAS une tautologie** : la ligne de largeur 7
    s'échappe de la fenêtre à la génération finale du jump de niveau 3.
    C'est le contraste décisif avec `BoxAssezGrandN`
    (`box_assez_grandN_trivial`) : le nouveau prédicat porte une
    information géométrique réelle — et ce témoin concret confirme que la
    marge de fenêtre `2^(k-1) + 2` est effectivement franchissable par des
    motifs réels dès `k = 3` (finding #6724). -/
theorem jumpCaptured_not_trivial : jumpCaptured lineCell3 = false := by
  native_decide

/-! ## 5. Correction du jump sous capture -/

/-- **Le jump Hashlife est exact (pas seulement clippé) sous capture** :
    si la génération finale reste dans la fenêtre centrale
    (`jumpCaptured`), alors le résultat du jump — placé à l'offset central
    `(2^c.level, 2^c.level)` — est EXACTEMENT l'évolution de la grille
    paddée sur l'horizon `2^c.level`. P4
    (`hashlifeResult_central_correct`) fournit l'égalité clippée par
    `restrictGridTo` ; la capture rend le clip transparent
    (`restrictGridTo_eq_self`). C'est la brique « un jump » de la
    re-signature de `p5_large_n_jumpN` (finding #6724, voie (a)). -/
theorem hashlifeJump_correct_of_captured (c : MacroCell)
    (hwf : c.wf = true) (hlvl : 1 ≤ c.level)
    (hcap : jumpCaptured c = true) :
    (hashlifeJump c).toGrid ((2 ^ c.level : Nat), (2 ^ c.level : Nat))
      = evolve (2 ^ c.level) ((padCenter2 c).toGrid (0, 0)) := by
  have hplvl : (padCenter2 c).level = c.level + 2 := level_padCenter2 c hlvl
  have hpwf : (padCenter2 c).wf = true := wf_padCenter2 c hwf
  have hjump : hashlifeJump c = hashlifeResultAux (c.level + 2) (padCenter2 c) := by
    unfold hashlifeJump hashlifeResult
    rw [hplvl]
  have h4 : (hashlifeResultAux (c.level + 2) (padCenter2 c)).toGrid
        ((2 ^ c.level : Nat), (2 ^ c.level : Nat))
      = restrictGridTo (evolve (2 ^ c.level) ((padCenter2 c).toGrid (0, 0)))
          (2 ^ c.level : Int) (2 ^ (c.level + 1)) :=
    hashlifeResult_central_correct (padCenter2 c) c.level hpwf hplvl
  calc (hashlifeJump c).toGrid ((2 ^ c.level : Nat), (2 ^ c.level : Nat))
      = (hashlifeResultAux (c.level + 2) (padCenter2 c)).toGrid
          ((2 ^ c.level : Nat), (2 ^ c.level : Nat)) := by rw [hjump]
    _ = restrictGridTo (evolve (2 ^ c.level) ((padCenter2 c).toGrid (0, 0)))
          (2 ^ c.level : Int) (2 ^ (c.level + 1)) := h4
    _ = evolve (2 ^ c.level) ((padCenter2 c).toGrid (0, 0)) :=
        restrictGridTo_eq_self _ _ _ ((jumpCaptured_iff c).mp hcap)

/-! ### BR4a : assemblage du saut unique (pont de localite (a), #6724)

La brique `hashlifeJump_correct_of_captured` ci-dessus est ancree sur
`(2^k, 2^k)` avec l'entree rembourree `(padCenter2 c).toGrid (0, 0)`. Le
moteur, lui, calcule `(hashlifeJump mc).toGrid (jumpResultOff off k)` a
partir de la grille originale `g`. Cet assemblage rejoint les deux par la
chaine complete du pont de localite (a) :

- BR2 (`toGrid_shift_grid`) re-ancre la sortie du saut de `jumpResultOff`
  vers `(2^k, 2^k)` en une translation `δ = newOff − (2^k, 2^k)` ;
- BR3 (`padCenter2_toGrid_shift`) deplie le rembourrage en une translation
  `pad = 3·2^(k−1)` ; `evolve_shift` la fait sortir de `evolve` ;
- BR2 a nouveau exprime `mc.toGrid (0, 0)` comme translation `−off` de
  `mc.toGrid off` ; `evolve_shift` la fait sortir ;
- BR5 (`evolve_congr`, #10895) + BR1 convertissent l'equivalence
  d'appartenance `mc.toGrid off ↔ g` en egalite des trajectoires `evolve` ;
- la composition `shift_shift` des trois translations donne le vecteur net
  `δ + pad + (−off)` dont chaque coordonnee s'annule EXACTEMENT
  (`−2^(k−1) − 2^k + 3·2^(k−1) = 2·2^(k−1) − 2^k = 0` pour `k ≥ 1`), et
  `shift_zero` elimine l'identite residuelle sur la grille canonique
  `evolve (2^k) g`.

Reste ouvert pour `p5_large_n_jumpN` : l'invariant multi-sauts (b) — la
preservation de `jumpCaptured` a travers le re-tramage — puis l'induction
sur le fuel de `evolveHashlifeFastAux`. -/

/-- **Assemblage du saut unique** : pour toute `MacroCell` `mc` dont l'image
    `toGrid off` a la meme appartenance que `g` (hypothese fournie par BR1,
    `mem_toGrid_gridToMacroCellWithOffset`), bien formee, de niveau ≥ 1 et
    sous capture, le saut du moteur produit exactement `evolve (jumpSize k) g`
    — la generation cible du saut, sans translation residuelle. C'est la
    forme exacte du bras de saut de `evolveHashlifeFastAux` (Hashlife.lean,
    `g' := jumped.toGrid newOff`). -/
theorem one_jump_toGrid_correct (g : Grid) (off : Int × Int) (mc : MacroCell)
    (hmem : ∀ p, p ∈ mc.toGrid off ↔ p ∈ g)
    (hwf : mc.wf = true) (hlvl : 1 ≤ mc.level)
    (hcap : jumpCaptured mc = true) :
    (hashlifeJump mc).toGrid (jumpResultOff off mc.level)
      = evolve (jumpSize mc.level) g := by
  have hk1 : mc.level - 1 + 1 = mc.level := by omega
  have hnjs : 0 < 2 ^ mc.level := Nat.two_pow_pos _
  have h1js : 1 ≤ 2 ^ mc.level := by omega
  have h2k : ((2 ^ mc.level : Nat) : Int)
      = 2 * ((2 ^ (mc.level - 1) : Nat) : Int) := by
    have hp : (2 : Nat) ^ (mc.level - 1 + 1) = 2 ^ (mc.level - 1) * 2 := by
      rw [Nat.pow_succ]
    rw [hk1] at hp
    rw [hp, Nat.cast_mul]
    push_cast
    ring
  have hbrick := hashlifeJump_correct_of_captured mc hwf hlvl hcap
  have hnew : jumpResultOff off mc.level
      = (off.1 - (2 ^ (mc.level - 1) : Nat),
         off.2 - (2 ^ (mc.level - 1) : Nat)) := by
    unfold jumpResultOff
    split
    · next h0 =>
        exfalso
        have hb : Nat.beq mc.level 0 = true := by simpa [BEq] using h0
        have hz : mc.level = 0 := Nat.eq_of_beq_eq_true hb
        omega
    · rfl
  have hmc0 : mc.toGrid (0, 0)
      = shift (0 - off.1, 0 - off.2) (mc.toGrid (off.1, off.2)) :=
    toGrid_shift_grid mc 0 0 off.1 off.2
  have hmem' : ∀ p, p ∈ mc.toGrid (off.1, off.2) ↔ p ∈ g := by
    simpa using hmem
  simp only [jumpSize]
  rw [hnew,
    toGrid_shift_grid (hashlifeJump mc) _ _ (2 ^ mc.level : Nat)
      (2 ^ mc.level : Nat),
    hbrick, padCenter2_toGrid_shift mc hlvl, ← evolve_shift, hmc0,
    ← evolve_shift, evolve_congr hmem' h1js, shift_shift, shift_shift]
  have hpow : (2 : Int) ^ (mc.level - 1) = ((2 ^ (mc.level - 1) : Nat) : Int) := by
    exact (Nat.cast_pow (2 : Nat) (mc.level - 1)).symm
  have hz1 : (off.1 - (2 ^ (mc.level - 1) : Nat)) - (2 ^ mc.level : Nat)
      + 3 * (2 ^ (mc.level - 1) : Int) + (0 - off.1) = 0 := by
    rw [hpow, h2k]
    omega
  have hz2 : (off.2 - (2 ^ (mc.level - 1) : Nat)) - (2 ^ mc.level : Nat)
      + 3 * (2 ^ (mc.level - 1) : Int) + (0 - off.2) = 0 := by
    rw [hpow, h2k]
    omega
  rw [hz1, hz2, shift_zero (canonical_evolve_of_pos hnjs g)]

end Life
end Conway
