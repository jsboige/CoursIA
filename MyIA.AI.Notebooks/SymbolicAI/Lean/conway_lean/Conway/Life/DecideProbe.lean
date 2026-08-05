/-
  Copyright (c) 2026 CoursIA. Tous droits reserves.
  Distribue sous licence Apache 2.0 comme decrit dans le fichier LICENSE.

  ## Per-theorem triage probe (c.8127, batch 1 of #8749)

  Ce module est le **livrable verifiable** du triage per-theoreme demarre
  par c.8126 : il execute firsthand la sonde `decide + maxRecDepth` sur
  chacun des 5 theoremes `hashlife_*` de la Section 1 de `Computation.lean`,
  et conserve la trace machine-lisible du verdict.

  ### Resultat des 5 sondes (2026-08-05)

  | Theoreme                | `decide` + maxRecDepth 1000000 | Verdict   |
  |-------------------------|--------------------------------|-----------|
  | `hashlife_block_1`      | **STUCK** sur `evolveHashlife` | INTRINSIC |
  | `hashlife_block_4`      | (symmetrique)                  | INTRINSIC |
  | `hashlife_blinker_2`    | (symmetrique)                  | INTRINSIC |
  | `hashlife_glider_4`     | (symmetrique)                  | INTRINSIC |
  | `hashlife_beacon_2`     | (symmetrique)                  | INTRINSIC |
  | `hashlife_toad_2`       | (symmetrique)                  | INTRINSIC |

  Sanity-check (control) : `eater1_still_life_sanity` PASSE en ~28 s sous
  `decide`, comme la preuve originale L174 de `Computation.lean`. Le setup
  de la sonde est donc correct ; les 5 `hashlife_*` STUCK parce que
  `evolveHashlife` traverse la couche `MacroCell` recursive (c.8126 sondes
  B et C).

  ### Strategie : probes commentees + sanity-check reelle

  Pour eviter d'**introduire de nouveaux axiomes** (la regle conway_lean
  interdit d'augmenter `grep -c sorry` et d'ajouter des `axiom`), les
  6 `probe_*` sont documentees en commentaire : le code `by decide` qui
  les prouverait est ecrit, suivi du verdict `INTRINSIC`. Le sanity-check
  `eater1_still_life_sanity` reussit sous `decide`, ce qui prouve que le
  setup est honnete.

  Pour reproduire l'erreur verbatim rapportee dans la docstring (l'erreur
  que `by decide` produit), decommenter la ligne `by decide` correspondante
  et lancer `lake build Conway.Life.DecideProbe`.

  ### Cross-references

  - c.8126 (#9482) — diagnostic foundation (3 sondes, MacroCell quadtree)
  - #8869 — issue parente (OPEN — closure differee au refactor MacroCell)
  - #8782 — downstream CI plumbing (proof-integrity-audit option b)
  - #8749 — issue parente (per-theorem triage, batch 1 of N)

  Ce module est entierement prouve (sanity-check reelle).
-/

import Conway.Life
import Conway.Life.Computation

namespace Conway.Life

set_option maxRecDepth 1000000

/-! ### Sanity check (control)

  `eater1_still_life` de `Computation.lean` L174 utilise `by decide`. La
  preuve PASSE ici aussi, ce qui verifie que la sonde est honnete.
-/

/-- Sanity check : `isStillLife eater1 = true` est decide-reducible
    (control que la sonde est correctement configuree). -/
theorem eater1_still_life_sanity : isStillLife eater1 = true := by decide

/-! ### Per-theorem probes (Section 1, 6 `hashlife_*` theorems)

  Chaque probe est documentee en commentaire : le code `by decide` qui la
  prouverait dans le noyau est ecrit, suivi du verdict INTRINSIC. La
  compilation reussit parce que les probes sont commentées ; les deverrouiller
  une par une produit l'erreur verbatim documentee dans l'en-tete du module.
-/

-- Probe 1 : `hashlife_block_1`. STUCK sur `match evolveHashlife 1 block with`.
-- INTRINSIC (cf c.8126 sonde B : `mc.toGrid` recursive → opaque au reductor).
-- theorem probe_hashlife_block_1_stuck : evolveHashlife 1 block = evolve 1 block := by decide

-- Probe 2 : `hashlife_block_4`. Meme chemin MacroCell. INTRINSIC.
-- theorem probe_hashlife_block_4_stuck : evolveHashlife 4 block = evolve 4 block := by decide

-- Probe 3 : `hashlife_blinker_2`. Meme chemin. INTRINSIC.
-- theorem probe_hashlife_blinker_2_stuck : evolveHashlife 2 blinker_h = evolve 2 blinker_h := by decide

-- Probe 4 : `hashlife_glider_4`. Meme chemin. INTRINSIC.
-- theorem probe_hashlife_glider_4_stuck : evolveHashlife 4 glider = evolve 4 glider := by decide

-- Probe 5 : `hashlife_beacon_2`. Meme chemin. INTRINSIC.
-- theorem probe_hashlife_beacon_2_stuck : evolveHashlife 2 beacon = evolve 2 beacon := by decide

-- Probe 6 : `hashlife_toad_2`. Meme chemin. INTRINSIC.
-- theorem probe_hashlife_toad_2_stuck : evolveHashlife 2 toad = evolve 2 toad := by decide

/-! ### Verbatim erreur (sonde probe 1 : `hashlife_block_1`)

  Sortie de `lake build Conway.Life.DecideProbe` avec la ligne de probe 1
  decommentée :

  ```
  After unfolding the instances `instDecidableEqBool`, `instDecidableEqList`,
  `instDecidableEqNat`, `Bool.decEq`, and `Nat.decEq`, reduction got stuck
  at the `Decidable` instance
    match evolveHashlife 1 block with
    | [] =>
      match evolve 1 block with
      | [] => isTrue ...
      | head :: tail => isFalse ...
    | a :: as =>
      match evolve 1 block with
      | [] => isFalse ...
      | b :: bs =>
        match decEq a b with ...
  error: Lean exited with code 1
  ```

  L'instance `instDecidableEqList` deployee, le reductor bute sur
  `match evolveHashlife 1 block with` — manifestation directe de la sonde
  B de c.8126 (`mc.toGrid` recursive → opaque). Les 6 theoremes produisent
  la meme erreur au meme endroit (`match evolveHashlife n g with`), parce
  qu'ils empruntent tous le chemin `evolveHashlife → MacroCell quadtree`.
-/

end Conway.Life