# Pli 1.2 — Vérification first-hand d'`OcclusionTriad.lean` (Project DarkSnail)

**Issue parente :** [#21310](https://github.com/jsboige/CoursIA/issues/21310) (EPIC Origami DarkSnail).
**Cadrage Pli :** sous-grain Pli 1.2 (Lean 4 micro-vérification).
**Lane :** `myia-po-2027:CoursIA-2`.
**Date :** 2026-10-18.
**Statut :** `INSUFFICISANT` — le code est propre (0 `sorry` réel, 0 axiome piégeant) mais le projet n'est **pas compilable en l'état** (imports non résolus, structure lake absente).

## TL;DR

Le dépôt upstream [`sneed-and-feed/projectdarksnail`](https://github.com/sneed-and-feed/projectdarksnail) annonce un badge « Lean 4 Verified (Zero Sorry) » dans son README. Une vérification first-hand du contenu Lean montre que le code `formalization/OcclusionTriad.lean` est **syntaxiquement propre** — aucun `sorry`, aucun `native_decide.*`, aucun `sorryAx`, aucun `Classical.choice`. **Mais** le projet n'a aucune structure de build (pas de `lakefile.lean`, pas de `lean-toolchain`), et le seul module `.lean` importe deux modules qui n'existent pas dans le dépôt. Le claim « Lean 4 Verified » est donc **non vérifiable** à partir du dépôt public.

## Méthode

1. **Clone shallow** du dépôt upstream (licence CC0-1.0 vérifiée c.485) :
   ```bash
   git clone --depth 1 https://github.com/sneed-and-feed/projectdarksnail.git
   ```
2. **Inventaire des sources Lean** :
   ```bash
   find D:/dev/darksnail -type f -name "*.lean"
   # → D:/dev/darksnail/formalization/OcclusionTriad.lean (SEUL fichier .lean)
   ```
3. **Recherche de la structure de build** :
   ```bash
   find D:/dev/darksnail -name "lakefile*" -o -name "lean-toolchain"
   # → 0 résultat (ni lakefile.lean, ni lean-toolchain)
   ```
4. **Audit `sorry` / axiomes piégeants** sur `OcclusionTriad.lean` (les 4 patterns reconnus par `scripts/lean/count_code_sorry.py`) :

   | Pattern | Compte |
   |---|---|
   | `:= by sorry` | 0 |
   | `^\s*sorry\s*$` | 0 |
   | `exact sorry` | 0 |
   | `<;> sorry` | 0 |
   | **Total `sorry` réel** | **0** |
   | `native_decide.*` | 0 |
   | `sorryAx` | 0 |
   | `Classical.choice` | 0 |
   | `Classical.choose` | 0 |
   | `Quot.sound` | 0 |
   | `propext` | 0 |
   | Total occurrences de `sorry` (prose incluse) | 0 |

5. **Tentative de `lake build` dans un lake d'enveloppe minimal** (créé en worktree `D:/dev/CoursIA-21310/tests/darksnail-envelope/`) : **impossible**, car le projet upstream n'a pas de `lakefile.lean` à importer. Le wrapper que j'ai créé localement exige une définition d'enveloppe qui n'existe pas dans DarkSnail.

## Constat factuel

### Code `OcclusionTriad.lean` (26 742 octets ; 26 232 hors LF)

Le module déclare `namespace Ultrametric.Analysis.OcclusionTriad` et expose **9 `theorem` + 13 `lemma` + 18 `def` (10 + 8 `noncomputable`) = 40 déclarations** :

**9 théorèmes** :
- `skew_triad_swap_neg`, `skew_triad_self_zero` (antisymétrie du tenseur)
- `occlusion_triad_breaks_symmetric_tie` (bris de symétrie exact)
- `darksnail_readout_energy_conservation` (conservation d'énergie)
- `darksnail_step0_system1_homotopy` (homotopie à l'initialisation)
- `rope2d_medoid_relative_invariance`, `rope2d_arithmetic_norm_lt` (RoPE 2D)
- `darksnail_multistep_spherical_invariance` (invariance sphérique multi-pas)
- `darksnail_multistep_step0_homotopy` (homotopie multi-pas à l'init)

**13 lemmes** de support (extraits : `triadOperator_two_color_eval`, `inner2_rot2_shift`, `normSq2_avg2_rot2`, `normSq2_nonneg`, `normSq2_avg2_rot2_le`, `normSq2_avg2_rot2_lt`, `shellEnergy_nonneg`, `shellEnergy_eq_zero_iff`, `tangentTriadStep_orthogonal`, `shellEnergy_add_of_orthogonal`, `shellEnergy_scale`, `sphericalTriadStep_preserves_energy`, `sphericalTriadStep_zero`).

**18 `def`** dont `tangentTriadStep`, `sphericalTriadStep`, `multistepSphericalTriad`, `darksnailReadout`, `rope2d`, `rope2dPatchAvg`, `rot2`, etc.

Les **preuves semblent complètes** au sens syntaxique : pas de `sorry`, pas d'axiome exotique, pas d'usage de `native_decide`. Stratégies de preuve effectivement présentes (comptées sur le source sans commentaires) : `simp` ×9, `linarith` ×5, `nlinarith` ×3. `norm_num` et `field_simp` sont **absents** du fichier (correction du rapport initial qui les mentionnait à tort).

### Imports non résolus

Le fichier commence par :
```lean
import Formalization.Analysis.TriadConservation
import Formalization.Analysis.RoPECoherence
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
```

`find D:/dev/darksnail -name "*.lean"` ne retourne **que** `OcclusionTriad.lean` lui-même. Les deux modules `Formalization.Analysis.TriadConservation` et `Formalization.Analysis.RoPECoherence` n'existent pas dans le dépôt public. Sans lakefile, `lake build` ne peut pas résoudre ces imports.

### Comparaison au badge du README

Le README upstream affiche un badge **« Lean 4 Verified (Zero Sorry) »** et la description du dépôt dit *« Lean 4 verified (0 sorry) »*. La partie « 0 sorry » est **conforme à notre vérif** : le code OcclusionTriad.lean ne contient aucun `sorry`. Mais « Lean 4 Verified » implique normalement un build clean — ce qui n'est pas reproductible à partir du dépôt public tel qu'il est publié.

## Verdict

**`INSUFFICISANT`** — les claims « Lean 4 verified (0 sorry) » ne sont **pas vérifiables** à partir du dépôt public.

- ✅ La partie « 0 sorry » est vraie (vérifiée first-hand, 4 patterns, 9 `theorem` + 13 `lemma` + 18 `def`).
- ❌ La partie « Lean 4 verified » (au sens d'un build clean) ne peut pas être reproduite par un tiers : pas de `lakefile.lean`, pas de `lean-toolchain`, et deux imports non résolus.

## Recommandations

1. **Demander à l'auteur DarkSnail** (via issue upstream sur `sneed-and-feed/projectdarksnail`) de :
   - publier un `lakefile.lean` minimal (package + `lean_lib` + pin Mathlib) ;
   - publier les deux modules `Formalization.Analysis.TriadConservation` et `Formalization.Analysis.RoPECoherence` ; ou
   - réduire `OcclusionTriad.lean` à un module self-contained (sans imports `Formalization.Analysis.*`).
2. **Si l'EPIC continue après correction** : Pli 2.1 (lake build témoin) devient exécutable une fois le `lakefile.lean` publié.
3. **Si l'auteur ne répond pas ou ne corrige pas** : EPIC documentée comme non vérifiable, arrêt Pli 2 (cohérent avec le critère d'arrêt du Pli 1 dans #21310).

## Conséquences pour la suite de l'EPIC

- **Pli 1.3 (audit ARC-AGI-1)** : reste actionnable indépendamment (pas de Lean requis).
- **Pli 2 (solidité mathématique)** : bloqué tant que le projet upstream n'a pas de structure de build.
- **Pli 3 (PostTraining)** et **Pli 4 (carnets)** : indépendants de la vérif Lean, mais leur gating dépend de Pli 2.

## Annexe — sortie verbatim de la vérif

```text
# find
$ find D:/dev/darksnail -type f -name "*.lean"
D:/dev/darksnail/formalization/OcclusionTriad.lean

# build structure
$ find D:/dev/darksnail -name "lakefile*" -o -name "lean-toolchain"
(aucun résultat)

# count sorry / axiomes
$ python -c "..." (cf. tableau ci-dessus)
TOTAL real sorry (4 patterns): 0
TOTAL "sorry" (any context): 0
native_decide: 0 ; sorryAx: 0 ; Classical.choice: 0 ; propext: 0
```

## Liens

- Issue parente : [#21310](https://github.com/jsboige/CoursIA/issues/21310)
- Pli 1.1 (sources/licences) : CLOSE par po-2024 c.485
- Pli 1.4 (inventaire Mistral + Cloudflare Clef) : CLOSE par po-2024 c.484
- `scripts/lean/count_code_sorry.py` (instrument de comptage `sorry` réel)
- Capacité Lean avérée sur po-2027 (blocage levé ; preuve dans l'historique de cette fiche)
