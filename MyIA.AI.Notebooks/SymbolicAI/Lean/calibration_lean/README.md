# Calibration Lean

Cibles de calibration du prouveur pour benchmarker le prouveur Lean multi-agents.

## Statut

- **Toolchain** : v4.30.0-rc2
- **Compte de sorry** : 0 en production (les 4 cibles de calibration sont prouvées ; un ancien compte de « 4 sorry » correspondait à du texte de docstring à l'intérieur de blocs `/-- ... -/`, pas à des termes `sorry` réels)
- **Build** : `lake build Calibration` -- SUCCESS
- **Dépendances** : Mathlib4

## Modules

| Fichier | sorry | Description |
|---------|-------|-------------|
| `Calibration/Nash.lean` | 0 | Cibles de calibration du prouveur (C/D/E/F) |

## Cibles de calibration

- **Cible C** : Prouvée
- **Cible D** : Prouvée
- **Cible E** : Prouvée
- **Cible F** : Prouvée (la docstring de ce lemme mentionne le mot « sorry » — des scans `grep` précédents s'en sont laissés induire en erreur)

## Notes

- Ce module benchmark la capacité du prouveur Lean multi-agents à clore des preuves de type manuel
- Toutes les cibles sont désormais fermées ; le module est conservé comme suite de régression permanente pour les changements du prouveur
- Vérification : `grep -nE '^[^/]*\bsorry\b' Calibration/Nash.lean` retourne 0 correspondance en production (cf [README Lean](../Lean-1-Setup.ipynb))

## Conclusion

Ce projet est une **suite de calibration** pour le prouveur Lean multi-agents :
quatre cibles de preuve de type manuel (C / D / E / F) dans
`Calibration/Nash.lean`, toutes **prouvées avec 0 `sorry`**
(`lake build Calibration` SUCCESS, toolchain `v4.30.0-rc2`).

### Pourquoi ce module existe

Les cibles benchmarkent la capacité du prouveur à clore des preuves courtes et
auto-contenues de bout en bout. Les quatre étant désormais fermées, le module
est conservé comme **suite de régression permanente** : tout changement du
prouveur qui casse l'une de ces preuves remonte ici comme un échec de build.

### La leçon du faux positif grep

Un ancien compte de « 4 `sorry` » était un **artéfact de mesure** — le mot
« sorry » apparaissait à l'intérieur de docstrings `/-- ... -/` (prose), pas
comme termes de preuve. Un `grep sorry` naïf sur-comptait ; la vérification
correcte `grep -nE '^[^/]*\bsorry\b'` (en excluant commentaires/docstrings)
retourne 0. La même distinction — `sorry` la tactique vs « sorry » le mot —
s'applique à toute la série Lean.

### Où aller ensuite

- **Harnais du prouveur** : [`agent_tests/prover/`](../agent_tests/prover/) — le prouveur multi-agents que ces cibles calibrent.
- **Cibles de production** : [`conway_lean/`](../conway_lean/),
  [`knot_lean/`](../knot_lean/) — projets Lean sur lesquels le prouveur
  s'exécute également.
