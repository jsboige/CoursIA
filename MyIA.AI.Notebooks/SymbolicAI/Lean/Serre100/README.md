# Serre 100 — Distillations

Série née du centenaire de Jean-Pierre Serre (conférence [Serre 100](https://serre100.sciencesconf.org/resource/page/id/1), 15-16 septembre 2026) — EPIC [#16334](https://github.com/jsboige/CoursIA/issues/16334).

Le geste « distillation » : prendre un énoncé ou une construction centrale de Serre et le rendre **calculé dans une sortie** — l'énoncé devient une expérience numérique vérifiable, démontrable en Lean quand Mathlib le permet, et exerçable (≥ 3 exercices par notebook).

## Notebooks

| # | Notebook | Source / écho | Outil |
|---|----------|---------------|-------|
| 01 | [01-corps-finis-borne-hasse.ipynb](01-corps-finis-borne-hasse.ipynb) | *A Course in Arithmetic* ch. 1-2 (et en fond, la borne de Hasse-Weil que Serre a tant maniée) | Python stdlib + matplotlib |
| 02 | [02-valeurs-zeta-multiples-finies.ipynb](02-valeurs-zeta-multiples-finies.ipynb) | Adèles et valeurs zêta multiples finies | Python stdlib |
| 03 | [03-cohomologie-cech-espaces-finis.ipynb](03-cohomologie-cech-espaces-finis.ipynb) | Pont Serre–Grothendieck : cohomologie de Čech calculée sur espaces finis | Python stdlib |
| 04 | [04-lemme-yoneda-categories-finies.ipynb](04-lemme-yoneda-categories-finies.ipynb) | Lemme de Yoneda calculé sur catégories finies | Python stdlib |
| 05 | [05-table-de-caracteres.ipynb](05-table-de-caracteres.ipynb) | Tables de caractères — squelette combinatoire des groupes finis | Python stdlib |
| 06 | [06-bulles-minkowski.ipynb](06-bulles-minkowski.ipynb) | Les bulles diaboliques de Minkowski — géométrie des nombres | Python stdlib |
| 08 | [08-serre-dans-mathlib.ipynb](08-serre-dans-mathlib.ipynb) | Tour des cinq « Serre » de Mathlib — le versant preuves du diptyque (index : grain 9 #16374) | Lean 4 (kernel `lean4-wsl`, lake [`serre100_lean/`](serre100_lean/)) |

## Conventions

- Français d'abord, arithmétique en stdlib pur (aucune dépendance au-delà de matplotlib pour les figures) ; le versant **preuves** Lean (08) vit dans le lake compagnon [`serre100_lean/`](serre100_lean/), mêmes pins Mathlib que `hecke_lean`.
- ≥ 3 exercices C.1 par notebook (convention #2161), exécution complète commitée (C.2).
- Verdict SOTA écrit au body de chaque PR (#3801).

## Voie décorélée

L'EPIC #16334 comporte aussi une voie décorélée du programme de l'anniversaire (pont Serre–Grothendieck avec le lake `SymbolicAI/Lean/grothendieck_lean`) : cohomologie de Čech calculée, Yoneda calculé, `SerreMap.lean`.


## Sources primaires

Deux témoignages filmés de J.-P. Serre, transcrits intégralement (Whisper large-v3-turbo, transcription automatique — noms propres corrigés dans les citations : Artin, Weil, Bombieri, Cartier), alimentent les carnets 03, 04 et 07 :

- **« Plaisir des mathématiques »** — J.-P. Serre, Institut Henri Poincaré, 2026 (YouTube `tNtoTzGltak`) — le contre-exemple de Terjanian à la conjecture d'Artin (11:05), cité dans 07.
- **« À propos de la correspondance Grothendieck-Serre »** — dialogue J.-P. Serre / Alain Connes, Fondation Hugot du Collège de France, 2019 (YouTube `pOv-ygSynRI`) — Tohoku et les axiomes (07:05), la montée H0-H1-H2 (12:36), le conducteur (17:57), citées dans 03, 04 et 07.

Transcriptions complètes (timestampées) : `G:\Mon Drive\MyIA\IA\Bibliographie IA\NumberTheory\` — hors dépôt, conformément à la convention bibliographique.
