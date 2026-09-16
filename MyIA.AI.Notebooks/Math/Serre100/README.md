# Serre 100 — Distillations

Série née du centenaire de Jean-Pierre Serre (conférence [Serre 100](https://serre100.sciencesconf.org/resource/page/id/1), 15-16 septembre 2026) — EPIC [#16334](https://github.com/jsboige/CoursIA/issues/16334).

Le geste « distillation » : prendre un énoncé ou une construction centrale de Serre et le rendre **calculé dans une sortie** — l'énoncé devient une expérience numérique vérifiable, démontrable en Lean quand Mathlib le permet, et exerçable (≥ 3 exercices par notebook).

## Notebooks

| # | Notebook | Source / écho | Outil |
|---|----------|---------------|-------|
| 01 | [01-corps-finis-borne-hasse.ipynb](01-corps-finis-borne-hasse.ipynb) | *A Course in Arithmetic* ch. 1-2 (et en fond, la borne de Hasse-Weil que Serre a tant maniée) | Python stdlib + matplotlib |

## Conventions

- Français d'abord, arithmétique en stdlib pur (aucune dépendance au-delà de matplotlib pour les figures).
- ≥ 3 exercices C.1 par notebook (convention #2161), exécution complète commitée (C.2).
- Verdict SOTA écrit au body de chaque PR (#3801).

## Voie décorélée

L'EPIC #16334 comporte aussi une voie décorélée du programme de l'anniversaire (pont Serre–Grothendieck avec le lake `SymbolicAI/Lean/grothendieck_lean`) : cohomologie de Čech calculée, Yoneda calculé, `SerreMap.lean`.
