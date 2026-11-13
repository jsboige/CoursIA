# Critère de frontière — utilitaire de série ou exposition MCP

> REFERENCE — vivante — dernière révision 2026-11-11

Provenance : issue #19379 (axe 3 du tracker de distillation #16457), arbitrage ai-01 du 2026-11-09 — formulation fusionnée des quatre livraisons du fil (A, B, synthèse c336, C), chaque divergence tranchée par un contre-exemple mesuré du dépôt.

## La question

Un organe né dans un notebook (un générateur, un solver, un utilitaire) grossit. À quel moment devient-il **utilitaire de série** importable, et à quel moment doit-il être **exposé en serveur MCP** ? Deux domaines du dépôt ont accumulé des outils sans que cette frontière soit écrite : `IIT/ICT-Series/` et `GameTheory/GameTheory-16*`.

## Barreau 1 → 2 : cellule → utilitaire de série

Le passage est commandé par la **réutilisation mesurée**, plus un contrat :

- **réutilisation** : duplication du même code entre carnets, **ou** premier consommateur cross-série (un carnet ou un script hors de la série d'origine qui importe l'organe) ;
- **contrat** : tests propres à l'organe, packaging installable — fin des insertions `sys.path` chez les consommateurs.

## Barreau 2 → 3 : module → exposition MCP

Le passage exige **les deux** conditions, et la réutilisation n'en fait partie d'aucune :

1. **audience hors-interpréteur** — le consommateur ne peut pas joindre l'organe **ni son état** par `import` (un agent dans une autre machine, un autre processus, une autre file d'exécution) ;
2. **état ou autorisation inter-processus** — kernels vivants, dashboards partagés, secrets, API authentifiée, quotas.

**La réutilisation ne commande jamais l'exposition.** C'est la correction commune que les contre-exemples du fil imposent : l'audience « agent » seule ne suffit pas (le consommateur de `execute_notebook_with_complex_topic.py` est un carnet Python, qui aurait joint l'organe par import si l'organe avait été installable), et la capacité d'être importé ne suffit pas non plus. Les deux barreaux sont des décisions **séparées** : la réutilisation commande 1 → 2, jamais 2 → 3.

## Contrôles vivants — le critère appliqué aux MCP existants du dépôt

| Serveur MCP | (i) audience hors-interpréteur | (ii) état / autorisation inter-processus | Verdict |
|---|---|---|---|
| `jupyter-papermill` | agents hors Python | kernels vivants | **MCP** (i+ii) |
| `roo-state-manager` | flotte cross-machine | dashboards + conversations partagés | **MCP** (i+ii) |
| `qc-mcp` | agents hors QC Cloud | auth QC Cloud + quotas d'appels | **MCP** (i+ii) |

## Cas mesurés du dépôt

| Cas | Mesure | Verdict |
|---|---|---|
| `IIT/ICT-Series/ict/` | package de modules `.py` + `pyproject.toml` à la racine de la série ; **8 consommateurs par import réel** hors ICT-Series (les carnets PT_15b, 2.9g, Obs-04, KNOTS-02, Lean-34, SL-13b + `scripts/hashlife/k_trajectory.py` et son test) ; les 6 carnets passent tous par `sys.path` (1-2 sites chacun) | **barreau 2 dû** — réutilisation mesurée sans i/ii : extraction/installation, **pas de MCP** |
| `GameTheory-16*` | aucun import cross-série, aucune duplication mesurée | **rien dû** — le palier reste notebook |
| `execute_notebook_with_complex_topic.py` | `@mcp.tool()` (l. 100), consommateur = un carnet Python | **MCP légitime** (kernels = état inter-processus) — et contre-exemple : l'audience agent et la capacité d'import ne sont pas des conditions nécessaires |

## Ce que le critère déclare dû aujourd'hui

Pour `ict/` (barreau 1 → 2) : rendre le package installable pour ses consommateurs hors série et retirer les insertions `sys.path` des six carnets recensés — grain de consolidation distinct, suivi en issue séparée (confié à la lane CoursIA-3).
