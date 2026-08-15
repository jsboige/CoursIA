# Documentation Lean 4 — index de référence

Références durables pour le travail Lean 4 du dépôt : prover multi-agent, i18n FR/EN, toolchain Windows, et pièges tactiques. Cette note sert d'**index de découvrabilité** : les documents ci-dessous étaient orphelins (aucun pointeur ne les reliait entre eux ni depuis le reste du dépôt), d'où le risque qu'un piège durement appris — par ex. la non-propagation d'instance `Decidable` — reste invisible au prochain worker qui le rencontre.

Pour la pédagogie Lean (notebooks étudiants), voir [`MyIA.AI.Notebooks/SymbolicAI/Lean/`](../../MyIA.AI.Notebooks/SymbolicAI/Lean/). Le harnais règles courantes vit dans [`.claude/rules/lean-merge-discipline.md`](../../.claude/rules/lean-merge-discipline.md).

## Pièges tactiques

| Document | Sujet |
|---|---|
| [decidable_instance_propagation.md](decidable_instance_propagation.md) | **Piège** : l'instance `Decidable` ne se propage pas à travers une `def : Prop` (2026-08-07, #9568). La première cause des `Decidable` manquants qui ne sont pas des `sorry`. |
| [l902_tactic_pitfalls.md](l902_tactic_pitfalls.md) | **Piège** : `rfl` direct impossible sur les fields de constructors polymorphes d'univers (`Equivalence.refl`, `CategoryTheory.yoneda`, `Sieve`). 4 strategies testées (Tier 1-4), 3 FAIL, 1 PASS. Solution canonique : argument `(e : C ≌ D)` ou retrait pragmatique (2026-08-12, PR #10638). |

## Prover multi-agent & LLM

| Document | Sujet |
|---|---|
| [prover_iteration_history.md](prover_iteration_history.md) | Historique d'itération du prover (Stable Marriage, 2026-05-07 → 05-18) — échecs reproductibles, tactiques tentées. |
| [sota-2026-analysis.md](sota-2026-analysis.md) | État de l'art de la preuve automatique Lean 4 (mai 2026) — leçons actionnables pour notre harnais. |
| [llm-endpoints.md](llm-endpoints.md) | Configuration des providers LLM du prover (`agent_tests/prover/`). |
| [ab-methodology.md](ab-methodology.md) | Méthodologie d'A/B pour comparer deux providers LLM sur les mêmes cibles Lean. |
| [coordinator-workflow.md](coordinator-workflow.md) | Workflow coordinateur Lean (ai-01) : Lake build pre-merge + itération BG prover systématique. |

## i18n FR/EN (EPIC #4980)

| Document | Sujet |
|---|---|
| [i18n-inventory-cycle-38.md](i18n-inventory-cycle-38.md) | Inventaire FR/EN + proposition de convention (cycle 38, décision user 2026-07-02). |
| [i18n-sibling-patterns.md](i18n-sibling-patterns.md) | Patterns de paires FR/EN (`Foo.lean` / `Foo_en.lean`) et discipline du checker `check_i18n_siblings.py`. |

## Toolchain

| Document | Sujet |
|---|---|
| [windows-native-toolchain.md](windows-native-toolchain.md) | Toolchain Windows-native (MSYS) — débloquer `lake build` hors WSL. |

## Voir aussi

- [`docs/reference/lean-dev-disk-hygiene.md`](../reference/lean-dev-disk-hygiene.md) — hygiène disque machine de dev Lean (#8924).
- [`docs/lean/`](.) (ce répertoire) est pointé depuis [`CLAUDE.md`](../../CLAUDE.md) § « Documentation déportée ».
