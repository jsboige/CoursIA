# Lake build SUCCESS local OBLIGATOIRE avant merge Lean PR

S'applique a **toute PR touchant `*.lean`**.

## Regle HARD

Avant CHAQUE merge Lean : `lake build <module>` LOCAL par le coordinateur (ai-01). Le claim "lake build SUCCESS Xs" dans le body PR n'est **PAS suffisant** (Trust mais verifie).

Si pas d'env Lean local : ne pas merger seul, dispatcher po-2026 avec build log complet + `grep -c sorry` avant/apres + diff sur defs partagees.

**CI != Lake build local** : `lean-social-choice.yml` ne build PAS Voting.lean. CI SUCCESS != module compile.

**Source incident** : 2026-05-10 merge #866 sur claim non-verifie → revert #885, 1 cycle perdu. Detail + workflow build local + cache get : [docs/lean/coordinator-workflow.md](../../docs/lean/coordinator-workflow.md#1-lake-build-success-local-avant-merge).

## Voir aussi

- [.claude/rules/anti-regression.md](anti-regression.md) — `grep -c sorry` avant/apres
- [.claude/rules/pr-review-discipline.md](pr-review-discipline.md) — Section B (4 elements Lean PR body)
