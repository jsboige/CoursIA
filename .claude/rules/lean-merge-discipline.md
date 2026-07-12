---
paths: "{**/*.lean,**/Lean/**/*,**/lean/**/*,**/social_choice_lean/**/*}"
---

# Lean PR discipline — Lake build local + BG iter post-po-2026

S'applique a **toute PR touchant `*.lean`** + au **coordinateur ai-01** pour BG iter prover.

## 1. Lake build SUCCESS local OBLIGATOIRE avant merge (HARD)

Avant CHAQUE merge Lean : `lake build <module>` LOCAL par ai-01. Le claim "lake build SUCCESS Xs" dans le body PR n'est **PAS suffisant** (trust mais verifie). Pas d'env Lean local : dispatcher po-2026 avec build log complet + `grep -c sorry` avant/apres + diff sur defs partagees.

**CI != Lake build local** : `lean-social-choice.yml` ne build PAS Voting.lean. CI SUCCESS != module compile.

**Incident source** : 2026-05-10 merge #866 sur claim non-verifie → revert #885, 1 cycle perdu.

## 2. Prover BG systematique post-PR/msg po-2026 (HARD)

Apres **chaque PR** ou **message dashboard/inbox** de `myia-po-2026:*` mentionnant un sorry Lean CoursIA, **lancer SYSTEMATIQUEMENT** un BG iter prover depuis ai-01 sur le meme sorry/file.

**Anti-pattern interdit** : "Le BG a deja FAILED hier, pas la peine de relancer". Le contexte change a chaque iteration manual po-2026. Meme si re-echec : donnee diagnostic precieuse.

**Verification fin de cycle** : avant `[DONE]` dashboard, repondre "Est-ce qu'il y a eu un PR ou msg po-2026 ce cycle ? Si oui, BG iter a-t-il ete lance ?". Pas de DONE sans cet item adresse.

**Source** : User 2026-05-16 ~13:55Z mandate explicite.

## Detail workflow

- Build local + cache get + DEMO_ID mapping + forensic interpretation + capture postmortem : [docs/lean/coordinator-workflow.md](../../docs/lean/coordinator-workflow.md)
- LLM endpoints providers : [docs/lean/llm-endpoints.md](../../docs/lean/llm-endpoints.md)
- Iterations F6-F11, B3 : [docs/lean/prover_iteration_history.md](../../docs/lean/prover_iteration_history.md)

## Voir aussi

- [anti-regression.md](anti-regression.md) — `grep -c sorry` avant/apres, pas de regression preuves
- [pr-review-discipline.md](pr-review-discipline.md) — Section B (4 elements Lean PR body)
