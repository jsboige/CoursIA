# Prover BG systematique post-PR/msg po-2026

S'applique au **coordinateur ai-01** sur projet Lean stable_marriage/social_choice/voting/etc.

## Regle HARD

Apres **chaque PR** ou **message dashboard/inbox** de `myia-po-2026:*` mentionnant un sorry Lean repository CoursIA, **lancer SYSTEMATIQUEMENT** un BG iter prover depuis ai-01 sur le meme sorry/file.

**Anti-pattern interdit** : "Le BG a deja FAILED hier, pas la peine de relancer". Le contexte change a chaque iteration manual po-2026. Meme si re-echec : donnee diagnostic precieuse (script ne progresse pas malgre nouveau contexte).

**Verification fin de cycle** : avant `[DONE]` dashboard, repondre "Est-ce qu'il y a eu un PR ou msg po-2026 ce cycle ? Si oui, BG iter a-t-il ete lance ?". Pas de DONE sans cet item adresse.

**Source** : User 2026-05-16 ~13:55Z : "Pour gale shapley, stp fais une iteration de ton cote en BG (ca devrait etre systematique apres chaque PR ou message de po-2026)".

Workflow complet (commande BG, DEMO_ID mapping, forensic interpretation guide, capture postmortem) : [docs/lean/coordinator-workflow.md](../../docs/lean/coordinator-workflow.md#2-bg-iter-prover-systematique-post-prmsg-po-2026).

## Voir aussi

- [docs/lean/llm-endpoints.md](../../docs/lean/llm-endpoints.md) — Providers prover
- [docs/lean/prover_iteration_history.md](../../docs/lean/prover_iteration_history.md) — Iterations F6-F11, B3
- [.claude/rules/lean-lake-build-required.md](lean-lake-build-required.md) — Lake build avant merge
