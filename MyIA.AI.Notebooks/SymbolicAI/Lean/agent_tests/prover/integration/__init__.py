"""Integration LeanDojo v2 dans le prouveur maison (pli 2 #18562 via #18915).

Ce sous-package abrite les carnets et tests qui valident l'integration
de `lean-dojo` (>= 2.2.0) comme outil de tracage de preuves Lean 4, en
mode model-only (sans torch/transformers -- INTRINSIC par manque de
GPU sur la lane ai-01).

Le scope de pli 1 (verdict SOTA, c.76) est documente dans le corps du
carnet `Lean-11-LeanDojo-V2-Faisabilite.ipynb` et dans l'issue #18915.
Le scope de pli 2 (integration dans le prouveur maison) est dans
`leandojo_feasibility.py` + `test_leandojo_feasibility.py`.
"""