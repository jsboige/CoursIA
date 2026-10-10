# Baselines de la Phase 3 — niveau « branche »

Corpus : `MyIA.AI.Notebooks/GenAI/FallacyDetection/data/teacher/val_fr.jsonl` (SHA-256 `d7621fffa05d`), 280 paires, 14 etiquettes, 25 scenarios (le plus reemploye 17 fois).

| Baseline | Protocole | Macro-F1 moyenne | Ecart-type |
|---|---|---:|---:|
| Majoritaire | plis groupes par scenario | 0.0034 | 0.0028 |
| Aleatoire (uniforme sur l'entrainement) | plis groupes par scenario | 0.0628 | IC 95 % [0.0371 ; 0.0919] |
| Lexicale (TF-IDF + centroide) | plis groupes par scenario | 0.2198 | 0.042 |
| Lexicale, plis naifs (controle de fuite) | plis stratifies, sans groupes | 0.2291 | 0.0297 |

**Ecart de fuite mesure** : 0.2291 (plis naifs) − 0.2198 (plis groupes) = **0.0093** de macro-F1 attribuables au recouvrement de scenario.

Niveau « nœud » : **280 etiquettes pour 280 paires** (support maximal 1) — sous le plancher de 2 par etiquette, donc **non mesurable** sur ce corpus. Le gate de Phase 3 exige une exactitude a la feuille exacte : elle demande un corpus ou chaque nœud porte plusieurs paires.
