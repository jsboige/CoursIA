# Baselines de la Phase 3 — corpus tranche B

Fichier généré par `scripts/fallacy_detection/measure_baselines_tranche_b.py` — ne pas éditer à la main.

Instrument : `scripts/fallacy_detection/baseline_branch_detection.py (rejoue tel quel)`. Graine 42, 5 plis groupes par scenario, 200 tirages aleatoires.

| Variante | Niveau | Lignes | Etiquettes | Support | Groupes | Majoritaire | Aleatoire | Lexicale groupee | Lexicale naive | Regles | Fuite |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| train_complet | branch | 14000 | 14 | 216-2520 | 117 | 0.0218 | 0.0599 | 0.2572 | 0.2598 | 0.0758 | 0.0026 |
| train_complet | node | 14000 | 1629 | 6-14 | 117 | 0.0 | 0.0004 | 0.1197 | 0.1255 | 0.0302 | 0.0058 |
| train_roundtrip | branch | 12498 | 14 | 148-2275 | 117 | 0.022 | 0.0593 | 0.2681 | 0.2758 | 0.0777 | 0.0077 |
| train_roundtrip | node | Niveau 'node' non mesurable sur ce corpus : 1628 etiquettes, 16 sous le plancher de 2 paires, support minimal 1 (support maximal 14). Etiquettes en deca : F1045 (1), F1071 (1), F1141 (1), F230 (1), F254 (1). Une macro-F1 par etiquette calculee sur un seul exemple mesure le tirage, pas le corpus. Fournir un corpus ou chaque etiquette porte au moins 2 paires, ou mesurer un niveau plus large. | | | | | | | | | |
| val_complet | branch | 1629 | 14 | 18-420 | 25 | 0.0292 | 0.0558 | 0.1682 | 0.1743 | 0.0847 | 0.0061 |
| val_complet | node | Niveau 'node' non mesurable sur ce corpus : 1629 etiquettes, 1629 sous le plancher de 2 paires, support minimal 1 (support maximal 1). Etiquettes en deca : F1 (1), F10 (1), F100 (1), F1000 (1), F1001 (1). Une macro-F1 par etiquette calculee sur un seul exemple mesure le tirage, pas le corpus. Fournir un corpus ou chaque etiquette porte au moins 2 paires, ou mesurer un niveau plus large. | | | | | | | | | |
| val_roundtrip | branch | 1452 | 14 | 14-386 | 25 | 0.03 | 0.054 | 0.1533 | 0.1632 | 0.0872 | 0.0099 |
| val_roundtrip | node | Niveau 'node' non mesurable sur ce corpus : 1452 etiquettes, 1452 sous le plancher de 2 paires, support minimal 1 (support maximal 1). Etiquettes en deca : F1 (1), F10 (1), F100 (1), F1000 (1), F1001 (1). Une macro-F1 par etiquette calculee sur un seul exemple mesure le tirage, pas le corpus. Fournir un corpus ou chaque etiquette porte au moins 2 paires, ou mesurer un niveau plus large. | | | | | | | | | |
