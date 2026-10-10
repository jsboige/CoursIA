# Baselines de la Phase 3 — niveau « branche »

Corpus : `MyIA.AI.Notebooks/GenAI/FallacyDetection/data/teacher/val_fr.jsonl` (SHA-256 `d7621fffa05d`), 280 paires, 14 etiquettes, 25 scenarios (le plus reemploye 17 fois).

| Baseline | Protocole | Macro-F1 moyenne | Ecart-type |
|---|---|---:|---:|
| Majoritaire | plis groupes par scenario | 0.0034 | 0.0028 |
| Aleatoire (uniforme sur l'entrainement) | plis groupes par scenario | 0.0628 | IC 95 % [0.0371 ; 0.0919] |
| A regles (dictionnaires de famille ponderes IDF) | aucun entrainement, corpus entier | 0.0328 | exactitude 0.075 |
| Lexicale (TF-IDF + centroide) | plis groupes par scenario | 0.2198 | 0.042 |
| Lexicale, plis naifs (controle de fuite) | plis stratifies, sans groupes | 0.2291 | 0.0297 |

Dictionnaires de la baseline a regles : 14 familles bâties sur les titres et definitions des deux taxonomies Argumentum, **jamais** sur les champs `example_*` (meme regle d'anti-circularite que les prompts de la tranche A). Les trois plus maigres : Justesse lexicale (18 nœuds, 146 jetons), Sens quantitatif (20 nœuds, 185 jetons), Présentation intègre (25 nœuds, 225 jetons).

**Ce que la baseline a regles a montre, contre l'attente** : le prompt de generation portait le titre et la definition du nœud cible, donc un texte repris de sa propre definition devait etre compte juste par sa propre famille -- cette reserve annoncait un chiffre *optimiste*. Mesure : il est **inferieur a l'aleatoire**, et les etiquettes jamais predites sont ['Argument pertinent', 'Erreur mathématique', 'Honnêteté intellectuelle', 'Inférence maîtrisée', 'Justesse lexicale', 'Présentation intègre', 'Sens quantitatif', 'Échange enrichissant']. Le canal de l'echo existe, mais il est domine par un autre effet : le dictionnaire d'une grande famille (`Influence`, 1816 jetons) couvre plus de texte que celui d'une petite (`Justesse lexicale`, 146), donc la regle se replie sur les sept familles de sophismes et n'atteint **aucune** famille de vertus. Une baseline a regles construite sur ces dictionnaires ne peut pas servir de reference basse utile au gate : elle est battue par le tirage uniforme.

**Ecart de fuite mesure** : 0.2291 (plis naifs) − 0.2198 (plis groupes) = **0.0093** de macro-F1 attribuables au recouvrement de scenario.

Niveau « nœud » : **280 etiquettes pour 280 paires** (support maximal 1) — sous le plancher de 2 par etiquette, donc **non mesurable** sur ce corpus. Le gate de Phase 3 exige une exactitude a la feuille exacte : elle demande un corpus ou chaque nœud porte plusieurs paires.
