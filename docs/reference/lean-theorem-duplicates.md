# Theoremes en double entre lacs Lean

Page regeneree par `scripts/lean/lean_theorem_duplicates.py` (`--write` pour la reecrire, `--check` pour verifier qu'elle suit l'arbre). Ne pas l'editer a la main.

## Theoremes en double entre lacs

Table generee par `scripts/lean/lean_theorem_duplicates.py`. Une **paire** represente deux declarations de **lacs differents** dont les noms se recouvrent (contenance >= 0.80 sur des tokens d'au moins trois caracteres) et dont un **terme discriminant** du nom est commun aux deux docstrings -- terme porte par au plus 8 declarations dans le depot, ce qui ecarte les lemmes generiques (`card`, `trans`, `wf`).

Ce tableau est un **signal**, pas un verdict : retirer, fusionner ou deplacer une preuve est une decision humaine. Les freres `_en` (convention i18n) et les paires internes a un meme lac sont exclus par construction.

### Paires fortes — docstrings proches

| Nom A | Lac A | Nom B | Lac B | Docstring | Termes |
|---|---|---|---|---|---|
| `arrow` | `MyIA.AI.Notebooks/GameTheory/game_theory_lean` | `arrow_impossibility` | `MyIA.AI.Notebooks/GameTheory/lean_game_defs` | 0.27 | `arrow` |
| `sen_impossibility` | `MyIA.AI.Notebooks/GameTheory/game_theory_lean` | `sen_impossibility` | `MyIA.AI.Notebooks/GameTheory/lean_game_defs` | 0.29 | `sen` |

### Paires faibles — terme de nom commun, docstrings eloignees

Ces paires partagent un terme rare mais ne decrivent pas clairement le meme resultat ; elles sont listees pour memoire, pas pour etre traitees.

| Nom A | Lac A | Nom B | Lac B | Docstring | Termes |
|---|---|---|---|---|---|
| `fairBot_fairBot_cooperation` | `MyIA.AI.Notebooks/GameTheory/game_theory_lean` | `fairBot_self_cooperation` | `MyIA.AI.Notebooks/SymbolicAI/Lean/formal_logic_lean` | 0.09 | `cooperation` |
| `fairBot_fairBot_cooperation` | `MyIA.AI.Notebooks/GameTheory/game_theory_lean` | `fairBot_mutual_cooperation` | `MyIA.AI.Notebooks/SymbolicAI/Lean/formal_logic_lean` | 0.09 | `cooperation` |
| `fairBot_fairBot_cooperation` | `MyIA.AI.Notebooks/GameTheory/game_theory_lean` | `pa_fairBot_self_cooperation` | `MyIA.AI.Notebooks/SymbolicAI/Lean/formal_logic_lean` | 0.09 | `cooperation` |
| `fairBot_fairBot_cooperation` | `MyIA.AI.Notebooks/GameTheory/game_theory_lean` | `standard_fairBot_pair_cooperation` | `MyIA.AI.Notebooks/SymbolicAI/Lean/formal_logic_lean` | 0.10 | `cooperation` |
| `one_sub_pow_le_exp` | `MyIA.AI.Notebooks/ML/learning_theory_lean` | `one_sub_pow_le_exp_mul` | `MyIA.AI.Notebooks/SymbolicAI/Lean/mimo_lean` | 0.00 | `exp`, `le`, `one`, `sub` |
| `countP_length_filter` | `MyIA.AI.Notebooks/SymbolicAI/Lean/KNOTS/knot_lean` | `Canonical.filter` | `MyIA.AI.Notebooks/SymbolicAI/Lean/conway_lean` | 0.11 | `filter` |
| `jumpCapturedF_reconstruction_of_still_life` | `MyIA.AI.Notebooks/SymbolicAI/Lean/conway_lean` | `reconstruction` | `MyIA.AI.Notebooks/SymbolicAI/Lean/sensitivity_lean` | 0.03 | `reconstruction` |
| `jumpCapturedF_reconstruction_of_period` | `MyIA.AI.Notebooks/SymbolicAI/Lean/conway_lean` | `reconstruction` | `MyIA.AI.Notebooks/SymbolicAI/Lean/sensitivity_lean` | 0.03 | `reconstruction` |
| `jumpCapturedF_reconstruction_of_period_mod` | `MyIA.AI.Notebooks/SymbolicAI/Lean/conway_lean` | `reconstruction` | `MyIA.AI.Notebooks/SymbolicAI/Lean/sensitivity_lean` | 0.03 | `reconstruction` |
| `jumpCapturedF_reconstruction_of_spaceship` | `MyIA.AI.Notebooks/SymbolicAI/Lean/conway_lean` | `reconstruction` | `MyIA.AI.Notebooks/SymbolicAI/Lean/sensitivity_lean` | 0.03 | `reconstruction` |
| `jumpCapturedF_reconstruction_of_spaceship_mod` | `MyIA.AI.Notebooks/SymbolicAI/Lean/conway_lean` | `reconstruction` | `MyIA.AI.Notebooks/SymbolicAI/Lean/sensitivity_lean` | 0.03 | `reconstruction` |
| `jumpCapturedF_reconstruction_of_static_frame` | `MyIA.AI.Notebooks/SymbolicAI/Lean/conway_lean` | `reconstruction` | `MyIA.AI.Notebooks/SymbolicAI/Lean/sensitivity_lean` | 0.04 | `reconstruction` |

Detail des paires (fichier et ligne) :

- **1.00** -- `arrow` (MyIA.AI.Notebooks/GameTheory/game_theory_lean/SocialChoice/Arrow.lean:696) et `arrow_impossibility` (MyIA.AI.Notebooks/GameTheory/lean_game_defs/SocialChoice.lean:899) -- nom 1.00 / docstring 0.27 / enonce 0.08 / termes arrow
- **1.00** -- `sen_impossibility` (MyIA.AI.Notebooks/GameTheory/game_theory_lean/SocialChoice/Sen.lean:77) et `sen_impossibility` (MyIA.AI.Notebooks/GameTheory/lean_game_defs/SocialChoice.lean:996) -- nom 1.00 / docstring 0.29 / enonce 0.09 / termes sen
- **1.00** -- `fairBot_fairBot_cooperation` (MyIA.AI.Notebooks/GameTheory/game_theory_lean/ProgramGames/FairBot.lean:205) et `fairBot_self_cooperation` (MyIA.AI.Notebooks/SymbolicAI/Lean/formal_logic_lean/FormalLogic/FairBotLoeb.lean:97) -- nom 1.00 / docstring 0.09 / enonce 0.00 / termes cooperation
- **1.00** -- `fairBot_fairBot_cooperation` (MyIA.AI.Notebooks/GameTheory/game_theory_lean/ProgramGames/FairBot.lean:205) et `fairBot_mutual_cooperation` (MyIA.AI.Notebooks/SymbolicAI/Lean/formal_logic_lean/FormalLogic/FairBotLoeb.lean:105) -- nom 1.00 / docstring 0.09 / enonce 0.00 / termes cooperation
- **1.00** -- `fairBot_fairBot_cooperation` (MyIA.AI.Notebooks/GameTheory/game_theory_lean/ProgramGames/FairBot.lean:205) et `pa_fairBot_self_cooperation` (MyIA.AI.Notebooks/SymbolicAI/Lean/formal_logic_lean/FormalLogic/FairBotLoeb.lean:175) -- nom 1.00 / docstring 0.09 / enonce 0.00 / termes cooperation
- **1.00** -- `fairBot_fairBot_cooperation` (MyIA.AI.Notebooks/GameTheory/game_theory_lean/ProgramGames/FairBot.lean:205) et `standard_fairBot_pair_cooperation` (MyIA.AI.Notebooks/SymbolicAI/Lean/formal_logic_lean/FormalLogic/FairBotLoeb.lean:218) -- nom 1.00 / docstring 0.10 / enonce 0.00 / termes cooperation
- **1.00** -- `one_sub_pow_le_exp` (MyIA.AI.Notebooks/ML/learning_theory_lean/PacLearning/PacFiniteBound.lean:116) et `one_sub_pow_le_exp_mul` (MyIA.AI.Notebooks/SymbolicAI/Lean/mimo_lean/Converse.lean:179) -- nom 1.00 / docstring 0.00 / enonce 0.33 / termes exp, le, one, sub
- **1.00** -- `countP_length_filter` (MyIA.AI.Notebooks/SymbolicAI/Lean/KNOTS/knot_lean/Knots/ArcPartition.lean:842) et `Canonical.filter` (MyIA.AI.Notebooks/SymbolicAI/Lean/conway_lean/Conway/Life/GridCanonical.lean:239) -- nom 1.00 / docstring 0.11 / enonce 0.22 / termes filter
- **1.00** -- `jumpCapturedF_reconstruction_of_still_life` (MyIA.AI.Notebooks/SymbolicAI/Lean/conway_lean/Conway/Life/HashlifeMarginFragment.lean:1216) et `reconstruction` (MyIA.AI.Notebooks/SymbolicAI/Lean/sensitivity_lean/Sensitivity/Fourier.lean:105) -- nom 1.00 / docstring 0.03 / enonce 0.00 / termes reconstruction
- **1.00** -- `jumpCapturedF_reconstruction_of_period` (MyIA.AI.Notebooks/SymbolicAI/Lean/conway_lean/Conway/Life/HashlifeMarginFragment.lean:1589) et `reconstruction` (MyIA.AI.Notebooks/SymbolicAI/Lean/sensitivity_lean/Sensitivity/Fourier.lean:105) -- nom 1.00 / docstring 0.03 / enonce 0.00 / termes reconstruction
- **1.00** -- `jumpCapturedF_reconstruction_of_period_mod` (MyIA.AI.Notebooks/SymbolicAI/Lean/conway_lean/Conway/Life/HashlifeMarginFragment.lean:1669) et `reconstruction` (MyIA.AI.Notebooks/SymbolicAI/Lean/sensitivity_lean/Sensitivity/Fourier.lean:105) -- nom 1.00 / docstring 0.03 / enonce 0.00 / termes reconstruction
- **1.00** -- `jumpCapturedF_reconstruction_of_spaceship` (MyIA.AI.Notebooks/SymbolicAI/Lean/conway_lean/Conway/Life/HashlifeMarginFragment.lean:2509) et `reconstruction` (MyIA.AI.Notebooks/SymbolicAI/Lean/sensitivity_lean/Sensitivity/Fourier.lean:105) -- nom 1.00 / docstring 0.03 / enonce 0.00 / termes reconstruction
- **1.00** -- `jumpCapturedF_reconstruction_of_spaceship_mod` (MyIA.AI.Notebooks/SymbolicAI/Lean/conway_lean/Conway/Life/HashlifeMarginFragment.lean:2689) et `reconstruction` (MyIA.AI.Notebooks/SymbolicAI/Lean/sensitivity_lean/Sensitivity/Fourier.lean:105) -- nom 1.00 / docstring 0.03 / enonce 0.00 / termes reconstruction
- **1.00** -- `jumpCapturedF_reconstruction_of_static_frame` (MyIA.AI.Notebooks/SymbolicAI/Lean/conway_lean/Conway/Life/HashlifeMarginFragment.lean:4137) et `reconstruction` (MyIA.AI.Notebooks/SymbolicAI/Lean/sensitivity_lean/Sensitivity/Fourier.lean:105) -- nom 1.00 / docstring 0.04 / enonce 0.00 / termes reconstruction

## Methode

1. **Population** : toutes les declarations `theorem` / `lemma` des fichiers `.lean` du depot, hors Lean vendu (`.lake/packages`), hors `_peters/` et hors fixtures de reference. Les freres `_en` (convention i18n #4980) sont exclus : ils republient le contenu FR.
2. **Rapprochement** : les declarations sont indexees par les tokens de leur **nom** (namespace retire, camelCase decoupe, tokens de trois caracteres ou plus). Deux declarations ne sont comparees que si un token de nom est commun.
3. **Filtre de rarete** : le token commun doit etre porte par au plus 8 declarations dans le depot. C'est ce qui ecarte les lemmes generiques (`card`, `trans`, `wf`, `le`), dont le nom se recoupe partout sans que les lemmes ne prouvent le meme resultat.
4. **Filtre de contenu** : le token doit figurer dans la docstring des **deux** declarations, et les deux docstrings doivent etre proches (Jaccard >= 0.15) pour classer la paire en **forte**.
5. **Perimetre** : une paire porte sur deux declarations de **lacs differents**. A l'interieur d'un lac, un resultat reecrit dans le vocabulaire du lac n'est pas un doublon.

**Controle positif** : la paire Arrow (`MyIA.AI.Notebooks/GameTheory/game_theory_lean/SocialChoice/Arrow.lean` contre `MyIA.AI.Notebooks/GameTheory/lean_game_defs/SocialChoice.lean`) et la paire Sen (`.../game_theory_lean/SocialChoice/Sen.lean` contre le meme fichier) doivent apparaitre parmi les paires fortes -- ce sont les deux doublons que #23097 avait conclut absents en comparant les noms de modules. Le test qui verifie ce point est `scripts/lean/tests/test_lean_theorem_duplicates.py`.
