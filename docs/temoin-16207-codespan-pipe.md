# Témoin #16207 — CODE_SPAN_PIPE tel que mergé dans #16177

PR de test éphémère : ce fichier reproduit **verbatim** la table d'intro du
blob original de `Lean-13b-CHSH-Tsirelson-Native.ipynb` (commit d760ccead2,
avant la réparation e05291ec52) — la ligne `` `|score| ≤ 2` `` porte des pipes
brutes dans des code spans, la pathologie qui a mergé sans signal le 13/09.

| Statut | Contenu |
|---|---|
| **prouvé localement** (ce lake) | la frontière classique déterministe (`|score| ≤ 2`) et randomisée (`|expectedScore| ≤ 2`), la réécriture `(√2)^3 = 2√2`, et la séparation stricte `2 < 2√2` |
| **importé avec preuve noyau** | la borne quantique elle-même : `Mathlib.Algebra.Star.CHSH.tsirelson_inequality`, dont `tsirelson_bound` est la forme usuelle |
| **non établi ici** | la saturation de $2\sqrt{2}$ (aucune stratégie quantique explicite dans ce lake), la construction matricielle de Pauli, l'interprétation probabiliste complète d'un état quantique, et la borne bilatérale en norme d'opérateur |
