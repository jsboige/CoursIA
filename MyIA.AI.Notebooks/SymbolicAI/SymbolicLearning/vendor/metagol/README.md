# Metagol (vendored)

`metagol.pl` est embarque ici (avec sa licence) pour que le notebook
[SL-6 Moteurs ILP modernes](../../SL-6-ModernILP.ipynb) puisse executer le
**vrai** moteur Metagol sans dependance reseau a l'execution.

## Source

- **Projet** : Metagol — Meta-Interpretive Learning (MIL)
- **Upstream** : https://github.com/metagol/metagol
- **Auteurs** : Andrew Cropper, Stephen Muggleton et al. (« Metagol authors »)
- **Reference** : S. Muggleton, D. Lin, A. Tamaddoni-Nezhad,
  *Meta-interpretive learning of higher-order dyadic datalog*, Machine Learning 100, 2015.

## Licence

**BSD 3-Clause** (permissive) — voir [`LICENSE`](./LICENSE). Cette licence
autorise la redistribution du source a condition de conserver la notice de
copyright et le texte de la licence, ce qui est fait ici (`metagol.pl`
conserve son en-tete de copyright, et `LICENSE` reproduit le texte complet).

## Statut upstream

Le depot Metagol est **archive** : ses auteurs orientent desormais vers
**Popper** (Learning From Failures), egalement presente dans cette serie
(SL-4 et SL-6). Metagol reste pedagogiquement precieux : c'est l'exemple
canonique d'**invention de predicat** par metarules, capacite qu'il demontre
en inventant un predicat auxiliaire (`ancestor_1`) lors de l'apprentissage de
la relation `ancestor` recursive dans SL-6.

## Runtime

`metagol.pl` est consulte par SWI-Prolog (`swipl`) ; le notebook l'execute
dans un sous-processus isole (l'etat global de Metagol se cumulerait entre
deux apprentissages dans le meme processus).
