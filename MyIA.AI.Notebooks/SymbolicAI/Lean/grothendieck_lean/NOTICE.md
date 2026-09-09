# Socle fppf — grothendieck_lean

## Source

Adaptation pédagogique du dépôt
[`anthropics/fermats-last-theorem`](https://github.com/anthropics/fermats-last-theorem),
fichier `Definitions/Def_AlgebraicGeometry_FppfSiteCohomology.lean`, commit
`aa2d8b34692b16c70f699536de0d8e75b9a3e9ef`.

Cette première tranche reprend et documente uniquement le socle formel des
lignes 1–65 de la source : propriété fppf, précouverture, prétopologie,
topologie de Grothendieck et inclusions étale/Zariski. Le petit site fppf et
sa cohomologie sont volontairement exclus.

## Licence

Le code source amont est publié sous licence **Apache 2.0**. Cette adaptation
préserve le copyright Anthropic et la même licence ; son texte complet est
reproduit dans `LICENSE-Apache-2.0.txt`. Les docstrings françaises, le sibling
anglais et le bornage pédagogique sont des additions CoursIA.

## Environnement

- Lean : `leanprover/lean4:v4.33.0`
- Mathlib : `db584cd6d46c92f209a44c0f1c829460d327499d`
- Option locale au module : `backward.isDefEq.respectTransparency false`

L'option de transparence n'est pas ajoutée au `lakefile` : son périmètre reste
borné à `Fppf.lean` et `Fppf_en.lean`, où elle est requise pour synthétiser les
instances de l'intersection `Flat ⊓ LocallyOfFinitePresentation`.
