# Exemples Mathlib

Exemples d'utilisation basique de Mathlib pour la série SymbolicAI/Lean.

**Mathlib** est la bibliothèque mathématique unifiée de Lean 4 : un corpus
communautaire de définitions, de lemmes et — surtout pour l'apprenant — de
**tactiques d'automatisation**. Ce module minimal est le « smoke test » de
l'installation Mathlib : il ferme quatre buts représentatifs avec les tactiques
du quotidien (`ring`, `linarith`, `omega`, `rw`), confirmant que
`lake build MathLibExamples` compile contre une Mathlib fonctionnelle. C'est
aussi une première prise en main des automatiseurs de Lean avant d'aborder les
projets plus ambitieux (`calibration_lean`, `JeuDeLaVie/conway_lean`, `sensitivity_lean`).

## Statut

- **Toolchain** : v4.33.0
- **Compte de sorry** : 0
- **Build** : `lake build MathLibExamples` -- SUCCESS
- **Dépendances** : Mathlib4
- **Couverture i18n (EPIC #4980)** : lake entièrement bilingue FR/EN — `Basic.lean` FR canonique + sibling `Basic_en.lean` miroir sur `main` (PR #6664, 2026-07-15). Convention EPIC #4980 Option A : docstrings `/-- ... -/` et commentaires `-- ...` diffèrent entre FR et EN, signatures et preuves byte-identiques — vérifié par `scripts/lean/check_i18n_siblings.py` : **toutes les paires byte-identical, 0 drift, 0 orphan** (y compris les siblings d'`examples/` et ce module).

## Modules

| Fichier | `_en` | sorry | Description |
|---------|-------|-------|-------------|
| `MathLibExamples/Basic.lean` | `MathLibExamples/Basic_en.lean` | 0 | Patterns et exemples d'utilisation basique de Mathlib |
| [`MathLibExamples/ProofBridge.lean`](MathLibExamples/ProofBridge.lean) | [`MathLibExamples/ProofBridge_en.lean`](MathLibExamples/ProofBridge_en.lean) | 0 | Produits, sommes et preuves paramétriques après le jeu |
| [`MathLibExamples/WallpaperP4m.lean`](MathLibExamples/WallpaperP4m.lean) | [`MathLibExamples/WallpaperP4m_en.lean`](MathLibExamples/WallpaperP4m_en.lean) | 0 | Groupe ponctuel du pavage p4m — matrices des générateurs du moteur `scripts/symmetry/wallpaper.py` |
| [`MathLibExamples/LinearAlgebra.lean`](MathLibExamples/LinearAlgebra.lean) | [`MathLibExamples/LinearAlgebra_en.lean`](MathLibExamples/LinearAlgebra_en.lean) | 0 | La marche Axler — algèbre linéaire exécutable, paliers successifs |
| [`MathLibExamples/CartierMiller.lean`](MathLibExamples/CartierMiller.lean) | [`MathLibExamples/CartierMiller_en.lean`](MathLibExamples/CartierMiller_en.lean) | 0 | Certificat de télescopage, identité préfixe et identité du point de quart sous une récurrence locale ; base `j = 1728` via `WeierstrassCurve` |
| [`MathLibExamples/CartierMillerCoefficients.lean`](MathLibExamples/CartierMillerCoefficients.lean) | [`MathLibExamples/CartierMillerCoefficients_en.lean`](MathLibExamples/CartierMillerCoefficients_en.lean) | 0 | La suite binomiale du point de quart et sa récurrence à tout indice ; congruence en `ZMod p` pour tout premier `p ≡ 1 (mod 4)` |

## Après le jeu : un premier module

Après les notions de types, fonctions, produits et sommes de `Lean-01` à
`Lean-06`, ouvrez [`ProofBridge.lean`](MathLibExamples/ProofBridge.lean).
Trois exercices corrigés y construisent une distribution, établissent ses
aller-retours et vérifient sa compatibilité avec des fonctions. Les deux
calculs de branches servent de témoins ; les théorèmes couvrent tous les types
et toutes les valeurs. Pour les modifier, copiez le module dans votre projet
Lean, puis comparez vos définitions et preuves aux corrections.

Dans ce répertoire, avec la toolchain du fichier `lean-toolchain` installée :

```sh
lake build MathLibExamples.ProofBridge MathLibExamples.ProofBridge_en
```

Ces cibles utilisent `Std` et ne demandent pas la compilation de tout Mathlib.
Elles constituent une étape vers un projet personnel, sans installer de nouveau
lake ni remplacer le parcours d'installation du jeu.

## La couche Cartier–Miller

Une paire de modules prolonge la série sur un même objet, le point de quart
d'une courbe elliptique. Ils se lisent dans cet ordre.

[`CartierMiller.lean`](MathLibExamples/CartierMiller.lean) déduit l'identité
préfixe et l'identité du point de quart d'une récurrence locale reçue en
hypothèse, puis construit la base `j = 1728` : courbe de Weierstrass et invariant
`j` établi formellement par `c₄^3 / Δ`.
[`CartierMillerCoefficients.lean`](MathLibExamples/CartierMillerCoefficients.lean)
construit ensuite la suite binomiale elle-même et prouve sa récurrence à tout
indice, dans un corps où `8` est inversible. Les identités deviennent alors des
théorèmes sur cette suite explicite, et la congruence du point de quart vaut en
`ZMod p` pour tout premier `p ≡ 1 (mod 4)`.

Ce que la couche **ne** prouve pas, et qu'il ne faut pas y lire : l'identification
de la somme des coefficients à l'évaluation de Cartier–Miller, l'égalité de `a_n`
avec la trace de Frobenius de la courbe, et tout énoncé sur les courbes
elliptiques au-delà de la base de Weierstrass. Les énoncés sont transcrits des
transcriptions du dépôt d'un manuscrit de travail non révisé par les pairs ;
l'oracle numérique de `scripts/cartier_miller/` corrobore les calculs par
l'exécution, il ne les prouve pas.

```sh
lake build MathLibExamples.CartierMillerCoefficients MathLibExamples.CartierMillerCoefficients_en
```

Les deux cibles importent Mathlib, comme `Basic.lean`.

## Résultats clés

- Illustre les tactiques Mathlib courantes et les schémas de preuve
- Sert de référence aux étudiants apprenant Lean 4 avec Mathlib

## Concepts clés

Les quatre exemples de [`MathLibExamples/Basic.lean`](MathLibExamples/Basic.lean)
introduisent les automatiseurs les plus utilisés en Lean 4 :

| Tactique | Rôle | Exemple `Basic.lean` |
|----------|------|----------------------|
| `ring` | Identités d'anneau commutatif (développer / factoriser) | `(a + b)^2 = a^2 + 2*a*b + b^2` sur `ℤ` |
| `linarith` | Inégalités linéaires par combinaison (ici sur `ℚ`) | `x ≤ 3*y ∧ y ≤ 1 → x ≤ 3` |
| `omega` | Arithmétique de Presburger sur `ℕ`/`ℤ` (Lean core depuis v4.30) | `n < n + 1` sur `ℕ` |
| `rw` + `ring` | Substituer des égalités d'hypothèses, puis clôture algébrique | `a = b ∧ b = c → a + a = 2*c` sur `ℤ` |

Ces quatre tactiques couvrent une large part des buts « calculatoires »
rencontrés en pratique : `ring` pour l'algèbre, `linarith` et `omega` pour les
inégalités et l'arithmétique entière, `rw` pour réécrire par égalité
d'hypothèses. Savoir laquelle invoquer est la première compétence tactique en
Lean, et ce module est le terrain d'entraînement minimal pour l'acquérir.

## Notes

- **Rôle assumé : smoke-test / environnement de validation** — ce lake vérifie
  que la toolchain et Mathlib résolvent les quatre automatiseurs du quotidien.
  Aucun notebook n'importe le module `MathLibExamples` : les notebooks de la
  série importent Mathlib directement ; `Lean-26-Munkres-Tribute.ipynb` utilise
  ce lake comme **environnement d'exécution** du kernel `lean4-wsl` (résolution
  des olean Mathlib), sans consommer son contenu.
- Partie de la série pédagogique SymbolicAI/Lean

## Conclusion

Un **lake de référence** avec un smoke-test minimal de schémas d'utilisation basique de Mathlib
(`MathLibExamples/Basic.lean`, 0 `sorry`, `lake build MathLibExamples` SUCCESS) :
un **smoke-test** de l'installation Mathlib — et l'environnement d'exécution
Mathlib du kernel `lean4-wsl` pour Lean-26 — pas un compagnon module-à-notebook.
Il est volontairement minimal : un point de départ pour les étudiants, pas un
aperçu exhaustif.

### Où aller ensuite

- **Prise en main Mathlib côté notebook** : `Lean-06-Mathlib-Essentials-Lean.ipynb`
  (tactiques exercées sur Mathlib importé directement) et
  `Lean-26-Munkres-Tribute.ipynb` (cours 18.901 de Munkres, exécuté sur ce lake).
- **Projets Lean plus complets** : [`calibration_lean/`](../calibration_lean/),
  [`conway_lean/`](../JeuDeLaVie/conway_lean/), [`sensitivity_lean/`](../sensitivity_lean/)
  — projets Lean de production bâtis sur Mathlib.
