# Compagnons Axler — comparaison et règle de distillation (Fille 3.2, Epic Origami)

**Objet :** choisir, pour chaque exercice d'Axler *Linear Algebra Done Right* (4e éd.), la voie de distillation — marche `.lean` formelle ou solution écrite au carnet — pour les marches 3+ de la Fille 3.1 de [#24838](https://github.com/jsboige/CoursIA/issues/24838). Fille 3.2 de cette Epic. Établi par la lane `myia-po-2028:CoursIA` (2026-11-22) ; toutes les mesures ci-dessous sont **firsthand** (arbres GitHub, README, fichiers de section échantillonnés), commandes de reproduction en fin de page.

## 1. Les deux compagnons, mesurés

| | [linear-algebra-done-right-lean](https://github.com/rkirov/linear-algebra-done-right-lean) (rkirov, 30★) | [Axler-Solutions](https://github.com/blanketism/Axler-Solutions) (blanketism, 5★) |
|---|---|---|
| **Licence** | **Apache-2.0**, déclarée en footer du README (sha `cb6fd5608934` lu le 2026-11-16, correctif après Concern mainteneur sur #26949) — pas de fichier LICENSE à la racine | **Aucune** — lecture seule stricte |
| **Couverture** | Ch. 1-9 : un fichier de section (`Section_1A`…`Section_9D`) + `Chapter_4` + deux hors-séries (`HarmonicPolynomial`, `L2Interval`) | Ch. 1-9 : un `.tex` par section (`exercises/chapter-N/…`) + `appendix/` (solutions alternatives ch. 1-9) |
| **Forme** | Énoncés du livre **prouvés** en idiomes Mathlib (`HasEigenvalue`, `aeval`, `Commute`, `IsUpperTriangular`) ; exercices = `theorem exercise_5A_N` énoncés **avec `sorry` à remplir** (mesure 5A : 71 `sorry` pour 67 énoncés `theorem`, livre et exercices confondus) | Énoncés restitués + **solutions rédigées complètes** (mesure `5a.tex` : 43 exercices, ~43 ko), y compris « prove or give a counterexample » et raisonnements multi-étapes |
| **Positionnement déclaré** | « A Lean translation of all definitions, proofs, examples, and exercises (without solutions)… cloned and worked through, replacing each `sorry` with a real proof » — le compagnon de Tao *Analysis I* comme canon | « clear, written solution strategies, concise mathematical exposition » — guide de révision pour lecteur du livre |
| **Qualité** | Conventions [companion-helper](https://github.com/rkirov/companion-helper) : Mathlib direct (jamais redéfinir `Field`/`Module`), ponts `recall` Axler→Mathlib, marqueur `@[avoiding …]` sur les exercices dont la solution Mathlib en une ligne tuerait le point pédagogique ; `REVIEW_PATTERNS.md` documente P1-P4 (exemples formalisés, généralité fidèle au livre, idiomes Mathlib, énoncés conformes) ; brouillon AI revu ligne à ligne (~1-2 h/sous-section) | Prose pédagogique propre, contre-exemples explicites ; statut « selected exercises » (couverture non exhaustive par section) |

**Convergence structurelle : aucun des deux ne couvre le ch. 10** (trace et déterminants). Ce n'est pas un accident de calendar : le choix d'Axler de rejeter les déterminants en fin de livre en fait le chapitre le moins « companion-friendly » — le compagnon Lean s'arrête au ch. 9, les solutions également.

## 2. Typologie mesurée des exercices (7 sections pivotes pour les marches 3+)

Comptages par expressions régulières sur les `.tex` restitués (la terminologie de l'énoncé dicte la voie) :

| Section | Exercices | « prove » | « give an example / find » | « counterexample » | « describe » |
|---|---|---|---|---|---|
| 3E | 19 | 21 | 0 | 0 | 0 |
| 3F | 33 | 25 | 0 | 0 | 2 |
| 5A | 43 | 35 | 10 | 1 | 0 |
| 5B | 29 | 18 | 3 | 0 | 0 |
| 6A | 35 | 23 | 0 | 2 | 0 |
| 6B | 23 | 13 | 3 | 0 | 0 |
| 7A | 32 | 22 | 5 | 1 | 0 |

Lecture : **60-75 % des exercices sont des « prove » purs** — des énoncés universels dont la traduction Lean est naturelle. Le reste se partage entre constructions explicites (« give an example », « find all », contre-exemples) et, marginalement (2 occurrences sur 7 sections), du « describe ».

## 3. Règle de distillation (la décision de la Fille 3.2)

Pour chaque exercice d'une marche, la voie se lit sur le **verbe de l'énoncé** :

1. **« Prove that … » universel** (invariance, stabilité, algèbre de `p(T)`, etc.) → **marche `.lean`**. Le compagnon Apache-2.0 fournit l'énoncé prêt (son `sorry` = notre stub étudiant : la correspondance est exacte, un exercice du livre ↔ un `theorem exercise_N` à remplir). Adapter avec attribution, pas recopier : nos marches gardent leurs propres noms et leur prose française (convention i18n du dépôt).
2. **« Give an example / find »** (construire un objet) → formel **possible mais à juger** : le compagnon traite ces cas par `def` concret + lemme (`T_5_6`, `forwardShift`) — le pattern est transférable quand la construction EST la leçon (5.9 : opérateur réel sans valeur propre réelle). Sinon, **cellule écrite du carnet**.
3. **« Prove or give a counterexample »** → les deux voies se valent ; le compagnon tranche dans l'énoncé même (`¬ ∃ γ : ℝ, HasEigenvalue …`). Pour nos marches : formel si le contre-exemple est réutilisé en aval, écrit sinon.
4. **« Describe »** (décrire toutes les valeurs propres…) → **solution écrite** : pas de type Lean naturel pour « décrire » ; la réponse est une phrase mathématique, pas un théorème.
5. **Calcul multi-étapes sur données numériques** (matrices 3×3 concrètes) → **écrit** : le coût de formalisation dépasse ce que la leçon y gagne (constat P1 du compagnon : les exemples numériques du livre sont formalisés quand ils portent un théorème, jamais pour le calcul lui-même).

**Signal `@[avoiding]` à reprendre tel quel :** quand le compagnon marque un exercice `@[avoiding …]`, la solution Mathlib une-ligne existe et **tue le point pédagogique**. Nos marches font pareil : garder l'énoncé du livre, prouver « à la main », ne pas binder l'API haute de Mathlib dans l'exercice. C'est le même geste que nos exercices étudiant face aux organes du dépôt (règle organ-first : la copie pédagogique déclarée).

**Conventions transférables du compagnon** (Apache-2.0, adapter avec attribution) : Mathlib direct + pont `recall` ; numérotation du livre conservée dans les docstrings (`T_5_57`, `exercise_5A_13`) ; les quatre patterns de revue P1-P4 comme checklist de qualité d'une marche.

## 4. Licences et attribution (application des règles de l'Epic)

- **Livre** : *Linear Algebra Done Right*, 4e éd., **CC BY-NC 4.0** — copie archivée au gisement : `G:\Mon Drive\MyIA\IA\Bibliographie IA\Pedagogie-Proves\2024 - Axler - Linear Algebra Done Right (Springer, 4e edition, CC BY-NC 4.0, version 30 oct 2026).pdf`. Toute attribution d'un résultat du livre s'écrit depuis cette copie (règle bibliography-hygiene).
- **Compagnon Lean Apache-2.0** : citer, présenter, consommer **avec attribution** (cap confirmé le 16/11 après Concern mainteneur). Une adaptation cite le dépôt et le sha dans le docstring du module.
- **Axler-Solutions sans licence** : **lecture seule** — sert à calibrer le niveau attendu des solutions écrites (longueur, structure, place du contre-exemple), jamais une ligne recopiée.

## 5. Application aux marches 3+ de la Fille 3.1

État mesuré au 2026-11-22 : marche 1 (ch. 1-2, `EspacesVectoriels` + `DimensionFinie`) mergée (#26894) ; marche 2 (ch. 3.A/B/D) en PR #26949 ouverte. Les marches suivantes trouvent ici leur carte :

| Marche | Voie dominante | Source formelle | Notes |
|---|---|---|---|
| 3C, 3E, 3F (matrices, quotient, dual) | `.lean` (100 % « prove » mesuré en 3E ; 3F porte les 2 seuls « describe ») | `Section_3C/3E/3F.lean` du compagnon | les 2 « describe » de 3F → solutions écrites au carnet compagnon de la série |
| Ch. 5 (valeurs propres) | `.lean` pour les « prove », écrit pour les 10 « find » de 5A | `Section_5A-5E.lean` (idiomes `HasEigenvalue`, `aeval`) | le plus riche en constructions : arbitrage au cas par cas (règle 2) |
| Ch. 6 (produit scalaire) | `.lean` | `Section_6A-6C.lean` | 6A/6B quasi exclusivement « prove » |
| Ch. 7 (opérateurs) | `.lean` | `Section_7A-7F.lean` (`IsUpperTriangular` via `tfae`) | cf. P3 : Schur bascule par `tfae_upperTriangular` |
| Ch. 10 (déterminants) | **à écrire nous-mêmes** | aucun compagnon ne le couvre | depuis Mathlib (`LinearAlgebra.det`) ; gap assumé, cohérent avec le choix d'Axler de clore par là |

## 6. Reproduire les mesures

```bash
# Arbres et licences
gh api repos/rkirov/linear-algebra-done-right-lean/git/trees/HEAD?recursive=1 --jq '[.tree[].path]'
gh api repos/blanketism/Axler-Solutions/git/trees/HEAD?recursive=1 --jq '[.tree[].path]'
# Densité d'un fichier de section (sorry / avoiding / theorems)
gh api repos/rkirov/linear-algebra-done-right-lean/contents/LinearAlgebraDoneRightLean/Section_5A.lean --jq .content \
  | python -c "import base64,sys; c=base64.b64decode(sys.stdin.read()).decode(); print(c.count('sorry'), c.count('@[avoiding'), c.count('theorem '))"
# Typologie des énoncés par section (les compteurs « prove/example/counterexample/describe »)
gh api repos/blanketism/Axler-Solutions/contents/exercises/chapter-5/5a.tex --jq .content
```

See [#24838](https://github.com/jsboige/CoursIA/issues/24838) (Fille 3.2) — la décision remonte au fil de l'Epic ; cette page en est la référence durable.
