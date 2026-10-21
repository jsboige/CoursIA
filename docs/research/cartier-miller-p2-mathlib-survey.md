# Cartier–Miller (Jordan) — P2 : enquête d'organes Mathlib 4 + arbitrage des candidats

**Issue** : [#19452](https://github.com/jsboige/CoursIA/issues/19452) — brique **P2** du plan de
formalisation du papier de David Jordan, *Cartier–Miller evaluation of genus-one coefficient
sums* (draft non relu, assisté par IA).
**Grain** : `DEEP/research-code` — une **mesure** de couverture (lecture du source, citations
`file:line`), pas un jugement de substance.

## 0. Portée et méthode

L'étape P2 de l'issue demande deux choses : (1) **arbitrer** les trois candidats de
formalisation ; (2) **mesurer l'état de couverture Mathlib** des trois piliers du papier
(courbes elliptiques / Frobenius / Cartier).

**Méthode de mesure.** Le Mathlib 4 vendé dans le dépôt (8 checkouts `.lake/packages/mathlib/`,
ici lu dans `Search/search_lean/`) a ses **fichiers working-tree purgés** (crise disque ; la
question « PURGE `.lake` » est ouverte côté user), mais ses **objets git sont intacts**
(HEAD `db584cd6d4`, toolchain **v4.33.0**). La couverture est donc mesurée sur le **contenu
commit** via `git ls-files` / `git grep … HEAD -- 'Mathlib/'` / `git show HEAD:<chemin>` —
c'est le source Mathlib réel, pas un résumé.

**Garde de l'issue (portée dans chaque brique).** Le papier est un **draft non relu par des
experts** ; la validation numérique (20 311 admissibles + 368 exceptionnels + 4 357
vérificateurs indépendants) est une **corroboration computationnelle, pas une preuve**. Le
point aveu de l'issue : l'elliptique/char-p n'est **pas** la spécialité de la lane — l'effort
est **formaliste** (Lean/Mathlib), l'arbitre de substance reste extérieur.

## 1. Couverture Mathlib 4 (mesurée, `file:line`)

| Pilier du papier | Organes Mathlib 4 | État | Preuve mesurée |
|---|---|---|---|
| **Courbes elliptiques** (base j=1728, Weierstrass) | `WeierstrassCurve` (`AlgebraicGeometry/EllipticCurve/Weierstrass.lean:77`) + invariants `b₂…b₈, c₄, c₆, Δ` (`:101`–`:132`) ; `DivisionPolynomial/` ; `Jacobian/` ; `Reduction.lean` ; `LFunction.lean` ; `NormalForms.lean` ; `ModelsWithJ.lean` | **PRÉSENT, fort** | **19 fichiers** dans `AlgebraicGeometry/EllipticCurve/` |
| **Frobenius** (caractère p) | `LinearMap.frobenius` + `frobenius_def : frobenius R S p x = x ^ p` (`Algebra/CharP/Frobenius.lean:126`) + `iterateFrobenius` (`:128`) | **PRÉSENT, fort** | **36 fichiers** mentionnent `Frobenius` |
| **Polynômes de division** (brique de l'algorithme de Miller) | `DivisionPolynomial/Basic.lean` + `DivisionPolynomial/Degree.lean` | **PRÉSENT** | **1 fichier** |
| **Descente / opérateur de Cartier** (pilier 1) | — | **ABSENT** | `cartier` = **0** fichier dans tout `Mathlib/` |
| **Appariage de Weil / Miller** (pilier 2) | — | **ABSENT** | `weil_pairing`/`WeilPairing` = **0** (voir §1.1 : les 124 hits bruts sont des faux positifs) |
| **Comptage de points / borne de Hasse / formule de Serre** (pilier 3) | — | **ABSENT** | `hasse` / `serre` / `point_count` / `frobenius` dans `EllipticCurve/` = **0** |
| Cohomologie de descente (de Rham / Hodge / cristalline) | — | **marginal** | de Rham = 1, Hodge = 3, cristalline = 5 fichiers ; **aucun opérateur de Cartier** |

### 1.1 Faux positifs écartés (G.1 — vérifié à la source)

Un premier `git grep -i "weil\|miller"` renvoie **124 fichiers**, ce qui aurait pu faire
croire à une couverture des appariages. Le tri à la source montre que **c'est un artefact de
noms de personnes**, pas une couverture mathématique :

- `miller` → **110 fichiers**, tous des en-têtes de copyright **« Kyle Miller »**
  (`Algebra/Quandle.lean`, `Combinatorics/Hall/Basic.lean`, …).
- `weil` → **14 fichiers** = **« Felix Weilacher »** (`Algebra/Group/Action/Equidecomp.lean`)
  et **« Henstock-Kurzweil »** (`Analysis/BoxIntegral/*`).

**Conclusion : aucun appariage de Weil ni de Miller n'existe dans Mathlib 4.** Le même
raisonnement s'applique à `cartier` (0), `hasse` (0), `serre` (0).

> Note : 12 fichiers du répertoire `EllipticCurve/` mentionnent « Tate » (Birational, Cover,
> Affine, Projective, Jacobian, `DivisionPolynomial/Degree.lean`, `Reduction.lean`, …) —
> c'est l'usage du terme dans les définitions de la courbe / du module, **pas** un appariage
> de Tate exploitable tel quel pour l'algorithme de Miller.

## 2. Arbitrage des trois candidats de formalisation

L'issue liste trois candidats. Critère d'arbitrage : **réusage d'organes Mathlib PRÉSENTS**
(pour) vs **dépendance d'organes ABSENTS** (contre) vs **oracle numérique déjà harnessé**
(facteur de risque).

| # | Candidat | Réutilise des organes PRÉSENTS | Dépend d'organes ABSENTS | Oracle |
|---|---|---|---|---|
| 3 | **Quarter-point j=1728** : `U_p(n) ≡ 4·B_n + (9/4)·a_n (mod p)` sur la courbe d'invariant `j = 1728` | Weierstrass + invariants `c₄/Δ` (j = c₄³/Δ) · Frobenius (`a_n` = trace) · division polynomials | **aucun** pour *énoncer* la congruence | **déjà harnessé** (P1) |
| 2 | **Normalisation du cas exceptionnel** (`τ = χ`, transfert additif Serre / Semaev / Rück / Voloch, char p direct) | Frobenius | **oui** : `serre` = 0 → l'organe doit d'abord être **construit** | à harnaiser |
| 1 | **Identité explicite** — le résultat central O(log p) | division polynomials (récurrences de Miller) · Frobenius (trace exacte) | **oui** : le **montage de descente de Cartier** (0) | à harnaiser |

### Arbitrage

- **Candidat 3 (quarter-point j=1728) = meilleur premier brick.** C'est le seul des trois qui
  **s'énonce en réutilisant exclusivement des organes présents** (Weierstrass/Frobenius/
  division polynomials) **sans dépendre d'un organe absent**, et c'est le seul dont l'**oracle
  numérique est déjà harnessé** (P1). Risque minimal, valeur de base maximale.
- **Candidat 2 (normalisation exceptionnelle) = différé.** Il exige de **construire**
  l'organe `serre` (absent) avant de pouvoir l'appuyer ; ce n'est pas une brique de base,
  c'est une extension.
- **Candidat 1 (identité explicite) = bout de chaîne.** C'est le résultat le plus précieux du
  papier, mais il s'appuie sur la **descente de Cartier** (absente) : il se formalise
  **après** que la base j=1728 est établie et que le montage de Cartier a été construit.

## 3. Recommandation P3

**P3 = brique quarter-point j=1728 (candidat 3).**

- Un **lake neuf** (modèle [EPIC #17845](https://github.com/jsboige/CoursIA/issues/17845))
  construit la courbe d'invariant `j = 1728` via `WeierstrassCurve`
  (`AlgebraicGeometry/EllipticCurve/Weierstrass.lean`), **énonce** la congruence
  `U_p(n) ≡ 4·B_n + (9/4)·a_n (mod p)`, et la **prouve formellement** — l'oracle numérique
  de P1 servant de **vérificateur indépendant**, jamais de preuve.
- **Séquence P3+** : `j=1728` (base) → **candidat 2** (construire l'organe `serre`, puis
  normaliser le cas exceptionnel) → **candidat 1** (identité explicite, bout de chaîne,
  après le montage de Cartier).
- **Garde de chaque brique** : énoncé + **preuve formelle** Lean ; l'oracle numérique est une
  corroboration indépendante, **jamais** la preuve.

## 4. Résiduel et honnêteté

- Quatre organes sont **absents** de Mathlib 4 et constituent un **investissement à
  construire** en P3+ : **Cartier** (0), **appariage de Weil/Miller** (0), **borne de Hasse**
  (0), **formule de Serre** (0). Ce n'est pas un obstacle à la brique P3 (qui les contourne),
  c'est le coût du P3+ (candidats 1–2).
- Le dépôt **n'a aucune lane spécialisée elliptique/char-p** ; l'effort de formalisation est
  **formaliste** (Lean/Mathlib) et l'arbitre de la substance mathématique reste extérieur au
  cluster (aveu de l'issue).
- **Prochaine étape actionnable** : ébauche du lake j=1728 (brique P3) — à dispatcher comme
  grain `DEEP/notebook-lean` / `research-code` distinct, hors du présent P2.

---

*Mesure de couverture : Mathlib 4 v4.33.0 (HEAD `db584cd6d4`), lue sur le contenu git du
checkout vendé. Qualification : les états PRÉSENT/ABSENT ci-dessus sont **mesurés**
(`git grep`/`ls-files`/`show` sur `HEAD`) ; l'arbitrage et la recommandation P3 sont
**jugements** fondés sur cette mesure.*
