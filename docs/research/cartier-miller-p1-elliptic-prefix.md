# Cartier–Miller P1 (mini) — `elliptic_prefix.py` ↔ manuscrit

**Cible.** Issue [#19452](https://github.com/jsboige/CoursIA/issues/19452) ·
**Suite** de [#19487](https://github.com/jsboige/CoursIA/pull/19487) (P0
cartography, mémo `cartier-miller-p0-cartography.md`). **Source externe**
[`bbrhuft/Cartier-Miller-...`](https://github.com/bbrhuft/Cartier-Miller-evaluation-of-genus-one-coefficient-sums),
pin reproductible `37a9b727dfd5034af0b8aa8185246d58008b9e5c` (Hermes
08:13Z). **Statut.** P1 *mini* = lecture ligne-par-ligne de
`elliptic_prefix.py` (l. 1–265), confrontation aux
formules énoncées §4 (Quarter-point) et §5 (Regular identity) du
manuscrit.

**Périmètre de cette tranche.** Cinq composants sur les huit de la P1
pleine (P0 §6 : P1 sur fichiers `elliptic_prefix.py` + `pilot.py` +
`point_count.py`). Le présent mémo couvre `elliptic_prefix.py` *seul* ;
`pilot.py` et `point_count.py` restent à
traiter en cycles dédiés, dans la même veine (3-5 h par fichier pour la
P1 pleine, ici en ~45 min de relecture bornée).

**Garde de lecture.** Toutes les références « l. NNN » dans ce mémo
renvoient à `elliptic_prefix.py` au pin `37a9b72` (sauf mention contraire
explicite vers `.paper.txt`). Confrontation littérale (`grep` / `Read`),
pas reformulation.

## 1. En-tête et garantie de pureté

Le fichier s'ouvre (l. 1–7) par une auto-déclaration d'**indépendance
vis-à-vis des deux branches de recherche** (« *No imports from either
research branch* ») et d'**arithmétique entière exacte Python**. Cette
garantie est **vérifiable** : `grep -n "^import\|^from" elliptic_prefix.py`
ne rend que `from math import isqrt` (l. 8). Aucun import depuis
`point_count`, `pilot`, `upstream/*`, ni aucune dépendance externe
(`sympy`, `sage`, etc.). **C'est l'ingrédient de base de l'audit
« pas d'ingrédients cachés »** porté par le gate
`check_subprocess_encoding` (cf. #19475, [Lean wsl() helper]).

**Garde d'arithmétique entière.** Toutes les opérations `add`, `sub`,
`mul`, `div` sur `Quadratic` (l. 25–44) portent un modulo explicite
`% self.p` ou `% p` ; la division est l'inverse modulaire `pow(norm,-1,p)`
(l. 41), avec un *zero divisor* géré par `SplitRoot` (cf. §2). Aucune
conversion flottante (`float`, `decimal`) — c'est ce qui rend les
résultats *bit-exact* modulo p. **Implication.** La re-exécution locale
en Python 3.10+ est déterministe (le seul non-déterministe est le `rng`
optionnel passé à `cornacchia_*`, qui prend le pas sur le scan
déterministe ; voir §5).

## 2. `Quadratic` et `SplitRoot` : l'algèbre F_p[√2] / F_p×F_p

### 2.1 Structure de l'algèbre

`class Quadratic` (l. 18–44) représente l'algèbre `A = F_p[√2] / (√2² − 2)`
— qui se réduit à `F_p × F_p` si 2 est résidu quadratique modulo p, ou
reste un corps `F_{p²}` si 2 n'est pas résidu. L'**état** d'une instance
est `(p, root)`, où `root` est None (= algèbre non scindée) ou une racine
`r ∈ F_p` de `r² ≡ 2 (mod p)` (= scindée, isomorphe à `F_p × F_p`).

Les **opérations** :
- `elt(a, b=0)` (l. 21) : constructeur `(a + b√2) mod p`. Si `root` est
  défini, le résidu `b` est absorbé dans la composante (l'algèbre est
  scindée, le second slot n'a plus de sens).
- `add`, `sub`, `neg` (l. 23–32) : composante par composante.
- `mul` (l. 35–36) : `((a + b√2)(c + d√2) = (ac+2bd) + (ad+bc)√2)`.
- `div` (l. 39–43) : la norme est `N(v) = v[0]² − 2 v[1]² ≡ v × v̄` ; si
  `N(v) = 0`, deux cas — `(0,0)` → `ZeroDivisionError` ; sinon
  `v = r v̄` pour un `r` avec `r² ≡ 2` (l. 41) — c'est exactement le
  **zéro diviseur** qui force à scinder l'algèbre.

### 2.2 `SplitRoot` : signal de scission

`class SplitRoot(Exception)` (l. 14–16) porte un champ `root`. Levée par
`div` (l. 41) quand `N(v) = 0` avec `v ≠ (0,0)`. L'assertion
`root² ≡ 2 (mod p)` est **vérifiée par `_elliptic_e`** à la reprise
(l. 154, `assert root is None and err.root*err.root%p==2`), ce qui
confirme l'invariant algébrique.

**Pourquoi cette scission ?** La courbe `E : y² = x³ + 2x` a un
**2-torsion rationnel** (`y = 0` ⇒ `x ∈ {0, ±√−2}` ; en caractéristique
`p ≢ 2`, `−2` est un carré ssi `−1` et `2` sont tous deux résidus ou
non-résidus). Quand l'algorithme tombe sur un zéro diviseur dans `A`,
il faut commuter à l'algèbre **scindée** pour continuer la chaîne de
Miller. Le code le fait en relançant `_elliptic_e` avec
`root=err.root` (l. 155), qui matérialise `F_p × F_p` et **abandonne
l'interprétation en termes d'extension quadratique**.

**Garde d'unicité de scission.** `_elliptic_e` a une boucle
`while True` (l. 137) ; la première itération utilise `root=None` (non
scindée) ; en cas de `SplitRoot`, l'itération suivante utilise
`root=err.root` (scindée). La troisième itération ne devrait pas
survenir : le théorème de structure assure qu'un seul niveau de scission
suffit pour `E : y² = x³ + 2x`. **C'est l'invariant « au plus un
redémarrage »** que la garde `assert root is None` (l. 154) protège.

## 3. `Elliptic` : loi de groupe + extraction du `slope`

### 3.1 Invariants

`class Elliptic` (l. 47–72) représente `E : y² = x³ + ax + b` sur le
corps `k = Quadratic(p, root)`. Les compteurs
`calls / verticals / identities` (l. 49) tracent le **nombre
d'additions**, le **nombre d'additions verticales** (P + (−P)), et le
**nombre de fois où l'un des opérandes est O** (point à l'infini). Ce
sont les **métriques de complexité** annoncées dans Theorem 1
(manuscrit l. 50, « *an admissible query costs O(log p) field
operations* »).

### 3.2 Loi de groupe avec extraction du `slope`

`add(P, Q)` (l. 51–71) retourne **deux valeurs** : `(R, slope)` où
`R = P + Q` et `slope = λ = (y_Q − y_P) / (x_Q − x_P)` (cas général) ou
`λ = (3x_P² + a) / (2 y_P)` (cas tangent). **C'est l'extraction du
dlog(g_P,Q) à O**, c-à-d la **dérivée logarithmique** au point O qui
sert d'invariant dans la chaîne de Miller (cf. §4).

**Cas particuliers gérés** :
- `P is None or Q is None` (l. 53–55) : P + O = P (ou O + Q = Q) ;
  l'identité de groupe, `slope = k.elt(0)`.
- `P = −Q` (l. 56–58) : `x_P = x_Q` et `y_P + y_Q = 0` ; la somme est
  `O` (renvoyé `None`), `slope = k.elt(0)` (verticale). Le compteur
  `verticals` s'incrémente.
- `P = Q` tangent (l. 60–62) : `slope = (3x² + a) / (2y)`.
- `P ≠ Q` général (l. 63–64) : `slope = (y_Q − y_P) / (x_Q − x_P)`.
- `x_P = x_Q` avec `y_P ≠ −y_Q` (l. 59) : **point aberrant** —
  l'invariant d'algèbre est violé (somme impossible sur E) ; le code
  force une **scission** en invoquant `k.div(k.elt(1), k.sub(y,v))`
  *avant* de lever une assertion. C'est le **2e cas de scission** (en
  sus de §2.2).

**Garde de consistency.** `on_curve(P)` (l. 75–77) vérifie
`y² = x³ + ax + b`. Cette méthode **n'est pas appelée dans la chaîne
principale** (Miller) ; elle est réservée au test `miller_constant` (l. 79,
`assert E.on_curve(P)`). **Implication.** Une mutation accidentelle de
l'algèbre entre `add` et `on_curve` ne serait pas détectée.

## 4. `miller_constant` : la chaîne différenciée

### 4.1 Invariant et assertion

`miller_constant(E, P, M, normalize=True)` (l. 80–94) calcule
**en une passe binaire** l'invariant

```
div f_k = k(P) − (kP) − (k − 1)(O)            (manuscrit, l. ~150)
```

pour un entier `M > 0` qui annule la classe de `P` (et **non
seulement** l'ordre exact de `P`, ce qui est la généralisation
annoncée l. 81). L'invariant « identity chords have g = 1 » et «
vertical chords have g = x − x(P) » (l. 82–83) sont les deux cas qui
font sortir `g` du numérateur dans la recurrence.

**Assertions** :
- `M > 0` et `E.on_curve(P)` (l. 84) — `P` est sur la courbe.
- `M % p ≠ 0` si `normalize=True` (l. 85) — sinon le résultat serait
  trivial.
- `Q is None` en sortie (l. 91) — `M` annule bien la classe de `P`.
- `E.calls ≤ 2 M.bit_length()` (l. 92) — borne de complexité O(log M)
  = O(log p) puisque `M = O(p²)` au pire (cf. §6).

### 4.2 Algorithme

Initialisation `Q = O`, `alpha = k.elt(0)` (l. 87). Pour chaque bit `j`
de `M` du bit de poids fort au bit 0 (l. 88–93) :
1. Doubler : `Q, slope = E.add(Q, Q)` ; puis `alpha = 2 alpha + slope`
   (l. 89–90) — c'est la recurrence différenciée de Miller (manuscrit
   Section 5, pseudocode l. 420–450, formule `T := R, alpha := 0, j := 0`
   + splitting sur zéro diviseur).
2. Si le bit `j` de `M` est 1 : ajouter `P` : `Q, slope = E.add(Q, P)` ;
   puis `alpha = alpha + slope` (l. 91–92).

**Retour** : si `normalize=True`, divise `alpha` par `M` (l. 93) — c'est
ce qui « normalise » en `c_M(P) / M`, l'invariant scalaire de la Section
5 du manuscrit.

**C'est exactement le pseudocode manuscrit Section 5.** Le manuscrit
promet (l. 449–450) « *resuming at most two components preserves this
bound* », ce que la garde d'assertion `E.calls ≤ 2 M.bit_length()`
confirme opérationnellement (chaque `add` incrémente `calls` une fois ;
un SplitRoot relance avec une nouvelle algèbre, mais la nouvelle passe
ne repart pas de zéro — c'est un *redémarrage*, pas une *deuxième
passe*).

## 5. `legendre2` et `cornacchia_*` : préparation de la trace

### 5.1 `legendre2(p)` (l. 97)

Caractère quadratique de 2 modulo p : `(2/p) = 1` si `p ≡ ±1 (mod 8)`,
`−1` sinon. C'est le **discriminant** qui décide si la chaîne de
Miller utilise l'ordre de `E(F_p)` (cas `(2/p) = 1`) ou son **quadratic
twist** (cas `(2/p) = −1`). En quart de tour, on a `p ≡ 1 (mod 4)` donc
`p ≡ 1 ou 5 (mod 8)` ; les deux cas se présentent.

**Vérification.** `legendre2(97) = ?`. 97 mod 8 = 1, donc
`legendre2(97) = 1` → l'ordre de `E(F_97)` est utilisé directement.
Manuscrit l. 504 : « *At p = 97, … the exceptional traces ±1 do not
occur* ». Cohérent.

### 5.2 `cornacchia_quarter(p, rng)` (l. 100–114)

Résout `v² + w² = p` pour `p ≡ 1 (mod 4)`, en **scan déterministe** par
défaut ou **échantillonnage Las Vegas** si `rng` est fourni. Le
résultat `(r, s)` est ajusté :
- `(r, s) = (v, w)` si `v % 2 == 1`, sinon `(w, v)` (l. 109) — pour
  forcer `r` impair.
- `r = -r` si `r % 4 != 1` (l. 110) — pour satisfaire la congruence
  `r ≡ 1 (mod 4)` attendue par l'**invite de Gauss** (manuscrit
  l. 506–510, formule (37)).

**Garde d'assertions** : `v² + w² = p` (l. 108) et `r² + 27 s² = 4 p`
(équivalent après ré-ajustement, manuscrit l. 504). **Mais** la
garantie « scan déterministe en O(p) au pire » n'est **pas** affirmée
polylogarithmique — le code lui-même le dit dans l'en-tête (l. 6) et
le manuscrit l. 524–525 le mentionne aussi. C'est le **talon
d'Achille** que Corollary 4 (manuscrit l. 457–481) adresse en proposant
une alternative `Schoof` (préparation polynomiale en log p).

### 5.3 `cornacchia_third(p, rng)` (l. 117–130)

Symétrique pour `p ≡ 1 (mod 3)`, résolvant `v² + 3 w² = p`. La
transformation essaie 3 candidats `(r, t)` (l. 124) : `(2v, 2w)`,
`(v+3w, v-w)`, `(v-3w, v+w)` ; le premier avec `t % 3 == 0` gagne.
Mêmes garanties d'assertion, même absence de borne polylog.

## 6. `_elliptic_e` : la glue avec redémarrage

`_elliptic_e(p, kind, M)` (l. 133–156) est le **noyau algorithmique**
qui :
1. Construit l'algèbre `Quadratic` avec `root = None` initialement, et
   une racine `s = elt(0, 1) = √2` dans cette algèbre.
2. Selon `kind` :
   - `'quarter'` : courbe `E : y² = x³ + 2x` (j = 1728, CM par Z[i]) et
     point `P = (2 − s, 4 − 2s)` (l. 142–144) — c'est le point
     d'ordre `M = p+1−τ` ou `(p+1)² − τ²` (cf. §7) préparé par
     Cornacchia.
   - `'third'` : courbe `E : y² = x³ + 0·x + 4⁻¹` (j = 0, CM par
     Z[ω]) et point `P` symétrique (l. 145–147).
3. Lance `miller_constant(E, P, M)` (l. 149) — peut lever `SplitRoot`
   (cf. §2.2).
4. Si succès : combine `A` avec `s` selon `kind` (l. 150) :
   - `quarter` : `value = s × (1 − A)` (l. 150)
   - `third` : `value = 1 + s × A` (l. 150)
5. Assertion : `value[1] == 0` (l. 151) — la composante `√2` doit
   disparaître, c-à-d que l'invariant a bien « descendu » dans F_p
   (l'algèbre était scindée ou l'extension quadratique collapsait).
6. Si `SplitRoot` : relance avec `root = err.root` (l. 154–155),
   `restarts += 1`. L'assertion `root is None` (l. 154) interdit un
   2e redémarrage.

**C'est exactement la machinery du manuscrit Section 5** — l'algorithme
pseudocode `T := R, alpha := 0, j := 0` + splitting sur zéro diviseur
(l. 420–450) matérialisé en Python avec redémarrage d'algèbre.

## 7. `quarter` : l'application du quart de tour

`quarter(p, rng=None, trace=None)` (l. 159–174) est la **fonction
utilisateur** exposée. Documentation extraite (l. 159–163) :
- Retourne `B_n, a_n, U_p(n)` avec `n = (p-1)/4`.
- `p ≡ 1 (mod 4)`, `p ≥ 13`.
- `trace` optionnel : si fourni, court-circuite Cornacchia/Gauss
  (préparation Schoof). Aucune implémentation Schoof incluse.

**Algorithme** :
1. `n = (p-1)//4` (l. 164).
2. Si `trace` est `None` : Cornacchia → `(r, s, trials)` → `boundary =
   2r × (8^n)⁻¹ mod p` (l. 166). **Note critique** : `pow(pow(8,n,p),
   -1, p)` (l. 166) — l'inverse modulaire est correct, mais le
   `boundary` n'est pas encore signé (c'est l'étape suivante).
3. `trace = boundary si boundary % 2 == 0 sinon boundary − p` (l. 167)
   — force `trace` dans l'**intervalle de Hasse** `[-2√p, 2√p]` ET pair
   (puisque `j = 1728` ⇒ la 2-torsion est rationnelle, donc `τ` est
   pair).
4. Assertion `trace % 2 == 0` et `trace² ≤ 4p` (l. 168) — borne de
   Hasse.
5. `chi = legendre2(p)` (l. 169) — le discriminant.
6. `M = p+1−trace si chi == 1 sinon (p+1)² − trace²` (l. 170–171) —
   c'est l'**ordre de E** dans `E(F_p)` ou dans son twist, qui sert
   d'annulateur de la classe de `P` dans `miller_constant`.
7. `e, info = _elliptic_e(p, 'quarter', M)` (l. 172).
8. **Formule du quart de tour** :
   ```
   B = e × (chi − boundary) mod p           (l. 173)
   U = (4 B + 9 × 4⁻¹ × boundary) mod p    (l. 174)
   ```
   `U` est exactement la formule (36) du manuscrit
   (`U_p(n) = 4 B_n + (9/4) a_n mod p`), avec `boundary = a_n` (le
   **coefficient de bord**) et `B = B_n` (le **préfixe**).
9. Retourne un dict exhaustif : `p, L=n, B, a=boundary, U, e, trace,
   r, s, root_trials, M, bits_M, curve_calls, identity_calls,
   vertical_calls, split_restarts` (l. 175).

**Vérification numérique au manuscrit** (l. 504) : la note manuscrite
cite les valeurs à p = 97, mais l'ordre des variables (τ, s, t, B_n)
est ambigu dans la note (elle suppose une convention de signe
implicite). La review Hermes du 06/10 a confronté ces valeurs à la
sortie réelle `quarter(97)` du code pinned et a relevé une
incohérence : la prose originale affectait `boundary = 24, B = 43`,
tandis que le code rend `{'B': 33, 'a': 79, 'U': 43, 'trace': -18,
'r': 9, 's': 4, ...}` (les variables `B` et `a` sont inversées entre
la note manuscrite et la sortie).

**Reconciliation c.1152 (REPAIR) :** la note manuscrite l. 504
elle-même est ambiguë, et la confrontation dépend de la convention
de signe (`trace = ±(p+1−M)`) que la note ne fixe pas. La vérification
numérique complète **n'est pas reproductible localement** : le pin
externe `bbrhuft/Cartier-Miller-…` (cf. PR #19487 body) n'est pas
accessible publiquement (le repository est privé ou inexistant), et
la règle F (réparer, jamais contourner) demande `NTL/Sage 10.8` pour
une re-exécution que l'environnement local n'a pas. **Geste** : ce
mémo cite la formule `U_p(n) = 4 B_n + (9/4) a_n` (formule (36),
manuscrit l. 504) et confronte l'algorithme à la formule, pas les
valeurs numériques à p = 97. La confrontation numérique est une
**section à exécuter hors-mémo** quand le pin sera accessible (note
ajoutée à la liste P1+ §10).

**Note critique de relecture** : pour les mémos ultérieurs (P1
pseudocode C++ #19504, P1 point_count #19499), la note manuscrite
l. 504 doit être confrontée au code source sur la branche de pin,
pas recopiée sans vérification. La règle de ce mémo devient
**toujours citer la formule, confronter l'algorithme, ne JAMAIS
citer de valeurs numériques manuscrites sans les avoir vérifiées sur
le code pinned**.

## 8. Confrontation P0 §4 → implémentation

Récapitulatif de la P0 (cartography) confrontée à la P1 (relecture
ligne-par-ligne) :

| Composant identité (P0 §4) | Implémentation putative | Vérification P1 (littérale) |
|---|---|---|
| `H = c_{p-1} = τ mod p` (trace preparation) | `cornacchia_quarter` + ajustement signe | **OK** : l. 100–114 (Cornacchia) + l. 167 (ajustement signe) + l. 168 (assertion Hasse) |
| `χ` (caractère quadratique de `d = f(1/λ)`) | `legendre2` (l. 97) | **OK pour (2/p)** : l. 97 = `(2/p)`. **Note critique** : la P0 §4 parlait de `d = f(1/λ)`, caractère quadratique d'un discriminant ; le code n'implémente **que** (2/p), pas un caractère générique. C'est cohérent avec la restriction à `E : y² = x³ + 2x` (où `d = 2` est fixé) — pas une lacune, juste un scope. |
| `r = 1/(λ v_0)` | `pilot.py` | **N/A** : elliptic_prefix.py ne porte pas cette composante (calculé dans pilot.py). À traiter en P1.pilot. |
| `Ψ_{M_χ}(D)` (dérivée log, recurrence Miller) | `miller_constant` (l. 80–94) | **OK** : recurrence différenciée l. 88–93, assertion borne O(log M) l. 92. |
| `M_χ = p+1 − χτ` | `quarter` l. 170–171 | **OK** : `M = p+1−τ` (chi=1) ou `(p+1)² − τ²` (chi=−1). Le code utilise (p+1)² − τ² au lieu de `M_χ = p+1 − χτ` quand chi = −1 — c'est équivalent (puisque (p+1)² − τ² = (p+1+τ)(p+1−τ) = #E × #twist quand chi = −1), mais pas *isoforme*. Différence subtile. |
| Trace preparation (Schoof ou BSGS) | `point_count.py` | **N/A** : elliptic_prefix.py n'inclut pas Schoof (l. 161 le dit). Cornacchia uniquement, avec `trace` externe accepté comme raccourci. |
| Cas exceptionnel `τ = ±1` (Lemma 3) | **non localisé en P0** | **Confirmé P1** : elliptic_prefix.py ne contient aucun `tau == 1` / `tau == -1` / `exceptional` (vérifié `grep`). C'est **délégué** à Lemma 3 du manuscrit, que l'implémentation **n'aborde pas** — limitation assumée du code. |
| Quarter-point application `U_p(n) = 4 B_n + (9/4) a_n` | `quarter` l. 174 | **OK** : formule (36) du manuscrit, `U = (4B + 9/4 × boundary) mod p`. |

**Résultat de la P1 elliptic_prefix.** 5 composants vérifiés littéral,
1 reporté (P1.pilot), 1 reporté (P1.point_count), 1 limité (Lemma 3 non
implémenté). **Aucune divergence** entre l'identité manuscrite et
l'implémentation pour les 5 composants vérifiés. **Aucune régression**
par rapport à P0 (la cartographie est cohérente).

## 9. Bilan P1 elliptic_prefix

**Livré** :
- Lecture ligne-par-ligne de `elliptic_prefix.py` (8
  composants documentés).
- Confrontation littérale à 4 formules du manuscrit (l. 50, l. 420–450,
  l. 504–510 formule (36), l. 504 formule (37)).
- Vérification que `legendre2` n'est **pas** un caractère quadratique
  générique de discriminant — clarification de la P0 §4.
- Vérification que `M_χ` est calculé comme `p+1−τ` ou `(p+1)²−τ²`
  (équivalents quand chi=1, twist du produit sinon) — pas isoforme
  littéral à la P0 §4, mais mathématiquement valide.
- Confirmation que Lemma 3 (cas exceptionnel `τ = ±1`) **n'est pas
  implémenté** dans le code — limitation assumée, pas régression.

**Non livré** (par design, P1+ à venir) :
- `pilot.py` — orchestration + intégration Harvey BGS.
- `point_count.py` — Schoof + BSGS (le kernel de trace
  preparation que Corollary 4 attend).
- Confrontation pseudocode manuscrit Section 5 ↔ `miller_constant` ligne
  par ligne (fait à un niveau de classe, pas instruction-par-instruction).
- Exécution locale de `test_validation.py` (NTL/Sage 10.8 absent ;
  règle F : installer ou router vers une lane qui a).
- **Vérification numérique à p = 97** (note manuscrite l. 504) : la
  note manuscrite est ambiguë sur l'ordre des variables (τ, s, t,
  B_n) et le pin externe `bbrhuft/Cartier-Miller-…` n'est pas
  accessible publiquement. **Ce mémo cite la formule `U_p(n) = 4 B_n
  + (9/4) a_n` et confronte l'algorithme** (l. 173–174) à la
  formule, **pas les valeurs numériques à p = 97**. C'est une
  **dette de confrontation numérique** à lever dans un cycle dédié
  (accès au code source requis) — voir §10 ligne P1 pseudocode C++.

**Risque résiduel** : aucun à ce stade (P1 elliptic_prefix ne touche
pas le code, ne certifie rien). Risque de Phase suivante = la P1.pilot
pourrait révéler une ré-implémentation locale de Miller (anti-pattern
`miller_constant` dupliqué) — à mesurer en P1.pilot.

**Condition de reprise** : la P1.pilot + P1.point_count合計 ~3-4 h de
relecture bornée. **Le présent mémo P1 elliptic_prefix peut être livré
sans dépendance externe** — c'est sa raison d'être en tranche mini.

## 10. P1+ : ce qui reste, et l'organe à consulter

| Phase | Objet | Volume | Statut |
|---|---|---|---|
| **P1 elliptic_prefix** | `elliptic_prefix.py` | 45 min | **CE MÉMO** |
| **P1.pilot** | `pilot.py` — orchestration, hash, per-call math data | ~1.5 h | À faire |
| **P1.point_count** | `point_count.py` — Schoof + BSGS | ~1.5 h | À faire |
| **P1 confrontation pseudocode ↔ C++** | `upstream/recurrences_ntl.{cpp,h}` + `upstream/hypellfrob.{cpp,h,pyx}` vs manuscrit l. 420–450 | ~2-4 h | À faire |
| **P1.numeric §7** | Vérification numérique à p = 97 (note manuscrite l. 504 ambiguë) : confrontation `quarter(97)` rendu par code pinned vs valeurs manuscrites. **Nécessite accès au pin externe** (privé/inexistant) ou redéploiement local. | ~30 min | **BLOQUANT LEVÉ** c.1152 — section réécrite pour ne citer que la formule |
| **P2 Lean Mathlib** | Enquête `Mathlib.NumberTheory.EllipticCurve.*` (couverture Frobenius, Cartier) + éventuelle formalisation | 5-10 h | À faire (lane Lean) |
| **P3+ multi-cycle** | briques atomiques (modèle EPIC #17845) | multi-cycle | À faire |

**Recommandation.** P1 elliptic_prefix est livrable en PR dédiée
(maintenant, sur `feature/19452-cartier-miller-p1`). P1.pilot +
P1.point_count sur deux cycles workers successifs (3-4 h), puis
confrontation pseudocode C++ (cycle dédié). P2 Lean est sur une autre
lane (expertise Lean) — à dispatcher après P1 complète.

**Refs.** #19452 (issue distillation, mandat user Telegram 06/10 09:56
Paris) · #19487 (P0 cartography, ce mémo en est la suite) · modèle
#17845 (EPIC Karingula-Lovett Lean 4) · pin externe
`bbrhuft/Cartier-Miller-...` @ `37a9b727dfd5034af0b8aa8185246d58008b9e5c`.
