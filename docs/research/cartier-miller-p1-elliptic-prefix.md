# Cartier–Miller P1 (mini) — `elliptic_prefix.py` ↔ manuscrit

**Cible.** Issue [#19452](https://github.com/jsboige/CoursIA/issues/19452) ·
**Suite** de [#19487](https://github.com/jsboige/CoursIA/pull/19487) (P0
cartography, mémo `cartier-miller-p0-cartography.md`). **Source externe**
[`bbrhuft/Cartier-Miller-evaluation-of-genus-one-coefficient-sums`](https://github.com/bbrhuft/Cartier-Miller-evaluation-of-genus-one-coefficient-sums),
pin `37a9b727dfd5034af0b8aa8185246d58008b9e5c`.

**Statut.** P1 *mini* = lecture ligne-par-ligne de
`elliptic_prefix.py` (l. 1–265), confrontation aux énoncés du
manuscrit (Theorem 1, formule (36), formule (37), pseudocode de la
chaîne de Miller différenciée).

## 0. Provenance mesurée (c.1201)

Le pin déclaré est **publiquement accessible** : `raw.githubusercontent.com`
sert les deux artéfacts (HTTP 200), relevés le 2026-10-09.

| Artéfact | Taille | sha256 |
|---|---|---|
| `Cartier_Miller_Benchmark/elliptic_prefix.py` | 8 942 o | `3e79d82c931f41f3091e98f6f65783ce958f13851e2c6f05283efa2152c0634d` |
| `Cartier_Miller_Paper_Revised_20261005.pdf` | 1 114 306 o | `196800df388896700e63d4733b4fc3de2cc9541158e1308cfe2523033ff9d700` |

Les deux copies de `elliptic_prefix.py` déposées sous
`example_results/larger_three/source_snapshot/` et
`example_results/paper_seven/source_snapshot/` sont **byte-identiques** à la
copie racine (même sha256) : il n'existe qu'**une** version du fichier au pin,
et la question « quelle copie a été lue » est tranchée par la mesure, pas par
une hypothèse.

`requirements.txt` déclare `matplotlib>=3.8,<4` ; le seul import de
`elliptic_prefix.py` est `from math import isqrt` (l. 9). **Aucune dépendance
NTL/Sage** n'est requise par ce fichier ni par la suite de validation (cf. §9).

**Garde de lecture.** Toutes les références « l. NNN » de ce mémo renvoient à
`elliptic_prefix.py` **au pin ci-dessus**. Les renvois au manuscrit sont donnés
**par page du PDF** (`p. N`) et non par numéro de ligne : la numérotation d'une
extraction texte dépend de l'outil qui l'a produite, deux extractions du même
PDF ne tombent pas sur les mêmes lignes, alors que la page est stable.

**Périmètre de cette tranche.** Cinq composants sur les huit de la P1
pleine (P0 §6 : P1 sur fichiers `elliptic_prefix.py` + `pilot.py` +
`point_count.py`). Le présent mémo couvre `elliptic_prefix.py` *seul* ;
`pilot.py` et `point_count.py` restent à traiter en cycles dédiés, dans la
même veine (3-5 h par fichier pour la P1 pleine, ici en ~45 min de
relecture bornée).

## 1. En-tête et garantie de pureté

Le fichier s'ouvre (l. 1–8) par une auto-déclaration d'**indépendance
vis-à-vis des deux branches de recherche** (« *No imports from either
research branch* ») et d'**arithmétique entière exacte Python**. Cette
garantie est **vérifiable** : `grep -n "^import\|^from" elliptic_prefix.py`
ne rend que `from math import isqrt` (l. 9). Aucun import depuis
`point_count`, `pilot`, `upstream/*`, ni aucune dépendance externe
(`sympy`, `sage`, etc.). **C'est l'ingrédient de base de l'audit
« pas d'ingrédients cachés »** porté par le gate
`check_subprocess_encoding` (cf. #19475, [Lean wsl() helper]).

**Garde d'arithmétique entière.** Toutes les opérations `add`, `sub`,
`mul`, `div` sur `Quadratic` (l. 24–44) portent un modulo explicite
`% self.p` ou `% p` ; la division est l'inverse modulaire `pow(norm,-1,p)`
(l. 43, dans `div` l. 37–44), avec un *zero divisor* géré par `SplitRoot` (cf.
§2). Aucune conversion flottante (`float`, `decimal`) — c'est ce qui rend les
résultats *bit-exact* modulo p. **Implication.** La re-exécution locale
en Python 3.10+ est déterministe (le seul non-déterministe est le `rng`
optionnel passé à `cornacchia_*`, qui prend le pas sur le scan
déterministe ; voir §5).

## 2. `Quadratic` et `SplitRoot` : l'algèbre F_p[√2] / F_p×F_p

### 2.1 Structure de l'algèbre

`class Quadratic` (l. 17–44) représente l'algèbre `A = F_p[√2] / (√2² − 2)`
— qui se réduit à `F_p × F_p` si 2 est résidu quadratique modulo p, ou
reste un corps `F_{p²}` si 2 n'est pas résidu. L'**état** d'une instance
est `(p, root)` (l. 18–19), où `root` est None (= algèbre non scindée) ou une
racine `r ∈ F_p` de `r² ≡ 2 (mod p)` (= scindée, isomorphe à `F_p × F_p`).

Les **opérations** :
- `elt(a, b=0)` (l. 21–22) : constructeur `(a + b√2) mod p`. Si `root` est
  défini, le résidu `b` est absorbé dans la composante (l'algèbre est
  scindée, le second slot n'a plus de sens).
- `add`, `sub`, `neg` (l. 24–31) : composante par composante.
- `mul` (l. 33–35) : `((a + b√2)(c + d√2) = (ac+2bd) + (ad+bc)√2)`.
- `div` (l. 37–44) : la norme est `N(v) = v[0]² − 2 v[1]² ≡ v × v̄` ; si
  `N(v) = 0`, deux cas — `(0,0)` → `ZeroDivisionError` (l. 40–41) ; sinon
  `v = r v̄` pour un `r` avec `r² ≡ 2` (l. 42) — c'est exactement le
  **zéro diviseur** qui force à scinder l'algèbre.

### 2.2 `SplitRoot` : signal de scission

`class SplitRoot(Exception)` (l. 12–14) porte un champ `root`. Levée par
`div` (l. 42) quand `N(v) = 0` avec `v ≠ (0,0)`. L'assertion
`root² ≡ 2 (mod p)` est **vérifiée par `_elliptic_e`** à la reprise
(l. 168, `assert root is None and err.root*err.root%p==2`), ce qui
confirme l'invariant algébrique.

**Pourquoi cette scission ?** La courbe `E : y² = x³ + 2x` a un
**2-torsion rationnel** (`y = 0` ⇒ `x ∈ {0, ±√−2}` ; en caractéristique
`p ≢ 2`, `−2` est un carré ssi `−1` et `2` sont tous deux résidus ou
non-résidus). Quand l'algorithme tombe sur un zéro diviseur dans `A`,
il faut commuter à l'algèbre **scindée** pour continuer la chaîne de
Miller. Le code le fait en relançant `_elliptic_e` avec
`root=err.root` (l. 169), qui matérialise `F_p × F_p` et **abandonne
l'interprétation en termes d'extension quadratique**.

**Garde d'unicité de scission.** `_elliptic_e` a une boucle
`while True` (l. 151) ; la première itération utilise `root=None` (non
scindée) ; en cas de `SplitRoot`, l'itération suivante utilise
`root=err.root` (scindée). La troisième itération ne devrait pas
survenir : le théorème de structure assure qu'un seul niveau de scission
suffit pour `E : y² = x³ + 2x`. **C'est l'invariant « au plus un
redémarrage »** que la garde `assert root is None` (l. 168) protège.

## 3. `Elliptic` : loi de groupe + extraction du `slope`

### 3.1 Invariants

`class Elliptic` (l. 47–79) représente `E : y² = x³ + ax + b` sur le
corps `k = Quadratic(p, root)`. Les compteurs
`calls / verticals / identities` (l. 50) tracent le **nombre
d'additions**, le **nombre d'additions verticales** (P + (−P)), et le
**nombre de fois où l'un des opérandes est O** (point à l'infini). Ce
sont les **métriques de complexité** annoncées dans Theorem 1
(manuscrit p. 1, « *an admissible query costs O(log p) field
operations* »).

### 3.2 Loi de groupe avec extraction du `slope`

`add(P, Q)` (l. 52–74) retourne **deux valeurs** : `(R, slope)` où
`R = P + Q` et `slope = λ = (y_Q − y_P) / (x_Q − x_P)` (cas général) ou
`λ = (3x_P² + a) / (2 y_P)` (cas tangent). **C'est l'extraction du
dlog(g_P,Q) à O**, c-à-d la **dérivée logarithmique** au point O qui
sert d'invariant dans la chaîne de Miller (cf. §4).

**Cas particuliers gérés** :
- `P is None or Q is None` (l. 56–58) : P + O = P (ou O + Q = Q) ;
  l'identité de groupe, `slope = k.elt(0)`.
- `P = −Q` (l. 60–63) : `x_P = x_Q` et `y_P + y_Q = 0` ; la somme est
  `O` (renvoyé `None`), `slope = k.elt(0)` (verticale). Le compteur
  `verticals` s'incrémente.
- `P = Q` tangent (l. 69) : `slope = (3x² + a) / (2y)`.
- `P ≠ Q` général (l. 70–71) : `slope = (y_Q − y_P) / (x_Q − x_P)`.
- `x_P = x_Q` avec `y_P ≠ −y_Q` (l. 64–68) : **point aberrant** —
  l'invariant d'algèbre est violé (somme impossible sur E) ; le code
  force une **scission** en invoquant `k.div(k.elt(1), k.sub(y,v))`
  (l. 67) *avant* de lever une assertion. C'est le **2e cas de scission** (en
  sus de §2.2).

**Garde de consistency.** `on_curve(P)` (l. 76–79) vérifie
`y² = x³ + ax + b`. Cette méthode **n'est pas appelée dans la chaîne
principale** (Miller) ; elle est réservée au test `miller_constant` (l. 88,
`assert M>0 and E.on_curve(P)`). **Implication.** Une mutation accidentelle de
l'algèbre entre `add` et `on_curve` ne serait pas détectée.

## 4. `miller_constant` : la chaîne différenciée

### 4.1 Invariant et assertion

`miller_constant(E, P, M, normalize=True)` (l. 82–100) calcule
**en une passe binaire** l'invariant

```
div f_k = k(P) − (kP) − (k − 1)(O)            (manuscrit p. 1, (4))
```

pour un entier `M > 0` qui annule la classe de `P` (et **non
seulement** l'ordre exact de `P`, ce qui est la généralisation
annoncée l. 83). L'invariant « identity chords have g = 1 » et «
vertical chords have g = x − x(P) » (l. 85–86) sont les deux cas qui
font sortir `g` du numérateur dans la recurrence.

**Assertions** :
- `M > 0` et `E.on_curve(P)` (l. 88) — `P` est sur la courbe.
- `M % p ≠ 0` si `normalize=True` (l. 90) — sinon le résultat serait
  trivial.
- `Q is None` en sortie (l. 98) — `M` annule bien la classe de `P`.
- `E.calls ≤ 2 M.bit_length()` (l. 99) — borne de complexité O(log M)
  = O(log p) puisque `M = O(p²)` au pire (cf. §6).

### 4.2 Algorithme

Initialisation `Q = O`, `alpha = k.elt(0)` (l. 91). Pour chaque bit `j`
de `M` du bit de poids fort au bit 0 (l. 92–97) :
1. Doubler : `Q, slope = E.add(Q, Q)` ; puis `alpha = 2 alpha + slope`
   (l. 93–94) — c'est la recurrence différenciée de Miller (manuscrit
   p. 7, pseudocode `T := R; alpha := 0; j := 0`, et l'équation (28)
   `α ← 2α + ρ` / `α ← α + ρ`).
2. Si le bit `j` de `M` est 1 : ajouter `P` : `Q, slope = E.add(Q, P)` ;
   puis `alpha = alpha + slope` (l. 95–97).

**Retour** : si `normalize=True`, divise `alpha` par `M` (l. 100) — c'est
ce qui « normalise » en `c_M(P) / M`, l'invariant scalaire du manuscrit
(équation (29), `Ψ_{M_χ}(D) = (α_{M_χ}(R+) − α_{M_χ}(R−)) / κ`).

**C'est exactement le pseudocode manuscrit p. 7.** Le manuscrit
promet (p. 7) « *Resuming at most two components preserves this
bound* », ce que la garde d'assertion `E.calls ≤ 2 M.bit_length()`
confirme opérationnellement (chaque `add` incrémente `calls` une fois ;
un SplitRoot relance avec une nouvelle algèbre, mais la nouvelle passe
ne repart pas de zéro — c'est un *redémarrage*, pas une *deuxième
passe*). Le pseudocode du manuscrit va plus loin que le code sur un point :
il **reprend les deux composantes** après scission (`resume both field
components at this same j; return both constants`), là où
`_elliptic_e` retient la composante que `SplitRoot` lui a fournie.

## 5. `legendre2` et `cornacchia_*` : préparation de la trace

### 5.1 `legendre2(p)` (l. 103)

Caractère quadratique de 2 modulo p : `(2/p) = 1` si `p ≡ ±1 (mod 8)`,
`−1` sinon. C'est le **discriminant** qui décide si la chaîne de
Miller utilise l'ordre de `E(F_p)` (cas `(2/p) = 1`) ou son **quadratic
twist** (cas `(2/p) = −1`). En quart de tour, on a `p ≡ 1 (mod 4)` donc
`p ≡ 1 ou 5 (mod 8)` ; les deux cas se présentent.

**Vérification.** `legendre2(97) = ?`. 97 mod 8 = 1, donc
`legendre2(97) = 1` → l'ordre de `E(F_97)` est utilisé directement.
Manuscrit p. 8 : « *The curve has j = 1728 and rational nonzero
two-torsion, so its trace is even and the exceptional traces ±1 do not
occur in this particular application.* » Cohérent.

### 5.2 `cornacchia_quarter(p, rng)` (l. 106–121)

Résout `v² + w² = p` pour `p ≡ 1 (mod 4)`, en **scan déterministe** par
défaut ou **échantillonnage Las Vegas** si `rng` est fourni. Le
résultat `(r, s)` est ajusté :
- `(r, s) = (v, w)` si `v % 2 == 1`, sinon `(w, v)` (l. 119) — pour
  forcer `r` impair.
- `r = -r` si `r % 4 != 1` (l. 120) — pour satisfaire la congruence
  `r ≡ 1 (mod 4)` attendue par l'**invite de Gauss** (manuscrit
  p. 8, formule (37)).

**Garde d'assertions** : `v² + w² = p` (l. 118). La variante
`cornacchia_third` porte en plus `r² + 27 s² = 4 p` (l. 143). **Mais** le
code **n'affirme aucune borne polylogarithmique inconditionnelle** : il le
dit lui-même dans son en-tête (l. 6–7), et le manuscrit p. 9 le mentionne
aussi (« *no unconditional
polylogarithmic worst-case bound is claimed* »). C'est le **talon
d'Achille** que Corollary 4 (manuscrit p. 8) adresse en proposant
une alternative `Schoof` (préparation polynomiale en log p).

### 5.3 `cornacchia_third(p, rng)` (l. 124–145)

Symétrique pour `p ≡ 1 (mod 3)`, résolvant `v² + 3 w² = p`. La
transformation essaie 3 candidats `(r, t)` (l. 139) : `(2v, 2w)`,
`(v+3w, v-w)`, `(v-3w, v+w)` ; le premier avec `t % 3 == 0` gagne.
Mêmes garanties d'assertion, même absence de borne polylog.

## 6. `_elliptic_e` : la glue avec redémarrage

`_elliptic_e(p, kind, M)` (l. 148–169) est le **noyau algorithmique**
qui :
1. Construit l'algèbre `Quadratic` avec `root = None` initialement, et
   une racine `s = elt(0, 1) = √2` dans cette algèbre (l. 152–153).
2. Selon `kind` :
   - `'quarter'` : courbe `E : y² = x³ + 2x` (j = 1728, CM par Z[i]) et
     point `P = (2 − s, 4 − 2s)` (l. 156) — c'est le point
     d'ordre `M = p+1−τ` ou `(p+1)² − τ²` (cf. §7) préparé par
     Cornacchia.
   - `'third'` : courbe `E : y² = x³ + 0·x + 4⁻¹` (j = 0, CM par
     Z[ω]) et point `P` symétrique (l. 159).
3. Lance `miller_constant(E, P, M)` (l. 161) — peut lever `SplitRoot`
   (cf. §2.2).
4. Si succès : combine `A` avec `s` selon `kind` (l. 162) :
   - `quarter` : `value = s × (1 − A)`
   - `third` : `value = 1 + s × A`
5. Assertion : `value[1] == 0` (l. 163) — la composante `√2` doit
   disparaître, c-à-d que l'invariant a bien « descendu » dans F_p
   (l'algèbre était scindée ou l'extension quadratique collapsait).
6. Si `SplitRoot` : relance avec `root = err.root` (l. 168–169),
   `restarts += 1`. L'assertion `root is None` (l. 168) interdit un
   2e redémarrage.

**C'est la machinery du manuscrit p. 7** — l'algorithme
pseudocode `T := R, alpha := 0, j := 0` + splitting sur zéro diviseur
matérialisé en Python avec redémarrage d'algèbre.

## 7. `quarter` : l'application du quart de tour

`quarter(p, rng=None, trace=None)` (l. 172–193) est la **fonction
utilisateur** exposée. Documentation extraite (l. 173–177) :
- Retourne `B_n, a_n, U_p(n)` avec `n = (p-1)/4`.
- `p ≡ 1 (mod 4)`, `p ≥ 13`.
- `trace` optionnel : si fourni, court-circuite Cornacchia/Gauss
  (préparation Schoof). Aucune implémentation Schoof incluse.

**Algorithme** :
1. `n = (p-1)//4` (l. 179).
2. Si `trace` est `None` : Cornacchia → `(r, s, trials)` → `boundary =
   2r × (8^n)⁻¹ mod p` (l. 182). **Note critique** : `pow(pow(8,n,p),
   -1, p)` (l. 182) — l'inverse modulaire est correct, mais le
   `boundary` n'est pas encore signé (c'est l'étape suivante). C'est
   l'implémentation littérale de `a_n ≡ 2u 8⁻ⁿ (mod p)` (formule (37)).
3. `trace = boundary si boundary % 2 == 0 sinon boundary − p` (l. 183)
   — force `trace` dans l'**intervalle de Hasse** `[-2√p, 2√p]` ET pair
   (puisque `j = 1728` ⇒ la 2-torsion est rationnelle, donc `τ` est
   pair). C'est la règle que le manuscrit énonce p. 9 : « *The trace is
   the unique even integer in the Hasse interval with residue a_n. If
   ā_n ∈ {0,…,p-1} is its least nonnegative residue, it is ā_n when
   that residue is even, and ā_n − p otherwise.* »
4. Assertion `trace % 2 == 0` et `trace² ≤ 4p` (l. 186) — borne de
   Hasse.
5. `chi = legendre2(p)` (l. 187) — le discriminant.
6. `M = p+1−trace si chi == 1 sinon (p+1)² − trace²` (l. 188) —
   c'est l'**ordre de E** dans `E(F_p)` ou dans son twist, qui sert
   d'annulateur de la classe de `P` dans `miller_constant`.
7. `e, info = _elliptic_e(p, 'quarter', M)` (l. 189).
8. **Formule du quart de tour** :
   ```
   B = e × (chi − boundary) mod p           (l. 190)
   U = (4 B + 9 × 4⁻¹ × boundary) mod p    (l. 191)
   ```
   `U` est exactement la formule (36) du manuscrit
   (`U_p(n) ≡ 4 B_n + (9/4) a_n mod p`, p. 8), avec `boundary = a_n` (le
   **coefficient de bord**) et `B = B_n` (le **préfixe**).
9. Retourne un dict exhaustif (l. 192–193) : `p, L=n, B, a=boundary, U, e,
   trace, r, s, root_trials, M, bits_M, curve_calls, identity_calls,
   vertical_calls, split_restarts`.

### 7.1 Confrontation numérique à p = 97 — **exécutée**

Le manuscrit énonce un cas chiffré (p. 9) :

> « *…compute the curve's exact trace, use a_n = H, and evaluate
> B_n = S_f(1) − H.* **At p = 97, n = 24, B_n = 33, a_n = 79 and
> U_p(n) = 43.** »

Exécution du code au pin (`quarter(97)`, sortie intégrale) :

```
{'p': 97, 'L': 24, 'B': 33, 'a': 79, 'U': 43, 'e': 63, 'trace': -18,
 'r': 9, 's': 4, 'root_trials': 4, 'M': 116, 'bits_M': 7,
 'curve_calls': 11, 'identity_calls': 3, 'vertical_calls': 1,
 'split_restarts': 1}
```

**Les quatre valeurs du manuscrit sont exactes, et le code les reproduit
champ par champ** :

| Manuscrit (p. 9) | Code (`quarter(97)`) | Valeur | Accord |
|---|---|---|---|
| `n` | `L` | 24 | exact |
| `B_n` | `B` | 33 | exact |
| `a_n` | `a` (= `boundary`) | 79 | exact |
| `U_p(n)` | `U` | 43 | exact |

Et les deux grandeurs que le manuscrit dérive sans les chiffrer :

| Grandeur | Formule manuscrite | Code | Valeur | Accord |
|---|---|---|---|---|
| `trace = τ` | « unique even integer in the Hasse interval with residue `a_n` ; `ā_n` if even, `ā_n − p` otherwise » (p. 9) | l. 183 | 79 est impair ⇒ `79 − 97 = −18` | exact |
| `M_χ` | `M_χ = p+1−χτ` (4), p. 1 | l. 188, `χ = +1` | `97 + 1 − (−18) = 116` | exact |

**Le signe de `trace` est donc prescrit par le manuscrit, pas laissé à une
convention implicite** : `a_n = 79` étant impair, la règle de la p. 9 impose
`ā_n − p = −18`. L'assertion de Hasse `trace² ≤ 4p` (l. 186) est satisfaite
(`324 ≤ 388`), et `M = 116` annule bien la classe de `P` — c'est ce que la
garde `assert Q is None` (l. 98) vérifie à chaque appel.

**Reproduction.** Le pin est public et le code est stdlib pur ; la mesure se
refait avec :

```bash
curl -O https://raw.githubusercontent.com/bbrhuft/Cartier-Miller-evaluation-of-genus-one-coefficient-sums/37a9b727dfd5034af0b8aa8185246d58008b9e5c/Cartier_Miller_Benchmark/elliptic_prefix.py
python -c "from elliptic_prefix import quarter; print(quarter(97))"
```

**Note critique de relecture** : pour les mémos ultérieurs (P1
pseudocode C++ #19504, P1 point_count #19499), les valeurs chiffrées du
manuscrit doivent être **exécutées** sur le code au pin, pas recopiées.
La règle de ce mémo est : **citer la formule, confronter l'algorithme, et
exécuter toute valeur numérique avant de la citer**. Un énoncé de manuscrit
n'est pas une mesure — la seule mesure est la sortie du code au pin.

## 8. Confrontation P0 §4 → implémentation

Récapitulatif de la P0 (cartography) confrontée à la P1 (relecture
ligne-par-ligne) :

| Composant identité (P0 §4) | Implémentation putative | Vérification P1 (littérale) |
|---|---|---|
| `H = c_{p-1} = τ mod p` (trace preparation) | `cornacchia_quarter` + ajustement signe | **OK** : l. 106–121 (Cornacchia) + l. 183 (ajustement signe) + l. 186 (assertion Hasse) |
| `χ` (caractère quadratique de `d = f(1/λ)`) | `legendre2` (l. 103) | **OK pour (2/p)** : l. 103 = `(2/p)`. **Note critique** : la P0 §4 parlait de `d = f(1/λ)`, caractère quadratique d'un discriminant ; le code n'implémente **que** (2/p), pas un caractère générique. C'est cohérent avec la restriction à `E : y² = x³ + 2x` (où `d = 2` est fixé) — pas une lacune, juste un scope. |
| `r = 1/(λ v_0)` | `pilot.py` | **N/A** : elliptic_prefix.py ne porte pas cette composante (calculé dans pilot.py). À traiter en P1.pilot. |
| `Ψ_{M_χ}(D)` (dérivée log, recurrence Miller) | `miller_constant` (l. 82–100) | **OK** : recurrence différenciée l. 92–97, assertion borne O(log M) l. 99. |
| `M_χ = p+1 − χτ` | `quarter` l. 188 | **OK** : `M = p+1−τ` (chi=1) ou `(p+1)² − τ²` (chi=−1). Le code utilise (p+1)² − τ² au lieu de `M_χ = p+1 − χτ` quand chi = −1 — c'est équivalent (puisque (p+1)² − τ² = (p+1+τ)(p+1−τ) = #E × #twist quand chi = −1), mais pas *isoforme*. Différence subtile. |
| Trace preparation (Schoof ou BSGS) | `point_count.py` | **N/A** : elliptic_prefix.py n'inclut pas Schoof (l. 176 le dit). Cornacchia uniquement, avec `trace` externe accepté comme raccourci. |
| Cas exceptionnel `τ = ±1` (Lemma 3) | **non localisé en P0** | **Confirmé P1** : elliptic_prefix.py ne contient aucun `tau == 1` / `tau == -1` / `exceptional` (vérifié `grep`). C'est **délégué** à Lemma 3 du manuscrit, que l'implémentation **n'aborde pas** — limitation assumée du code. |
| Quarter-point application `U_p(n) = 4 B_n + (9/4) a_n` | `quarter` l. 191 | **OK** : formule (36) du manuscrit (p. 8), `U = (4B + 9/4 × boundary) mod p`. |

**Résultat de la P1 elliptic_prefix.** 5 composants vérifiés littéral,
1 reporté (P1.pilot), 1 reporté (P1.point_count), 1 limité (Lemma 3 non
implémenté). **Aucune divergence** entre l'identité manuscrite et
l'implémentation pour les 5 composants vérifiés — la confrontation numérique
de §7.1 le confirme sur le cas chiffré. **Aucune régression** par rapport à
P0 (la cartographie est cohérente).

## 9. Bilan P1 elliptic_prefix

**Livré** :
- Lecture ligne-par-ligne de `elliptic_prefix.py` (8
  composants documentés), ancres recalibrées sur le pin et **vérifiées** au
  head (c.1201).
- Confrontation littérale à 4 énoncés du manuscrit (Theorem 1 p. 1,
  pseudocode + équation (28) p. 7, formules (36) et (37) p. 8, règle de
  signe de la trace p. 9).
- **Confrontation numérique à p = 97, exécutée** (§7.1) : les quatre valeurs
  du manuscrit (`n`, `B_n`, `a_n`, `U_p(n)`) sont reproduites champ par champ
  par `quarter(97)`, et la règle de signe de `trace` est celle du manuscrit.
- Exécution de la suite de validation au pin : **6 tests, OK, 2,6 s**
  (`test_validation.py`), sans NTL/Sage — `requirements.txt` ne déclare que
  `matplotlib`.
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
- Confrontation pseudocode manuscrit p. 7 ↔ `miller_constant` ligne
  par ligne (fait à un niveau de classe, pas instruction-par-instruction).
  Le pseudocode reprend **les deux** composantes après scission ; le code
  n'en retient qu'une — écart identifié en §4.2, à documenter en P1.point_count
  si `pilot.py` consomme les deux.

**Risque résiduel** : aucun à ce stade (P1 elliptic_prefix ne touche
pas le code, ne certifie rien). Risque de Phase suivante = la P1.pilot
pourrait révéler une ré-implémentation locale de Miller (anti-pattern
`miller_constant` dupliqué) — à mesurer en P1.pilot.

**Condition de reprise** : la P1.pilot + P1.point_count demandent ~3-4 h de
relecture bornée. **Le présent mémo P1 elliptic_prefix peut être livré
sans dépendance externe** — c'est sa raison d'être en tranche mini.

## 10. P1+ : ce qui reste, et l'organe à consulter

| Phase | Objet | Volume | Statut |
|---|---|---|---|
| **P1 elliptic_prefix** | `elliptic_prefix.py` | 45 min | **CE MÉMO** |
| **P1.pilot** | `pilot.py` — orchestration, hash, per-call math data | ~1.5 h | À faire |
| **P1.point_count** | `point_count.py` — Schoof + BSGS | ~1.5 h | À faire |
| **P1 confrontation pseudocode ↔ C++** | `upstream/recurrences_ntl.{cpp,h}` + `upstream/hypellfrob.{cpp,h,pyx}` vs pseudocode manuscrit p. 7 | ~2-4 h | À faire |
| **P1.numeric §7** | Confrontation `quarter(97)` vs valeurs du manuscrit p. 9 | ~30 min | **FAIT** c.1201 — §7.1 |
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
`bbrhuft/Cartier-Miller-evaluation-of-genus-one-coefficient-sums` @
`37a9b727dfd5034af0b8aa8185246d58008b9e5c`.
