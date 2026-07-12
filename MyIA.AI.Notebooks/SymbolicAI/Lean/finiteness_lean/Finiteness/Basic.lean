/-! # Dérivées symboliques de Brzozowski — démonstration pédagogique autonome

Soit une expression régulière `r` sur un alphabet `α`. La **dérivée** de `r`
par un caractère `a` (Janusz Brzozowski, *Derivatives of Regular Expressions*,
JACM 1964) est l'expression `D_a(r)` qui reconnaît exactement les mots `w` tels
que le mot `a :: w` est reconnu par `r`. Itérée sur les caractères d'un mot, la
dérivée calcule la correspondance (*matching*) **sans reculer**
(non-backtracking) : un mot `w` est reconnu par `r` si et seulement si la
dérivée de `r` par `w` est *nullable* (reconnaît le mot vide ε).

## Le théorème de finitude

Brzozowski (1964) démontre que l'ensemble des dérivées itérées d'une expression
régulière est **fini** — modulo l'équivalence ACI (Associativité, Commutativité,
Idempotence) des unions. C'est cette finitude qui garantit la **terminaison** et
la complexité **linéaire** des reconnaisseurs modernes :
  * .NET `RegexOptions.NonBacktracking` (PLDI 2023),
  * **RE#** (POPL 2025, Varatalu/Veanes/Ernits),
  * SymPy.

## La formalisation Lean constructive (ITP 2025)

La formalisation **constructive** complète en Lean 4 — on construit un ensemble
fini majorant l'espace des dérivées (modulo équivalence) — est due à **Ekaterina
Zhuchko, Hendrik Maarand, Margus Veanes, Gabriel Ebner** (*Finiteness of
Symbolic Derivatives in Lean*, ITP 2025), dépôt
[`ezhuchko/finiteness-derivatives`](https://github.com/ezhuchko/finiteness-derivatives).
Sa licence amont n'étant pas confirmée, **ce fichier ne vendore pas leur code** :
il en illustre l'intuition par des définitions et exemples **originaux**, sans
dépendance (pas de Mathlib). Le notebook
[`Lean-14-Finiteness-Derivatives.ipynb`](../../Lean-14-Finiteness-Derivatives.ipynb)
développe la présentation pédagogique et le pont vers l'epic Conway #2162. -/


/-- Une expression régulière minimale sur l'alphabet `α`.
    * `empty` : langage vide ∅
    * `eps`   : langage du mot vide {ε}
    * `char a`: singleton {a}
    * `concat r s` : concaténation r·s
    * `union r s`  : union r ∪ s
    * `star r`     : étoile de Kleene r* -/
inductive Regex (α : Type) where
  | empty : Regex α
  | eps   : Regex α
  | char  : α → Regex α
  | concat : Regex α → Regex α → Regex α
  | union  : Regex α → Regex α → Regex α
  | star   : Regex α → Regex α
  deriving Repr

open Regex

/-- `nullable r` : la regex `r` reconnaît-elle le mot vide ε ?
    (Point fixe de la reconnaissance : une dérivée nullable ⇒ le mot lu est
    accepté.) -/
def nullable {α : Type} : Regex α → Bool
  | empty => false
  | eps => true
  | char _ => false
  | concat r s => nullable r && nullable s
  | union r s => nullable r || nullable s
  | star _ => true

/-- La **dérivée de Brzozowski** `D_a(r)` : reconnaît les mots `w` tels que
    `a :: w ∈ L(r)`. Définition récursive standard ; le cas `concat` fait
    apparaître une union quand le facteur gauche est nullable — c'est cette
    union qui, modulo ACI, borne l'espace des dérivées. -/
def deriv {α : Type} [BEq α] (a : α) : Regex α → Regex α
  | empty => empty
  | eps => empty
  | char b => if a == b then eps else empty
  | concat r s => if nullable r then union (concat (deriv a r) s) (deriv a s)
                  else concat (deriv a r) s
  | union r s => union (deriv a r) (deriv a s)
  | star r => concat (deriv a r) (star r)

/-- Dérivée par un mot (liste de caractères) : pliée de gauche à droite. -/
def derivWord {α : Type} [BEq α] (w : List α) (r : Regex α) : Regex α :=
  w.foldl (fun r' c => deriv c r') r

/-- Un mot `w` est reconnu par `r` ssi sa dérivée est nullable. C'est le
    *matching* non-backtracking : on consomme chaque caractère une seule fois,
    sans retour en arrière. (`matches` est un mot réservé en Lean 4, d'où le
    nom `accepts`.) -/
def accepts {α : Type} [BEq α] (w : List α) (r : Regex α) : Bool :=
  nullable (derivWord w r)

/-! ## Exemples : la finitude en action

On observe sur des exemples concrets que l'espace des dérivées reste fini (et
souvent minuscule) — c'est précisément le théorème de Brzozowski. -/

/-- Le langage `a*` (étoile sur le caractère 'a'). -/
def aStar : Regex Char := star (char 'a')

/- `a*` est un **point fixe** de sa dérivée par 'a' : `D_a(a*) ≡ a*`.
   L'espace des dérivées est donc réduit à un singleton — d'où la reconnaissance
   en temps linéaire. -/
#eval accepts ['a', 'a', 'a', 'a'] aStar   -- "aaaa" ∈ a*  → true
#eval accepts ['a', 'b'] aStar              -- "ab"  ∉ a*  → false

/-- Le langage `ab` (le mot "ab"). Les dérivées successives par les préfixes
    forment l'ensemble fini {ab, b, ε, ∅}. -/
def abWord : Regex Char := concat (char 'a') (char 'b')

#eval accepts ['a', 'b'] abWord   -- "ab" ∈ ab → true
#eval accepts ['a'] abWord        -- "a"  ∉ ab → false
#eval accepts ['a', 'b', 'c'] abWord -- "abc" ∉ ab → false

/- Dérivée concrète : `D_a(char a) = ε` (le singleton est « consommé »). -/
example : deriv 'a' (char 'a') = eps := by
  simp [deriv]

/- Dérivée concrète : `D_b(char a) = ∅` (caractères distincts). -/
example : deriv 'b' (char 'a') = empty := by
  simp [deriv]

/-! ## Note d'homonymie (footnote pédagogique)

Le pont vers l'Epic Conway #2162 appelle une clarification : **Damian Conway**
(auteur du célèbre *sudoku en regex Perl*, Perlmonks 2002) n'est pas **John
Horton Conway** (mathématicien, créateur du *Game of Life* — le héros de notre
Epic Lean `conway_lean`). Les deux Conway « se rencontrent » dans cette série
SymbolicAI/Lean : l'un par la reconnaissance par regex, l'autre par la
formalisation du Jeu de la Vie. Clin d'œil à documenter, pas une confusion. -/
