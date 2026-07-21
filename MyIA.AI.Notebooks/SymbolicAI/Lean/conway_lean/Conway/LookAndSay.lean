/-
  `Conway.LookAndSay` — La suite look-and-say de Conway
  ======================================================
  La suite look-and-say démarre avec « 1 ». Chaque terme suivant décrit le
  terme précédent en lisant à voix haute les groupes de chiffres consécutifs :
    1 → 11 → 21 → 1211 → 111221 → 312211 → 13112221 → ...

  Conway a démontré des propriétés remarquables :
  - Le rapport |a(n+1)| / |a(n)| converge vers la constante de Conway
    λ ≈ 1.303577...
  - λ est l'unique racine réelle positive d'un polynôme de degré 71
  - La suite se décompose en exactement 92 « éléments atomiques » (nommés
    d'après les éléments chimiques)

  Ce fichier formalise la génération de la suite et vérifie les premiers
  termes.

  ### i18n — convention #4980 (ratifiée 2026-07-04)

  Ce fichier est le **canonique français**. Le miroir anglais est le fichier
  frère `LookAndSay_en.lean` (`namespace Conway_en`, `open Conway`) — modèle
  sibling pair, cf `code-style.md` §Lean i18n et l'analogue `Fractran.lean` /
  `Fractran_en.lean`. Docstrings en français ici ; le corps (signatures, defs,
  `#eval!`) reste byte-identique entre les deux fichiers. Pas de bloc bilingue
  inline (option B rejetée).

  Cross-références : c.366 `Conway.lean` racine bilingue (MERGED), c.451
  `Conway/Fractran` sibling pair (MERGED), c.456 `Conway/FreeWillTheorem`
  sibling pair (MERGED), **c.457 `Conway/LookAndSay` sibling pair (ce PR)**,
  c.518 `Conway/Nim` sibling pair (à suivre).
-/

import Mathlib.Data.List.Basic

namespace Conway

/-- Décompose un entier en ses chiffres décimaux (chiffre le plus significatif en premier).
  1211 → [1, 2, 1, 1]  -/
def natToDigits (n : Nat) : List Nat :=
  if n = 0 then []
  else natToDigits (n / 10) ++ [n % 10]
  termination_by n
  decreasing_by omega

/-- Convertit une liste de chiffres (le plus significatif en premier) en un Nat.
  [1, 2, 1, 1] → 1211 -/
def digitsToNat : List Nat → Nat
  | [] => 0
  | d :: ds => d * 10 ^ ds.length + digitsToNat ds

/-- Encodage run-length d'une liste : regroupe les éléments consécutifs égaux.
  [1, 1, 2, 2, 2, 1] → [(2, 1), (3, 2), (1, 1)]
  Utilise un carburant (fuel) pour satisfaire le vérificateur de terminaison. -/
def runLengthAux : Nat → List Nat → List (Nat × Nat)
  | 0, _ => []
  | _ + 1, [] => []
  | fuel + 1, a :: as =>
    match as.span (· = a) with
    | (eqs, rest) => (eqs.length + 1, a) :: runLengthAux fuel rest

/-- Encodage run-length d'une liste (enveloppe avec carburant suffisant). -/
def runLength (l : List Nat) : List (Nat × Nat) :=
  runLengthAux (l.length + 1) l

/-- Aplatit les paires (compte, chiffre) en une liste de chiffres : [(2,1), (3,2)] → [2,1,3,2] -/
def flattenPairs : List (Nat × Nat) → List Nat
  | [] => []
  | (count, digit) :: rest =>
    natToDigits count ++ [digit] ++ flattenPairs rest

/-- Une étape de la transformation look-and-say.
  Lit les chiffres de gauche à droite, produit l'encodage run-length sous forme d'entier. -/
def lookAndSayStep (n : Nat) : Nat :=
  if n = 0 then 0
  else digitsToNat (flattenPairs (runLength (natToDigits n)))

/-- Génère le n-ième nombre de la suite look-and-say (indexé depuis 0, germe = 1) -/
def lookAndSay : Nat → Nat
  | 0 => 1
  | n + 1 => lookAndSayStep (lookAndSay n)

-- Vérifie les 6 premiers termes de la suite look-and-say
#eval! lookAndSay 0  -- 1
#eval! lookAndSay 1  -- 11
#eval! lookAndSay 2  -- 21
#eval! lookAndSay 3  -- 1211
#eval! lookAndSay 4  -- 111221
#eval! lookAndSay 5  -- 312211

end Conway