/-
  `Conway.Fractran` — FRACTRAN, une machine universelle
  ======================================================
  FRACTRAN est sans doute le modèle de calcul universel connu le plus
  simple. Un programme FRACTRAN est une liste de fractions positives.
  Étant donné un entier N en entrée, la machine trouve la première
  fraction f telle que N*f soit un entier, remplace N par N*f, puis
  recommence. Conway a démontré que FRACTRAN est Turing-complet.

  Exemple — génération des nombres premiers (programme de Conway à
  14 fractions) :
    À partir de 2, les puissances de 2 dans la sortie sont exactement
    2^p pour chaque nombre premier p : 2^2, 2^3, 2^5, 2^7, 2^11, ...

  ### i18n — convention #4980 (ratifiée 2026-07-04)

  Ce fichier est le **canonique français**. Le miroir anglais est le fichier
  frère `Fractran_en.lean` (`namespace Conway_en`, `open Conway`) — modèle
  sibling pair, cf `code-style.md` §Lean i18n et l'analogue `Angel.lean` /
  `Angel_en.lean`. Docstrings en français ici ; le corps (signatures, defs,
  `#eval`) reste byte-identique entre les deux fichiers. Pas de bloc bilingue
  inline (option B rejetée).
-/

namespace Conway

/-- Une instruction FRACTRAN : fraction num/den stockée comme deux Nat.
  den doit être positif (garanti par construction). -/
structure Frac where
  num : Nat
  den : Nat
  h : den > 0
  deriving Repr

/-- Crée un Frac à partir de deux Nat, en prouvant den > 0 par décision -/
def frac (n d : Nat) (h : d > 0) : Frac := ⟨n, d, h⟩

/-- Vérifie si n * (num/den) est un nombre entier -/
def fracMulNat (n : Nat) (f : Frac) : Bool :=
  n * f.num % f.den == 0

/-- Une étape FRACTRAN : trouve la première fraction applicable, ou s'arrête -/
def fractranStep : List Frac → Nat → Option Nat
  | [], _ => none
  | f :: rest, n =>
    if fracMulNat n f then some (n * f.num / f.den)
    else fractranStep rest n

/-- Exécute FRACTRAN pendant k étapes (ou jusqu'à l'arrêt) -/
def fractranRun (prog : List Frac) (n : Nat) : Nat → List Nat
  | 0 => [n]
  | k + 1 =>
    match fractranStep prog n with
    | some n' => n :: fractranRun prog n' k
    | none => [n]

/-- Auxiliaire : liste de paires de Nat → liste de Frac -/
def mkFracs : List (Nat × Nat) → List Frac
  | [] => []
  | (n, d) :: rest =>
    if h : d > 0 then ⟨n, d, h⟩ :: mkFracs rest
    else mkFracs rest -- skip invalid fractions

/-- Programme FRACTRAN générateur de nombres premiers de Conway (14 fractions).
  À partir de n=2, les puissances de 2 dans la sortie sont 2^p pour chaque nombre premier p. -/
def primeProgram : List Frac := mkFracs [
  (17, 91), (78, 85), (19, 51), (23, 38), (29, 33),
  (77, 19), (95, 23), (77, 19), (1, 17), (11, 13),
  (13, 11), (15, 2), (1, 7), (55, 1)]

-- Exécute quelques étapes du générateur de nombres premiers à partir de n=2
#eval fractranRun primeProgram 2 20

end Conway
