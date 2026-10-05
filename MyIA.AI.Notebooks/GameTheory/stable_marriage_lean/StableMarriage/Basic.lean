/-
  StableMarriage.Basic -- tranche 1 (issue #19276)
  Definitions de base : preferences totales, notion de paire bloquante.
  Cf. PORT_ANALYSIS.md pour le verdict HIGH-EFFORT PORT et le plan de port
  (Preferences partial -> total, Matching Option -> bijection, option B
  GSState separe).

  Le matching cible (total bijectif sur `Fin n`) et l'etat intermediaire
  `IntermediateMatching` (avec `Option`) sont definis dans `GaleShapley.lean`.
  Ce fichier porte les concepts statiques : preferences, blocking pair.
-/
namespace StableMarriage

/-- Preference totale : pour un homme `m`, `menPref m w` est le rang de la
    femme `w` dans la liste de preferences de `m` (0 = preferee).
    La condition `< n` encode la borne (rang dans une liste de taille n). -/
abbrev TotalPref (n : Nat) : Type := Fin n → Fin n → Nat

/-- Une femme `w` est preferable par un homme `m` a une autre `w'` selon
    `menPref`. -/
def ManPrefers {n : Nat} (menPref : TotalPref n) (m w w' : Fin n) : Prop :=
  menPref m w < menPref m w'

/-- Symetrique pour les femmes. -/
def WomanPrefers {n : Nat} (womenPref : TotalPref n) (w m m' : Fin n) : Prop :=
  womenPref w m < womenPref w m'

/-- Une paire `(m, w)` est **bloquante** pour un matching donne si :
    1. `m` prefere `w` a sa partenaire courante (ou est libre),
    2. `w` prefere `m` a son partenaire courant (ou est libre).

    Le matching est dit **stable** s'il n'a aucune paire bloquante.
    C'est la definition de Gale-Shapley 1962 etablissant l'existence
    d'un matching stable pour toute instance du probleme. -/
def IsBlockingPair {n : Nat} (menPref womenPref : TotalPref n)
    (menMatches womenMatches : Fin n → Option (Fin n))
    (m w : Fin n) : Prop :=
  (menMatches m = none ∨
   ∃ w', menMatches m = some w' ∧ ManPrefers menPref m w w') ∧
  (womenMatches w = none ∨
   ∃ m', womenMatches w = some m' ∧ WomanPrefers womenPref w m m')

end StableMarriage
