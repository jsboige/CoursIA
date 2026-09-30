import MUH.Structure

/-! # Encodage d'une structure finie (Tegmark R16 Annexe A §c)

Tegmark (2007, Annexe A §c) décrit un schéma d'encodage simple pour une
structure finie : un en-tête `# of sets | # of relations`, suivi de la
*définition* de chaque ensemble (un entier donnant son cardinal), puis de la
*définition* de chaque relation sous la forme
`# of args | arg type 1 ... | output type | value array`.

Ce module :
  - expose le type `Encoding := List Nat` (Tegmark §c, format aplati),
  - fournit `encodeCardinalities` qui ne code **que** les cardinaux des
    ensembles (préambule de Tegmark §c). L'encodage complet des relations
    (arité 2+) nécessiterait `Fin.pi`, hors scope ici,
  - fournit `complexity` selon Tegmark §d : `H(s) = Σᵢ log₂(2 + kᵢ)`. -/

/-- Encodage Tegmark Annexe A §c d'une structure finie sous la forme d'une
    `List Nat`. Le format est :
    - en-tête : `#sets, #relations`
    - pour chaque ensemble Sᵢ : cardinal `sizes i` (entier ≥ 1)
    - pour chaque relation R : `#args, arg[0], ..., arg[k-1], outType, val₀, val₁, ...`
    Le tout est aplati en une liste unique. Les relations Booléennes sont
    représentées par `val ∈ {0, 1}`. -/
abbrev Encoding := List Nat

namespace Encoding

/-- Encode les cardinaux des ensembles (le préambule de Tegmark §c).
    Le format émis est : `nSets, sizes 0, sizes 1, ..., sizes (n-1)`. -/
def encodeCardinalities (s : Structure) : List Nat :=
  s.nSets :: List.ofFn s.sizes

/-- Complexité de Tegmark §d : H(s) = Σᵢ log₂(2 + kᵢ).
    La complexité est définie pour un encodage (entier par entier). On
    l'approxime par un `Nat` : `Nat.log2 (k + 2)` est le nombre de bits
    nécessaires pour représenter `k + 2` (à 1 près, floor). -/
def complexity (s : Encoding) : Nat :=
  List.foldl (fun acc k => acc + Nat.log2 (k + 2)) 0 s

end Encoding