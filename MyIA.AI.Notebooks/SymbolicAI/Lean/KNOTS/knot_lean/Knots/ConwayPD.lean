/-
  Knots.ConwayPD — Les nœuds de Conway (11n34) et Kinoshita-Terasaka (11n42)
  ========================================================================

  Les deux codes PD concrets : le nœud de Conway 11n34 (découvert par Conway via
  sa notation des nœuds, 11 croisements, polynôme d'Alexander trivial) et le nœud
  de Kinoshita-Terasaka 11n42 — la paire de mutants qui partage un polynôme
  d'Alexander trivial (§4 de `Knots.Conway` pour la preuve).

  Extrait de `Knots.Conway` (tranche 2 du split #18397, tranche 1 = `Knots.Slice`
  en #18528). Epic #2874.
-/

import Knots.Basic

namespace Knots

/-! ## 2. Le nœud de Conway (11n34)

11 croisements dans la table de Rolfsen. Découvert par Conway (1970).
Polynôme d'Alexander trivial. Topologiquement slice (Freedman).
Non slice lisse (Piccirillo 2018).

Code PD du census KnotInfo (généré par spherogram 2.4.1), **corrigé** : le
code commité par #12892 n'était pas connexe — son croisement 11
`⟨21, 22, 22, 21⟩` n'utilisait que les arêtes {21, 22}, composante isolée du
reste du diagramme, et l'arête 19 apparaissait deux fois dans son propre
croisement `⟨19, 14, 20, 19⟩`. Le contrôle `wf` (étiquettes dans [1, 22],
chacune exactement deux fois) ne voit pas la connexité : le défaut passait.
Conséquence mesurée : la ligne du croisement 11 était entièrement nulle dans
le mineur désigné → déterminant 0, et l'énoncé `conway_trivial_alexander`
d'origine (`= 1`) était faux sous la normalisation désignée. Les tuples
ci-dessous sont la rotation (t₁, t₂, t₃, t₀) des tuples census, telle que le
brin passant-dessus occupe les positions (e2, e4) de la convention du présent
fichier. Cible désignée vérifiée (sonde Python fidèle à la construction,
validée sur 3₁/4₁/5₁) : mineur = −t⁶, une unité — Δ = 1 au sens classique.
-/

def conwayKnotDiagram : KnotDiagram where
  crossings := [
    ⟨1, 4, 22, 3⟩,
    ⟨7, 2, 6, 1⟩,
    ⟨3, 8, 2, 7⟩,
    ⟨4, 12, 5, 11⟩,
    ⟨12, 6, 13, 5⟩,
    ⟨16, 9, 15, 8⟩,
    ⟨9, 21, 10, 20⟩,
    ⟨17, 11, 18, 10⟩,
    ⟨13, 19, 14, 18⟩,
    ⟨19, 15, 20, 14⟩,
    ⟨22, 17, 21, 16⟩
  ]
  numEdges := 22

/-- Contrôle : le code corrigé est bien formé au sens `wf` (chaque étiquette
de [1, 22] exactement deux fois). Le code non connexe précédent passait
aussi ce contrôle — c'est le contrôle d'arcs qui distingue. -/
theorem conway_wf : conwayKnotDiagram.wf = true := by
  decide

/-- Contrôle : la partition d'arcs du code corrigé — 11 arcs couvrant les 22
arêtes, condition de non-dégénérescence du mineur d'Alexander (le code non
connexe précédent produisait un arc isolé {21, 22} absorbé par la colonne
éliminée du mineur désigné). Énoncé en §4 (`conway_arcPartition`). -/

def conwayKnot : Knot where
  diagram := conwayKnotDiagram

/-! ## 3. Le nœud de Kinoshita-Terasaka (11n42)

Également 11 croisements. Partage le polynôme d'Alexander trivial avec 11n34.
EST slice lisse (borde un disque dans B⁴).
Mutant du nœud de Conway.

Code PD census corrigé comme en §2 (le code précédent était connexe mais
portait des arêtes répétées intra-croisement aux croisements 10 et 11 —
`⟨19, 14, 20, 19⟩` et `⟨21, 12, 22, 21⟩` — donnant un mineur désigné non
unitaire de degré 7, faux pour Δ = 1). Même rotation (t₁, t₂, t₃, t₀).
Cible désignée vérifiée : mineur = t⁵, une unité.
-/

def kinoshitaTerasakaDiagram : KnotDiagram where
  crossings := [
    ⟨1, 4, 22, 3⟩,
    ⟨7, 2, 6, 1⟩,
    ⟨3, 8, 2, 7⟩,
    ⟨4, 12, 5, 11⟩,
    ⟨12, 6, 13, 5⟩,
    ⟨17, 9, 18, 8⟩,
    ⟨9, 15, 10, 14⟩,
    ⟨20, 11, 19, 10⟩,
    ⟨14, 19, 13, 18⟩,
    ⟨15, 21, 16, 20⟩,
    ⟨21, 17, 22, 16⟩
  ]
  numEdges := 22

/-- Contrôle `wf` du code KT corrigé (cf. `conway_wf`). -/
theorem kinoshitaTerasaka_wf : kinoshitaTerasakaDiagram.wf = true := by
  decide

/-- Contrôle : partition d'arcs du code KT corrigé — 11 arcs, même structure
que Conway aux croisements 1-5 (arcs partagés), divergente au-delà. Énoncé
en §4 (`kinoshitaTerasaka_arcPartition`). -/

def kinoshitaTerasakaKnot : Knot where
  diagram := kinoshitaTerasakaDiagram


end Knots
