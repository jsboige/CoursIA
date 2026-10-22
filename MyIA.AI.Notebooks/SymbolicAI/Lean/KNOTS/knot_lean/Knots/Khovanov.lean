/-
  Knots.Khovanov — homologie de Khovanov du trèfle (banc #8182)
  ====================================================================

  Ce fichier construit le **complexe de Khovanov** d'un diagramme de noeud
  codé en PD, selon Bar-Natan, *On Khovanov's categorification of the Jones
  polynomial* (arXiv:math/0201043, §2-§3), et l'évalue sur le trèfle du lac
  (`Knots.Basic.trefoilDiagram`). Il s'appuie sur le bracket de Kauffman de
  `Knots.Jones` : les états, les deux lissages A/B, l'énumération des
  boucles et le signe des croisements y sont déjà définis et prouvés.

  ## Conventions (celles de Bar-Natan, alignées sur A14 de Jones)

  - Le module `V` a pour base `v₊` (degré +1) et `v₋` (degré −1) ; ici
    `v₊ = true`, `v₋ = false`.
  - Le **0-lissage** de Bar-Natan est le lissage **A** (`true` chez Jones),
    le **1-lissage** est le lissage **B** (`false`). La hauteur `r` d'un
    état est son nombre de 1-lissages, donc le nombre de `false`.
  - Au sommet `ε` de hauteur `r`, dont le lissage a `k` boucles, on attache
    `V^ε := V^{⊗k}{r}` (décalage quantique `{r}` ; `qdim V^ε = q^r
    (q + q⁻¹)^k`). Les facteurs tensoriels sont rangés dans l'ordre
    **croissant par arête minimale** de la boucle (§3 de Bar-Natan) :
    `sortedComponents`.
  - Les arêtes du cube basculent un **0 → 1** (A → B) ; le signe est
    `(−1)^{nombre de 1 avant le croisement basculé}`. L'application d'arête
    est `m` quand deux boucles fusionnent, `Δ` quand une boucle se scinde,
    l'identité sur les autres facteurs :
    `m(v₊⊗v₊) = v₊`, `m(v₊⊗v₋) = m(v₋⊗v₊) = v₋`, `m(v₋⊗v₋) = 0`,
    `Δ(v₊) = v₊⊗v₋ + v₋⊗v₊`, `Δ(v₋) = v₋⊗v₋`.
  - Le complexe final est `C(L) = L[−n₋]{n₊ − 2n₋}` ; `n₊` et `n₋` sont les
    nombres de croisements positifs et négatifs au sens de
    `Knots.Jones.crossingSign`. L'existence de ces entiers est le seul
    usage de la planarité ; le trèfle du lac a `n₊ = 3`, `n₋ = 0`.

  ## Ce que le fichier décide (noyau, `decide`)

  Sur `trefoilDiagram` :

  - dimensions des groupes de chaînes : **4, 6, 12, 8** (30 générateurs) ;
  - **`d ∘ d = 0`** aux deux étages composables ;
  - rangs des différentielles : **2, 4, 7** ;
  - dimensions de l'homologie par étage : **2, 0, 1, 1** ;
  - table graduée de l'homologie : `H^{0,1}`, `H^{0,3}`, `H^{2,5}`, `H^{3,9}`
    de dimension 1, tout le reste nul, soit `q + q³ + q⁵t² + q⁹t³` — la
    table publiée par Bar-Natan §4.1 pour son trèfle de démonstration ;
  - caractéristique d'Euler graduée en `q = −1` : **χ|_{q=−1} = −2**.

  ## Divergences consignées par rapport au pré-enregistrement (#12208)

  - Le pré-enregistrement annonçait « 27 générateurs, C¹ de dimension 3 » ;
    le calcul donne **30 générateurs**, de dimensions 4/6/12/8 par étage
    (le « 3 » confondait le rang du morceau gradué de degré 0 avec la
    dimension du module).
  - Le pré-enregistrement annonçait « même code PD que Bar-Natan » ;
    `trefoilDiagram` est en réalité `[⟨1,4,2,5⟩, ⟨3,6,4,1⟩, ⟨5,2,6,3⟩]`,
    là où le code littéral de la démonstration de Bar-Natan est
    `X[1,5,2,4], X[5,3,6,2], X[3,1,4,6]` — les deux codes se déduisent l'un
    de l'autre par échange `e2 ↔ e4` croisement par croisement (le miroir
    au sens de `mirrorCrossing`). Le banc est construit sur le diagramme du
    lac, et son homologie graduée coïncide avec la table publiée : la
    divergence de code n'en est pas une pour l'invariant.
  - Le discriminant scellé portait sur χ|_{q=−1} (le carnet KNOTS-02
    affichait −8) ; le banc tranche à **−2**, valeur compatible avec la
    table de Bar-Natan (`q + q³ + q⁵ − q⁹` en `t = −1` vaut −2).

  Référence : D. Bar-Natan, arXiv:math/0201043 (copie archivée au gisement
  bibliographique partagé, hors dépôt). Issue #8182 ; pré-enregistrement
  scellé #12208.
-/

import Knots.Jones

/-- Accès indexé avec valeur par défaut. Le noyau de cette version de Lean ne
fournit pas `List.get!` ; ce shim le rétablit sur `List.getD`, qui est présent,
de sorte que les définitions restent réductibles par `decide`. -/
def List.get! {α : Type} [Inhabited α] (l : List α) (i : Nat) : α := l.getD i default

namespace Knots

/-! ## Le module `V` et ses applications (TQFT à 1+1 dimensions, §3.2)

`true` représente `v₊` (degré +1), `false` représente `v₋` (degré −1). -/

/-- `m : V ⊗ V → V`, multiplication de la Frobenius : `v₊⊗v₊ ↦ v₊`,
`v₊⊗v₋ ↦ v₋`, `v₋⊗v₊ ↦ v₋`, `v₋⊗v₋ ↦ 0`. -/
def khMulGen (a b : Bool) : List (ℤ × Bool) :=
  if a && b then [(1, true)]
  else if a || b then [(1, false)]
  else []

/-- `Δ : V → V ⊗ V`, comultiplication : `v₊ ↦ v₊⊗v₋ + v₋⊗v₊`,
`v₋ ↦ v₋⊗v₋`. -/
def khComulGen (a : Bool) : List (ℤ × (Bool × Bool)) :=
  if a then [(1, (true, false)), (1, (false, true))]
  else [(1, (false, false))]

/-- Signe de l'arête basculant le croisement `i` de l'état `v` :
`(−1)^{nombre de 1-lissages avant i}`. -/
def khEdgeSign (v : List Bool) (i : Nat) : ℤ :=
  if (v.take i).count false % 2 == 0 then 1 else -1

/-! ## Ordre canonique des boucles

Bar-Natan étiquette chaque boucle par son arête minimale et range les
facteurs tensoriels par ordre croissant. `connectedComponents` de
`Knots.Jones` rend une partition dont l'ordre n'est pas canonique ; on
trie chaque composante puis la liste par arête minimale. -/

/-- Insertion triée d'un entier naturel. -/
def insertNat (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insertNat x ys

/-- Tri par insertion d'une liste d'entiers naturels. -/
def sortNats : List Nat → List Nat
  | [] => []
  | x :: xs => insertNat x (sortNats xs)

/-- Insertion triée d'une composante (comparaison par arête minimale). -/
def insertComp (c : List Nat) : List (List Nat) → List (List Nat)
  | [] => [c]
  | d :: ds => if c.head! ≤ d.head! then c :: d :: ds else d :: insertComp c ds

/-- Tri des composantes par arête minimale. -/
def sortComps : List (List Nat) → List (List Nat)
  | [] => []
  | c :: cs => insertComp c (sortComps cs)

/-- Composantes connexes de l'état `v`, chacune triée, la liste ordonnée
par arête minimale : l'ordre canonique des facteurs tensoriels. -/
def sortedComponents (d : KnotDiagram) (v : List Bool) : List (List Nat) :=
  sortComps ((connectedComponents (stateConnections d v)).map sortNats)

/-! ## L'application d'arête

Pour une arête basculant le croisement `i` de l'état `v` (de `v[i] = true`
vers `false`), on calcule les boucles avant et après, on lit quelles
anciennes boucles nourrissent quelles nouvelles, et on applique `m` (une
fusion : deux anciennes boucles dans une nouvelle) ou `Δ` (une scission :
une ancienne boucle sur deux nouvelles), l'identité ailleurs. -/

/-- Pour chaque nouvelle boucle, les indices des anciennes boucles qui la
nourrissent (elles partagent une arête). -/
def khFeeders (old newC : List (List Nat)) : List (List Nat) :=
  newC.map (fun nc =>
    (List.range old.length).filter (fun oi => (old.get! oi).any (fun e => nc.contains e)))

/-- Termes `(coeff, nouvelles marques)` de l'arête basculant le croisement
`i` de l'état `v`, les marques `m` listant la base choisie sur chaque
boucle dans l'ordre canonique. -/
def khEdgeTerms (d : KnotDiagram) (v : List Bool) (m : List Bool) (i : Nat) :
    List (ℤ × List Bool) :=
  let v' := v.set i false
  let old := sortedComponents d v
  let newC := sortedComponents d v'
  let feed := khFeeders old newC
  if newC.length + 1 = old.length then
    -- fusion : une nouvelle boucle a deux nourricières
    match (List.range newC.length).find? (fun j => 2 ≤ (feed.get! j).length) with
    | none => []
    | some j =>
      let fs := feed.get! j
      let i1 := fs.get! 0
      let i2 := fs.get! 1
      (khMulGen (m.get! i1) (m.get! i2)).map (fun (c, b) =>
        (c, (List.range newC.length).map (fun jj =>
          if jj = j then b else m.get! (feed.get! jj).head!)))
  else if newC.length = old.length + 1 then
    -- scission : une ancienne boucle nourrit deux nouvelles
    let js := (List.range newC.length).filter (fun j => (feed.get! j).length = 1)
    match js.find? (fun j => 2 ≤ (js.filter (fun j2 => feed.get! j2 = feed.get! j)).length) with
    | none => []
    | some j =>
      let oStar := (feed.get! j).head!
      let pair := js.filter (fun j2 => feed.get! j2 = [oStar])
      let j1 := pair.get! 0
      let j2 := pair.get! 1
      (khComulGen (m.get! oStar)).map (fun (c, f) =>
        (c, (List.range newC.length).map (fun jj =>
          if jj = j1 then f.1 else if jj = j2 then f.2
          else m.get! (feed.get! jj).head!)))
  else []

/-! ## Groupes de chaînes et différentielle -/

/-- Générateurs du complexe au-dessus d'un état : un choix de base par
boucle, dans l'ordre canonique. -/
def khGen (d : KnotDiagram) (v : List Bool) : List (List Bool × List Bool) :=
  (allBoolVectors (stateLoops d v)).map (fun m => (v, m))

/-- Générateurs du groupe de chaînes `C^r` : tous les états de hauteur `r`
(nombre de 1-lissages, donc de `false`) avec toutes leurs bases. -/
def khChainGens (d : KnotDiagram) (r : Nat) : List (List Bool × List Bool) :=
  ((allBoolVectors d.crossings.length).filter (fun v => v.count false = r)).flatMap (khGen d)

/-- Coefficient d'une matrice de différentielle : entrée reliant le
générateur source au générateur cible. -/
def khDiffEntry (d : KnotDiagram) (tgt src : List Bool × List Bool) : ℤ :=
  let v := src.1
  let m := src.2
  let v' := tgt.1
  let m' := tgt.2
  ((List.range v.length).filter (fun i => v.get! i == true && v.set i false == v')).foldl
    (fun acc i =>
      acc + khEdgeSign v i *
        ((khEdgeTerms d v m i).foldl (fun a t => if t.2 = m' then a + t.1 else a) 0)) 0

/-- Matrice de la différentielle `d^r : C^r → C^{r+1}` (lignes = cibles,
colonnes = sources). -/
def khDiff (d : KnotDiagram) (r : Nat) : List (List ℤ) :=
  (khChainGens d (r + 1)).map (fun t => (khChainGens d r).map (fun s => khDiffEntry d t s))

/-- Produit matriciel sur `ℤ` (listes de lignes). -/
def matMul (A B : List (List ℤ)) : List (List ℤ) :=
  let w := (B.headD []).length
  A.map (fun row => (List.range w).map (fun j =>
    (List.range B.length).foldl (fun acc t => acc + row.get! t * (B.get! t).get! j) 0))

/-- Annulation de la colonne `c` de la ligne `r` par la ligne pivot `p`,
par opérations de lignes entières : `r' = p[c]·r − r[c]·p`. -/
def rowCancel (p r : List ℤ) (c : Nat) : List ℤ :=
  (List.range p.length).map (fun j => p.get! c * r.get! j - r.get! c * p.get! j)

/-- Rang par élimination entière (pivot trouvé colonne par colonne, lignes
restantes annulées). Le rang sur `ℚ` d'une matrice entière est inchangé par
ces opérations ; le carburant décroît à chaque pivot. -/
def matRankAux : Nat → List (List ℤ) → Nat
  | 0, _ => 0
  | fuel + 1, rows =>
    match rows.find? (fun r => r.any (fun x => x ≠ 0)) with
    | none => 0
    | some p =>
      let c := ((List.range p.length).find? (fun j => p.get! j ≠ 0)).getD 0
      let rest := (rows.erase p).map (fun r => rowCancel p r c)
      1 + matRankAux fuel rest

/-- Rang d'une matrice entière sur `ℚ`. -/
def matRank (M : List (List ℤ)) : Nat :=
  matRankAux (M.length * ((M.headD []).length) + 1) M

/-- Dimension de l'homologie à l'étage `r` : `dim C^r − rang d^{r−1} −
rang d^r`. -/
def homDim (d : KnotDiagram) (r : Nat) : Nat :=
  (khChainGens d r).length
    - (if r = 0 then 0 else matRank (khDiff d (r - 1)))
    - matRank (khDiff d r)

/-! ## Graduation quantique et caractéristique d'Euler -/

/-- Nombre de croisements positifs (au sens de `crossingSign`). -/
def nPlus (d : KnotDiagram) : Nat :=
  (d.crossings.filter (fun c => crossingSign d.numEdges c = 1)).length

/-- Nombre de croisements négatifs. -/
def nMinus (d : KnotDiagram) : Nat :=
  (d.crossings.filter (fun c => crossingSign d.numEdges c = -1)).length

/-- Degré quantique d'un générateur : `(#v₊ − #v₋) + r + (n₊ − 2n₋)`, où
`r` est la hauteur de l'état (décalage `{r}` du sommet). La
différentielle le préserve. -/
def qDeg (d : KnotDiagram) (g : List Bool × List Bool) : ℤ :=
  ((g.2.count true : ℤ) - (g.2.count false : ℤ)) + (g.1.count false : ℤ)
    + (nPlus d : ℤ) - 2 * (nMinus d : ℤ)

/-- Insertion triée d'un entier relatif. -/
def insertInt (x : ℤ) : List ℤ → List ℤ
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insertInt x ys

/-- Tri par insertion d'une liste d'entiers relatifs. -/
def sortInts : List ℤ → List ℤ
  | [] => []
  | x :: xs => insertInt x (sortInts xs)

/-- Dimensions graduées de `C^r` : liste `(j, dim)` triée par degré. -/
def gradedDim (d : KnotDiagram) (r : Nat) : List (ℤ × Nat) :=
  let gs := khChainGens d r
  (sortInts ((gs.map (qDeg d)).eraseDups)).map (fun j =>
    (j, gs.countP (fun g => qDeg d g = j)))

/-- Caractéristique d'Euler graduée évaluée en `q = −1` :
`Σ_{r,g} (−1)^{r + deg(g)}`. -/
def chiAtMinusOne (d : KnotDiagram) : ℤ :=
  (List.range (d.crossings.length + 1)).foldl (fun acc r =>
    acc + (khChainGens d r).foldl (fun a g =>
      a + (if ((r : ℤ) + qDeg d g) % 2 = 0 then 1 else -1)) 0) 0

/-- Générateurs de `C^{r}` au degré quantique `j`. -/
def khChainGensAt (d : KnotDiagram) (r : Nat) (j : ℤ) : List (List Bool × List Bool) :=
  (khChainGens d r).filter (fun g => qDeg d g = j)

/-- Dimension graduée de l'homologie : `dim C^{r,j} − rang d^{r−1}|_j −
rang d^r|_j` (la différentielle préserve `qDeg`, donc le bloc de degré `j`
est un sous-complexe). -/
def homGradedDim (d : KnotDiagram) (r : Nat) (j : ℤ) : Nat :=
  let srcs := khChainGensAt d r j
  let bIn := if r = 0 then 0 else
    matRank ((srcs).map (fun t => (khChainGensAt d (r - 1) j).map (fun s => khDiffEntry d t s)))
  let bOut :=
    matRank (((khChainGensAt d (r + 1) j)).map (fun t => srcs.map (fun s => khDiffEntry d t s)))
  srcs.length - bIn - bOut

/-! ## Évaluations sur le trèfle (décidées par le noyau)

Valeurs épinglées : ce sont les nombres que le calcul du noyau doit rendre
et que la PR cite. Toute régression de convention les casse. -/

/-- Le trèfle du lac a trois croisements positifs. -/
theorem nPlus_trefoil : nPlus trefoilDiagram = 3 := by decide

/-- … et aucun croisement négatif. -/
theorem nMinus_trefoil : nMinus trefoilDiagram = 0 := by decide

/-- Boucles de l'état tout-A (0-lissages) : 2. -/
theorem loops_allA_trefoil : stateLoops trefoilDiagram [true, true, true] = 2 := by decide

/-- Boucles de l'état tout-B (1-lissages) : 3. -/
theorem loops_allB_trefoil : stateLoops trefoilDiagram [false, false, false] = 3 := by decide

/-- Boucles des trois états à un 1-lissage : 1 partout. -/
theorem loops_r1_trefoil :
    stateLoops trefoilDiagram [true, true, false] = 1 ∧
    stateLoops trefoilDiagram [true, false, true] = 1 ∧
    stateLoops trefoilDiagram [false, true, true] = 1 := by decide

/-- Boucles des trois états à deux 1-lissages : 2 partout. -/
theorem loops_r2_trefoil :
    stateLoops trefoilDiagram [true, false, false] = 2 ∧
    stateLoops trefoilDiagram [false, true, false] = 2 ∧
    stateLoops trefoilDiagram [false, false, true] = 2 := by decide

/-- Dimensions des groupes de chaînes : 4, 6, 12, 8. -/
theorem dim_chain_trefoil :
    (khChainGens trefoilDiagram 0).length = 4 ∧
    (khChainGens trefoilDiagram 1).length = 6 ∧
    (khChainGens trefoilDiagram 2).length = 12 ∧
    (khChainGens trefoilDiagram 3).length = 8 := by decide

/-- `d¹ ∘ d⁰ = 0`. -/
theorem khovanov_d0_square_zero :
    (matMul (khDiff trefoilDiagram 1) (khDiff trefoilDiagram 0)).all
      (fun row => row.all (fun x => x == 0)) = true := by decide

/-- `d² ∘ d¹ = 0`. -/
theorem khovanov_d1_square_zero :
    (matMul (khDiff trefoilDiagram 2) (khDiff trefoilDiagram 1)).all
      (fun row => row.all (fun x => x == 0)) = true := by decide

/-- Rangs des différentielles : 2, 4, 7. -/
theorem ranks_trefoil :
    matRank (khDiff trefoilDiagram 0) = 2 ∧
    matRank (khDiff trefoilDiagram 1) = 4 ∧
    matRank (khDiff trefoilDiagram 2) = 7 := by decide

/-- Dimensions de l'homologie par étage : 2, 0, 1, 1 (total 4). -/
theorem homDim_trefoil :
    homDim trefoilDiagram 0 = 2 ∧
    homDim trefoilDiagram 1 = 0 ∧
    homDim trefoilDiagram 2 = 1 ∧
    homDim trefoilDiagram 3 = 1 := by decide

/-- Dimensions graduées des groupes de chaînes. -/
theorem gradedDim_trefoil :
    gradedDim trefoilDiagram 0 = [(1, 1), (3, 2), (5, 1)] ∧
    gradedDim trefoilDiagram 1 = [(3, 3), (5, 3)] ∧
    gradedDim trefoilDiagram 2 = [(3, 3), (5, 6), (7, 3)] ∧
    gradedDim trefoilDiagram 3 = [(3, 1), (5, 3), (7, 3), (9, 1)] := by decide

/-- La table graduée de l'homologie : `q + q³ + q⁵t² + q⁹t³`, identique à
la table publiée par Bar-Natan §4.1 pour son trèfle de démonstration. -/
theorem homGradedDim_trefoil :
    homGradedDim trefoilDiagram 0 1 = 1 ∧
    homGradedDim trefoilDiagram 0 3 = 1 ∧
    homGradedDim trefoilDiagram 1 3 = 0 ∧
    homGradedDim trefoilDiagram 1 5 = 0 ∧
    homGradedDim trefoilDiagram 2 5 = 1 ∧
    homGradedDim trefoilDiagram 3 9 = 1 := by decide

/-- Caractéristique d'Euler graduée en `q = −1` : −2 (le discriminant du
pré-enregistrement ; le carnet KNOTS-02 affichait −8). -/
theorem chi_trefoil : chiAtMinusOne trefoilDiagram = -2 := by decide

end Knots