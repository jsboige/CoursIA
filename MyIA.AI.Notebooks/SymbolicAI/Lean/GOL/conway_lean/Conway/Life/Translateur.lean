/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

## Jeu de Vie de Conway - Translateurs : familles finies et certificats d'impossibilite

Compagnon formel du carnet `GOL-08-Loi-II-Translateur-Life.ipynb` (GOL-08b) :
la Loi II du Jeu de Vie - « un pattern qui se translate de `v` en `p`
generations (un translateur) ne peut pas depasser la vitesse de la lumiere `c`
(1 cellule/generation), ni `c/2` en deplacement orthogonal » - est ici
instanciee sur des **familles finies explicitement enumerees**, comme dans le
synthetiseur Python du carnet.

La famille `family b k` est l'ensemble (liste) de tous les patterns de 1 a `k`
cellules dans la boite `b x b` (coin inferieur gauche a l'origine). Le
certificat `noTranslator b k v p = true` - prouve par `decide` - affirme
qu'**aucun** pattern de la famille n'est un translateur de vecteur `v` et de
periode `p`. Le kernel evalue litteralement chaque candidat : c'est une
preuve formelle de l'echec exhaustif, pas un test statistique.

Instances formelles (cellules ``Int x Int``, coordonnees ligne/colonne du
module `Conway.Life`, tri lexicographique) :

- `translator_witness_glider` : la famille (3, 5) - 381 patterns de 1 a 5
  cellules dans la boite 3x3 - contient un translateur (1, -1)/4 : le glider
  de `Conway.Life`, retrouve par enumeration (le kernel arrete au premier
  temoin, exactement comme le synthetiseur du carnet).
- `no_translator_two_thirds_c` : dans cette meme famille (3, 5), aucun
  pattern ne se translate de (2, 0) en 3 generations - vitesse 2/3 c,
  au-dela de la limite orthogonale c/2. Le glider lui-meme est dans la
  famille et n'echappe pas au verdict.
- `no_small_orthogonal_translator` : la famille (3, 3) - 129 patterns d'au
  plus 3 cellules - ne contient aucun translateur (0, 2)/4 ; le vaisseau
  LWSS de `Conway.Life.Spaceships` (9 cellules, hors famille par la taille)
  realise pourtant ce deplacement (`lwss_spaceship`). La frontiere de la
  famille est bien la taille, pas la regle.

Frontiere honnete par rapport au carnet Python : les instances Python
enumeraient la boite 5x5 jusqu'a 5 cellules (68 405 candidats) ; le budget
de reduction du kernel `decide` nous borne ici a la boite 3x3 (381 et 129
candidats). Les enonces formels sont strictement plus faibles que la
counterpartie Python, et le restent jusqu'a ce qu'un plafond de reduction
plus genereux soit disponible. Aucun enonce ci-dessous ne pretend couvrir
la boite 5x5.

Convention i18n (EPIC #4980) : ce fichier est le jumeau FR canonique ; le
miroir EN vit dans `Translateur_en.lean` (consumer twin, cf
`Spaceships_en.lean`). Les corps (signatures, preuves, tactiques) restent
byte-identiques entre les deux fichiers ; seules les docstrings et
commentaires different.

Ce module est integralement prouve (aucun `sorry`).
-/

import Conway.Life

namespace Conway
namespace Life

/-! ## La boite et sa famille

`boxCells b` enumere les `b * b` cellules de la boite `b x b` dans l'ordre
lexicographique - le meme ordre canonique que les grilles de `Conway.Life`.
`family b k` en prend les sous-listes de 1 a `k` cellules : chaque element
est deja trie et sans doublon (sous-liste d'une liste triee `Nodup`), donc
canonique sans passage par `sortDedup`.
-/

/-- Les cellules de la boite `b x b` (origine au coin nord-ouest), en ordre
    lexicographique. Par construction la liste est triee et `Nodup`. -/
def boxCells (b : Nat) : List (Int × Int) :=
  (List.range b).flatMap fun i => (List.range b).map fun j => ((i : Int), (j : Int))

/-- Les cellules de la boite sont dans `[0, b)` : tout point de `boxCells b` a
    ses deux coordonnees dans l'intervalle. Sens unique, celui dont
    `family_scope` a besoin ; la reciproque n'est pas enoncee. -/
theorem mem_boxCells {b : Nat} {p : Int × Int} (hp : p ∈ boxCells b) :
    0 ≤ p.1 ∧ p.1 < b ∧ 0 ≤ p.2 ∧ p.2 < b := by
  obtain ⟨x, y⟩ := p
  simp only [boxCells, List.mem_flatMap, List.mem_map] at hp
  obtain ⟨i, hi, j, hj, hxy⟩ := hp
  -- Le `do`-bloc produit par `simp` est un `List.bind` : il faut le deplier
  -- avant que `List.mem_range` ne s'applique (mesure, pas supposition).
  simp only [List.pure_def, List.bind_eq_flatMap, List.mem_flatMap, List.mem_range,
    List.mem_cons, List.not_mem_nil, or_false] at hi hj
  obtain ⟨a, ha, rfl⟩ := hi
  obtain ⟨c, hc, rfl⟩ := hj
  simp only [Prod.mk.injEq] at hxy
  obtain ⟨hx, hy⟩ := hxy
  subst hx
  subst hy
  omega

/-- La famille des patterns de 1 a `k` cellules dans la boite `b x b` :
    toutes les sous-listes non vides de `boxCells b` de longueur au plus
    `k`. Chaque element est une `Grid` canonique (triee, `Nodup`). -/
def family (b k : Nat) : List Grid :=
  ((boxCells b).sublists).filter fun g => decide (0 < g.length ∧ g.length ≤ k)

/-- Portee de la famille : tout pattern couvert vit dans la boite. C'est ce
    lemme qui rend le certificat precis - « aucun translateur **dans la
    boite `b x b` a au plus `k` cellules** », ni plus ni moins. -/
theorem family_scope {b k : Nat} {g : Grid} (hg : g ∈ family b k)
    {p : Int × Int} (hp : p ∈ g) :
    0 ≤ p.1 ∧ p.1 < b ∧ 0 ≤ p.2 ∧ p.2 < b := by
  obtain ⟨hg', -⟩ := List.mem_filter.1 hg
  exact mem_boxCells ((List.mem_sublists.1 hg').subset hp)

/-! ## Le synthetiseur et son certificat

Deux predicats booleens, decideables par le kernel, qui parcourent la
famille exactement comme le `synthetiseur` du carnet GOL-08 : `hasTranslator`
cherche un temoin (arret au premier trouve), `noTranslator` constate l'echec
exhaustif. Les deux sont des preuves quand le kernel les reduit a `true`.
-/

/-- Certificat d'impossibilite : aucun pattern de `family b k` n'est un
    vaisseau de vecteur `v` et de periode `p`. -/
def noTranslator (b k : Nat) (v : Int × Int) (p : Nat) : Bool :=
  (family b k).all fun g => !isSpaceship g p v

/-- Synthetiseur : la famille `family b k` contient un vaisseau de vecteur
    `v` et de periode `p`. -/
def hasTranslator (b k : Nat) (v : Int × Int) (p : Nat) : Bool :=
  (family b k).any fun g => isSpaceship g p v

/-! ## Instances formelles

Trois `decide`, chacun une evaluation kernel complete de la famille. Les
tailles de familles : (3, 5) = 381 patterns, (3, 3) = 129 patterns.
-/

/-- Le glider de `Conway.Life` est bien un pattern de la famille (3, 5) :
    5 cellules dans la boite 3x3. Le temoin du `decide` suivant est donc
    un element legitime de la famille enumeree. -/
theorem glider_mem_family : glider ∈ family 3 5 := by decide

set_option maxHeartbeats 1000000 in
/-- **Temoin** - la famille (3, 5) contient un translateur (1, -1)/4 :
    c'est le glider, retrouve par enumeration kernel (arret au premier
    temoin). Contrepartie formelle du cas (3, 5, 1, 1, 4) du carnet
    (dy Python vers le bas = dy Lean negatif). -/
theorem translator_witness_glider : hasTranslator 3 5 (1, -1) 4 = true := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
/-- **Impossibilite** - dans la famille (3, 5) - qui contient le glider -
    aucun pattern ne se translate de (2, 0) en 3 generations : vitesse 2/3 c,
    au-dela de la limite orthogonale c/2 de la Loi II. Contrepartie du cas
    (5, 5, 2, 0, 3) du carnet, bornee ici a la boite 3x3. -/
theorem no_translator_two_thirds_c : noTranslator 3 5 (2, 0) 3 = true := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
/-- **Frontiere de famille** - la famille (3, 3) (au plus 3 cellules) ne
    contient aucun translateur (0, 2)/4, alors que le LWSS - 9 cellules,
    hors de la famille par la seule taille - realise exactement ce
    deplacement (`Conway.Life.Spaceships.lwss_spaceship`). Contrepartie du
    contraste (5, 5, 2, 0, 4) du carnet. -/
theorem no_small_orthogonal_translator : noTranslator 3 3 (0, 2) 4 = true := by
  decide

end Life
end Conway
