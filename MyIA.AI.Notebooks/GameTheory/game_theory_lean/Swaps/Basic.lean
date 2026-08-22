/-
  Chemins de swaps sur les jeux 2×2 ordinaux — vérificateur certifié
  =================================================================

  Compagnon Lean du notebook `GameTheory-3c-Chemins-de-Swaps.ipynb`
  (grain #12222, suite de GameTheory-3b « Chambres et Murs »).

  Répartition des rôles, que le notebook documente explicitement :
  - le **générateur** (Python, dans le notebook) explore l'espace des
    576 jeux stricts par parcours en largeur (BFS, niveau par niveau)
    et **propose** un plus court chemin ;
  - le **certificat** (ce module) **garantit** qu'un chemin proposé est
    bien formé — chaque étape est l'un des six générateurs adjacents —
    et qu'il mène bien du jeu de départ au jeu d'arrivée ;
  - la **minimalité** est certifiée ici sur le cas témoin Dilemme →
    Chicken : aucun chemin de longueur inférieure à 2 ne relie les deux
    jeux (énumération décidable), donc la distance vaut exactement 2.

  Représentation (convention GameTheory-3 / GameTheory-21) : une table
  de paiements porte les rangs 1-4 des quatre cellules dans l'ordre
  (haut-gauche, haut-droit, bas-gauche, bas-droit). Un jeu est le
  couple (table Ligne, table Colonne). Un générateur échange les deux
  cellules portant deux rangs adjacents — vu des valeurs, c'est une
  relabellisation k ↔ k+1.

  Ce module est volontairement SANS Mathlib : tout est calcul fini
  décidable sur des listes littérales, clos par `rfl` et `decide`.
  Vérifié par `lake build Swaps.Basic` — aucun axiome, aucune preuve
  trouée.
-/

/-- Une table de paiements : les quatre rangs 1-4 dans l'ordre
(haut-gauche, haut-droit, bas-gauche, bas-droit). -/
def Table : Type := List Nat

/-- Un jeu 2×2 ordinale : la table de Ligne et celle de Colonne. -/
def Jeu : Type := Table × Table

-- Instances pont : la synthèse de classes ne traverse pas les `def`,
-- on les reexporte explicitement pour que `decide` s'applique aux jeux.
instance : DecidableEq Table := (inferInstance : DecidableEq (List Nat))
instance : DecidableEq Jeu := (inferInstance : DecidableEq (Table × Table))

/-- Échange les rangs `k` et `k + 1` dans une table — le générateur
élémentaire : relabellisation de deux valeurs adjacentes. -/
def swapAdj (t : Table) (k : Nat) : Table :=
  t.map (fun v => if v = k then k + 1 else if v = k + 1 then k else v)

/-- Les six générateurs : trois paires adjacentes par joueur. -/
inductive Etape where
  | R12 | R23 | R34  -- côté Ligne
  | C12 | C23 | C34  -- côté Colonne
  deriving DecidableEq, Repr

/-- La valeur de base `k` d'une étape (1, 2 ou 3). -/
def Etape.k : Etape → Nat
  | .R12 | .C12 => 1
  | .R23 | .C23 => 2
  | .R34 | .C34 => 3

/-- L'étape agit-elle sur la table de Ligne ? -/
def Etape.ligne : Etape → Bool
  | .R12 | .R23 | .R34 => true
  | .C12 | .C23 | .C34 => false

/-- Application d'une étape à un jeu. -/
def appliqueEtape (g : Jeu) (e : Etape) : Jeu :=
  if e.ligne then (swapAdj g.1 e.k, g.2) else (g.1, swapAdj g.2 e.k)

/-- Application d'un chemin (liste d'étapes) à un jeu. -/
def applique : Jeu → List Etape → Jeu
  | g, [] => g
  | g, e :: p => applique (appliqueEtape g e) p

/-! ## Les jeux témoins (encodages GameTheory-3 / GameTheory-21) -/

/-- Le Dilemme du prisonnier. -/
def dilemme : Jeu := (([3, 1, 4, 2] : Table), [3, 4, 1, 2])

/-- Chicken (Hawk-Dove). -/
def chicken : Jeu := (([3, 2, 4, 1] : Table), [3, 4, 2, 1])

/-- La chasse au cerf (Stag Hunt). -/
def cerf : Jeu := (([4, 1, 3, 2] : Table), [4, 3, 1, 2])

/-! ## Le chemin proposé par le générateur -/

/-- Le chemin proposé par le BFS du notebook : R₁₂ puis C₁₂. -/
def cheminDilemmeChicken : List Etape := [.R12, .C12]

/-! ## Certificats -/

/-- **Certificat d'arrivée** : le chemin proposé mène bien du Dilemme à
Chicken. Évalué par le noyau (`rfl`) — aucune tactique, aucun axiome. -/
theorem certificat_chemin : applique dilemme cheminDilemmeChicken = chicken := by rfl

/-- Un chemin **valide mais non minimal** : l'aller-retour R₂₃ ∘ R₂₃
s'annule, la longueur passe à 4 sans changer l'arrivée. Le certificat
d'arrivée l'accepte — seule l'analyse de minimalité le distingue du
plus court chemin. -/
theorem chemin_valide_non_minimal :
    applique dilemme [.R12, .R23, .R23, .C12] = chicken := by rfl

/-- **Bornes inférieures** : aucun chemin de longueur 0 ou 1 ne relie
le Dilemme à Chicken. Chaque cas est tranché par énumération décidable. -/
theorem aucun_chemin_court :
    ∀ p : List Etape, p.length < 2 → applique dilemme p ≠ chicken := by
  intro p hp
  match p with
  | [] => decide
  | [e] => cases e <;> decide
  | _ :: _ :: reste =>
      simp only [List.length_cons] at hp
      omega

/-- **Distance exacte** : la distance de swap entre le Dilemme et
Chicken vaut exactement 2 — un chemin de longueur 2 existe
(certificat) et aucun chemin plus court n'existe (bornes
inférieures). -/
theorem distance_dilemme_chicken :
    applique dilemme cheminDilemmeChicken = chicken ∧
    ∀ p : List Etape, p.length < 2 → applique dilemme p ≠ chicken :=
  ⟨certificat_chemin, aucun_chemin_court⟩

/-! ## Vérificateur générique -/

/-- Vérificateur générique : `p` est un certificat valide de `depart`
vers `arrivee` si le chemin mène bien de l'un à l'autre. Rien n'est
affirmé ici sur la minimalité — c'est le rôle des bornes inférieures. -/
def cheminValide (depart arrivee : Jeu) (p : List Etape) : Prop :=
  applique depart p = arrivee

/-- Deuxième témoin : la chasse au cerf est à distance 2 du Dilemme,
par l'échange des deux meilleurs rangs chez chaque joueur. -/
theorem certificat_cerf : cheminValide dilemme cerf [.R34, .C34] := by rfl
