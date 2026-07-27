/-
  Knots.Lidman - Le nombre de dénouement de 11n102 vaut 2
  =======================================================

  Tye Lidman (2026) a démontré que le nombre de dénouement u(11n102) = 2.
  Il était préalablement connu que u(11n102) appartient à {1, 2}.

  La preuve tient en une page mais extraordinairement profonde, utilisant :
  1. Astuce de Montesinos : revêtement ramifié double <-> chirurgie demi-entière
  2. Espaces fibrés de Seifert et leurs descriptions par plomberie
  3. Homologie de Heegaard Floer (d-invariants, HFred)
  4. Formule de Ni-Wu pour les chirurgies cosmétiques
  5. Formule du cône de Gainullin

  Référence : Lidman (2026), arXiv:2606.12431

  Epic #2874, Phase 1 (scaffolding only - sorry permanent).

  Prérequis Mathlib nécessaires (TRÈS LOINTAIN) :
  - Topologie des 3-variétés (revêtements ramifiés, espaces fibrés de Seifert)
  - Homologie de Heegaard Floer (d-invariants, HFred)
  - Chirurgie sur les nœuds (chirurgie de Dehn, entière/demi-entière)
  - Diagrammes de plomberie pour les 4-variétés
  - Algorithme de Némethi pour le calcul de HF des variétés de plomberie
-/

import Knots.Basic
import Knots.Invariant

/-
  Convention i18n (EPIC #4980, décision user 2026-07-04) : ce fichier est **FR canonique**,
  avec son miroir anglais dans le fichier sibling `Lidman_en.lean` (modèle sibling pair
  ratifié 2026-07-04, cf `code-style.md` paragraphe Lean i18n). Les énoncés de théorèmes,
  les tactiques Lean, les noms de lemmes et les références Mathlib restent en anglais
  (compatibilité Mathlib 4) ; seules les docstrings de module et ce bloc d'en-tête
  diffèrent entre les deux fichiers.
-/

namespace Knots

/-! ## 1. Le nœud 11n102

11n102 est un nœud à 11 croisements dans la table KnotInfo.
C'est un nœud de Montesinos M(-2/3, 1/3, 2/7) de déterminant 3.
-/

/-- Le nœud 11n102, défini par son PD-code issu de KnotInfo.
    Référence : KnotInfo, https://knotinfo.org (entrée 11n_102, notation PD),
    récupéré et vérifié à la main 2026-07-02 : 11 croisements, 22 labels d'arêtes,
    chaque label 1..22 apparaît exactement deux fois.
    Classification (KnotInfo) : Montesinos K(2/3;-1/3;-2/7), déterminant 3. -/
def knot_11n102_diagram : KnotDiagram where
  crossings := [
    ⟨4,  2,  5,  1⟩,   -- crossing 1
    ⟨7,  12, 8,  13⟩,  -- crossing 2
    ⟨10, 3,  11, 4⟩,   -- crossing 3
    ⟨2,  11, 3,  12⟩,  -- crossing 4
    ⟨5,  14, 6,  15⟩,  -- crossing 5
    ⟨13, 6,  14, 7⟩,   -- crossing 6
    ⟨17, 20, 18, 21⟩,  -- crossing 7
    ⟨9,  19, 10, 18⟩,  -- crossing 8
    ⟨19, 9,  20, 8⟩,   -- crossing 9
    ⟨15, 22, 16, 1⟩,   -- crossing 10
    ⟨21, 16, 22, 17⟩   -- crossing 11
  ]
  numEdges := 22
  hwell := by trivial  -- TODO Phase 2: proper well-formedness check

def knot_11n102 : Knot where
  diagram := knot_11n102_diagram


/-! ## 2. Bornes sur le nombre de dénouement

KnotInfo donne u(11n102) ∈ {1, 2}. Lidman montre que la valeur exacte est 2.
-/

/-- Le nombre de dénouement de 11n102 est au plus 2
(évident à partir d'un diagramme avec les changements de croisement appropriés). -/
theorem unknotting_11n102_upper : Knot.unknottingNumber knot_11n102 ≤ 2 := by
  exact sorry
  -- Proof: exhibit 2 crossing changes that unknot the diagram
  -- Phase 3 target (once unknottingNumber is properly defined)

/-! ## 3. Théorème de Lidman (énoncé seul)

Le théorème principal : u(11n102) = 2, prouvé par contradiction.
Supposons u(11n102) = 1. Alors, par l'astuce de Montesinos, le revêtement
ramifié double Y de 11n102 est une chirurgie en ±3/2 sur un nœud J dans S³.

Le calcul de l'homologie de Heegaard Floer de Y (un espace fibré de Seifert)
et la comparaison des d-invariants via Ni-Wu mènent à une contradiction
sur la structure de HFred(Y).
-/

/-- Théorème de Lidman : le nombre de dénouement de 11n102 est exactement 2. -/
theorem unknotting_11n102 : Knot.unknottingNumber knot_11n102 = 2 := by
  exact sorry
  -- Reference: Lidman (2026), arXiv:2606.12431
  --
  -- Proof sketch (contradiction from u = 1):
  --
  -- Step 1 (Montesinos trick):
  --   If u(11n102) = 1, then the branched double cover Y is
  --   half-integral surgery ±3/2 on some knot J in S³.
  --   Reference: Montesinos (1973), Bol. Soc. Mat. Mexicana
  --
  -- Step 2 (Seifert structure):
  --   Y = S²(1; 1/3, 1/3, 2/7) is a Seifert fibered space.
  --   The plumbing bounding Y is positive-definite.
  --   Reference: Montesinos (1973)
  --
  -- Step 3 (Heegaard Floer computation):
  --   Using Némethi's algorithm: HFred has two spinc structures
  --   with HFred = 0 and one with HFred = F₂.
  --   d-invariants: d = 1/6 (×2) and d = -1/2 (×1).
  --   Reference: Némethi (2005),Geom. Topol.
  --             Ozsváth-Szabó (2003),Geom. Topol.
  --
  -- Step 4 (Ni-Wu comparison):
  --   The mod 2 d-invariants match +3/2-surgery on the unknot,
  --   so Y = +3/2(J) and V_s(J) = H_s(J) = 0 for all s ≥ 0.
  --   Reference: Ni-Wu (2015),J. Reine Angew. Math.
  --
  -- Step 5 (Gainullin's formula):
  --   HFred(Y, s_i) ≅ A^{red}_{i,3/2} where
  --   A^{red}_{i,3/2} = ⊕_k Q_{⌊(i+3k)/2⌋}
  --   Each Q_s appears in TWO of the three A^{red}_{i,3/2}.
  --   But only ONE of the three HFred(Y, s_i) is non-zero.
  --   Contradiction: impossible for exactly one to be non-zero.
  --   Reference: Gainullin (2017),Algebr. Geom. Topol.
  --
  -- Mathlib prerequisites (ALL missing):
  --   - 3-manifolds, branched double covers
  --   - Seifert fibered spaces
  --   - Heegaard Floer homology (d-invariants, HFred)
  --   - Surgery on knots
  --   - Plumbing diagrams for 4-manifolds
  --   - Ni-Wu formula
  --   - Gainullin's mapping cone formula
  --
  -- Estimated difficulty: **decades** away from formalization.
  -- This sorry is effectively permanent.

end Knots
