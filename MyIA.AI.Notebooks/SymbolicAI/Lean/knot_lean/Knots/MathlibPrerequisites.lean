/-
Knots.MathlibPrerequisites — Index des prérequis Mathlib manquants
===================================================================

Ce fichier documente les prérequis Mathlib nécessaires pour résoudre chaque
sorry dans le projet knot_lean. Il sert de feuille de route pour ce qui
devrait être construit (soit dans Mathlib, soit comme dépendances externes)
pour formaliser les résultats de la théorie des noeuds.

Epic #2874, Phase 1.

Convention : organisé par tier de difficulté.
-/

/-
  Convention i18n (EPIC #4980, decision user 2026-07-04) : ce fichier est **FR canonique**,
  avec son miroir anglais dans le fichier sibling `MathlibPrerequisites_en.lean` (modèle
  sibling pair ratifié 2026-07-04, cf `code-style.md` §Lean i18n). Les énoncés de
  théorèmes, les tactiques Lean, les noms de lemmes et les références Mathlib restent
  en anglais (compat Mathlib 4) ; seules les docstrings de module et ce bloc
  d'en-tête diffèrent entre les deux fichiers.
-/

namespace Knots.MathlibPrerequisites

/-! ## Tier 1 : Accessible (cibles Phase 2, sans prerequis profonds)

Celles-ci pourraient etre prouvees avec le Mathlib actuel une fois les
definitions correctement posees.
-/

/-- #1 : Bien-fondation des PD-codes
Chaque arete apparait exactement deux fois a travers tous les croisements.
Mathlib possede : List, Finset, Fintype, denombrement
Necessaire : extraction correcte de l'index d'arete depuis PDCrossing
-/
theorem pd_wellformed_prerequisites : True := trivial

/-- #2 : Le trefoil est tricoloriable
On assigne rouge/bleu/vert cycliquement aux 3 brins.
Mathlib possede : Fin n -> TriColor, egalite decidable
Necessaire : indexation correcte des aretes, application croisement->arete
-/
theorem trefoil_tricolorable_prerequisites : True := trivial

/-- #3 : Le noeud trivial n'est pas tricoloriable
Diagramme a 0 croisement -> seulement 1 arete -> ne peut pas utiliser >= 2 couleurs.
Mathlib possede : tout le necessaire
Necessaire : indexation correcte des aretes
-/
theorem unknot_not_tricolorable_prerequisites : True := trivial

/-- #4 : La tricolorabilite est invariante sous R1, R2, R3
On verifie chaque mouvement cas par cas.
Mathlib possede : logique propositionnelle, types Fin
Necessaire : descriptions formelles de l'effet de chaque mouvement sur les aretes
-/
theorem tricolorable_invariant_prerequisites : True := trivial

/-! ## Tier 2 : Modere (cibles Phase 3-4)

Celles-ci necessitent une infrastructure qui n'existe pas encore mais
qu'il est plausible de construire.
-/

/-- #5 : Mouvements de Reidemeister (description formelle)
Il faut une description combinatoire precise de l'effet de chaque
mouvement sur les PD-codes. Possible mais fastidieux.
Reference : shua/leanknot possede une formalisation partielle.
-/
theorem reidemeister_formal_prerequisites : True := trivial

/-- #6 : Polynome d'Alexander
Via representation de Burau ou calcul de Fox.
Mathlib possede : Polynomial Z, matrices, groupes libres (partiel)
Necessaire : calcul differentiel libre de Fox, representation de Burau
Reference : Alexander (1928), Crowell & Fox (1963)
-/
theorem alexander_polynomial_prerequisites : True := trivial

/-- #7 : Polynome de Jones via le crochet de Kauffman
Le crochet de Kauffman est un modele de somme sur les etats.
Mathlib possede : Polynomial, sommes sur types finis
Necessaire : modele d'etats du crochet de Kauffman, normalisation du writhe
Reference : Jones (1985), Kauffman (1987)
-/
theorem jones_polynomial_prerequisites : True := trivial

/-! ## Tier 3 : Approfondi (Phase 5+, effectively permanent sorry)

Celles-ci requierent une infrastructure **bien** au-dela du Mathlib
actuel et representent des projets de recherche majeurs en formalisation.
-/

/-- #8 : Isotopie ambiante <-> equivalence de Reidemeister
LE theoreme fondamental de la theorie des noeuds.
Necessite : topologie PL, position generale, theoreme d'Alexander
Reference : Reidemeister (1927), Alexander (1928)
Chronologie : annees a decennies
-/
theorem reidemeister_theorem_prerequisites : True := trivial

/-- #9 : Theoreme de Piccirillo (Conway non lisse-slice)
Necessite :
  - topologie des 4-varietes (decompositions en anses, calcul de Kirby)
  - homologie de Khovanov
  - s-invariant de Rasmussen
  - lemme d'inclusion de trace
Reference : Piccirillo (2018), arXiv:1808.02923
Lean AI Leaderboard : https://lean-lang.org/eval/problems/conway_knot_not_smoothly_slice/
Chronologie : decennies
-/
theorem piccirillo_prerequisites : True := trivial

/-- #10 : Theoreme de Lidman (nombre de denouement de 11n102 = 2)
Necessite :
  - astuce de Montesinos (revetements doubles ramifies)
  - espaces fibres de Seifert
  - homologie de Heegaard Floer (d-invariants, HFred)
  - formule de Ni-Wu pour les chirurgies cosmetiques
  - formule du cone d'application de Gainullin
Reference : Lidman (2026), arXiv:2606.12431
Chronologie : decennies
-/
theorem lidman_prerequisites : True := trivial

/-- #11 : Theoreme de Freedman (Conway topologiquement slice)
Necessite :
  - chirurgie topologique en dimension 4
  - theoreme d'inclusion de disque
  - theoreme de h-cobordisme topologique
Reference : Freedman (1982), J. Differential Geom.
Lean AI Leaderboard : https://lean-lang.org/eval/problems/conway_knot_topologically_slice/
Chronologie : decennies
-/
theorem freedman_prerequisites : True := trivial

end Knots.MathlibPrerequisites
