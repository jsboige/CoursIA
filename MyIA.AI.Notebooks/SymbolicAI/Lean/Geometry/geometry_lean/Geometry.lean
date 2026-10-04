/-
  Geometry — racine du lac `geometry_lean`
  =======================================

  * Racine du lac companion de la série Geometry (`SymbolicAI/Lean/Geometry/`,
    EPIC #18601 volet B), présentée selon la convention i18n #4980 :
    `Geometry.lean` canonique FR ; les siblings `_en` suivront si une
    audience externe les justifie (l'umbrella les globbe via `.submodules`).

  * Cible : doubler chaque notebook Python de concept (01 figure vers
    équation, 02 Gröbner, 03 Wu, 03b Ritt) d'un module qui formalise ce que
    l'algorithme Python calcule. Le lac ne remplace pas sympy : il en
    formalise la sémantique.

  * Modules :
    - `Geometry.MidpointHypotenuse` — le théorème du milieu de l'hypoténuse,
      fil rouge de la série Python et première marche du pont formel
      (position 05 du programme gradué #17544).
-/

import Geometry.MidpointHypotenuse
