/-!
# FormalLogic — pont Tweety ↔ Lean (EPIC #15066)

Racine du lake du pont : la serie Tweety execute et compare des systemes logiques,
la bibliotheque [Formalized Formal Logic](https://github.com/FormalizedFormalLogic)
expose leurs syntaxes, semantiques et metatheoremes comme objets certifies.
Ce lake consomme FFL en `CONSUMER_PINNE` (verdict pilote #15520) — aucun module
upstream n'est vende ni adapte ici.

Module unique :
- `FormalLogic.Bridge` — pilote Tranche A (#15520) : laboratoire propositionnel,
  validite/preuve/contre-modele sur les memes formules que le notebook.
-/

import FormalLogic.Bridge
