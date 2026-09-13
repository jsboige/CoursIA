/-!
# FormalLogic — pont Tweety ↔ Lean (EPIC #15066)

Racine du lake du pont : la serie Tweety execute et compare des systemes logiques,
la bibliotheque [Formalized Formal Logic](https://github.com/FormalizedFormalLogic)
expose leurs syntaxes, semantiques et metatheoremes comme objets certifies.
Ce lake consomme FFL en `CONSUMER_PINNE` (verdict pilote #15520) — aucun module
upstream n'est vende ni adapte ici.

Modules consommateurs :
- `FormalLogic.Bridge` — pilote Tranche A (#15520) : laboratoire propositionnel,
  validité/preuve/contre-modèle sur les mêmes formules que le notebook ;
- `FormalLogic.GLBridge` — pilote Tranche F (#15916) : schéma de Löb, contrôle
  négatif par contre-modèle fini, point fixe de de Jongh–Sambin et interprétation
  arithmétique sous les conditions de Hilbert–Bernays–Löb.
-/

import FormalLogic.Bridge
import FormalLogic.GLBridge
