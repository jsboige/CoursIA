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
- `FormalLogic.FolBridge` — Tranche B (#16877) : micro-théorie FOL (socrate/platon)
  partagée avec `Tweety-02d-FOL-Lab-Lean.ipynb` — conséquences sémantiques certifiées
  et contre-modèle fini à deux éléments sur la sémantique FFL des structures ;
- `FormalLogic.GLBridge` — pilote Tranche F (#15916) : schéma de Löb, contrôle
  négatif par contre-modèle fini, point fixe de de Jongh–Sambin et interprétation
  arithmétique sous les conditions de Hilbert–Bernays–Löb.
- `FormalLogic.ModalBridge` — pilote Tranche C (#15066) : logiques modales via
  `ModalLogic` (fork compat 4.33.1) — `K` valide sur tout cadre, contre-modèles
  finis de `T`/`4`/`5` sur cadres témoins génériques, duaux diamant de `T`/`4`
  sur les cadres S4 de Fin74.
-/

import FormalLogic.Bridge
import FormalLogic.FolBridge
import FormalLogic.GLBridge
import FormalLogic.ModalBridge
