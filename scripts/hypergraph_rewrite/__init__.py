"""Pli 5 Origami Wolfram (#23093) : verdict d'outil et premier jalon de mesure.

Le pli demande la reecriture d'hypergraphes, les systemes multiway et le graphe
causal emergent. Le verdict d'outil precede toute mesure : on ne mesure pas la
reductibilite d'un systeme qu'on n'a pas su faire tourner.

Ce module porte trois choses, dans cet ordre :

1. la sonde d'outil (`engine_probe`, `capabilities`), qui parcourt le module ET les
   classes publiques du moteur ;
2. le controle de coherence (`calibrate`), dont le modele est ecrit en clair
   AVANT toute execution (constante `CALIBRATION`) ;
3. la mesure (`growth`, `fit_power_law`, `fit_power_law_raw`, `occurrences`), avec
   des bandes de verdict declarees avant la mesure (constante `EXPONENT_BANDS`).
   La selection de modele compare deux R2 pris sur la MEME variable reponse, et la
   frontiere d'occurrences rendue par `occurrences` varie avec la regle : c'est une
   mesure, pas un temoin negatif.

Le moteur n'est pas une dependance dure du depot : s'il est absent, le module
le dit et rend un verdict d'outil, il n'invente pas de chiffres.
"""
