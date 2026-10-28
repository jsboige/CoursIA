"""Pli 5 Origami Wolfram (#23093) : verdict d'outil et premier jalon de mesure.

Le pli demande la reecriture d'hypergraphes, les systemes multiway et le graphe
causal emergent. Le verdict d'outil precede toute mesure : on ne mesure pas la
reductibilite d'un systeme qu'on n'a pas su faire tourner.

Ce module porte trois choses, dans cet ordre :

1. la sonde d'outil (`engine_probe`, `capabilities`) ;
2. le controle de correction (`calibrate`), dont le modele est ecrit en clair
   AVANT toute execution (constante `CALIBRATION`) ;
3. la mesure (`growth`, `fit_power_law`, `fanout`), avec des bandes de verdict
   declarees avant la mesure (constante `EXPONENT_BANDS`).

Le moteur n'est pas une dependance dure du depot : s'il est absent, le module
le dit et rend un verdict d'outil, il n'invente pas de chiffres.
"""
