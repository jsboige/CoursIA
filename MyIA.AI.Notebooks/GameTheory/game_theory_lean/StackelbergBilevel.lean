/-
Organe 2 de #21221 (distillation D4 de #16775) : companion formel du notebook
`GameTheory-19b-Bilevel-PPO-Python.ipynb`. Duopole de Stackelberg en quantites,
demande lineaire p = a - qL - qF (cas b = 1, comme les tests `test_stackelberg.py`
de la serie) : le suiveur repond par sa meilleure reponse (niveau bas), le leader
optimise son profit CONTRE cette reponse (niveau haut) — la structure de la eq. 1
de Dai, Wang, Ashley, Schmidhuber (ICLR 2026, arXiv:2603.15388), ici en forme
close sur Q. Le notebook 19b remplace la meilleure reponse close par un suiveur
PPO entrainable ; ce module demontre la version exacte.

Ce fichier agrege le module ; la substance vit dans `StackelbergBilevel.Basic`.
-/
import StackelbergBilevel.Basic
