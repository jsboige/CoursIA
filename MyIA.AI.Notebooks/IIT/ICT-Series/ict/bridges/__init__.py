"""Adaptateurs : pont entre :mod:`ict.causal_attribution` et les organes causaux natifs.

Greffe 5 tranche 2/3 (issue #13903, Epic #4588) -- **cross-engine verification**.

Organes natifs reellement presents dans le depot (inventaire first-hand c.293) :

- ``Quasi-Experimental.make_panel_did`` et ``Quasi-Experimental.iv_replay``
  dans ``Probas/DecisionTheory/Causal-Bridges/Quasi-Experimental.ipynb``
- ``PyMC-05.enumerate_scm`` et ``PyMC-05.p_y_given_m_x``
  dans ``Probas/PyMC/PyMC-05-Causal-Inference.ipynb``

Notes
-----
Les estimateurs exposes par les notebooks natifs sont du **meme genre** que
ceux de :mod:`ict.causal_attribution` : DiD est un cas de backdoor adjustment
sur Z=periode, 2SLS est l'implementation canonique de l'IV d'Angrist-Krueger,
l'enumeration SCM est l'implementation discrete du backdoor adjustment. Les
adaptateurs prennent ces estimateurs et les passent dans l'interface
analytique close-form de :mod:`ict.causal_attribution`.

Cablage des adaptateurs sur leur organe natif (issue #14051)
-------------------------------------------------------------
Cette section remplace une phrase qui affirmait, de tous les adaptateurs, que
« les adaptateurs ici ne reimplementent rien ». Elle etait fausse au moment ou
elle a ete ecrite : les deux adaptateurs redeclaraient localement les organes
natifs, faute de cible importable. L'etat reel, adaptateur par adaptateur :

- :mod:`~ict.bridges.quasi_experimental` -- **cablage canonique**. Importe
  ``make_panel_did``, ``panel_did_two_by_two`` et ``iv_replay`` depuis
  ``causal_organs``, le module qui vit a cote de ``Quasi-Experimental.ipynb``
  et que le notebook lui-meme consomme (PR #14076, #14092). Verrouille par
  ``ict/tests/test_bridges_canonical_wiring.py`` : identite d'objet,
  ``__module__``, absence de redefinition dans la source.
- :mod:`~ict.bridges.pymc_enumerate` -- **copies declarees, encore**. Detient
  toujours des reproductions byte-identiques de ``enumerate_scm`` (cellule 5)
  et ``p_y_given_m_x`` (cellule 20) de ``PyMC-05-Causal-Inference.ipynb``. La
  cible importable ``pymc_causal_organs.py`` est portee par la PR #14133 ; le
  cablage suivra son merge. Tant que ce point n'est pas ferme, la verification
  cross-engine de cet adaptateur compare ``ict.causal_attribution`` a une
  reproduction de l'organe, et non a l'organe -- un changement d'estimateur
  dans PyMC-05 la laisserait verte.

Inventaire des estimateurs exposes par organe natif (mesure c.293) :

- Quasi-Experimental : ``make_panel_did`` (DiD), ``iv_replay`` (2SLS)
- PyMC-05 : ``enumerate_scm`` (enumeration SCM), ``p_y_given_m_x`` (helper)
- Tweety-11 : ``F`` (parseur PL, pas un estimateur numerique)
- Do-Calculus-Bridge : helpers structurels, pas un estimateur

Les 3 adaptateurs de cette tranche couvrent les 3 estimateurs numeriques
reellement presents dans le depot ; ``Tweety-11`` et ``Do-Calculus-Bridge``
sont des organes structurels/symboliques et ne pretendent pas rivaliser
avec les estimateurs numeriques de :mod:`ict.causal_attribution`.
"""

from __future__ import annotations
