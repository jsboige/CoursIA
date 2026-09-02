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
adaptateurs ici ne **reimplementent** rien -- ils prennent les generateurs de
donnees et estimateurs des notebooks natifs et les passent dans l'interface
analytique close-form de :mod:`ict.causal_attribution`.

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
