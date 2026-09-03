"""Organes canoniques des estimateurs PyMC-05 — enumeration exacte SCM (cellules 5 et 20).

Issue #14051, seconde moitie de l'acceptance 1 : extraire les estimateurs
natifs du notebook ``PyMC-05-Causal-Inference.ipynb`` vers un module
importable, a cote du notebook, pour que la substance demeure accessible
(le notebook importe le module au lieu de definir les fonctions) et pour
que les adaptateurs cross-engine — notamment ``ict.bridges.pymc_enumerate``
(PR #13921) — aient une cible **reellement observable**, plutot que de
redeclarer localement et de verifier ICT contre une copie d'elle-meme.

Le module frere ``Probas/DecisionTheory/Causal-Bridges/causal_organs.py``
(livre par PR #14076) couvre les estimateurs Quasi-Experimental (DiD, IV).
Le present module couvre l'autre ligne de la table d'acceptance #14051 :

- ``enumerate_scm(...)`` (cellule 5) — inference exacte par enumeration sur
  un SCM discret booleen, avec conditionnement (niveau 1) et mutilation
  (niveau 2, ``do_vars``).
- ``p_y_given_m_x(...)`` (cellule 20) — la quantite ``P(Y | M, X)`` du cas
  front-door, extraite en fonction de premier ordre.

Determinisme — une difference nette avec le module frere
--------------------------------------------------------

``causal_organs.py`` documente une deviation explicite au pattern
« byte-identique strict » : ses estimateurs DiD et IV sont **aleatoires**
par construction, donc seules les grandeurs agregees sont comparables.

Ici, ce n'est pas le cas. ``enumerate_scm`` somme exhaustivement les
``2**n`` configurations d'un SCM booleen : il n'utilise **aucun RNG**. La
sortie est une fonction pure de ``(nodes, query, evidence, do_vars)``.

Consequence : l'egalite **byte-identique stricte** entre le module et la
cellule native est ici atteignable, et c'est elle que les tests verifient
(``==`` exact, pas ``approx``). C'est le pattern byte-identique de
``ict/bridges/pymc_enumerate.py``, applicable ici sans reserve.

Parametrisation (minimale, CLAUDE.md section D)
-----------------------------------------------

``enumerate_scm`` est reprise **sans modification algorithmique** de la
cellule 5 : meme signature, meme corps, meme convention de retour
(``nan`` si la masse de l'evidence est nulle).

``p_y_given_m_x`` est la seule fonction reellement parametree. Dans la
cellule 20 elle **capture** ``front_scm`` par cloture, ce qui la rend
inutilisable hors de ce notebook. Elle prend ici le SCM en argument
nomme, avec ``FRONT_SCM`` pour valeur par defaut — de sorte que
``p_y_given_m_x(mval, xval)`` rende exactement la valeur de la cellule 20,
tout en devenant applicable a un autre SCM.

References
----------

- Source canonique : ``MyIA.AI.Notebooks/Probas/PyMC/PyMC-05-Causal-Inference.ipynb``,
  cellules 5 et 20, branche ``origin/main``.
- Issue #14051 — table « Module a creer », ligne ``Probas/PyMC/pymc_causal_organs.py``.
- Le cas front-door suit Pearl (2009), *Causality*, chap. 3.3.
"""

from __future__ import annotations

import itertools
from typing import Callable, Dict, List, Optional, Sequence, Tuple

__all__ = ["enumerate_scm", "p_y_given_m_x", "FRONT_SCM"]

# Type de l'argument ``nodes`` : liste ordonnee topologiquement de couples
# (nom, fn) ou fn(assign) rend P(nom=True | parents), les parents etant lus
# dans le dict ``assign``.
SCM = Sequence[Tuple[str, Callable[[Dict[str, bool]], float]]]


def enumerate_scm(
    nodes: SCM,
    query: str,
    evidence: Optional[Dict[str, bool]] = None,
    do_vars: Optional[Dict[str, bool]] = None,
) -> float:
    """Inference exacte par enumeration sur un SCM discret booleen.

    Reprise byte-identique de la cellule 5 de ``PyMC-05-Causal-Inference.ipynb``.

    nodes    : liste ordonnee (topologique) de (nom, proba_true_fn). proba_true_fn(assign)
               renvoie P(nom=True | parents) en lisant les parents dans le dict `assign`.
    query    : nom du noeud dont on veut P(query=True).
    evidence : dict {nom: bool} de variables OBSERVEES (conditionnement / niveau 1).
    do_vars  : dict {nom: bool} de variables INTERVENUES (mutilation / niveau 2).

    Retourne P(query=True | evidence, do(do_vars)).
    """
    evidence = evidence or {}
    do_vars = do_vars or {}
    names = [n for n, _ in nodes]
    num = 0.0  # masse de (query=True, evidence)
    den = 0.0  # masse de (evidence)
    for bits in itertools.product([False, True], repeat=len(names)):
        assign = dict(zip(names, bits))
        # incompatibilite avec une intervention forcee -> proba nulle
        if any(assign[k] != v for k, v in do_vars.items()):
            continue
        if any(assign[k] != v for k, v in evidence.items()):
            continue
        p = 1.0
        for name, fn in nodes:
            if name in do_vars:        # arc parent coupe : la CPT devient une constante
                continue
            pt = fn(assign)
            p *= pt if assign[name] else (1.0 - pt)
        den += p
        if assign[query]:
            num += p
    return num / den if den > 0 else float("nan")


# SCM front-door de la cellule 20 : X=smoke, M=tar, Y=cancer, U=genotype (non observe).
# Reprise byte-identique des CPT de la cellule ; seul le nom passe de
# ``front_scm`` (local a la cellule) a ``FRONT_SCM`` (constante de module).
FRONT_SCM: List[Tuple[str, Callable[[Dict[str, bool]], float]]] = [
    ("u",      lambda a: 0.20),                          # genotype (latent)
    ("smoke",  lambda a: 0.80 if a["u"] else 0.30),      # U -> X
    ("tar",    lambda a: 0.90 if a["smoke"] else 0.10),  # X -> M
    ("cancer", lambda a: (0.95 if a["u"] else 0.70) if a["tar"]      # {M,U} -> Y
                          else (0.50 if a["u"] else 0.05)),
]


def p_y_given_m_x(mval: bool, xval: bool, scm: Optional[SCM] = None) -> float:
    """P(Y=True | M=mval, X=xval) — le terme interne de l'ajustement front-door.

    Reprise de la cellule 20 de ``PyMC-05-Causal-Inference.ipynb``. Dans la
    cellule, la fonction capture ``front_scm`` par cloture ; ici le SCM est
    un argument nomme dont la valeur par defaut ``FRONT_SCM`` reproduit
    exactement le comportement natif.

    mval : valeur du mediateur M (``tar``).
    xval : valeur du traitement X (``smoke``).
    scm  : le SCM a interroger (defaut : ``FRONT_SCM``, celui de la cellule 20).
    """
    if scm is None:
        scm = FRONT_SCM
    return enumerate_scm(scm, "cancer", evidence={"tar": mval, "smoke": xval})
