"""Organes canoniques de la ligne dowhy -- contrefactuel individuel (DoWhy-2).

Issue #14049 (slice 1/4, DoWhy-2-Contrefactuel-Individuel) : chaque notebook
de la serie DoWhy expose son organe des sa livraison -- une petite API
importable a cote du notebook, que le notebook consomme et qu'un tiers
(ICT, un autre notebook) peut appeler sans recopier (lecon #13921 :
la duplication se cree quand un consommateur recopie une fonction
cell-scoped parce qu'il n'y a rien d'appelable).

Ce module est le frere de ``causal_organs.py`` (scope : Quasi-Experimental,
issue #14051) -- scope distinct, fichier distinct, zero collision avec la
tranche 2/2 de #14051.

Fonctions exposees
------------------

- ``generer_donnees(n, seed)`` -- monde generatif a heterogeneite qui
  s'annule en moyenne : V ~ U(-1, 1), T = 0.5 + 0.3 V + N(0, 0.2),
  Y = 1 + 3 T V + 0.5 V + N(0, 0.5). ATE vrai = 3 E[V] = 0,
  CATE(v) = 3v (effect modification pure).
- ``construire_scm(donnees, degre_y)`` -- InvertibleStructuralCausalModel
  fitte : V racine (distribution empirique), T bruit additif lineaire,
  Y bruit additif polynomial de degre ``degre_y``. L'inversibilite des
  mecanismes a bruit additif est la condition pour abduction du bruit
  INDIVIDUEL (``counterfactual_samples`` avec ``observed_data`` l'exige).
- ``contrefactuel_individuel(scm, individu, variable, valeur)`` -- un
  contrefactuel pour UNE ligne : retourne les tirages de Y sous
  l'intervention ``variable = valeur`` (abduction sur l'individu observe).
- ``ecarts_contrefactuels(scm, donnees, variable, valeur, sous_echantillon)``
  -- boucle ROW-WISE (la version batch de ``counterfactual_samples`` ne
  fait pas l'abduction par individu) et retourne la Serie des ecarts
  Y_obs - Y_contrefactuel.

Doctrine de parametrisation (cf. ``causal_organs.py``, L532 MEMORY) :
RandomState LOCAL par fonction, jamais de dependance au seed global ;
les constantes du monde generatif vivent en constantes de module
documentees, les fonctions ne les exposent que par kwargs par defaut.

References
----------

- Notebook consommateur : ``DoWhy-2-Contrefactuel-Individuel.ipynb``.
- Precedent d'architecture : issue #14051 / ``causal_organs.py``.
- API dowhy 0.14 : ``gcm.InvertibleStructuralCausalModel``,
  ``gcm.AdditiveNoiseModel``, ``gcm.counterfactual_samples``.
"""

import networkx as nx
import numpy as np
import pandas as pd
from dowhy import gcm

# Monde generatif -- constantes documentees (l'unique verite du simulateur)
GRAPHE = [("V", "T"), ("V", "Y"), ("T", "Y")]
BETA_INTERACTION = 3.0  # CATE(v) = BETA_INTERACTION * v
COEF_V_Y = 0.5          # effet direct V -> Y
COEF_V_T = 0.3          # confondant V -> T
BRUIT_T = 0.2
BRUIT_Y = 0.5


def generer_donnees(n=600, seed=42):
    """Genere le DataFrame (V, T, Y) du monde a ATE nul, CATE heterogene."""
    rng = np.random.RandomState(seed)
    v = rng.uniform(-1, 1, n)
    t = 0.5 + COEF_V_T * v + rng.normal(0, BRUIT_T, n)
    y = 1.0 + BETA_INTERACTION * t * v + COEF_V_Y * v + rng.normal(0, BRUIT_Y, n)
    return pd.DataFrame({"V": v, "T": t, "Y": y})


def construire_scm(donnees, degre_y=2):
    """Construit et fitte le SCM a mecanismes inversibles.

    ``degre_y=2`` (polynomial) capte l'interaction T x V ; ``degre_y=1``
    (lineaire) ne le peut pas -- c'est le diagnostic de fragilite du
    notebook (un mecanisme mal specifie ecrase le contrefactuel).
    """
    scm = gcm.InvertibleStructuralCausalModel(nx.DiGraph(GRAPHE))
    scm.set_causal_mechanism("V", gcm.EmpiricalDistribution())
    scm.set_causal_mechanism("T", gcm.AdditiveNoiseModel(gcm.ml.create_linear_regressor()))
    if degre_y >= 2:
        regresseur_y = gcm.ml.create_polynom_regressor(degree=degre_y)
    else:
        regresseur_y = gcm.ml.create_linear_regressor()
    scm.set_causal_mechanism("Y", gcm.AdditiveNoiseModel(regresseur_y))
    gcm.fit(scm, donnees)
    return scm


def contrefactuel_individuel(scm, individu, variable="T", valeur=0.0, seed=42):
    """Contrefactuel pour UNE ligne : tirages de Y sous variable=valeur.

    ``individu`` : DataFrame d'une ligne (ou Series convertie ici).
    Retourne un DataFrame des tirages (colonnes = variables descendantes)
    ; l'effectif des tirages est fixe par dowhy (API 0.14 : pas de
    ``num_samples`` sur ``counterfactual_samples``).

    ``counterfactual_samples`` (API 0.14) n'expose pas non plus de
    ``random_state`` injectable : le seed global est pose TEMPORAIREMENT,
    l'etat du RNG de l'appelant etant sauvegarde puis restaure -- la
    doctrine du module (aucune dependance au seed global) reste tenue :
    zero effet de bord sur les tirages ulterieurs de l'appelant.
    """
    if isinstance(individu, pd.Series):
        individu = individu.to_frame().T
    etat_rng_appelant = np.random.get_state()
    try:
        np.random.seed(seed)
        return gcm.counterfactual_samples(
            scm,
            interventions={variable: lambda _: valeur},
            observed_data=individu,
        )
    finally:
        np.random.set_state(etat_rng_appelant)


def ecarts_contrefactuels(scm, donnees, variable="T", valeur=0.0, seed=42):
    """Serie des ecarts individuels Y_obs - Y_contrefactuel (boucle row-wise).

    La version batch de ``counterfactual_samples`` ne fait pas l'abduction
    par individu -- la boucle est la semantique voulue : CHAQUE ligne garde
    son bruit propre (abduction), seule l'intervention change.
    """
    ecarts = []
    for _, ligne in donnees.iterrows():
        tirages = contrefactuel_individuel(scm, ligne, variable, valeur, seed=seed)
        ecarts.append(float(ligne["Y"]) - float(tirages["Y"].mean()))
    return pd.Series(ecarts, index=donnees.index, name="ecart_individuel")
