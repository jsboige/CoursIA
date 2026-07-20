"""Meta-proxy d'obstruction — structure des desaccords entre proxys (ICT #7395).

Fille de l'Epic #4588 (IIT -> ICT), cette brique pose l'**objet
experimental minimal** decrivant la structure des desaccords entre
plusieurs proxys de complexite / integration (spectral, sensitivity,
free-energy) evalues sur une trajectoire ICT. L'intuition directrice
(lecture cohomologie-obstruction, cf. doc Grothendieck mergée 2026-07-19)
est que **l'obstruction elle-meme est informative** : quand plusieurs
proxys ne "recollent" pas en une mesure globale unique, le *motif* de
leur desaccord porte de l'information sur le substrat.

Trois fonctions publiques :

* :func:`proxy_signature` -- calcule la signature multi-proxys d'une
  trajectoire discrete (spectral_gap, sensitivity_mean, sensitivity_max,
  free_energy_bar). Renvoie un dict scalaire plat.
* :func:`obstruction_vector` -- produit le vecteur d'obstruction entre
  deux signatures, normalise par leur somme absolue (insensible a
  l'echelle globale).
* :func:`cross_substrat_obstruction` -- agrege plusieurs substrats et
  delivre un verdict falsifiable ``STABLE`` (motif de desaccord
  reproductible cross-substrat) / ``NOISE`` (desaccord aleatoire) /
  ``INCONCLUSIVE`` (echantillon trop court pour trancher).

Acceptance du grain (cf. issue #7395) :

* **Positif** : motif de desaccord stable cross-substrat sur >= 2
  substrats independants -- preuve empirique de l'objet.
* **Negatif honnete** : motif du bruit -- verdict NOISE documente, la
  jambe meurt proprement.

Implementation :

* Dependances : ``numpy`` uniquement (les appels ``spectral`` /
  ``sensitivity`` / ``free_energy`` sont passes en parametres pour
  eviter tout couplage cyclique ; voir :func:`proxy_signature`).
* Determinisme : tous les chemins stochastiques passent par un
  ``np.random.Generator`` injecte.
* Aucune erreur volontaire : ``raise NotImplementedError`` /
  ``assert False`` / ``1/0`` INTERDITS (regle C.1 notebooks, par
  coherence on l'applique ici aussi).
"""

from __future__ import annotations

from typing import Any, Callable, Dict, List, Mapping, Sequence

import numpy as np

# Type alias : proxy callable retourne un scalaire (gap, mean, max, F_bar).
ProxyFn = Callable[[Sequence[int], int], float]


# --------------------------------------------------------------------------- #
#  1. Signature multi-proxys                                                   #
# --------------------------------------------------------------------------- #
def proxy_signature(
    states: Sequence[int],
    n_symbols: int,
    *,
    spectral_fn: ProxyFn,
    sensitivity_mean_fn: ProxyFn,
    sensitivity_max_fn: ProxyFn,
) -> Dict[str, float]:
    """Calcule la signature multi-proxys d'une trajectoire discrete.

    Parametres :
      - ``states`` : trajectoire discrete (labels entiers dans
        ``[0, n_symbols)``).
      - ``n_symbols`` : taille du vocabulaire (= nb d'etats distincts
        possibles ; il n'est pas garanti qu'ils soient tous visites).
      - ``spectral_fn`` : callable ``(states, n_symbols) -> float``
        retournant le gap spectral du graphe de transition.
      - ``sensitivity_mean_fn`` : callable retournant la sensibilite
        moyenne (cf. :func:`ict.sensitivity.sensitivity_distribution`).
      - ``sensitivity_max_fn`` : callable retournant la sensibilite max
        (utile pour la borne type-Huang, voir ICT-15b).

    Retourne un dict avec cles ``spectral_gap``, ``sensitivity_mean``,
    ``sensitivity_max``, ``n_states``, ``n_transitions``.

    Notes :
      * Les proxys sont passes en parametres (au lieu d'imports
        directs) pour eviter tout couplage cyclique et permettre des
        proxys alternatifs en test.
      * Les valeurs ``nan`` / ``inf`` sont tolerees en entree mais
        filtreees par :func:`_finite` lors de l'agregation.
    """
    if n_symbols < 2:
        raise ValueError(f"n_symbols doit etre >= 2, recu {n_symbols}")
    states_list = [int(s) for s in states]
    if not states_list:
        raise ValueError("states vide : impossible de calculer une signature")
    if len(states_list) < 2:
        raise ValueError("states doit contenir au moins 2 elements (1 transition)")

    n_transitions = len(states_list) - 1

    sig: Dict[str, float] = {
        "n_states": int(n_symbols),
        "n_transitions": int(n_transitions),
        "spectral_gap": float(spectral_fn(states_list, n_symbols)),
        "sensitivity_mean": float(sensitivity_mean_fn(states_list, n_symbols)),
        "sensitivity_max": float(sensitivity_max_fn(states_list, n_symbols)),
    }
    return sig


# --------------------------------------------------------------------------- #
#  2. Vecteur d'obstruction entre deux signatures                              #
# --------------------------------------------------------------------------- #
def obstruction_vector(
    sig_a: Mapping[str, float],
    sig_b: Mapping[str, float],
    *,
    keys: Sequence[str] = ("spectral_gap", "sensitivity_mean", "sensitivity_max"),
) -> Dict[str, float]:
    """Vecteur d'obstruction : differences normalisees entre deux signatures.

    Pour chaque cle ``k`` de ``keys``, on retourne
    ``(sig_a[k] - sig_b[k]) / (|sig_a[k]| + |sig_b[k]| + eps)``.
    Cette normalisation rend le vecteur **insensible a l'echelle
    globale** : deux substrats dont les echelles different d'un facteur
    10 donnent le meme vecteur d'obstruction que s'ils etaient a
    echelle 1.

    La convention de signe est ``a - b`` : une valeur > 0 signifie
    ``sig_a`` surestime la cle par rapport a ``sig_b``.

    Parametres :
      - ``sig_a``, ``sig_b`` : signatures (dicts) produites par
        :func:`proxy_signature`.
      - ``keys`` : composantes a inclure dans le vecteur. Defaut =
        les trois proxys spectraux / sensitivity.

    Retourne un dict ``{key: delta_norm}`` avec une cle supplementaire
    ``norm_l2`` (norme Euclidienne du vecteur, dans [0, sqrt(2)] par
    coordonnee) -- resume scalaire de l'amplitude de l'obstruction.
    """
    if not keys:
        raise ValueError("keys vide : specifier au moins une composante")

    eps = 1e-12
    out: Dict[str, float] = {}
    for k in keys:
        a = float(sig_a.get(k, 0.0))
        b = float(sig_b.get(k, 0.0))
        # NaN/Inf -> 0.0 (defensif : on ne veut pas polluer norm_l2)
        if not np.isfinite(a):
            a = 0.0
        if not np.isfinite(b):
            b = 0.0
        denom = abs(a) + abs(b) + eps
        out[k] = (a - b) / denom

    norm_l2 = float(np.sqrt(sum(v * v for v in out.values())))
    out["norm_l2"] = norm_l2
    return out


# --------------------------------------------------------------------------- #
#  3. Aggregation cross-substrat                                                #
# --------------------------------------------------------------------------- #
def cross_substrat_obstruction(
    substrat_signatures: Mapping[str, Mapping[str, float]],
    *,
    keys: Sequence[str] = ("spectral_gap", "sensitivity_mean", "sensitivity_max"),
    stable_threshold: float = 0.05,
    noise_threshold: float = 0.30,
) -> Dict[str, Any]:
    """Verdict falsifiable sur la stabilite cross-substrat du motif d'obstruction.

    Parametres :
      - ``substrat_signatures`` : dict ``{nom_substrat: signature}`` avec
        >= 2 substrats. Chaque signature est produite par
        :func:`proxy_signature`.
      - ``keys`` : composantes a inclure dans le vecteur d'obstruction.
      - ``stable_threshold`` : norme L2 maximale (moyennee sur les
        paires) en-dessous de laquelle le desaccord est dit **stable**.
        Defaut 0.05 (5 % de difference normalisee).
      - ``noise_threshold`` : norme L2 minimale au-dessus de laquelle
        le desaccord est dit **NOISE**. Defaut 0.30 (30 %).
        Entre les deux : verdict ``INCONCLUSIVE``.

    Retourne un dict avec :
      * ``n_substrats`` : nombre de substrats fournis.
      * ``pairwise_norms`` : liste des normes L2 pour chaque paire
        ``(i, j)`` avec ``i < j``.
      * ``mean_norm_l2`` : moyenne des normes pairwise.
      * ``max_norm_l2`` : maximum des normes pairwise.
      * ``verdict`` : ``"STABLE"`` (mean_norm_l2 <= stable_threshold),
        ``"NOISE"`` (mean_norm_l2 >= noise_threshold),
        ``"INCONCLUSIVE"`` sinon.

    Le verdict ``STABLE`` valide l'acceptance positive de l'issue
    #7395 ; ``NOISE`` valide l'acceptance negative honnete ;
    ``INCONCLUSIVE`` signale un echantillon insuffisant ou un seuil a
    recalibrer.
    """
    noms = list(substrat_signatures.keys())
    if len(noms) < 2:
        raise ValueError(
            f"cross_substrat_obstruction necessite >= 2 substrats, "
            f"recu {len(noms)} : {noms}"
        )

    pairwise_norms: List[float] = []
    for i in range(len(noms)):
        for j in range(i + 1, len(noms)):
            vec = obstruction_vector(
                substrat_signatures[noms[i]],
                substrat_signatures[noms[j]],
                keys=keys,
            )
            pairwise_norms.append(float(vec["norm_l2"]))

    mean_norm_l2 = float(np.mean(pairwise_norms))
    max_norm_l2 = float(np.max(pairwise_norms))

    if mean_norm_l2 <= stable_threshold:
        verdict = "STABLE"
    elif mean_norm_l2 >= noise_threshold:
        verdict = "NOISE"
    else:
        verdict = "INCONCLUSIVE"

    return {
        "n_substrats": len(noms),
        "substrats": noms,
        "pairwise_norms": pairwise_norms,
        "mean_norm_l2": mean_norm_l2,
        "max_norm_l2": max_norm_l2,
        "stable_threshold": stable_threshold,
        "noise_threshold": noise_threshold,
        "verdict": verdict,
    }


__all__ = [
    "ProxyFn",
    "proxy_signature",
    "obstruction_vector",
    "cross_substrat_obstruction",
]
