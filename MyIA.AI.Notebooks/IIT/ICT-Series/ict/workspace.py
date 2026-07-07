"""Workspace et ignition (ICT-24, strate 5 capstone technique, Epic #4588).

Le **workspace** est un objet intermediaire entre la dynamique continue des
features (ICT-20, :mod:`ict.feature_dynamics`) et la batterie d'emergence
causale discrete (ICT-15, :mod:`ict.synthesis`). Il re-emballe la lecture
d'un systeme multi-niches, multi-features en trois primitives mesurables :

* :func:`ignition_step` -- winner-take-all par pas de temps : pour chaque
  niche, la feature dont l'activation est la plus elevee cet instant
  ("qui s'allume quand"). Renvoie les ignitions par niche.
* :func:`hub_of_influence` -- top-K features par activation cumulee
  ("qui tient le workspace sur la duree"). Mesure d'influence, pas une
  ponderation physique.
* :func:`co_location_ignitions` -- matrice de co-allumage entre features,
  calculee sur la sequence de winners. Distingue l'anti-correlation
  (sorties opposees) du simple decalage temporel (co-allumage positif).
* :func:`event_triggered_battery` -- application directe de la batterie
  ``emergence_gain`` (:mod:`ict.synthesis`) a la suite d'etats discrets
  extraite du workspace. **Importe la fonction de maniere verbatim** (cf
  acceptance du ticket #5635) : pas de redifinition locale, pas de
  raccourci, pas de hack. Quand ``emergence_gain`` evolue, le workspace
  suit automatiquement.

Ce module est volontairement **numpy-only** : pas de scipy, pas de
ruptures, pas de reseaux. Toute la complexite de la batterie d'emergence
est delestee a :mod:`ict.synthesis`. La passerelle est le seul
responsabilite ajoutee ici, et elle est explicitee par 4 fonctions
autonomes que le notebook ICT-24 peut appeler individuellement.

Pourquoi un discretiseur quantile (et non un k-means ou une
classification supervisee)
--------------------------------------------------------------------
Le substrat de l'ICT-24 est un panel multi-niches multi-features reel,
dont la discretisation est un **choix** documente dans le notebook (cf
la convention ICT-15 : discretisation documentee dans le notebook, pas
constante cachee dans la lib). Le seul defaut raisonnable pour le mode
GPU-free / CPU 1 cycle est le **binning quantile** (``np.quantile``) :
c'est non-parametrique (rien a apprendre), c'est borne par construction
meme si le panel est lourdement skewed, et c'est reversible (les bornes
de chaque bin sont exposees).

Numpy uniquement (comme le reste du package leger ``ict``). Pas de scipy,
pas de ruptures, pas de sklearn. Testable sur un seul CPU, 1 cycle, AR(1)
synthetique.

References
----------
* ICT-0 (cadrage + feuille de route), Epic #4588 -- ce module est le
  dernier substrat prevu avant la jonction notebook ICT-24.
* :mod:`ict.feature_dynamics` -- source des panel synthetiques AR(1)
  calibres pour les transitions anodines (le "neutre" qui sert ici
  d'hub planté pour la falsification).
* :mod:`ict.synthesis` -- machine d'emergence causale discrete que ce
  module appelle verbatim (sans modification locale).
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Dict, Sequence, Tuple

import numpy as np

# Import VERBATIM -- ne pas redefinir emergence_gain localement (acceptance
# ticket #5635, audit anti-regression) : evoluera avec synthesis.py sans
# intervention ici.
from . import synthesis as SYN


# --------------------------------------------------------------------------- #
# Dataclasse Workspace
# --------------------------------------------------------------------------- #
@dataclass
class Workspace:
    """Matrice niches x features d'activations au cours du temps.

    Attributs
    ---------
    activations : np.ndarray, shape ``(T, N, F)``
        ``T`` pas de temps, ``N`` niches, ``F`` features. Convention axe 0 =
        temps. Une seule matrice 3D : on evite la liste de frames ou la
        structure nichee pour rendre la vectorisation triviale.
    niche_names : list[str], longueur ``N``
        Etiquettes lisibles des niches (defaut : ``["niche_0", ..., "niche_{N-1}"]``).
    feature_names : list[str], longueur ``F``
        Etiquettes lisibles des features (defaut : ``["f_0", ..., "f_{F-1}"]``).
    """

    activations: np.ndarray
    niche_names: list = field(default_factory=list)
    feature_names: list = field(default_factory=list)

    def __post_init__(self) -> None:
        a = np.asarray(self.activations, dtype=float)
        if a.ndim != 3:
            raise ValueError(
                f"activations doit etre de forme (T, N, F), recu shape={a.shape}"
            )
        t, n, f = a.shape
        if not self.niche_names:
            self.niche_names = [f"niche_{i}" for i in range(n)]
        else:
            if len(self.niche_names) != n:
                raise ValueError(
                    f"niche_names longueur {len(self.niche_names)} != N={n}"
                )
        if not self.feature_names:
            self.feature_names = [f"f_{j}" for j in range(f)]
        else:
            if len(self.feature_names) != f:
                raise ValueError(
                    f"feature_names longueur {len(self.feature_names)} != F={f}"
                )
        self.activations = a

    @property
    def n_steps(self) -> int:
        return int(self.activations.shape[0])

    @property
    def n_niches(self) -> int:
        return int(self.activations.shape[1])

    @property
    def n_features(self) -> int:
        return int(self.activations.shape[2])


# --------------------------------------------------------------------------- #
# 1) ignition_step : winner-take-all par niche, par pas de temps
# --------------------------------------------------------------------------- #
def ignition_step(workspace: Workspace, threshold_quantile: float = 0.85) -> dict:
    """Indices et intensites des features dominantes par niche.

    Pour chaque niche ``i`` et chaque pas de temps ``t``, on garde
    l'index ``argmax_j activations[t, i, j]`` -- la feature "qui s'allume"
    a cet instant dans cette niche. On conserve aussi la valeur de
    l'activation correspondante (utile comme mesure d'intensite) et un
    booleen ``above_threshold`` : True si l'activation depasse le quantile
    declare sur l'integralite du panel (un signal qu'il y a vraiment
    ignition, pas un bruit faible qui gagne par accident).

    Parametres
    ----------
    workspace : Workspace
        Matrice ``(T, N, F)`` d'activations.
    threshold_quantile : float dans ``[0, 1]``
        Seuil de lemination au-dessus duquel une activation est creditee
        "ignition" (et pas juste le max par defaut). Defaut ``0.85`` =
        top 15% des activations observees sur le panel.

    Retour
    ------
    dict avec :
        ``winners`` : ``np.ndarray`` shape ``(T, N)`` int, indices des
            features gagnantes par (t, niche).
        ``intensities`` : ``np.ndarray`` shape ``(T, N)`` float, valeurs
            des activations gagnantes.
        ``above_threshold`` : ``np.ndarray`` shape ``(T, N)`` bool, True
            si l'activation du gagnant depasse ``threshold_quantile``.
        ``threshold_value`` : float, la valeur du quantile utilisee.
    """
    a = workspace.activations
    winners = np.argmax(a, axis=2)  # shape (T, N)
    # Intensites : gather sur la troisieme dim -- boucle par niche.
    intensities = np.take_along_axis(a, winners[..., None], axis=2).squeeze(axis=2)
    thr = float(np.quantile(a, threshold_quantile))
    return {
        "winners": winners,
        "intensities": intensities,
        "above_threshold": intensities >= thr,
        "threshold_value": thr,
    }


# --------------------------------------------------------------------------- #
# 2) hub_of_influence : top-K features par activation cumulee
# --------------------------------------------------------------------------- #
def hub_of_influence(workspace: Workspace, top_k: int = 5) -> dict:
    """Top-K features par activation cumulee sur l'integralite du panel.

    Une feature "influence le workspace" si son activation cumulee sur
    toutes les niches et tous les pas de temps est importante. La
    normalisation par ``T*N`` (moyenne par (niche, pas de temps)) rend la
    mesure independante de la longueur du panel et du nombre de niches.

    Parametres
    ----------
    workspace : Workspace
        Matrice ``(T, N, F)`` d'activations.
    top_k : int
        Nombre de features a retourner dans le top.

    Retour
    ------
    dict avec :
        ``mean_per_feature`` : ``np.ndarray`` shape ``(F,)`` float,
            activation moyenne par feature (sur tous les T et toutes les N).
        ``total_per_feature`` : ``np.ndarray`` shape ``(F,)`` float,
            activation cumulee par feature.
        ``order`` : ``np.ndarray`` shape ``(F,)`` int, indices des
            features classes par ordre d'activation cumulee decroissante.
        ``top_k`` : ``(K,)`` indices des top features (= ``order[:top_k]``).
        ``top_k_names`` : list[str], longueur ``K``, noms correspondants.
        ``top_k_mean`` : ``(K,)`` float, moyennes des top features.
    """
    total = workspace.activations.sum(axis=(0, 1))  # shape (F,)
    mean = workspace.activations.mean(axis=(0, 1))  # shape (F,)
    order = np.argsort(total)[::-1]
    k = int(min(top_k, workspace.n_features))
    top_idx = order[:k]
    return {
        "mean_per_feature": mean,
        "total_per_feature": total,
        "order": order,
        "top_k": top_idx,
        "top_k_names": [workspace.feature_names[i] for i in top_idx],
        "top_k_mean": mean[top_idx],
    }


# --------------------------------------------------------------------------- #
# 3) co_location_ignitions : matrice de co-allumage entre features
# --------------------------------------------------------------------------- #
def co_location_ignitions(workspace: Workspace, ignition_times=None) -> dict:
    """Matrice symetrique de co-allumage entre paires de features.

    Pour chaque pas de temps ``t`` et chaque niche ``i``, on garde
    l'index de la feature gagnante (:func:`ignition_step`). Puis, par
    paire ``(j1, j2)``, on compte le nombre de (t, i) ou **les deux**
    features sont gagneuses **dans la meme niche au meme instant** --
    c'est la definition stricte de la co-location (pas de lag temporel,
    pas de correlation retardee).

    Le panneau diagonal est le nombre d'ignitions (toute feature gagne
    par (t, i)) : c'est la "densite d'ignition" du workspace. La
    symmetrie est triviale puisque la definition est symetrique.

    Parametres
    ----------
    workspace : Workspace
        Matrice ``(T, N, F)``.
    ignition_times : None
        Reserve pour evolution future (restriction a un sous-ensemble
        de pas de temps). Aujourd'hui : ignore, la signature reste
        stable pour evolutivite.

    Retour
    ------
    dict avec :
        ``co_count`` : ``np.ndarray`` shape ``(F, F)`` int, comptes
            bruts de co-allumage par paire de features.
        ``co_rate`` : ``np.ndarray`` shape ``(F, F)`` float, taux de
            co-allumage normalise par le nombre total d'ignitions (la
            diagonale). La diagonale de ``co_rate`` est 1.0 par
            construction (chaque feature est co-allumee avec elle-meme
            partout ou elle s'allume).
        ``n_ignitions`` : int, nombre total de (t, i) ou une feature
            est gagneante (= le denomineur de la normalisation).
    """
    _ = ignition_times  # signature stable ; ignore pour l'instant
    ign = ignition_step(workspace)
    winners = ign["winners"]  # shape (T, N)
    t, n = winners.shape
    f = workspace.n_features
    # Encodage one-hot : shape (T*N, F) ; 1 exactement a la colonne gagnante.
    # Important : utiliser ``int`` (et pas ``bool``) pour que ``@`` retourne
    # un compte entier, pas un booleen (sinon on plafonne a 1 -- bug attrape
    # par Gate 4 du test_workspace.py).
    flat = winners.reshape(-1)  # shape (T*N,)
    one_hot = np.zeros((flat.shape[0], f), dtype=np.int64)
    one_hot[np.arange(flat.shape[0]), flat] = 1
    co_count = one_hot.T @ one_hot  # shape (F, F), int
    n_ign = int(one_hot.sum())
    if n_ign == 0:
        # Aucune ignition : tout reste a zero, taux = 0 par convention.
        co_rate = np.zeros_like(co_count, dtype=float)
    else:
        co_rate = co_count / float(n_ign)
    return {
        "co_count": co_count.astype(int),
        "co_rate": co_rate.astype(float),
        "n_ignitions": n_ign,
    }


# --------------------------------------------------------------------------- #
# 4) event_triggered_battery : passerelle vers emergence_gain VERBATIM
# --------------------------------------------------------------------------- #
def _discretize_workspace(
    workspace: Workspace, n_bins: int = 4
) -> np.ndarray:
    """Discretise les activations du workspace en ``n_bins`` niveaux quantiles.

    Chaque feature est binnée **independamment** (les ``n_bins`` quantiles
    sont calcules par colonne de la matrice ``(T, N, F)``). Le bin
    resultant est dans ``[0, n_bins - 1]``. Le resultat est un seul
    tableau d'entiers shape ``(T, N, F)`` -- chaque "evenement" est un
    triplet (t, i, j) avec une valeur discretee dans ``[0, n_bins - 1]``.

    Bornes strictes (cf acceptance ticket #5635) :
      * ``n_bins >= 2`` (un seul bin ne porte aucune information) ;
      * les valeurs manquantes ou constantes par feature donnent un
        tableau rempli de ``0`` (comportement deterministe, pas de NaN).
    """
    if n_bins < 2:
        raise ValueError(f"n_bins doit etre >= 2 (reçu {n_bins})")
    a = workspace.activations
    t, n, f = a.shape
    discretized = np.zeros((t, n, f), dtype=int)
    # Quantiles par feature, sur l'axe temps concatene aux niches.
    flat = a.reshape(t * n, f)
    for j in range(f):
        col = flat[:, j]
        if np.all(col == col[0]):
            # Feature constante : tout dans le bin 0 (deterministe, pas de NaN).
            discretized[:, :, j] = 0
            continue
        # `n_bins - 1` seuils via np.quantile, puis np.searchsorted.
        qs = np.linspace(0.0, 1.0, n_bins + 1)[1:-1]
        edges = np.quantile(col, qs)
        bins = np.searchsorted(edges, col)
        discretized[:, :, j] = bins.reshape(t, n)
    return discretized


def event_triggered_battery(
    workspace: Workspace,
    ignition_times=None,
    rng: np.random.Generator = None,
    n_shuffles: int = 20,
    n_bins: int = 4,
    unseen: str = "self",
) -> dict:
    """Batterie d'emergence sur les evenements extraits du workspace.

    Pipeline en 4 etapes strictement bornees :

      1. discretisation quantile par feature (``n_bins`` niveaux, defaut 4) ;
      2. concatenation des (t, i) en une suite lineaire d'etats (la
         batterie emergence_gain opere sur des sequences discretes
         unidimensionnelles) ;
      3. import **verbatim** de :func:`ict.synthesis.emergence_gain` (cf
         acceptance #5635) ;
      4. retour du meme dict que emergence_gain, augmente de ``n_bins``
         et ``n_ignitions`` pour la tracabilite.

    Parametres
    ----------
    workspace : Workspace
        Matrice ``(T, N, F)`` d'activations.
    ignition_times : None
        Reserve ; signature stable pour extension ulterieure.
    rng : np.random.Generator
        Generateur de nombres aleatoires reproductible (defaut :
        ``np.random.default_rng(0)``).
    n_shuffles : int
        Nombre de permutations pour le controle shuffle (defaut 20).
    n_bins : int
        Nombre de niveaux quantiles pour la discretisation (defaut 4).
    unseen : str
        Politique pour les etats non vus en transition (``"self"`` ou
        ``"absorb"``), transmise a ``emergence_gain`` (cf
        :mod:`ict.tpm_estimation`).

    Retour
    ------
    dict conforme au retour de :func:`ict.synthesis.emergence_gain`
    (``ei_real``, ``ei_shuffled``, ``ei_gain``, ``ec_real``,
    ``ec_shuffled``, ``ec_gain``, ``credited``, ``n_states``,
    ``fe_gain``, ``k_gain``) + ``n_bins`` (int) + ``n_ignitions`` (int)
    + ``sequence_length`` (int) pour la tracabilite.
    """
    _ = ignition_times  # signature stable ; ignore
    if rng is None:
        rng = np.random.default_rng(0)
    discretized = _discretize_workspace(workspace, n_bins=n_bins)
    # Encode chaque (t, i) comme un tuple (i, j_bin) -- "niche i, feature j,
    # bin k". On garde la trace de la niche pour la tracabilite
    # (sequence_length = nombre d'evenements), mais emergence_gain n'opere
    # que sur les labels : on aplatit en str(niche) + "_" + str(feature) +
    # "_" + str(bin) pour eviter les collisions cross-niches.
    t, n, f = discretized.shape
    seq: list = []
    for tt in range(t):
        for ii in range(n):
            bins = discretized[tt, ii]  # shape (F,)
            for jj in range(f):
                seq.append((ii, jj, int(bins[jj])))
    # IMPORT VERBATIM (acceptance #5635) -- ne PAS redefinir emergence_gain.
    battery = SYN.emergence_gain(
        seq, rng=rng, n_shuffles=n_shuffles, unseen=unseen
    )
    battery["n_bins"] = int(n_bins)
    battery["n_ignitions"] = int(t * n * f)
    battery["sequence_length"] = int(len(seq))
    return battery


# --------------------------------------------------------------------------- #
# API publique
# --------------------------------------------------------------------------- #
__all__ = [
    "Workspace",
    "ignition_step",
    "hub_of_influence",
    "co_location_ignitions",
    "event_triggered_battery",
]
