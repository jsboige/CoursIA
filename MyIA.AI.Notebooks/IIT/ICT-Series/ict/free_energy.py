"""La jambe energie-libre du representant interne ``p_hat`` (strate 4, ICT-14).

ICT est ne << Integrated Complexity Theory >> (reformulation d'IIT issue d'une
discussion fondatrice, preservee verbatim dans ICT-0-Framing) : integration
**dynamique** (Phi_dyn), **minimisation de la surprise** (energie libre, lignee
Friston), **compression** (Schmidhuber). La serie a developpe la jambe *causale*
(Levin tri-morphogenese + Hoel emergence causale + Thom catastrophes) ; la jambe
energie-libre restait non attachee, alors que le banc experimentale la preparait
sans le dire : le representant interne ``p_hat`` d'ICT-10 (module ``catastrophe``).

Le pont est une reformulation, pas une refonte. Un modele generatif gaussien a
un pas predit ``p_hat[t]`` avec precision ``sigma^2`` ; la **surprise** de
l'observation reelle ``o[t]`` est la negative log-vraisemblance :

    S_t = -ln N(o_t ; p_hat_t, sigma^2_t)
        = 1/2 * [ (o_t - p_hat_t)^2 / sigma^2_t  +  ln(2 pi sigma^2_t) ]

C'est exactement l'**energie libre variationnelle** dans le cas gaussien ferme
(avec un prior posterieur = prediction, approximation Laplacienne). Elle se
decompose en deux termes dont la litterature Friston nomme les poles :

* **accuracy** (term d'erreur, pondere par la precision) :
  ``1/2 * (o_t - p_hat_t)^2 / sigma^2_t``. C'est le MSE **renormalise par la
  precision attendue** -- une erreur inattendue (sigma petit) coute plus cher
  qu'une erreur attendue (sigma grand).
* **complexity** (cout du modele, l'entropie de la prediction) :
  ``1/2 * ln(2 pi sigma^2_t)``. Croit avec l'incertitude revendiquee.

L'energie libre moyenne ``F_bar`` est la somme des deux sur la trajectoire.

Deux regimes, deux gates falsifiables (notebook ICT-14) :

1. **Precision fixe** (``sigma`` constant). Alors ``F_bar = MSE/(2 sigma^2) +
   cte`` : transformation **monotone** du MSE. Le classement des estimateurs par
   ``F_bar`` **coincide exactement** avec le classement par ``lead_error``.
   Verdict honnete : a precision fixe, l'energie libre n'est qu'un habillage du
   MSE -- il faut le dire plutot que le cacher.
2. **Precision adaptative** (``sigma^2_t`` = EMA causale des erreurs passees).
   Alors la ponderation ``1/sigma^2_t`` **varie** : une erreur courante est
   rapportee a la variance que le modele s'attendait a rencontrer. Aux
   discontinuites (famille ``creneau``), le ``p_hat`` a vitesse constante reste
   sur-confiant (sigma petit accumule en rampe) puis se plante au saut -- la
   surprise explose. Le classement par ``F_bar`` peut alors **diverger** du
   classement par MSE : c'est le seul regime ou l'energie libre ajoute quelque
   chose au-dela de l'erreur de prediction. Echo direct du verdict
   << avantage regime-dependant >> d'ICT-10.

Le banc reutilise integralement ``catastrophe`` (``constant_velocity_tracker``,
``persistence_tracker``, ``moving_average_tracker``, ``ar1_tracker``,
``lead_error``, ``anticipation_report``, ``prey_trajectory``) : on change la
metrique (MSE -> F), pas la scene. Numpy uniquement, comme tout le package leger
``ict`` -- hors numpy, le module ne depend de rien (PyPhi n'est sollicite que
pour les calculs IIT stricts sur petits systemes, hors-scope ici).
"""

from __future__ import annotations

from typing import Dict, Optional

import numpy as np

from . import catastrophe as cat


# Plancher numerique pour la precision : eviter log(0) et division par zero.
# Un estimateur trop confiant (sigma -> 0) ferait exploser la surprise ; on
# borne la precision par en bas pour garder les quantites finies et comparables.
_SIGMA2_FLOOR = 1e-6
_TWO_PI = 2.0 * np.pi


def gaussian_surprise(
    obs: np.ndarray, pred: np.ndarray, sigma
) -> np.ndarray:
    """Surprise (negative log-vraisemblance gaussienne) pas-a-pas.

    ``S_t = 1/2 * [(o_t - p_hat_t)^2 / sigma^2  +  ln(2 pi sigma^2)]``.

    Le deuxieme terme (``ln``) est le cout de complexite : il penalise un
    modele qui revendique beaucoup d'incertitude. Le premier est l'accuracy
    (erreur ponderee par la precision).

    Parametres
    ----------
    obs : array
        Observations reelles ``o_t``.
    pred : array
        Predictions du representant interne ``p_hat_t`` (alignees sur ``obs``).
    sigma : float ou array
        Ecart-type du modele generatif. Scalaire (precision fixe) ou tableau
        (precision adaptive, aligne sur ``obs``). La **variance** ``sigma^2``
        est bornee par ``_SIGMA2_FLOOR``.

    Renvoie
    -------
    array
        Surprise ``S_t`` par pas (>= 0 en pratique).
    """
    o = np.asarray(obs, dtype=float)
    p = np.asarray(pred, dtype=float)
    s = np.asarray(sigma, dtype=float)
    var = np.maximum(s * s, _SIGMA2_FLOOR)
    return 0.5 * ((o - p) ** 2 / var + np.log(_TWO_PI * var))


def adaptive_precision(
    errors: np.ndarray, alpha: float = 0.3, var0: Optional[float] = None
) -> np.ndarray:
    """Variance adaptive ``sigma^2_t`` par EMA **causale** des erreurs passees.

    ``sigma^2_t`` reflete l'incertitude que le modele s'attendait a rencontrer
    avant de voir ``o_t`` : c'est une EMA des carres d'erreur **anterieurs**
    (pas d'``o_t`` lui-meme, sinon fuite vers l'observation courante -- le
    modele ne peut pas savoir a l'avance qu'il va se tromper maintenant).

    ``sigma^2_t = alpha * err^2_{t-1} + (1 - alpha) * sigma^2_{t-1}``

    avec ``sigma^2_0 = var0`` (defaut : variance globale des erreurs, estimateur
    non causal raisonnable pour amorcer la recurrence). ``alpha`` grand = EMA
    reactive (le modele re-estime vite sa precision) ; ``alpha`` petit = EMA
    paresseuse (precision quasi-constante, on retombe vers le regime fixe).

    Parametres
    ----------
    errors : array
        Erreurs de prediction ``o_t - p_hat_t``.
    alpha : float
        Facteur de lissage EMA dans ``]0, 1]``.
    var0 : float ou None
        Variance initiale. Si None, ``var(errors)`` (amorce non causale).

    Renvoie
    -------
    array
        ``sigma^2_t`` aligne sur ``errors``, borde par ``_SIGMA2_FLOOR``.
    """
    e = np.asarray(errors, dtype=float)
    a = float(alpha)
    if not 0.0 < a <= 1.0:
        raise ValueError(f"alpha doit etre dans ]0, 1], recu {a}")
    if var0 is None:
        var0 = float(np.var(e)) if e.size else 1.0
    var0 = max(float(var0), _SIGMA2_FLOOR)
    var = np.empty_like(e)
    prev = var0
    sq = e * e
    # sigma^2_t n'utilise QUE err_{t-1} (causal) : a t=0, rien de connu -> var0.
    for t in range(e.shape[0]):
        var[t] = prev
        prev = a * sq[t] + (1.0 - a) * prev
    return np.maximum(var, _SIGMA2_FLOOR)


def free_energy_trajectory(
    obs: np.ndarray,
    pred: np.ndarray,
    sigma=None,
    mode: str = "fixed",
    alpha: float = 0.3,
    var0: Optional[float] = None,
) -> Dict[str, np.ndarray]:
    """Trajectoire d'energie libre ``F_t`` + decomposition accuracy/complexity.

    Si ``mode="fixed"`` : ``sigma`` scalaire requis (defaut 1.0). ``F_bar`` est
    alors une transformation monotone du MSE (gate 1 : habillage du MSE).
    Si ``mode="adaptive"`` : ``sigma^2_t`` calcule par ``adaptive_precision`` sur
    les erreurs (gate 2 : la ponderation varie, F peut diverger du MSE).

    Renvoie un dict ``{"F", "accuracy", "complexity", "sigma2"}`` aligne sur
    ``obs``. ``F_t = accuracy_t + complexity_t``.
    """
    o = np.asarray(obs, dtype=float)
    p = np.asarray(pred, dtype=float)
    if mode == "fixed":
        s = 1.0 if sigma is None else float(sigma)
        var = np.full(o.shape, max(s * s, _SIGMA2_FLOOR))
    elif mode == "adaptive":
        var = adaptive_precision(o - p, alpha=alpha, var0=var0)
    else:
        raise ValueError(f"mode inconnu : {mode!r} ('fixed' ou 'adaptive')")
    accuracy = 0.5 * (o - p) ** 2 / var
    complexity = 0.5 * np.log(_TWO_PI * var)
    return {
        "F": accuracy + complexity,
        "accuracy": accuracy,
        "complexity": complexity,
        "sigma2": var,
    }


def fe_anticipation_report(
    observation: np.ndarray,
    lead: int = 4,
    alpha_cv: float = 0.25,
    sigma=None,
    mode: str = "fixed",
    alpha_prec: float = 0.3,
    window: int = 5,
    max_lag: int = 10,
) -> Dict[str, Dict[str, float]]:
    """Banc de mesure de l'anticipation, score en **energie libre moyenne**.

    Meme scene qu'``anticipation_report`` (4 estimateurs : ``p_hat``,
    ``persistance``, ``moyenne_mobile``, ``ar1`` ; 2 metriques separees) mais la
    metrique d'erreur est **``F_bar``** (sur la trajectoire alignee) au lieu du
    MSE ``lead_error``. ``pic_lag`` (lag du pic de correlation croisee) est
    conserve -- il mesure l'horizon d'anticipation, orthogonal a la metrique
    d'erreur.

    Pour chaque estimateur, renvoie ``{"F": F_bar, "erreur": MSE_lead,
    "pic_lag": lag}``. Les deux metriques d'erreur (F_bar et MSE) sont renvoyees
    ensemble : **c'est leur comparaison qui est le gate** -- a precision fixe les
    rangs coincident, a precision adaptive ils peuvent diverger.
    """
    obs = np.asarray(observation, dtype=float)
    estimateurs = {
        "p_hat": cat.constant_velocity_tracker(obs, lead=lead, alpha=alpha_cv),
        "persistance": cat.persistence_tracker(obs),
        "moyenne_mobile": cat.moving_average_tracker(obs, window=window),
        "ar1": cat.ar1_tracker(obs, lead=lead),
    }
    if lead < 1:
        raise ValueError(f"lead doit etre >= 1 (tache anticipative), recu {lead}")
    rapport: Dict[str, Dict[str, float]] = {}
    for nom, est in estimateurs.items():
        lags, corr = cat.cross_correlation(est, obs, max_lag=max_lag)
        # p_hat[t] anticipe obs[t+lead] : la surprise se mesure sur les paires
        # *lead-ahead* (est[t] vs obs[t+lead]), exactement la tache de
        # ``lead_error``. Sinon F et MSE ne scoreraient pas la meme chose et
        # leurs rangs divergeraient par artefact (gate 1 invalide).
        fe = free_energy_trajectory(
            obs[lead:], est[:-lead], sigma=sigma, mode=mode, alpha=alpha_prec
        )
        rapport[nom] = {
            "F": float(np.mean(fe["F"])),
            "erreur": cat.lead_error(est, obs, lead),
            "pic_lag": float(cat.peak_lag(lags, corr)),
        }
    return rapport


# --------------------------------------------------------------------------- #
#  Surprise transitionnelle (capstone ICT-15) : la jambe F sur la trajectoire  #
# --------------------------------------------------------------------------- #
# Contrairement a ``gaussian_surprise`` (continue, sur le representant interne
# ``p_hat``), la surprise transitionnelle mesure la **predictibilite d'un modele
# generatif discret** estime depuis la trajectoire : une TPM etat-a-etat est
# ajustee sur une portion d'apprentissage, puis la cross-entropie held-out
# ``-log2 P(s_{t+1} | s_t)`` est moyennee sur la portion de test. C'est la
# definition operationnelle de F pour le capstone ICT-15 (gate de convergence
# Φ/F/K), au meme titre que ``ec_gain`` est celle de Φ et ``k_gain`` celle de K.


def transition_surprise(states, split: float = 0.5, alpha: float = 0.5) -> dict:
    """Cross-entropie held-out d'une TPM etat-a-etat estimee sur la trajectoire.

    La sequence ``states`` (labels hachables) est coupee en deux : la 1re
    fraction ``split`` ajuste une TPM empirique (via
    ``tpm_estimation.tpm_from_transitions``), la 2de fraction mesure la
    surprise **held-out** ``F = mean(-log2 P(s_{t+1}|s_t))`` sur les transitions
    de test dont l'etat source a ete vu a l'entrainement.

    Lissage Laplace ``alpha`` (defaut 0.5, type Jeffreys) : ajoute ``alpha`` au
    compte de chaque transition (etat source vu) pour eviter ``log2(0)`` sur les
    transitions plausibles non observees a l'entrainement. La normalisation se
    fait sur le compte total par ligne (somme des comptes + ``alpha * n_vu``),
    ou ``n_vu`` est le nombre d'etats cibles possibles (l'unions des etats de
    train + l'etat cible courant). Documente honnetement : ce lissage est une
    *regularisation* modeste, pas un modele de structure -- la surprise mesure
    la predictibilite de l'ordre-1, pas une compression optimale.

    Retourne ``{"F": surprise moyennee, "n_train", "n_test", "alpha", "n_states"}``.
    ``F`` est en **bits** (base 2). Retourne ``F = nan`` si aucune transition de
    test n'a un etat source connu (trajectoire trop courte / split trop petit).
    """
    from . import tpm_estimation as TE

    seq = list(states)
    if not 0.0 < split < 1.0:
        raise ValueError(f"split doit etre dans ]0, 1[, recu {split}")
    n = len(seq)
    n_train = max(2, int(round(split * n)))
    if n_train >= n:
        # trajectoire trop courte pour un vrai split : on prend la 1re moitié
        n_train = max(1, n // 2)
    train = seq[:n_train]
    test = seq[n_train:]

    # TPM empirique sur le train : comptes bruts (non normalises) pour appliquer
    # le lissage Laplace nous-memes. ``tpm_from_transitions`` normalise, donc on
    # reconstruit les comptes a la main (cohrent avec ``_normalize_counts``).
    mapping: dict = {}
    for s in train:
        mapping.setdefault(s, len(mapping))
    # on enrichit le mapping des etats rencontres dans le test (un etat cible
    # inedit au test reste "surprenant" -- il compte dans le vocabulaire).
    for s in test:
        mapping.setdefault(s, len(mapping))
    counts = {src: {} for src in mapping}
    for a, b in zip(train, train[1:]):
        counts[a][b] = counts[a].get(b, 0) + 1.0

    # surprise held-out
    n_vu = len(mapping)
    surprisals = []
    for a, b in zip(test, test[1:]):
        if a not in mapping:
            # etat source jamais vu au train : on ne sait rien predire, on
            # l'ignore (pas de fuite : la TPM n'aurait pas de ligne pour lui).
            continue
        row = counts.get(a, {})
        total = sum(row.values()) + alpha * n_vu
        if total <= 0:
            continue
        p = (row.get(b, 0.0) + alpha) / total
        surprisals.append(-np.log2(p))

    if not surprisals:
        f = float("nan")
    else:
        f = float(np.mean(surprisals))
    return {
        "F": f,
        "n_train": int(n_train),
        "n_test": int(len(test)),
        "alpha": float(alpha),
        "n_states": int(n_vu),
    }


def surprise_gain(states, rng: np.random.Generator, n_shuffles: int = 20,
                  split: float = 0.5, alpha: float = 0.5) -> dict:
    """Gain de surprise : reel vs controle permute (le signal credite).

    ``fe_gain = F_shuffled - F_real`` : une trajectoire reelle structurée est
    PLUS previsible (F_real petit) qu'une permutation de memes etats
    (F_shuffled grand -- le shuffle detruit les transitions regulieres, la TPM
    held-out devient proche de l'uniforme). ``fe_gain`` positif = la dynamique
    porte de la structure predictable au-dela du reservoir d'etats.

    Contraste au MEME shuffle que ``emergence_gain`` (Φ) et ``compression_gain``
    (K) : les trois scalaires du capstone ICT-15 sont definis sur le meme
    controle degenere, condition necessaire au gate de convergence (Gate 4).
    """
    real = transition_surprise(states, split=split, alpha=alpha)
    seq = list(states)
    fs = []
    for _ in range(int(n_shuffles)):
        idx = rng.permutation(len(seq))
        perm = [seq[i] for i in idx]
        fs.append(transition_surprise(perm, split=split, alpha=alpha)["F"])
    f_shuffled = float(np.nanmean(fs)) if fs else float("nan")
    f_real = real["F"]
    if np.isnan(f_real) or np.isnan(f_shuffled):
        gain = float("nan")
    else:
        gain = float(f_shuffled - f_real)
    return {
        "F_real": f_real,
        "F_shuffled": f_shuffled,
        "fe_gain": gain,
        "n_shuffles": int(n_shuffles),
        "n_states": real["n_states"],
    }

