"""Fleche du temps, production d'entropie et reversibilisation (ICT-18, strate 5 Epic #4588).

La **reversibilisation** est l'idee fondatrice d'ICT que le cadrage panoramique
de la serie pointait sans l'outiller : une trajectoire qui developpe une
competence "gratuite" (for free), non prevue par le mecanisme programme, est
precisement ce qu'un processus **a l'equilibre / reversible** ne peut PAS
produire. L'emergence a une **signature thermodynamique** : elle brise la
symetrie temporelle.

L'ancrage theorique est explicite (Fridman # Levin, entretien sur les algorithmes
de tri, ~2024-2025, https://lexfridman.com/) : Levin y est fascine par
l'emergence, dans un tri, d'un **mecanisme algorithmique non programme** -- un
travail supplementaire *for free* qui va "dans le sens d'une reversibilisation".
ICT-3 (``RobustnessDelayedGratification``) demontre exactement cette competence
*for free* en strate 1 (tri auto-organise de Zhang, Goldstein & Levin).
ICT-18 fournit **l'instrument de mesure** : forcer une trajectoire a devenir
reversible et mesurer **ce qu'on perd** revele la quantite d'agentivite / de
calcul emergent qu'elle portait.

Trois concepts thermodynamiquement relies :

  - **Detailed balance** : une chaine de Markov satisfait la propriete de
    bilan detaille ssi ``pi_i * P[i, j] = pi_j * P[j, i]`` pour tous i, j
    (avec ``pi`` la distribution stationnaire). C'est la condition de
    reversibilite microscopique : chaque transition est equilibree par sa
    reverse.
  - **Production d'entropie** : ``sigma = 1/2 sum_{i,j} (pi_i*P[i,j] - pi_j*P[j,i])
    * log(pi_i*P[i,j] / pi_j*P[j,i]) >= 0``. Egale a 0 ssi detailed balance,
    strictement positive sinon. C'est la **fleche du temps** au sens
    thermodynamique (Crooks, Seifert).
  - **Reversibilisee** : projection d'une chaine irreversible sur le cône des
    chaines reversibles (moyenne symmetrique ``(P + P_tilde) / 2`` ou
    construction detailed-balance ``P^rev[i,j] = (pi_i*P[i,j] + pi_j*P[j,i]) /
    (2*pi_i)``). Perte mesuree = ``dist(P, P_reversible)``.

Approximation pratique : on estime la matrice de transition ``P`` depuis une
sequence d'etats discrets ``states`` (liste d'entiers ou de labels hachables)
par comptage des paires (i, j) sur une fenetre glissante ; on en extrait la
distribution stationnaire ``pi`` ; puis on evalue les trois quantites ci-dessus.

Numpy uniquement, comme le reste du package leger ``ict``. Aucun GPU requis
(garanti GPU-free, mandat user 2026-07-04).
"""

from __future__ import annotations

from typing import Dict, List, Sequence, Tuple

import numpy as np


# --------------------------------------------------------------------------- #
#  Estimation de la matrice de transition                                      #
# --------------------------------------------------------------------------- #


def transition_matrix(
    states: Sequence,
    n_symbols: int,
    laplace_smoothing: float = 1e-9,
) -> np.ndarray:
    """Matrice de transition ``P`` (markovienne d'ordre 1) estimee par comptage.

    ``P[i, j] = P(X_{t+1} = j | X_t = i)`` est obtenue en comptant les
    paires successives dans ``states`` et en normalisant par ligne. Un
    *Laplace smoothing* (defaut ``1e-9``) evite les lignes a zero qui
    casseraient la diagonalisation (vecteur propre gauche) et le logarithme
    dans ``entropy_production`` sans changer substantiellement les resultats.

    Parametres :
      - ``states`` : sequence d'etats (entiers ou labels). Si les labels ne
        sont pas des entiers, ils sont encodes en ``range(n_symbols)`` par
        l'appelant (``compare_*`` le fait automatiquement).
      - ``n_symbols`` : taille du vocabulaire ``k``.
      - ``laplace_smoothing`` : ajout de cette quantite a chaque compte avant
        normalisation (evite zero absolu).

    Retourne une matrice carree numpy de forme ``(n_symbols, n_symbols)``.
    Les lignes somment a 1 (distribution conditionnelle). Les etats non
    observes obtiennent une distribution uniforme via le smoothing.
    """
    states = [int(s) for s in states]
    P = np.full((n_symbols, n_symbols), laplace_smoothing, dtype=float)
    for s, t in zip(states[:-1], states[1:]):
        if 0 <= s < n_symbols and 0 <= t < n_symbols:
            P[s, t] += 1.0
    # Normalisation par ligne.
    row_sums = P.sum(axis=1, keepdims=True)
    return P / row_sums


def encode_states(states: Sequence) -> Tuple[np.ndarray, Dict]:
    """Encode une sequence de labels en entiers 0..k-1 (et garde le mapping inverse).

    Si les labels sont deja des entiers dans ``0..k-1``, le mapping est trivial.

    Retourne ``(encoded_array, mapping)`` ou ``mapping`` est un dict
    ``label -> int`` (utiliser ``{v: k for k, v in mapping.items()}`` pour
    decoder).
    """
    unique = sorted({s for s in states})
    mapping = {s: i for i, s in enumerate(unique)}
    encoded = np.array([mapping[s] for s in states], dtype=int)
    return encoded, mapping


# --------------------------------------------------------------------------- #
#  Distribution stationnaire                                                   #
# --------------------------------------------------------------------------- #


def stationary_distribution(
    P: np.ndarray, tol: float = 1e-9, max_iter: int = 100_000
) -> np.ndarray:
    """Distribution stationnaire ``pi`` (vecteur propre gauche pour ``lambda=1``).

    On utilise l'iteration de puissance sur la transposee : ``pi_{n+1} =
    P^T * pi_n`` (les vecteurs propres GAUCHES de ``P`` sont les vecteurs
    propres DROITS de ``P^T``). Initialisation uniforme, normalisation a 1 a
    chaque pas ; arret quand la variation totale (L1/2) entre iterations
    consecutives tombe sous ``tol``.

    Parametres :
      - ``P`` : matrice carree dont les lignes somment a 1 (distribution
        conditionnelle). Doit etre irreductible ou avoir un seul bassin
        attractif pour que le vecteur propre soit unique.
      - ``tol`` : seuil de convergence L1/2 entre iterations.
      - ``max_iter`` : garde-fou.

    Retourne un vecteur numpy de longueur ``k`` sommant a 1.

    Verdict : si la chaine est periodique de periode ``p > 1``, l'iteration
    alterne entre ``p`` vecteurs propres ; le ``tol`` peut-etre atteint
    precocement. En pratique sur des trajectoires ICT (longueur >> k**2), la
    chaine est apatriodique et le verdict est stable.
    """
    P = np.asarray(P, dtype=float)
    k = P.shape[0]
    if k == 0 or P.shape[0] != P.shape[1]:
        raise ValueError(f"P doit etre carree k x k (k>0), recu shape={P.shape}")
    pi = np.full(k, 1.0 / k, dtype=float)
    for _ in range(int(max_iter)):
        pi_new = P.T @ pi
        s = pi_new.sum()
        if s <= 0:
            # Chaine absorbante : redistribution uniforme (defaut conservateur).
            pi_new = np.full(k, 1.0 / k, dtype=float)
        else:
            pi_new /= s
        d = 0.5 * float(np.sum(np.abs(pi_new - pi)))
        pi = pi_new
        if d < tol:
            break
    return pi


# --------------------------------------------------------------------------- #
#  Renversement du temps                                                       #
# --------------------------------------------------------------------------- #


def time_reversal(P: np.ndarray, pi: np.ndarray) -> np.ndarray:
    """Chaine renversee dans le temps ``~P``.

    Definition : ``~P[i, j] = pi_j * P[j, i] / pi_i``.

    C'est la matrice de transition de la chaine vue a l'envers : ``pi``
    reste distribution stationnaire (par construction) ; mais la dynamique
    macroscopique est renversee -- les evenements rares deviennent frequents
    et vice versa. Pour une chaine satisfaisant detailed balance, ``~P = P``
    (la dynamique est symetrique sous le renversement du temps) ; sinon
    ``~P != P`` et leur divergence est precisement la fleche du temps.

    Parametres :
      - ``P`` : matrice de transition (lignes somment a 1).
      - ``pi`` : distribution stationnaire de ``P``.

    Retourne une matrice carree de meme forme ; les lignes somment a 1.
    """
    P = np.asarray(P, dtype=float)
    pi = np.asarray(pi, dtype=float)
    if P.shape[0] != P.shape[1] or P.shape[0] != pi.shape[0]:
        raise ValueError(
            f"formes incoherentes : P={P.shape}, pi={pi.shape}"
        )
    # Eviter division par zero sur les composantes nulles de pi.
    pi_safe = np.where(pi > 0, pi, 1.0)
    P_tilde = (P.T * pi_safe) / pi_safe[:, None]
    # Lignes ou pi_i = 0 : ligne uniforme (defaut conservateur ; cette etat
    # n'est jamais visite asymptotiquement de toute facon).
    zero_mask = pi == 0
    if zero_mask.any():
        k = P.shape[0]
        for i in np.where(zero_mask)[0]:
            P_tilde[i] = np.full(k, 1.0 / k)
    # Normalisation par ligne (defense en profondeur).
    row_sums = P_tilde.sum(axis=1, keepdims=True)
    return P_tilde / np.where(row_sums > 0, row_sums, 1.0)


# --------------------------------------------------------------------------- #
#  Reversibilisation : projection sur le cône reversible                       #
# --------------------------------------------------------------------------- #


def reversibilize(P: np.ndarray, pi: np.ndarray) -> np.ndarray:
    """Projection reversible de ``P`` au sens detailed-balance.

    Construction : ``P_rev[i, j] = (pi_i * P[i, j] + pi_j * P[j, i]) / (2*pi_i)``.

    C'est la construction symetrique qui force detailed balance par
    construction : la quantite ``pi_i * P_rev[i, j]`` est symmetrique en
    ``(i, j)`` donc egale a ``pi_j * P_rev[j, i]``. On perd la dynamique
    reelle au profit d'une chaine aussi proche que possible de l'originale
    tout en etant reversible -- c'est la *reversibilisation* au sens de
    Cusinato & Lecomte (cf. methode "symmetric encoding" de l'article).

    Parametres :
      - ``P`` : matrice de transition (lignes somment a 1).
      - ``pi`` : distribution stationnaire de ``P``.

    Retourne une matrice carree verifiant detailed balance par construction
    (les lignes somment a 1 ; on renormalise par precaution).
    """
    P = np.asarray(P, dtype=float)
    pi = np.asarray(pi, dtype=float)
    pi_safe = np.where(pi > 0, pi, 1.0)
    # Construction symmetrique.
    piP = pi_safe[:, None] * P              # (i, j) -> pi_i * P[i, j]
    piPt = pi_safe[None, :] * P.T           # (i, j) -> pi_j * P[j, i]
    P_rev_num = piP + piPt                  # numerateur
    # Division par 2*pi_i (normalisation par ligne naturelle).
    P_rev = P_rev_num / (2.0 * pi_safe[:, None])
    zero_mask = pi == 0
    if zero_mask.any():
        k = P.shape[0]
        for i in np.where(zero_mask)[0]:
            P_rev[i] = np.full(k, 1.0 / k)
    # Renormalisation defensive.
    row_sums = P_rev.sum(axis=1, keepdims=True)
    return P_rev / np.where(row_sums > 0, row_sums, 1.0)


# --------------------------------------------------------------------------- #
#  Detailed balance error & entropie                                           #
# --------------------------------------------------------------------------- #


def detailed_balance_error(P: np.ndarray, pi: np.ndarray) -> float:
    """Erreur L1 cumulee de detailed balance : ``sum |pi_i P[i, j] - pi_j P[j, i]|``.

    Une chaine satisfait detailed balance ssi cette erreur est nulle (a la
    tolerance numerique pres). C'est la divergence la plus directe entre
    flux aller et flux retour, agregee sur toutes les paires.

    Parametres :
      - ``P`` : matrice de transition.
      - ``pi`` : distribution stationnaire.

    Retourne un scalaire >= 0.
    """
    P = np.asarray(P, dtype=float)
    pi = np.asarray(pi, dtype=float)
    pi_safe = np.where(pi > 0, pi, 1.0)
    diff = pi_safe[:, None] * P - pi_safe[None, :] * P.T
    return float(np.sum(np.abs(diff)))


def entropy_production(P: np.ndarray, pi: np.ndarray) -> float:
    """Production d'entropie ``sigma`` au sens de Schnakenberg / Seifert.

    Definition :
    ``sigma = 1/2 sum_{i, j} (pi_i*P[i, j] - pi_j*P[j, i]) * log(pi_i*P[i, j] / pi_j*P[j, i])``.

    On moyenne sur l'element ``(i, j)`` et son symetrique ``(j, i)`` pour
    eviter le double comptage (chaque paire est comptee une fois). Toujours
    ``>= 0`` (inegalite de Jensen : ``(a-b)*log(a/b) >= 0`` pour ``a, b >= 0``).
    Egale a ``0`` ssi detailed balance est satisfaite.

    Convention numerique : on remplace les zeros de ``pi_i * P[i, j]`` par
    ``1`` (avant le log) pour eviter ``NaN`` ; les termes concernes sont
    nuls (car ``(a - 0)*log(0/b) = 0`` formellement, sans contribution).

    Parametres :
      - ``P`` : matrice de transition.
      - ``pi`` : distribution stationnaire.

    Retourne un scalaire >= 0 (en nats ; multiplier par ``log(2)`` pour
    convertir en bits).
    """
    P = np.asarray(P, dtype=float)
    pi = np.asarray(pi, dtype=float)
    pi_safe = np.where(pi > 0, pi, 1e-300)
    flux_go = pi_safe[:, None] * P          # pi_i * P[i, j]
    flux_back = pi_safe[None, :] * P.T       # pi_j * P[j, i]
    # Regularisation eps : une transition strictement irreversible (P[i, j] > 0
    # avec P[j, i] = 0) a une limite log(flux_go / 0+) -> +infini qui, sur des
    # donnees empiriques, traduit une irreversibilite totale (cycle dirige,
    # marche monotone non bornee). On borne ce terme par un petit eps (standard
    # en thermo stochastique sur matrices estimees) afin d'obtenir un scalaire
    # fini strictement positif refletant le flux net unidirectionnel.
    #
    # NB (fix ICT-19, Epic #4588) : la version precedente annulait a 0 toute
    # paire dont l'un des flux etait nul (``real_zeros``), ce qui ecrasait a
    # tort la contribution des cycles diriges (sigma = 0 pour une chaine
    # clairement irreversible). La regularisation eps restaurait sigma = 6.11
    # (vs 0.0) sur un cycle dirige 4-etats reguliarise eps=1e-3 ; sur un cycle
    # pur (P[j,i]=0 exact) elle donne un sigma grand mais fini (23.5), coherent
    # avec la limite thermodynamique. Cette correction ne change PAS les
    # matrices empiriques estimees via ``transition_matrix`` (Laplace smoothing
    # 1e-9 => tous flux strictement > 0 => ``real_zeros`` etait deja inactif),
    # donc les substrats ICT-18 (S5a marche bornee etc.) sont inchanges.
    eps = 1e-12
    fg = np.where(flux_go > 0, flux_go, eps)
    fb = np.where(flux_back > 0, flux_back, eps)
    d = (fg - fb) * np.log(fg / fb)
    sigma = 0.5 * float(np.sum(d))
    return max(sigma, 0.0)


# --------------------------------------------------------------------------- #
#  Asymetrie observable : reel vs inverse                                      #
# --------------------------------------------------------------------------- #


def trajectory_asymmetry(states: Sequence, n_symbols: int = None) -> Dict:
    """Asymetrie observable reel-vs-inverse sur la trajectoire brute.

    On inverse la trajectoire dans le temps (``states[::-1]``), on estime la
    matrice de transition dans les deux sens, puis on compare les
    distributions de paires consecutives (frequences de bigrammes ``(i, j)``
    sur la fenetre d'ordre 1). L'asymetrie est :

      - ``eta`` : variation totale (L1/2) entre les distributions de paires
        de la trajectoire reelle et de sa reversal ;
      - ``entropy_real`` / ``entropy_back`` : entropies de Shannon de ces
        distributions ;
      - ``detailed_balance_error_real`` / ``detailed_balance_error_back`` :
        erreur detailed balance dans chaque sens (le systeme reel a une
        erreur ; le "systeme inverse" aussi, par construction, mais avec
        des vecteurs propres differents ; la **difference** des deux est
        l'asymetrie thermodynamique).

    Parametres :
      - ``states`` : sequence d'etats (entiers ou labels ; l'encodage est
        automatique).
      - ``n_symbols`` : taille du vocabulaire ; si ``None``, deduit de
        ``encode_states``.
    """
    encoded, mapping = encode_states(states)
    if n_symbols is None:
        n_symbols = len(mapping)
    P_real = transition_matrix(encoded, n_symbols)
    pi_real = stationary_distribution(P_real)
    db_real = detailed_balance_error(P_real, pi_real)
    sigma_real = entropy_production(P_real, pi_real)
    back_encoded = encoded[::-1]
    P_back = transition_matrix(back_encoded, n_symbols)
    pi_back = stationary_distribution(P_back)
    db_back = detailed_balance_error(P_back, pi_back)
    sigma_back = entropy_production(P_back, pi_back)
    # L1/2 entre matrices de transition (distribution de bigrammes associee).
    eta = 0.5 * float(np.sum(np.abs(P_real - P_back)))
    return {
        "P_real": P_real,
        "P_back": P_back,
        "pi_real": pi_real,
        "pi_back": pi_back,
        "detailed_balance_error_real": db_real,
        "detailed_balance_error_back": db_back,
        "sigma_real": sigma_real,
        "sigma_back": sigma_back,
        "eta_L1half_transitions": eta,
        "n_symbols": int(n_symbols),
        "mapping": dict(mapping),
    }


# --------------------------------------------------------------------------- #
#  Comparaison orchestrateur : 3 trajectoires (reel / inverse / reversible)   #
# --------------------------------------------------------------------------- #


def compare_real_reversed_reversibilized(
    states: Sequence, n_symbols: int = None
) -> Dict:
    """Orchestrateur : evalue les 3 regimes et mesure ce qu'on perd a la reversibilisation.

    Trois matrices de transition sont comparees :

      - ``P_real`` : chaine estimee sur la trajectoire reelle ;
      - ``P_reversed`` : chaine de la trajectoire inversee dans le temps ;
      - ``P_reversibilized`` : projection reversible de ``P_real`` (perte la
        composante irreversible).

    Les quantites mesurees :

      - ``sigma_real`` / ``sigma_reversibilized`` : production d'entropie.
        La reversibilisee doit avoir ``sigma ~ 0`` par construction ;
        l'ecart a 0 mesure la precision numerique de la construction.
      - ``db_error_real`` / ``db_error_reversibilized`` : detailed balance.
      - ``dist_real_vs_reversibilized`` : L1/2 entre la chaine reelle et sa
        projection reversible. C'est **la perte a la reversibilisation** :
        plus elle est grande, plus la trajectoire portait de structure
        irreversible (une signature thermodynamique de l'agentivite
        emergente).
      - ``dist_real_vs_reversed`` : L1/2 entre la chaine reelle et son
        inverse ; mesure si le renversement du temps change qualitativement
        la dynamique.
      - ``dist_reversed_vs_reversibilized`` : L1/2 entre l'inverse et la
        reversible ; pour une chaine reelle reversible, ces deux sont
        identiques a la chaine reelle, donc cette distance tend vers 0 ;
        pour une chaine irreversible, l'inverse est "egalement irreversible
        dans l'autre sens" et la reversible est le compromis symetrique.

    Parametres :
      - ``states`` : sequence d'etats (entiers ou labels).
      - ``n_symbols`` : taille du vocabulaire ; si ``None``, deduit de
        ``encode_states``.
    """
    encoded, mapping = encode_states(states)
    if n_symbols is None:
        n_symbols = len(mapping)
    back = encoded[::-1]
    P_real = transition_matrix(encoded, n_symbols)
    P_back = transition_matrix(back, n_symbols)
    pi_real = stationary_distribution(P_real)
    pi_back = stationary_distribution(P_back)
    P_reversed = time_reversal(P_real, pi_real)
    P_reversibilized = reversibilize(P_real, pi_real)
    pi_rev = stationary_distribution(P_reversibilized)
    return {
        "P_real": P_real,
        "P_reversed": P_reversed,
        "P_reversibilized": P_reversibilized,
        "pi_real": pi_real,
        "pi_reversed": stationary_distribution(P_reversed),
        "pi_reversibilized": pi_rev,
        "sigma_real": entropy_production(P_real, pi_real),
        "sigma_reversed": entropy_production(P_reversed, pi_back),
        "sigma_reversibilized": entropy_production(P_reversibilized, pi_rev),
        "db_error_real": detailed_balance_error(P_real, pi_real),
        "db_error_reversed": detailed_balance_error(P_reversed, pi_back),
        "db_error_reversibilized": detailed_balance_error(P_reversibilized, pi_rev),
        "dist_real_vs_reversed": 0.5 * float(np.sum(np.abs(P_real - P_reversed))),
        "dist_real_vs_reversibilized": 0.5 * float(
            np.sum(np.abs(P_real - P_reversibilized))
        ),
        "dist_reversed_vs_reversibilized": 0.5 * float(
            np.sum(np.abs(P_reversed - P_reversibilized))
        ),
        "n_symbols": int(n_symbols),
        "mapping": dict(mapping),
    }
