"""Morphodynamique strategique d'Axelrod (notebook ICT-13).

Une **strategie** est-elle une **forme stable** dans un paysage d'interactions ?
La bistabilite d'ICT-10 devient ici bistabilite de regime **cooperation /
defection**. On simule le dilemme du prisonnier itere (IPD) avec bruit
d'implementation, des tournois round-robin, la dynamique de replicateur, et l'on
cartographie les **bassins d'invasion**.

La theorie (grim trigger, seuil $\\delta \\ge (T-R)/(T-P)$, Folk theorem) est
traitee **par renvoi** a GameTheory-6c (merge `182bf33cc`) et, quand il sera
livre, au lake formel `repeated_games_lean` (#4880). Ce module ne re-derive pas
la theorie des jeux repetes : il **verifie numeriquement** ses previsions et
cartographie la morphologie des regimes.

Discipline « sans complaisance » (gate 5) : les strategies annoncees robustes
qui ne le sont pas dans un regime (bruit d'implementation) le montrent en sortie
commitee. numpy CPU pur, gel GPU respecte.
"""

from __future__ import annotations

from typing import Callable, Dict, List, Optional, Tuple

import numpy as np

# --------------------------------------------------------------------------- #
#  Dilemme du prisonnier : gains canoniques d'Axelrod                          #
# --------------------------------------------------------------------------- #
# T (Temptation) > R (Reward) > P (Punishment) > S (Sucker), et 2R > T+S.
CANON = {"T": 5.0, "R": 3.0, "P": 1.0, "S": 0.0}

# Coups : C = cooperer (0), D = defecter (1)
C, D = 0, 1


def payoff_pair(a: int, b: int, T=None, R=None, P=None, S=None) -> Tuple[float, float]:
    """Gain (a, b) pour le couple de coups (a, b). ``a`` joue en ligne, ``b`` en
    colonne. ``a=C, b=C`` -> (R, R) ; ``a=D, b=C`` -> (T, S) ; etc."""
    g = {"T": T or CANON["T"], "R": R or CANON["R"], "P": P or CANON["P"], "S": S or CANON["S"]}
    table = {(C, C): (g["R"], g["R"]), (C, D): (g["S"], g["T"]),
             (D, C): (g["T"], g["S"]), (D, D): (g["P"], g["P"])}
    return table[(int(a), int(b))]


# --------------------------------------------------------------------------- #
#  Strategies (histoires -> coup)                                              #
# --------------------------------------------------------------------------- #
# Une strategie est une fonction (own_hist, opp_hist) -> coup dans {C, D}.
Strategy = Callable[[np.ndarray, np.ndarray], int]


def allc(own: np.ndarray, opp: np.ndarray) -> int:
    """AllC : coopere toujours."""
    return C


def alld(own: np.ndarray, opp: np.ndarray) -> int:
    """AllD : defocte toujours."""
    return D


def tft(own: np.ndarray, opp: np.ndarray) -> int:
    """Tit-for-Tat : coopere au premier coup, puis imite le dernier coup de
    l'adversaire. Coordinateur d'Axelrod 1980, mais fragile au bruit
    (deux TFT se font echo de defection = mort-a-mort)."""
    return C if len(opp) == 0 else int(opp[-1])


def gtft(p: float = 1 / 3):
    """Generous Tit-for-Tat : comme TFT mais **pardonne** une defection adverse
    avec probabilite ``p`` (recoopere meme si l'adversaire a defocte). Resiste au
    bruit la ou TFT s'effondre (Nowak & Sigmund 1992)."""

    def _gtft(own: np.ndarray, opp: np.ndarray, _p: float = p, _st=None) -> int:
        if len(opp) == 0:
            return C
        if opp[-1] == C:
            return C
        # adversaire a defocte : cooperer avec prob p, sinon punir
        return C if _st.random() < _p else D

    return _gtft


def pavlov(own: np.ndarray, opp: np.ndarray) -> int:
    """Pavlov (Win-Stay Lose-Shift) : conserve son coup si le gain precedent etait
    eleve (R ou T), change sinon (S ou P). Resiste au bruit et envahit TFT dans
    une population bruitee (Nowak & Sigmund 1993)."""
    if len(own) == 0:
        return C
    last = int(own[-1])
    opp_last = int(opp[-1])
    pa, _ = payoff_pair(last, opp_last)
    # « gagne » = R (muetuel) ou T (exploitation) ; « perd » = S ou P
    won = pa >= CANON["R"]
    return last if won else (1 - last)  # stay si gagne, shift sinon


def grim(own: np.ndarray, opp: np.ndarray) -> int:
    """Grim Trigger (Rancunier) : coopere jusqu'a la premiere defection adverse,
    puis defocte a jamais. Strategie de seuil du Folk theorem (cf. GT-6c) :
    soutient la cooperation a l'equilibre si $\\delta \\ge (T-R)/(T-P)$."""
    return D if (len(opp) > 0 and D in opp) else C


def random_strategy(p_coop: float = 0.5):
    """Strategie aleatoire : coopere avec probabilite ``p_coop``."""

    def _rand(own: np.ndarray, opp: np.ndarray, _p: float = p_coop, _st=None) -> int:
        return C if _st.random() < _p else D

    return _rand


# Une strategie a etat (gtft, random) a besoin d'un generateur par match ;
# on les construit via une factory qui injecte le rng.
STRATEGY_NAMES = ["allc", "alld", "tft", "gtft", "pavlov", "grim"]


def make_strategies(rng: Optional[np.random.Generator] = None) -> Dict[str, Strategy]:
    """Construit le dictionnaire des strategies. Celles aleatoires (gtft, random)
    partagent le ``rng`` fourni (reproductible)."""
    st = {"rng": rng or np.random.default_rng(0)}

    def _gtft(own, opp):
        if len(opp) == 0:
            return C
        if opp[-1] == C:
            return C
        return C if st["rng"].random() < 1 / 3 else D

    return {
        "allc": allc,
        "alld": alld,
        "tft": tft,
        "gtft": _gtft,
        "pavlov": pavlov,
        "grim": grim,
    }


# --------------------------------------------------------------------------- #
#  Match IPD avec bruit d'implementation                                       #
# --------------------------------------------------------------------------- #

def play_match(
    s1: Strategy,
    s2: Strategy,
    n_rounds: int = 200,
    noise: float = 0.0,
    rng: Optional[np.random.Generator] = None,
    T=None, R=None, P=None, S=None,
) -> Tuple[float, float]:
    """Joue un match IPD de ``n_rounds`` coups entre ``s1`` et ``s2``. ``noise``
    est la probabilite que le coup **intentionnel** soit inverse (bruit
    d'implementation : erreur, tremblement). Renvoie le gain moyen par coup de
    chacun (gain cumul / n_rounds).

    Le bruit n'est pas cosmetique : il discrimine TFT (effondrement par echo) de
    GTFT/Pavlov (résistent) — c'est le gate 3 du regime-dependance."""
    if rng is None:
        rng = np.random.default_rng(0)
    own1, own2 = [], []
    g1 = g2 = 0.0
    for _ in range(n_rounds):
        a = int(s1(np.array(own1), np.array(own2)))
        b = int(s2(np.array(own2), np.array(own1)))
        if noise > 0.0:
            if rng.random() < noise:
                a = 1 - a
            if rng.random() < noise:
                b = 1 - b
        pa, pb = payoff_pair(a, b, T=T, R=R, P=P, S=S)
        g1 += pa
        g2 += pb
        own1.append(a)
        own2.append(b)
    return g1 / n_rounds, g2 / n_rounds


# --------------------------------------------------------------------------- #
#  Tournoi round-robin (gate 1)                                                #
# --------------------------------------------------------------------------- #

def round_robin(
    strategies: Dict[str, Strategy],
    n_rounds: int = 200,
    noise: float = 0.0,
    n_reps: int = 1,
    rng: Optional[np.random.Generator] = None,
) -> Dict[str, float]:
    """Tournoi round-robin : chaque paire (i, j) (y compris i==j) joue ``n_reps``
    matchs de ``n_rounds`` coups. Renvoie le score moyen par coup de chaque
    strategie (moyenne sur tous ses matchs ponderee equitablement).

    Les outputs sont SIMULES, jamais recopies d'un tableau d'Axelrod (gate 1)."""
    if rng is None:
        rng = np.random.default_rng(0)
    names = list(strategies.keys())
    totals = {n: [] for n in names}
    for i, ni in enumerate(names):
        for j, nj in enumerate(names):
            for _ in range(n_reps):
                # reconstruire l'etat interne aleatoire a chaque match (gtft/random)
                s_i = strategies[ni]
                s_j = strategies[nj]
                g_i, g_j = play_match(s_i, s_j, n_rounds=n_rounds, noise=noise, rng=rng)
                totals[ni].append(g_i)
                if i != j:
                    totals[nj].append(g_j)
    return {n: float(np.mean(totals[n])) for n in names}


def payoff_matrix(
    strategies: Dict[str, Strategy],
    n_rounds: int = 200,
    noise: float = 0.0,
    n_reps: int = 3,
    rng: Optional[np.random.Generator] = None,
) -> np.ndarray:
    """Matrice de gain A[i,j] = score moyen de la strategie i face a j (n_reps
    matchs). Sert de noyau a la dynamique de replicateur (fitness_i = A x)."""
    if rng is None:
        rng = np.random.default_rng(0)
    names = list(strategies.keys())
    n = len(names)
    A = np.zeros((n, n))
    for i, ni in enumerate(names):
        for j, nj in enumerate(names):
            scores = []
            for _ in range(n_reps):
                gi, _ = play_match(strategies[ni], strategies[nj], n_rounds=n_rounds,
                                   noise=noise, rng=rng)
                scores.append(gi)
            A[i, j] = float(np.mean(scores))
    return A


# --------------------------------------------------------------------------- #
#  Dynamique de replicateur discrete                                            #
# --------------------------------------------------------------------------- #

def replicator_trajectory(
    A: np.ndarray,
    x0: np.ndarray,
    n_steps: int = 1000,
) -> np.ndarray:
    """Trajectoire de la dynamique de replicateur discrete :

        x_i(t+1) = x_i(t) * f_i(t) / <f>(t),   f_i = (A x)_i.

    ``x0`` = vecteur de fréquences (somme 1) sur les strategies. Renvoie la
    trajectoire ``(n_steps+1, n_strategies)``. Les strategies sous-performantes
    decroissent, les performantes envahissent ; les points fixes sont les ESS."""
    x = np.asarray(x0, dtype=float).copy()
    x = x / x.sum()
    traj = np.empty((n_steps + 1, x.size))
    traj[0] = x
    for t in range(n_steps):
        f = A @ x  # fitness de chaque strategie
        avg = float(np.dot(f, x))
        if avg < 1e-12:
            break
        x = x * f / avg
        x = np.clip(x, 0.0, None)
        s = x.sum()
        if s > 1e-12:
            x = x / s
        traj[t + 1] = x
    return traj


def fixation(traj: np.ndarray, tol: float = 1e-3) -> np.ndarray:
    """Vecteur de frequence final de la trajectoire (derniere ligne). Une
    strategie a « envahi » si sa frequence finale > 1 - tol."""
    return traj[-1]


# --------------------------------------------------------------------------- #
#  Gate 2 : seuil de grim trigger vs prediction analytique                     #
# --------------------------------------------------------------------------- #

def grim_threshold(T=None, R=None, P=None) -> float:
    """Seuil analytique $\\delta^* = (T-R)/(T-P)$ au-dela duquel grim trigger
    resiste a l'invasion d'AllD dans le PD repete avec continuation $\\delta$
    (Folk theorem, cf. GT-6c). Pour les gains canoniques T=5,R=3,P=1 : 0.5."""
    t = T or CANON["T"]; r = R or CANON["R"]; p = P or CANON["P"]
    return (t - r) / (t - p)


def grim_continuation_payoff(delta: float, n_rounds: int = 500,
                              T=None, R=None, P=None, S=None,
                              rng: Optional[np.random.Generator] = None) -> Tuple[float, float]:
    """Gain **escompte total** de grim (vs grim) et d'AllD (vs grim) dans le PD
    repete, avec facteur d'escompte ``delta`` : $G = \\sum_{t \\ge 0} \\delta^t g_t$.

    Fidele au Folk theorem (cf. GT-6c) : grim resiste a l'invasion d'AllD si son
    gain escompte $R/(1-\\delta)$ bat celui d'AllD $T + \\delta P/(1-\\delta)$,
    i.e. $\\delta \\ge (T-R)/(T-P)$. grim et AllD sont **deterministes** : pas de
    RNG, la somme escomptee converge vers la prediction analytique. Renvoie
    (G_grim, G_alld). Compare a :func:`grim_threshold` (gate 2)."""
    g_grim = _grim_discounted(delta, n_rounds, opponent="grim", invader="grim",
                              T=T, R=R, P=P, S=S)
    g_alld = _grim_discounted(delta, n_rounds, opponent="grim", invader="alld",
                              T=T, R=R, P=P, S=S)
    return g_grim, g_alld


def _grim_discounted(delta: float, max_rounds: int, opponent: str = "grim",
                     invader: str = "grim", T=None, R=None, P=None, S=None) -> float:
    """Gain escompte total d'un envahisseur face a un resident grim, sur un
    horizon de ``max_rounds`` coups (converge vers la somme infinie pour un
    horizon assez long). Deterministe (grim/AllD ne tirent pas au hasard)."""
    strat = make_strategies()
    own_i, own_g = [], []
    total = 0.0
    pow_d = 1.0
    for _ in range(max_rounds):
        a = int(strat[invader](np.array(own_i), np.array(own_g)))
        b = int(strat[opponent](np.array(own_g), np.array(own_i)))
        pa, _ = payoff_pair(a, b, T=T, R=R, P=P, S=S)
        total += pow_d * pa
        pow_d *= float(delta)
        own_i.append(a)
        own_g.append(b)
        if pow_d < 1e-9:  # convergence atteinte
            break
    return total


def grim_resists_threshold(delta_grid: np.ndarray,
                            rng: Optional[np.random.Generator] = None,
                            T=None, R=None, P=None, S=None,
                            ) -> Tuple[np.ndarray, np.ndarray, float]:
    """Pour chaque ``delta`` de la grille, calcule la difference de score
    (grim_vs_grim - alld_vs_grim) et localise le croisement numerique (binary
    search sur la grille). Renvoie (deltas, diffs, delta_crossing). Doit
    s'accorder avec :func:`grim_threshold` (gate 2)."""
    if rng is None:
        rng = np.random.default_rng(0)
    diffs = np.empty_like(delta_grid, dtype=float)
    for k, d in enumerate(delta_grid):
        gg, ga = grim_continuation_payoff(float(d), rng=rng, T=T, R=R, P=P, S=S)
        diffs[k] = gg - ga
    # croisement : premier delta ou diff >= 0 (grim resiste)
    crossing = float(delta_grid[np.argmax(diffs >= 0)]) if np.any(diffs >= 0) else float("nan")
    return delta_grid, diffs, crossing


# --------------------------------------------------------------------------- #
#  Gate 4 : bassins d'invasion (fraction initiale critique)                    #
# --------------------------------------------------------------------------- #

def invasion_basin(
    A: np.ndarray,
    invader_idx: int,
    resident_idx: int,
    n_points: int = 51,
    n_steps: int = 600,
) -> Tuple[np.ndarray, np.ndarray]:
    """Cartographie du bassin d'invasion : pour chaque fraction initiale ``x0``
    de l'envahisseur (le reste au resident), simule la replicateur et note la
    frequence finale de l'envahisseur. Renvoie (fractions_initiales, frequences_finales).

    La **fraction initiale critique** est le seuil au-dela duquel l'envahisseur
    envahit (frequence finale > 0.5) — c'est la mesure morphodynamique centrale
    du gate 4 : une forme stable a un bassin large (seuil eleve)."""
    x0s = np.linspace(0.0, 1.0, n_points)
    finals = np.empty_like(x0s)
    n = A.shape[0]
    for k, x0 in enumerate(x0s):
        x = np.zeros(n)
        x[invader_idx] = x0
        x[resident_idx] = 1.0 - x0
        traj = replicator_trajectory(A, x, n_steps=n_steps)
        finals[k] = traj[-1, invader_idx]
    return x0s, finals


def critical_fraction(x0s: np.ndarray, finals: np.ndarray, tol: float = 0.5) -> Optional[float]:
    """Fraction initiale critique : plus petit ``x0`` tel que l'envahisseur
    atteigne une frequence finale >= ``tol`` (0.5 = envahit). ``None`` s'il
    n'envahit jamais."""
    mask = finals >= tol
    return float(x0s[np.argmax(mask)]) if np.any(mask) else None


# --------------------------------------------------------------------------- #
#  Gate 3 : effondrement sous bruit (regime-dependance)                        #
# --------------------------------------------------------------------------- #

def noise_collapse(
    strategies: Dict[str, Strategy],
    noise_grid: np.ndarray,
    n_rounds: int = 200,
    n_reps: int = 3,
    rng: Optional[np.random.Generator] = None,
) -> Dict[str, np.ndarray]:
    """Score de tournoi de chaque strategie en fonction du bruit d'implementation.
    Doit reveler (gate 3) que **TFT s'effondre** (echo de defection mort-a-mort)
    tandis que **GTFT et Pavlov resistent** — prolonge le fil regime-dependance
    10.1/12. Renvoie {strategie: scores_par_bruit}."""
    if rng is None:
        rng = np.random.default_rng(0)
    out: Dict[str, np.ndarray] = {n: np.empty_like(noise_grid) for n in strategies}
    for k, noise in enumerate(noise_grid):
        scores = round_robin(strategies, n_rounds=n_rounds, noise=float(noise),
                             n_reps=n_reps, rng=rng)
        for n in strategies:
            out[n][k] = scores[n]
    return out
