"""Diagnostic de signatures *scale-free* (sans echelle) et de criticalite.

Ce module outille le notebook **ICT-7** : il fournit de quoi (a) generer des
signatures de reference -- un vrai processus critique (branchement de
Galton-Watson) et des echantillons synthetiques loi-de-puissance / exponentiels
-- et (b) **diagnostiquer honnetement** si une distribution observee est
*scale-free* (loi de puissance, aucune echelle caracteristique) ou possede au
contraire une echelle caracteristique (coupure exponentielle).

Pourquoi un module dedie
-------------------------
Le piege central de la detection scale-free est qu'une foule de distributions a
queue lourde **paraissent droites** sur un trace log-log, sans etre des lois de
puissance. La lecon (Clauset, Shalizi & Newman, 2009) : ne jamais conclure sur
l'oeil. Il faut (1) estimer l'exposant par maximum de vraisemblance, (2) mesurer
l'ecart (distance de Kolmogorov-Smirnov), et (3) **comparer** la loi de puissance
a une alternative (exponentielle) par rapport de vraisemblance. C'est ce que ce
module rend reproductible.

Reference theorique exacte
--------------------------
La taille totale de la descendance d'un processus de Galton-Watson a progeniture
Poisson de moyenne mu = 1 (critique) suit la loi de Borel :
``P(s) = s^(s-1) e^(-s) / s!``, dont la queue est ``~ s^(-3/2)`` -- donc une loi
de puissance d'exposant tau = 3/2. C'est notre etalon : un systeme reellement
sans echelle, avec un exposant connu, sur lequel le diagnostic doit retomber.

Bibliotheque standard uniquement (``math``, ``random``), comme tout ``ict``.
"""

from __future__ import annotations

import math
import random
from typing import Optional


# --------------------------------------------------------------------------- #
# Generateurs de reference
# --------------------------------------------------------------------------- #
def _poisson(mu: float, rng: random.Random) -> int:
    """Tirage Poisson(mu) par l'algorithme de Knuth (stdlib, sans numpy)."""
    if mu <= 0.0:
        return 0
    target = math.exp(-mu)
    k, p = 0, 1.0
    while True:
        k += 1
        p *= rng.random()
        if p <= target:
            return k - 1


def branching_avalanche_size(mu: float, rng: random.Random, max_size: int = 100000) -> int:
    """Taille totale d'une avalanche : processus de Galton-Watson partant d'une
    graine, progeniture ~ Poisson(mu). Retourne le nombre total de noeuds.

    mu < 1 : sous-critique (avalanches courtes, echelle caracteristique).
    mu = 1 : critique (loi de puissance, aucune echelle).
    mu > 1 : sur-critique (avalanches geantes possibles).

    L'avalanche est plafonnee a ``max_size`` (on retourne ``max_size`` si la
    borne est atteinte -- a traiter comme "censuree" en aval)."""
    total = 1
    active = 1
    while active > 0:
        active -= 1
        children = _poisson(mu, rng)
        total += children
        active += children
        if total >= max_size:
            return max_size
    return total


def branching_avalanche_sizes(
    mu: float, n: int, rng: random.Random, max_size: int = 100000
) -> list:
    """Echantillon de ``n`` tailles d'avalanches (cf. branching_avalanche_size)."""
    return [branching_avalanche_size(mu, rng, max_size) for _ in range(n)]


def sample_powerlaw(alpha: float, xmin: float, n: int, rng: random.Random) -> list:
    """Echantillon loi de puissance continue d'exposant ``alpha`` (> 1) et de
    borne basse ``xmin``, par transformation inverse :
    ``x = xmin * (1 - u)^(-1/(alpha-1))``."""
    return [xmin * (1.0 - rng.random()) ** (-1.0 / (alpha - 1.0)) for _ in range(n)]


def sample_exponential(rate: float, xmin: float, n: int, rng: random.Random) -> list:
    """Echantillon exponentiel decale sur [xmin, +inf), de taux ``rate``."""
    return [xmin - math.log(1.0 - rng.random()) / rate for _ in range(n)]


# --------------------------------------------------------------------------- #
# Distribution empirique
# --------------------------------------------------------------------------- #
def ccdf(data: list) -> tuple:
    """Fonction de repartition complementaire empirique P(X >= x).

    Retourne (xs, ps) avec xs trie croissant (valeurs distinctes) et ps la
    proportion d'observations >= x. C'est la courbe a tracer en log-log : une
    vraie loi de puissance y est une droite."""
    if not data:
        return [], []
    s = sorted(data)
    n = len(s)
    xs, ps = [], []
    i = 0
    while i < n:
        x = s[i]
        # nombre d'observations strictement inferieures a x
        ps.append((n - i) / n)
        xs.append(x)
        while i < n and s[i] == x:
            i += 1
    return xs, ps


# --------------------------------------------------------------------------- #
# Estimateurs (maximum de vraisemblance) et comparaison de modeles
# --------------------------------------------------------------------------- #
def hill_alpha(data: list, xmin: float, discrete: bool = False) -> Optional[float]:
    """Exposant ``alpha`` d'une loi de puissance par maximum de vraisemblance
    (estimateur de Hill / MLE), sur la queue ``x >= xmin``.

    alpha = 1 + n / sum( ln( x / x0 ) ), avec x0 = xmin (cas continu) ou
    xmin - 0.5 (correction de continuite pour donnees entieres, ``discrete``)."""
    x0 = (xmin - 0.5) if discrete else xmin
    tail = [x for x in data if x >= xmin]
    if len(tail) < 2 or x0 <= 0:
        return None
    s = sum(math.log(x / x0) for x in tail)
    if s <= 0:
        return None
    return 1.0 + len(tail) / s


def _powerlaw_ccdf(x: float, xmin: float, alpha: float) -> float:
    """CCDF theorique d'une loi de puissance continue : (x / xmin)^-(alpha-1)."""
    return (x / xmin) ** (-(alpha - 1.0))


def ks_distance(data: list, xmin: float, alpha: float) -> Optional[float]:
    """Distance de Kolmogorov-Smirnov entre la CCDF empirique de la queue et la
    CCDF theorique de la loi de puissance ajustee. Petit = bon ajustement."""
    tail = sorted(x for x in data if x >= xmin)
    n = len(tail)
    if n < 2:
        return None
    d = 0.0
    for k, x in enumerate(tail):
        emp = (n - k) / n            # P(X >= x) empirique
        theo = _powerlaw_ccdf(x, xmin, alpha)
        d = max(d, abs(emp - theo))
    return d


def _loglik_powerlaw(tail: list, xmin: float, alpha: float) -> float:
    n = len(tail)
    return (
        n * math.log(alpha - 1.0)
        - n * math.log(xmin)
        - alpha * sum(math.log(x / xmin) for x in tail)
    )


def _loglik_exponential(tail: list, xmin: float, rate: float) -> float:
    n = len(tail)
    return n * math.log(rate) - rate * sum(x - xmin for x in tail)


def exponential_rate(data: list, xmin: float) -> Optional[float]:
    """Taux MLE d'une exponentielle decalee sur [xmin, +inf) : 1 / (moyenne - xmin)."""
    tail = [x for x in data if x >= xmin]
    if len(tail) < 2:
        return None
    mean = sum(tail) / len(tail)
    if mean <= xmin:
        return None
    return 1.0 / (mean - xmin)


def gof_pvalue(
    data: list,
    xmin: float,
    alpha: float,
    rng: random.Random,
    n_boot: int = 200,
    discrete: bool = False,
) -> Optional[float]:
    """p-valeur d'adequation (goodness-of-fit) de la loi de puissance ajustee,
    facon Clauset, Shalizi & Newman (version pedagogique simplifiee).

    On mesure la distance KS observee, puis on tire ``n_boot`` echantillons
    synthetiques *issus de la loi de puissance ajustee* (meme taille de queue),
    on re-ajuste alpha sur chacun et on mesure leur KS. La p-valeur est la
    fraction d'echantillons synthetiques dont le KS **egale ou depasse** le KS
    observe. p faible (< 0.1) => l'ecart observe serait atypique pour une vraie
    loi de puissance => on **rejette** la loi de puissance."""
    tail = [x for x in data if x >= xmin]
    n = len(tail)
    if n < 2:
        return None
    ks_obs = ks_distance(data, xmin, alpha)
    if ks_obs is None:
        return None
    worse = 0
    for _ in range(n_boot):
        synth = sample_powerlaw(alpha, xmin, n, rng)
        a_b = hill_alpha(synth, xmin, discrete=discrete)
        if a_b is None:
            continue
        ks_b = ks_distance(synth, xmin, a_b)
        if ks_b is not None and ks_b >= ks_obs:
            worse += 1
    return worse / n_boot


def select_xmin(
    data: list, candidates: Optional[list] = None, discrete: bool = False
) -> Optional[float]:
    """Choisit ``xmin`` a la facon de Clauset, Shalizi & Newman : la valeur qui
    **minimise la distance KS** entre la queue ``x >= xmin`` et sa loi de
    puissance ajustee. Selectionne le segment ou les donnees sont *le plus*
    compatibles avec une loi de puissance, sans le supposer a priori.

    Renvoie None si aucune queue exploitable. Par defaut, les candidats sont les
    valeurs distinctes observees (en excluant les plus grandes pour garder une
    queue d'au moins ~50 points)."""
    if not data:
        return None
    uniq = sorted(set(data))
    if candidates is None:
        candidates = [x for x in uniq if sum(1 for v in data if v >= x) >= 50]
    best_x, best_ks = None, float("inf")
    for xm in candidates:
        a = hill_alpha(data, xm, discrete=discrete)
        if a is None:
            continue
        ks = ks_distance(data, xm, a)
        if ks is not None and ks < best_ks:
            best_ks, best_x = ks, xm
    return best_x


def compare_powerlaw_exponential(
    data: list,
    xmin: float,
    discrete: bool = False,
    margin: float = 0.0,
    ks_max: float = 0.10,
    rng: Optional[random.Random] = None,
    gof_boot: int = 0,
) -> dict:
    """Confronte loi de puissance et exponentielle sur la queue ``x >= xmin``.

    Deux criteres, dans cet ordre -- car le second sans le premier *trompe* :

    1. **Adequation** (goodness-of-fit). Si la distance KS du meilleur ajustement
       loi-de-puissance depasse ``ks_max``, la loi de puissance **ne tient pas** :
       la queue est lourde mais ce n'est PAS une loi de puissance (echelle
       caracteristique, coupure, ou borne finie). C'est le garde-fou contre le
       piege du log-log "droit a l'oeil".
    2. **Comparaison de modeles**. Si l'ajustement tient (KS faible), le rapport
       de log-vraisemblance ``R = ll_powerlaw - ll_exp`` confronte la loi de
       puissance a l'exponentielle : R > marge => *scale-free* ; R < -marge =>
       exponentielle.

    Indices complementaires renvoyes : ``alpha`` (exposant, ~stable a travers
    les xmin si vraie loi de puissance), ``ks``, ``loglik_ratio`` et, si ``rng``
    et ``gof_boot>0`` sont fournis, une ``gof_pvalue`` de bootstrap (a manier
    avec prudence : pour de grands echantillons elle rejette presque tout, y
    compris de vraies lois de puissance imparfaites -- une limite a enseigner,
    pas un verdict binaire).

    Avertissement honnete : aucun test ne *prouve* une loi de puissance ; on ne
    fait que rejeter des alternatives et verifier l'adequation."""
    tail = [x for x in data if x >= xmin]
    alpha = hill_alpha(data, xmin, discrete=discrete)
    rate = exponential_rate(data, xmin)
    out = {
        "n_tail": len(tail),
        "xmin": xmin,
        "alpha": alpha,
        "rate": rate,
        "ks": None,
        "loglik_ratio": None,
        "gof_pvalue": None,
        "verdict": "indecidable (queue trop courte)",
    }
    if alpha is None or rate is None:
        return out
    out["ks"] = ks_distance(data, xmin, alpha)
    r = _loglik_powerlaw(tail, xmin, alpha) - _loglik_exponential(tail, xmin, rate)
    out["loglik_ratio"] = r
    if rng is not None and gof_boot > 0:
        out["gof_pvalue"] = gof_pvalue(data, xmin, alpha, rng, n_boot=gof_boot, discrete=discrete)
    # 1. garde-fou d'adequation (KS) -- rejette le faux scale-free a l'oeil
    if out["ks"] is not None and out["ks"] > ks_max:
        out["verdict"] = "echelle caracteristique (ajustement loi de puissance insuffisant)"
        return out
    # 2. comparaison de modeles
    if r > margin:
        out["verdict"] = "scale-free (loi de puissance, ajustement correct)"
    elif r < -margin:
        out["verdict"] = "echelle caracteristique (exponentielle preferee)"
    else:
        out["verdict"] = "indecidable"
    return out


# --------------------------------------------------------------------------- #
# Auto-similarite / effondrement d'echelle (le cote "fractal")
# --------------------------------------------------------------------------- #
def rescaled_ccdf(data: list, scale: float) -> tuple:
    """CCDF avec l'axe des x divise par ``scale`` (x -> x / scale).

    Une signature scale-free est *auto-similaire* : les CCDF de sous-echantillons
    de tailles differentes se superposent une fois l'axe x renormalise par
    l'echelle propre de chaque sous-echantillon (effondrement d'echelle). Une
    distribution a echelle caracteristique ne se superpose pas."""
    xs, ps = ccdf(data)
    return [x / scale for x in xs], ps
