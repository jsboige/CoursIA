# -*- coding: utf-8 -*-
"""Coeur du service TrueSkill (Probas/Infer.NET), pli 0 v2 de l'Epic #19571.

Logique reprise du jumeau ``Infer-08b-TrueSkill-Formules-Fermees-CSharp.ipynb``
(formes fermees EP de Herbrich-Minka-Graepel, NIPS 19 / 2006), adaptee au
contrat REST JSON du service notebook-http (issue #27217).

L'organe natif du calcul est la forme fermee EP : elle est implementee ici en
Python pur (``math.erf``), SANS reimplementation du moteur Infer.NET. La
bibliotheque publique ``trueskill`` (Heungsub Lee, reference communautaire)
n'est utilisee QUE par les tests, comme verification independante du cœur —
jamais appelee par ce module (regle organ-first : l'organe calcule, la
reference verifie).

Contrat REST (carnet phare ``Infer-08b-...-Python.ipynb``, cellule annotee) :
    POST /probas/trueskill
      {"games": [{"teams": [["A","B"],["C"]], "ranks": [1,2]}, ...],
       "initial": {"mu": 25.0, "sigma": 8.333}?,
       "beta": <float>?}
    -> {"status": "ok",     "data": {"players": {"A": {"mu":..,"sigma":..}, ...}}}
    -> {"status": "invalid","error": "<motif>"}   (entree incoherente)
    -> {"status": "error",  "error": "<motif>"}   (defaut interne)

Modele : apprentissage EN LIGNE (une passe sequentielle par partie, jamais
itere) — c'est la production TrueSkill. Pour chaque partie, les equipes sont
traitees par paires de rangs consecutifs ; une equipe est reduite a la SOMME
des competences de ses joueurs (mu = somme des mu, variance = somme des
variances + beta^2 par joueur pour le bruit de performance). La mise a jour
closed-form (V, W) est ensuite repartie a chaque joueur au prorata de sa
variance, exactement comme dans le jumeau C# (cellules 3, 6, 9).
"""
from __future__ import annotations

import math
from typing import Dict, List, Optional, Sequence, Tuple

# Parametres TrueSkill par defaut (identiques a Infer-08 / Infer-08b).
DEFAULT_MU = 25.0
DEFAULT_SIGMA = 25.0 / 3.0
# beta = ecart-type du bruit de performance ; sa variance vaut beta^2.
DEFAULT_BETA = (25.0 / 3.0) / 2.0


# --------------------------------------------------------------------------
# Formes fermees EP (Herbrich-Minka-Graepel, NIPS 19 / 2006)
# --------------------------------------------------------------------------

def _phi(t: float) -> float:
    """Densite de la Gaussienne centree reduite."""
    return math.exp(-0.5 * t * t) / math.sqrt(2.0 * math.pi)


def _Phi(t: float) -> float:
    """Fonction de repartition de la Gaussienne centree reduite."""
    return 0.5 * (1.0 + math.erf(t / math.sqrt(2.0)))


def V(t: float) -> float:
    """V(t) = phi(t) / Phi(t), fonction de troncature de Herbrich 2006."""
    return _phi(t) / _Phi(t)


def W(t: float) -> float:
    """W(t) = V(t) * (V(t) + t)."""
    v = V(t)
    return v * (v + t)


def match_update(
    winner: Tuple[float, float],
    loser: Tuple[float, float],
    beta2: float,
) -> Tuple[Tuple[float, float], Tuple[float, float]]:
    """Mise a jour EP closed-form d'un match (w bat l).

    Moment matching EXACT du marginal incline (identite du probit), comme
    ``WinnerUpdate`` du jumeau C# (cellule 9). Les entrees/sorties sont des
    couples ``(mu, variance)`` ; ``beta2`` est la variance de performance
    additionnelle portee par le facteur de comparaison (2*beta^2 pour un match
    1v1 ; pour une equipe, la somme des beta^2 des joueurs est deja dans la
    variance d'equipe, on ne rajoute donc ici que le bruit propre a la paire).

    Returns:
        ``(winner_apres, loser_apres)``, chacun ``(mu, variance)``.
    """
    mw, vw = winner
    ml, vl = loser
    c = math.sqrt(vw + vl + beta2)
    t = (mw - ml) / c
    vt, wt = V(t), W(t)
    mu_w = mw + vw / c * vt
    var_w = vw * (1.0 - vw / (c * c) * wt)
    mu_l = ml - vl / c * vt
    var_l = vl * (1.0 - vl / (c * c) * wt)
    return (mu_w, var_w), (mu_l, var_l)


# --------------------------------------------------------------------------
# Application d'une partie (equipes ordonnees par rang)
# --------------------------------------------------------------------------

def _ppf(p: float) -> float:
    """Quantile de la Gaussienne centree reduite (inverse de _Phi).

    Approximation rationnelle d'Acklam, suffisamment precise pour la marge de
    nul (portee de la reference trueskill.calc_draw_margin).
    """
    # Coefficients d'Acklam.
    a = [-3.969683028665376e+01, 2.209460984245205e+02, -2.759285104469687e+02,
         1.383577518672690e+02, -3.066479806614716e+01, 2.506628277459239e+00]
    b = [-5.447609879822406e+01, 1.615858368580409e+02, -1.556989798598866e+02,
         6.680131188771972e+01, -1.328068155288572e+01]
    c = [-7.784894002430293e-03, -3.223964580411365e-01, -2.400758277161838e+00,
         -2.549732539343734e+00, 4.374664141464968e+00, 2.938163982698783e+00]
    d = [7.784695709041462e-03, 3.224671290700398e-01, 2.445134137142996e+00,
         3.754408661907416e+00]
    plow, phigh = 0.02425, 1 - 0.02425
    if p < plow:
        q = math.sqrt(-2 * math.log(p))
        return (((((c[0]*q+c[1])*q+c[2])*q+c[3])*q+c[4])*q+c[5]) / \
               ((((d[0]*q+d[1])*q+d[2])*q+d[3])*q+1)
    if p > phigh:
        q = math.sqrt(-2 * math.log(1 - p))
        return -(((((c[0]*q+c[1])*q+c[2])*q+c[3])*q+c[4])*q+c[5]) / \
                ((((d[0]*q+d[1])*q+d[2])*q+d[3])*q+1)
    q = p - 0.5
    r = q * q
    return (((((a[0]*r+a[1])*r+a[2])*r+a[3])*r+a[4])*r+a[5])*q / \
           (((((b[0]*r+b[1])*r+b[2])*r+b[3])*r+b[4])*r+1)


def draw_margin(draw_probability: float, size: int, beta: float) -> float:
    """Marge de nul : quantile de la proba de nul, calibre sur beta*sqrt(size).

    Portee de trueskill.calc_draw_margin.
    """
    return _ppf((draw_probability + 1) / 2.0) * math.sqrt(size) * beta


def V_draw(diff: float, margin: float) -> float:
    """V du match nul, troncature bilaterale sur |d| < margin."""
    abs_diff = abs(diff)
    a = margin - abs_diff
    b = -margin - abs_diff
    denom = _Phi(a) - _Phi(b)
    numer = _phi(b) - _phi(a)
    v = (numer / denom) if denom else a
    return v * (-1.0 if diff < 0 else 1.0)


def W_draw(diff: float, margin: float) -> float:
    """W du match nul, troncature bilaterale sur |d| < margin."""
    abs_diff = abs(diff)
    a = margin - abs_diff
    b = -margin - abs_diff
    denom = _Phi(a) - _Phi(b)
    if not denom:
        return 0.0
    v = V_draw(diff, margin)
    return (v ** 2) + (a * _phi(a) - b * _phi(b)) / denom


def match_update_draw(
    a: Tuple[float, float],
    b: Tuple[float, float],
    beta2: float,
    margin: float,
) -> Tuple[Tuple[float, float], Tuple[float, float]]:
    """Mise a jour EP d'un match NUL : rapproche les deux joueurs.

    La troncature agit sur la bande |d| < margin ; le joueur le moins bon
    monte, le meilleur descend, et les deux variances baissent (production
    TrueSkill). ``margin`` est la marge de nul (draw_margin). Formules portees
    de trueskill.v_draw/w_draw appliquees a la difference normalisee.
    """
    ma, va = a
    mb, vb = b
    c = math.sqrt(va + vb + beta2)
    diff = (ma - mb) / c
    marge_norm = margin / c
    vd, wd = V_draw(diff, marge_norm), W_draw(diff, marge_norm)
    mu_a = ma + va / c * vd
    var_a = va * (1.0 - va / (c * c) * wd)
    mu_b = mb - vb / c * vd
    var_b = vb * (1.0 - vb / (c * c) * wd)
    return (mu_a, var_a), (mu_b, var_b)


class _Rating:
    """Etat (mu, variance) mutable d'un joueur pendant le deroule."""

    __slots__ = ("mu", "var")

    def __init__(self, mu: float, sigma: float) -> None:
        self.mu = mu
        self.var = sigma * sigma


def _propagate_pair(
    ratings: Dict[str, _Rating],
    equipe_w: Sequence[str],
    equipe_l: Sequence[str],
    beta2: float,
    nul: bool,
    margin: float = 0.0,
) -> None:
    """Propagation EP exacte d'une paire d'equipes.

    Formules portees du jumeau C# et de la reference ``trueskill`` :
      - equipe = somme des skills ; variance d'equipe = somme des variances,
        bruit de performance = beta^2 par joueur ;
      - la troncature agit sur la difference d'equipes (match_update, ou
        match_update_draw pour un nul avec ``margin`` = marge de nul) ;
      - la mise a jour est repartie a chaque joueur au prorata de sa variance
        de PERFORMANCE (var_j + beta^2), propagation cavity du SumFactor.
    """
    mu_w = sum(ratings[p].mu for p in equipe_w)
    mu_l = sum(ratings[p].mu for p in equipe_l)
    var_w = sum(ratings[p].var for p in equipe_w)
    var_l = sum(ratings[p].var for p in equipe_l)
    perf = beta2 * (len(equipe_w) + len(equipe_l))

    if nul:
        (nw_mu, nw_var), (nl_mu, nl_var) = match_update_draw(
            (mu_w, var_w), (mu_l, var_l), perf, margin
        )
    else:
        (nw_mu, nw_var), (nl_mu, nl_var) = match_update(
            (mu_w, var_w), (mu_l, var_l), perf
        )

    dmu_w, dvar_w = nw_mu - mu_w, nw_var - var_w
    dmu_l, dvar_l = nl_mu - mu_l, nl_var - var_l

    # Repartition de la mise a jour d'equipe a chaque joueur, au prorata de sa
    # variance de skill (forme fermee online du jumeau C#, WinnerUpdate /
    # production TrueSkill) :
    #   mu_j   += (var_j / var_equipe) * dmu_equipe
    #   var_j  += (var_j / var_equipe) * dvar_equipe
    # Exact en 1v1 (mu 29.21/20.79, sigma 7.1948 = posterior Infer-08) ; en
    # equipe, concorde en mu avec la reference EP iteree (27.97), la variance
    # individuelle etant plus reduite en une passe qu'a convergence (divergence
    # online vs EP iteree, documentee dans le carnet).
    def _equipe(equipe, var_e, dmu, dvar):
        for p in equipe:
            r = ratings[p]
            part = r.var / var_e if var_e > 0 else 1.0 / len(equipe)
            r.mu += part * dmu
            r.var = max(1e-9, r.var + part * dvar)

    _equipe(equipe_w, var_w, dmu_w, dvar_w)
    _equipe(equipe_l, var_l, dmu_l, dvar_l)


def _apply_game(
    ratings: Dict[str, _Rating],
    teams: Sequence[Sequence[str]],
    ranks: Sequence[int],
    beta: float,
    draw_probability: float = 0.0,
) -> None:
    """Applique une partie : paires de rangs consecutifs, propagation cavity.

    Deux equipes de meme rang font match nul : la paire est traitee par le
    facteur de nul (rapprochement des competences), avec la marge de nul
    deduite de ``draw_probability`` et du nombre de joueurs de la paire.
    """
    beta2 = beta * beta
    for i in range(len(teams) - 1):
        j = i + 1
        nul = ranks[i] == ranks[j]
        marge = 0.0
        if nul and draw_probability > 0.0:
            taille = len(teams[i]) + len(teams[j])
            marge = draw_margin(draw_probability, taille, beta)
        _propagate_pair(ratings, list(teams[i]), list(teams[j]), beta2, nul, marge)


# --------------------------------------------------------------------------
# Contrat REST
# --------------------------------------------------------------------------

def _validate_initial(initial: object) -> Optional[Tuple[float, float]]:
    """Valide le bloc ``initial`` optionnel. None si absent ou invalide.

    Renvoie ``(mu, sigma)`` si fourni et valide, ``(DEFAULT_MU, DEFAULT_SIGMA)``
    si absent, ou ``None`` si present mais incoherent (mu non reel, sigma<=0).
    Le sentinel ``"absent"`` distingue l'absence d'une erreur : on renvoie un
    tuple a 3 elements ``(mu, sigma, ok)``.
    """
    if initial is None:
        return (DEFAULT_MU, DEFAULT_SIGMA, True)  # type: ignore[return-value]
    if not isinstance(initial, dict):
        return None
    mu = initial.get("mu", DEFAULT_MU)
    sigma = initial.get("sigma", DEFAULT_SIGMA)
    try:
        mu_f = float(mu)
        sigma_f = float(sigma)
    except (TypeError, ValueError):
        return None
    if not (math.isfinite(mu_f) and math.isfinite(sigma_f)) or sigma_f <= 0:
        return None
    return (mu_f, sigma_f, True)  # type: ignore[return-value]


def solve_request(payload: object) -> dict:
    """Contrat REST : valide le corps JSON, deroule les parties, rend players.

    ``payload`` est le corps deja parse en dict (la cellule d'endpoint gere les
    differentes formes de REQUEST). Aucune exception ne fuit : tout chemin
    d'erreur retourne un statut ``invalid`` ou ``error`` avec son motif.
    """
    if not isinstance(payload, dict):
        return {"status": "invalid", "error": "corps JSON attendu (objet)"}

    games = payload.get("games")
    if not isinstance(games, list) or not games:
        return {"status": "invalid", "error": "champ 'games' : liste non vide requise"}

    init = _validate_initial(payload.get("initial"))
    if init is None:
        return {"status": "invalid", "error": "bloc 'initial' incoherent (mu reel, sigma>0)"}
    mu0, sigma0, _ = init  # type: ignore[misc]

    beta = payload.get("beta", DEFAULT_BETA)
    try:
        beta_f = float(beta)
    except (TypeError, ValueError):
        return {"status": "invalid", "error": "'beta' doit etre un reel"}
    if not math.isfinite(beta_f) or beta_f <= 0:
        return {"status": "invalid", "error": "'beta' doit etre un reel > 0"}

    dp = payload.get("draw_probability", 0.0)
    try:
        dp_f = float(dp)
    except (TypeError, ValueError):
        return {"status": "invalid", "error": "'draw_probability' doit etre un reel"}
    if not math.isfinite(dp_f) or not (0.0 <= dp_f < 1.0):
        return {"status": "invalid", "error": "'draw_probability' dans [0, 1["}

    ratings: Dict[str, _Rating] = {}

    def _rating_of(name: str) -> _Rating:
        if name not in ratings:
            ratings[name] = _Rating(mu0, sigma0)
        return ratings[name]

    try:
        for gi, game in enumerate(games):
            if not isinstance(game, dict):
                return {"status": "invalid", "error": f"partie {gi} : objet attendu"}
            teams = game.get("teams")
            ranks = game.get("ranks")
            if not isinstance(teams, list) or len(teams) < 2:
                return {"status": "invalid", "error": f"partie {gi} : 'teams' >= 2 equipes"}
            if not isinstance(ranks, list) or len(ranks) != len(teams):
                return {"status": "invalid", "error": f"partie {gi} : 'ranks' aligne sur 'teams'"}
            norm_teams: List[List[str]] = []
            norm_ranks: List[int] = []
            for ti, team in enumerate(teams):
                if not isinstance(team, list) or not team:
                    return {"status": "invalid", "error": f"partie {gi} equipe {ti} : liste non vide"}
                joueurs: List[str] = []
                for p in team:
                    if not isinstance(p, str) or not p:
                        return {"status": "invalid", "error": f"partie {gi} equipe {ti} : noms non vides"}
                    joueurs.append(p)
                    _rating_of(p)
                norm_teams.append(joueurs)
                rk = ranks[ti]
                if not isinstance(rk, int) or rk < 1:
                    return {"status": "invalid", "error": f"partie {gi} equipe {ti} : rang entier >= 1"}
                norm_ranks.append(rk)
            # Ordonner les equipes par rang croissant (meilleur d'abord).
            ordre = sorted(range(len(norm_teams)), key=lambda k: norm_ranks[k])
            teams_triees = [norm_teams[k] for k in ordre]
            ranks_tries = [norm_ranks[k] for k in ordre]
            _apply_game(ratings, teams_triees, ranks_tries, beta_f, dp_f)
    except Exception as exc:  # pragma: no cover - garde-fou contractuel
        return {"status": "error", "error": f"{type(exc).__name__}: {exc}"}

    players = {
        name: {"mu": round(r.mu, 4), "sigma": round(math.sqrt(r.var), 4)}
        for name, r in ratings.items()
    }
    return {"status": "ok", "data": {"players": players}}
