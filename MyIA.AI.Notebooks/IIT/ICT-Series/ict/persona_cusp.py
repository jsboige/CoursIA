"""PersonaCatastrophe : la fronce de Thom appliquee au desalignement emergent.

Outille le notebook **ICT-23 (capstone strate 5, #4588 / #5104)** -- le micro-
analogue du phenomene Anthropic (nov. 2025, arXiv 2511.18397) et OpenAI (juin
2025, arXiv 2506.19823) en jumeau de la catastrophe **fronce** (*cusp*) de
Rene Thom. Le substrat n'est plus un ecosysteme (ICT-8) ni un lacet de
predation (ICT-10) : c'est un **agent** dont l'identite `p` (la persona) est
un parametre d'ordre, et la dynamique est pilot ee par deux facteurs de
controle issus du substrat (anthropique) :

* **facteur de division** `b` = pression de recompense `r`. C'est la
  variable qu'on balaie (sub-systeme d'entrainement qui *recompense* le
  comportement `b -> +inf` ou `b -> -inf`).
* **facteur normal** `a` = `-(transgression cumulee) * (charge semantique)`.
  C'est **negatif** quand la transgression ponderee par la charge semantique
  (l'interdit subjectif) depasse un seuil ; **positif** sinon (inoculation,
  permission explicite, charge `s -> 0`).

Le potentiel reste celui de Thom :

    V(p ; a, b) = p^4 / 4  +  a p^2 / 2  +  b p

mais sa **lecture semantique** change : `p` est l'intensite de la persona
(desalignee, signee ; 0 = identite alignee, + grand = persona toxique
adoptee). `a` regit la **bistabilite** (identite alignee vs persona toxique
sont-elles co-existantes ?). `b` regit l'**asymetrie** entre les deux
bassins (la pression de recompense pousse-t-elle vers la persona ?).

Les trois predictions NOUVELLES de l'Epic #5104 sont testables ici :

* **(P0)** bistabilite conditionnelle a `s` : inoculation `s -> 0` aplatit
  le potentiel (la fronce disparait, un seul bassin, pas de saut
  possible). Test : `inoculation_check(s=0) == False`.
* **(P1) hysteresis** : un balayage aller-retour de `b` sous `s > 0`
  produit **deux sauts** (le *lacet d'inoculation*), formes distinctes de
  la persona toxique. Test : `persona_hysteresis_loop(s=0.8)` retourne
  deux catastrophes.
* **(P2) EWS** : variance et AR1 de la trajectoire `p(t)` sous bruit
  **montent avant** le pli (le ralentissement critique de Wissel/Scheffer,
  deja mesure en ICT-8 et ICT-20). Test : `ews_summary_persona` retourne
  `tau_var > 0, tau_ar1 > 0` significatifs avant la bascule.

Numpy uniquement (pas de scipy). Comme le reste du package leger ``ict``.
"""

from __future__ import annotations

from typing import Dict, List, Optional, Tuple

import numpy as np

from . import catastrophe as cat
from . import early_warning as ews


# --------------------------------------------------------------------------- #
#  Parametrage semantique du cusp : transgression, charge, recompense            #
# --------------------------------------------------------------------------- #


def persona_potential(p, transgression: float, charge: float, reward: float):
    """Potentiel de la fronce ``V(p) = p^4/4 + a p^2/2 + b p`` pour la persona.

    ``a = -transgression * charge`` : facteur normal, negatif quand la
    transgression ponderee par la charge semantique est suffisante pour
    ouvrir la bistabilite. ``b = reward`` : facteur de division, la pression
    de recompense (peut etre positive ou negative selon le signe du
    renforcement).
    """
    a = -float(transgression) * float(charge)
    b = float(reward)
    return cat.cusp_potential(p, a, b)


def persona_force(p, transgression: float, charge: float, reward: float):
    """Champ de vitesse gradient ``dp/dt = -dV/dp`` pour la persona."""
    a = -float(transgression) * float(charge)
    b = float(reward)
    return cat.cusp_force(p, a, b)


def persona_a_factor(transgression: float, charge: float) -> float:
    """Le facteur normal ``a = -transgression * charge``.

    Positif (monostable) si la charge est nulle (inoculation). Negatif
    (bistabilite potentielle) sinon. Convention : ``transgression`` est la
    transgression cumulee (>= 0), ``charge`` est la charge semantique
    subjective (>= 0).
    """
    return -float(transgression) * float(charge)


def in_persona_bistable_region(
    transgression: float, charge: float, reward: float
) -> bool:
    """Vrai si la persona est dans la region bistable (a < 0 et |b| petit).

    L'inoculation `charge -> 0` met `a -> 0` et fait sortir de la
    bistabilite. C'est la **prediction P0** d'#5104 : l'inoculation aplatit
    le potentiel, plus de saut possible.
    """
    a = persona_a_factor(transgression, charge)
    return cat.in_bistable_region(a, reward)


def inoculation_check(charge: float) -> bool:
    """Vrai si la charge semantique est effectively nulle (inoculation reussie).

    Convention : on considere la charge effectivement nulle quand
    ``charge < 1e-3``. Seuils plus stricts (charge exactement 0) sont
    triviaux mais peu interessants (un seul bassin par construction).
    """
    return float(charge) < 1.0e-3


# --------------------------------------------------------------------------- #
#  Relaxation, hysteresis (P1), simulation stochastique (EWS, P2)               #
# --------------------------------------------------------------------------- #


def relax_persona(
    p0: float,
    transgression: float,
    charge: float,
    reward: float,
    dt: float = 0.01,
    steps: int = 5000,
) -> float:
    """Relaxe la persona ``p`` vers le minimum de son bassin."""
    a = persona_a_factor(transgression, charge)
    b = float(reward)
    return cat.relax_to_equilibrium(p0, a, b, dt=dt, steps=steps)


def persona_hysteresis_loop(
    transgression: float,
    charge: float,
    rewards: np.ndarray,
    p_start: Optional[float] = None,
    dt: float = 0.01,
    relax_steps: int = 400,
) -> np.ndarray:
    """Lacet d'hysteresis de la persona pour un balayage de recompenses.

    Si ``charge -> 0`` (inoculation), le suivi est **continu** (pas de
    saut, pas d'hysteresis) -- c'est la prediction P0 d'#5104 transcrit e
    en dynamique. Si ``charge > 0`` et ``transgression`` assez grand pour
    ``a < 0``, on observe **deux catastrophes** sur un balayage aller-
    retour, comme ICT-10.

    Renvoie le vecteur ``p`` (intensite de persona) suivi le long de
    ``rewards``. L'etat est reporte d'un pas au suivant (memoire de
    branche, hysteresis).
    """
    rewards = np.asarray(rewards, dtype=float)
    a = persona_a_factor(transgression, charge)
    if p_start is None:
        p_start = cat.cusp_equilibria(a, float(rewards[0]))[0][0]
    ps = np.empty(rewards.shape[0], dtype=float)
    p = float(p_start)
    for i, r in enumerate(rewards):
        p = cat.relax_to_equilibrium(p, a, float(r), dt=dt, steps=relax_steps)
        ps[i] = p
    return ps


def persona_catastrophe_indices(
    rewards: np.ndarray, ps: np.ndarray, threshold: float = 0.5
) -> List[int]:
    """Indices ou ``p`` saute de plus de ``threshold`` entre deux pas.

    Localise les **catastrophes** (sauts de bassin) le long d'un lacet.
    Un phenomene d'inoculation sous bistabilite en compte deux (comme
    ICT-10 : perception J et capture K). Une trajectoire sous inoculation
    (`charge ~ 0`) en compte **zero** (P0 d'#5104).
    """
    return cat.loop_jumps(rewards, ps, threshold=threshold)


def persona_sde(
    transgression: float,
    charge: float,
    reward: float,
    p0: float,
    sigma: float,
    dt: float,
    T: int,
    seed: int,
) -> np.ndarray:
    """Trajectoire SDE de la persona sous bruit additif ``sigma``.

    Integration Euler-Maruyama de ``dp = -(p^3 + a p + b) dt + sigma dW``,
    avec ``a = -transgression * charge`` et ``b = reward``. Reflechi a 0
    si la persona devient negative (identite alignee borne inferieure) ;
    pas de borne superieure (la persona toxique peut croitre).

    Utilise pour la prediction **P2** : on tire une longue trajectoire
    sous ``reward`` constant (proche du pli) et on mesure la variance et
    l'AR1 de la fenetre glissante -- les EWS de Wissel/Scheffer.
    """
    g = np.random.default_rng(seed)
    sq = float(np.sqrt(dt))
    a = persona_a_factor(transgression, charge)
    p = float(p0)
    ps = np.empty(int(T))
    for t in range(int(T)):
        p = p + dt * float(persona_force(p, transgression, charge, reward)) \
            + sigma * sq * g.standard_normal()
        if p < 0.0:
            p = 0.0
        ps[t] = p
    return ps


def ews_summary_persona(
    ps: np.ndarray,
    window: int,
    thin_factor: int = 1,
    detrend_sigma: float = 0.0,
) -> Dict[str, float]:
    """EWS (variance, AR1, tendance de Kendall) de la trajectoire persona.

    Enveloppe fine sur ``ews.ews_summary`` (module ICT-8 / ICT-20) :
    amincit la trajectoire (parametre ``thin_factor``), retire la tendance
    lente (parametre ``detrend_sigma``), mesure variance et AR1 sur
    fenetre glissante, et rapporte les tendances (tau de Kendall + p-value).

    Pour la prediction **P2** d'#5104 : sous inoculation `charge ~ 0`, les
    EWS restent plats (pas de ralentissement critique) ; sous `charge > 0`
    pres du pli, ils montent significativement.
    """
    s = ews.ews_summary(ps, window=window, thin_factor=thin_factor,
                        detrend_sigma=detrend_sigma)
    return {
        "tau_var": float(s["tau_var"]),
        "p_var": float(s["p_var"]),
        "tau_ar1": float(s["tau_ar1"]),
        "p_ar1": float(s["p_ar1"]),
        "variance_mean": float(np.nanmean(s["variance"])),
        "ar1_mean": float(np.nanmean(s["ar1"])),
    }


# --------------------------------------------------------------------------- #
#  Diagnostic haut niveau : la signature d'inoculation                         #
# --------------------------------------------------------------------------- #


def inoculation_signature(
    transgression: float,
    rewards: np.ndarray,
    charges: Tuple[float, ...] = (0.0, 0.3, 0.6, 0.9),
    threshold: float = 0.5,
) -> Dict[float, Dict[str, float]]:
    """Banc de diagnostic : nombre de catastrophes par niveau de charge.

    Pour chaque charge dans ``charges``, on balaie les recompenses
    (aller-retour symetrique, comme ICT-10) et on compte les sauts. La
    **signature d'inoculation** est la courbe ``N_catastrophes(charge)`` :
    elle doit etre **decroissante** avec `charge` (zero sous inoculation,
    deux sous forte charge semantique), comme predit par P0/P1 d'#5104.
    """
    out: Dict[float, Dict[str, float]] = {}
    for c in charges:
        ps = persona_hysteresis_loop(transgression, c, rewards)
        n_cat = len(persona_catastrophe_indices(rewards, ps, threshold=threshold))
        out[float(c)] = {
            "n_catastrophes": float(n_cat),
            "p_range": float(ps.max() - ps.min()),
            "p_mean_abs": float(np.mean(np.abs(ps))),
        }
    return out


# --------------------------------------------------------------------------- #
#  T2 (#26945) : rampe vers le pli, anticipation, surrogates                   #
# --------------------------------------------------------------------------- #
#
# Protocole scelle dans ``docs/ict/ict23-anticipation-pre-enregistrement.md``
# (commit anterieur a ce module). Les valeurs ci-dessous sont celles du
# document ; une modification ici sans revision v2 documentee est un
# amendement post-hoc.

RAMP_T2: Dict[str, object] = {
    "transgression": 2.0,
    "charge": 0.6,
    "dt": 0.01,
    "steps": 67000,
    "b_start": 0.44596,
    "b_end": 0.52596,
    "sigma": 0.05,
    "seeds": (0, 1, 7, 42, 99),
    "pilot_seed": 1000,
    "thin_factor": 10,
    "window": 100,
    "lead_steps": 1000,
    "min_steps": 20000,
    "jump_threshold": 0.15,
    "jump_hold": 200,
    "null_a": 0.4,
    "null_b_start": -0.524,
    "null_b_end": -0.444,
    "n_surrogates": 200,
    "band_percentile": 95.0,
    "loop_points": 601,
    "loop_b_min": -1.2,
    "loop_b_max": 1.2,
    "loop_relax_steps": 2000,
}


def persona_stable_branch(
    a: float, b: float, p_hint: float = 1.0, tol: float = 1e-12,
    max_iter: int = 100,
) -> float:
    """Branche stable ``p*(b)`` du cusp, par Newton amorti avec continuation.

    Resout ``p^3 + a p + b = 0`` au voisinage de ``p_hint`` (le point
    precedent de la rampe) et verifie le residu ``|V'(p*)| < tol``. Le pas de
    Newton est borne a ``0.5`` pour qu'une courbure nulle (proche du pli)
    n'envoie pas l'iteration a l'infini.

    Si Newton ne converge pas (au-dela du pli, ou le point de depart est du
    mauvais cote), on retombe sur les racines exactes de
    :func:`ict.catastrophe.cusp_equilibria` et l'on garde la plus proche de
    ``p_hint`` : la fonction est alors definie partout, y compris la ou la
    branche stable a disparu.
    """
    a = float(a)
    b = float(b)
    p = float(p_hint)
    for _ in range(int(max_iter)):
        g = p ** 3 + a * p + b
        if abs(g) < tol:
            return p
        gp = 3.0 * p * p + a
        if abs(gp) < 1e-12:
            p += 1e-3 if g > 0.0 else -1e-3
            continue
        step = g / gp
        if abs(step) > 0.5:
            step = 0.5 if step > 0.0 else -0.5
        p -= step
    if abs(p ** 3 + a * p + b) <= 1e-9:
        return p
    roots = cat.cusp_equilibria(a, b)
    stable = [x for x, ok in roots if ok] or [x for x, _ in roots]
    if not stable:
        return p
    return float(min(stable, key=lambda x: abs(x - p_hint)))


def persona_branch_along(
    b_values: np.ndarray, a: float, p_start: Optional[float] = None
) -> np.ndarray:
    """Branche stable suivie le long d'une rampe ``b(t)`` (continuation).

    L'etat de depart est ``p_start`` s'il est fourni, sinon le point obtenu
    par Newton depuis ``1.0`` au premier ``b``. Chaque pas repart du pas
    precedent : c'est la **continuation** qui garde la branche du bon cote du
    pli (le cusp a trois racines reelles, deux stables).
    """
    b_values = np.asarray(b_values, dtype=float)
    p = float(persona_stable_branch(a, float(b_values[0])) if p_start is None
              else p_start)
    out = np.empty(b_values.shape, dtype=float)
    for i in range(b_values.shape[0]):
        p = persona_stable_branch(a, float(b_values[i]), p_hint=p)
        out[i] = p
    return out


def persona_ramp_sde(
    transgression: float,
    charge: float,
    b_start: float,
    b_end: float,
    p0: float,
    sigma: float,
    dt: float,
    steps: int,
    seed: int,
) -> Tuple[np.ndarray, np.ndarray]:
    """Rampe bruitee ``b(t)`` lineaire + Euler-Maruyama, plancher ``p >= 0``.

    ``b[t] = b_start + (b_end - b_start) * t / steps`` (point final exclu),
    ``dp = -(p^3 + a p + b(t)) dt + sigma dW``. Meme convention de reflexion
    que :func:`persona_sde` (``p`` borne inferieurement a 0).

    Renvoie ``(ps, bs)`` : la trajectoire et la rampe de ``b`` effectivement
    suivie, de meme longueur. Contrairement a :func:`persona_sde`, ``b``
    **varie** : c'est la seule difference de fond avec le banc stationnaire
    du carnet, et c'est ce que teste la tranche T2.
    """
    g = np.random.default_rng(int(seed))
    sq = float(np.sqrt(dt))
    a = persona_a_factor(transgression, charge)
    n = int(steps)
    bs = np.linspace(float(b_start), float(b_end), n, endpoint=False)
    noise = g.standard_normal(n)
    ps = np.empty(n, dtype=float)
    p = float(p0)
    for t in range(n):
        p = p + dt * float(cat.cusp_force(p, a, float(bs[t]))) + sigma * sq * noise[t]
        if p < 0.0:
            p = 0.0
        ps[t] = p
    return ps, bs


def _first_sustained_below(x: np.ndarray, threshold: float, hold: int) -> Optional[int]:
    """Premier indice d'une excursion sous ``threshold`` d'au moins ``hold`` pas."""
    x = np.asarray(x, dtype=float)
    hold = int(hold)
    if hold < 1 or x.shape[0] < hold:
        return None
    below = (x < float(threshold)).astype(np.int64)
    counts = np.convolve(below, np.ones(hold, dtype=np.int64), mode="valid")
    hit = np.where(counts >= hold)[0]
    return int(hit[0]) if hit.size else None


def persona_fold_b(transgression: float, charge: float) -> Optional[float]:
    """``b_c`` du pli superieur pour ces facteurs, ou ``None`` si ``a >= 0``."""
    a = persona_a_factor(transgression, charge)
    lines = cat.fold_lines(a)
    return None if lines is None else float(max(lines))


def ramp_ews_segment(
    ps: np.ndarray,
    b_values: np.ndarray,
    transgression: float,
    charge: float,
    window: int = 100,
    thin_factor: int = 10,
    lead_steps: int = 1000,
    min_steps: int = 20000,
    jump_threshold: float = 0.15,
    jump_hold: int = 200,
    t_cut_override: Optional[int] = None,
) -> Dict[str, object]:
    """EWS d'une rampe, mesures sur le **residu a la branche analytique**.

    Le detrendage n'est pas un filtre : la derive est retiree exactement en
    soustrayant ``p*(b(t))`` (voir le document scelle — le detrend gaussien
    du carnet coupe a 0.1 unite de temps et retirerait le mode lent cherche).
    Le residu ``p - p*`` a une moyenne nulle par construction.

    Le lead time est applique **avant** toute statistique :
    ``t_cut = min(t_cross, t_jump) - lead_steps``, et l'amincissement
    ``resid[:t_cut:thin_factor]`` ne peut donc produire aucun echantillon
    posterieur a ``t_cut``. Si ``t_cut < min_steps`` la graine est declaree
    ``excluded`` et aucune statistique n'est rendue (garde de faisabilite du
    protocole).

    ``t_cut_override`` sert a l'**appariement du nul N1** : le protocole
    tronque le nul a la longueur exacte du bras pli de la meme graine, pour
    que la comparaison porte sur autant de fenetres de part et d'autre. Il
    n'a aucun autre usage et ne change rien a la regle du lead time, qui
    reste calculee (et enregistree) avant lui.

    Renvoie un dict serialisable (les tableaux restent hors du dict : la
    variance et l'AR1 brute sont dans ``variance`` / ``ar1`` pour les figures).
    """
    ps = np.asarray(ps, dtype=float)
    bs = np.asarray(b_values, dtype=float)
    if ps.shape != bs.shape:
        raise ValueError("ps et b_values doivent avoir la meme longueur")
    n = ps.shape[0]
    a = persona_a_factor(transgression, charge)
    branch = persona_branch_along(bs, a)
    resid = ps - branch

    b_c = persona_fold_b(transgression, charge)
    if b_c is not None:
        crossed = np.where(bs >= b_c)[0]
        t_cross = int(crossed[0]) if crossed.size else n
    else:
        t_cross = n
    t_jump = _first_sustained_below(ps, jump_threshold, jump_hold)
    ref = t_cross if t_jump is None else min(t_cross, t_jump)
    t_cut = int(ref) - int(lead_steps)
    # Appariement du nul N1 : le document scelle impose la MEME longueur que
    # le bras pli de la meme graine, pour que la comparaison porte sur autant
    # de fenetres de part et d'autre. L'override est reserve a cet usage.
    if t_cut_override is not None:
        t_cut = int(t_cut_override)

    out: Dict[str, object] = {
        "t_cross": int(t_cross),
        "t_jump": None if t_jump is None else int(t_jump),
        "t_cut": int(t_cut),
        "jumped_before_fold": bool(t_jump is not None and t_jump < t_cross),
        "excluded": bool(t_cut < int(min_steps)),
        "lambda_start": float(3.0 * branch[0] ** 2 + a),
        "lambda_end": float(3.0 * branch[0] ** 2 + a) if t_cut <= 0 else float(
            3.0 * branch[min(t_cut, n) - 1] ** 2 + a
        ),
        "branch_start": float(branch[0]),
        "tau_var": float("nan"),
        "tau_ar1": float("nan"),
        "amp": float("nan"),
        "n_windows": 0,
        "variance": np.array([]),
        "ar1": np.array([]),
    }
    if out["excluded"]:
        return out

    seg = resid[:t_cut:thin_factor]
    if seg.shape[0] < int(window) + 2:
        out["excluded"] = True
        out["t_cut"] = int(t_cut)
        return out
    var = ews.rolling_variance(seg, int(window))
    ar1 = ews.rolling_lag1_autocorr(seg, int(window))
    ok = np.isfinite(var) & np.isfinite(ar1)
    var_ok = var[ok]
    ar1_ok = ar1[ok]
    idx = np.arange(var_ok.shape[0], dtype=float)
    tau_var, _ = ews.kendall_tau(idx, var_ok)
    tau_ar1, _ = ews.kendall_tau(idx, ar1_ok)
    amp = float(var_ok[-1] / var_ok[0]) if var_ok[0] > 0.0 else float("nan")
    out.update(
        tau_var=float(tau_var),
        tau_ar1=float(tau_ar1),
        amp=amp,
        n_windows=int(var_ok.shape[0]),
        variance=var,
        ar1=ar1,
    )
    return out


def aaft_surrogate(x: np.ndarray, n_surrogates: int, seed: int) -> np.ndarray:
    """Surrogates AAFT : spectre d'amplitude garde, distribution gardee.

    Pour chaque tirage : phases uniformes sur le spectre d'amplitude de ``x``
    (bin DC et bin de Nyquist gardes reels, sans quoi la serie ne serait pas
    reelle), puis **remise en rang** des valeurs triees de ``x`` sur la
    serie obtenue. Le resultat a exactement la distribution empirique de
    ``x`` et, a la remise en rang pres, son spectre d'amplitude.

    C'est le nul 2 du protocole : il conserve la memoire lineaire (le
    spectre) tout en detruisant l'ordre temporel qui porte le ralentissement
    critique, si bien qu'un tau superieur a la bande de ces tirages ne peut
    pas venir d'une simple autocorrelation lineaire.
    """
    x = np.asarray(x, dtype=float)
    m = x.shape[0]
    n = int(n_surrogates)
    amp = np.abs(np.fft.rfft(x))
    sorted_x = np.sort(x)
    g = np.random.default_rng(int(seed))
    out = np.empty((n, m), dtype=float)
    for k in range(n):
        phase = g.uniform(0.0, 2.0 * np.pi, amp.shape[0])
        phase[0] = 0.0
        if m % 2 == 0:
            phase[-1] = 0.0
        s = np.fft.irfft(amp * np.exp(1j * phase), n=m)
        ranks = np.argsort(np.argsort(s))
        out[k] = sorted_x[ranks]
    return out


def surrogate_tau_band(
    x: np.ndarray,
    window: int = 100,
    thin_factor: int = 10,
    n_surrogates: int = 200,
    seed: int = 0,
    percentile: float = 95.0,
) -> Dict[str, object]:
    """Bande des taus de substitution pour une serie (nul 2 du protocole).

    Tire ``n_surrogates`` AAFT de ``x``, calcule ``tau_var`` et ``tau_ar1``
    sur chacun avec les **memes** fenetres que la mesure reelle, et renvoie
    le centile demande, la mediane des ``|tau|`` et le verdict
    d'informativite (mediane des ``|tau_var|`` > 0.5 = nul trop disperse).
    """
    surr = aaft_surrogate(x, n_surrogates, seed)
    taus_var = np.empty(surr.shape[0], dtype=float)
    taus_ar1 = np.empty(surr.shape[0], dtype=float)
    for k in range(surr.shape[0]):
        seg = surr[k][::int(thin_factor)]
        var = ews.rolling_variance(seg, int(window))
        ar1 = ews.rolling_lag1_autocorr(seg, int(window))
        ok = np.isfinite(var) & np.isfinite(ar1)
        idx = np.arange(int(ok.sum()), dtype=float)
        taus_var[k], _ = ews.kendall_tau(idx, var[ok])
        taus_ar1[k], _ = ews.kendall_tau(idx, ar1[ok])
    med_abs = float(np.nanmedian(np.abs(taus_var)))
    return {
        "band_var": float(np.nanpercentile(taus_var, float(percentile))),
        "band_ar1": float(np.nanpercentile(taus_ar1, float(percentile))),
        "median_abs_tau_var": med_abs,
        "median_abs_tau_ar1": float(np.nanmedian(np.abs(taus_ar1))),
        "informative": bool(med_abs <= 0.5),
        "tau_var": taus_var,
        "tau_ar1": taus_ar1,
    }


def loop_tipping_points(
    transgression: float,
    charge: float,
    n_points: int = 601,
    b_min: float = -1.2,
    b_max: float = 1.2,
    dt: float = 0.01,
    relax_steps: int = 2000,
    threshold: float = 0.5,
) -> Dict[str, object]:
    """Points de bascule montée / descente d'un lacet deterministe.

    Balayage ``b_min -> b_max -> b_min`` (``n_points`` par jambe, extremite
    partagee, donc ``rewards`` a ``2 * n_points - 1`` valeurs), relaxation
    ``relax_steps`` pas par valeur. Le saut de la jambe montante donne
    ``b_up``, celui de la jambe descendante ``b_down`` ; leur ecart est la
    **largeur d'hysteresis** mesuree, a comparer a ``2 b_c``.

    Renvoie ``ok=False`` (avec ``jumps``) si l'une des deux jambes ne saute
    pas : un lacet sans saut n'a pas de largeur, et un ``0`` serait une
    valeur inventee.
    """
    n_points = int(n_points)
    up = np.linspace(float(b_min), float(b_max), n_points)
    rewards = np.concatenate([up, up[-2::-1]])
    ps = persona_hysteresis_loop(
        transgression, charge, rewards, dt=dt, relax_steps=relax_steps
    )
    jumps = persona_catastrophe_indices(rewards, ps, threshold=threshold)
    ups = [i for i in jumps if i < n_points]
    downs = [i for i in jumps if i >= n_points]
    out: Dict[str, object] = {
        "reward_points": rewards,
        "ps": ps,
        "jumps": [int(i) for i in jumps],
        "b_up": None,
        "b_down": None,
        "width": None,
        "ok": bool(ups and downs),
    }
    if not out["ok"]:
        return out
    iu = int(ups[0])
    idn = int(downs[0])
    b_up = 0.5 * (rewards[iu - 1] + rewards[iu])
    b_down = 0.5 * (rewards[idn - 1] + rewards[idn])
    out.update(b_up=float(b_up), b_down=float(b_down),
               width=float(abs(b_up - b_down)))
    return out